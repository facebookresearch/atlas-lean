/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.InversionSequencePatternSets
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.TakeWhile
import Mathlib.Data.List.Triplewise
import Mathlib.Tactic.FinCases

/-!
# Exchanging 201 and 210 in inversion sequences

We prove that exchanging `201` and `210` alongside `010`, `100`, `101`, and `120`
preserves the avoidance counts. The bijection reverses the strictly monotone word
following each run of a record maximum. It also preserves avoidance of `102`.

## References

* Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
  (2024), Article A76, Theorem 11 (pp. 33–34) and the `201`/`210` case of Theorem 15 (p. 58).
-/

namespace MetaMathlibExt
namespace invSeq_wilf_010_100_101_120_201_210

private def Ordered (asc : Bool) (x y : ℕ) : Prop := if asc then x < y else y < x

/-- With first entry `a`, an ascent must stay above `a`. After a descent, the next
entry must exceed `a` or continue in the prescribed order strictly below `a`. -/
private def Allowed (asc : Bool) (a x y : ℕ) : Prop :=
  (a < x → a < y) ∧ (x < a → a < y ∨ (y < a ∧ Ordered asc x y))

private def Bounded (offset : ℕ) (l : List ℕ) : Prop :=
  ∀ i (hi : i < l.length), l[i] ≤ offset + i

private theorem bounded_append {m : ℕ} {p q : List ℕ} :
    Bounded m (p ++ q) ↔ Bounded m p ∧ Bounded (m + p.length) q := by
  constructor
  · intro h
    constructor
    · intro i hi
      have hb := h i (by simp; omega)
      rwa [List.getElem_append_left hi] at hb
    · intro i hi
      have hb := h (p.length + i) (by simpa using hi)
      rw [List.getElem_append_right (by omega)] at hb
      simpa [Nat.add_assoc] using hb
  · rintro ⟨hp, hq⟩ i hi
    by_cases h : i < p.length
    · simpa [List.getElem_append_left h] using hp i h
    · rw [List.getElem_append_right (by omega)]
      have := hq (i - p.length) (by simp at hi; omega)
      omega

/-- Split off the initial segment satisfying `P` when failure of `P` persists. -/
private theorem split_prefix {P : ℕ → Prop} {l : List ℕ}
    (h : l.Pairwise fun x y => ¬ P x → ¬ P y) :
    ∃ p q, l = p ++ q ∧ (∀ x ∈ p, P x) ∧ ∀ y ∈ q, ¬ P y := by
  induction l with
  | nil => exact ⟨[], [], rfl, by simp, by simp⟩
  | cons x l ih =>
    obtain ⟨hx, hl⟩ := List.pairwise_cons.mp h
    by_cases hp : P x
    · obtain ⟨p, q, rfl, hp', hq⟩ := ih hl
      exact ⟨x :: p, q, rfl, by simpa using And.intro hp hp', hq⟩
    · exact ⟨[], x :: l, rfl, by simp, by simpa using And.intro hp (fun y hy => hx y hy hp)⟩

/-- After the first entry come its remaining copies, a monotone word below it,
and a suffix lying strictly above it. -/
private theorem split_block {asc : Bool} {a : ℕ} {r : List ℕ}
    (h : r.Pairwise (Allowed asc a)) :
    ∃ u v w, r = u ++ v ++ w ∧ (∀ x ∈ u, x = a) ∧ (∀ x ∈ v, x < a) ∧
      v.Pairwise (Ordered asc) ∧ ∀ x ∈ w, a < x := by
  obtain ⟨s, w, rfl, hs, hw⟩ := split_prefix (P := (· ≤ a))
    (h.imp fun hh hn => not_le_of_gt (hh.1 (lt_of_not_ge hn)))
  have hpair := (List.pairwise_append.mp h).1
  obtain ⟨u, v, rfl, hu, hv⟩ := split_prefix (P := (· = a)) (hpair.imp_of_mem (by
    intro x y hx _ hxy hne he
    have := hxy.2 (lt_of_le_of_ne (hs _ hx) hne)
    omega))
  have hvlt (x) (hx : x ∈ v) := lt_of_le_of_ne (hs x (List.mem_append_right _ hx)) (hv x hx)
  refine ⟨u, v, w, rfl, hu, hvlt, (List.pairwise_append.mp hpair).2.1.imp_of_mem ?_,
    fun x hx => lt_of_not_ge (hw x hx)⟩
  intro x y hx hy hxy
  exact ((hxy.2 (hvlt x hx)).resolve_left (not_lt_of_gt (hvlt y hy))).2

private theorem monotone_triples {asc : Bool} {v : List ℕ} (h : v.Pairwise (Ordered asc)) :
    v.Triplewise (Allowed asc) := by
  rw [List.triplewise_iff_getElem]
  intro i j k hij hjk hk
  have hxy := List.pairwise_iff_getElem.mp h i j (by omega) (by omega) hij
  have hyz := List.pairwise_iff_getElem.mp h j k (by omega) hk hjk
  cases asc <;> simp [Allowed, Ordered] at * <;> omega

private theorem block_triples {asc : Bool} {a : ℕ} {u v : List ℕ}
    (hu : ∀ x ∈ u, x = a) (hv : ∀ x ∈ v, x < a) (hs : v.Pairwise (Ordered asc)) :
    (u ++ v).Triplewise (Allowed asc) := by
  have hp : v.Pairwise (Allowed asc a) := hs.imp_of_mem (by
    intro x y hx hy hxy
    exact ⟨fun h => (not_lt_of_gt (hv _ hx) h).elim, fun _ => Or.inr ⟨hv _ hy, hxy⟩⟩)
  induction u with
  | nil => exact monotone_triples hs
  | cons x u ih =>
    obtain ⟨rfl, hu'⟩ := List.forall_mem_cons.mp hu
    apply List.Triplewise.cons _ (ih hu')
    apply List.pairwise_append.mpr ⟨?_, hp, ?_⟩
    · apply List.pairwise_of_forall_mem_list
      intro x hx y _
      simp [hu' x hx, Allowed]
    · intro x hx y _
      simp [hu' x hx, Allowed]

private theorem separated_triples {asc : Bool} {p q : List ℕ}
    (hp : p.Triplewise (Allowed asc)) (hq : q.Triplewise (Allowed asc))
    (hlt : ∀ x ∈ p, ∀ y ∈ q, x < y) : (p ++ q).Triplewise (Allowed asc) := by
  refine List.triplewise_append.mpr ⟨hp, hq, ?_, ?_⟩
  · intro x hx
    apply List.pairwise_of_forall_mem_list
    intro y hy z hz
    exact ⟨fun _ => hlt x hx z hz, fun _ => Or.inl (hlt x hx z hz)⟩
  · intro z hz
    apply List.pairwise_of_forall_mem_list
    intro x hx y _
    exact ⟨fun _ => hlt x hx z hz, fun _ => Or.inl (hlt x hx z hz)⟩

/-- Reverse the subword strictly below the leading record, then process the next record. -/
private def flip : List ℕ → List ℕ
  | [] => []
  | a :: r =>
    let rest := r.dropWhile (· == a)
    a :: (r.takeWhile (· == a) ++ (rest.takeWhile (· < a)).reverse ++
      flip (rest.dropWhile (· < a)))
termination_by l => l.length
decreasing_by
  exact Nat.lt_succ_of_le ((List.length_dropWhile_le _ _).trans (List.length_dropWhile_le _ _))

private theorem flip_block {a : ℕ} {u v w : List ℕ}
    (hu : ∀ x ∈ u, x = a) (hv : ∀ x ∈ v, x < a) (hw : ∀ x ∈ w, a < x) :
    flip (a :: (u ++ v ++ w)) = a :: (u ++ v.reverse ++ flip w) := by
  have cut {p : ℕ → Bool} {s t : List ℕ} (hs : ∀ x ∈ s, p x) (ht : ∀ x ∈ t, ¬ p x) :
      (s ++ t).takeWhile p = s ∧ (s ++ t).dropWhile p = t := by
    rw [List.takeWhile_append_of_pos hs, List.dropWhile_append_of_pos hs]
    cases t with
    | nil => simp
    | cons x t => simp [ht x (by simp)]
  have h₁ := cut (p := (· == a)) (fun x hx => beq_iff_eq.mpr (hu x hx))
    (t := v ++ w) (by
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · simpa using (hv x h).ne
      · simpa using (hw x h).ne')
  have h₂ := cut (p := fun x => decide (x < a)) (fun x hx => decide_eq_true (hv x hx))
    (fun x hx => by simpa using (hw x hx).not_gt)
  rw [flip]
  simp only [List.append_assoc, h₁.1, h₁.2, h₂.1, h₂.2]

private theorem flip_spec {asc : Bool} {m : ℕ} {l : List ℕ}
    (h : l.Triplewise (Allowed asc)) (hb : Bounded m l) :
    (flip l).Perm l ∧ (flip l).Triplewise (Allowed !asc) ∧
      Bounded m (flip l) ∧ flip (flip l) = l := by
  cases l with
  | nil => simp [flip, hb]
  | cons a r =>
    obtain ⟨u, v, w, rfl, hu, hv, hs, hw⟩ := split_block (List.triplewise_cons.mp h).1
    let p := (a :: u) ++ v
    let q := (a :: u) ++ v.reverse
    have hpw : (p ++ w).Triplewise (Allowed asc) := h
    have hbw : Bounded m (p ++ w) := hb
    have ⟨hperm, hwtrip, hwbound, hinv⟩ :=
      flip_spec (List.triplewise_append.mp hpw).2.1 (bounded_append.mp hbw).2
    have hw' (x) (hx : x ∈ flip w) := hw x (hperm.mem_iff.mp hx)
    have hv' (x) (hx : x ∈ v.reverse) := hv x (List.mem_reverse.mp hx)
    have hrev : v.reverse.Pairwise (Ordered !asc) := by
      rw [List.pairwise_reverse]
      cases asc <;> exact hs
    have hu' : ∀ x ∈ a :: u, x = a := by simpa using hu
    have hq : ∀ x ∈ q, x ≤ a := by
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact (hu' _ h).le
      · exact (hv' _ h).le
    have hpq : q.Perm p := (List.reverse_perm v).append_left _
    rw [flip_block hu hv hw]
    change (q ++ flip w).Perm (p ++ w) ∧ (q ++ flip w).Triplewise (Allowed !asc) ∧
      Bounded m (q ++ flip w) ∧ _
    refine ⟨hpq.append hperm, separated_triples (block_triples hu' hv' hrev) hwtrip
      (fun x hx y hy => (hq x hx).trans_lt (hw' y hy)), bounded_append.mpr ⟨?_, ?_⟩, ?_⟩
    · have ha : a ≤ m := by simpa using hb 0 (by simp)
      intro i hi
      exact (hq _ (List.getElem_mem hi)).trans (by omega)
    · rwa [hpq.length_eq]
    · rw [flip_block hu hv' hw', hinv, List.reverse_reverse]
termination_by l.length
decreasing_by subst_vars; simp; omega

private def patterns (asc : Bool) : Set (Fin 3 → ℕ) :=
  {![0, 1, 0], ![1, 0, 0], ![1, 0, 1], ![1, 2, 0], if asc then ![2, 1, 0] else ![2, 0, 1]}

private def SameOrder (x y z : ℕ) (p : Fin 3 → ℕ) : Prop :=
  ∀ i j, (![x, y, z] : Fin 3 → ℕ) i < ![x, y, z] j ↔ p i < p j

private theorem allowed_iff (asc : Bool) (x y z : ℕ) :
    Allowed asc x y z ↔ ∀ p ∈ patterns asc, ¬ SameOrder x y z p := by
  cases asc <;> simp [Allowed, Ordered, patterns, SameOrder, Fin.forall_fin_succ] <;> omega

private theorem avoidance_iff {R : ℕ → ℕ → ℕ → Prop} {S : Set (Fin 3 → ℕ)}
    (hR : ∀ x y z, R x y z ↔ ∀ p ∈ S, ¬ SameOrder x y z p)
    {n : ℕ} (e : Fin n → ℕ) :
    (List.ofFn e).Triplewise R ↔ ∀ p ∈ S, ¬ InvSeqContainsPattern e p := by
  rw [List.triplewise_iff_getElem]
  constructor
  · intro h p hp ⟨f, hf⟩
    have hij := f.strictMono (show (0 : Fin 3) < 1 by decide)
    have hjk := f.strictMono (show (1 : Fin 3) < 2 by decide)
    have ht : R (e (f 0)) (e (f 1)) (e (f 2)) := by
      simpa using h (f 0).val (f 1).val (f 2).val hij hjk (by simp)
    apply (hR ..).mp ht p hp
    have hv (i : Fin 3) : ![e (f 0), e (f 1), e (f 2)] i = e (f i) := by
      fin_cases i <;> rfl
    simpa only [SameOrder, hv] using hf
  · intro h i j k hij hjk hk
    have hk' : k < n := by simpa using hk
    let f : Fin 3 → Fin n := ![⟨i, by omega⟩, ⟨j, by omega⟩, ⟨k, hk'⟩]
    have hm : StrictMono f := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp at hab
      · exact hij
      · exact hij.trans hjk
      · exact hjk
    suffices R (e (f 0)) (e (f 1)) (e (f 2)) by simpa [f] using this
    apply (hR ..).mpr
    intro p hp hs
    refine h p hp ⟨OrderEmbedding.ofStrictMono f hm, ?_⟩
    have hv (a : Fin 3) : ![e (f 0), e (f 1), e (f 2)] a = e (f a) := by
      fin_cases a <;> rfl
    change ∀ a b, e (f a) < e (f b) ↔ p a < p b
    simpa only [SameOrder, hv] using hs

private abbrev Words (R : ℕ → ℕ → ℕ → Prop) (n : ℕ) :=
  {l : List ℕ // l.Triplewise R ∧ Bounded 0 l ∧ l.length = n}

private noncomputable def listEquiv {R : ℕ → ℕ → ℕ → Prop} {S : Set (Fin 3 → ℕ)}
    (hR : ∀ x y z, R x y z ↔ ∀ p ∈ S, ¬ SameOrder x y z p) (n : ℕ) :
    {e : Fin n → ℕ // (∀ i, e i ≤ i) ∧ ∀ p ∈ S, ¬ InvSeqContainsPattern e p} ≃ Words R n := by
  have bound (e : Fin n → ℕ) : Bounded 0 (List.ofFn e) ↔ ∀ i, e i ≤ i := by
    simp [Bounded, Fin.forall_iff]
  refine Equiv.ofBijective (fun e => ⟨List.ofFn e.1, (avoidance_iff hR e.1).mpr e.2.2,
    (bound e.1).mpr e.2.1, List.length_ofFn⟩) ⟨?_, ?_⟩
  · exact fun _ _ h => Subtype.ext (List.ofFn_injective (congrArg Subtype.val h))
  · rintro ⟨l, ht, hb, rfl⟩
    refine ⟨⟨l.get, (bound l.get).mp ?_, (avoidance_iff hR l.get).mp ?_⟩,
      Subtype.ext (List.ofFn_get l)⟩
    · simpa using hb
    · simpa using ht

private def flipWord {asc : Bool} {n : ℕ} (w : Words (Allowed asc) n) :
    Words (Allowed !asc) n :=
  let h := flip_spec w.2.1 w.2.2.1
  ⟨flip w.1, h.2.1, h.2.2.1, h.1.length_eq.trans w.2.2.2⟩

private def flipEquiv (n : ℕ) : Words (Allowed false) n ≃ Words (Allowed true) n where
  toFun := flipWord
  invFun := flipWord
  left_inv w := Subtype.ext (flip_spec w.2.1 w.2.2.1).2.2.2
  right_inv w := Subtype.ext (flip_spec w.2.1 w.2.2.1).2.2.2

private def No102 (x y z : ℕ) : Prop := y < x → z ≤ x

private theorem no102_of_ordered {asc : Bool} {v : List ℕ} (h : v.Pairwise (Ordered asc)) :
    v.Triplewise No102 := by
  rw [List.triplewise_iff_getElem]
  intro i j k hij hjk hk
  have hxy := List.pairwise_iff_getElem.mp h i j (by omega) (by omega) hij
  have hxz := List.pairwise_iff_getElem.mp h i k (by omega) hk (hij.trans hjk)
  cases asc <;> simp [Ordered, No102] at * <;> omega

/-- A constant prefix cannot create a `102` across the join if the remaining entries
are all on the same side of its value. -/
private theorem no102_append_const {a : ℕ} {p q : List ℕ}
    (hp : ∀ x ∈ p, x = a) (hq : q.Triplewise No102)
    (hside : (∀ x ∈ q, x ≤ a) ∨ ∀ x ∈ q, a ≤ x) : (p ++ q).Triplewise No102 := by
  refine List.triplewise_append.mpr ⟨?_, hq, ?_, ?_⟩
  · rw [List.triplewise_iff_getElem]
    intro i j k hij hjk hk
    simp [No102, hp _ (List.getElem_mem (by omega : i < p.length)),
      hp _ (List.getElem_mem (by omega : j < p.length))]
  · intro x hx
    apply List.pairwise_of_forall_mem_list
    intro y hy z hz
    rw [hp x hx]
    rcases hside with hlo | hhi
    · exact fun _ => hlo z hz
    · exact fun h => (not_lt_of_ge (hhi y hy) h).elim
  · intro z _
    apply List.pairwise_of_forall_mem_list
    intro x hx y hy
    simp [No102, hp x hx, hp y hy]

/-- In the block decomposition, a smaller letter followed by a larger one would
form `102` with the leading letter. Thus at least one of the two blocks is empty. -/
private theorem flip_preserves_no102 {asc : Bool} {m : ℕ} {l : List ℕ}
    (h : l.Triplewise (Allowed asc)) (hb : Bounded m l) (h102 : l.Triplewise No102) :
    (flip l).Triplewise No102 := by
  cases l with
  | nil => simp [flip]
  | cons a r =>
    obtain ⟨u, v, w, rfl, hu, hv, hs, hw⟩ := split_block (List.triplewise_cons.mp h).1
    have hempty : v = [] ∨ w = [] := by
      by_contra! hne
      obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil v hne.1
      obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil w hne.2
      have hcross := (List.pairwise_append.mp (List.triplewise_cons.mp h102).1).2.2
      exact (hw y hy).not_ge (hcross x (List.mem_append_right _ hx) y hy (hv x hx))
    have hu' : ∀ x ∈ a :: u, x = a := by simpa using hu
    rw [flip_block hu hv hw]
    rcases hempty with rfl | rfl
    · let p := (a :: u) ++ ([] : List ℕ)
      have hpw : (p ++ w).Triplewise (Allowed asc) := h
      have hbw : Bounded m (p ++ w) := hb
      have hpw102 : (p ++ w).Triplewise No102 := h102
      have hwt := (List.triplewise_append.mp hpw).2.1
      have hwb := (bounded_append.mp hbw).2
      have hw102 := (List.triplewise_append.mp hpw102).2.1
      have hperm := (flip_spec hwt hwb).1
      simpa using no102_append_const hu' (flip_preserves_no102 hwt hwb hw102)
        (Or.inr fun x hx => (hw x (hperm.mem_iff.mp hx)).le)
    · have hrev : v.reverse.Pairwise (Ordered !asc) := by
        rw [List.pairwise_reverse]
        cases asc <;> exact hs
      simpa [flip] using no102_append_const hu' (no102_of_ordered hrev)
        (Or.inl fun x hx => (hv x (List.mem_reverse.mp hx)).le)
termination_by l.length
decreasing_by subst_vars; simp

private def patterns102 (asc : Bool) : Set (Fin 3 → ℕ) :=
  {![0, 1, 0], ![1, 0, 0], ![1, 0, 1], ![1, 0, 2], ![1, 2, 0],
    if asc then ![2, 1, 0] else ![2, 0, 1]}

private def Allowed102 (asc : Bool) (x y z : ℕ) : Prop := Allowed asc x y z ∧ No102 x y z

private theorem allowed102_iff (asc : Bool) (x y z : ℕ) :
    Allowed102 asc x y z ↔ ∀ p ∈ patterns102 asc, ¬ SameOrder x y z p := by
  have hset : patterns102 asc = insert ![1, 0, 2] (patterns asc) := by
    ext p
    simp only [patterns102, patterns, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have h102 : No102 x y z ↔ ¬ SameOrder x y z ![1, 0, 2] := by
    simp [No102, SameOrder, Fin.forall_fin_succ]
    omega
  rw [hset, Set.forall_mem_insert, ← h102, ← allowed_iff, Allowed102, and_comm]

private theorem triplewise_allowed102 {asc : Bool} {l : List ℕ} :
    l.Triplewise (Allowed102 asc) ↔ l.Triplewise (Allowed asc) ∧ l.Triplewise No102 := by
  simp only [List.triplewise_iff_getElem, Allowed102, forall_and]

private def flipWord102 {asc : Bool} {n : ℕ} (w : Words (Allowed102 asc) n) :
    Words (Allowed102 !asc) n :=
  let h := triplewise_allowed102.mp w.2.1
  let w' := flipWord (⟨w.1, h.1, w.2.2⟩ : Words (Allowed asc) n)
  ⟨w'.1, triplewise_allowed102.mpr ⟨w'.2.1, flip_preserves_no102 h.1 w.2.2.1 h.2⟩, w'.2.2⟩

private def flipEquiv102 (n : ℕ) : Words (Allowed102 false) n ≃ Words (Allowed102 true) n where
  toFun := flipWord102
  invFun := flipWord102
  left_inv w := Subtype.ext (flip_spec (triplewise_allowed102.mp w.2.1).1 w.2.2.1).2.2.2
  right_inv w := Subtype.ext (flip_spec (triplewise_allowed102.mp w.2.1).1 w.2.2.1).2.2.2

end invSeq_wilf_010_100_101_120_201_210

open invSeq_wilf_010_100_101_120_201_210 in
/-- **I-Wilf equivalence of $\{010, 100, 101, 120, 201\}$ and $\{010, 100, 101, 120, 210\}$.**
Write length-3 patterns as digit strings ($101$ is the pattern $(1, 0, 1)$) and let $|I_n(B)|$ be
the number of inversion sequences of length $n$ that avoid every pattern in the set $B$. Then for
every $n \ge 0$, $|I_n(\{010, 100, 101, 120, 201\})| = |I_n(\{010, 100, 101, 120, 210\})|$.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Theorem 11 (`integers-2024-A76-thm-11`). -/
public theorem invSeq_wilf_010_100_101_120_201_210 :
    invSeqAvoidCount ({![0, 1, 0], ![1, 0, 0], ![1, 0, 1], ![1, 2, 0], ![2, 0, 1]}
        : Set (Fin 3 → ℕ)) =
      invSeqAvoidCount ({![0, 1, 0], ![1, 0, 0], ![1, 0, 1], ![1, 2, 0], ![2, 1, 0]}
          : Set (Fin 3 → ℕ)) := by
  funext n
  exact Nat.card_congr ((listEquiv (allowed_iff false) n).trans
    ((flipEquiv n).trans (listEquiv (allowed_iff true) n).symm))

open invSeq_wilf_010_100_101_120_201_210 in
/-- **Exchanging $201$ and $210$ in $\{010, 100, 101, 102, 120, 201\}$.** Write length-3
patterns as digit strings ($101$ is the pattern $(1, 0, 1)$) and let $|I_n(B)|$ be the number of
inversion sequences of length $n$ that avoid every pattern in the set $B$. For a pattern $\tau$
let $A_\tau = \{010, 100, 101, 102, 120, \tau\}$. Then for every $n \ge 0$,
$|I_n(A_{201})| = |I_n(A_{210})|$.

The source further claims $|I_n(A_{210})| = |I_n(B)| = |I_n(C)|$ for all $n$, with
$B = \{010, 100, 110, 102, 120, 201\}$ and $C = \{010, 101, 110, 102, 120, 210\}$; these claims are
false as printed ($|I_7| = 538, 537, 539$ for $A_{210}$, $B$, $C$) and are omitted.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Theorem 15 (`integers-2024-A76-thm-15`). -/
public theorem invSeq_wilf_010_100_101_102_120_201_210 :
    invSeqAvoidCount ({![0, 1, 0], ![1, 0, 0], ![1, 0, 1], ![1, 0, 2], ![1, 2, 0], ![2, 0, 1]}
        : Set (Fin 3 → ℕ)) =
      invSeqAvoidCount ({![0, 1, 0], ![1, 0, 0], ![1, 0, 1], ![1, 0, 2], ![1, 2, 0], ![2, 1, 0]}
          : Set (Fin 3 → ℕ)) := by
  funext n
  exact Nat.card_congr ((listEquiv (allowed102_iff false) n).trans
    ((flipEquiv102 n).trans (listEquiv (allowed102_iff true) n).symm))

end MetaMathlibExt
