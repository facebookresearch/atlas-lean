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
following each run of a record maximum.
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

private theorem avoidance_iff {n : ℕ} (asc : Bool) (e : Fin n → ℕ) :
    (List.ofFn e).Triplewise (Allowed asc) ↔
      ∀ p ∈ patterns asc, ¬ InvSeqContainsPattern e p := by
  rw [List.triplewise_iff_getElem]
  constructor
  · intro h p hp ⟨f, hf⟩
    have hij := f.strictMono (show (0 : Fin 3) < 1 by decide)
    have hjk := f.strictMono (show (1 : Fin 3) < 2 by decide)
    have ht : Allowed asc (e (f 0)) (e (f 1)) (e (f 2)) := by
      simpa using h (f 0).val (f 1).val (f 2).val hij hjk (by simp)
    apply (allowed_iff ..).mp ht p hp
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
    suffices Allowed asc (e (f 0)) (e (f 1)) (e (f 2)) by simpa [f] using this
    apply (allowed_iff ..).mpr
    intro p hp hs
    refine h p hp ⟨OrderEmbedding.ofStrictMono f hm, ?_⟩
    have hv (a : Fin 3) : ![e (f 0), e (f 1), e (f 2)] a = e (f a) := by
      fin_cases a <;> rfl
    change ∀ a b, e (f a) < e (f b) ↔ p a < p b
    simpa only [SameOrder, hv] using hs

private abbrev Words (asc : Bool) (n : ℕ) :=
  {l : List ℕ // l.Triplewise (Allowed asc) ∧ Bounded 0 l ∧ l.length = n}

private noncomputable def listEquiv (asc : Bool) (n : ℕ) :
    {e : Fin n → ℕ // (∀ i, e i ≤ i) ∧ ∀ p ∈ patterns asc, ¬ InvSeqContainsPattern e p} ≃
      Words asc n := by
  have bound (e : Fin n → ℕ) : Bounded 0 (List.ofFn e) ↔ ∀ i, e i ≤ i := by
    simp [Bounded, Fin.forall_iff]
  refine Equiv.ofBijective (fun e => ⟨List.ofFn e.1, (avoidance_iff asc e.1).mpr e.2.2,
    (bound e.1).mpr e.2.1, List.length_ofFn⟩) ⟨?_, ?_⟩
  · exact fun _ _ h => Subtype.ext (List.ofFn_injective (congrArg Subtype.val h))
  · rintro ⟨l, ht, hb, rfl⟩
    refine ⟨⟨l.get, (bound l.get).mp ?_, (avoidance_iff asc l.get).mp ?_⟩,
      Subtype.ext (List.ofFn_get l)⟩
    · simpa using hb
    · simpa using ht

private def flipWord {asc : Bool} {n : ℕ} (w : Words asc n) : Words (!asc) n :=
  let h := flip_spec w.2.1 w.2.2.1
  ⟨flip w.1, h.2.1, h.2.2.1, h.1.length_eq.trans w.2.2.2⟩

private def flipEquiv (n : ℕ) : Words false n ≃ Words true n where
  toFun := flipWord
  invFun := flipWord
  left_inv w := Subtype.ext (flip_spec w.2.1 w.2.2.1).2.2.2
  right_inv w := Subtype.ext (flip_spec w.2.1 w.2.2.1).2.2.2

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
  exact Nat.card_congr ((listEquiv false n).trans ((flipEquiv n).trans (listEquiv true n).symm))

end MetaMathlibExt
