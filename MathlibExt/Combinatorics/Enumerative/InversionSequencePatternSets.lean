/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Hom.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.TakeWhile
import Mathlib.Data.List.Triplewise
import Mathlib.Tactic.FinCases

/-!
# Pattern avoidance in inversion sequences

We define containment, avoidance counts and generating functions for length-three patterns, and
prove that exchanging `101` and `110` alongside `000`, `010`, `100` and `120` preserves the counts.

## References

* Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24 (2024),
  Article A76, pp. 1–112, Introduction and Theorem 4.
-/

namespace MetaMathlibExt

open PowerSeries

@[expose] public section

/-- **Containment of a length-3 pattern.** A sequence $e = e_0 e_1 \cdots e_{n-1}$ of natural
numbers contains the length-3 pattern $p = p_0 p_1 p_2$ of natural numbers when there are
positions $i_0 < i_1 < i_2$ in $\{0, \dots, n - 1\}$ such that, for all $a, b \in \{0, 1, 2\}$,
$e_{i_a} < e_{i_b}$ if and only if $p_a < p_b$; that is, the subsequence $e_{i_0} e_{i_1} e_{i_2}$
is order-isomorphic to $p$.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Introduction. -/
def InvSeqContainsPattern {n : ℕ} (e : Fin n → ℕ) (p : Fin 3 → ℕ) : Prop :=
  ∃ f : Fin 3 ↪o Fin n, ∀ a b, e (f a) < e (f b) ↔ p a < p b

/-- The triple `(x, y, z)` is order-isomorphic to the length-three pattern `p`: all strict
comparisons between positions agree, including when some of the entries are equal. -/
def InvSeqPatternSameOrder (x y z : ℕ) (p : Fin 3 → ℕ) : Prop :=
  ∀ i j, (![x, y, z] : Fin 3 → ℕ) i < ![x, y, z] j ↔ p i < p j

/-- A triple has the same order as `p` exactly when all six directed comparisons between
its distinct positions agree with the corresponding comparisons in `p`. -/
theorem invSeqPatternSameOrder_iff {x y z : ℕ} {p : Fin 3 → ℕ} :
    InvSeqPatternSameOrder x y z p ↔
      (x < y ↔ p 0 < p 1) ∧ (x < z ↔ p 0 < p 2) ∧
      (y < x ↔ p 1 < p 0) ∧ (y < z ↔ p 1 < p 2) ∧
      (z < x ↔ p 2 < p 0) ∧ (z < y ↔ p 2 < p 1) := by
  simp [InvSeqPatternSameOrder, Fin.forall_fin_succ, and_assoc]

/-- A sequence contains a length-three pattern if and only if some three strictly increasing
indices select entries that have the same order as the pattern. -/
theorem invSeqContainsPattern_iff_exists_indices {n : ℕ} (e : Fin n → ℕ) (p : Fin 3 → ℕ) :
    InvSeqContainsPattern e p ↔
      ∃ (i j k : Fin n), i < j ∧ j < k ∧ InvSeqPatternSameOrder (e i) (e j) (e k) p := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f 0, f 1, f 2, f.strictMono (by decide), f.strictMono (by decide), ?_⟩
    have hval (i : Fin 3) : ![e (f 0), e (f 1), e (f 2)] i = e (f i) := by
      fin_cases i <;> rfl
    simpa only [InvSeqPatternSameOrder, hval] using hf
  · rintro ⟨i, j, k, hij, hjk, hs⟩
    let f : Fin 3 → Fin n := ![i, j, k]
    have hmono : StrictMono f := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp at hab
      · exact hij
      · exact hij.trans hjk
      · exact hjk
    refine ⟨OrderEmbedding.ofStrictMono f hmono, ?_⟩
    have hval (a : Fin 3) : ![e i, e j, e k] a = e (f a) := by
      fin_cases a <;> rfl
    change ∀ a b, e (f a) < e (f b) ↔ p a < p b
    simpa only [InvSeqPatternSameOrder, hval] using hs

/-- **Short sequences contain no length-3 pattern.** If $n < 3$, then no sequence
$e_0 e_1 \cdots e_{n-1}$ of natural numbers contains a length-3 pattern $p$.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Introduction. -/
theorem not_invSeqContainsPattern_of_lt {n : ℕ} (hn : n < 3) (e : Fin n → ℕ)
    (p : Fin 3 → ℕ) : ¬ InvSeqContainsPattern e p := by
  rintro ⟨f, -⟩
  have := Fintype.card_le_of_embedding f.toEmbedding
  simp at this
  omega

/-- **Number of inversion sequences avoiding a set of patterns.** An inversion sequence of length
$n$ is a sequence $e = e_0 e_1 \cdots e_{n-1}$ of natural numbers with $e_i \le i$ for every $i$.
It contains a length-3 pattern $p = p_0 p_1 p_2$ (a triple of natural numbers) when some
subsequence $e_a e_b e_c$ with $a < b < c$ is order-isomorphic to $p$. For a set $B$ of length-3
patterns, $|I_n(B)|$ is the number of inversion sequences of length $n$ that contain no pattern
of $B$.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Introduction. -/
noncomputable def invSeqAvoidCount (B : Set (Fin 3 → ℕ)) (n : ℕ) : ℕ :=
  Nat.card {e : Fin n → ℕ // (∀ i, e i ≤ i) ∧ ∀ p ∈ B, ¬ InvSeqContainsPattern e p}

/-- **One inversion sequence of length one.** For every set $B$ of length-3 patterns, the number
$|I_1(B)|$ of inversion sequences of length one that avoid every pattern in $B$ equals $1$: the
only inversion sequence of length one is $0$, and it avoids every length-3 pattern.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Introduction. -/
theorem invSeqAvoidCount_one (B : Set (Fin 3 → ℕ)) : invSeqAvoidCount B 1 = 1 := by
  rw [invSeqAvoidCount, Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun e e' => Subtype.ext (funext fun i => ?_)⟩, ⟨⟨fun _ => 0, ?_⟩⟩⟩
  · have h := e.2.1 i
    have h' := e'.2.1 i
    have hi : (i : ℕ) = 0 := by omega
    omega
  · exact ⟨fun i => Nat.zero_le _, fun p _ => not_invSeqContainsPattern_of_lt (by omega) _ p⟩

/-- **Generating function of inversion sequences avoiding a set of patterns.** For a set $B$ of
length-3 patterns, $F_B(x) = \sum_{n \ge 1} |I_n(B)| x^n$ is the formal power series in
$\mathbb{Q}[[x]]$ with constant coefficient $0$ whose coefficient of $x^n$, for $n \ge 1$, is the
number $|I_n(B)|$ of inversion sequences of length $n$ that avoid every pattern in $B$.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Section 2. -/
noncomputable def invSeqAvoidGF (B : Set (Fin 3 → ℕ)) : ℚ⟦X⟧ :=
  PowerSeries.mk fun n => if n = 0 then 0 else (invSeqAvoidCount B n : ℚ)

/-- **Coefficients of the generating function of pattern-avoiding inversion sequences.** For
every set $B$ of length-3 patterns and every $n \ge 0$, the generating function
$F_B(x) = \sum_{m \ge 1} |I_m(B)| x^m \in \mathbb{Q}[[x]]$ has constant coefficient $0$, and its
coefficient of $x^{n+1}$ is $|I_{n+1}(B)|$, the number of inversion sequences of length $n + 1$
that avoid every pattern in $B$.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Section 2. -/
theorem coeff_invSeqAvoidGF (B : Set (Fin 3 → ℕ)) (n : ℕ) :
    coeff 0 (invSeqAvoidGF B) = 0 ∧
      coeff (n + 1) (invSeqAvoidGF B) = (invSeqAvoidCount B (n + 1) : ℚ) := by
  simp [invSeqAvoidGF]

end

namespace invSeq_wilf_000_010_100_120_101_110

/-- The first three conditions exclude `000` and `010`, `100`, and `120`, respectively.
The final condition excludes `110` when the second copy is at the end, and `101` otherwise. -/
private def Allowed (atEnd : Bool) (x y z : ℕ) : Prop :=
  (x = z → y < x) ∧ (y = z → x ≤ y) ∧ (x < y → x ≤ z) ∧
    if atEnd then x = y → x ≤ z else x = z → x ≤ y

private def IsInversion (l : List ℕ) : Prop :=
  ∀ i (hi : i < l.length), l[i] ≤ i

private def Valid (atEnd : Bool) (l : List ℕ) : Prop :=
  l.Triplewise (Allowed atEnd) ∧ IsInversion l

/-- The entries after the first occurrence of the block maximum. -/
private def afterMax (atEnd : Bool) (a : ℕ) (t : List ℕ) (dup : Bool) : List ℕ :=
  if dup then (if atEnd then t ++ [a] else a :: t) else t

private theorem mem_afterMax {atEnd dup : Bool} {a x : ℕ} {t : List ℕ} :
    x ∈ afterMax atEnd a t dup ↔ x ∈ t ∨ (dup = true ∧ x = a) := by
  cases dup <;> cases atEnd <;> simp [afterMax, or_comm]

private theorem length_afterMax (atEnd : Bool) (a : ℕ) (t : List ℕ) (dup : Bool) :
    (afterMax atEnd a t dup).length = t.length + dup.toNat := by
  cases dup <;> cases atEnd <;> simp [afterMax]

/-- The conditions on a block, which depend only on its first maximum and the entries other
than that maximum. A block begins at a new record value. -/
private structure BlockOk (p : List ℕ) (a : ℕ) (t : List ℕ) : Prop where
  prefix_lt : ∀ x ∈ p, x < a
  tail_lt : ∀ x ∈ t, x < a
  separated : ∀ x ∈ p, ∀ y ∈ t, x < y
  tail_nodup : t.Nodup
  tail_120 : t.Triplewise (fun x y z => x < y → x ≤ z)
  bound : a ≤ p.length

private theorem BlockOk.congr {p q t : List ℕ} {a : ℕ} (h : BlockOk p a t)
    (hm : ∀ x, x ∈ q ↔ x ∈ p) (hl : q.length = p.length) : BlockOk q a t :=
  ⟨fun x hx => h.prefix_lt x ((hm x).1 hx), h.tail_lt,
    fun x hx => h.separated x ((hm x).1 hx), h.tail_nodup, h.tail_120, hl ▸ h.bound⟩

private theorem lt_of_mem_prefix {p t : List ℕ} {a x y : ℕ} {atEnd dup : Bool}
    (h : BlockOk p a t) (hx : x ∈ p) (hy : y ∈ a :: afterMax atEnd a t dup) : x < y := by
  rcases List.mem_cons.mp hy with rfl | hy
  · exact h.prefix_lt _ hx
  · rcases mem_afterMax.mp hy with ht | ⟨_, rfl⟩
    · exact h.separated _ hx _ ht
    · exact h.prefix_lt _ hx

private theorem le_of_mem_block {a x : ℕ} {atEnd dup : Bool} {t : List ℕ}
    (ht : ∀ y ∈ t, y < a) (hx : x ∈ a :: afterMax atEnd a t dup) : x ≤ a := by
  rcases List.mem_cons.mp hx with rfl | hx
  · exact le_rfl
  · rcases mem_afterMax.mp hx with hx | ⟨_, rfl⟩
    · exact (ht _ hx).le
    · exact le_rfl

private theorem Allowed.of_prefix {atEnd : Bool} {x y z : ℕ}
    (hy : x < y) (hz : x < z) : Allowed atEnd x y z := by
  cases atEnd <;> simp only [Allowed, Bool.false_eq_true, ↓reduceIte] <;> omega

private theorem Allowed.of_suffix {atEnd : Bool} {x y z : ℕ}
    (hx : x < z) (hy : y < z) : Allowed atEnd x y z := by
  cases atEnd <;> simp only [Allowed, Bool.false_eq_true, ↓reduceIte] <;> omega

private theorem Allowed.same_ends {atEnd : Bool} {a y : ℕ} (h : Allowed atEnd a y a) :
    atEnd = true ∧ y < a := by
  cases atEnd <;> simp [Allowed] at h ⊢ <;> omega

private theorem Allowed.same_start {atEnd : Bool} {a y : ℕ} (h : Allowed atEnd a a y)
    (hy : y ≤ a) : atEnd = false ∧ y < a := by
  cases atEnd <;> simp [Allowed] at h ⊢ <;> omega

private theorem block_triplewise {p t : List ℕ} {a : ℕ} (h : BlockOk p a t)
    (atEnd dup : Bool) : (a :: afterMax atEnd a t dup).Triplewise (Allowed atEnd) := by
  have tail : t.Triplewise (Allowed atEnd) := by
    have h120 := List.triplewise_iff_getElem.mp h.tail_120
    rw [List.triplewise_iff_getElem]
    have nd := List.pairwise_iff_getElem.mp h.tail_nodup
    intro i j k hij hjk hk
    have hxy := nd i j (by omega) (by omega) hij
    have hxz := nd i k (by omega) hk (by omega)
    have hyz := nd j k (by omega) hk hjk
    have hle := h120 i j k hij hjk hk
    cases atEnd <;> simpa [Allowed, hxy, hxz, hyz] using hle
  have head : t.Pairwise (Allowed atEnd a) := by
    have nd := List.pairwise_iff_getElem.mp h.tail_nodup
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    have hi' := h.tail_lt _ (List.getElem_mem hi)
    have hj' := h.tail_lt _ (List.getElem_mem hj)
    have hne := nd i j hi hj hij
    cases atEnd <;> simp [Allowed, ne_of_gt hj', ne_of_gt hi', hne, not_lt_of_gt hi']
  cases dup
  · exact List.Triplewise.cons head tail
  cases atEnd
  · have hh : ∀ x ∈ t, Allowed false a a x := by
      intro x hx
      have hlt := h.tail_lt x hx
      simp [Allowed, ne_of_gt hlt]
    exact List.Triplewise.cons (List.pairwise_cons.mpr ⟨hh, head⟩)
      (List.Triplewise.cons head tail)
  · change (a :: (t ++ [a])).Triplewise (Allowed true)
    apply List.Triplewise.cons
    · rw [List.pairwise_append]
      refine ⟨head, by simp, ?_⟩
      intro x hx y hy
      simp only [List.mem_singleton] at hy
      subst y
      have hlt := h.tail_lt x hx
      simp [Allowed, hlt, ne_of_gt hlt, ne_of_lt hlt, not_lt_of_gt hlt]
    · rw [List.triplewise_append]
      refine ⟨tail, by simp, fun _ _ => by simp, ?_⟩
      intro y hy
      simp only [List.mem_singleton] at hy
      subst y
      rw [List.pairwise_iff_getElem]
      intro i j hi hj _
      exact Allowed.of_suffix (h.tail_lt _ (List.getElem_mem hi))
        (h.tail_lt _ (List.getElem_mem hj))

private theorem valid_append {p t : List ℕ} {a : ℕ} {atEnd dup : Bool}
    (hp : Valid atEnd p) (h : BlockOk p a t) :
    Valid atEnd (p ++ a :: afterMax atEnd a t dup) := by
  refine ⟨List.triplewise_append.mpr ⟨hp.1, block_triplewise h _ _, ?_, ?_⟩, ?_⟩
  · intro x hx
    rw [List.pairwise_iff_getElem]
    intro i j hi hj _
    exact Allowed.of_prefix (lt_of_mem_prefix h hx (List.getElem_mem hi))
      (lt_of_mem_prefix h hx (List.getElem_mem hj))
  · intro y hy
    rw [List.pairwise_iff_getElem]
    intro i j hi hj _
    exact Allowed.of_suffix (lt_of_mem_prefix h (List.getElem_mem hi) hy)
      (lt_of_mem_prefix h (List.getElem_mem hj) hy)
  · intro i hi
    by_cases hpi : i < p.length
    · rw [List.getElem_append_left hpi]
      exact hp.2 i hpi
    · rw [List.getElem_append_right (by omega)]
      exact (le_of_mem_block h.tail_lt (List.getElem_mem _)).trans (by
        have := h.bound
        omega)

private theorem split_at_first_max {a : ℕ} {l : List ℕ} (ha : a ∈ l)
    (hle : ∀ x ∈ l, x ≤ a) : ∃ p r, l = p ++ a :: r ∧ ∀ x ∈ p, x < a := by
  induction l with
  | nil => simp at ha
  | cons x l ih =>
    by_cases h : x = a
    · subst x
      exact ⟨[], l, rfl, by simp⟩
    · obtain ⟨p, r, he, hlt⟩ :=
        ih ((List.mem_cons.mp ha).resolve_left (Ne.symm h))
          (fun y hy => hle y (List.mem_cons_of_mem _ hy))
      refine ⟨x :: p, r, by rw [he, List.cons_append], ?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact lt_of_le_of_ne (hle _ (by simp)) h
      · exact hlt _ hy

private theorem split_after_max {atEnd : Bool} {a : ℕ} {r : List ℕ}
    (h : r.Pairwise (Allowed atEnd a)) (hle : ∀ x ∈ r, x ≤ a) :
    ∃ t dup, r = afterMax atEnd a t dup ∧ ∀ x ∈ t, x < a := by
  by_cases ha : a ∈ r
  · obtain ⟨u, v, rfl⟩ := List.mem_iff_append.mp ha
    obtain ⟨_, hr, hcross⟩ := List.pairwise_append.mp h
    have hleft : ∀ x ∈ u, atEnd = true ∧ x < a :=
      fun x hx => (hcross x hx a (by simp)).same_ends
    have hright : ∀ x ∈ v, atEnd = false ∧ x < a := fun x hx =>
      ((List.pairwise_cons.mp hr).1 x hx).same_start (hle x (by simp [hx]))
    cases atEnd
    · have hu : u = [] := List.eq_nil_iff_forall_not_mem.mpr fun x hx =>
        Bool.noConfusion (hleft x hx).1
      subst u
      exact ⟨v, true, rfl, fun x hx => (hright x hx).2⟩
    · have hv : v = [] := List.eq_nil_iff_forall_not_mem.mpr fun x hx =>
        Bool.noConfusion (hright x hx).1
      subst v
      exact ⟨u, true, rfl, fun x hx => (hleft x hx).2⟩
  · refine ⟨r, false, rfl, fun x hx => lt_of_le_of_ne (hle _ hx) ?_⟩
    rintro rfl
    exact ha hx

private theorem triplewise_without_copy {atEnd dup : Bool} {a : ℕ} {t : List ℕ}
    (h : (a :: afterMax atEnd a t dup).Triplewise (Allowed atEnd)) :
    (a :: t).Triplewise (Allowed atEnd) := by
  cases dup
  · exact h
  cases atEnd
  · exact (List.triplewise_cons.mp h).2
  · change (a :: t ++ [a]).Triplewise (Allowed true) at h
    exact (List.triplewise_append.mp h).1

-- Split at the first occurrence of the largest entry. The remaining entries below the
-- maximum are distinct by avoidance of 100, and exceed the prefix by avoidance of 010 and 120.
private theorem valid_split {atEnd : Bool} {l : List ℕ} (h : Valid atEnd l) (hne : l ≠ []) :
    ∃ p a t dup, l = p ++ a :: afterMax atEnd a t dup ∧ Valid atEnd p ∧ BlockOk p a t := by
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp
    (show l.max? ≠ none from fun he => hne (List.max?_eq_none_iff.mp he))
  obtain ⟨hm, hle⟩ := List.max?_eq_some_iff.mp ha
  obtain ⟨p, r, rfl, hplt⟩ := split_at_first_max hm hle
  obtain ⟨hp, hs, hcross, _⟩ := List.triplewise_append.mp h.1
  obtain ⟨t, dup, rfl, htlt⟩ := split_after_max (List.triplewise_cons.mp hs).1
    (fun x hx => hle x (List.mem_append_right _ (List.mem_cons_of_mem _ hx)))
  obtain ⟨hpairs, ht⟩ := List.triplewise_cons.mp (triplewise_without_copy hs)
  refine ⟨p, a, t, dup, rfl, ⟨hp, ?_⟩, ⟨hplt, htlt, ?_, ?_, ?_, ?_⟩⟩
  · intro i hi
    have hb := h.2 i (by simp; omega)
    rwa [List.getElem_append_left hi] at hb
  · intro x hx y hy
    have hy' : y ∈ afterMax atEnd a t dup := mem_afterMax.mpr (Or.inl hy)
    have hxy := (List.pairwise_cons.mp (hcross x hx)).1 y hy'
    have hxa := hplt x hx
    have hya := htlt y hy
    have hle := hxy.2.2.1 hxa
    by_contra! hge
    exact (not_lt_of_gt hxa) (hxy.1 (le_antisymm hle hge))
  · rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_getElem] at ⊢
    rw [List.pairwise_iff_getElem] at hpairs
    intro i j hi hj hij he
    exact (not_le_of_gt (htlt _ (List.getElem_mem hi))) ((hpairs i j hi hj hij).2.1 he)
  · exact ht.imp fun hh => hh.2.2.1
  · have hb := h.2 p.length (by simp)
    simpa [List.getElem_append_right (le_refl p.length)] using hb

-- Encode the blocks in reverse order, so the prefix is represented by the tail of the code.
private abbrev Block := ℕ × List ℕ × Bool

private def render (atEnd : Bool) : List Block → List ℕ
  | [] => []
  | (a, t, dup) :: c => render atEnd c ++ a :: afterMax atEnd a t dup

private theorem render_length (atEnd : Bool) (c : List Block) :
    (render atEnd c).length = (render false c).length := by
  induction c with
  | nil => rfl
  | cons b c ih =>
    obtain ⟨a, t, dup⟩ := b
    simp [render, length_afterMax, ih]

private theorem render_mem (atEnd : Bool) (c : List Block) (x : ℕ) :
    x ∈ render atEnd c ↔ x ∈ render false c := by
  induction c with
  | nil => rfl
  | cons b c ih =>
    obtain ⟨a, t, dup⟩ := b
    simp [render, mem_afterMax, ih]

private inductive ValidCode : List Block → Prop
  | nil : ValidCode []
  | cons {c : List Block} {a : ℕ} {t : List ℕ} {dup : Bool} :
      ValidCode c → BlockOk (render false c) a t → ValidCode ((a, t, dup) :: c)

private theorem render_valid {c : List Block} (h : ValidCode c) (atEnd : Bool) :
    Valid atEnd (render atEnd c) := by
  induction h with
  | nil => exact ⟨.nil, by simp [IsInversion, render]⟩
  | @cons c a t dup hc hb ih =>
    exact valid_append ih (hb.congr (render_mem atEnd c) (render_length atEnd c))

private theorem code_exists {atEnd : Bool} {l : List ℕ} (h : Valid atEnd l) :
    ∃ c, ValidCode c ∧ render atEnd c = l := by
  by_cases hn : l = []
  · exact ⟨[], .nil, hn.symm⟩
  obtain ⟨p, a, t, dup, he, hp, hb⟩ := valid_split h hn
  obtain ⟨c, hc, hec⟩ := code_exists hp
  have hb' : BlockOk (render false c) a t := hb.congr
    (fun x => (render_mem atEnd c x).symm.trans (hec ▸ Iff.rfl))
    ((render_length atEnd c).symm.trans (congrArg List.length hec))
  exact ⟨(a, t, dup) :: c, .cons hc hb', by rw [render, hec, ← he]⟩
termination_by l.length
decreasing_by simp [he]

private theorem max?_append_block {p t : List ℕ} {a : ℕ} {atEnd dup : Bool}
    (h : BlockOk p a t) :
    (p ++ a :: afterMax atEnd a t dup).max? = some a := by
  refine List.max?_eq_some_iff.mpr ⟨by simp, ?_⟩
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact (h.prefix_lt _ hx).le
  · exact le_of_mem_block h.tail_lt hx

private theorem takeWhile_append_block {p t : List ℕ} {a : ℕ} {atEnd dup : Bool}
    (h : BlockOk p a t) :
    (p ++ a :: afterMax atEnd a t dup).takeWhile (fun x => decide (x < a)) = p := by
  rw [List.takeWhile_append_of_pos (fun _ hx => decide_eq_true (h.prefix_lt _ hx))]
  simp

private theorem filter_afterMax {t : List ℕ} {a : ℕ} {atEnd dup : Bool}
    (ht : ∀ x ∈ t, x < a) :
    (afterMax atEnd a t dup).filter (fun x => decide (x < a)) = t := by
  have he := List.filter_eq_self.mpr (fun _ hx => decide_eq_true (ht _ hx))
  cases atEnd <;> cases dup <;> simp [afterMax, he]

private theorem render_inj {c c' : List Block} (hc : ValidCode c) (hc' : ValidCode c')
    {atEnd : Bool} (he : render atEnd c = render atEnd c') : c = c' := by
  induction hc generalizing c' with
  | nil =>
    cases hc' with
    | nil => rfl
    | cons => simp [render] at he
  | @cons c a t dup hc hb ih =>
    cases hc' with
    | nil => simp [render] at he
    | @cons c' a' t' dup' hc' hb' =>
      have hp := hb.congr (render_mem atEnd c) (render_length atEnd c)
      have hp' := hb'.congr (render_mem atEnd c') (render_length atEnd c')
      simp only [render] at he
      have ha : a = a' := by
        simpa only [max?_append_block hp, max?_append_block hp', Option.some.injEq]
          using congrArg List.max? he
      subst a'
      have hec : render atEnd c = render atEnd c' := by
        simpa only [takeWhile_append_block hp, takeWhile_append_block hp'] using
          congrArg (List.takeWhile fun x => decide (x < a)) he
      have htail := (List.cons.inj (List.append_cancel_left (hec ▸ he))).2
      have ht : t = t' := by
        simpa only [filter_afterMax hp.tail_lt, filter_afterMax hp'.tail_lt] using
          congrArg (List.filter fun x => decide (x < a)) htail
      subst t'
      have hd := congrArg List.length htail
      simp only [length_afterMax, Nat.add_left_cancel_iff] at hd
      have hdup : dup = dup' := by cases dup <;> cases dup' <;> simp_all
      subst dup'
      rw [ih hc' hec]

private noncomputable def renderEquiv (atEnd : Bool) (n : ℕ) :
    {c : List Block // ValidCode c ∧ (render false c).length = n} ≃
      {l : List ℕ // Valid atEnd l ∧ l.length = n} :=
  Equiv.ofBijective
    (fun c => ⟨render atEnd c, render_valid c.2.1 atEnd,
      (render_length atEnd c).trans c.2.2⟩)
    ⟨fun c c' h => Subtype.ext (render_inj c.2.1 c'.2.1 (congrArg Subtype.val h)),
      fun l => by
        obtain ⟨c, hc, he⟩ := code_exists l.2.1
        exact ⟨⟨c, hc, (render_length atEnd c).symm.trans (he ▸ l.2.2)⟩, Subtype.ext he⟩⟩

private def patterns (atEnd : Bool) : Set (Fin 3 → ℕ) :=
  if atEnd then {![0, 0, 0], ![0, 1, 0], ![1, 0, 0], ![1, 1, 0], ![1, 2, 0]}
  else {![0, 0, 0], ![0, 1, 0], ![1, 0, 0], ![1, 0, 1], ![1, 2, 0]}

private theorem allowed_iff (atEnd : Bool) (x y z : ℕ) :
    Allowed atEnd x y z ↔ ∀ p ∈ patterns atEnd, ¬ InvSeqPatternSameOrder x y z p := by
  have h000 : InvSeqPatternSameOrder x y z ![0, 0, 0] ↔ x = y ∧ y = z := by
    simp [invSeqPatternSameOrder_iff]
    omega
  have h010 : InvSeqPatternSameOrder x y z ![0, 1, 0] ↔ x = z ∧ x < y := by
    simp [invSeqPatternSameOrder_iff]
    omega
  have h100 : InvSeqPatternSameOrder x y z ![1, 0, 0] ↔ y = z ∧ y < x := by
    simp [invSeqPatternSameOrder_iff]
    omega
  have h101 : InvSeqPatternSameOrder x y z ![1, 0, 1] ↔ x = z ∧ y < x := by
    simp [invSeqPatternSameOrder_iff]
    omega
  have h110 : InvSeqPatternSameOrder x y z ![1, 1, 0] ↔ x = y ∧ z < x := by
    simp [invSeqPatternSameOrder_iff]
    omega
  have h120 : InvSeqPatternSameOrder x y z ![1, 2, 0] ↔ x < y ∧ z < x := by
    simp [invSeqPatternSameOrder_iff]
    omega
  cases atEnd <;> simp [Allowed, patterns, h000, h010, h100, h101, h110, h120] <;> omega

private theorem valid_ofFn_iff {n : ℕ} (atEnd : Bool) (e : Fin n → ℕ) :
    Valid atEnd (List.ofFn e) ↔
      (∀ i, e i ≤ i) ∧ ∀ p ∈ patterns atEnd, ¬ InvSeqContainsPattern e p := by
  have hbound : IsInversion (List.ofFn e) ↔ ∀ i, e i ≤ i := by
    simp [IsInversion, Fin.forall_iff]
  have htrip : (List.ofFn e).Triplewise (Allowed atEnd) ↔
      ∀ i j k : Fin n, i < j → j < k → Allowed atEnd (e i) (e j) (e k) := by
    rw [List.triplewise_iff_getElem]
    constructor
    · intro h i j k hij hjk
      simpa using h i.val j.val k.val hij hjk (by simp)
    · intro h i j k hij hjk hk
      have hk' : k < n := by simpa using hk
      simpa using h ⟨i, by omega⟩ ⟨j, by omega⟩ ⟨k, hk'⟩ hij hjk
  rw [Valid, hbound, htrip, and_comm]
  refine and_congr_right' ⟨?_, ?_⟩
  · intro h p hp hc
    obtain ⟨i, j, k, hij, hjk, hs⟩ := (invSeqContainsPattern_iff_exists_indices e p).mp hc
    exact (allowed_iff _ _ _ _).mp (h i j k hij hjk) p hp hs
  · intro h i j k hij hjk
    exact (allowed_iff _ _ _ _).mpr fun p hp hs =>
      h p hp ((invSeqContainsPattern_iff_exists_indices e p).mpr ⟨i, j, k, hij, hjk, hs⟩)

private noncomputable def listEquiv (atEnd : Bool) (n : ℕ) :
    {e : Fin n → ℕ // (∀ i, e i ≤ i) ∧ ∀ p ∈ patterns atEnd, ¬ InvSeqContainsPattern e p} ≃
      {l : List ℕ // Valid atEnd l ∧ l.length = n} :=
  Equiv.ofBijective (fun e => ⟨List.ofFn e.1, (valid_ofFn_iff _ _).mpr e.2, List.length_ofFn⟩)
    ⟨fun e e' h => Subtype.ext (List.ofFn_injective (congrArg Subtype.val h)),
      fun ⟨l, hl, hn⟩ => by
        subst n
        refine ⟨⟨l.get, (valid_ofFn_iff _ _).mp ?_⟩, Subtype.ext (List.ofFn_get l)⟩
        simpa using hl⟩

private theorem count_eq (n : ℕ) :
    invSeqAvoidCount (patterns false) n = invSeqAvoidCount (patterns true) n :=
  Nat.card_congr ((listEquiv false n).trans ((renderEquiv false n).symm.trans
    ((renderEquiv true n).trans (listEquiv true n).symm)))

end invSeq_wilf_000_010_100_120_101_110

/-- **I-Wilf equivalence of $\{000, 010, 100, 101, 120\}$ and $\{000, 010, 100, 110, 120\}$.**
Write length-3 patterns as digit strings ($101$ is the pattern $(1, 0, 1)$) and let $|I_n(B)|$ be
the number of inversion sequences of length $n$ that avoid every pattern in the set $B$. Then for
every $n \ge 0$, $|I_n(\{000, 010, 100, 101, 120\})| = |I_n(\{000, 010, 100, 110, 120\})|$.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Theorem 4 (`integers-2024-A76-thm-4`). -/
public theorem invSeq_wilf_000_010_100_120_101_110 :
    invSeqAvoidCount ({![0, 0, 0], ![0, 1, 0], ![1, 0, 0], ![1, 0, 1], ![1, 2, 0]}
        : Set (Fin 3 → ℕ)) =
      invSeqAvoidCount ({![0, 0, 0], ![0, 1, 0], ![1, 0, 0], ![1, 1, 0], ![1, 2, 0]}
          : Set (Fin 3 → ℕ)) := by
  funext n
  exact invSeq_wilf_000_010_100_120_101_110.count_eq n

end MetaMathlibExt
