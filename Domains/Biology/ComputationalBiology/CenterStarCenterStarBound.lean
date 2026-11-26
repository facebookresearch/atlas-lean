/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Center-star multiple alignment is a (2 - 2/k)-approximation

For `k` strings and a pairwise scoring `s` on `Option α` (`none` is a gap)
with zero self-costs (`s x x = 0`, in particular `s none none = 0`), the triangle inequality,
and symmetry, let the center `X c` be an input string minimizing the total optimal-pairwise
distance `∑ⱼ D(X c, Xⱼ)` over the inputs (Gusfield's selection rule) and let `Ac` be a multiple
alignment whose projection onto the rows `c` and `i` is an optimal pairwise alignment of `X c` and
`X i` for every `i`, as for the center-star alignment built by merging optimal pairwise alignments
to `X c` (Lemma 3.1). With `V` the sum-of-pairs value and `A*` an optimal multiple alignment,
`k * V(Ac) ≤ 2 * (k - 1) * V(A*)`, i.e. `V(Ac) / V(A*) ≤ 2 * (k - 1) / k < 2`.

This file defines pairwise alignments (`PairAlignment`), their value (`alignValue`), row erasure
(`erasesTo`), pairwise validity (`IsPairAlignmentOf`), the optimal pairwise value (`pairDist`),
multiple alignments (`MSAlignment`), row erasure for multiple alignments (`msErasesTo`), the
induced pairwise value (`inducedValue`), the sum-of-pairs value (`msaValue`), and the center
total (`centerTotal`). It proves the center-star approximation bound (`centerStar_bound`): the
projection property is the premise, and the star bound `V_{ij}(Ac) ≤ D(X c, X i) + D(X c, X j)`
is derived from the triangle inequality applied column by column.

Sources: D. Gusfield, "Efficient methods for multiple sequence alignment with
guaranteed error bounds", Bulletin of Mathematical Biology 55(1):141-154,
1993, doi:10.1007/BF02460299, Lemma 3.1 and Theorem 3.1.
-/

@[expose] public section

namespace WantedExt.Biology.ComputationalBiology.CenterStarWanted


variable {α : Type*} [DecidableEq α]

/-- A pairwise alignment: two equal-length rows over `Option α`. -/
structure PairAlignment (α : Type*) where
  left : List (Option α)
  right : List (Option α)
  len_eq : left.length = right.length

/-- Value of a pairwise alignment: sum of column scores. -/
def alignValue (s : Option α → Option α → ℝ) (A : PairAlignment α) : ℝ :=
  List.sum ((A.left.zip A.right).map fun p => s p.1 p.2)

/-- Row erasure: deleting gaps recovers the string. -/
def erasesTo (l : List (Option α)) (X : List α) : Prop := l.filterMap id = X

/-- Validity: the rows erase to `X` and `Y`. -/
def IsPairAlignmentOf (A : PairAlignment α) (X Y : List α) : Prop :=
  erasesTo A.left X ∧ erasesTo A.right Y

/-- Optimal pairwise value: infimum of alignment values. Characterized by
`hD_le` (lower bound) and `hD_att` (attainment) in the theorems below. -/
noncomputable def pairDist (s : Option α → Option α → ℝ)
    (X Y : List α) : ℝ :=
  sInf {v | ∃ A : PairAlignment α, IsPairAlignmentOf A X Y ∧
    alignValue s A = v}

/-- A multiple alignment of `k` strings: columns of optional characters. -/
structure MSAlignment (α : Type*) (k : ℕ) where
  cols : List (Fin k → Option α)

/-- Row erasure for multiple alignments. -/
def msErasesTo {k : ℕ} (A : MSAlignment α k) (X : Fin k → List α) : Prop :=
  ∀ j, (A.cols.map fun c => c j).filterMap id = X j

/-- Induced pairwise value of rows `i`, `j`: column scores of the projection. -/
def inducedValue (s : Option α → Option α → ℝ) {k : ℕ}
    (A : MSAlignment α k) (i j : Fin k) : ℝ :=
  List.sum (((A.cols.map fun c => c i).zip
    (A.cols.map fun c => c j)).map fun p => s p.1 p.2)

/-- Sum-of-pairs value over unordered row pairs. -/
def msaValue (s : Option α → Option α → ℝ) {k : ℕ}
    (A : MSAlignment α k) : ℝ :=
  Finset.sum ((Finset.univ : Finset (Fin k × Fin k)).filter
    fun p => p.1 < p.2) fun p => inducedValue s A p.1 p.2

/-- Center total: sum of optimal distances from a candidate center. -/
noncomputable def centerTotal (s : Option α → Option α → ℝ) {k : ℕ}
    (X : Fin k → List α) (C : List α) : ℝ :=
  Finset.sum Finset.univ fun j => pairDist s C (X j)

omit [DecidableEq α] in
private theorem score_nonneg (s : Option α → Option α → ℝ)
    (hdiag : ∀ x : Option α, s x x = 0)
    (htria : ∀ x y z : Option α, s x z ≤ s x y + s y z)
    (hsymm : ∀ x y : Option α, s x y = s y x) (x y : Option α) :
    0 ≤ s x y := by
  have h := htria x y x
  rw [hdiag x, hsymm y x] at h
  linarith

omit [DecidableEq α] in
private theorem alignValue_nonneg (s : Option α → Option α → ℝ)
    (hdiag : ∀ x : Option α, s x x = 0)
    (htria : ∀ x y z : Option α, s x z ≤ s x y + s y z)
    (hsymm : ∀ x y : Option α, s x y = s y x)
    (l₁ l₂ : List (Option α)) :
    0 ≤ List.sum ((l₁.zip l₂).map fun p => s p.1 p.2) := by
  induction l₁ generalizing l₂ with
  | nil => simp [List.zip_nil_left]
  | cons a t ih =>
    cases l₂ with
    | nil => simp [List.zip_nil_right]
    | cons b u =>
      simp only [List.zip_cons_cons, List.map_cons, List.sum_cons]
      exact add_nonneg (score_nonneg s hdiag htria hsymm a b) (ih u)

omit [DecidableEq α] in
private theorem alignValue_swap (s : Option α → Option α → ℝ)
    (hsymm : ∀ x y : Option α, s x y = s y x)
    (l₁ l₂ : List (Option α)) :
    List.sum ((l₁.zip l₂).map fun p => s p.1 p.2) =
      List.sum ((l₂.zip l₁).map fun p => s p.1 p.2) := by
  induction l₁ generalizing l₂ with
  | nil => cases l₂ <;> simp [List.zip_nil_left, List.zip_nil_right]
  | cons a t ih =>
    cases l₂ with
    | nil => simp [List.zip_nil_left, List.zip_nil_right]
    | cons b u =>
      simp only [List.zip_cons_cons, List.map_cons, List.sum_cons,
        hsymm a b, ih u]

omit [DecidableEq α] in
private theorem diag_align_zero (s : Option α → Option α → ℝ)
    (hdiag : ∀ x : Option α, s x x = 0) (l : List (Option α)) :
    List.sum ((l.zip l).map fun p => s p.1 p.2) = 0 := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.zip_cons_cons, List.map_cons, List.sum_cons,
      hdiag a, ih, add_zero]

omit [DecidableEq α] in
private theorem list_triangle (s : Option α → Option α → ℝ)
    (htria : ∀ x y z : Option α, s x z ≤ s x y + s y z)
    {k : ℕ} (l : List (Fin k → Option α)) (i j c : Fin k) :
    List.sum (((l.map fun x => x i).zip
        (l.map fun x => x j)).map fun p => s p.1 p.2) ≤
      List.sum (((l.map fun x => x i).zip
        (l.map fun x => x c)).map fun p => s p.1 p.2) +
      List.sum (((l.map fun x => x c).zip
        (l.map fun x => x j)).map fun p => s p.1 p.2) := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.zip_cons_cons, List.map_cons,
      List.sum_cons]
    linarith [htria (hd i) (hd c) (hd j), ih]

omit [DecidableEq α] in
private theorem pairDist_symm (s : Option α → Option α → ℝ)
    (hsymm : ∀ x y : Option α, s x y = s y x)
    (hD_le : ∀ (U V : List α) (A : PairAlignment α),
      IsPairAlignmentOf A U V → pairDist s U V ≤ alignValue s A)
    (hD_att : ∀ U V : List α, ∃ A : PairAlignment α,
      IsPairAlignmentOf A U V ∧ pairDist s U V = alignValue s A)
    (U V : List α) : pairDist s U V = pairDist s V U := by
  apply le_antisymm
  · obtain ⟨A, hval, hD⟩ := hD_att V U
    have hval' : IsPairAlignmentOf ⟨A.right, A.left, A.len_eq.symm⟩ U V :=
      ⟨hval.2, hval.1⟩
    have hle := hD_le U V _ hval'
    have hswap : alignValue s ⟨A.right, A.left, A.len_eq.symm⟩ =
        alignValue s A :=
      alignValue_swap s hsymm A.right A.left
    rw [hD, ← hswap]
    exact hle
  · obtain ⟨A, hval, hD⟩ := hD_att U V
    have hval' : IsPairAlignmentOf ⟨A.right, A.left, A.len_eq.symm⟩ V U :=
      ⟨hval.2, hval.1⟩
    have hle := hD_le V U _ hval'
    have hswap : alignValue s ⟨A.right, A.left, A.len_eq.symm⟩ =
        alignValue s A :=
      alignValue_swap s hsymm A.right A.left
    rw [hD, ← hswap]
    exact hle

omit [DecidableEq α] in
private theorem pairDist_self (s : Option α → Option α → ℝ)
    (hdiag : ∀ x : Option α, s x x = 0)
    (htria : ∀ x y z : Option α, s x z ≤ s x y + s y z)
    (hsymm : ∀ x y : Option α, s x y = s y x)
    (hD_le : ∀ (U V : List α) (A : PairAlignment α),
      IsPairAlignmentOf A U V → pairDist s U V ≤ alignValue s A)
    (hD_att : ∀ U V : List α, ∃ A : PairAlignment α,
      IsPairAlignmentOf A U V ∧ pairDist s U V = alignValue s A)
    (X : List α) : pairDist s X X = 0 := by
  apply le_antisymm
  · have hval : IsPairAlignmentOf ⟨X.map some, X.map some, rfl⟩ X X := by
      constructor <;> simp [erasesTo]
    have hle := hD_le X X _ hval
    have hzero : alignValue s ⟨X.map some, X.map some, rfl⟩ = 0 :=
      diag_align_zero s hdiag (X.map some)
    rw [hzero] at hle
    exact hle
  · obtain ⟨A, hval, hD⟩ := hD_att X X
    rw [hD]
    exact alignValue_nonneg s hdiag htria hsymm A.left A.right

omit [DecidableEq α] in
private theorem induced_symm (s : Option α → Option α → ℝ)
    (hsymm : ∀ x y : Option α, s x y = s y x)
    {k : ℕ} (A : MSAlignment α k) (i j : Fin k) :
    inducedValue s A i j = inducedValue s A j i := by
  unfold inducedValue
  exact alignValue_swap s hsymm _ _

omit [DecidableEq α] in
private theorem induced_ge_pairDist (s : Option α → Option α → ℝ) {k : ℕ}
    (X : Fin k → List α)
    (hD_le : ∀ (U V : List α) (A : PairAlignment α),
      IsPairAlignmentOf A U V → pairDist s U V ≤ alignValue s A)
    (A : MSAlignment α k) (hac : msErasesTo A X) (i j : Fin k) :
    pairDist s (X i) (X j) ≤ inducedValue s A i j := by
  have hval : IsPairAlignmentOf
      ⟨A.cols.map fun c => c i, A.cols.map fun c => c j, by simp⟩
      (X i) (X j) := ⟨hac i, hac j⟩
  exact hD_le (X i) (X j) _ hval

private theorem sum_partition {k : ℕ} (g : Fin k × Fin k → ℝ) :
    ∑ p ∈ (Finset.univ : Finset (Fin k × Fin k)), g p =
      ∑ p ∈ (Finset.univ : Finset (Fin k × Fin k)).filter
        fun p => p.1 < p.2, g p +
      ∑ p ∈ (Finset.univ : Finset (Fin k × Fin k)).filter
        fun p => p.2 < p.1, g p +
      ∑ p ∈ (Finset.univ : Finset (Fin k × Fin k)).filter
        fun p => p.1 = p.2, g p := by
  have h1 : ∑ p ∈ (Finset.univ : Finset (Fin k × Fin k)).filter
      fun p => p.1 < p.2, g p +
      ∑ p ∈ (Finset.univ : Finset (Fin k × Fin k)).filter
      fun p => ¬ p.1 < p.2, g p =
      ∑ p ∈ (Finset.univ : Finset (Fin k × Fin k)), g p :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have h2 : ∑ p ∈ ((Finset.univ : Finset (Fin k × Fin k)).filter
      fun p => ¬ p.1 < p.2).filter fun p => p.2 < p.1, g p +
      ∑ p ∈ ((Finset.univ : Finset (Fin k × Fin k)).filter
      fun p => ¬ p.1 < p.2).filter fun p => ¬ p.2 < p.1, g p =
      ∑ p ∈ (Finset.univ : Finset (Fin k × Fin k)).filter
      fun p => ¬ p.1 < p.2, g p :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have hG : ((Finset.univ : Finset (Fin k × Fin k)).filter
      (fun p => ¬ p.1 < p.2)).filter (fun p => p.2 < p.1) =
      (Finset.univ : Finset (Fin k × Fin k)).filter
      (fun p => p.2 < p.1) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      exact h.2
    · intro h
      exact ⟨not_lt.mpr (le_of_lt h), h⟩
  have hD : ((Finset.univ : Finset (Fin k × Fin k)).filter
      (fun p => ¬ p.1 < p.2)).filter (fun p => ¬ p.2 < p.1) =
      (Finset.univ : Finset (Fin k × Fin k)).filter
      (fun p => p.1 = p.2) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      exact le_antisymm (not_lt.mp h.2) (not_lt.mp h.1)
    · intro h
      rw [h]
      exact ⟨lt_irrefl _, lt_irrefl _⟩
  rw [hG, hD] at h2
  linarith [h1, h2]

private theorem sum_swap_eq {k : ℕ} (g : Fin k × Fin k → ℝ) :
    ∑ p ∈ (Finset.univ : Finset (Fin k × Fin k)).filter
      fun p => p.2 < p.1, g p =
    ∑ p ∈ (Finset.univ : Finset (Fin k × Fin k)).filter
      fun p => p.1 < p.2, g p.swap := by
  apply Finset.sum_bij (fun p _ => p.swap)
  · intro p hp
    obtain ⟨a, b⟩ := p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact hp
  · intro p _ q _ h
    have h2 := congrArg Prod.swap h
    simpa using h2
  · intro q hq
    obtain ⟨a, b⟩ := q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    exact ⟨(b, a), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩, rfl⟩
  · intro p _
    rw [Prod.swap_swap]

private theorem sum_diag_eq {k : ℕ} (g : Fin k × Fin k → ℝ) :
    ∑ p ∈ (Finset.univ : Finset (Fin k × Fin k)).filter
      fun p => p.1 = p.2, g p =
    ∑ i, g (i, i) := by
  apply Finset.sum_bij (fun p _ => p.1)
  · intro p _
    exact Finset.mem_univ _
  · intro p hp q hq h
    obtain ⟨a, b⟩ := p
    obtain ⟨c, d⟩ := q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq h
    rw [Prod.mk.injEq]
    constructor
    · exact h
    · rw [← hp, ← hq, h]
  · intro b _
    exact ⟨(b, b), Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, rfl⟩
  · intro a ha
    obtain ⟨x, y⟩ := a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    subst ha
    rfl

private theorem sum_unordered_add {k : ℕ} (f : Fin k → ℝ) :
    ∑ p ∈ (Finset.univ : Finset (Fin k × Fin k)).filter
      fun p => p.1 < p.2, (f p.1 + f p.2) =
    ((k : ℝ) - 1) * ∑ i, f i := by
  have hpart := sum_partition (fun p : Fin k × Fin k => f p.1 + f p.2)
  have h1 : ∑ p ∈ (Finset.univ : Finset (Fin k × Fin k)), f p.1 =
      (k : ℝ) * ∑ i, f i := by
    rw [← Finset.univ_product_univ, Finset.sum_product]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    rw [← Finset.mul_sum]
  have h2 : ∑ p ∈ (Finset.univ : Finset (Fin k × Fin k)), f p.2 =
      (k : ℝ) * ∑ i, f i := by
    rw [← Finset.univ_product_univ, Finset.sum_product_right]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    rw [← Finset.mul_sum]
  have hfull : ∑ p ∈ (Finset.univ : Finset (Fin k × Fin k)),
      (f p.1 + f p.2) = 2 * (k : ℝ) * ∑ i, f i := by
    rw [Finset.sum_add_distrib, h1, h2]
    ring
  have hswap : ∑ p ∈ (Finset.univ : Finset (Fin k × Fin k)).filter
      fun p => p.2 < p.1, (f p.1 + f p.2) =
      ∑ p ∈ (Finset.univ : Finset (Fin k × Fin k)).filter
      fun p => p.1 < p.2, (f p.1 + f p.2) := by
    have h := sum_swap_eq (fun p : Fin k × Fin k => f p.1 + f p.2)
    rw [h]
    apply Finset.sum_congr rfl
    rintro ⟨a, b⟩ -
    exact add_comm _ _
  have hdiag : ∑ p ∈ (Finset.univ : Finset (Fin k × Fin k)).filter
      fun p => p.1 = p.2, (f p.1 + f p.2) = 2 * ∑ i, f i := by
    have h := sum_diag_eq (fun p : Fin k × Fin k => f p.1 + f p.2)
    have h2' : (∑ i : Fin k, (f i + f i)) = 2 * ∑ i, f i := by
      rw [Finset.sum_add_distrib]
      ring
    rw [h]
    exact h2'
  have hU : ∑ p ∈ (Finset.univ : Finset (Fin k × Fin k)),
      (f p.1 + f p.2) =
      2 * (∑ p ∈ (Finset.univ : Finset (Fin k × Fin k)).filter
        fun p => p.1 < p.2, (f p.1 + f p.2)) + 2 * ∑ i, f i := by
    linarith [hpart, hswap, hdiag]
  rw [hfull] at hU
  calc (∑ p ∈ (Finset.univ : Finset (Fin k × Fin k)).filter
      fun p => p.1 < p.2, (f p.1 + f p.2))
      = (k : ℝ) * (∑ i, f i) - ∑ i, f i := by linarith [hU]
    _ = ((k : ℝ) - 1) * ∑ i, f i := by ring

private theorem sum_all_eq_two_unordered {k : ℕ} (d : Fin k → Fin k → ℝ)
    (hsymm : ∀ i j, d i j = d j i) (hself : ∀ i, d i i = 0) :
    ∑ i, ∑ j, d i j =
    2 * ∑ p ∈ (Finset.univ : Finset (Fin k × Fin k)).filter
      fun p => p.1 < p.2, d p.1 p.2 := by
  have hpart := sum_partition (fun p : Fin k × Fin k => d p.1 p.2)
  have hfull : ∑ p ∈ (Finset.univ : Finset (Fin k × Fin k)), d p.1 p.2 =
      ∑ i, ∑ j, d i j := by
    rw [← Finset.univ_product_univ, Finset.sum_product]
  have hswap : ∑ p ∈ (Finset.univ : Finset (Fin k × Fin k)).filter
      fun p => p.2 < p.1, d p.1 p.2 =
      ∑ p ∈ (Finset.univ : Finset (Fin k × Fin k)).filter
      fun p => p.1 < p.2, d p.1 p.2 := by
    have h := sum_swap_eq (fun p : Fin k × Fin k => d p.1 p.2)
    rw [h]
    apply Finset.sum_congr rfl
    rintro ⟨a, b⟩ -
    exact hsymm b a
  have hdiag : ∑ p ∈ (Finset.univ : Finset (Fin k × Fin k)).filter
      fun p => p.1 = p.2, d p.1 p.2 = 0 := by
    have h := sum_diag_eq (fun p : Fin k × Fin k => d p.1 p.2)
    rw [h]
    simp [hself]
  linarith [hpart, hfull, hswap, hdiag]

-- The `DecidableEq` instance is part of the pinned statement signature.
set_option linter.unusedDecidableInType false in
/-- **Center-star approximation** (Gusfield 1993, Theorem 3.1): hypotheses are
a gap scoring with `s none none = 0` (`hgap`) and zero self-costs `s x x = 0` for every
`x : Option α` (`hdiag`), the triangle inequality
(`htria`), explicit symmetry (`hsymm`), at least two strings (`hk`), the
`pairDist` characterization (`hD_le`, `hD_att`), a center index `c : Fin k`
whose input string minimizes the center total over the inputs,
`∑ j, D (X c) (X j) ≤ ∑ j, D (X i) (X j)` for every `i : Fin k` (`hcenter`, Gusfield's selection
rule), a multiple alignment `Ac` of `X` (`hac`) whose projection onto the center row `c` and
each row `i` is an optimal pairwise alignment, `inducedValue s Ac c i = D (X c) (X i)` for every
`i` (`hproj`, the center-star property of Gusfield's Lemma 3.1), and an optimal alignment `Astar`
valid for `X` and minimal (`hopt`). Conclusion: `k * V(Ac) ≤ 2 * (k - 1) * V(Astar)`. The star
bound `V_{ij}(Ac) ≤ D (X c) (X i) + D (X c) (X j)` is not assumed; it follows from `hproj` and the
triangle inequality.

Source: Gusfield (1993), Theorem 3.1 (via Lemma 3.1). -/
theorem centerStar_bound (s : Option α → Option α → ℝ)
    (hgap : s none none = 0)
    (hdiag : ∀ x : Option α, s x x = 0)
    (htria : ∀ x y z : Option α, s x z ≤ s x y + s y z)
    (hsymm : ∀ x y : Option α, s x y = s y x)
    (k : ℕ) (hk : 2 ≤ k)
    (X : Fin k → List α)
    (hD_le : ∀ (U V : List α) (A : PairAlignment α),
      IsPairAlignmentOf A U V → pairDist s U V ≤ alignValue s A)
    (hD_att : ∀ U V : List α, ∃ A : PairAlignment α,
      IsPairAlignmentOf A U V ∧ pairDist s U V = alignValue s A)
    (c : Fin k)
    (hcenter : ∀ i : Fin k, centerTotal s X (X c) ≤ centerTotal s X (X i))
    (Ac : MSAlignment α k)
    (hac : msErasesTo Ac X)
    (hproj : ∀ i, inducedValue s Ac c i = pairDist s (X c) (X i))
    (Astar : MSAlignment α k)
    (hastar : msErasesTo Astar X)
    (hopt : ∀ A' : MSAlignment α k, msErasesTo A' X →
      msaValue s Astar ≤ msaValue s A') :
    (k : ℝ) * msaValue s Ac ≤ 2 * ((k : ℝ) - 1) * msaValue s Astar := by
  have _ : DecidableEq α := by assumption
  have _ := hgap
  have _ := hac
  have _ := hopt
  have hstar : ∀ i j : Fin k, inducedValue s Ac i j ≤
      pairDist s (X c) (X i) + pairDist s (X c) (X j) := by
    intro i j
    have htri : inducedValue s Ac i j ≤
        inducedValue s Ac i c + inducedValue s Ac c j :=
      list_triangle s htria Ac.cols i j c
    have esymm : inducedValue s Ac i c = inducedValue s Ac c i :=
      induced_symm s hsymm Ac i c
    rw [esymm, hproj i, hproj j] at htri
    exact htri
  have hAc : msaValue s Ac ≤
      ((k : ℝ) - 1) * centerTotal s X (X c) := by
    have hsum : ∑ p ∈ (Finset.univ : Finset (Fin k × Fin k)).filter
        fun p => p.1 < p.2,
        (pairDist s (X c) (X p.1) + pairDist s (X c) (X p.2)) =
        ((k : ℝ) - 1) * ∑ m, pairDist s (X c) (X m) :=
      sum_unordered_add (fun m : Fin k => pairDist s (X c) (X m))
    have hle : msaValue s Ac ≤ ∑ p ∈ (Finset.univ : Finset
        (Fin k × Fin k)).filter fun p => p.1 < p.2,
        (pairDist s (X c) (X p.1) + pairDist s (X c) (X p.2)) :=
      Finset.sum_le_sum (fun p _ => hstar p.1 p.2)
    rw [hsum] at hle
    exact hle
  have hdouble : (∑ i : Fin k, ∑ j : Fin k, pairDist s (X i) (X j)) =
      2 * ∑ p ∈ (Finset.univ : Finset (Fin k × Fin k)).filter
        fun p => p.1 < p.2, pairDist s (X p.1) (X p.2) :=
    sum_all_eq_two_unordered (fun i j : Fin k => pairDist s (X i) (X j))
      (fun i j => pairDist_symm s hsymm hD_le hD_att (X i) (X j))
      (fun i => pairDist_self s hdiag htria hsymm hD_le hD_att (X i))
  have hcenter_sum : (k : ℝ) * centerTotal s X (X c) ≤
      ∑ i : Fin k, ∑ j : Fin k, pairDist s (X i) (X j) := by
    have hle : (∑ _i : Fin k, centerTotal s X (X c)) ≤
        ∑ i : Fin k, centerTotal s X (X i) :=
      Finset.sum_le_sum (fun i _ => hcenter i)
    have hconst : (∑ _i : Fin k, centerTotal s X (X c)) =
        (k : ℝ) * centerTotal s X (X c) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
    rw [hconst] at hle
    exact hle
  have hlow : ∑ p ∈ (Finset.univ : Finset (Fin k × Fin k)).filter
      fun p => p.1 < p.2, pairDist s (X p.1) (X p.2) ≤
      msaValue s Astar :=
    Finset.sum_le_sum
      (fun p _ => induced_ge_pairDist s X hD_le Astar hastar p.1 p.2)
  have hkey : (k : ℝ) * centerTotal s X (X c) ≤
      2 * msaValue s Astar := by
    linarith [hcenter_sum, hdouble, hlow]
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
    have h1k : (1 : ℕ) ≤ k := le_trans (by decide) hk
    have h : ((1 : ℕ) : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr h1k
    rwa [Nat.cast_one] at h
  calc (k : ℝ) * msaValue s Ac
      ≤ (k : ℝ) * (((k : ℝ) - 1) * centerTotal s X (X c)) :=
        mul_le_mul_of_nonneg_left hAc hk0
    _ = ((k : ℝ) - 1) * ((k : ℝ) * centerTotal s X (X c)) := by ring
    _ ≤ ((k : ℝ) - 1) * (2 * msaValue s Astar) :=
        mul_le_mul_of_nonneg_left hkey (by linarith)
    _ = 2 * ((k : ℝ) - 1) * msaValue s Astar := by ring

end WantedExt.Biology.ComputationalBiology.CenterStarWanted
