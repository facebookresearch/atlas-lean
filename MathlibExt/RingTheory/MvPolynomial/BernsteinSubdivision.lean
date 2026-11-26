/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.MvPolynomial.BernsteinBounds
public import MathlibExt.RingTheory.Polynomial.BernsteinSubdivision
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Logic.Equiv.Prod

/-!
# Coordinatewise subdivision of tensor Bernstein expansions

De Casteljau coefficients reconstruct the two affine restrictions of a tensor
Bernstein expansion and retain every parent coefficient enclosure for cuts
in the closed unit interval. Reference: A. P. Smith (2012), *Enclosure Methods
for Systems of Polynomial Equations and Inequalities*, §3.3.2, equation (3.27),
https://d-nb.info/1028327854/34.
-/

@[expose] public section

namespace MvPolynomial

open Finset bernsteinPolynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The tensor Bernstein expansion with coordinate degrees `n` and real
control coefficients `c`. The finite sum uses precisely `k i ≤ n i`; values
of `c` outside those indices have no effect. -/
noncomputable def bernsteinExpansion (n : ι → ℕ) (c : (ι → ℕ) → ℝ) : MvPolynomial ι ℝ :=
  ∑ k : (i : ι) → Fin (n i + 1), C (c fun i => k i) * bernstein n (fun i => k i)

/-- Left-child tensor control coefficients for a cut at parameter `t` in
coordinate `r`: the `k r`-th diagonal of the de Casteljau triangle. The other
coordinate indices are unchanged. -/
noncomputable def bernsteinSubdivideLeft (r : ι) (t : ℝ) (c : (ι → ℕ) → ℝ)
    (k : ι → ℕ) : ℝ :=
  deCasteljau t (fun j => c (Function.update k r j)) (k r)

/-- Right-child tensor control coefficients for degree vector `n` and a cut
at parameter `t` in coordinate `r`. At a valid index `k r ≤ n r`, use depth
`n r - k r` starting at that index. Subtraction is truncated outside this range. -/
noncomputable def bernsteinSubdivideRight (n : ι → ℕ) (r : ι) (t : ℝ)
    (c : (ι → ℕ) → ℝ) (k : ι → ℕ) : ℝ :=
  deCasteljau t (fun j => c (Function.update k r (k r + j))) (n r - k r)

private def splitIndex (n : ι → ℕ) (r : ι)
    (z : (i : {i // i ≠ r}) → Fin (n i + 1)) (j : ℕ) (i : ι) : ℕ :=
  if h : i = r then j else z ⟨i, h⟩

omit [Fintype ι] in
@[simp] private theorem splitIndex_self (n : ι → ℕ) (r : ι)
    (z : (i : {i // i ≠ r}) → Fin (n i + 1)) (j : ℕ) : splitIndex n r z j r = j := by
  simp [splitIndex]

omit [Fintype ι] in
@[simp] private theorem update_splitIndex (n : ι → ℕ) (r : ι)
    (z : (i : {i // i ≠ r}) → Fin (n i + 1)) (j l : ℕ) :
    Function.update (splitIndex n r z j) r l = splitIndex n r z l := by
  funext i
  by_cases hi : i = r
  · subst i
    simp
  · simp [splitIndex, hi]

private theorem prod_split (r : ι) (f : ι → ℝ) :
    (∏ i, f i) = f r * ∏ i : {i // i ≠ r}, f i := by
  rw [← mul_prod_erase univ f (mem_univ r)]
  congr 1
  exact prod_subtype (univ.erase r) (by simp) f

private theorem eval_bernsteinExpansion_split (n : ι → ℕ) (c : (ι → ℕ) → ℝ)
    (x : ι → ℝ) (r : ι) :
    eval x (bernsteinExpansion n c) =
      ∑ z : (i : {i // i ≠ r}) → Fin (n i + 1),
        deCasteljau (x r) (fun j => c (splitIndex n r z j)) (n r) *
          ∏ i : {i // i ≠ r}, (bernsteinPolynomial ℝ (n i) (z i)).eval (x i) := by
  simp only [bernsteinExpansion, map_sum, map_mul, eval_C, eval_bernstein]
  let e := Equiv.piSplitAt r (fun i => Fin (n i + 1))
  rw [← e.symm.sum_comp (fun k : (i : ι) → Fin (n i + 1) =>
    c (fun i => k i) * ∏ i, (bernsteinPolynomial ℝ (n i) (k i)).eval (x i))]
  rw [Fintype.sum_prod_type, sum_comm]
  apply sum_congr rfl
  intro z _
  rw [deCasteljau_eq_sum, sum_range, sum_mul]
  apply sum_congr rfl
  intro j _
  have hindex : (fun i => ((e.symm (j, z)) i : ℕ)) = splitIndex n r z j := by
    funext i
    by_cases hi : i = r
    · subst i
      simp [e, Equiv.piSplitAt, splitIndex]
    · simp [e, Equiv.piSplitAt, splitIndex, hi]
  rw [hindex, prod_split r]
  have hprod : (∏ i : {i // i ≠ r},
      (bernsteinPolynomial ℝ (n i) ((e.symm (j, z)) i)).eval (x i)) =
      ∏ i : {i // i ≠ r}, (bernsteinPolynomial ℝ (n i) (z i)).eval (x i) := by
    apply prod_congr rfl
    intro i _
    simp [e, Equiv.piSplitAt, i.property]
  rw [hprod]
  simp [e, Equiv.piSplitAt, mul_assoc]

/-- Left subdivision reconstructs the original tensor Bernstein expansion
at the point with coordinate `r` replaced by `t*x r`. This identity holds
for every real cut parameter and every real evaluation point. -/
theorem eval_bernsteinExpansion_subdivideLeft (n : ι → ℕ) (r : ι) (t : ℝ)
    (c : (ι → ℕ) → ℝ) (x : ι → ℝ) :
    eval x (bernsteinExpansion n (bernsteinSubdivideLeft r t c)) =
      eval (Function.update x r (t * x r)) (bernsteinExpansion n c) := by
  rw [eval_bernsteinExpansion_split n _ x r,
    eval_bernsteinExpansion_split n _ _ r]
  apply sum_congr rfl
  intro z _
  simp only [bernsteinSubdivideLeft, splitIndex_self, update_splitIndex,
    deCasteljau_left, Function.update_self]
  rw [mul_comm (x r) t]
  congr 1
  apply prod_congr rfl
  intro i _
  rw [Function.update_of_ne i.property]

/-- Right subdivision reconstructs the original tensor Bernstein expansion
at the point with coordinate `r` replaced by `t+(1-t)*x r`. This identity
holds for every real cut parameter and every real evaluation point. -/
theorem eval_bernsteinExpansion_subdivideRight (n : ι → ℕ) (r : ι) (t : ℝ)
    (c : (ι → ℕ) → ℝ) (x : ι → ℝ) :
    eval x (bernsteinExpansion n (bernsteinSubdivideRight n r t c)) =
      eval (Function.update x r (t + (1 - t) * x r)) (bernsteinExpansion n c) := by
  rw [eval_bernsteinExpansion_split n _ x r,
    eval_bernsteinExpansion_split n _ _ r]
  apply sum_congr rfl
  intro z _
  simp only [bernsteinSubdivideRight, splitIndex_self, update_splitIndex,
    Function.update_self]
  have h := deCasteljau_right t (x r) (fun j => c (splitIndex n r z j)) (n r)
  have hrow : deCasteljau (x r)
      (fun j => deCasteljau t (fun l => c (splitIndex n r z (j + l))) (n r - j))
      (n r) = deCasteljau (t + (1 - t) * x r) (fun j => c (splitIndex n r z j)) (n r) := by
    simpa only [Nat.add_comm] using h
  rw [hrow]
  congr 1
  apply prod_congr rfl
  intro i _
  rw [Function.update_of_ne i.property]

omit [Fintype ι] in
/-- At a cut parameter in `[0,1]`, every valid left-child coefficient lies
in any interval containing all valid parent coefficients. Coordinate degrees
may be zero and cuts at either endpoint are included. -/
theorem bernsteinSubdivideLeft_mem_Icc {n : ι → ℕ} {r : ι} {t L U : ℝ}
    {c : (ι → ℕ) → ℝ} (ht : t ∈ Set.Icc 0 1)
    (hc : ∀ k, (∀ i, k i ≤ n i) → c k ∈ Set.Icc L U)
    (k : ι → ℕ) (hk : ∀ i, k i ≤ n i) :
    bernsteinSubdivideLeft r t c k ∈ Set.Icc L U := by
  apply deCasteljau_mem_Icc ht
  intro j hj
  apply hc
  intro i
  by_cases hi : i = r
  · subst i
    simp only [Function.update_self]
    exact hj.trans (hk r)
  · simpa [Function.update_of_ne hi] using hk i

omit [Fintype ι] in
/-- At a cut parameter in `[0,1]`, every valid right-child coefficient lies
in any interval containing all valid parent coefficients. Coordinate degrees
may be zero and cuts at either endpoint are included. -/
theorem bernsteinSubdivideRight_mem_Icc {n : ι → ℕ} {r : ι} {t L U : ℝ}
    {c : (ι → ℕ) → ℝ} (ht : t ∈ Set.Icc 0 1)
    (hc : ∀ k, (∀ i, k i ≤ n i) → c k ∈ Set.Icc L U)
    (k : ι → ℕ) (hk : ∀ i, k i ≤ n i) :
    bernsteinSubdivideRight n r t c k ∈ Set.Icc L U := by
  apply deCasteljau_mem_Icc ht
  intro j hj
  apply hc
  intro i
  by_cases hi : i = r
  · subst i
    simp only [Function.update_self]
    have := hk r
    omega
  · simpa [Function.update_of_ne hi] using hk i

/-- The left child of the coefficient net of a box pullback reconstructs
exactly the pullback along the left affine restriction, which replaces the
`r`-th upper endpoint by `(1 - t) * a r + t * b r`. For ordered
endpoints `a r ≤ b r` and `t ∈ [0, 1]` it is the left subbox; the identity
holds for arbitrary real endpoints and cut parameters, including zero
widths. The degree bound is coordinatewise. -/
theorem bernsteinExpansion_subdivideLeft_box {n : ι → ℕ} {p : MvPolynomial ι ℝ}
    (hp : ∀ i, p.degreeOf i ≤ n i) (a b : ι → ℝ) (r : ι) (t : ℝ) :
    bernsteinExpansion n (bernsteinSubdivideLeft r t
      (bernsteinCoeff n (boxPullback a b p))) =
      boxPullback a (Function.update b r ((1 - t) * a r + t * b r)) p := by
  have hrepr : bernsteinExpansion n (bernsteinCoeff n (boxPullback a b p)) =
      boxPullback a b p :=
    (eq_sum_bernstein (fun i => (degreeOf_boxPullback_le a b p i).trans (hp i))).symm
  apply MvPolynomial.funext
  intro x
  rw [eval_bernsteinExpansion_subdivideLeft, hrepr, eval_boxPullback, eval_boxPullback]
  congr 2
  funext i
  by_cases hi : i = r
  · subst i
    simp only [Function.update_self]
    ring
  · simp [Function.update_of_ne hi]

/-- The right child of the coefficient net of a box pullback reconstructs
exactly the pullback along the right affine restriction, which replaces the
`r`-th lower endpoint by `(1 - t) * a r + t * b r`. For ordered
endpoints `a r ≤ b r` and `t ∈ [0, 1]` it is the right subbox; the identity
holds for arbitrary real endpoints and cut parameters, including zero
widths. The degree bound is coordinatewise. -/
theorem bernsteinExpansion_subdivideRight_box {n : ι → ℕ} {p : MvPolynomial ι ℝ}
    (hp : ∀ i, p.degreeOf i ≤ n i) (a b : ι → ℝ) (r : ι) (t : ℝ) :
    bernsteinExpansion n (bernsteinSubdivideRight n r t
      (bernsteinCoeff n (boxPullback a b p))) =
      boxPullback (Function.update a r ((1 - t) * a r + t * b r)) b p := by
  have hrepr : bernsteinExpansion n (bernsteinCoeff n (boxPullback a b p)) =
      boxPullback a b p :=
    (eq_sum_bernstein (fun i => (degreeOf_boxPullback_le a b p i).trans (hp i))).symm
  apply MvPolynomial.funext
  intro x
  rw [eval_bernsteinExpansion_subdivideRight, hrepr, eval_boxPullback, eval_boxPullback]
  congr 2
  funext i
  by_cases hi : i = r
  · subst i
    simp only [Function.update_self]
    ring
  · simp [Function.update_of_ne hi]

/-- Any interval containing all valid control coefficients contains every
value of their tensor Bernstein expansion on the closed unit cube. This
also applies to child nets and does not require canonical coefficient extraction. -/
theorem eval_bernsteinExpansion_mem_Icc {n : ι → ℕ} {c : (ι → ℕ) → ℝ}
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Icc 0 1) {L U : ℝ}
    (hc : ∀ k, (∀ i, k i ≤ n i) → c k ∈ Set.Icc L U) :
    eval x (bernsteinExpansion n c) ∈ Set.Icc L U := by
  simp only [bernsteinExpansion, map_sum, map_mul, eval_C]
  have hk (k : (i : ι) → Fin (n i + 1)) := hc (fun i => k i)
    (fun i => Nat.le_of_lt_succ (k i).isLt)
  constructor
  · calc
      L = ∑ k : (i : ι) → Fin (n i + 1), L * eval x (bernstein n (fun i => k i)) := by
        rw [← mul_sum, sum_eval_bernstein, mul_one]
      _ ≤ _ := sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hk k).1
        (eval_bernstein_nonneg _ _ hx)
  · calc
      _ ≤ ∑ k : (i : ι) → Fin (n i + 1), U * eval x (bernstein n (fun i => k i)) :=
        sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hk k).2
          (eval_bernstein_nonneg _ _ hx)
      _ = U := by rw [← mul_sum, sum_eval_bernstein, mul_one]

omit [Fintype ι] in
/-- Cutting one coordinate of a closed box at a point between its endpoints
covers the parent box by the two closed child boxes. Other coordinates may
be degenerate; the two children meet on the cutting face. -/
theorem _root_.Set.Icc_eq_union_update (a b : ι → ℝ) (r : ι) {m : ℝ}
    (hm : m ∈ Set.Icc (a r) (b r)) :
    Set.Icc a b = Set.Icc a (Function.update b r m) ∪
      Set.Icc (Function.update a r m) b := by
  ext x
  constructor
  · intro hx
    rcases le_total (x r) m with h | h
    · left
      refine ⟨hx.1, fun i => ?_⟩
      by_cases hi : i = r
      · subst i; simpa using h
      · simpa [Function.update_of_ne hi] using hx.2 i
    · right
      refine ⟨fun i => ?_, hx.2⟩
      by_cases hi : i = r
      · subst i; simpa using h
      · simpa [Function.update_of_ne hi] using hx.1 i
  · rintro (hx | hx)
    · refine ⟨hx.1, fun i => ?_⟩
      by_cases hi : i = r
      · subst i
        exact (by simpa using hx.2 r : x r ≤ m).trans hm.2
      · simpa [Function.update_of_ne hi] using hx.2 i
    · refine ⟨fun i => ?_, hx.2⟩
      by_cases hi : i = r
      · subst i
        exact hm.1.trans (by simpa using hx.1 r : m ≤ x r)
      · simpa [Function.update_of_ne hi] using hx.1 i

/-- For a real polynomial in finitely many variables, suppose its affine box
pullback equals the degree-`n` tensor Bernstein expansion with coefficients `c`.
If every valid coefficient `c k` lies in `[L,U]`, then the polynomial value at
every point of that closed box lies in `[L,U]`. The representation may use
subdivided coefficients, and zero-width coordinates are allowed. -/
theorem eval_mem_Icc_of_bernsteinExpansion_box {n : ι → ℕ}
    {p : MvPolynomial ι ℝ} {a b : ι → ℝ} {c : (ι → ℕ) → ℝ}
    (hrep : bernsteinExpansion n c = boxPullback a b p)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Icc (a i) (b i)) {L U : ℝ}
    (hc : ∀ k, (∀ i, k i ≤ n i) → c k ∈ Set.Icc L U) :
    eval x p ∈ Set.Icc L U := by
  have hparam (i : ι) : ∃ t ∈ Set.Icc (0 : ℝ) 1,
      a i + (b i - a i) * t = x i := by
    by_cases h : a i = b i
    · refine ⟨0, by norm_num, ?_⟩
      have heq : x i = a i := le_antisymm (h ▸ (hx i).2) (hx i).1
      simp [heq]
    · have hpos : 0 < b i - a i :=
        sub_pos.mpr (lt_of_le_of_ne ((hx i).1.trans (hx i).2) h)
      refine ⟨(x i - a i) / (b i - a i),
        ⟨div_nonneg (sub_nonneg.mpr (hx i).1) hpos.le,
          (div_le_one hpos).mpr (sub_le_sub_right (hx i).2 _)⟩, ?_⟩
      rw [mul_div_cancel₀ _ hpos.ne']
      ring
  choose t ht heq using hparam
  have h := eval_bernsteinExpansion_mem_Icc ht hc
  rw [hrep, eval_boxPullback] at h
  simpa only [heq] using h

end MvPolynomial
