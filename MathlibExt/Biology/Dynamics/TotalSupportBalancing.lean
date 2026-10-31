/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Dynamics.SystemsBiology
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Symmetric matrix balancing under total support

A symmetric nonnegative matrix `A` with total support (`HasTotalSupport`: nonzero, and every
positive entry lies on a positive diagonal) has a positive vector `d` such that
`diag(d) A diag(d)` is doubly stochastic (Csima & Datta 1972). Together with the necessity
direction `hasTotalSupport_of_balancing` this characterizes the symmetric nonnegative matrices
that can be balanced, e.g. Hi-C contact maps under iterative correction (Imakaev et al. 2012).

The proof here is variational, not the original argument of Csima & Datta. Total support
gives a doubly stochastic `B` with the same zero pattern as `A` (an average of permutation
matrices). The function `G(s) = ∑_{A i j > 0} (A i j * exp (s i j) - B i j * s i j)`, plus
`s i j ^ 2` off the pattern, is coercive on `Fin n × Fin n → ℝ`, so it attains its minimum on
the closed subspace of the `s` with `s i j = x i + x j` on the pattern and `0` off it. Since
`B` is doubly stochastic, `G` there equals `∑ i j, A i j * exp (x i + x j) - 2 ∑ i, x i`, so a
minimizer `x` is stationary: `∑ j, A k j * exp (x k + x j) = 1` for each `k`, and `d = exp x`
balances `A`. Uniqueness of `d` fails in general (e.g. for `!![0, 1; 1, 0]`, where every
`d = (t, t⁻¹)` works) and is not claimed.

## Main results

* `exists_symmetric_balancing_of_hasTotalSupport`: total support suffices.
* `exists_symmetric_balancing_iff_hasTotalSupport`: for `0 < n`, a symmetric nonnegative matrix
  can be balanced if and only if it has total support. (For `n = 0` the empty matrix is balanced
  but has no total support, since `HasTotalSupport` asks for a nonzero matrix.)

Convergence of the Sinkhorn/ICE iteration for such matrices is not covered.

## References

* J. Csima and B. N. Datta, "The DAD theorem for symmetric non-negative matrices", J. Combin.
  Theory Ser. A 12 (1972) 147–152.
* R. Sinkhorn and P. Knopp, "Concerning nonnegative matrices and doubly stochastic matrices",
  Pacific J. Math. 21 (1967) 343–348.
* M. Imakaev et al., "Iterative correction of Hi-C data reveals hallmarks of chromosome
  organization", Nat. Methods 9 (2012) 999–1003.
-/

@[expose] public section

namespace MathlibExt.Biology.Dynamics.SystemsBiology

open Matrix

variable {n : ℕ}

/-- Total support gives a doubly stochastic matrix with the same zero pattern: the average of
the permutation matrices of positive diagonals through the positive entries. -/
private theorem exists_doublyStochastic_pattern {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hts : HasTotalSupport A) :
    ∃ B : Matrix (Fin n) (Fin n) ℝ, (∀ i j, 0 ≤ B i j) ∧ (∀ i j, 0 < A i j → 0 < B i j) ∧
      (∀ i j, A i j = 0 → B i j = 0) ∧ (∀ i, ∑ j, B i j = 1) ∧ ∀ j, ∑ i, B i j = 1 := by
  classical
  obtain ⟨hA0, hσ⟩ := hts
  set P := Finset.univ.filter fun q : Fin n × Fin n => 0 < A q.1 q.2 with hPdef
  have hP : P.Nonempty := by
    by_contra h
    apply hA0
    ext i j
    have : (i, j) ∉ P := fun hm => h ⟨_, hm⟩
    simp only [P, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at this
    exact le_antisymm this (hA i j)
  choose! σ hσi hσk using fun q : Fin n × Fin n => fun h : 0 < A q.1 q.2 => hσ q.1 q.2 h
  have hcard : (0 : ℝ) < P.card := by exact_mod_cast hP.card_pos
  refine ⟨fun i j => (P.card : ℝ)⁻¹ * ∑ q ∈ P, if σ q i = j then 1 else 0,
    fun i j => mul_nonneg (inv_nonneg.2 hcard.le)
      (Finset.sum_nonneg fun q _ => by split_ifs <;> norm_num), fun i j hij => ?_,
    fun i j hij => ?_, fun i => ?_, fun j => ?_⟩
  · refine mul_pos (inv_pos.2 hcard) (lt_of_lt_of_le one_pos ?_)
    have hmem : (i, j) ∈ P := by simp [P, hij]
    have := Finset.single_le_sum (f := fun q => if σ q i = j then (1 : ℝ) else 0)
      (fun q _ => by split_ifs <;> norm_num) hmem
    simpa [hσi (i, j) hij] using this
  · change (P.card : ℝ)⁻¹ * _ = 0
    rw [Finset.sum_eq_zero, mul_zero]
    intro q hq
    have hq' : 0 < A q.1 q.2 := by simpa [P] using hq
    simp only [ite_eq_right_iff, one_ne_zero, imp_false]
    intro hqi
    have := hσk q hq' i
    rw [hqi, hij] at this
    exact lt_irrefl _ this
  · rw [← Finset.mul_sum, Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const, nsmul_eq_mul,
      mul_one]
    exact inv_mul_cancel₀ hcard.ne'
  · have hc : ∀ q, ∑ i, (if σ q i = j then (1 : ℝ) else 0) = 1 := fun q => by
      rw [Fintype.sum_equiv (σ q) (fun i => if σ q i = j then (1 : ℝ) else 0)
        (fun i => if i = j then 1 else 0) (fun _ => rfl)]
      simp
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp only [hc, Finset.sum_const, nsmul_eq_mul, mul_one]
    exact inv_mul_cancel₀ hcard.ne'

/-- The balancing objective `∑ i j, A i j * exp (x i + x j) - 2 ∑ i, x i`; its stationary points
`x` give the balancing `d = exp x`. -/
private noncomputable def balObj (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * Real.exp (x i + x j) - 2 * ∑ i, x i

/-- `a eᵗ - b t ≥ β |t| - 2 b² / a` for `a > 0` and `0 ≤ β ≤ b`. -/
private theorem coord_bound_pos {a b β : ℝ} (ha : 0 < a) (hβ : 0 ≤ β) (hβb : β ≤ b) (t : ℝ) :
    β * |t| - 2 * b ^ 2 / a ≤ a * Real.exp t - b * t := by
  have hb : 0 ≤ b := hβ.trans hβb
  have hc : 0 ≤ 2 * b ^ 2 / a := by positivity
  have he := Real.exp_pos t
  rcases le_or_gt 0 t with ht | ht
  · have hq := Real.quadratic_le_exp_of_nonneg ht
    rw [abs_of_nonneg ht]
    have key : 2 * b * t - 2 * b ^ 2 / a ≤ a * Real.exp t := by
      have h1 : a * (1 + t + t ^ 2 / 2) ≤ a * Real.exp t := mul_le_mul_of_nonneg_left hq ha.le
      have h2 : 2 * b * t - 2 * b ^ 2 / a ≤ a * (t ^ 2 / 2) := by
        have : a * (t ^ 2 / 2) - (2 * b * t - 2 * b ^ 2 / a) = (a * t - 2 * b) ^ 2 / (2 * a) := by
          field_simp
          ring
        nlinarith [sq_nonneg (a * t - 2 * b), this, div_nonneg (sq_nonneg (a * t - 2 * b))
          (by linarith : (0 : ℝ) ≤ 2 * a)]
      nlinarith
    nlinarith
  · rw [abs_of_neg ht]
    nlinarith [mul_pos ha he]

/-- `t² ≥ β |t| - β² / 4`. -/
private theorem coord_bound_sq (β t : ℝ) : β * |t| - β ^ 2 / 4 ≤ t ^ 2 := by
  nlinarith [sq_nonneg (|t| - β / 2), sq_abs t]

/-- Under total support the balancing objective attains its minimum. -/
private theorem exists_isMin_balObj {A B : Matrix (Fin n) (Fin n) ℝ} (hA : ∀ i j, 0 ≤ A i j)
    (hAB : ∀ i j, 0 < A i j → 0 < B i j)
    (hBA : ∀ i j, A i j = 0 → B i j = 0) (hrow : ∀ i, ∑ j, B i j = 1)
    (hcol : ∀ j, ∑ i, B i j = 1) :
    ∃ x : Fin n → ℝ, ∀ x', balObj A x ≤ balObj A x' := by
  classical
  -- the coordinatewise objective on the pattern, with `t ^ 2` off the pattern
  let h : Fin n × Fin n → ℝ → ℝ := fun q t =>
    if 0 < A q.1 q.2 then A q.1 q.2 * Real.exp t - B q.1 q.2 * t else t ^ 2
  let G : (Fin n × Fin n → ℝ) → ℝ := fun s => ∑ q, h q (s q)
  let Φ : (Fin n → ℝ) →ₗ[ℝ] (Fin n × Fin n → ℝ) :=
    { toFun := fun x q => if 0 < A q.1 q.2 then x q.1 + x q.2 else 0
      map_add' := fun x y => by
        funext q
        simp only [Pi.add_apply]
        split_ifs <;> ring
      map_smul' := fun a x => by
        funext q
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        split_ifs <;> ring }
  have hGΦ : ∀ x, G (Φ x) = balObj A x := by
    intro x
    have hterm : ∀ q : Fin n × Fin n, h q (Φ x q) =
        A q.1 q.2 * Real.exp (x q.1 + x q.2) - B q.1 q.2 * (x q.1 + x q.2) := by
      intro q
      simp only [h, Φ, LinearMap.coe_mk, AddHom.coe_mk]
      split_ifs with hq
      · rfl
      · have hA0 : A q.1 q.2 = 0 := le_antisymm (not_lt.1 hq) (hA _ _)
        simp [hA0, hBA _ _ hA0]
    have hBx : ∑ i, ∑ j, B i j * (x i + x j) = 2 * ∑ i, x i := by
      have h1 : ∑ i, ∑ j, B i j * x i = ∑ i, x i :=
        Finset.sum_congr rfl fun i _ => by rw [← Finset.sum_mul, hrow, one_mul]
      have h2 : ∑ i, ∑ j, B i j * x j = ∑ j, x j := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => by rw [← Finset.sum_mul, hcol, one_mul]
      simp only [mul_add, Finset.sum_add_distrib, h1, h2]
      ring
    simp only [G, hterm, balObj, Fintype.sum_prod_type, Finset.sum_sub_distrib, hBx]
  -- a uniform coercivity constant
  obtain ⟨β, hβ, hβB⟩ : ∃ β : ℝ, 0 < β ∧ ∀ i j, 0 < A i j → β ≤ B i j := by
    by_cases hne : (Finset.univ.filter fun q : Fin n × Fin n => 0 < A q.1 q.2).Nonempty
    · obtain ⟨q₀, hq₀, hmin⟩ := Finset.exists_min_image _ (fun q => B q.1 q.2) hne
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq₀ hmin
      exact ⟨B q₀.1 q₀.2, hAB _ _ hq₀, fun i j hij => hmin (i, j) hij⟩
    · refine ⟨1, one_pos, fun i j hij => absurd ⟨(i, j), ?_⟩ hne⟩
      simp [hij]
  let C : Fin n × Fin n → ℝ := fun q =>
    if 0 < A q.1 q.2 then 2 * B q.1 q.2 ^ 2 / A q.1 q.2 else β ^ 2 / 4
  have hC0 : ∀ q, 0 ≤ C q := fun q => by
    simp only [C]
    split_ifs with hq
    · exact div_nonneg (by positivity) hq.le
    · positivity
  have hhC : ∀ q t, β * |t| ≤ h q t + C q := by
    intro q t
    simp only [h, C]
    split_ifs with hq
    · linarith [coord_bound_pos hq hβ.le (hβB _ _ hq) t]
    · linarith [coord_bound_sq β t]
  have hGC : ∀ s q, β * |s q| ≤ G s + ∑ q, C q := by
    intro s q
    have := Finset.single_le_sum (f := fun q => h q (s q) + C q)
      (fun q _ => (mul_nonneg hβ.le (abs_nonneg _)).trans (hhC q _)) (Finset.mem_univ q)
    simp only [G, ← Finset.sum_add_distrib]
    linarith [hhC q (s q)]
  have hGcont : Continuous G := by
    refine continuous_finsetSum _ fun q _ => ?_
    simp only [h]
    split_ifs
    · fun_prop
    · fun_prop
  -- coercivity: `G` exceeds `G 0` outside a ball
  set R := (G 0 + ∑ q, C q) / β with hR
  have hG0 : 0 ≤ G 0 + ∑ q, C q := by
    simp only [G, ← Finset.sum_add_distrib]
    exact Finset.sum_nonneg fun q _ => by simpa using hhC q 0
  have hR0 : 0 ≤ R := div_nonneg hG0 hβ.le
  have hev : ∀ᶠ s in Filter.cocompact (Fin n × Fin n → ℝ), G 0 ≤ G s := by
    filter_upwards [tendsto_norm_cocompact_atTop.eventually_gt_atTop R] with s hs
    by_contra hlt
    push Not at hlt
    have : ‖s‖ ≤ R := by
      refine (pi_norm_le_iff_of_nonneg hR0).2 fun q => ?_
      rw [Real.norm_eq_abs, hR, le_div_iff₀ hβ]
      linarith [hGC s q]
    linarith
  obtain ⟨s, hsV, hsmin⟩ := hGcont.continuousOn.exists_isMinOn'
    (LinearMap.range Φ).closed_of_finiteDimensional (Submodule.zero_mem _)
    (hev.filter_mono inf_le_left)
  obtain ⟨x, rfl⟩ := LinearMap.mem_range.1 hsV
  exact ⟨x, fun x' => by
    rw [← hGΦ, ← hGΦ]
    exact hsmin (LinearMap.mem_range_self Φ x')⟩

/-- At a minimizer of the balancing objective of a symmetric matrix, every row of
`A i j * exp (x i + x j)` sums to `1`. -/
private theorem row_sum_of_isMin {A : Matrix (Fin n) (Fin n) ℝ} (hsymm : A.IsSymm)
    {x : Fin n → ℝ} (hmin : ∀ x', balObj A x ≤ balObj A x') (k : Fin n) :
    ∑ j, A k j * Real.exp (x k + x j) = 1 := by
  classical
  have hAij : ∀ i j, A i j = A j i := fun i j => by
    simpa using congrFun (congrFun hsymm.symm i) j
  set e : Fin n → ℝ := fun i => if i = k then 1 else 0 with he
  let f : ℝ → ℝ := fun t => balObj A fun i => x i + t * e i
  have hf : HasDerivAt f (∑ i, ∑ j, A i j * (Real.exp (x i + x j) * (e i + e j)) -
      2 * ∑ i, e i) 0 := by
    have hlin : ∀ i, HasDerivAt (fun t : ℝ => x i + t * e i) (e i) 0 := fun i => by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (e i)).const_add (x i)
    have hexp : ∀ i j, HasDerivAt (fun t : ℝ => A i j * Real.exp (x i + t * e i +
        (x j + t * e j))) (A i j * (Real.exp (x i + x j) * (e i + e j))) 0 := fun i j => by
      have := (((hlin i).add (hlin j)).exp).const_mul (A i j)
      simpa using this
    have h1 : HasDerivAt (fun t : ℝ => ∑ i, ∑ j, A i j * Real.exp (x i + t * e i +
        (x j + t * e j))) (∑ i, ∑ j, A i j * (Real.exp (x i + x j) * (e i + e j))) 0 :=
      HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => hexp i j
    have h2 : HasDerivAt (fun t : ℝ => ∑ i, (x i + t * e i)) (∑ i, e i) 0 :=
      HasDerivAt.fun_sum fun i _ => hlin i
    exact h1.sub (h2.const_mul 2)
  have hloc : IsLocalMin f 0 := Filter.Eventually.of_forall fun t => by
    have : f 0 = balObj A x := by simp [f]
    rw [this]
    exact hmin _
  have h0 := hloc.hasDerivAt_eq_zero hf
  have hsum_e : ∑ i, e i = 1 := by simp [he]
  have hsplit : ∑ i, ∑ j, A i j * (Real.exp (x i + x j) * (e i + e j)) =
      2 * ∑ j, A k j * Real.exp (x k + x j) := by
    simp only [mul_add, Finset.sum_add_distrib, he, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [two_mul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hAij, add_comm]
  rw [hsplit, hsum_e] at h0
  linarith

/-- **Csima–Datta: sufficiency of total support.** A symmetric nonnegative matrix with total
support has a positive vector `d` with `diag(d) A diag(d)` doubly stochastic.

Source: Csima & Datta (1972); Sinkhorn & Knopp (1967). -/
theorem exists_symmetric_balancing_of_hasTotalSupport {A : Matrix (Fin n) (Fin n) ℝ}
    (hsymm : A.IsSymm) (hA : ∀ i j, 0 ≤ A i j) (hts : HasTotalSupport A) :
    ∃ d : Fin n → ℝ, (∀ i, 0 < d i) ∧
      (fun i j => d i * A i j * d j) ∈ doublyStochastic ℝ (Fin n) := by
  obtain ⟨B, -, hAB, hBA, hrow, hcol⟩ := exists_doublyStochastic_pattern hA hts
  obtain ⟨x, hx⟩ := exists_isMin_balObj hA hAB hBA hrow hcol
  have hAij : ∀ i j, A i j = A j i := fun i j => by
    simpa using congrFun (congrFun hsymm.symm i) j
  have hd : ∀ i j, Real.exp (x i) * A i j * Real.exp (x j) = A i j * Real.exp (x i + x j) :=
    fun i j => by rw [Real.exp_add]; ring
  refine ⟨fun i => Real.exp (x i), fun i => Real.exp_pos _, ?_⟩
  refine mem_doublyStochastic_iff_sum.2 ⟨fun i j =>
    mul_nonneg (mul_nonneg (Real.exp_pos _).le (hA i j)) (Real.exp_pos _).le, fun i => ?_,
    fun j => ?_⟩
  · simp only [hd]
    exact row_sum_of_isMin hsymm hx i
  · rw [← row_sum_of_isMin hsymm hx j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hd, hAij, add_comm]

/-- **Csima–Datta theorem.** For `0 < n`, a symmetric nonnegative matrix has a positive vector
`d` with `diag(d) A diag(d)` doubly stochastic if and only if it has total support. -/
theorem exists_symmetric_balancing_iff_hasTotalSupport (hn : 0 < n)
    {A : Matrix (Fin n) (Fin n) ℝ} (hsymm : A.IsSymm) (hA : ∀ i j, 0 ≤ A i j) :
    (∃ d : Fin n → ℝ, (∀ i, 0 < d i) ∧
      (fun i j => d i * A i j * d j) ∈ doublyStochastic ℝ (Fin n)) ↔ HasTotalSupport A :=
  ⟨fun ⟨_, hd, h⟩ => hasTotalSupport_of_balancing hn hd h,
    exists_symmetric_balancing_of_hasTotalSupport hsymm hA⟩

end MathlibExt.Biology.Dynamics.SystemsBiology
