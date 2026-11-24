/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import Mathlib.Topology.Algebra.InfiniteSum.ContinuousEval
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Tactic

open scoped ENNReal

/-!
# Neumann series for a contractive operator

We formalize the Neumann-series solution of the fixed-point equation `I = gε + T I`
for a bounded linear operator `T` with uniform norm bound `‖T‖ ≤ c < 1` on a
complete normed space, together with the truncation error bound
`c ^ (K + 1) * ‖gε‖ / (1 - c)`.

This is the abstract form of the formal solution of the rendering equation
`I = gε + gM I` as a Neumann series `I = gε + gMgε + ⋯`, as written by
James T. Kajiya in "The Rendering Equation" (Computer Graphics, SIGGRAPH 1986).
Two modelling notes: the uniform norm bound `‖T‖ ≤ c < 1` used here strengthens
Kajiya's spectral-radius condition, and that strengthening is what the truncation
bound needs; positivity of `T` is not needed for any proof below, so it is
deliberately not assumed.
-/

@[expose] public section
namespace ContinuousLinearMap

/-- The Neumann series `∑' k, T ^ k` in the endomorphism ring, whose value at `x`
solves `I = x + T I` when `‖T‖ ≤ c < 1`. -/
noncomputable def neumannSeries {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (T : E →L[ℝ] E) : E →L[ℝ] E :=
  ∑' k, T ^ k

/-- Auxiliary bound: iterates of a bounded operator satisfy `‖T ^ k‖ ≤ c ^ k`. -/
private theorem norm_iterate_le_pow {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (T : E →L[ℝ] E) (c : ℝ) (hT : ‖T‖ ≤ c)
    (k : ℕ) : ‖T ^ k‖ ≤ c ^ k := by
  have hc0 : 0 ≤ c := le_trans (norm_nonneg T) hT
  induction k with
  | zero =>
      simp only [pow_zero]
      exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by simp)
  | succ k ih =>
      simp only [pow_succ]
      calc ‖T ^ k * T‖ ≤ ‖T ^ k‖ * ‖T‖ := norm_mul_le _ _
        _ ≤ c ^ k * c := mul_le_mul ih hT (norm_nonneg _) (pow_nonneg hc0 k)

/-- Auxiliary summability of the operator powers under `‖T‖ ≤ c < 1`. -/
private theorem summable_iterate {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (T : E →L[ℝ] E) (c : ℝ) (hT : ‖T‖ ≤ c)
    (hc : c < 1) : Summable (fun k => T ^ k) := by
  have hc0 : 0 ≤ c := le_trans (norm_nonneg T) hT
  exact Summable.of_norm_bounded (summable_geometric_of_lt_one hc0 hc)
    (fun k => norm_iterate_le_pow T c hT k)

/-- Auxiliary summability of the operator powers applied to a vector. -/
private theorem summable_iterate_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (T : E →L[ℝ] E) (c : ℝ) (hT : ‖T‖ ≤ c)
    (hc : c < 1) (x : E) : Summable (fun k => (T ^ k) x) := by
  have hc0 : 0 ≤ c := le_trans (norm_nonneg T) hT
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one hc0 hc).mul_right ‖x‖) (fun k => ?_)
  calc ‖(T ^ k) x‖ ≤ ‖T ^ k‖ * ‖x‖ := le_opNorm _ _
    _ ≤ c ^ k * ‖x‖ :=
        mul_le_mul_of_nonneg_right (norm_iterate_le_pow T c hT k) (norm_nonneg x)

/-- The Neumann series solves the fixed-point equation `I = x + T I`. -/
theorem neumannSeries_apply_eq_add {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (T : E →L[ℝ] E) (c : ℝ) (hT : ‖T‖ ≤ c)
    (hc : c < 1) (x : E) : neumannSeries T x = x + T (neumannSeries T x) := by
  have hs : Summable (fun k => (T ^ k) x) := summable_iterate_apply T c hT hc x
  have hS : neumannSeries T x = ∑' k, (T ^ k) x :=
    tsum_apply (summable_iterate T c hT hc) x
  have hsplit : (∑' k, (T ^ k) x) = (T ^ 0) x + ∑' k, (T ^ (k + 1)) x :=
    Summable.tsum_eq_zero_add hs
  have hmap : T (∑' k, (T ^ k) x) = ∑' k, (T ^ (k + 1)) x := by
    have h : T (∑' k, (T ^ k) x) = ∑' k, T ((T ^ k) x) :=
      ContinuousLinearMap.map_tsum T hs
    rw [h]
    apply tsum_congr
    intro k
    rw [pow_succ', mul_apply_eq_comp]
  have hLHS : neumannSeries T x = x + ∑' k, (T ^ (k + 1)) x := by
    rw [hS, hsplit, pow_zero, one_apply_eq_self]
  have hRHS : x + T (neumannSeries T x) = x + ∑' k, (T ^ (k + 1)) x := by
    rw [hS, hmap]
  calc neumannSeries T x = x + ∑' k, (T ^ (k + 1)) x := hLHS
    _ = x + T (neumannSeries T x) := hRHS.symm

/-- Uniqueness: any solution of `y = x + T y` equals the Neumann series at `x`. -/
theorem eq_neumannSeries_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (T : E →L[ℝ] E) (c : ℝ) (hT : ‖T‖ ≤ c)
    (hc : c < 1) {x y : E} (hy : y = x + T y) : y = neumannSeries T x := by
  have hS := neumannSeries_apply_eq_add T c hT hc x
  have hdiff : y - neumannSeries T x = T (y - neumannSeries T x) := by
    have h1 : T (y - neumannSeries T x) = T y - T (neumannSeries T x) :=
      map_sub _ _ _
    rw [h1]
    conv_lhs => rw [hy]
    conv_lhs => rw [hS]
    abel
  have hnorm : ‖y - neumannSeries T x‖ ≤ c * ‖y - neumannSeries T x‖ := by
    calc ‖y - neumannSeries T x‖ = ‖T (y - neumannSeries T x)‖ :=
          congr_arg _ hdiff
      _ ≤ ‖T‖ * ‖y - neumannSeries T x‖ := le_opNorm T _
      _ ≤ c * ‖y - neumannSeries T x‖ :=
          mul_le_mul_of_nonneg_right hT (norm_nonneg _)
  have h0 : ‖y - neumannSeries T x‖ = 0 := by
    by_contra hcon
    have hpos : 0 < ‖y - neumannSeries T x‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hcon)
    have hlt : c * ‖y - neumannSeries T x‖ < 1 * ‖y - neumannSeries T x‖ :=
      mul_lt_mul_of_pos_right hc hpos
    linarith
  exact sub_eq_zero.mp (norm_eq_zero.mp h0)

/-- Truncation bound: the error after `K + 1` terms is at most
`c ^ (K + 1) * ‖x‖ / (1 - c)`. -/
theorem norm_neumannSeries_apply_sub_sum_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (T : E →L[ℝ] E) (c : ℝ) (hT : ‖T‖ ≤ c)
    (hc0 : 0 ≤ c) (hc : c < 1) (x : E) (K : ℕ) :
    ‖neumannSeries T x - ∑ k ∈ Finset.range (K + 1), (T ^ k) x‖ ≤
      c ^ (K + 1) * ‖x‖ / (1 - c) := by
  have hs : Summable (fun k => (T ^ k) x) := summable_iterate_apply T c hT hc x
  have hSx : neumannSeries T x = ∑' k, (T ^ k) x :=
    tsum_apply (summable_iterate T c hT hc) x
  have h1c : (0 : ℝ) < 1 - c := by linarith
  have hnormS : ‖∑' k, (T ^ k) x‖ ≤ ‖x‖ / (1 - c) := by
    have hfix := neumannSeries_apply_eq_add T c hT hc x
    have hle : ‖neumannSeries T x‖ ≤ ‖x‖ + c * ‖neumannSeries T x‖ := by
      have h1 : ‖T (neumannSeries T x)‖ ≤ c * ‖neumannSeries T x‖ :=
        le_trans (le_opNorm T _) (mul_le_mul_of_nonneg_right hT (norm_nonneg _))
      calc ‖neumannSeries T x‖ = ‖x + T (neumannSeries T x)‖ := congr_arg _ hfix
        _ ≤ ‖x‖ + ‖T (neumannSeries T x)‖ := norm_add_le _ _
        _ ≤ ‖x‖ + c * ‖neumannSeries T x‖ := by
            rw [add_le_add_iff_left]
            exact h1
    rw [← hSx]
    rw [le_div_iff₀ h1c]
    have hexp : ‖neumannSeries T x‖ * (1 - c)
        = ‖neumannSeries T x‖ - c * ‖neumannSeries T x‖ := by ring
    linarith
  have hsum : (∑ k ∈ Finset.range (K + 1), (T ^ k) x)
      + (∑' n, (T ^ (n + (K + 1))) x) = ∑' k, (T ^ k) x :=
    Summable.sum_add_tsum_nat_add (K + 1) hs
  have hshift : (∑' n, (T ^ (n + (K + 1))) x)
      = (T ^ (K + 1)) (∑' k, (T ^ k) x) := by
    have hmap := ContinuousLinearMap.map_tsum (T ^ (K + 1)) hs
    have hmap' : (T ^ (K + 1)) (∑' k, (T ^ k) x)
        = ∑' k, (T ^ (K + 1)) ((T ^ k) x) := hmap
    rw [hmap']
    apply tsum_congr
    intro n
    rw [add_comm n (K + 1), pow_add, mul_apply_eq_comp]
  have hsum' : (∑ k ∈ Finset.range (K + 1), (T ^ k) x)
      + (T ^ (K + 1)) (∑' k, (T ^ k) x) = ∑' k, (T ^ k) x := by
    rw [← hshift]
    exact hsum
  have htail : (∑' k, (T ^ k) x) - ∑ k ∈ Finset.range (K + 1), (T ^ k) x
      = (T ^ (K + 1)) (∑' k, (T ^ k) x) := by
    rw [sub_eq_iff_eq_add, add_comm]
    exact hsum'.symm
  rw [hSx, htail]
  calc ‖(T ^ (K + 1)) (∑' k, (T ^ k) x)‖
      ≤ ‖T ^ (K + 1)‖ * ‖∑' k, (T ^ k) x‖ := le_opNorm _ _
    _ ≤ c ^ (K + 1) * (‖x‖ / (1 - c)) :=
        mul_le_mul (norm_iterate_le_pow T c hT (K + 1)) hnormS (norm_nonneg _)
          (pow_nonneg hc0 _)
    _ = c ^ (K + 1) * ‖x‖ / (1 - c) := by ring

/-- Coefficient bound for the diagonal counterexample: each entry lies in `[0, 1]`. -/
private theorem lpDiagCoeff_mem (n : ℕ) :
    0 ≤ 1 - 1 / (n + 1 : ℝ) ∧ 1 - 1 / (n + 1 : ℝ) ≤ 1 := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hpos : (0 : ℝ) < (n + 1 : ℝ) := by positivity
  have hle : (1 : ℝ) / (n + 1 : ℝ) ≤ 1 := by
    rw [div_le_one hpos]
    linarith
  have hnn : (0 : ℝ) ≤ 1 / (n + 1 : ℝ) := one_div_nonneg.mpr (le_of_lt hpos)
  constructor <;> linarith

/-- Underlying function of the diagonal operator. -/
noncomputable def lpDiagFun (x : ↥(lp (fun _ : ℕ => ℝ) ⊤)) :
    ↥(lp (fun _ : ℕ => ℝ) ⊤) :=
  ⟨fun n => (1 - 1 / (n + 1 : ℝ)) * x.1 n, by
    apply memℓp_infty
    refine ⟨‖x‖, ?_⟩
    rintro y ⟨n, rfl⟩
    change ‖(1 - 1 / (n + 1 : ℝ)) * x.1 n‖ ≤ ‖x‖
    calc ‖(1 - 1 / (n + 1 : ℝ)) * x.1 n‖
        = ‖(1 - 1 / (n + 1 : ℝ))‖ * ‖x.1 n‖ := norm_mul _ _
      _ ≤ 1 * ‖x.1 n‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          rw [Real.norm_eq_abs, abs_of_nonneg (lpDiagCoeff_mem n).1]
          exact (lpDiagCoeff_mem n).2
      _ = ‖x.1 n‖ := one_mul _
      _ ≤ ‖x‖ := lp.norm_apply_le_norm (by simp) x n⟩

/-- Pointwise action of the underlying function. -/
private theorem lpDiagFun_coe (x : ↥(lp (fun _ : ℕ => ℝ) ⊤)) (m : ℕ) :
    (↑(lpDiagFun x) : (n : ℕ) → ℝ) m
      = (1 - 1 / (m + 1 : ℝ)) * (↑x : (n : ℕ) → ℝ) m := rfl

/-- The diagonal operator as a linear map. -/
noncomputable def lpDiagLin :
    ↥(lp (fun _ : ℕ => ℝ) ⊤) →ₗ[ℝ] ↥(lp (fun _ : ℕ => ℝ) ⊤) where
  toFun := lpDiagFun
  map_add' x y := by
    apply lp.ext
    funext n
    simp [lpDiagFun_coe, mul_add]
  map_smul' c x := by
    apply lp.ext
    funext n
    simp [lpDiagFun_coe, smul_eq_mul, mul_left_comm]

/-- The diagonal operator is nonexpansive. -/
private theorem lpDiagLin_norm_le (x : ↥(lp (fun _ : ℕ => ℝ) ⊤)) :
    ‖lpDiagLin x‖ ≤ ‖x‖ := by
  apply lp.norm_mono (by simp)
  intro n
  change ‖(1 - 1 / (n + 1 : ℝ)) * (↑x : (n : ℕ) → ℝ) n‖ ≤ ‖(↑x : (n : ℕ) → ℝ) n‖
  rw [norm_mul]
  have h1 : ‖(1 - 1 / (n + 1 : ℝ))‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (lpDiagCoeff_mem n).1]
    exact (lpDiagCoeff_mem n).2
  calc ‖(1 - 1 / (n + 1 : ℝ))‖ * ‖(↑x : (n : ℕ) → ℝ) n‖
      ≤ 1 * ‖(↑x : (n : ℕ) → ℝ) n‖ :=
        mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = ‖(↑x : (n : ℕ) → ℝ) n‖ := one_mul _

/-- Diagonal operator on `ℓ^∞(ℕ)` with entries `1 - 1 / (n + 1)`: every diagonal
entry is `< 1`, yet the operator norm is `1`. This shows entrywise strict
contraction does not give a uniform bound `c < 1`. -/
noncomputable def lpDiag :
    ↥(lp (fun _ : ℕ => ℝ) ⊤) →L[ℝ] ↥(lp (fun _ : ℕ => ℝ) ⊤) :=
  LinearMap.mkContinuous lpDiagLin 1 (fun x => by
    rw [one_mul]
    exact lpDiagLin_norm_le x)

/-- Applying the diagonal operator is applying the linear map. -/
private theorem lpDiag_apply (x : ↥(lp (fun _ : ℕ => ℝ) ⊤)) : lpDiag x = lpDiagLin x :=
  LinearMap.mkContinuous_apply _ _ _ _

/-- Coordinatewise action of the diagonal operator on arbitrary vectors. -/
theorem lpDiag_apply_apply (x : ↥(lp (fun _ : ℕ => ℝ) ⊤)) (n : ℕ) :
    (↑(lpDiag x) : (m : ℕ) → ℝ) n
      = (1 - 1 / (n + 1 : ℝ)) * (↑x : (m : ℕ) → ℝ) n := by
  rw [lpDiag_apply]
  exact lpDiagFun_coe x n

/-- The diagonal operator scales each standard unit vector by its diagonal entry. -/
theorem lpDiag_single (n : ℕ) :
    lpDiag (lp.single ⊤ n 1) = (1 - 1 / (n + 1 : ℝ)) • lp.single ⊤ n 1 := by
  have hsmul : ∀ (c : ℝ) (y : ↥(lp (fun _ : ℕ => ℝ) ⊤)),
      (↑(c • y) : (n : ℕ) → ℝ) = c • (↑y : (n : ℕ) → ℝ) := fun c y => by simp
  have hdiag : ∀ (x : ↥(lp (fun _ : ℕ => ℝ) ⊤)) (m : ℕ),
      (↑(lpDiagLin x) : (n : ℕ) → ℝ) m
        = (1 - 1 / (m + 1 : ℝ)) * (↑x : (n : ℕ) → ℝ) m :=
    fun x m => lpDiagFun_coe x m
  apply lp.ext
  funext m
  rw [lpDiag_apply, hdiag, hsmul, Pi.smul_apply, smul_eq_mul, lp.single_apply]
  by_cases h : m = n
  · simp [h]
  · simp [h]

/-- The diagonal operator has norm `1`, although every diagonal entry is `< 1`:
entrywise strict contraction does not give a uniform bound `c < 1`. -/
theorem lpDiag_norm : ‖lpDiag‖ = 1 := by
  have htop_ne : (⊤ : ℝ≥0∞) ≠ 0 := by simp
  have htop_pos : (0 : ℝ≥0∞) < ⊤ := by simp
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    rw [lpDiag_apply, one_mul]
    exact lpDiagLin_norm_le x
  · by_contra hcon
    push Not at hcon
    have hpos : (0 : ℝ) < 1 - ‖lpDiag‖ := by linarith
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
    have hn' : 1 / (n + 1 : ℝ) < 1 - ‖lpDiag‖ := hn
    have hTe := lpDiag_single n
    have hle := le_opNorm lpDiag (lp.single ⊤ n 1)
    rw [hTe, lp.norm_const_smul htop_ne, Real.norm_eq_abs,
      abs_of_nonneg (lpDiagCoeff_mem n).1, lp.norm_single htop_pos, norm_one] at hle
    have hentry : 1 - 1 / (n + 1 : ℝ) ≤ ‖lpDiag‖ := by simpa using hle
    linarith

/-- There is a diagonal operator on `ℓ^∞`, diagonal in the coordinatewise sense,
with every entry `< 1` but norm `1`: entrywise strict contraction does not give
a uniform bound `c < 1`. -/
theorem exists_lp_diagonal_norm_eq_one :
    ∃ T : ↥(lp (fun _ : ℕ => ℝ) ⊤) →L[ℝ] ↥(lp (fun _ : ℕ => ℝ) ⊤),
      (∀ (x : ↥(lp (fun _ : ℕ => ℝ) ⊤)) (n : ℕ),
        (↑(T x) : (m : ℕ) → ℝ) n
          = (1 - 1 / (n + 1 : ℝ)) * (↑x : (m : ℕ) → ℝ) n)
        ∧ ‖T‖ = 1 :=
  ⟨lpDiag, lpDiag_apply_apply, lpDiag_norm⟩

end ContinuousLinearMap
