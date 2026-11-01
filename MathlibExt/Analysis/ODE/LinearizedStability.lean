/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.MMatrix
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Order.IntermediateValue

/-!
# Linearized stability (Lyapunov's indirect method)

Let `f : ℝⁿ → ℝⁿ` vanish at `x⋆` and be (Fréchet) differentiable there with Jacobian matrix
`A`. If `A` is Hurwitz (every eigenvalue has negative real part), then `x⋆` is a locally
exponentially stable equilibrium of `x' = f(x)`: there are `δ, C, α > 0` such that every
solution with `‖x(0) - x⋆‖ < δ` satisfies `‖x(t) - x⋆‖ ≤ C e^{-α t} ‖x(0) - x⋆‖` for `t ≥ 0`.
In particular `x⋆` is Lyapunov stable and attracts all solutions starting within `δ`, i.e. it
is locally asymptotically stable.

Vectors are functions `ι → ℝ` with the sup norm; since all norms on `ℝⁿ` are equivalent, the
statement does not depend on this choice (only the constants `δ` and `C` do). Only
differentiability of `f` at `x⋆` is assumed (the classical statement assumes `f` is `C¹`), and
no existence theorem for solutions is needed: the conclusion is about every solution.

The converse instability statement (an eigenvalue with positive real part makes `x⋆` unstable)
is not proved here.

## Main results

* `Matrix.IsHurwitz.exists_norm_exp_smul_mulVec_le`: if `A` is Hurwitz, then
  `‖exp(t A) v‖ ≤ M e^{-α t} ‖v‖` for `t ≥ 0`, for some `M, α > 0`.
* `exists_locallyExponentiallyStable_of_hasFDerivAt`: Lyapunov's indirect method.

## References

* A. M. Lyapunov, *The general problem of the stability of motion* (1892); English
  translation, Internat. J. Control 55 (1992) 531–773.
* H. K. Khalil, *Nonlinear Systems*, 3rd ed., Prentice Hall (2002), §4.3, Theorem 4.7.
-/

@[expose] public section

open Filter Real
open scoped Topology
open scoped Matrix

private theorem finite_spectral_gap (s : Finset ℂ) (hs : ∀ μ ∈ s, μ.re < 0) :
    ∃ α : ℝ, 0 < α ∧ ∀ μ ∈ s, μ.re + α < 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert μ s hμ ih =>
    obtain ⟨α, hα, hαs⟩ := ih (fun z hz => hs z (Finset.mem_insert_of_mem hz))
    refine ⟨min α (-μ.re / 2), lt_min hα (by linarith [hs μ (by simp)]), ?_⟩
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · have := min_le_right α (-z.re / 2)
      linarith [hs z (by simp)]
    · have := min_le_left α (-μ.re / 2)
      linarith [hαs z hz]

private theorem polynomial_exp_bound (α r t : ℝ) (k : ℕ) (hr : r + α < 0)
    (ht : 0 ≤ t) :
    t ^ k / (k.factorial : ℝ) * Real.exp (r * t) ≤
      ((-(r + α)) ^ k)⁻¹ * Real.exp (-(α * t)) := by
  let b := -(r + α)
  have hb : 0 < b := by dsimp [b]; linarith
  have hpow : t ^ k / (k.factorial : ℝ) ≤ Real.exp (b * t) / b ^ k := by
    apply (le_div_iff₀ (pow_pos hb k)).mpr
    calc
      t ^ k / (k.factorial : ℝ) * b ^ k = (b * t) ^ k / (k.factorial : ℝ) := by
        rw [mul_pow]
        ring_nf
      _ ≤ Real.exp (b * t) :=
        Real.pow_div_factorial_le_exp (b * t) (mul_nonneg hb.le ht) k
  calc
    t ^ k / (k.factorial : ℝ) * Real.exp (r * t) ≤
        (Real.exp (b * t) / b ^ k) * Real.exp (r * t) := by gcongr
    _ = (b ^ k)⁻¹ * Real.exp (-(α * t)) := by
      rw [div_eq_mul_inv, mul_right_comm, ← Real.exp_add, mul_comm]
      congr 1
      dsimp [b]
      ring_nf

private theorem exp_apply_of_pow_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (N : E →L[ℂ] E) (v : E) (n : ℕ)
    (hn : (N ^ n) v = 0) (t : ℝ) :
    (NormedSpace.exp (t • N)) v =
      ∑ k ∈ Finset.range n, ((t ^ k / (k.factorial : ℝ) : ℝ) : ℂ) • (N ^ k) v := by
  have hzero (k : ℕ) (hk : n ≤ k) : (N ^ k) v = 0 := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [add_comm, pow_add, mul_apply_eq_comp, hn, map_zero]
  have hsum : (NormedSpace.exp (t • N)) v =
      ∑' k : ℕ, (k.factorial : ℂ)⁻¹ • ((t • N) ^ k) v := by
    rw [NormedSpace.exp_eq_tsum ℂ]
    exact (ContinuousLinearMap.apply ℂ E v).map_tsum
      (NormedSpace.expSeries_summable' (t • N))
  rw [hsum]
  rw [tsum_eq_sum (s := Finset.range n)]
  · apply Finset.sum_congr rfl
    intro k hk
    simp only [smul_pow, smul_apply]
    rw [← Complex.coe_smul, smul_smul]
    congr 1
    simp [div_eq_mul_inv, mul_comm]
  · intro k hk
    have hk' : n ≤ k := by simpa using hk
    simp [smul_pow, hzero k hk']

private theorem exp_apply_gen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (f : E →L[ℂ] E) (μ : ℂ) (v : E) (n : ℕ)
    (hn : ((f - μ • 1) ^ n) v = 0) (t : ℝ) :
    (NormedSpace.exp (t • f)) v = Complex.exp ((t : ℂ) * μ) •
      ∑ k ∈ Finset.range n, ((t ^ k / (k.factorial : ℝ) : ℝ) : ℂ) •
        ((f - μ • 1) ^ k) v := by
  have hsplit : t • f =
      algebraMap ℂ (E →L[ℂ] E) ((t : ℂ) * μ) + t • (f - μ • 1) := by
    simp only [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul, smul_sub, smul_smul]
    module
  have hscalar (z : ℂ) : NormedSpace.exp (algebraMap ℂ (E →L[ℂ] E) z) =
      Complex.exp z • (1 : E →L[ℂ] E) := by
    rw [← NormedSpace.algebraMap_exp_comm, ← Complex.exp_eq_exp_ℂ,
      Algebra.algebraMap_eq_smul_one]
  let := NormedAlgebra.restrictScalars ℚ ℂ (E →L[ℂ] E)
  rw [hsplit, NormedSpace.exp_add_of_commute (Algebra.commute_algebraMap_left _ _),
    hscalar, mul_apply_eq_comp]
  change Complex.exp ((t : ℂ) * μ) • (NormedSpace.exp (t • (f - μ • 1))) v = _
  rw [exp_apply_of_pow_eq_zero (f - μ • 1) v n hn t]

private theorem gen_vector_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (f : E →L[ℂ] E) (μ : ℂ) (v : E) (n : ℕ)
    (hn : ((f - μ • 1) ^ n) v = 0) (α : ℝ) (hα : μ.re + α < 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, 0 ≤ t →
      ‖(NormedSpace.exp (t • f)) v‖ ≤ M * Real.exp (-(α * t)) := by
  let M := ∑ k ∈ Finset.range n, ((-(μ.re + α)) ^ k)⁻¹ * ‖((f - μ • 1) ^ k) v‖
  have hb : 0 < -(μ.re + α) := neg_pos.mpr hα
  refine ⟨M, Finset.sum_nonneg (fun k hk => by positivity), ?_⟩
  intro t ht
  rw [exp_apply_gen f μ v n hn t, norm_smul, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  calc
    Real.exp (t * μ.re) *
        ‖∑ k ∈ Finset.range n, ((t ^ k / (k.factorial : ℝ) : ℝ) : ℂ) •
          ((f - μ • 1) ^ k) v‖ ≤
        Real.exp (t * μ.re) * ∑ k ∈ Finset.range n,
          ‖((t ^ k / (k.factorial : ℝ) : ℝ) : ℂ) • ((f - μ • 1) ^ k) v‖ := by
      gcongr
      exact norm_sum_le _ _
    _ = ∑ k ∈ Finset.range n,
        (t ^ k / (k.factorial : ℝ) * Real.exp (μ.re * t)) *
          ‖((f - μ • 1) ^ k) v‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [mul_comm t μ.re]
      ring_nf
    _ ≤ M * Real.exp (-(α * t)) := by
      dsimp [M]
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro k hk
      rw [mul_right_comm _ _ (Real.exp _)]
      exact mul_le_mul_of_nonneg_right (polynomial_exp_bound α μ.re t k hα ht)
        (norm_nonneg _)

private theorem complex_vector_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    (f : E →L[ℂ] E) (α : ℝ) (hα : ∀ μ ∈ spectrum ℂ f.toLinearMap, μ.re + α < 0) :
    ∀ v : E, ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, 0 ≤ t →
      ‖(NormedSpace.exp (t • f)) v‖ ≤ M * Real.exp (-(α * t)) := by
  let S : Submodule ℂ E :=
    { carrier := {v | ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, 0 ≤ t →
        ‖(NormedSpace.exp (t • f)) v‖ ≤ M * Real.exp (-(α * t))}
      zero_mem' := ⟨0, le_rfl, by simp⟩
      add_mem' := by
        rintro v w ⟨M, hM, hv⟩ ⟨N, hN, hw⟩
        refine ⟨M + N, add_nonneg hM hN, ?_⟩
        intro t ht
        calc
          ‖(NormedSpace.exp (t • f)) (v + w)‖ ≤
              ‖(NormedSpace.exp (t • f)) v‖ + ‖(NormedSpace.exp (t • f)) w‖ := by
            rw [map_add]
            exact norm_add_le _ _
          _ ≤ (M + N) * Real.exp (-(α * t)) := by
            linarith [hv t ht, hw t ht]
      smul_mem' := by
        rintro c v ⟨M, hM, hv⟩
        refine ⟨‖c‖ * M, mul_nonneg (norm_nonneg _) hM, ?_⟩
        intro t ht
        rw [map_smul, norm_smul, mul_assoc]
        exact mul_le_mul_of_nonneg_left (hv t ht) (norm_nonneg _) }
  have htop : S = ⊤ := by
    apply top_unique
    rw [← Module.End.iSup_maxGenEigenspace_eq_top f.toLinearMap]
    refine iSup_le fun μ v hv => ?_
    by_cases hv0 : v = 0
    · subst v
      exact S.zero_mem
    have hgen : Module.End.HasUnifEigenvalue f.toLinearMap μ ⊤ := by
      intro hbot
      have hv' : v ∈ (⊥ : Submodule ℂ E) := hbot ▸ hv
      exact hv0 (by simpa using hv')
    have hμ : Module.End.HasEigenvalue f.toLinearMap μ :=
      Module.End.HasUnifEigenvalue.lt zero_lt_one hgen
    obtain ⟨n, hn⟩ := (Module.End.mem_maxGenEigenspace f.toLinearMap μ v).mp hv
    have hn' : ((f - μ • 1) ^ n) v = 0 := by
      change ((f - μ • 1) ^ n).toLinearMap v = 0
      simp only [ContinuousLinearMap.toLinearMap_pow, ContinuousLinearMap.toLinearMap_sub,
        ContinuousLinearMap.toLinearMap_smul, ContinuousLinearMap.toLinearMap_one]
      exact hn
    exact gen_vector_bound f μ v n hn' α
      (hα μ (Module.End.hasEigenvalue_iff_mem_spectrum.mp hμ))
  intro v
  have : v ∈ S := htop ▸ Submodule.mem_top
  exact this

private theorem complex_semigroup_bound {ι : Type*} [Fintype ι]
    (f : (ι → ℂ) →L[ℂ] (ι → ℂ))
    (hf : ∀ μ ∈ spectrum ℂ f.toLinearMap, μ.re < 0) :
    ∃ M α : ℝ, 0 < M ∧ 0 < α ∧ ∀ t : ℝ, 0 ≤ t → ∀ v : ι → ℂ,
      ‖(NormedSpace.exp (t • f)) v‖ ≤ M * Real.exp (-(α * t)) * ‖v‖ := by
  classical
  let s := (Module.End.finite_spectrum f.toLinearMap).toFinset
  obtain ⟨α, hα, hgap⟩ := finite_spectral_gap s (by simpa [s] using hf)
  have hgap' : ∀ μ ∈ spectrum ℂ f.toLinearMap, μ.re + α < 0 := by
    simpa [s] using hgap
  choose C hC hbound using fun j : ι =>
    complex_vector_bound f α hgap' (Pi.single j 1)
  have hsum : 0 ≤ ∑ j, C j := Finset.sum_nonneg fun j hj => hC j
  refine ⟨(∑ j, C j) + 1, α, by linarith, hα, ?_⟩
  intro t ht v
  have hexpand : v = ∑ j, v j • Pi.single j (1 : ℂ) := by
    ext i
    simp [Pi.single_apply]
  calc
    ‖(NormedSpace.exp (t • f)) v‖ =
        ‖∑ j, v j • (NormedSpace.exp (t • f)) (Pi.single j 1)‖ := by
      conv_lhs => rw [hexpand]
      simp
    _ ≤ ∑ j, ‖v j • (NormedSpace.exp (t • f)) (Pi.single j 1)‖ := norm_sum_le _ _
    _ ≤ ∑ j, C j * Real.exp (-(α * t)) * ‖v‖ := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_smul, mul_comm]
      exact mul_le_mul (hbound j t ht) (norm_le_pi_norm v j)
        (norm_nonneg _) (mul_nonneg (hC j) (Real.exp_nonneg _))
    _ = (∑ j, C j) * Real.exp (-(α * t)) * ‖v‖ := by
      rw [Finset.sum_mul, Finset.sum_mul]
    _ ≤ ((∑ j, C j) + 1) * Real.exp (-(α * t)) * ‖v‖ := by gcongr; linarith

open scoped Matrix.Norms.Operator in
private theorem matrix_exp_to_clm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℂ) (t : ℝ) (v : ι → ℂ) :
    (NormedSpace.exp (t • LinearMap.toContinuousLinearMap B.toLin')) v =
      NormedSpace.exp (t • B) *ᵥ v := by
  let e : Matrix ι ι ℂ ≃ₐ[ℂ] ((ι → ℂ) →L[ℂ] (ι → ℂ)) :=
    Matrix.toLinAlgEquiv'.trans (Module.End.toContinuousLinearMap (ι → ℂ))
  let := NormedAlgebra.restrictScalars ℚ ℂ ((ι → ℂ) →L[ℂ] (ι → ℂ))
  have he : e (t • B) = t • e B := e.toLinearMap.map_smul_of_tower t B
  have hexp := NormedSpace.map_exp e e.toLinearMap.continuous_of_finiteDimensional (t • B)
  rw [he] at hexp
  change (NormedSpace.exp (t • e B)) v = _
  rw [← hexp]
  rfl

open scoped Matrix.Norms.Operator in
private theorem matrix_exp_ofReal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) :
    (NormedSpace.exp A).map (algebraMap ℝ ℂ) =
      NormedSpace.exp (A.map (algebraMap ℝ ℂ)) := by
  apply NormedSpace.map_exp Complex.ofRealHom.mapMatrix _ A
  change Continuous (fun A : Matrix ι ι ℝ => fun i j => (A i j : ℂ))
  fun_prop

private theorem complexification_norm {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    ‖fun i => (v i : ℂ)‖ = ‖v‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
    intro i
    simpa using norm_le_pi_norm v i
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (fun i => (v i : ℂ)))).mpr
    intro i
    simpa using norm_le_pi_norm (fun i => (v i : ℂ)) i


namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Exponential decay of a Hurwitz semigroup.** If `A` is Hurwitz, there are `M, α > 0`
with `‖exp(t A) v‖ ≤ M e^{-α t} ‖v‖` for all `t ≥ 0` and all vectors `v`. -/
theorem IsHurwitz.exists_norm_exp_smul_mulVec_le {A : Matrix ι ι ℝ} (hA : A.IsHurwitz) :
    ∃ M α : ℝ, 0 < M ∧ 0 < α ∧ ∀ t : ℝ, 0 ≤ t → ∀ v : ι → ℝ,
      ‖NormedSpace.exp (t • A) *ᵥ v‖ ≤ M * exp (-(α * t)) * ‖v‖ := by
  let B := A.map (algebraMap ℝ ℂ)
  let f := LinearMap.toContinuousLinearMap B.toLin'
  have hf : ∀ μ ∈ spectrum ℂ f.toLinearMap, μ.re < 0 := by
    simpa [f, B, Matrix.spectrum_toLin', IsHurwitz] using hA
  obtain ⟨M, α, hM, hα, hbound⟩ := complex_semigroup_bound f hf
  refine ⟨M, α, hM, hα, ?_⟩
  intro t ht v
  have hmap : (t • A).map (algebraMap ℝ ℂ) = t • B := by
    ext i j
    simp [B, Complex.real_smul]
  have hvec : (fun i => ((NormedSpace.exp (t • A) *ᵥ v) i : ℂ)) =
      NormedSpace.exp (t • B) *ᵥ (fun i => (v i : ℂ)) := by
    ext i
    rw [← hmap, ← matrix_exp_ofReal]
    exact RingHom.map_mulVec (algebraMap ℝ ℂ) _ _ i
  have h := hbound t ht (fun i => (v i : ℂ))
  rw [matrix_exp_to_clm B t, ← hvec, complexification_norm, complexification_norm] at h
  exact h

end Matrix

namespace MathlibExt.Analysis.ODE.LinearizedStability

open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem remainder_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → ℝ) → ι → ℝ} {xstar : ι → ℝ} {A : Matrix ι ι ℝ}
    (hf : f xstar = 0)
    (hfA : HasFDerivAt f (LinearMap.toContinuousLinearMap (Matrix.toLin' A)) xstar)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∀ y : ι → ℝ, ‖y‖ < r → ‖f (xstar + y) - A *ᵥ y‖ ≤ ε * ‖y‖ := by
  have h := (hasFDerivAt_iff_isLittleO_nhds_zero.mp hfA).def hε
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff_ball.mp h
  refine ⟨r, hr, fun y hy => ?_⟩
  simpa [hf, Matrix.toLin'_apply] using hb y (by simpa using hy)

private theorem transformed_deriv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) {y : ℝ → ι → ℝ} {y' : ι → ℝ} {s : ℝ}
    (hy : HasDerivAt y y' s) (t : ℝ) :
    HasDerivAt (fun u => NormedSpace.exp ((t - u) • A) *ᵥ y u)
      (NormedSpace.exp ((t - s) • A) *ᵥ (y' - A *ᵥ y s)) s := by
  open scoped Matrix.Norms.Operator in
    have he := (hasDerivAt_exp_smul_const (𝕂 := ℝ) A (t - s)).scomp s
      ((hasDerivAt_const s t).sub (hasDerivAt_id s))
  apply hasDerivAt_pi.mpr
  intro i
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
    ((hasDerivAt_pi.mp (hasDerivAt_pi.mp he i) j).mul (hasDerivAt_pi.mp hy j)))
  convert hsum using 1
  · rfl
  · simp only [Function.comp_apply, zero_sub, Matrix.smul_apply, smul_eq_mul,
      neg_mul, one_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    change (NormedSpace.exp ((t - s) • A) *ᵥ (y' - A *ᵥ y s)) i =
      -((NormedSpace.exp ((t - s) • A) * A) *ᵥ y s) i +
        (NormedSpace.exp ((t - s) • A) *ᵥ y') i
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec]
    simp only [Pi.sub_apply]
    ring

private theorem interval_decay {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) {M b t : ℝ} (hM : 0 < M) (hb : 0 < b) (ht : 0 ≤ t)
    (hE : ∀ u : ℝ, 0 ≤ u → ∀ v : ι → ℝ,
      ‖NormedSpace.exp (u • A) *ᵥ v‖ ≤ M * exp (-(2 * b * u)) * ‖v‖)
    {y y' : ℝ → ι → ℝ} (hy : ∀ s ∈ Set.Icc 0 t, HasDerivAt y (y' s) s)
    (hr : ∀ s ∈ Set.Ico 0 t, ‖y' s - A *ᵥ y s‖ ≤ b / (2 * M) * ‖y s‖) :
    ‖y t‖ ≤ 2 * M * exp (-(b * t)) * ‖y 0‖ := by
  have hc : ContinuousOn y (Set.Icc 0 t) :=
    fun s hs => (hy s hs).continuousAt.continuousWithinAt
  have hw : ContinuousOn (fun s => exp (b * s) * ‖y s‖) (Set.Icc 0 t) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul hc.norm
  obtain ⟨u, hu, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr ht) hw
  let W := exp (b * u) * ‖y u‖
  have hW : 0 ≤ W := by positivity
  have hbound : ∀ s ∈ Set.Icc 0 t, ‖y s‖ ≤ W / exp (b * s) := by
    intro s hs
    apply (le_div_iff₀ (exp_pos _)).mpr
    simpa [mul_comm] using hmax hs
  let B := fun s => exp (-(2 * b * u)) *
    (M * ‖y 0‖ + W / 2 * (exp (b * s) - 1))
  let B' := fun s => b / 2 * exp (-(2 * b * u)) * exp (b * s) * W
  have hB : ∀ s, HasDerivAt B (B' s) s := by
    intro s
    have hd := (((hasDerivAt_id s).const_mul b).exp.sub_const 1).const_mul (W / 2)
    convert (hd.const_add (M * ‖y 0‖)).const_mul (exp (-(2 * b * u))) using 1
    · rfl
    · dsimp [B']
      ring
  have hstart : ‖NormedSpace.exp ((u - 0) • A) *ᵥ y 0‖ ≤ B 0 := by
    simpa [B, mul_comm, mul_left_comm, mul_assoc] using hE u hu.1 (y 0)
  have hd_bound : ∀ s ∈ Set.Ico 0 u,
      ‖NormedSpace.exp ((u - s) • A) *ᵥ (y' s - A *ᵥ y s)‖ ≤ B' s := by
    intro s hs
    have hst : s ∈ Set.Icc 0 t := ⟨hs.1, hs.2.le.trans hu.2⟩
    have hrt := hr s ⟨hs.1, hs.2.trans_le hu.2⟩
    have heq : exp (-(2 * b * (u - s))) =
        exp (-(2 * b * u)) * exp (b * s) * exp (b * s) := by
      rw [← exp_add, ← exp_add]
      congr 1
      ring
    calc
      _ ≤ M * exp (-(2 * b * (u - s))) * ‖y' s - A *ᵥ y s‖ :=
        hE (u - s) (sub_nonneg.mpr hs.2.le) _
      _ ≤ M * exp (-(2 * b * (u - s))) * (b / (2 * M) * (W / exp (b * s))) := by
        gcongr
        exact hrt.trans (mul_le_mul_of_nonneg_left (hbound s hst) (by positivity))
      _ = B' s := by
        rw [heq]
        dsimp [B']
        field_simp
  have hz : ContinuousOn (fun s => NormedSpace.exp ((u - s) • A) *ᵥ y s)
      (Set.Icc 0 u) := by
    intro s hs
    exact (transformed_deriv A (hy s ⟨hs.1, hs.2.trans hu.2⟩) u).continuousAt.continuousWithinAt
  have hzu := image_norm_le_of_norm_deriv_right_le_deriv_boundary hz
    (fun s hs => (transformed_deriv A (hy s ⟨hs.1, hs.2.le.trans hu.2⟩) u).hasDerivWithinAt)
    hstart hB hd_bound (Set.right_mem_Icc.mpr hu.1)
  have hlocal : ‖y u‖ ≤ exp (-(2 * b * u)) *
      (M * ‖y 0‖ + W / 2 * (exp (b * u) - 1)) := by
    simpa [B, NormedSpace.exp_zero] using hzu
  have hexp : exp (b * u) * exp (-(2 * b * u)) = exp (-(b * u)) := by
    rw [← exp_add]
    congr 1
    ring
  have hinv : exp (-(b * u)) * exp (b * u) = 1 := by
    rw [← exp_add]
    simp
  have hsmall : exp (-(b * u)) ≤ 1 := exp_le_one_iff.mpr (by nlinarith [hu.1])
  have hineq : W ≤ M * ‖y 0‖ + W / 2 := by
    calc
      W ≤ exp (b * u) * (exp (-(2 * b * u)) *
          (M * ‖y 0‖ + W / 2 * (exp (b * u) - 1))) :=
        mul_le_mul_of_nonneg_left hlocal (le_of_lt (exp_pos _))
      _ = exp (-(b * u)) * (M * ‖y 0‖) +
          W / 2 * (1 - exp (-(b * u))) := by
        rw [← mul_assoc, hexp]
        nlinarith [hinv]
      _ ≤ M * ‖y 0‖ + W / 2 := by
        have hn : 0 ≤ M * ‖y 0‖ := by positivity
        nlinarith [exp_pos (-(b * u))]
  have hfinal : ‖y t‖ ≤ (2 * M * ‖y 0‖) / exp (b * t) :=
    (hbound t (Set.right_mem_Icc.mpr ht)).trans (by gcongr; linarith)
  simpa [div_eq_mul_inv, ← exp_neg, mul_assoc, mul_comm, mul_left_comm] using hfinal

/-- **Lyapunov's indirect method (linearized stability).** Let `f (x⋆) = 0` and let `f` be
differentiable at `x⋆` with Jacobian matrix `A`. If `A` is Hurwitz, then `x⋆` is locally
exponentially stable: for some `δ, C, α > 0`, every solution of `x' = f(x)` on `[0, ∞)` with
`‖x(0) - x⋆‖ < δ` satisfies `‖x(t) - x⋆‖ ≤ C e^{-α t} ‖x(0) - x⋆‖` for all `t ≥ 0`
(Khalil 2002, Theorem 4.7, which assumes `f` is `C¹` and concludes asymptotic stability). -/
theorem exists_locallyExponentiallyStable_of_hasFDerivAt {f : (ι → ℝ) → ι → ℝ}
    {xstar : ι → ℝ} {A : Matrix ι ι ℝ} (hf : f xstar = 0)
    (hfA : HasFDerivAt f (LinearMap.toContinuousLinearMap (Matrix.toLin' A)) xstar)
    (hA : A.IsHurwitz) :
    ∃ δ C α : ℝ, 0 < δ ∧ 0 < C ∧ 0 < α ∧ ∀ x : ℝ → ι → ℝ,
      (∀ t, 0 ≤ t → HasDerivAt x (f (x t)) t) → ‖x 0 - xstar‖ < δ →
        ∀ t, 0 ≤ t → ‖x t - xstar‖ ≤ C * exp (-(α * t)) * ‖x 0 - xstar‖ := by
  obtain ⟨M₀, a, hM₀, ha, hE₀⟩ := hA.exists_norm_exp_smul_mulVec_le
  let M := M₀ + 1
  let b := a / 2
  have hM : 0 < M := by dsimp [M]; linarith
  have hMone : 1 ≤ M := by dsimp [M]; linarith
  have hb : 0 < b := by dsimp [b]; positivity
  have hE : ∀ u : ℝ, 0 ≤ u → ∀ v : ι → ℝ,
      ‖NormedSpace.exp (u • A) *ᵥ v‖ ≤ M * exp (-(2 * b * u)) * ‖v‖ := by
    intro u hu v
    have heq : 2 * b * u = a * u := by dsimp [b]; ring
    rw [heq]
    exact (hE₀ u hu v).trans (by dsimp [M]; gcongr; linarith)
  obtain ⟨r, hr, hrem⟩ := remainder_bound hf hfA (show 0 < b / (2 * M) by positivity)
  refine ⟨r / (4 * M), 2 * M, b, by positivity, by positivity, hb, ?_⟩
  intro x hx hx₀
  let y := fun t => x t - xstar
  let y' := fun t => f (x t)
  have hy : ∀ s, 0 ≤ s → HasDerivAt y (y' s) s := by
    intro s hs
    exact (hx s hs).sub_const xstar
  have hsmall : 2 * M * ‖y 0‖ < r / 2 := by
    have hi := (lt_div_iff₀ (show 0 < 4 * M by positivity)).mp hx₀
    change ‖y 0‖ * (4 * M) < r at hi
    nlinarith
  have hinit : ‖y 0‖ ≤ r / 2 := by
    nlinarith [norm_nonneg (y 0)]
  have hlocal : ∀ t, 0 ≤ t →
      (∀ s ∈ Set.Ico 0 t, ‖y s‖ < r) →
      ‖y t‖ ≤ 2 * M * exp (-(b * t)) * ‖y 0‖ := by
    intro t ht hs
    apply interval_decay A hM hb ht hE (fun s hs => hy s hs.1)
    intro s hst
    have heq : xstar + y s = x s := by dsimp [y]; abel
    simpa [y', heq] using hrem (y s) (hs s hst)
  have hstay : ∀ t, 0 ≤ t → ‖y t‖ ≤ r / 2 := by
    intro t ht
    let S := {s : ℝ | ‖y s‖ ≤ r / 2}
    have hc : ContinuousOn y (Set.Icc 0 t) :=
      fun s hs => (hy s hs.1).continuousAt.continuousWithinAt
    have hclosed : IsClosed (S ∩ Set.Icc 0 t) := by
      simpa only [S, ← Set.Iic_def, Set.preimage_ofPred_eq, Set.inter_comm] using
        hc.norm.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_Iic (a := r / 2))
    have hsub : Set.Icc 0 t ⊆ S := by
      apply hclosed.Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset hinit
      intro u hu hprev
      have hlu := hlocal u hu.1 (fun s hs =>
        (hprev ⟨hs.1, hs.2.le⟩).trans_lt (by linarith))
      have hexp : exp (-(b * u)) ≤ 1 := exp_le_one_iff.mpr (by nlinarith [hu.1])
      have hlt : ‖y u‖ < r / 2 := by
        have hle : 2 * M * exp (-(b * u)) * ‖y 0‖ ≤ 2 * M * ‖y 0‖ := by
          calc
            _ ≤ 2 * M * 1 * ‖y 0‖ := by gcongr
            _ = _ := by ring
        exact (hlu.trans hle).trans_lt hsmall
      have hn : S ∈ 𝓝 u :=
        ((hy u hu.1).continuousAt.norm.eventually (gt_mem_nhds hlt)).mono
          (fun s hs => hs.le)
      exact mem_nhdsWithin_of_mem_nhds hn
    exact hsub (Set.right_mem_Icc.mpr ht)
  intro t ht
  exact hlocal t ht (fun s hs => (hstay s hs.1).trans_lt (by linarith))

end MathlibExt.Analysis.ODE.LinearizedStability
