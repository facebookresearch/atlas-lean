/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.GLM.IRLSConvergence
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

open Filter Metric Set Topology
open MathlibExt.Probability.Statistics.GLM.IRLSConvergence

/-! ### Boundary cases computed from the definitions -/

-- The constant `L / 2` in `norm_sub_sub_fderiv_le` is sharp: for `U x = x²` (`H x = 2 x`,
-- `L = 2`), the remainder between `0` and `1` equals `L / 2 * ‖1 - 0‖² = 1`.
example :
    ‖(1 : ℝ) ^ 2 - (0 : ℝ) ^ 2 - (2 * (0 : ℝ)) * (1 - 0)‖ = 2 / 2 * ‖(1 : ℝ) - 0‖ ^ 2 := by
  norm_num

-- The Lipschitz-derivative bound itself, instantiated at that sharp case.
private theorem smul_id_sub_smul_id (a c : ℝ) :
    a • ContinuousLinearMap.id ℝ ℝ - c • ContinuousLinearMap.id ℝ ℝ =
      (a - c) • ContinuousLinearMap.id ℝ ℝ := by
  ext
  simp

private theorem norm_smul_id_le (a : ℝ) : ‖a • ContinuousLinearMap.id ℝ ℝ‖ ≤ ‖a‖ := by
  rw [norm_smul]
  exact mul_le_of_le_one_right (norm_nonneg _) ContinuousLinearMap.norm_id_le

example :
    ‖(1 : ℝ) ^ 2 - (0 : ℝ) ^ 2 - ((2 * (0 : ℝ)) • ContinuousLinearMap.id ℝ ℝ) (1 - 0)‖ ≤
      2 / 2 * ‖(1 : ℝ) - 0‖ ^ 2 := by
  refine norm_sub_sub_fderiv_le (U := fun x : ℝ => x ^ 2)
    (H := fun x : ℝ => (2 * x) • ContinuousLinearMap.id ℝ ℝ) (s := univ) convex_univ
    (fun z _ => ?_) (fun z _ => ?_) (mem_univ _) (mem_univ _)
  · convert (hasDerivAt_pow 2 z).hasFDerivAt using 1
    ext
    simp
  · rw [smul_id_sub_smul_id, ← mul_sub]
    refine (norm_smul_id_le _).trans ?_
    rw [norm_mul]
    norm_num

-- The threshold `M δ ≤ 1/2` in the perturbation bound is exact. With `A₀ = A₀inv = id`,
-- `A = (1 - δ) • id` and `M = 1`, every other hypothesis holds, and for `1/2 < δ < 3/2` the
-- conclusion `‖v‖ ≤ 2 M ‖A v‖` fails at `v = 1`.
example (δ : ℝ) (h1 : 1 / 2 < δ) (h2 : δ < 3 / 2) :
    (∀ v : ℝ, ContinuousLinearMap.id ℝ ℝ (ContinuousLinearMap.id ℝ ℝ v) = v) ∧
      ‖ContinuousLinearMap.id ℝ ℝ‖ ≤ 1 ∧
      ‖ContinuousLinearMap.id ℝ ℝ - (1 - δ) • ContinuousLinearMap.id ℝ ℝ‖ ≤ δ ∧
      ¬ (‖(1 : ℝ)‖ ≤ 2 * 1 * ‖((1 - δ) • ContinuousLinearMap.id ℝ ℝ) 1‖) := by
  refine ⟨fun v => rfl, ContinuousLinearMap.norm_id_le, ?_, ?_⟩
  · have h : ContinuousLinearMap.id ℝ ℝ - (1 - δ) • ContinuousLinearMap.id ℝ ℝ =
        δ • ContinuousLinearMap.id ℝ ℝ := by
      ext
      simp
    rw [h]
    refine (norm_smul_id_le δ).trans (le_of_eq ?_)
    rw [Real.norm_eq_abs, abs_of_pos (by linarith)]
  · intro h
    have h' : 1 ≤ 2 * |1 - δ| := by simpa using h
    have : |1 - δ| < 1 / 2 := abs_lt.2 ⟨by linarith, by linarith⟩
    linarith

-- At the threshold `δ = 1/2` the bound applies, and it holds with equality.
example (v : ℝ) :
    ‖v‖ ≤ 2 * 1 * ‖((1 - 1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ) v‖ := by
  refine norm_le_two_mul_norm_apply (A₀ := ContinuousLinearMap.id ℝ ℝ)
    (A₀inv := ContinuousLinearMap.id ℝ ℝ) (δ := 1 / 2) (fun _ => rfl)
    ContinuousLinearMap.norm_id_le ?_ (by norm_num) v
  have h : ContinuousLinearMap.id ℝ ℝ - (1 - 1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ =
      (1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ := by
    ext
    norm_num
  rw [h]
  refine (norm_smul_id_le _).trans (le_of_eq ?_)
  norm_num

/-! ### Gaussian linear model: Fisher scoring reaches the root in one step

For the normal family with identity (canonical) link and one observation `y` with covariate `a`,
the score is `U β = a (y - a β)` and the Fisher information is `I β = a²`, constant, so `L = 0`. -/

-- The Fisher-scoring step `T β = β + U β / a² = y / a` lands on the root, from any start.
example (a y β : ℝ) (ha : a ≠ 0) : β + a * (y - a * β) / a ^ 2 = y / a := by
  field_simp
  ring

-- The root is `y / a`, computed from the score.
example (a y : ℝ) (ha : a ≠ 0) : a * (y - a * (y / a)) = 0 := by
  field_simp
  ring

-- Non-vacuity at `L = 0`: `fisherScoring_local_convergence` applies with `ε = r` for any `r`.
example (a y : ℝ) (ha : a ≠ 0) (β₀ : ℝ) (r : ℝ) (hβ₀ : β₀ ∈ ball (y / a) r) :
    Tendsto (fun n => (fun _ : ℝ => y / a)^[n] β₀) atTop (𝓝 (y / a)) := by
  have h := fisherScoring_local_convergence (U := fun β : ℝ => a * (y - a * β))
    (I := fun _ => (a ^ 2) • ContinuousLinearMap.id ℝ ℝ)
    (I₀inv := (a ^ 2)⁻¹ • ContinuousLinearMap.id ℝ ℝ) (T := fun _ => y / a)
    (r := r) (ε := r) (M := ‖(a ^ 2)⁻¹ • ContinuousLinearMap.id ℝ ℝ‖) (L := 0)
    (by field_simp; ring)
    (fun x _ => by
      have := ((hasDerivAt_id x).const_mul (a ^ 2)).const_sub (a * y)
      convert this.hasFDerivAt using 1
      · funext t; simp; ring
      · ext; simp)
    (fun x _ y _ => by simp) (fun v => by simp [ha]) le_rfl
    (fun x _ => by simp; field_simp) le_rfl (by simp) hβ₀
  exact h.2.2.2.2

/-! ### A nonlinear score: `U β = -β - β² / 2`, `I β = β + 1`

`I` is `1`-Lipschitz, `I 0 = 1`, the root is `0`, and the Fisher-scoring map is
`T β = β² / (2 (β + 1))`. -/

/-- The information `β ↦ (β + 1) • id`. -/
private noncomputable abbrev infoEx (β : ℝ) : ℝ →L[ℝ] ℝ := (β + 1) • ContinuousLinearMap.id ℝ ℝ

/-- The score `β ↦ -β - β² / 2`. -/
private noncomputable abbrev scoreEx (β : ℝ) : ℝ := -β - β ^ 2 / 2

/-- The Fisher-scoring map `β ↦ β² / (2 (β + 1))`. -/
private noncomputable abbrev stepEx (β : ℝ) : ℝ := β ^ 2 / (2 * (β + 1))

-- The scoring map solves `I β (T β - β) = U β` away from `β = -1`, computed from definitions.
example (β : ℝ) (hβ : β + 1 ≠ 0) : infoEx β (stepEx β - β) = scoreEx β := by
  simp only [infoEx, stepEx, scoreEx, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.coe_id', id_eq, smul_eq_mul]
  field_simp
  ring

-- Quadratic error decay, computed from definitions: one step from `1/4` gives `1/40`.
example : stepEx (1 / 4) = 1 / 40 := by
  norm_num [stepEx]

-- At `β = -1` the information vanishes and the scoring equation has no solution, so some
-- radius restriction (`2 M L ε ≤ 1`, here `ε ≤ 1/2`) is needed.
example : ¬ ∃ t : ℝ, infoEx (-1) (t - (-1)) = scoreEx (-1) := by
  rintro ⟨t, ht⟩
  simp only [infoEx, scoreEx, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.coe_id', id_eq, smul_eq_mul] at ht
  norm_num at ht

/-! ### Non-vacuity: the hypotheses of the main theorems are satisfiable -/

private theorem hasFDerivAt_scoreEx (x : ℝ) : HasFDerivAt scoreEx (-infoEx x) x := by
  have h : HasDerivAt scoreEx (-1 - x) x := by
    have h' := ((hasDerivAt_id x).neg).sub ((hasDerivAt_pow 2 x).div_const 2)
    convert h' using 1
    · funext t
      simp [scoreEx, sub_eq_add_neg]
    · norm_num
  convert h.hasFDerivAt using 1
  ext
  simp
  ring

private theorem infoEx_lipschitz (x y : ℝ) : ‖infoEx x - infoEx y‖ ≤ 1 * ‖x - y‖ := by
  rw [infoEx, infoEx, smul_id_sub_smul_id, add_sub_add_right_eq_sub, one_mul]
  exact norm_smul_id_le _

private theorem stepEx_spec (x : ℝ) (hx : x ∈ ball (0 : ℝ) (1 / 2)) :
    infoEx x (stepEx x - x) = scoreEx x := by
  have hx' : -(1 / 2 : ℝ) < x := by
    rw [mem_ball, Real.dist_eq, sub_zero] at hx
    linarith [neg_abs_le x]
  have hne : x + 1 ≠ 0 := by linarith
  simp only [infoEx, stepEx, scoreEx, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.coe_id', id_eq, smul_eq_mul]
  field_simp
  ring

-- Fisher scoring converges to the root `0` from every start in `ball 0 (1/2)`, with the
-- quadratic bound `‖Tⁿ⁺¹ β₀‖ ≤ ‖Tⁿ β₀‖²` (`M = L = 1`).
example (β₀ : ℝ) (hβ₀ : β₀ ∈ ball (0 : ℝ) (1 / 2)) :
    (∀ n, ‖stepEx^[n + 1] β₀ - 0‖ ≤ 1 * 1 * ‖stepEx^[n] β₀ - 0‖ ^ 2) ∧
      Tendsto (fun n => stepEx^[n] β₀) atTop (𝓝 0) := by
  have h := fisherScoring_local_convergence (U := scoreEx) (I := infoEx)
    (I₀inv := ContinuousLinearMap.id ℝ ℝ) (r := 1 / 2) (M := 1) (L := 1)
    (by norm_num [scoreEx]) (fun x _ => hasFDerivAt_scoreEx x)
    (fun x _ y _ => infoEx_lipschitz x y) (fun v => by simp [infoEx])
    ContinuousLinearMap.norm_id_le stepEx_spec le_rfl (by norm_num) hβ₀
  exact ⟨h.2.1, h.2.2.2.2⟩

-- The root `0` is the only score zero in `ball 0 (1/2)`; the other zero `-2` lies outside.
example : scoreEx (-2) = 0 ∧ (-2 : ℝ) ∉ ball (0 : ℝ) (1 / 2) := by
  constructor
  · norm_num [scoreEx]
  · rw [mem_ball, Real.dist_eq]
    norm_num

example (β : ℝ) (hβ : β ∈ ball (0 : ℝ) (1 / 2)) (h0 : scoreEx β = 0) : β = 0 :=
  eq_of_score_eq_zero (U := scoreEx) (H := fun x => -infoEx x)
    (H₀inv := -ContinuousLinearMap.id ℝ ℝ) (r := 1 / 2) (M := 1) (L := 1)
    (by norm_num [scoreEx]) (fun x _ => hasFDerivAt_scoreEx x)
    (fun x _ y _ => by rw [← neg_sub', norm_neg]; exact infoEx_lipschitz x y)
    (fun v => by simp [infoEx]) (by simp) le_rfl
    (by norm_num) hβ h0

-- In finite dimension a Newton map exists on the ball without being supplied.
example : ∃ T : ℝ → ℝ, ∀ x ∈ ball (0 : ℝ) (1 / 2),
    (fun x => -infoEx x) x (T x - x) = -scoreEx x :=
  exists_newton_map (H := fun x => -infoEx x) (H₀inv := -ContinuousLinearMap.id ℝ ℝ)
    (r := 1 / 2) (M := 1) (L := 1)
    (fun x _ y _ => by rw [← neg_sub', norm_neg]; exact infoEx_lipschitz x y)
    (fun v => by simp [infoEx]) (by simp) le_rfl
    (by norm_num)

/-! ### The IRLS step satisfies the Newton equations

Values below are computed from the definitions of `irlsWeights`, `weightedGram`,
`workingResponse` and `wlsClosedForm`, not through `irlsStep_fisherScoring_eq`. -/

section IRLSNewton

open Matrix
open MathlibExt.Probability.Statistics.GLM.IRLS

/-! #### Nonzero weights and an invertible Gram matrix

Two observations `y = (2, 5)` with covariates `X = (1, 2)ᵀ`, one coefficient, mean function
`mean η = η³/3 + η` and weight `weight η = η² + 1 = mean' η`. At `β = 1` the linear predictor is
`η = (1, 2)`, the weights are `(2, 5)`, the Gram matrix is `[22]`, the score is
`Xᵀ (y - μ) = 1 · (2 - 4/3) + 2 · (5 - 14/3) = 4/3`, and the IRLS step is `35/33`. -/

/-- The design `X = (1, 2)ᵀ`. -/
private def Xn : Matrix (Fin 2) (Fin 1) ℝ := !![1; 2]

/-- The responses `y = (2, 5)`. -/
private def yn : Fin 2 → ℝ := ![2, 5]

/-- The mean function `η ↦ η³/3 + η`. -/
private noncomputable def meann (η : ℝ) : ℝ := η ^ 3 / 3 + η

/-- The weight function `η ↦ η² + 1`, the derivative of `meann`. -/
private def weightn (η : ℝ) : ℝ := η ^ 2 + 1

private theorem hasDerivAt_meann (x : ℝ) : HasDerivAt meann (weightn x) x := by
  have h := ((hasDerivAt_pow 3 x).div_const 3).add (hasDerivAt_id x)
  have hf : ((fun y : ℝ => y ^ 3 / 3) + id) = meann := by
    funext y
    simp [meann]
  rw [hf] at h
  convert h using 1
  norm_num [weightn]

private theorem irlsWeights_n : irlsWeights weightn Xn ![1] = ![2, 5] := by
  funext i
  fin_cases i <;> norm_num [irlsWeights, weightn, Xn, mulVec, dotProduct]

private theorem weightedGram_n : weightedGram Xn ![2, 5] = !![22] := by
  ext i j
  fin_cases i
  fin_cases j
  norm_num [weightedGram, Xn, Matrix.mul_apply, Fin.sum_univ_two]

private theorem irlsWeights_n_ne_zero : ∀ i, irlsWeights weightn Xn ![1] i ≠ 0 := by
  rw [irlsWeights_n]
  intro i
  fin_cases i <;> norm_num

private theorem isUnit_weightedGram_n : IsUnit (weightedGram Xn (irlsWeights weightn Xn ![1])) := by
  rw [irlsWeights_n, weightedGram_n, isUnit_iff_isUnit_det]
  norm_num

-- The IRLS step from `β = 1`, computed from the closed form `(Xᵀ W X)⁻¹ Xᵀ W z` with the
-- working response `z = η + (y - μ) / w = (4/3, 31/15)`.
private theorem irlsStep_n : irlsStep Xn yn meann weightn ![1] = ![35 / 33] := by
  rw [irlsStep, wlsClosedForm_eq irlsWeights_n_ne_zero, irlsWeights_n, weightedGram_n]
  funext i
  fin_cases i
  norm_num [workingResponse, meann, weightn, Xn, yn, Matrix.inv_def, mulVec, dotProduct,
    Fin.sum_univ_two]

-- The Fisher-scoring equation at `β = 1`, computed from the definitions: `22 · (35/33 - 1)` and
-- the score both equal `4/3`.
example :
    LinearMap.toContinuousLinearMap (Matrix.toLin' (weightedGram Xn (irlsWeights weightn Xn ![1])))
        (![35 / 33] - ![1]) =
      Xnᵀ *ᵥ (yn - fun i => meann ((Xn *ᵥ ![1]) i)) := by
  rw [irlsWeights_n, weightedGram_n]
  funext i
  fin_cases i
  norm_num [meann, Xn, yn, mulVec, dotProduct, Fin.sum_univ_two]

-- `irlsStep_fisherScoring_eq` gives the same equation for `irlsStep`, whose value is `35/33`.
example :
    LinearMap.toContinuousLinearMap (Matrix.toLin' (weightedGram Xn (irlsWeights weightn Xn ![1])))
        (irlsStep Xn yn meann weightn ![1] - ![1]) =
      Xnᵀ *ᵥ (yn - fun i => meann ((Xn *ᵥ ![1]) i)) :=
  irlsStep_fisherScoring_eq ![1] irlsWeights_n_ne_zero isUnit_weightedGram_n

/-- The canonical score `Xᵀ (y - μ(β))` of the example. -/
private noncomputable def scoren (β : Fin 1 → ℝ) : Fin 1 → ℝ :=
  Xnᵀ *ᵥ (yn - fun i => meann ((Xn *ᵥ β) i))

/-- The Hessian `-Xᵀ W(β) X` of the example. -/
private def hessn (β : Fin 1 → ℝ) : Matrix (Fin 1) (Fin 1) ℝ :=
  -weightedGram Xn (irlsWeights weightn Xn β)

private theorem isCanonical_n : IsCanonicalScoreHessian Xn yn meann weightn scoren hessn :=
  ⟨fun _ => rfl, fun _ => rfl⟩

-- `hessn β` is the derivative of `scoren` at `β`, so the equation below is Newton's.
example (β : Fin 1 → ℝ) :
    HasFDerivAt scoren (LinearMap.toContinuousLinearMap (Matrix.toLin' (hessn β))) β :=
  isCanonical_n.hasFDerivAt hasDerivAt_meann β

-- The Newton equation `H β (T β - β) = -U β` at `β = 1` for `irlsStep`
-- (`irlsStep_newton_eq`), and its value `-4/3` computed from the definitions.
example :
    LinearMap.toContinuousLinearMap (Matrix.toLin' (hessn ![1]))
        (irlsStep Xn yn meann weightn ![1] - ![1]) = -scoren ![1] ∧
      -scoren ![1] = ![-4 / 3] := by
  refine ⟨irlsStep_newton_eq isCanonical_n ![1] irlsWeights_n_ne_zero isUnit_weightedGram_n, ?_⟩
  funext i
  fin_cases i
  norm_num [scoren, meann, Xn, yn, mulVec, dotProduct, Fin.sum_univ_two, Matrix.vecHead,
    Matrix.vecTail]

/-! #### A zero weight: the Newton form is not claimed

`X = (0, 1)ᵀ`, `y = (0, 2)`, `mean η = η²/2`, `weight η = η`, `β = 1`. The weights are
`(0, 1)`, so the nonzero-weight hypothesis fails, although the Gram matrix `[1]` is invertible.
The IRLS formula then inverts the singular `diag (0, 1)`, and `irlsStep` is the junk value `0`.
The Newton step is `1 + 3/2 = 5/2`, but `irlsStep` misses it: `1 · (0 - 1) = -1 ≠ 3/2`. -/

/-- The design `X = (0, 1)ᵀ`. -/
private def Xz : Matrix (Fin 2) (Fin 1) ℝ := !![0; 1]

/-- The responses `y = (0, 2)`. -/
private def yz : Fin 2 → ℝ := ![0, 2]

/-- The mean function `η ↦ η² / 2`. -/
private noncomputable def meanz (η : ℝ) : ℝ := η ^ 2 / 2

private theorem irlsWeights_z : irlsWeights id Xz ![1] = ![0, 1] := by
  funext i
  fin_cases i <;> norm_num [irlsWeights, Xz, mulVec, dotProduct]

example : ¬ ∀ i, irlsWeights id Xz ![1] i ≠ 0 := by
  rw [irlsWeights_z]
  intro h
  exact h 0 rfl

example : IsUnit (weightedGram Xz (irlsWeights id Xz ![1])) := by
  rw [irlsWeights_z, isUnit_iff_isUnit_det]
  norm_num [weightedGram, Xz, Matrix.mul_apply, Fin.sum_univ_two]

private theorem irlsStep_z : irlsStep Xz yz meanz id ![1] = ![0] := by
  have hV : (diagonal (irlsWeights id Xz ![1])⁻¹)⁻¹ = 0 := by
    refine Matrix.nonsing_inv_apply_not_isUnit _ ?_
    rw [irlsWeights_z, det_diagonal]
    norm_num [Fin.prod_univ_two]
  funext i
  fin_cases i
  simp [irlsStep, wlsClosedForm,
    MathlibExt.Probability.Statistics.GeneralizedLeastSquares.glsMatrix, hV]

-- `irlsStep` does not solve the Fisher-scoring equation.
example :
    LinearMap.toContinuousLinearMap (Matrix.toLin' (weightedGram Xz (irlsWeights id Xz ![1])))
        (irlsStep Xz yz meanz id ![1] - ![1]) ≠
      Xzᵀ *ᵥ (yz - fun i => meanz ((Xz *ᵥ ![1]) i)) := by
  rw [irlsStep_z, irlsWeights_z]
  intro h
  have := congrFun h 0
  norm_num [weightedGram, meanz, Xz, yz, mulVec, dotProduct, Matrix.mul_apply,
    Fin.sum_univ_two] at this

-- The Newton step `5/2` does solve it, so the failure is the junk value, not the system.
example :
    LinearMap.toContinuousLinearMap (Matrix.toLin' (weightedGram Xz (irlsWeights id Xz ![1])))
        (![5 / 2] - ![1]) =
      Xzᵀ *ᵥ (yz - fun i => meanz ((Xz *ᵥ ![1]) i)) := by
  rw [irlsWeights_z]
  funext i
  fin_cases i
  norm_num [weightedGram, meanz, Xz, yz, mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_two]

/-! #### A singular Gram matrix: the Newton form is not claimed

The Gaussian model with `X = [1 1]`, `y = 5`, `mean = id`, `weight = 1`, `β = 0`. The weights
are nonzero, but the Gram matrix `Xᵀ X = [[1, 1], [1, 1]]` is singular and `irlsStep` is the
junk value `0`. The Newton equation `Xᵀ X v = Xᵀ (y - X β) = (5, 5)` has solutions (for example
`v = (5, 0)`), but `v = irlsStep - β = 0` is not one. -/

/-- The design `X = [1 1]`. -/
private def Xs : Matrix (Fin 1) (Fin 2) ℝ := !![1, 1]

example : ∀ i, irlsWeights (fun _ => 1) Xs 0 i ≠ 0 := fun _ => one_ne_zero

example : ¬ IsUnit (weightedGram Xs (irlsWeights (fun _ => 1) Xs 0)) := by
  rw [isUnit_iff_isUnit_det]
  norm_num [weightedGram, irlsWeights, Xs, Matrix.det_fin_two, Matrix.mul_apply]

private theorem irlsStep_s : irlsStep Xs ![5] id (fun _ => 1) 0 = 0 := by
  simp [irlsStep, wlsClosedForm, Xs,
    MathlibExt.Probability.Statistics.GeneralizedLeastSquares.glsMatrix,
    Matrix.inv_def, Matrix.det_fin_two, Matrix.mul_apply]

-- `irlsStep` does not solve the Newton (here Fisher-scoring) equation.
example :
    LinearMap.toContinuousLinearMap
        (Matrix.toLin' (weightedGram Xs (irlsWeights (fun _ => 1) Xs 0)))
        (irlsStep Xs ![5] id (fun _ => 1) 0 - 0) ≠
      Xsᵀ *ᵥ (![5] - fun i => id ((Xs *ᵥ 0) i)) := by
  rw [irlsStep_s, sub_zero, map_zero]
  intro h
  have := congrFun h 0
  norm_num [Xs, mulVec, dotProduct] at this

-- The step `v = (5, 0)` does solve it.
example :
    LinearMap.toContinuousLinearMap
        (Matrix.toLin' (weightedGram Xs (irlsWeights (fun _ => 1) Xs 0)))
        ![5, 0] =
      Xsᵀ *ᵥ (![5] - fun i => id ((Xs *ᵥ 0) i)) := by
  funext i
  fin_cases i <;> norm_num [weightedGram, irlsWeights, Xs, mulVec, dotProduct, Matrix.mul_apply,
    Fin.sum_univ_two]

end IRLSNewton

#print axioms newton_local_convergence
#print axioms fisherScoring_local_convergence
#print axioms exists_newton_map
#print axioms eq_of_score_eq_zero
#print axioms norm_sub_sub_fderiv_le
#print axioms newton_step_error_le
#print axioms norm_le_two_mul_norm_apply
#print axioms irlsStep_fisherScoring_eq
#print axioms irlsStep_newton_eq
