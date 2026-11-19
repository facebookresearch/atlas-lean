/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Dynamics.Repressilator
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The six-variable repressilator: Hopf condition and periodic orbits

The mRNA–protein model of Elowitz and Leibler's repressilator, without leak (`α₀ = 0`), is

  `ṁᵢ = α / (1 + pᵢ₋₁ⁿ) - mᵢ`,   `ṗᵢ = -β (pᵢ - mᵢ)`,   `i ∈ ZMod 3`,        (EL)

with `α > 0` the maximal transcription rate, `β > 0` the ratio of protein to mRNA decay rates and
`n` the Hill coefficient. The state is `x : Fin 6 → ℝ` with `mᵢ = x i` and `pᵢ = x (i + 3)`, so
gene `0` is repressed by `p₂ = x 5`, gene `1` by `p₀ = x 3` and gene `2` by `p₁ = x 4`.
**This ODE form (EL) is frozen**: `vectorField n α β` is exactly its right-hand side.

The protein-only reduction of `MathlibExt.Biology.Dynamics.Repressilator` (T196) has a Hopf
point only for `n > 2`. The six-variable model already has Hopf points for `n = 2`, the Hill
coefficient of Elowitz and Leibler's standard regime; this file proves its Hopf condition, the
linear stability boundary and, under the same Hopf-theorem hypothesis as T196, periodic
orbits.

**Symmetric equilibrium.** With an equilibrium level `p ≥ 0` and `α = eqRate n p = p (1 + pⁿ)`
(T196's parametrization by the equilibrium level), the constant state `x = (p, …, p)` is an
equilibrium; for `n ≥ 1`, `α > 0` and `β ≠ 0` it is the only one in the closed nonnegative
orthant. The hypothesis `p ≥ 0` is needed: for `n = 1`, `β = 1` and `p = -2`,
`α = eqRate 1 (-2) = 2` and `(-2, …, -2)` is an equilibrium, but so is the nonnegative state
`(1, …, 1)`.

**Linearization.** At the symmetric equilibrium the Jacobian is the block matrix
`[[-I, -a P], [β I, -β I]]`, with `P` the cyclic shift and `a = gain n p = n pⁿ / (1 + pⁿ)` the
loop gain of T196. Its characteristic polynomial is

  `χ(λ) = ((λ + 1)(λ + β))³ + (a β)³ = (Q + a β) (Q - a β c) (Q - a β c̄)`,
  `Q = (λ + 1)(λ + β)`,   `c = e^{iπ/3} = 1/2 + i √3/2`.

**Stability boundary.** Writing `b = 1 + β` (`β > 0`, `a ≥ 0`), the equilibrium is linearly
stable when `3 a² β < (4 - 2 a) b²` and linearly unstable when `3 a² β > (4 - 2 a) b²`; this is
Elowitz and Leibler's boundary `(β + 1)² / β = 3 a² / (4 - 2 a)`. On the boundary
(`IsHopf a β`, `a > 0`) `iω`, `ω = √3 a β / (2 (1 + β))`, is a simple eigenvalue of the
linearization, and every eigenvalue on the imaginary axis is `iω` or `-iω`. The eigenvalue
curve `λ(μ) = (-(1 + β) + √D(μ)) / 2`, `D(μ) = (1 - β)² + 4 a(μ) β c` (principal square root),
passes through `iω` at a Hopf level and its real part crosses zero with positive speed.

**Standard regime.** For `n = 2`, `α = 216`, `β = 5` the symmetric equilibrium is linearly
unstable (`exists_re_pos_standardRegime`), whereas T196's reduction with `n = 2` is linearly
stable for every `α ≥ 0` (`Repressilator.re_neg_of_le_two`).

## Scope

Linear stability means every eigenvalue of the linearization has negative real part; the
nonlinear stability it implies is not proved. **The periodic orbits rest on the Hopf
theorem, which is a hypothesis, not a theorem proved here**: `exists_periodicOrbit` assumes
T196's `HopfBifurcationTheorem 6` (Mathlib has no Hopf bifurcation theorem) and verifies every
other hypothesis of it for (EL). The direction of the bifurcation (first Lyapunov coefficient),
the stability of the orbits, the global bifurcation diagram and the leaky model `α₀ > 0` are out
of scope.

## Main results

* `vectorField_const_eq_zero_iff`, `eq_const_of_vectorField_eq_zero`: the symmetric equilibrium
  and its uniqueness in the nonnegative orthant.
* `hasFDerivAt_vectorField`, `toMatrix'_fderiv_vectorField`: the linearization.
* `charpoly_jacobian`, `charpoly_map_jacobian`, `isRoot_iff`: the characteristic equation.
* `re_neg_of_isRoot`, `exists_re_pos_of_isRoot`: the Elowitz–Leibler stability boundary.
* `rootMultiplicity_hopf`, `eq_of_isRoot_of_re_eq_zero`, `hopfEigenvalue_hopf`,
  `hasDerivAt_hopfEigenvalue`, `re_hopfSpeed_pos`: the Hopf condition.
* `exists_re_pos_standardRegime`: instability at `n = 2`, `α = 216`, `β = 5`.
* `exists_periodicOrbit`: periodic orbits near a Hopf point, assuming the Hopf theorem.

## References

* M. B. Elowitz and S. Leibler, *A synthetic oscillatory network of transcriptional
  regulators*, Nature 403 (2000) 335–338 (the model, its stability boundary and the standard
  parameters).
* E. Hopf (1942) and J. E. Marsden and M. McCracken, *The Hopf Bifurcation and Its
  Applications*, Springer (1976) (the Hopf theorem stated as `HopfBifurcationTheorem`).
-/

@[expose] public section

open Filter Polynomial Real Set
open scoped Topology ContDiff

namespace MathlibExt.Biology.Dynamics.RepressilatorSixVar

open MathlibExt.Biology.Dynamics.Repressilator (eqRate gain linCharpoly HopfBifurcationTheorem
  one_add_pow_pos continuous_eqRate hasDerivAt_repression hasDerivAt_gain gain_nonneg gain_lt)

/-! ### The model -/

/-- The right-hand side of (EL): `ṁᵢ = α / (1 + pᵢ₋₁ⁿ) - mᵢ`, `ṗᵢ = -β (pᵢ - mᵢ)`, with
`mᵢ = x i`, `pᵢ = x (i + 3)`. -/
noncomputable def vectorField (n : ℕ) (α β : ℝ) (x : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![α / (1 + x 5 ^ n) - x 0, α / (1 + x 3 ^ n) - x 1, α / (1 + x 4 ^ n) - x 2,
    -β * (x 3 - x 0), -β * (x 4 - x 1), -β * (x 5 - x 2)]

/-- The cyclic shift `P` on `ℝ³`: `1` at the entries `(i, i - 1)`. -/
def shift : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun i j => if j = i - 1 then 1 else 0

/-- The Jacobian of (EL) at a symmetric equilibrium with loop gain `a`, in block form
`[[-I, -a P], [β I, -β I]]` (mRNA block first). -/
def jacobianBlocks (a β : ℝ) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ :=
  Matrix.fromBlocks (-1) (-a • shift) (β • 1) (-β • 1)

/-- The Jacobian of (EL) at a symmetric equilibrium with loop gain `a`. -/
def jacobian (a β : ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  !![-1, 0, 0, 0, 0, -a; 0, -1, 0, -a, 0, 0; 0, 0, -1, 0, -a, 0;
     β, 0, 0, -β, 0, 0; 0, β, 0, 0, -β, 0; 0, 0, β, 0, 0, -β]

/-- The Hopf condition (Elowitz–Leibler boundary) `3 a² β = (4 - 2 a) (1 + β)²`. -/
def IsHopf (a β : ℝ) : Prop := 3 * a ^ 2 * β = (4 - 2 * a) * (1 + β) ^ 2

/-- The Hopf frequency `ω = √3 a β / (2 (1 + β))`. -/
noncomputable def hopfFreq (a β : ℝ) : ℝ := √3 * a * β / (2 * (1 + β))

/-- The primitive sixth root of unity `c = 1/2 + i √3/2`. -/
noncomputable def rootSix : ℂ := ⟨1 / 2, √3 / 2⟩

/-- Its conjugate `c̄ = 1/2 - i √3/2`. -/
noncomputable def rootSixConj : ℂ := ⟨1 / 2, -(√3 / 2)⟩

/-- The quadratic `Q(λ) = (λ + 1)(λ + β)`. -/
noncomputable def quad (β : ℝ) : ℂ[X] := (X + 1) * (X + C (β : ℂ))

/-! ### The symmetric equilibrium -/

/-- The constant state `(p, …, p)`, `p ≥ 0`, is an equilibrium of (EL) iff `α = p (1 + pⁿ)`. -/
theorem vectorField_const_eq_zero_iff {n : ℕ} {α β p : ℝ} (hp : 0 ≤ p) :
    vectorField n α β (fun _ => p) = 0 ↔ α = eqRate n p := by
  have h := (one_add_pow_pos hp n).ne'
  constructor
  · intro hf
    have h0 := congrFun hf 0
    simp only [vectorField, Matrix.cons_val_zero, Pi.zero_apply, sub_eq_zero] at h0
    rw [div_eq_iff h] at h0
    rw [eqRate, h0]
  · rintro rfl
    have he : eqRate n p / (1 + p ^ n) = p := by
      rw [eqRate, mul_div_assoc, div_self h, mul_one]
    funext k
    fin_cases k <;> simp [vectorField, he]

/-- For `n ≥ 1`, `α > 0`, `β ≠ 0` and an equilibrium level `p ≥ 0` with `α = p (1 + pⁿ)`, the
symmetric equilibrium `(p, …, p)` is the only equilibrium of (EL) in the closed nonnegative
orthant. Without `p ≥ 0` this fails: for `n = 1`, `p = -2`, `α = 2`, the nonnegative state
`(1, …, 1)` is also an equilibrium. -/
theorem eq_const_of_vectorField_eq_zero {n : ℕ} (hn : 0 < n) {α β p : ℝ} (hα : 0 < α)
    (hβ : β ≠ 0) (hp : 0 ≤ p) (hpα : eqRate n p = α) {x : Fin 6 → ℝ} (hx : ∀ j, 0 ≤ x j)
    (h : vectorField n α β x = 0) : x = fun _ => p := by
  have h0 : α / (1 + x 5 ^ n) - x 0 = 0 := congrFun h 0
  have h1 : α / (1 + x 3 ^ n) - x 1 = 0 := congrFun h 1
  have h2 : α / (1 + x 4 ^ n) - x 2 = 0 := congrFun h 2
  have h3 : -β * (x 3 - x 0) = 0 := congrFun h 3
  have h4 : -β * (x 4 - x 1) = 0 := congrFun h 4
  have h5 : -β * (x 5 - x 2) = 0 := congrFun h 5
  have e3 : x 3 = x 0 := by
    have := mul_eq_zero.1 h3; rcases this with h | h
    · exact absurd (neg_eq_zero.1 h) hβ
    · linarith
  have e4 : x 4 = x 1 := by
    have := mul_eq_zero.1 h4; rcases this with h | h
    · exact absurd (neg_eq_zero.1 h) hβ
    · linarith
  have e5 : x 5 = x 2 := by
    have := mul_eq_zero.1 h5; rcases this with h | h
    · exact absurd (neg_eq_zero.1 h) hβ
    · linarith
  set y : Fin 3 → ℝ := ![x 0, x 1, x 2] with hy
  have hy0 : Repressilator.vectorField n α y = 0 := by
    funext i
    fin_cases i
    · have e : Repressilator.vectorField n α y 0 = α / (1 + x 2 ^ n) - x 0 := rfl
      have : Repressilator.vectorField n α y 0 = 0 := by rw [e, ← e5]; linarith
      exact this
    · have e : Repressilator.vectorField n α y 1 = α / (1 + x 0 ^ n) - x 1 := rfl
      have : Repressilator.vectorField n α y 1 = 0 := by rw [e, ← e3]; linarith
      exact this
    · have e : Repressilator.vectorField n α y 2 = α / (1 + x 1 ^ n) - x 2 := rfl
      have : Repressilator.vectorField n α y 2 = 0 := by rw [e, ← e4]; linarith
      exact this
  have hyc := Repressilator.eq_const_of_vectorField_eq_zero hn hα hp hpα
    (fun j => by fin_cases j <;> simp [hy, hx]) hy0
  have y0 : x 0 = p := congrFun hyc 0
  have y1 : x 1 = p := congrFun hyc 1
  have y2 : x 2 = p := congrFun hyc 2
  funext k
  fin_cases k
  · exact y0
  · exact y1
  · exact y2
  · exact e3.trans y0
  · exact e4.trans y1
  · exact e5.trans y2

/-! ### The linearization -/

/-- The continuous linear map of `jacobian a β`. -/
noncomputable def jacobianCLM (a β : ℝ) : (Fin 6 → ℝ) →L[ℝ] Fin 6 → ℝ :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' (jacobian a β))

/-- Derivative of an mRNA row `x ↦ p (1 + pⁿ) / (1 + x jⁿ) - x i` at the symmetric state, for
`p ≥ 0`. -/
lemma hasFDerivAt_mRow (n : ℕ) {p : ℝ} (hp : 0 ≤ p) (i j : Fin 6) :
    HasFDerivAt (fun x : Fin 6 → ℝ => eqRate n p / (1 + x j ^ n) - x i)
      ((-gain n p) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 6 => ℝ) j -
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 6 => ℝ) i) (fun _ => p) := by
  have h1 := HasDerivAt.comp_hasFDerivAt (fun _ : Fin 6 => p) (hasDerivAt_repression n hp)
    (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 6 => ℝ) j (fun _ : Fin 6 => p))
  exact HasFDerivAt.sub h1 (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 6 => ℝ) i _)

/-- Derivative of a protein row `x ↦ -β (x j - x i)`. -/
lemma hasFDerivAt_pRow (β : ℝ) (i j : Fin 6) (x₀ : Fin 6 → ℝ) :
    HasFDerivAt (fun x : Fin 6 → ℝ => -β * (x j - x i))
      ((-β) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 6 => ℝ) j -
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 6 => ℝ) i)) x₀ :=
  ((hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 6 => ℝ) j x₀).sub
    (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 6 => ℝ) i x₀)).const_mul (-β)

/-- **Linearization at the symmetric equilibrium.** With `p ≥ 0` and `α = p (1 + pⁿ)`, the
derivative of the field at `(p, …, p)` is `jacobian (gain n p) β`. -/
theorem hasFDerivAt_vectorField (n : ℕ) (β : ℝ) {p : ℝ} (hp : 0 ≤ p) :
    HasFDerivAt (vectorField n (eqRate n p) β) (jacobianCLM (gain n p) β) (fun _ => p) := by
  rw [hasFDerivAt_pi']
  intro k
  fin_cases k
  · refine (hasFDerivAt_mRow n hp 0 5).congr_fderiv ?_
    ext v
    simp [jacobianCLM, jacobian, Matrix.toLin'_apply, dotProduct, Fin.sum_univ_succ]
    ring
  · refine (hasFDerivAt_mRow n hp 1 3).congr_fderiv ?_
    ext v
    simp [jacobianCLM, jacobian, Matrix.toLin'_apply, dotProduct, Fin.sum_univ_succ]
    ring
  · refine (hasFDerivAt_mRow n hp 2 4).congr_fderiv ?_
    ext v
    simp [jacobianCLM, jacobian, Matrix.toLin'_apply, dotProduct, Fin.sum_univ_succ]
    ring
  · refine (hasFDerivAt_pRow β 0 3 _).congr_fderiv ?_
    ext v
    simp [jacobianCLM, jacobian, Matrix.toLin'_apply, dotProduct, Fin.sum_univ_succ]
    ring
  · refine (hasFDerivAt_pRow β 1 4 _).congr_fderiv ?_
    ext v
    simp [jacobianCLM, jacobian, Matrix.toLin'_apply, dotProduct, Fin.sum_univ_succ]
    ring
  · refine (hasFDerivAt_pRow β 2 5 _).congr_fderiv ?_
    ext v
    simp [jacobianCLM, jacobian, Matrix.toLin'_apply, dotProduct, Fin.sum_univ_succ]
    ring

/-- The matrix of the linearization at the symmetric equilibrium `(p, …, p)`, `p ≥ 0`, with
`α = p (1 + pⁿ)` is `jacobian (gain n p) β`. -/
theorem toMatrix'_fderiv_vectorField (n : ℕ) (β : ℝ) {p : ℝ} (hp : 0 ≤ p) :
    LinearMap.toMatrix' (fderiv ℝ (vectorField n (eqRate n p) β) (fun _ => p) :
      (Fin 6 → ℝ) →ₗ[ℝ] Fin 6 → ℝ) = jacobian (gain n p) β := by
  rw [(hasFDerivAt_vectorField n β hp).fderiv, jacobianCLM, LinearMap.coe_toContinuousLinearMap,
    LinearMap.toMatrix'_toLin']

lemma linCharpoly_vectorField (n : ℕ) (β : ℝ) {p : ℝ} (hp : 0 ≤ p) :
    linCharpoly (vectorField n (eqRate n p) β) (fun _ => p) =
      (jacobian (gain n p) β).charpoly.map Complex.ofRealHom := by
  rw [linCharpoly, toMatrix'_fderiv_vectorField n β hp]

/-! ### The characteristic equation -/

private lemma finSumFinEquiv_symm_0 : (finSumFinEquiv.symm (0 : Fin 6) : Fin 3 ⊕ Fin 3) =
    Sum.inl 0 := rfl
private lemma finSumFinEquiv_symm_1 : (finSumFinEquiv.symm (1 : Fin 6) : Fin 3 ⊕ Fin 3) =
    Sum.inl 1 := rfl
private lemma finSumFinEquiv_symm_2 : (finSumFinEquiv.symm (2 : Fin 6) : Fin 3 ⊕ Fin 3) =
    Sum.inl 2 := rfl
private lemma finSumFinEquiv_symm_3 : (finSumFinEquiv.symm (3 : Fin 6) : Fin 3 ⊕ Fin 3) =
    Sum.inr 0 := rfl
private lemma finSumFinEquiv_symm_4 : (finSumFinEquiv.symm (4 : Fin 6) : Fin 3 ⊕ Fin 3) =
    Sum.inr 1 := rfl
private lemma finSumFinEquiv_symm_5 : (finSumFinEquiv.symm (5 : Fin 6) : Fin 3 ⊕ Fin 3) =
    Sum.inr 2 := rfl

/-- The Jacobian is the block matrix `[[-I, -a P], [β I, -β I]]`, reindexed to `Fin 6`. -/
theorem jacobian_eq_reindex (a β : ℝ) :
    jacobian a β = Matrix.reindex finSumFinEquiv finSumFinEquiv (jacobianBlocks a β) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp (config := { decide := true }) [jacobian, jacobianBlocks, shift, Matrix.reindex_apply,
      Matrix.submatrix_apply, finSumFinEquiv_symm_0, finSumFinEquiv_symm_1,
      finSumFinEquiv_symm_2, finSumFinEquiv_symm_3, finSumFinEquiv_symm_4,
      finSumFinEquiv_symm_5]

/-- `det [[A, B], [C, D]] = det (A D - B C)` when `C` and `D` commute and `det D ≠ 0`. -/
lemma det_fromBlocks_of_commute {R : Type*} [CommRing R] [IsDomain R]
    (A B C D : Matrix (Fin 3) (Fin 3) R) (hCD : C * D = D * C) (hD : D.det ≠ 0) :
    (Matrix.fromBlocks A B C D).det = (A * D - B * C).det := by
  have hmul : Matrix.fromBlocks A B C D * Matrix.fromBlocks D 0 (-C) 1 =
      Matrix.fromBlocks (A * D - B * C) B 0 D := by
    rw [Matrix.fromBlocks_multiply]
    simp [hCD, sub_eq_add_neg]
  have h := congrArg Matrix.det hmul
  rw [Matrix.det_mul, Matrix.det_fromBlocks_zero₁₂, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, mul_one] at h
  exact mul_right_cancel₀ hD h

/-- **Characteristic equation.** `det (λ I - J) = ((λ + 1)(λ + β))³ + (a β)³`. -/
theorem charpoly_jacobian (a β : ℝ) :
    (jacobian a β).charpoly = ((X + 1) * (X + C β)) ^ 3 + C ((a * β) ^ 3) := by
  rw [jacobian_eq_reindex, Matrix.charpoly_reindex, Matrix.charpoly, jacobianBlocks,
    Matrix.charmatrix_fromBlocks]
  have hA : Matrix.charmatrix (-1 : Matrix (Fin 3) (Fin 3) ℝ) = (X + 1 : ℝ[X]) • 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hB : -(-a • shift).map C = C a • shift.map (C : ℝ →+* ℝ[X]) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp (config := { decide := true }) [shift]
  have hC : -((β • (1 : Matrix (Fin 3) (Fin 3) ℝ)).map C) = (-C β : ℝ[X]) • 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hD : Matrix.charmatrix (-β • (1 : Matrix (Fin 3) (Fin 3) ℝ)) = (X + C β : ℝ[X]) • 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [hA, hB, hC, hD, det_fromBlocks_of_commute]
  · rw [Matrix.det_fin_three]
    simp (config := { decide := true }) [shift]
    ring
  · simp [smul_smul, mul_comm]
  · rw [Matrix.det_smul, Matrix.det_one, mul_one]
    exact pow_ne_zero _ (X_add_C_ne_zero β)

lemma rootSix_add_conj : rootSix + rootSixConj = 1 := by
  apply Complex.ext <;> norm_num [rootSix, rootSixConj]

lemma rootSix_mul_conj : rootSix * rootSixConj = 1 := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  apply Complex.ext
  · simp [rootSix, rootSixConj]; nlinarith
  · simp [rootSix, rootSixConj]; ring

lemma rootSix_re : rootSix.re = 1 / 2 := rfl
lemma rootSix_im : rootSix.im = √3 / 2 := rfl
lemma rootSixConj_re : rootSixConj.re = 1 / 2 := rfl
lemma rootSixConj_im : rootSixConj.im = -(√3 / 2) := rfl

/-- Over `ℂ` the characteristic polynomial factors as `(Q + a β) (Q - a β c) (Q - a β c̄)`. -/
theorem charpoly_map_jacobian (a β : ℝ) :
    (jacobian a β).charpoly.map Complex.ofRealHom =
      (quad β + C ((a * β : ℝ) : ℂ)) * (quad β - C ((a * β : ℝ) * rootSix)) *
        (quad β - C ((a * β : ℝ) * rootSixConj)) := by
  rw [charpoly_jacobian]
  have h1 : C rootSix + C rootSixConj = (1 : ℂ[X]) := by rw [← C_add, rootSix_add_conj, C_1]
  have h2 : C rootSix * C rootSixConj = (1 : ℂ[X]) := by rw [← C_mul, rootSix_mul_conj, C_1]
  simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_X,
    Polynomial.map_one, Polynomial.map_C, Complex.ofRealHom_eq_coe, quad, C_mul]
  set y : ℂ[X] := (X + 1) * (X + C (β : ℂ))
  set b : ℂ[X] := C ((a * β : ℝ) : ℂ)
  have hb : C (((a * β) ^ 3 : ℝ) : ℂ) = b ^ 3 := by
    simp only [b, ← C_pow, Complex.ofReal_pow]
  rw [hb]
  linear_combination (y + b) * b * y * h1 - (y + b) * b ^ 2 * h2

lemma eval_quad (β : ℝ) (z : ℂ) : (quad β).eval z = (z + 1) * (z + β) := by
  simp [quad]

/-- **Eigenvalues.** `z` is an eigenvalue iff `Q(z) = -a β`, `Q(z) = a β c` or `Q(z) = a β c̄`. -/
theorem isRoot_iff (a β : ℝ) (z : ℂ) :
    ((jacobian a β).charpoly.map Complex.ofRealHom).IsRoot z ↔
      (z + 1) * (z + β) = -((a * β : ℝ) : ℂ) ∨ (z + 1) * (z + β) = (a * β : ℝ) * rootSix ∨
        (z + 1) * (z + β) = (a * β : ℝ) * rootSixConj := by
  rw [charpoly_map_jacobian]
  simp only [IsRoot, eval_mul, eval_add, eval_sub, eval_C, eval_quad, mul_eq_zero,
    sub_eq_zero, or_assoc, add_eq_zero_iff_eq_neg]

lemma re_quad (β : ℝ) (z : ℂ) : ((z + 1) * (z + β)).re = (z.re + 1) * (z.re + β) - z.im ^ 2 := by
  simp; ring

lemma im_quad (β : ℝ) (z : ℂ) : ((z + 1) * (z + β)).im = z.im * (2 * z.re + 1 + β) := by
  simp; ring

/-! ### The stability boundary -/

/-- A root of `Q(z) = d` with `d_r b² > d_i²` (`b = 1 + β > 0`) has negative real part. -/
private lemma re_neg_of_quad_eq {β dr di : ℝ} (hb : 0 < 1 + β) (hdr : 0 < dr)
    (hd : di ^ 2 < dr * (1 + β) ^ 2) {z : ℂ} (hz : (z + 1) * (z + β) = ⟨β - dr, -di⟩) :
    z.re < 0 := by
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  rw [re_quad] at hre
  rw [im_quad] at him
  simp only at hre him
  by_contra hx
  have hx := not_lt.1 hx
  set x := z.re
  set y := z.im
  have hs : 1 + β ≤ 2 * x + 1 + β := by linarith
  have hs0 : 0 < 2 * x + 1 + β := by linarith
  -- `x² + b x + d_r = y²` and `y (2x + b) = -d_i`
  have e1 : x ^ 2 + (1 + β) * x + dr = y ^ 2 := by nlinarith
  have e2 : (y * (2 * x + 1 + β)) ^ 2 = di ^ 2 := by rw [him]; ring
  have : dr * (2 * x + 1 + β) ^ 2 ≤ y ^ 2 * (2 * x + 1 + β) ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    nlinarith
  have h2 : dr * (1 + β) ^ 2 ≤ dr * (2 * x + 1 + β) ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ hdr.le
    nlinarith
  nlinarith

/-- **Linear stability inside the Elowitz–Leibler boundary.** For `a ≥ 0`, `β > 0` and
`3 a² β < (4 - 2 a) (1 + β)²`, every eigenvalue has negative real part. -/
theorem re_neg_of_isRoot {a β : ℝ} (ha : 0 ≤ a) (hβ : 0 < β)
    (h : 3 * a ^ 2 * β < (4 - 2 * a) * (1 + β) ^ 2) {z : ℂ}
    (hz : ((jacobian a β).charpoly.map Complex.ofRealHom).IsRoot z) : z.re < 0 := by
  have hb : 0 < 1 + β := by linarith
  have h2a : 0 < 2 - a := by nlinarith [sq_nonneg a, sq_nonneg (1 + β)]
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hdi : (√3 / 2 * a * β) ^ 2 = 3 / 4 * a ^ 2 * β ^ 2 := by
    rw [mul_pow, mul_pow, div_pow, Real.sq_sqrt (by norm_num)]; ring
  have hβh := mul_lt_mul_of_pos_left h hβ
  rcases (isRoot_iff a β z).1 hz with hq | hq | hq
  · refine re_neg_of_quad_eq (dr := β + a * β) (di := 0) hb (by positivity)
      (by simpa using mul_pos (by positivity : (0 : ℝ) < β + a * β) (pow_pos hb 2)) ?_
    rw [hq]; apply Complex.ext <;> simp
  · refine re_neg_of_quad_eq (dr := β - a * β / 2) (di := -(√3 / 2 * a * β)) hb
      (by nlinarith) ?_ ?_
    · rw [neg_sq, hdi]; nlinarith
    · rw [hq]; apply Complex.ext <;> simp [rootSix] <;> ring
  · refine re_neg_of_quad_eq (dr := β - a * β / 2) (di := √3 / 2 * a * β) hb
      (by nlinarith) ?_ ?_
    · rw [hdi]; nlinarith
    · rw [hq]; apply Complex.ext <;> simp [rootSixConj] <;> ring

/-- An explicit root with positive real part of `z² + b z + d = 0` when `d_i² > b² d_r`,
`b > 0`: with `E = b² / 4 - d` and `u = √((|E| + E_r) / 2)`, `z = u - b/2 + i E_i / (2u)`. -/
private lemma exists_re_pos_of_quad {β dr di : ℝ} (hb : 0 < 1 + β)
    (hd : dr * (1 + β) ^ 2 < di ^ 2) :
    ∃ z : ℂ, (z + 1) * (z + β) = ⟨β - dr, -di⟩ ∧ 0 < z.re := by
  set Er := (1 + β) ^ 2 / 4 - dr with hEr
  set nE := √(Er ^ 2 + di ^ 2) with hnE
  have hnE2 : nE ^ 2 = Er ^ 2 + di ^ 2 := Real.sq_sqrt (by positivity)
  have hnE0 : 0 ≤ nE := Real.sqrt_nonneg _
  have hEr' : |Er| ≤ nE := Real.abs_le_sqrt (by nlinarith [sq_nonneg di])
  -- `nE > b²/4 + d_r`, `b = 1 + β`
  have hkey : (1 + β) ^ 2 / 4 + dr < nE := by
    rcases le_or_gt ((1 + β) ^ 2 / 4 + dr) 0 with h | h
    · have : 0 < (1 + β) ^ 2 := by positivity
      linarith [le_abs_self Er]
    · have : ((1 + β) ^ 2 / 4 + dr) ^ 2 < nE ^ 2 := by rw [hnE2, hEr]; nlinarith
      nlinarith
  set u := √((nE + Er) / 2) with hu
  have hu2 : u ^ 2 = (nE + Er) / 2 := Real.sq_sqrt (by linarith [neg_abs_le Er])
  have hub : (1 + β) / 2 < u := by
    rw [hu]
    apply Real.lt_sqrt_of_sq_lt
    linarith
  have hu0 : 0 < u := by linarith
  refine ⟨⟨u - (1 + β) / 2, -di / (2 * u)⟩, ?_, by simp only; linarith⟩
  have hsum : 0 < nE + Er := by nlinarith
  have hy2 : (-di / (2 * u)) ^ 2 = (nE - Er) / 2 := by
    rw [div_pow, neg_sq, mul_pow, hu2]
    have : di ^ 2 = (nE - Er) * (nE + Er) := by nlinarith
    rw [this]; field_simp
  apply Complex.ext
  · rw [re_quad]
    simp only
    rw [hy2]
    linear_combination hu2 + hEr
  · rw [im_quad]
    simp only
    field_simp
    ring

/-- **Linear instability outside the Elowitz–Leibler boundary.** For `β > 0` and
`3 a² β > (4 - 2 a) (1 + β)²`, some eigenvalue has positive real part. -/
theorem exists_re_pos_of_isRoot {a β : ℝ} (hβ : 0 < β)
    (h : (4 - 2 * a) * (1 + β) ^ 2 < 3 * a ^ 2 * β) :
    ∃ z, ((jacobian a β).charpoly.map Complex.ofRealHom).IsRoot z ∧ 0 < z.re := by
  have hb : 0 < 1 + β := by linarith
  have hdi : (-(√3 / 2 * a * β)) ^ 2 = 3 / 4 * a ^ 2 * β ^ 2 := by
    rw [neg_sq, mul_pow, mul_pow, div_pow, Real.sq_sqrt (by norm_num)]; ring
  have hβh := mul_lt_mul_of_pos_left h hβ
  obtain ⟨z, hz, hre⟩ := exists_re_pos_of_quad (dr := β - a * β / 2) (di := -(√3 / 2 * a * β))
    hb (by rw [hdi]; nlinarith)
  refine ⟨z, (isRoot_iff a β z).2 (Or.inr (Or.inl ?_)), hre⟩
  rw [hz]; apply Complex.ext <;> simp [rootSix] <;> ring

/-! ### The Hopf condition -/

lemma hopfFreq_pos {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) : 0 < hopfFreq a β := by
  unfold hopfFreq; have : (0 : ℝ) < √3 := Real.sqrt_pos.2 (by norm_num); positivity

lemma one_add_mul_hopfFreq {a β : ℝ} (hβ : 0 < β) :
    (1 + β) * hopfFreq a β = √3 / 2 * a * β := by
  unfold hopfFreq; field_simp

lemma hopfFreq_sq {a β : ℝ} (hβ : 0 < β) (hH : IsHopf a β) :
    hopfFreq a β ^ 2 = β - a * β / 2 := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  unfold IsHopf at hH
  have hb : 0 < 1 + β := by linarith
  have e : hopfFreq a β ^ 2 = 3 * a ^ 2 * β ^ 2 / (4 * (1 + β) ^ 2) := by
    unfold hopfFreq; rw [div_pow, mul_pow, mul_pow, mul_pow, h3]; ring
  rw [e, div_eq_iff (by positivity)]
  linear_combination β * hH

/-- At a Hopf point `Q(iω) = a β c`. -/
lemma quad_hopf {a β : ℝ} (hβ : 0 < β) (hH : IsHopf a β) :
    ((hopfFreq a β : ℂ) * Complex.I + 1) * ((hopfFreq a β : ℂ) * Complex.I + β) =
      (a * β : ℝ) * rootSix := by
  have hsq := hopfFreq_sq hβ hH
  have hm := one_add_mul_hopfFreq (a := a) hβ
  apply Complex.ext
  · rw [re_quad]; simp [rootSix]; nlinarith
  · rw [im_quad]; simp [rootSix]; nlinarith

/-- At a Hopf point, `Q - a β c = (X - iω) (X - r₂)` with `r₂ = -(1 + β) - iω`. -/
lemma quad_sub_hopf {a β : ℝ} (hβ : 0 < β) (hH : IsHopf a β) :
    quad β - C ((a * β : ℝ) * rootSix) =
      (X - C ((hopfFreq a β : ℂ) * Complex.I)) *
        (X - C (-(1 + β : ℂ) - (hopfFreq a β : ℂ) * Complex.I)) := by
  set r := (hopfFreq a β : ℂ) * Complex.I
  have h1 : C r * C (-(1 + β : ℂ) - r) = C (β : ℂ) - C ((a * β : ℝ) * rootSix) := by
    rw [← C_mul, ← C_sub]
    congr 1
    have := quad_hopf hβ hH
    linear_combination -this
  have h2 : C (-(1 + β : ℂ) - r) = -1 - C (β : ℂ) - C r := by
    simp only [C_sub, C_neg, C_add, C_1]; ring
  rw [quad]
  linear_combination X * h2 - h1

/-- **No other eigenvalue on the imaginary axis.** For `a ≥ 0`, `β > 0`, every eigenvalue with
zero real part is `iω` or `-iω`, `ω = √3 a β / (2 (1 + β))`. -/
theorem eq_of_isRoot_of_re_eq_zero {a β : ℝ} (ha : 0 ≤ a) (hβ : 0 < β) {z : ℂ}
    (hz : ((jacobian a β).charpoly.map Complex.ofRealHom).IsRoot z) (hre : z.re = 0) :
    z = (hopfFreq a β : ℂ) * Complex.I ∨ z = -((hopfFreq a β : ℂ) * Complex.I) := by
  have hb : (0 : ℝ) < 1 + β := by linarith
  have hm := one_add_mul_hopfFreq (a := a) hβ
  rcases (isRoot_iff a β z).1 hz with hq | hq | hq
  · exfalso
    have hr : (0 + 1) * (0 + β) - z.im ^ 2 = -(a * β) := by
      have := congrArg Complex.re hq
      rwa [re_quad, hre, Complex.neg_re, Complex.ofReal_re] at this
    have hi : z.im * (2 * 0 + 1 + β) = 0 := by
      have := congrArg Complex.im hq
      rwa [im_quad, hre, Complex.neg_im, Complex.ofReal_im, neg_zero] at this
    have hy : z.im = 0 := by
      have h0 : z.im * (1 + β) = 0 := by linarith
      rcases mul_eq_zero.1 h0 with h | h
      · exact h
      · linarith
    rw [hy] at hr
    nlinarith [mul_nonneg ha hβ.le]
  · left
    have hi : z.im * (2 * 0 + 1 + β) = a * β * (√3 / 2) := by
      have := congrArg Complex.im hq
      rwa [im_quad, hre, Complex.im_ofReal_mul, rootSix_im] at this
    apply Complex.ext
    · simp [hre]
    · rw [Complex.mul_I_im, Complex.ofReal_re]
      exact mul_right_cancel₀ hb.ne' (by linarith)
  · right
    have hi : z.im * (2 * 0 + 1 + β) = a * β * -(√3 / 2) := by
      have := congrArg Complex.im hq
      rwa [im_quad, hre, Complex.im_ofReal_mul, rootSixConj_im] at this
    apply Complex.ext
    · simp [hre]
    · rw [Complex.neg_im, Complex.mul_I_im, Complex.ofReal_re]
      exact mul_right_cancel₀ hb.ne' (by linarith)

/-- **Simplicity.** At a Hopf point with `a > 0`, `iω` is a simple eigenvalue. -/
theorem rootMultiplicity_hopf {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) (hH : IsHopf a β) :
    ((jacobian a β).charpoly.map Complex.ofRealHom).rootMultiplicity
      ((hopfFreq a β : ℂ) * Complex.I) = 1 := by
  classical
  have hne : (jacobian a β).charpoly.map Complex.ofRealHom ≠ 0 :=
    ((Matrix.charpoly_monic _).map _).ne_zero
  have hq := quad_hopf hβ hH
  have hω := hopfFreq_pos ha hβ
  have hab : 0 < a * β := mul_pos ha hβ
  rw [charpoly_map_jacobian, quad_sub_hopf hβ hH] at hne ⊢
  rw [rootMultiplicity_mul hne, rootMultiplicity_mul (left_ne_zero_of_mul hne),
    rootMultiplicity_mul (right_ne_zero_of_mul (left_ne_zero_of_mul hne)),
    rootMultiplicity_X_sub_C_self, rootMultiplicity_X_sub_C,
    rootMultiplicity_eq_zero, rootMultiplicity_eq_zero]
  · have : (hopfFreq a β : ℂ) * Complex.I ≠ -(1 + β : ℂ) - (hopfFreq a β : ℂ) * Complex.I := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    simp only [this, ite_false, add_zero, zero_add]
  · simp only [IsRoot, eval_sub, eval_C, eval_quad, hq]
    intro h
    have him : ((a * β : ℝ) * rootSix - (a * β : ℝ) * rootSixConj : ℂ).im = a * β * √3 := by
      simp only [Complex.sub_im, Complex.im_ofReal_mul, rootSix_im, rootSixConj_im]; ring
    rw [h, Complex.zero_im] at him
    have : (0 : ℝ) < √3 := Real.sqrt_pos.2 (by norm_num)
    nlinarith [mul_pos hab this]
  · simp only [IsRoot, eval_add, eval_C, eval_quad, hq]
    intro h
    have := congrArg Complex.re h
    simp [rootSix] at this
    nlinarith

/-! ### The eigenvalue curve -/

/-- `D(μ) = (1 - β)² + 4 a(μ) β c`, the discriminant of `Q(λ) = a(μ) β c`. -/
noncomputable def disc (n : ℕ) (β μ : ℝ) : ℂ :=
  (((1 - β) ^ 2 : ℝ) : ℂ) + (gain n μ : ℂ) * (4 * β * rootSix)

/-- The eigenvalue curve `λ(μ) = (-(1 + β) + √D(μ)) / 2` (principal square root), a root of
`Q(λ) = a(μ) β c` for every `μ`. -/
noncomputable def hopfEigenvalue (n : ℕ) (β μ : ℝ) : ℂ :=
  (-(1 + β : ℂ) + disc n β μ ^ (2⁻¹ : ℂ)) / 2

lemma cpow_inv_two_sq (z : ℂ) : (z ^ (2⁻¹ : ℂ)) ^ 2 = z := by
  simp

/-- The eigenvalue curve solves `Q(λ(μ)) = a(μ) β c`. -/
theorem quad_hopfEigenvalue (n : ℕ) (β μ : ℝ) :
    (hopfEigenvalue n β μ + 1) * (hopfEigenvalue n β μ + β) = (gain n μ * β : ℝ) * rootSix := by
  have hs := cpow_inv_two_sq (disc n β μ)
  unfold hopfEigenvalue
  unfold disc at hs ⊢
  push_cast at hs ⊢
  linear_combination (1 / 4 : ℂ) * hs

/-- `λ(μ)` is an eigenvalue of the linearization at level `μ`. -/
theorem isRoot_hopfEigenvalue (n : ℕ) (β μ : ℝ) :
    ((jacobian (gain n μ) β).charpoly.map Complex.ofRealHom).IsRoot (hopfEigenvalue n β μ) :=
  (isRoot_iff _ _ _).2 (Or.inr (Or.inl (quad_hopfEigenvalue n β μ)))

/-- `w = (1 + β) + 2 i ω`, the square root of the discriminant at a Hopf point. -/
noncomputable def hopfRoot (a β : ℝ) : ℂ := ⟨1 + β, 2 * hopfFreq a β⟩

lemma hopfRoot_sq {a β : ℝ} (hβ : 0 < β) (hH : IsHopf a β) :
    hopfRoot a β ^ 2 = (((1 - β) ^ 2 : ℝ) : ℂ) + (a : ℂ) * (4 * β * rootSix) := by
  have hsq := hopfFreq_sq hβ hH
  have hm := one_add_mul_hopfFreq (a := a) hβ
  apply Complex.ext
  · simp [hopfRoot, pow_two, rootSix]; nlinarith
  · simp [hopfRoot, pow_two, rootSix]; nlinarith

/-- **The eigenvalue curve passes through `iω` at a Hopf level.** -/
theorem hopfEigenvalue_hopf {n : ℕ} {β μ : ℝ} (hβ : 0 < β) (hH : IsHopf (gain n μ) β) :
    hopfEigenvalue n β μ = (hopfFreq (gain n μ) β : ℂ) * Complex.I := by
  have hw : (hopfRoot (gain n μ) β ^ 2) ^ (2⁻¹ : ℂ) = hopfRoot (gain n μ) β := by
    have harg : |(hopfRoot (gain n μ) β).arg| < π / 2 :=
      Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl (by simp [hopfRoot]; linarith))
    have := Complex.pow_cpow_ofNat_inv (x := hopfRoot (gain n μ) β) (n := 2)
      (by have := neg_abs_le (hopfRoot (gain n μ) β).arg; norm_num; linarith)
      (by have := le_abs_self (hopfRoot (gain n μ) β).arg; norm_num; linarith)
    simpa using this
  unfold hopfEigenvalue
  rw [show disc n β μ = hopfRoot (gain n μ) β ^ 2 from (hopfRoot_sq hβ hH).symm, hw]
  apply Complex.ext <;> simp [hopfRoot]

/-- The derivative of the loop gain, `a'(μ) = n² μⁿ⁻¹ / (1 + μⁿ)²`, for `μ ≥ 0` (T196). -/
noncomputable def gainDeriv (n : ℕ) (μ : ℝ) : ℝ := n ^ 2 * μ ^ (n - 1) / (1 + μ ^ n) ^ 2

/-- The crossing speed `λ'(μ) = a'(μ) β c / w` at a Hopf level. -/
noncomputable def hopfSpeed (n : ℕ) (β μ : ℝ) : ℂ :=
  (gainDeriv n μ * β : ℝ) * rootSix / hopfRoot (gain n μ) β

lemma hopfRoot_ne_zero {a β : ℝ} (hβ : 0 < β) : hopfRoot a β ≠ 0 := by
  intro h; have := congrArg Complex.re h; simp [hopfRoot] at this; linarith

/-- **Transversality.** At a Hopf level `μ > 0` the eigenvalue curve has derivative
`a'(μ) β c / w`, `w = (1 + β) + 2iω`. -/
theorem hasDerivAt_hopfEigenvalue {n : ℕ} {β μ : ℝ} (hβ : 0 < β) (hμ : 0 < μ)
    (hH : IsHopf (gain n μ) β) :
    HasDerivAt (hopfEigenvalue n β) (hopfSpeed n β μ) μ := by
  have hg : HasDerivAt (fun x => (gain n x : ℂ)) (gainDeriv n μ : ℂ) μ :=
    (hasDerivAt_gain n hμ.le).ofReal_comp
  have hD : HasDerivAt (disc n β) ((gainDeriv n μ : ℂ) * (4 * β * rootSix)) μ :=
    (hg.mul_const _).const_add _
  have hslit : disc n β μ ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]; right
    have ha : 0 < gain n μ := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · exfalso; unfold IsHopf at hH; simp [gain] at hH; nlinarith
      · unfold gain; positivity
    have : (0 : ℝ) < √3 := Real.sqrt_pos.2 (by norm_num)
    have him : (disc n β μ).im = gain n μ * (4 * β * (√3 / 2)) := by
      rw [disc, Complex.add_im, Complex.ofReal_im, zero_add, Complex.im_ofReal_mul]
      congr 1
      have e : (4 * (β : ℂ) * rootSix) = ((4 * β : ℝ) : ℂ) * rootSix := by push_cast; ring
      rw [e, Complex.im_ofReal_mul, rootSix_im]
    rw [him]; positivity
  have hcp := ((Complex.hasStrictDerivAt_cpow_const (c := (2⁻¹ : ℂ)) hslit).hasDerivAt.comp μ
    hD)
  have hl : HasDerivAt (hopfEigenvalue n β) ((2⁻¹ * disc n β μ ^ ((2⁻¹ : ℂ) - 1) *
      ((gainDeriv n μ : ℂ) * (4 * β * rootSix))) / 2) μ :=
    (hcp.const_add (-(1 + β : ℂ))).div_const 2
  set L := (2⁻¹ * disc n β μ ^ ((2⁻¹ : ℂ) - 1) *
      ((gainDeriv n μ : ℂ) * (4 * β * rootSix))) / 2
  -- implicit differentiation of `Q(λ(μ)) - a(μ) β c ≡ 0`
  have hz : HasDerivAt (fun x => (hopfEigenvalue n β x + 1) * (hopfEigenvalue n β x + β) -
      (gain n x : ℂ) * (β * rootSix))
      (L * (hopfEigenvalue n β μ + β) + (hopfEigenvalue n β μ + 1) * L -
        (gainDeriv n μ : ℂ) * (β * rootSix)) μ :=
    ((hl.add_const 1).mul (hl.add_const (β : ℂ))).sub (hg.mul_const _)
  have hzero : (fun x => (hopfEigenvalue n β x + 1) * (hopfEigenvalue n β x + β) -
      (gain n x : ℂ) * (β * rootSix)) = fun _ => 0 := by
    funext x; rw [quad_hopfEigenvalue]; push_cast; ring
  rw [hzero] at hz
  have hu := hz.unique (hasDerivAt_const μ (0 : ℂ))
  rw [hopfEigenvalue_hopf hβ hH] at hu
  have hLw : L * hopfRoot (gain n μ) β = (gainDeriv n μ * β : ℝ) * rootSix := by
    have e : hopfRoot (gain n μ) β = 2 * ((hopfFreq (gain n μ) β : ℂ) * Complex.I) + 1 + β := by
      apply Complex.ext <;> simp [hopfRoot]
    rw [e]; push_cast; linear_combination hu
  have hL : L = hopfSpeed n β μ := by
    rw [hopfSpeed, eq_div_iff (hopfRoot_ne_zero hβ), hLw]
  rwa [hL] at hl

/-- **Nonzero crossing speed.** For `n ≥ 1`, `μ > 0`, `β > 0`, `a(μ) > 0`, the real part of the
crossing speed is positive. -/
theorem re_hopfSpeed_pos {n : ℕ} (hn : 0 < n) {β μ : ℝ} (hβ : 0 < β) (hμ : 0 < μ) :
    0 < (hopfSpeed n β μ).re := by
  have hga : 0 < gain n μ := by unfold gain; positivity
  have hω := hopfFreq_pos hga hβ
  have hd : 0 < gainDeriv n μ := by
    unfold gainDeriv; have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have hns : 0 < Complex.normSq (hopfRoot (gain n μ) β) :=
    Complex.normSq_pos.2 (hopfRoot_ne_zero hβ)
  have : (0 : ℝ) < √3 := Real.sqrt_pos.2 (by norm_num)
  have hwre : (hopfRoot (gain n μ) β).re = 1 + β := rfl
  have hwim : (hopfRoot (gain n μ) β).im = 2 * hopfFreq (gain n μ) β := rfl
  rw [hopfSpeed, Complex.div_re, Complex.re_ofReal_mul, Complex.im_ofReal_mul, rootSix_re,
    rootSix_im, hwre, hwim]
  exact add_pos (div_pos (by positivity) hns) (div_pos (by positivity) hns)

/-! ### Linear stability statements at the symmetric equilibrium -/

/-- **Linear stability** at the symmetric equilibrium `(p, …, p)`, `p ≥ 0`, with `α = p (1 + pⁿ)`
and `β > 0`, inside the Elowitz–Leibler boundary. -/
theorem re_neg_of_isRoot_linCharpoly {n : ℕ} {β p : ℝ} (hβ : 0 < β) (hp : 0 ≤ p)
    (h : 3 * gain n p ^ 2 * β < (4 - 2 * gain n p) * (1 + β) ^ 2) {z : ℂ}
    (hz : (linCharpoly (vectorField n (eqRate n p) β) (fun _ => p)).IsRoot z) : z.re < 0 := by
  rw [linCharpoly_vectorField n β hp] at hz
  exact re_neg_of_isRoot (gain_nonneg n hp) hβ h hz

/-- **Linear instability** at the symmetric equilibrium `(p, …, p)`, `p ≥ 0`, with
`α = p (1 + pⁿ)` and `β > 0`, outside the Elowitz–Leibler boundary. -/
theorem exists_re_pos_of_isRoot_linCharpoly {n : ℕ} {β p : ℝ} (hβ : 0 < β) (hp : 0 ≤ p)
    (h : (4 - 2 * gain n p) * (1 + β) ^ 2 < 3 * gain n p ^ 2 * β) :
    ∃ z, (linCharpoly (vectorField n (eqRate n p) β) (fun _ => p)).IsRoot z ∧ 0 < z.re := by
  rw [linCharpoly_vectorField n β hp]
  exact exists_re_pos_of_isRoot hβ h

/-- **The standard regime is unstable.** For Elowitz–Leibler's standard parameters `n = 2`,
`α = 216`, `β = 5`, with `p > 0` the equilibrium level (`p (1 + p²) = 216`), some eigenvalue of
the linearization at `(p, …, p)` has positive real part. -/
theorem exists_re_pos_standardRegime {p : ℝ} (hp : 0 < p) (hpα : eqRate 2 p = 216) :
    ∃ z, (linCharpoly (vectorField 2 216 5) (fun _ => p)).IsRoot z ∧ 0 < z.re := by
  rw [← hpα]
  refine exists_re_pos_of_isRoot_linCharpoly (by norm_num) hp.le ?_
  have hp5 : 5 < p := by
    by_contra h; have h := not_lt.1 h
    unfold eqRate at hpα; nlinarith [sq_nonneg p]
  have h1 : 0 < 1 + p ^ 2 := by positivity
  have hg : gain 2 p = 2 * p ^ 2 / (1 + p ^ 2) := by simp [gain]
  have hg' : 19 / 10 < gain 2 p := by
    rw [hg, lt_div_iff₀ h1]; nlinarith
  have hg2 : gain 2 p < 2 := gain_lt (by norm_num) hp.le |>.trans_le (by norm_num)
  nlinarith

/-! ### Periodic orbits from the Hopf theorem -/

/-- The open positive orthant in `(μ, x)`-space, where (EL) is smooth. -/
def posOrthant : Set (ℝ × (Fin 6 → ℝ)) := {q | ∀ j, 0 < q.2 j}

lemma isOpen_posOrthant : IsOpen posOrthant := by
  have : posOrthant = ⋂ j : Fin 6, {q : ℝ × (Fin 6 → ℝ) | 0 < q.2 j} := by
    ext q; simp [posOrthant]
  rw [this]
  exact isOpen_iInter_of_finite fun j =>
    isOpen_lt continuous_const ((continuous_apply j).comp continuous_snd)

lemma contDiffOn_repression (n : ℕ) (j : Fin 6) :
    ContDiffOn ℝ ∞ (fun q : ℝ × (Fin 6 → ℝ) => eqRate n q.1 / (1 + q.2 j ^ n)) posOrthant := by
  simp only [eqRate]
  refine ContDiffOn.div (by fun_prop) (by fun_prop) ?_
  intro q hq
  exact (one_add_pow_pos (hq j).le n).ne'

lemma contDiffOn_vectorField (n : ℕ) (β : ℝ) :
    ContDiffOn ℝ ∞ (fun q : ℝ × (Fin 6 → ℝ) => vectorField n (eqRate n q.1) β q.2)
      posOrthant := by
  refine contDiffOn_pi.2 fun k => ?_
  fin_cases k
  · exact (contDiffOn_repression n 5).sub (by fun_prop)
  · exact (contDiffOn_repression n 3).sub (by fun_prop)
  · exact (contDiffOn_repression n 4).sub (by fun_prop)
  · exact ContDiffOn.mul contDiffOn_const (by fun_prop)
  · exact ContDiffOn.mul contDiffOn_const (by fun_prop)
  · exact ContDiffOn.mul contDiffOn_const (by fun_prop)

/-- **Periodic orbits of the six-variable repressilator near a Hopf point** (from the Hopf
theorem). Let `β > 0` and let `μc > 0` be a Hopf level, `IsHopf (gain n μc) β`, with critical
rate `αc = μc (1 + μcⁿ)` and Hopf frequency `ω`. Assuming the Hopf theorem on `ℝ⁶`, for every
`ε > 0` there are a rate `α` with `|α - αc| < ε` and a nonconstant `T`-periodic solution of
(EL), `|T - 2π/ω| < ε`, staying within `ε` of the symmetric equilibrium. -/
theorem exists_periodicOrbit (hH : HopfBifurcationTheorem 6) {n : ℕ} {β μc : ℝ} (hβ : 0 < β)
    (hμc : 0 < μc) (hc : IsHopf (gain n μc) β) :
    ∀ ε > 0, ∃ α T : ℝ, ∃ γ : ℝ → Fin 6 → ℝ, |α - eqRate n μc| < ε ∧ 0 < T ∧
      |T - 2 * π / hopfFreq (gain n μc) β| < ε ∧
      IsIntegralCurve γ (fun _ x => vectorField n α β x) ∧
      (∀ t, γ (t + T) = γ t) ∧ (∃ t, γ t ≠ γ 0) ∧ ∀ t, dist (γ t) (fun _ => μc) < ε := by
  intro ε hε
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exfalso; unfold IsHopf at hc; simp [gain] at hc; nlinarith
    · exact h
  have hga : 0 < gain n μc := by unfold gain; positivity
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuousAt_iff.1 (continuous_eqRate n).continuousAt ε hε
  have hev : ∀ᶠ μ in 𝓝 μc, 0 < μ := lt_mem_nhds hμc
  have hpoly : ∀ μ, 0 < μ → linCharpoly (vectorField n (eqRate n μ) β) (fun _ => μ) =
      (jacobian (gain n μ) β).charpoly.map Complex.ofRealHom := fun μ hμ =>
    linCharpoly_vectorField n β hμ.le
  obtain ⟨μ, T, γ, hμ, hT, hTε, hγ, hper, hnc, hdist⟩ :=
    hH (fun μ x => vectorField n (eqRate n μ) β x) posOrthant (fun μ _ => μ)
      (hopfEigenvalue n β) (hopfSpeed n β μc) μc (hopfFreq (gain n μc) β) isOpen_posOrthant
      (fun _ => hμc) (contDiffOn_vectorField n β)
      (continuous_pi fun _ => continuous_id).continuousAt
      (hev.mono fun μ hμ => (vectorField_const_eq_zero_iff hμ.le).2 rfl)
      (hopfFreq_pos hga hβ)
      (by rw [hpoly μc hμc]; exact rootMultiplicity_hopf hga hβ hc)
      (fun z hz hre => by
        rw [hpoly μc hμc] at hz; exact eq_of_isRoot_of_re_eq_zero hga.le hβ hz hre)
      (hev.mono fun μ hμ => by rw [hpoly μ hμ]; exact isRoot_hopfEigenvalue n β μ)
      (hopfEigenvalue_hopf hβ hc) (hasDerivAt_hopfEigenvalue hβ hμc hc)
      (re_hopfSpeed_pos hn hβ hμc).ne' (min ε δ) (lt_min hε hδ)
  refine ⟨eqRate n μ, T, γ, ?_, hT, hTε.trans_le (min_le_left _ _), hγ, hper, hnc,
    fun t => (hdist t).trans_le (min_le_left _ _)⟩
  have := hδε (x := μ) (by rw [Real.dist_eq]; exact hμ.trans_le (min_le_right _ _))
  rwa [Real.dist_eq] at this

end MathlibExt.Biology.Dynamics.RepressilatorSixVar
