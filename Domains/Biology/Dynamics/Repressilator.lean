/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.ODE.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The repressilator: symmetric equilibrium, Hopf condition and periodic orbits

The **repressilator** of Elowitz and Leibler is a ring of three genes, each repressing the next.
Their mRNA–protein model is `ṁᵢ = -mᵢ + α / (1 + pⱼⁿ) + α₀`, `ṗᵢ = -β (pᵢ - mᵢ)`, where gene
`j` is the predecessor of gene `i` in the ring. This file treats the leakless (`α₀ = 0`)
**protein-only reduction**: with the mRNAs at quasi-steady state `mᵢ = α / (1 + pⱼⁿ)` and time
rescaled by `β`, the protein concentrations `xᵢ = pᵢ` satisfy, with indices in `ZMod 3`
(`Fin 3` with wrap-around subtraction),

  `ẋᵢ = α / (1 + xᵢ₋₁ⁿ) - xᵢ`,   `i = 0, 1, 2`,   `α > 0`, `n ∈ ℕ`.        (R)

**This ODE form (R) is frozen**: `vectorField n α` is exactly its right-hand side, the state
space is `Fin 3 → ℝ`, `α` is the maximal (dimensionless) transcription rate and `n` the Hill
coefficient. The full six-dimensional mRNA–protein model is not treated.

**The reduction (R) does not cover Elowitz–Leibler's standard regime.** For the six-variable
model (with `α₀ = 0`) and loop gain `a < 2`, Elowitz and Leibler's instability boundary is
`(β + 1)² / β < 3 a² / (4 - 2 a)`; as `β → 0` or `β → ∞` the left side tends to `∞` and the
boundary tends to `a = 2`, the threshold of (R). At their standard parameters `n = 2`,
`α = 216`, `β = 5` the six-variable model is unstable (`a ≈ 1.94 < 2`, and
`3 a² / (4 - 2 a) ≈ 103 > 36 / 5`), while (R) with `n = 2` is linearly stable for every `α`
(`re_neg_of_le_two`). In (R) a Hopf point needs `n > 2`. These six-variable facts are quoted, not
proved here.

**Symmetric equilibrium.** For `α > 0` there is a unique `p > 0` with `p (1 + pⁿ) = α`, and the
constant state `(p, p, p)` is an equilibrium; for `n ≥ 1` it is the only equilibrium in the
closed nonnegative orthant (cyclic negative feedback with an odd number of repressions). It is
convenient to parametrize by the equilibrium level `p`, with `α = eqRate n p = p (1 + pⁿ)`, a
strictly increasing bijection `[0, ∞) → [0, ∞)`.

**Linearization.** At `(p, p, p)` with `α = p (1 + pⁿ)` the Jacobian is `-I - a P`, where `P` is
the cyclic shift and `a = gain n p = n pⁿ / (1 + pⁿ)` is the loop gain (minus the slope of the
repression function). Its characteristic polynomial is

  `χ(λ) = (λ + 1)³ + a³`,

with roots `-1 - a` and `-1 + a / 2 ± i (√3 / 2) a`. Hence the equilibrium is linearly stable
for `a < 2`, linearly unstable for `a > 2`, and at `a = 2` the linearization has the simple pure
imaginary pair `±i√3` (and the real eigenvalue `-3`). Since `a < n`, a Hopf point exists only
for `n > 2`, at `pⁿ = 2 / (n - 2)`; for `n ≤ 2` the symmetric equilibrium is linearly stable
for every `α > 0`. Along the curve `μ ↦ -1 + a(μ) / 2 + i (√3 / 2) a(μ)` of eigenvalues
(`μ` the equilibrium level) the real part crosses zero with speed `a'(μ) / 2 > 0`.

**Periodic orbits.** Mathlib has no Hopf bifurcation theorem (and Poincaré–Bendixson, which is
planar, does not apply to the three-dimensional system (R)). We state the classical local Hopf
theorem for `C^∞` families on `ℝᴺ` as an explicit hypothesis, `HopfBifurcationTheorem N`: a
smooth family with an equilibrium branch whose linearization has a simple pair of eigenvalues
`±iω₀`, no other eigenvalue on the imaginary axis, and an eigenvalue curve crossing the
imaginary axis with nonzero speed, has nonconstant periodic orbits, with periods near
`2π / ω₀`, at parameters arbitrarily close to the critical one and arbitrarily close to the
equilibrium. `exists_periodicOrbit` verifies every hypothesis of that theorem for (R) at any
Hopf point and concludes that (R) has nonconstant periodic orbits with periods near `2π / √3`
for transcription rates `α` arbitrarily close to the critical rate.

## Scope

Linear stability means every eigenvalue of the linearization has negative real part; the
nonlinear (Lyapunov) stability that it implies is not proved. The periodic orbit is obtained
from `HopfBifurcationTheorem 3`, which is a hypothesis, not a theorem proved here. The
direction of the bifurcation (first Lyapunov coefficient), the stability of the orbits and the
global bifurcation diagram are out of scope. The results are about the protein-only reduction
(R) only: they do not cover Elowitz–Leibler's standard regime (`n = 2`, `α = 216`, `β = 5`),
where the six-variable model oscillates but (R) is linearly stable.

## Main results

* `vectorField_const_eq_zero_iff`, `existsUnique_eqLevel`, `eq_const_of_vectorField_eq_zero`:
  the symmetric equilibrium and its uniqueness in the nonnegative orthant.
* `hasFDerivAt_vectorField`, `toMatrix'_fderiv_vectorField`: the linearization.
* `charpoly_jacobian`, `charpoly_map_jacobian`, `isRoot_iff`: the characteristic equation and
  its roots.
* `re_neg_of_isRoot`, `exists_re_pos_of_isRoot`: stability for `a < 2`, instability for
  `a > 2`.
* `isRoot_iff_of_gain_eq_two`, `rootMultiplicity_eq_one`, `eq_of_isRoot_of_re_eq_zero`,
  `hasDerivAt_hopfEigenvalue`, `re_hopfEigenvalue_deriv_pos`: the Hopf condition.
* `gain_lt`, `gain_lt_two_of_le_two`, `gain_eq_two_iff`: location of the Hopf point.
* `HopfBifurcationTheorem`, `exists_periodicOrbit`: periodic orbits near the Hopf point.

## References

* M. B. Elowitz and S. Leibler, *A synthetic oscillatory network of transcriptional
  regulators*, Nature 403 (2000) 335–338 (the mRNA–protein model and its stability boundary).
* S. Müller, J. Hofbauer, L. Endler, C. Flamm, S. Widder and P. Schuster, *A generalized model
  of the repressilator*, J. Math. Biol. 53 (2006) 905–937 (the protein-only model (R)).
* E. Hopf, *Abzweigung einer periodischen Lösung von einer stationären Lösung eines
  Differentialsystems*, Ber. Math.-Phys. Kl. Sächs. Akad. Wiss. Leipzig 94 (1942) 1–22, and
  J. E. Marsden and M. McCracken, *The Hopf Bifurcation and Its Applications*, Springer (1976)
  (the Hopf theorem stated as `HopfBifurcationTheorem`).
-/

@[expose] public section

open Filter Polynomial Real Set
open scoped Topology ContDiff

namespace MathlibExt.Biology.Dynamics.Repressilator

/-! ### The model -/

/-- The right-hand side of the repressilator (R): `ẋᵢ = α / (1 + xᵢ₋₁ⁿ) - xᵢ`, indices in
`Fin 3` with wrap-around subtraction (gene `i - 1` represses gene `i`). -/
noncomputable def vectorField (n : ℕ) (α : ℝ) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => α / (1 + x (i - 1) ^ n) - x i

/-- The transcription rate for which the symmetric equilibrium is at level `p`:
`eqRate n p = p (1 + pⁿ)`. -/
def eqRate (n : ℕ) (p : ℝ) : ℝ := p * (1 + p ^ n)

/-- The loop gain at the symmetric equilibrium of level `p`: `gain n p = n pⁿ / (1 + pⁿ)`, minus
the slope of the repression function `y ↦ eqRate n p / (1 + yⁿ)` at `y = p`. -/
noncomputable def gain (n : ℕ) (p : ℝ) : ℝ := n * p ^ n / (1 + p ^ n)

/-- The Jacobian `-I - a P` of (R) at a symmetric equilibrium with loop gain `a` (`P` the cyclic
shift `eᵢ₋₁ ↦ eᵢ`): `-1` on the diagonal, `-a` at the entries `(i, i - 1)`. -/
def jacobian (a : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => if j = i then -1 else if j = i - 1 then -a else 0

/-- The characteristic polynomial, over `ℂ`, of the linearization of a vector field `F` on `ℝᴺ`
at `x`. -/
noncomputable def linCharpoly {N : ℕ} (F : (Fin N → ℝ) → Fin N → ℝ) (x : Fin N → ℝ) : ℂ[X] :=
  (LinearMap.toMatrix' (fderiv ℝ F x : (Fin N → ℝ) →ₗ[ℝ] Fin N → ℝ)).charpoly.map
    Complex.ofRealHom

/-! ### The symmetric equilibrium -/

lemma one_add_pow_pos {p : ℝ} (hp : 0 ≤ p) (n : ℕ) : 0 < 1 + p ^ n := by positivity

/-- The constant state `(p, p, p)`, `p ≥ 0`, is an equilibrium of (R) iff `α = p (1 + pⁿ)`. -/
theorem vectorField_const_eq_zero_iff {n : ℕ} {α p : ℝ} (hp : 0 ≤ p) :
    vectorField n α (fun _ => p) = 0 ↔ α = eqRate n p := by
  have h := (one_add_pow_pos hp n).ne'
  constructor
  · intro hf
    have h0 := congrFun hf 0
    simp only [vectorField, Pi.zero_apply, sub_eq_zero] at h0
    rw [div_eq_iff h] at h0
    rw [eqRate, h0]
  · rintro rfl
    funext i
    simp [vectorField, eqRate, mul_div_assoc, div_self h]

lemma eqRate_strictMonoOn (n : ℕ) : StrictMonoOn (eqRate n) (Ici 0) := by
  intro p hp q hq hpq
  simp only [mem_Ici] at hp hq
  have : p ^ n ≤ q ^ n := pow_le_pow_left₀ hp hpq.le n
  simp only [eqRate]
  nlinarith [one_add_pow_pos hp n]

lemma continuous_eqRate (n : ℕ) : Continuous (eqRate n) := by
  unfold eqRate; fun_prop

/-- For `α > 0` there is exactly one positive equilibrium level `p`, i.e. one `p > 0` with
`p (1 + pⁿ) = α`. -/
theorem existsUnique_eqLevel (n : ℕ) {α : ℝ} (hα : 0 < α) :
    ∃! p : ℝ, 0 < p ∧ eqRate n p = α := by
  obtain ⟨p, hp, hpα⟩ : ∃ p ∈ Icc 0 α, eqRate n p = α := by
    refine intermediate_value_Icc hα.le (continuous_eqRate n).continuousOn ⟨?_, ?_⟩
    · simp [eqRate, hα.le]
    · have : 0 ≤ α ^ n := by positivity
      simp only [eqRate]; nlinarith
  have hp0 : 0 < p := by
    rcases hp.1.lt_or_eq with h | h
    · exact h
    · subst h; simp [eqRate] at hpα; linarith
  refine ⟨p, ⟨hp0, hpα⟩, fun q ⟨hq, hqα⟩ => ?_⟩
  exact (eqRate_strictMonoOn n).injOn (mem_Ici.2 hq.le) (mem_Ici.2 hp0.le) (hqα.trans hpα.symm)

/-- For `n ≥ 1` and `α > 0`, the symmetric equilibrium is the only equilibrium of (R) in the
closed nonnegative orthant: if `x ≥ 0` is an equilibrium and `p ≥ 0` with `p (1 + pⁿ) = α`,
then `x = (p, p, p)`. -/
theorem eq_const_of_vectorField_eq_zero {n : ℕ} (hn : 0 < n) {α p : ℝ} (hα : 0 < α)
    (hp : 0 ≤ p) (hpα : eqRate n p = α) {x : Fin 3 → ℝ} (hx : ∀ j, 0 ≤ x j)
    (h : vectorField n α x = 0) : x = fun _ => p := by
  set f : ℝ → ℝ := fun y => α / (1 + y ^ n) with hf
  have anti : ∀ y z, 0 ≤ y → y < z → f z < f y := by
    intro y z hy hyz
    have : y ^ n < z ^ n := pow_lt_pow_left₀ hyz hy hn.ne'
    exact div_lt_div_of_pos_left hα (one_add_pow_pos hy n) (by linarith)
  have fix : ∀ i, x i = f (x (i - 1)) := fun i => by
    have := congrFun h i
    simp only [vectorField, Pi.zero_apply, sub_eq_zero] at this
    exact this.symm
  have hfp : f p = p := by
    have h1 := (one_add_pow_pos hp n).ne'
    simp only [hf, ← hpα, eqRate, mul_div_assoc, div_self h1, mul_one]
  have e0 : x 0 = f (x 2) := fix 0
  have e1 : x 1 = f (x 0) := fix 1
  have e2 : x 2 = f (x 1) := fix 2
  have h0 : x 0 = p := by
    rcases lt_trichotomy (x 0) p with hlt | heq | hgt
    · have h1 : p < x 1 := by rw [e1, ← hfp]; exact anti _ _ (hx 0) hlt
      have h2 : x 2 < p := by rw [e2, ← hfp]; exact anti _ _ hp h1
      have h0' : p < x 0 := by rw [e0, ← hfp]; exact anti _ _ (hx 2) h2
      linarith
    · exact heq
    · have h1 : x 1 < p := by rw [e1, ← hfp]; exact anti _ _ hp hgt
      have h2 : p < x 2 := by rw [e2, ← hfp]; exact anti _ _ (hx 1) h1
      have h0' : x 0 < p := by rw [e0, ← hfp]; exact anti _ _ hp h2
      linarith
  have h1 : x 1 = p := by rw [e1, h0, hfp]
  have h2 : x 2 = p := by rw [e2, h1, hfp]
  funext i
  fin_cases i <;> assumption

/-! ### The linearization -/

private lemma fin_three_neg_one : (-1 : Fin 3) = 2 := rfl

/-- Derivative of the repression function `y ↦ p (1 + pⁿ) / (1 + yⁿ)` at `y = p`. -/
lemma hasDerivAt_repression (n : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    HasDerivAt (fun y => eqRate n p / (1 + y ^ n)) (-gain n p) p := by
  have hd : HasDerivAt (fun y : ℝ => 1 + y ^ n) (n * p ^ (n - 1)) p := by
    simpa using HasDerivAt.const_add 1 (hasDerivAt_pow n p)
  have h := HasDerivAt.div (hasDerivAt_const p (eqRate n p)) hd (one_add_pow_pos hp n).ne'
  convert h using 1
  have h1 := (one_add_pow_pos hp n).ne'
  rcases n with _ | m
  · simp [gain]
  · simp only [gain, eqRate, Nat.add_sub_cancel, pow_succ]
    field_simp
    ring

/-- The continuous linear map of `jacobian a`. -/
noncomputable def jacobianCLM (a : ℝ) : (Fin 3 → ℝ) →L[ℝ] Fin 3 → ℝ :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' (jacobian a))

/-- **Linearization at the symmetric equilibrium.** With `α = p (1 + pⁿ)`, the derivative of the
repressilator field at `(p, p, p)` is the Jacobian `-I - a P`, `a = gain n p`. -/
theorem hasFDerivAt_vectorField (n : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    HasFDerivAt (vectorField n (eqRate n p)) (jacobianCLM (gain n p)) (fun _ => p) := by
  have hcomp : ∀ i : Fin 3, HasFDerivAt (fun x : Fin 3 → ℝ => vectorField n (eqRate n p) x i)
      ((-gain n p) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) (i - 1) -
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i)
      (fun _ => p) := by
    intro i
    have hr := hasDerivAt_repression n hp
    have h1 := HasDerivAt.comp_hasFDerivAt (fun _ : Fin 3 => p) hr
      (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) (i - 1) (fun _ : Fin 3 => p))
    exact HasFDerivAt.sub h1
      (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) i (fun _ : Fin 3 => p))
  have hpi := hasFDerivAt_pi.2 hcomp
  convert hpi using 1
  ext v i
  fin_cases i <;>
    simp (config := { decide := true }) [jacobianCLM, jacobian, Matrix.toLin'_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three, fin_three_neg_one] <;> ring

/-- The matrix of the linearization at the symmetric equilibrium is `jacobian (gain n p)`. -/
theorem toMatrix'_fderiv_vectorField (n : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    LinearMap.toMatrix' (fderiv ℝ (vectorField n (eqRate n p)) (fun _ => p) :
      (Fin 3 → ℝ) →ₗ[ℝ] Fin 3 → ℝ) = jacobian (gain n p) := by
  rw [(hasFDerivAt_vectorField n hp).fderiv, jacobianCLM, LinearMap.coe_toContinuousLinearMap,
    LinearMap.toMatrix'_toLin']

/-! ### The characteristic equation -/

/-- **Characteristic equation.** `det (λ I - J) = (λ + 1)³ + a³` for `J = -I - a P`. -/
theorem charpoly_jacobian (a : ℝ) : (jacobian a).charpoly = (X + 1) ^ 3 + C (a ^ 3) := by
  rw [Matrix.charpoly, Matrix.det_fin_three]
  simp (config := { decide := true }) [jacobian]
  ring

/-- The real eigenvalue `-1 - a`. -/
noncomputable def rootReal (a : ℝ) : ℂ := ⟨-1 - a, 0⟩

/-- The eigenvalue `-1 + a / 2 + i (√3 / 2) a`. -/
noncomputable def rootPlus (a : ℝ) : ℂ := ⟨-1 + a / 2, √3 / 2 * a⟩

/-- The eigenvalue `-1 + a / 2 - i (√3 / 2) a`. -/
noncomputable def rootMinus (a : ℝ) : ℂ := ⟨-1 + a / 2, -(√3 / 2 * a)⟩

private lemma cubic_expand (u v w : ℂ) :
    (X - C u) * (X - C v) * (X - C w) =
      X ^ 3 - C (u + v + w) * X ^ 2 + C (u * v + u * w + v * w) * X - C (u * v * w) := by
  simp only [map_add, map_mul]; ring

/-- Over `ℂ` the characteristic polynomial splits as
`(λ - (-1 - a)) (λ - (-1 + a/2 + i√3 a/2)) (λ - (-1 + a/2 - i√3 a/2))`. -/
theorem charpoly_map_jacobian (a : ℝ) :
    (jacobian a).charpoly.map Complex.ofRealHom =
      (X - C (rootReal a)) * (X - C (rootPlus a)) * (X - C (rootMinus a)) := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have e1 : rootReal a + rootPlus a + rootMinus a = -3 := by
    apply Complex.ext
    · simp [rootReal, rootPlus, rootMinus]; ring
    · simp [rootReal, rootPlus, rootMinus]
  have e2 : rootReal a * rootPlus a + rootReal a * rootMinus a + rootPlus a * rootMinus a = 3 := by
    apply Complex.ext
    · simp [rootReal, rootPlus, rootMinus]; ring_nf; simp [Real.sq_sqrt]; ring
    · simp [rootReal, rootPlus, rootMinus]; ring
  have e3 : rootReal a * rootPlus a * rootMinus a = -(1 + (a : ℂ) ^ 3) := by
    apply Complex.ext
    · simp [rootReal, rootPlus, rootMinus, pow_succ]; ring_nf; simp [Real.sq_sqrt]; ring
    · simp [rootReal, rootPlus, rootMinus, pow_succ]; ring
  rw [cubic_expand, e1, e2, e3, charpoly_jacobian]
  simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one,
    Polynomial.map_C, Complex.ofRealHom_eq_coe, map_neg, map_add, map_one,
    map_pow]
  have : (C (3 : ℂ)) = (3 : ℂ[X]) := rfl
  rw [this]
  ring

/-- **Eigenvalues.** The roots of the characteristic polynomial are `-1 - a` and
`-1 + a / 2 ± i (√3 / 2) a`. -/
theorem isRoot_iff (a : ℝ) (z : ℂ) :
    ((jacobian a).charpoly.map Complex.ofRealHom).IsRoot z ↔
      z = rootReal a ∨ z = rootPlus a ∨ z = rootMinus a := by
  rw [charpoly_map_jacobian]
  simp [IsRoot, sub_eq_zero, or_assoc]

lemma re_rootReal (a : ℝ) : (rootReal a).re = -1 - a := rfl
lemma re_rootPlus (a : ℝ) : (rootPlus a).re = -1 + a / 2 := rfl
lemma re_rootMinus (a : ℝ) : (rootMinus a).re = -1 + a / 2 := rfl

/-- **Linear stability below the Hopf point.** For `0 ≤ a < 2` every eigenvalue has negative
real part. -/
theorem re_neg_of_isRoot {a : ℝ} (ha : 0 ≤ a) (ha2 : a < 2) {z : ℂ}
    (hz : ((jacobian a).charpoly.map Complex.ofRealHom).IsRoot z) : z.re < 0 := by
  rcases (isRoot_iff a z).1 hz with rfl | rfl | rfl
  · rw [re_rootReal]; linarith
  · rw [re_rootPlus]; linarith
  · rw [re_rootMinus]; linarith

/-- **Instability above the Hopf point.** For `a > 2` some eigenvalue has positive real
part. -/
theorem exists_re_pos_of_isRoot {a : ℝ} (ha2 : 2 < a) :
    ∃ z, ((jacobian a).charpoly.map Complex.ofRealHom).IsRoot z ∧ 0 < z.re :=
  ⟨rootPlus a, (isRoot_iff a _).2 (Or.inr (Or.inl rfl)), by rw [re_rootPlus]; linarith⟩

/-! ### The Hopf condition -/

lemma rootPlus_two : rootPlus 2 = (√3 : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [rootPlus]

lemma rootMinus_two : rootMinus 2 = -((√3 : ℂ) * Complex.I) := by
  apply Complex.ext <;> simp [rootMinus]

lemma rootReal_two : rootReal 2 = -3 := by
  apply Complex.ext
  · simp [rootReal]; norm_num
  · simp [rootReal]

/-- **Eigenvalues at the Hopf point.** At loop gain `a = 2` the eigenvalues are `-3` and the
pure imaginary pair `±i√3`. -/
theorem isRoot_iff_of_gain_eq_two (z : ℂ) :
    ((jacobian 2).charpoly.map Complex.ofRealHom).IsRoot z ↔
      z = -3 ∨ z = (√3 : ℂ) * Complex.I ∨ z = -((√3 : ℂ) * Complex.I) := by
  rw [isRoot_iff, rootReal_two, rootPlus_two, rootMinus_two]

/-- **Simplicity.** At `a = 2`, `i√3` is a simple root of the characteristic polynomial. -/
theorem rootMultiplicity_eq_one :
    ((jacobian 2).charpoly.map Complex.ofRealHom).rootMultiplicity ((√3 : ℂ) * Complex.I) = 1 := by
  classical
  have hs : (0 : ℝ) < √3 := Real.sqrt_pos.2 (by norm_num)
  rw [charpoly_map_jacobian, rootMultiplicity_mul, rootMultiplicity_mul,
    rootMultiplicity_X_sub_C, rootMultiplicity_X_sub_C, rootMultiplicity_X_sub_C,
    rootReal_two, rootPlus_two, rootMinus_two]
  · have h1 : (√3 : ℂ) * Complex.I ≠ -3 := fun h => by
      have := congrArg Complex.re h; simp at this
    have h2 : (√3 : ℂ) * Complex.I ≠ -((√3 : ℂ) * Complex.I) := fun h => by
      have := congrArg Complex.im h; simp at this; linarith
    simp [h1, h2]
  · exact mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)
  · exact mul_ne_zero (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)) (X_sub_C_ne_zero _)

/-- **No other eigenvalue on the imaginary axis.** At `a = 2` the only eigenvalues with zero
real part are `±i√3`. -/
theorem eq_of_isRoot_of_re_eq_zero {z : ℂ}
    (hz : ((jacobian 2).charpoly.map Complex.ofRealHom).IsRoot z) (hre : z.re = 0) :
    z = (√3 : ℂ) * Complex.I ∨ z = -((√3 : ℂ) * Complex.I) := by
  rcases (isRoot_iff_of_gain_eq_two z).1 hz with rfl | h | h
  · norm_num at hre
  · exact Or.inl h
  · exact Or.inr h

/-- The eigenvalue curve through `i√3`: `μ ↦ -1 + a(μ) / 2 + i (√3 / 2) a(μ)`, `a = gain n`,
parametrized by the equilibrium level `μ`. -/
noncomputable def hopfEigenvalue (n : ℕ) (μ : ℝ) : ℂ := rootPlus (gain n μ)

lemma hopfEigenvalue_eq (n : ℕ) (μ : ℝ) :
    hopfEigenvalue n μ =
      ((-1 + gain n μ / 2 : ℝ) : ℂ) + ((√3 / 2 * gain n μ : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [hopfEigenvalue, rootPlus]

/-- The derivative of the loop gain: `a'(μ) = n² μⁿ⁻¹ / (1 + μⁿ)²`. -/
lemma hasDerivAt_gain (n : ℕ) {μ : ℝ} (hμ : 0 ≤ μ) :
    HasDerivAt (gain n) (n ^ 2 * μ ^ (n - 1) / (1 + μ ^ n) ^ 2) μ := by
  have hd : HasDerivAt (fun y : ℝ => y ^ n) (n * μ ^ (n - 1)) μ := hasDerivAt_pow n μ
  have h := HasDerivAt.div (HasDerivAt.const_mul (n : ℝ) hd) (HasDerivAt.const_add 1 hd)
    (one_add_pow_pos hμ n).ne'
  convert h using 1
  · funext y; simp [gain]
  · have h1 := (one_add_pow_pos hμ n).ne'
    field_simp
    ring

/-- **Transversality.** The eigenvalue curve `hopfEigenvalue n` has derivative
`(1/2 + i √3/2) a'(μ)`. -/
theorem hasDerivAt_hopfEigenvalue (n : ℕ) {μ : ℝ} (hμ : 0 ≤ μ) :
    HasDerivAt (hopfEigenvalue n)
      (((n ^ 2 * μ ^ (n - 1) / (1 + μ ^ n) ^ 2 / 2 : ℝ) : ℂ) +
        ((√3 / 2 * (n ^ 2 * μ ^ (n - 1) / (1 + μ ^ n) ^ 2) : ℝ) : ℂ) * Complex.I) μ := by
  have hg := hasDerivAt_gain n hμ
  have hre := HasDerivAt.ofReal_comp (HasDerivAt.const_add (-1) (HasDerivAt.div_const hg 2))
  have him := HasDerivAt.mul_const (HasDerivAt.ofReal_comp (HasDerivAt.const_mul (√3 / 2) hg))
    Complex.I
  convert HasDerivAt.add hre him using 1
  funext y; rw [hopfEigenvalue_eq]; rfl

/-- **Nonzero crossing speed.** For `n ≥ 1` and `μ > 0` the real part of the eigenvalue curve
increases with speed `a'(μ) / 2 > 0`. -/
theorem re_hopfEigenvalue_deriv_pos {n : ℕ} (hn : 0 < n) {μ : ℝ} (hμ : 0 < μ) :
    0 < (((n ^ 2 * μ ^ (n - 1) / (1 + μ ^ n) ^ 2 / 2 : ℝ) : ℂ) +
        ((√3 / 2 * (n ^ 2 * μ ^ (n - 1) / (1 + μ ^ n) ^ 2) : ℝ) : ℂ) * Complex.I).re := by
  have : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  positivity

/-! ### Location of the Hopf point -/

/-- The loop gain is below the Hill coefficient: `gain n p < n` for `n ≥ 1`, `p ≥ 0`. -/
theorem gain_lt {n : ℕ} (hn : 0 < n) {p : ℝ} (hp : 0 ≤ p) : gain n p < n := by
  have h1 := one_add_pow_pos hp n
  have : (0 : ℝ) < n := by exact_mod_cast hn
  rw [gain, div_lt_iff₀ h1]
  nlinarith

lemma gain_nonneg (n : ℕ) {p : ℝ} (hp : 0 ≤ p) : 0 ≤ gain n p := by
  unfold gain; have := one_add_pow_pos hp n; positivity

/-- **No Hopf point for `n ≤ 2`.** The loop gain stays below `2`. -/
theorem gain_lt_two_of_le_two {n : ℕ} (hn : n ≤ 2) {p : ℝ} (hp : 0 ≤ p) : gain n p < 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · simp [gain]
  · exact (gain_lt hn0 hp).trans_le (by exact_mod_cast hn)

/-- **The Hopf point for `n > 2`.** The loop gain equals `2` iff `pⁿ = 2 / (n - 2)`. -/
theorem gain_eq_two_iff {n : ℕ} (hn : 2 < n) {p : ℝ} (hp : 0 ≤ p) :
    gain n p = 2 ↔ p ^ n = 2 / (n - 2) := by
  have h1 := one_add_pow_pos hp n
  have hn' : (2 : ℝ) < n := by exact_mod_cast hn
  have h2 : (n : ℝ) - 2 ≠ 0 := by linarith
  rw [gain, div_eq_iff h1.ne', eq_div_iff h2]
  constructor <;> intro h <;> linarith

/-! ### Stability of the symmetric equilibrium -/

lemma linCharpoly_vectorField (n : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    linCharpoly (vectorField n (eqRate n p)) (fun _ => p) =
      (jacobian (gain n p)).charpoly.map Complex.ofRealHom := by
  rw [linCharpoly, toMatrix'_fderiv_vectorField n hp]

/-- **Linear stability.** If `gain n p < 2`, every eigenvalue of the linearization of (R) at its
symmetric equilibrium `(p, p, p)` (with `α = p (1 + pⁿ)`) has negative real part. -/
theorem re_neg_of_isRoot_linCharpoly {n : ℕ} {p : ℝ} (hp : 0 ≤ p) (hg : gain n p < 2) {z : ℂ}
    (hz : (linCharpoly (vectorField n (eqRate n p)) (fun _ => p)).IsRoot z) : z.re < 0 := by
  rw [linCharpoly_vectorField n hp] at hz
  exact re_neg_of_isRoot (gain_nonneg n hp) hg hz

/-- **Instability.** If `gain n p > 2`, some eigenvalue of the linearization of (R) at its
symmetric equilibrium has positive real part. -/
theorem exists_re_pos_of_isRoot_linCharpoly {n : ℕ} {p : ℝ} (hp : 0 ≤ p) (hg : 2 < gain n p) :
    ∃ z, (linCharpoly (vectorField n (eqRate n p)) (fun _ => p)).IsRoot z ∧ 0 < z.re := by
  rw [linCharpoly_vectorField n hp]
  exact exists_re_pos_of_isRoot hg

/-- **No Hopf bifurcation for `n ≤ 2`.** For every equilibrium level `p ≥ 0` (equivalently every
`α ≥ 0`), every eigenvalue of the linearization at the symmetric equilibrium has negative real
part; in particular none lies on the imaginary axis. -/
theorem re_neg_of_le_two {n : ℕ} (hn : n ≤ 2) {p : ℝ} (hp : 0 ≤ p) {z : ℂ}
    (hz : (linCharpoly (vectorField n (eqRate n p)) (fun _ => p)).IsRoot z) : z.re < 0 :=
  re_neg_of_isRoot_linCharpoly hp (gain_lt_two_of_le_two hn hp) hz

/-! ### Periodic orbits from the Hopf theorem -/

/-- **The local Hopf bifurcation theorem on `ℝᴺ`** (Hopf 1942; Marsden–McCracken), stated as a
proposition; it is used as an explicit hypothesis. Let `F μ x` be `C^∞` in `(μ, x)` on an open
set `U` containing `(μ₀, xe μ₀)`, let `xe` be a branch of equilibria continuous at `μ₀`, and
suppose the linearization at `xe μ₀` has `iω₀` (`ω₀ > 0`) as a simple eigenvalue, no
eigenvalue on the imaginary axis other than `±iω₀`, and an eigenvalue curve `lam` of the
linearizations at `xe μ` through `iω₀` whose real part crosses zero with nonzero speed. Then for
every `ε > 0` there are a parameter `μ` with `|μ - μ₀| < ε` and a nonconstant `T`-periodic
solution of `ẋ = F μ x` with `|T - 2π/ω₀| < ε` staying within `ε` of `xe μ₀`. -/
def HopfBifurcationTheorem (N : ℕ) : Prop :=
  ∀ (F : ℝ → (Fin N → ℝ) → Fin N → ℝ) (U : Set (ℝ × (Fin N → ℝ))) (xe : ℝ → Fin N → ℝ)
    (lam : ℝ → ℂ) (lam' : ℂ) (μ₀ ω₀ : ℝ),
    IsOpen U → (μ₀, xe μ₀) ∈ U → ContDiffOn ℝ ∞ (fun q : ℝ × (Fin N → ℝ) => F q.1 q.2) U →
    ContinuousAt xe μ₀ → (∀ᶠ μ in 𝓝 μ₀, F μ (xe μ) = 0) → 0 < ω₀ →
    (linCharpoly (F μ₀) (xe μ₀)).rootMultiplicity ((ω₀ : ℂ) * Complex.I) = 1 →
    (∀ z, (linCharpoly (F μ₀) (xe μ₀)).IsRoot z → z.re = 0 →
      z = (ω₀ : ℂ) * Complex.I ∨ z = -((ω₀ : ℂ) * Complex.I)) →
    (∀ᶠ μ in 𝓝 μ₀, (linCharpoly (F μ) (xe μ)).IsRoot (lam μ)) →
    lam μ₀ = (ω₀ : ℂ) * Complex.I → HasDerivAt lam lam' μ₀ → lam'.re ≠ 0 →
    ∀ ε > 0, ∃ μ T : ℝ, ∃ γ : ℝ → Fin N → ℝ, |μ - μ₀| < ε ∧ 0 < T ∧ |T - 2 * π / ω₀| < ε ∧
      IsIntegralCurve γ (fun _ x => F μ x) ∧ (∀ t, γ (t + T) = γ t) ∧ (∃ t, γ t ≠ γ 0) ∧
      ∀ t, dist (γ t) (xe μ₀) < ε

/-- The open positive orthant in `(μ, x)`-space, where (R) is smooth. -/
def posOrthant : Set (ℝ × (Fin 3 → ℝ)) := {q | ∀ j, 0 < q.2 j}

lemma isOpen_posOrthant : IsOpen posOrthant := by
  have : posOrthant = ⋂ j : Fin 3, {q : ℝ × (Fin 3 → ℝ) | 0 < q.2 j} := by
    ext q; simp [posOrthant]
  rw [this]
  exact isOpen_iInter_of_finite fun j =>
    isOpen_lt continuous_const ((continuous_apply j).comp continuous_snd)

lemma contDiffOn_vectorField (n : ℕ) :
    ContDiffOn ℝ ∞ (fun q : ℝ × (Fin 3 → ℝ) => vectorField n (eqRate n q.1) q.2) posOrthant := by
  refine contDiffOn_pi.2 fun i => ?_
  simp only [vectorField, eqRate]
  refine ContDiffOn.sub (ContDiffOn.div (by fun_prop) (by fun_prop) ?_) (by fun_prop)
  intro q hq
  exact (one_add_pow_pos (hq (i - 1)).le n).ne'

/-- **Periodic orbits of the repressilator near the Hopf point** (from the Hopf theorem). Let
`μc > 0` be a Hopf level, `gain n μc = 2`, with critical rate `αc = μc (1 + μcⁿ)`. Assuming the
Hopf theorem on `ℝ³`, for every `ε > 0` there are a rate `α` with `|α - αc| < ε` and a
nonconstant `T`-periodic solution of (R), `|T - 2π/√3| < ε`, staying within `ε` of the
symmetric equilibrium `(μc, μc, μc)`. -/
theorem exists_periodicOrbit (hH : HopfBifurcationTheorem 3) {n : ℕ} {μc : ℝ} (hμc : 0 < μc)
    (hc : gain n μc = 2) :
    ∀ ε > 0, ∃ α T : ℝ, ∃ γ : ℝ → Fin 3 → ℝ, |α - eqRate n μc| < ε ∧ 0 < T ∧
      |T - 2 * π / √3| < ε ∧ IsIntegralCurve γ (fun _ x => vectorField n α x) ∧
      (∀ t, γ (t + T) = γ t) ∧ (∃ t, γ t ≠ γ 0) ∧ ∀ t, dist (γ t) (fun _ => μc) < ε := by
  intro ε hε
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp [gain] at hc
    · exact h
  have hs : (0 : ℝ) < √3 := Real.sqrt_pos.2 (by norm_num)
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuousAt_iff.1 (continuous_eqRate n).continuousAt ε hε
  have hev : ∀ᶠ μ in 𝓝 μc, 0 < μ := lt_mem_nhds hμc
  have hpoly : ∀ μ, 0 < μ → linCharpoly (vectorField n (eqRate n μ)) (fun _ => μ) =
      (jacobian (gain n μ)).charpoly.map Complex.ofRealHom := fun μ hμ =>
    linCharpoly_vectorField n hμ.le
  obtain ⟨μ, T, γ, hμ, hT, hTε, hγ, hper, hnc, hdist⟩ :=
    hH (fun μ x => vectorField n (eqRate n μ) x) posOrthant (fun μ _ => μ) (hopfEigenvalue n) _
      μc √3 isOpen_posOrthant (fun _ => hμc) (contDiffOn_vectorField n)
      (continuous_pi fun _ => continuous_id).continuousAt
      (hev.mono fun μ hμ => (vectorField_const_eq_zero_iff hμ.le).2 rfl) hs
      (by rw [hpoly μc hμc, hc]; exact rootMultiplicity_eq_one)
      (fun z hz hre => by
        rw [hpoly μc hμc, hc] at hz; exact eq_of_isRoot_of_re_eq_zero hz hre)
      (hev.mono fun μ hμ => by
        rw [hpoly μ hμ]; exact (isRoot_iff _ _).2 (Or.inr (Or.inl rfl)))
      (by rw [hopfEigenvalue, hc, rootPlus_two]) (hasDerivAt_hopfEigenvalue n hμc.le)
      (re_hopfEigenvalue_deriv_pos hn hμc).ne' (min ε δ) (lt_min hε hδ)
  refine ⟨eqRate n μ, T, γ, ?_, hT, hTε.trans_le (min_le_left _ _), hγ, hper, hnc,
    fun t => (hdist t).trans_le (min_le_left _ _)⟩
  have := hδε (x := μ) (by rw [Real.dist_eq]; exact hμ.trans_le (min_le_right _ _))
  rwa [Real.dist_eq] at this

end MathlibExt.Biology.Dynamics.Repressilator
