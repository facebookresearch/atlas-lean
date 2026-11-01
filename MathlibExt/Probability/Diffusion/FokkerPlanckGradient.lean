/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Stationary densities of gradient-drift diffusions

On `ℝⁿ` (here `Fin n → ℝ`), the diffusion `dX = b(X) dt + √(2D) dW` has density evolving by
the Fokker–Planck equation `∂ₜ p = -div J`, with probability flux `J = b p - D ∇p`. For a
gradient drift `b = -∇Ψ` (as in the population-level diffusion models of Hashimoto, Gifford
and Jaakkola 2016 and PRESCIENT, Yeo, Saksena and Gifford 2021):

* the Gibbs density `p = c e^{-Ψ / D}` has **zero flux** everywhere, hence is stationary
  (`flux_gibbs_eq_zero`, `fokkerPlanckOp_gibbs_eq_zero`);
* conversely, a positive density with zero flux determines the potential: `∇Ψ = -D ∇ log p`
  (`pderiv_eq_of_flux_eq_zero`), so two potentials with a common zero-flux density differ by a
  constant (`exists_const_of_flux_eq_zero`): **the potential is identifiable** from the
  stationary density within the class of gradient drifts;
* outside that class the drift is not identifiable: for any antisymmetric matrix `A` the drift
  `-(∇Ψ + A ∇Ψ)` has the same stationary Gibbs density (`divergence_flux_rotational_gibbs`),
  and `exists_rotational_flux_ne_zero` gives an explicit drift of this kind on `ℝ²` with
  nonzero flux, so it differs from the gradient drift. This witness is our derivation.

Partial derivatives are `pderiv i f x = fderiv ℝ f x (Pi.single i 1)` (Mathlib's `lineDeriv`
along `Pi.single i 1` agrees with it at points of differentiability; the `fderiv` form is used
so that the second-derivative symmetry lemmas apply directly). For a non-differentiable `f`
Mathlib's `fderiv` is `0`, so each statement assumes the differentiability it needs. The
Gibbs density is not normalized here; stationarity is linear in `p`, and normalizability
(`∫ e^{-Ψ/D} < ∞`) is a separate condition not needed by these statements.

## Main definitions

* `pderiv i f x`, `grad f x`, `divergence F x`: coordinate partial derivatives, gradient and
  divergence on `Fin n → ℝ`.
* `flux D b p`: the probability flux `b p - D ∇p`.
* `fokkerPlanckOp D b p = -div (flux D b p)`: the right-hand side of the Fokker–Planck equation.
* `gibbs Ψ D x = e^{-Ψ x / D}`.

## References

* T. Hashimoto, D. Gifford, T. Jaakkola, *Learning population-level diffusions with generative
  RNNs*, ICML 2016, PMLR 48.
* G. H. T. Yeo, S. D. Saksena, D. K. Gifford, *Generative modeling of single-cell time series
  with PRESCIENT enables prediction of cell trajectories with interventions*, Nat. Commun. 12
  (2021), 3222.
* G. A. Pavliotis, *Stochastic Processes and Applications*, Springer (2014), ch. 4
  (stationary Fokker–Planck equation, reversible diffusions).
-/

@[expose] public section

open Finset

namespace MathlibExt.Probability.FokkerPlanck

variable {n : ℕ}

/-- The partial derivative `∂ᵢ f (x) = Df(x) eᵢ` on `Fin n → ℝ`. -/
noncomputable def pderiv (i : Fin n) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  fderiv ℝ f x (Pi.single i 1)

/-- The gradient `∇f(x) = (∂ᵢ f(x))ᵢ`. -/
noncomputable def grad (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => pderiv i f x

/-- The divergence `div F (x) = ∑ᵢ ∂ᵢ Fᵢ (x)` of a vector field. -/
noncomputable def divergence (F : (Fin n → ℝ) → Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, pderiv i (fun y => F y i) x

/-- The **probability flux** `J = b p - D ∇p` of the diffusion `dX = b dt + √(2D) dW` with
density `p`. -/
noncomputable def flux (D : ℝ) (b : (Fin n → ℝ) → Fin n → ℝ) (p : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => b x i * p x - D * pderiv i p x

/-- The **Fokker–Planck operator** `-div J`: the density evolves by `∂ₜ p = fokkerPlanckOp D b p`,
and `p` is stationary iff this vanishes. -/
noncomputable def fokkerPlanckOp (D : ℝ) (b : (Fin n → ℝ) → Fin n → ℝ) (p : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) : ℝ :=
  -divergence (flux D b p) x

/-- The (unnormalized) **Gibbs density** `e^{-Ψ(x) / D}`. -/
noncomputable def gibbs (Ψ : (Fin n → ℝ) → ℝ) (D : ℝ) (x : Fin n → ℝ) : ℝ :=
  Real.exp (-Ψ x / D)

private lemma pderiv_const_mul_gibbs {Ψ : (Fin n → ℝ) → ℝ} (hΨ : Differentiable ℝ Ψ) (D c : ℝ)
    (i : Fin n) (x : Fin n → ℝ) :
    pderiv i (fun y => c * gibbs Ψ D y) x = c * gibbs Ψ D x * (-pderiv i Ψ x / D) := by
  have h : HasFDerivAt (fun y => c * gibbs Ψ D y)
      (c • (Real.exp (-Ψ x / D) • ((-1 / D) • fderiv ℝ Ψ x))) x := by
    have h1 : HasFDerivAt (fun y => -Ψ y / D) ((-1 / D) • fderiv ℝ Ψ x) x := by
      have := ((hΨ x).hasFDerivAt.const_smul (-1 / D))
      refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
      simp [smul_eq_mul]; ring
    exact (h1.exp).const_mul c
  rw [pderiv, h.fderiv, pderiv]
  simp [gibbs, smul_eq_mul]
  ring

/-- **The Gibbs density has zero flux** under the gradient drift `-∇Ψ`: for differentiable `Ψ`,
`D ≠ 0` and any constant `c`, `J = -∇Ψ · c e^{-Ψ/D} - D ∇(c e^{-Ψ/D}) = 0`. -/
theorem flux_gibbs_eq_zero {Ψ : (Fin n → ℝ) → ℝ} (hΨ : Differentiable ℝ Ψ) {D : ℝ}
    (hD : D ≠ 0) (c : ℝ) : flux D (fun x => -grad Ψ x) (fun x => c * gibbs Ψ D x) = 0 := by
  funext x i
  simp only [flux, pderiv_const_mul_gibbs hΨ, Pi.neg_apply, grad, Pi.zero_apply]
  field_simp
  ring

/-- **The Gibbs density is stationary** for the gradient drift: `-div J = 0`. -/
theorem fokkerPlanckOp_gibbs_eq_zero {Ψ : (Fin n → ℝ) → ℝ} (hΨ : Differentiable ℝ Ψ) {D : ℝ}
    (hD : D ≠ 0) (c : ℝ) (x : Fin n → ℝ) :
    fokkerPlanckOp D (fun x => -grad Ψ x) (fun x => c * gibbs Ψ D x) x = 0 := by
  rw [fokkerPlanckOp, flux_gibbs_eq_zero hΨ hD c]
  simp [divergence, pderiv]

/-- **A zero-flux density determines the drift**: if `p > 0` is differentiable and the
gradient drift `-∇Ψ` has zero flux for `p`, then `∂ᵢ Ψ = -D ∂ᵢ log p`. -/
theorem pderiv_eq_of_flux_eq_zero {Ψ p : (Fin n → ℝ) → ℝ} {D : ℝ} (hp : Differentiable ℝ p)
    (hpos : ∀ x, 0 < p x) (h : flux D (fun x => -grad Ψ x) p = 0) (i : Fin n)
    (x : Fin n → ℝ) : pderiv i Ψ x = -D * pderiv i (fun y => Real.log (p y)) x := by
  have hx := congrFun (congrFun h x) i
  simp only [flux, grad, Pi.neg_apply, Pi.zero_apply] at hx
  have hlog : pderiv i (fun y => Real.log (p y)) x = pderiv i p x / p x := by
    rw [pderiv, ((hp x).hasFDerivAt.log (hpos x).ne').fderiv, pderiv]
    simp [smul_eq_mul]
    field_simp
  rw [hlog]
  have := (hpos x).ne'
  field_simp
  linarith

/-- **Identifiability of the potential**: two differentiable potentials whose gradient drifts
both have zero flux for the same positive differentiable density differ by a constant. -/
theorem exists_const_of_flux_eq_zero {Ψ₁ Ψ₂ p : (Fin n → ℝ) → ℝ} {D : ℝ}
    (hΨ₁ : Differentiable ℝ Ψ₁) (hΨ₂ : Differentiable ℝ Ψ₂) (hp : Differentiable ℝ p)
    (hpos : ∀ x, 0 < p x) (h₁ : flux D (fun x => -grad Ψ₁ x) p = 0)
    (h₂ : flux D (fun x => -grad Ψ₂ x) p = 0) : ∃ C, ∀ x, Ψ₁ x = Ψ₂ x + C := by
  have hd : Differentiable ℝ (fun x => Ψ₁ x - Ψ₂ x) := hΨ₁.sub hΨ₂
  have hzero : ∀ x, fderiv ℝ (fun x => Ψ₁ x - Ψ₂ x) x = 0 := by
    intro x
    have hpart : ∀ i, fderiv ℝ (fun x => Ψ₁ x - Ψ₂ x) x (Pi.single i 1) = 0 := by
      intro i
      rw [fderiv_fun_sub (hΨ₁ x) (hΨ₂ x)]
      have e1 := pderiv_eq_of_flux_eq_zero hp hpos h₁ i x
      have e2 := pderiv_eq_of_flux_eq_zero hp hpos h₂ i x
      simp only [pderiv] at e1 e2
      simp [e1, e2]
    ext v
    have hv : v = ∑ i, v i • (Pi.single i (1 : ℝ) : Fin n → ℝ) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    rw [hv, map_sum]
    simp [map_smul, hpart]
  obtain h := is_const_of_fderiv_eq_zero hd hzero
  exact ⟨Ψ₁ 0 - Ψ₂ 0, fun x => by have := h x 0; linarith⟩

/-- The flux of the Gibbs density under the drift `-(∇Ψ + A ∇Ψ)` is the rotational part
`-(A ∇Ψ) e^{-Ψ / D}` (for differentiable `Ψ`, `D ≠ 0`, any matrix `A`). -/
theorem flux_rotational_gibbs {Ψ : (Fin n → ℝ) → ℝ} (hΨ : Differentiable ℝ Ψ) {D : ℝ}
    (hD : D ≠ 0) (A : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) (i : Fin n) :
    flux D (fun y => -(grad Ψ y + A.mulVec (grad Ψ y))) (gibbs Ψ D) y i =
      -(A.mulVec (grad Ψ y) i * gibbs Ψ D y) := by
  have h := pderiv_const_mul_gibbs hΨ D 1 i y
  simp only [one_mul] at h
  simp only [flux, h, Pi.neg_apply, Pi.add_apply, grad]
  field_simp
  ring

private lemma sum_antisymm_mul_symm {A S : Matrix (Fin n) (Fin n) ℝ} (hA : A.transpose = -A)
    (hS : ∀ i j, S i j = S j i) : ∑ i, ∑ j, A i j * S i j = 0 := by
  have hA' : ∀ i j, A j i = -A i j := fun i j => by
    simpa using congrFun (congrFun hA i) j
  have h : ∑ i, ∑ j, A i j * S i j = -∑ i, ∑ j, A i j * S i j := by
    calc ∑ i, ∑ j, A i j * S i j = ∑ j, ∑ i, A i j * S i j := Finset.sum_comm
      _ = ∑ j, ∑ i, -(A j i * S j i) := by
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
          rw [hA' j i, hS i j]; ring
      _ = -∑ i, ∑ j, A i j * S i j := by simp [Finset.sum_neg_distrib]
  linarith

/-- **Rotational drifts share the Gibbs stationary density** (non-identifiability): for a
`C²` potential `Ψ`, `D ≠ 0` and an antisymmetric matrix `A` (`Aᵀ = -A`), the drift
`-(∇Ψ + A ∇Ψ)` satisfies `div J = 0` for `p = e^{-Ψ / D}`. -/
theorem divergence_flux_rotational_gibbs {Ψ : (Fin n → ℝ) → ℝ} (hΨ : ContDiff ℝ 2 Ψ) {D : ℝ}
    (hD : D ≠ 0) {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.transpose = -A) (x : Fin n → ℝ) :
    divergence (flux D (fun y => -(grad Ψ y + A.mulVec (grad Ψ y))) (gibbs Ψ D)) x = 0 := by
  have hΨd : Differentiable ℝ Ψ := hΨ.differentiable (by norm_num)
  have hF : ContDiff ℝ 1 (fderiv ℝ Ψ) := hΨ.fderiv_right (by norm_num)
  have hFd : Differentiable ℝ (fderiv ℝ Ψ) := hF.differentiable (by norm_num)
  have hg : ∀ i y, fderiv ℝ (gibbs Ψ D) y (Pi.single i 1) =
      gibbs Ψ D y * (-fderiv ℝ Ψ y (Pi.single i 1) / D) := by
    intro i y
    simpa [pderiv] using pderiv_const_mul_gibbs hΨd D 1 i y
  have hflux : flux D (fun y => -(grad Ψ y + A.mulVec (grad Ψ y))) (gibbs Ψ D) =
      fun y i => -((∑ j, A i j * fderiv ℝ Ψ y (Pi.single j 1)) * gibbs Ψ D y) := by
    funext y i
    simp only [flux, grad, Pi.neg_apply, Pi.add_apply, Matrix.mulVec, dotProduct, pderiv, hg]
    field_simp
    ring
  -- derivatives of the pieces
  have hgd : ∀ y, HasFDerivAt (gibbs Ψ D)
      (Real.exp (-Ψ y / D) • ((-1 / D) • fderiv ℝ Ψ y)) y := by
    intro y
    have h1 : HasFDerivAt (fun y => -Ψ y / D) ((-1 / D) • fderiv ℝ Ψ y) y := by
      have := ((hΨd y).hasFDerivAt.const_smul (-1 / D))
      refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
      simp [smul_eq_mul]; ring
    exact h1.exp
  have hdj : ∀ j, HasFDerivAt (fun y => fderiv ℝ Ψ y (Pi.single j 1))
      ((fderiv ℝ (fderiv ℝ Ψ) x).flip (Pi.single j 1)) x := by
    intro j
    simpa using (hFd x).hasFDerivAt.clm_apply (hasFDerivAt_const (Pi.single j (1 : ℝ)) x)
  have hsum : ∀ i, HasFDerivAt (fun y => ∑ j, A i j * fderiv ℝ Ψ y (Pi.single j 1))
      (∑ j, A i j • (fderiv ℝ (fderiv ℝ Ψ) x).flip (Pi.single j 1)) x := by
    intro i
    exact HasFDerivAt.fun_sum fun j _ => (hdj j).const_mul (A i j)
  have hterm : ∀ i, pderiv i (fun y => -((∑ j, A i j * fderiv ℝ Ψ y (Pi.single j 1)) *
      gibbs Ψ D y)) x =
      -(∑ j, A i j * fderiv ℝ (fderiv ℝ Ψ) x (Pi.single i 1) (Pi.single j 1)) * gibbs Ψ D x +
        (∑ j, A i j * fderiv ℝ Ψ x (Pi.single j 1)) * gibbs Ψ D x *
          (fderiv ℝ Ψ x (Pi.single i 1) / D) := by
    intro i
    rw [pderiv, (((hsum i).fun_mul (hgd x)).fun_neg).fderiv]
    simp only [neg_add_rev, add_apply, neg_apply, smul_apply, _root_.sum_apply,
      ContinuousLinearMap.flip_apply, smul_eq_mul, neg_mul, gibbs]
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [divergence, hflux]
  simp only [hterm, Finset.sum_add_distrib]
  have hH : ∀ i j, fderiv ℝ (fderiv ℝ Ψ) x (Pi.single i 1) (Pi.single j 1) =
      fderiv ℝ (fderiv ℝ Ψ) x (Pi.single j 1) (Pi.single i 1) := fun i j =>
    (hΨ.contDiffAt.isSymmSndFDerivAt (by simp)) _ _
  have h1 := sum_antisymm_mul_symm hA (S := Matrix.of fun i j =>
    fderiv ℝ (fderiv ℝ Ψ) x (Pi.single i 1) (Pi.single j 1)) (fun i j => by simp [hH i j])
  have h2 := sum_antisymm_mul_symm hA (S := Matrix.of fun i j =>
    fderiv ℝ Ψ x (Pi.single i 1) * fderiv ℝ Ψ x (Pi.single j 1)) (fun i j => by simp; ring)
  simp only [Matrix.of_apply] at h1 h2
  have e1 : ∑ i, -(∑ j, A i j * fderiv ℝ (fderiv ℝ Ψ) x (Pi.single i 1) (Pi.single j 1)) *
      gibbs Ψ D x = -(gibbs Ψ D x * ∑ i, ∑ j, A i j *
        fderiv ℝ (fderiv ℝ Ψ) x (Pi.single i 1) (Pi.single j 1)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i, (∑ j, A i j * fderiv ℝ Ψ x (Pi.single j 1)) * gibbs Ψ D x *
      (fderiv ℝ Ψ x (Pi.single i 1) / D) = gibbs Ψ D x / D * ∑ i, ∑ j, A i j *
        (fderiv ℝ Ψ x (Pi.single i 1) * fderiv ℝ Ψ x (Pi.single j 1)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e1, e2, h1, h2]
  simp

/-- **An explicit rotational drift with nonzero flux** (our derivation): on `ℝ²` with
`Ψ(x) = (x₀² + x₁²) / 2`, `D = 1` and the rotation generator `A = [[0, 1], [-1, 0]]`, the
drift `-(∇Ψ + A ∇Ψ)` has the Gibbs (standard Gaussian, up to normalization) density as a
stationary density, yet its flux at `(1, 0)` is nonzero, so it is not the gradient drift. -/
theorem exists_rotational_flux_ne_zero :
    let Ψ : (Fin 2 → ℝ) → ℝ := fun x => (x 0 ^ 2 + x 1 ^ 2) / 2
    let A : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]
    (∀ x, divergence (flux 1 (fun y => -(grad Ψ y + A.mulVec (grad Ψ y))) (gibbs Ψ 1)) x = 0) ∧
      flux 1 (fun y => -(grad Ψ y + A.mulVec (grad Ψ y))) (gibbs Ψ 1) ![1, 0] ≠ 0 := by
  intro Ψ A
  have hΨ : ContDiff ℝ 2 Ψ := by
    simp only [Ψ]
    fun_prop
  have hA : A.transpose = -A := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [A]
  refine ⟨fun x => divergence_flux_rotational_gibbs hΨ one_ne_zero hA x, fun h => ?_⟩
  have h1 := congrFun h 1
  rw [flux_rotational_gibbs (hΨ.differentiable (by norm_num)) one_ne_zero] at h1
  have hd : ∀ x : Fin 2 → ℝ, HasFDerivAt Ψ
      (x 0 • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0 +
        x 1 • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1) x := by
    intro x
    have := ((((hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) x).pow 2).fun_add
      ((hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) x).pow 2)).mul_const (1 / 2 : ℝ))
    convert this using 1
    · funext y; simp only [Ψ]; ring
    · ext v
      simp
      ring
  have hg : grad Ψ ![1, 0] = ![1, 0] := by
    funext j
    fin_cases j <;> simp [grad, pderiv, (hd _).fderiv]
  simp [hg, A, Matrix.mulVec, dotProduct, Fin.sum_univ_two, gibbs, Real.exp_ne_zero] at h1

end MathlibExt.Probability.FokkerPlanck
