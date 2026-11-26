/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Domains.Biology.Ecology.BoundaryESSStabilityTendstoOfPos

/-!
# A regular ESS is linearly stable for the replicator dynamics

For a symmetric matrix game with payoff matrix `A`, the replicator equation on the simplex
`Δ = {x | x ≥ 0, ∑ x = 1}` is `ẋ_i = x_i ((A x)_i - x · A x)`. This module proves that a
**regular** evolutionarily stable state `p` (Taylor and Jonker 1978) is linearly stable: every
complex eigenvalue of the Jacobian of the replicator field at `p` with an eigenvector in the
tangent space has negative real part.

## Definitions

* `simplex`: the simplex of mixed strategies.
* `replicatorField`: the replicator vector field of the matrix game `A`.
* `IsESS`: evolutionarily stable state (Maynard Smith and Price).
* `IsRegularESS`: regular ESS (Taylor and Jonker 1978).
* `replicatorJacobian`: the Jacobian matrix of the replicator vector field at `p`.

## Main result

* `IsRegularESS.re_lt_zero`: every complex eigenvalue of the Jacobian at a regular ESS with an
  eigenvector in the tangent space has negative real part.

Sources: J. Hofbauer, P. Schuster and K. Sigmund, "A note on evolutionary stable strategies and
game dynamics", J. Theor. Biol. 81 (1979) 609–612; P. D. Taylor and L. B. Jonker,
"Evolutionarily stable strategies and game dynamics", Math. Biosci. 40 (1978) 145–156, §§2–4;
J. Hofbauer and K. Sigmund, "Evolutionary game dynamics", Bull. Amer. Math. Soc. (N.S.) 40
(2003) 479–519, §2.6, Theorem 7.
-/

@[expose] public section

namespace WantedExt.Biology.Ecology.BoundaryESSStabilityWanted

open Matrix Filter Topology

variable {ι : Type*} [Fintype ι]

/-- A **regular ESS** in the sense of Taylor and Jonker (1978): an ESS `p` such that
`(A p)_i < p · A p` for every strategy `i` outside the support of `p`, and `x · A x < 0` for
every nonzero `x` with `∑ x = 0` supported in the support of `p`. -/
def IsRegularESS (A : Matrix ι ι ℝ) (p : ι → ℝ) : Prop :=
  IsESS A p ∧ (∀ i, p i = 0 → (A *ᵥ p) i < p ⬝ᵥ A *ᵥ p) ∧
    ∀ x : ι → ℝ, x ≠ 0 → ∑ i, x i = 0 → (∀ i, p i = 0 → x i = 0) → x ⬝ᵥ A *ᵥ x < 0

/-- The Jacobian matrix of the replicator vector field of `A` at `p`. -/
noncomputable def replicatorJacobian [DecidableEq ι] (A : Matrix ι ι ℝ) (p : ι → ℝ) :
    Matrix ι ι ℝ :=
  LinearMap.toMatrix' (fderiv ℝ (replicatorField A) p : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))

/-- An ESS is a Nash equilibrium: no mixed strategy earns more against `p` than `p` itself. -/
private theorem IsESS.le_of_mem_simplex {A : Matrix ι ι ℝ} {p q : ι → ℝ}
    (h : IsESS A p) (hq : q ∈ simplex ι) : q ⬝ᵥ A *ᵥ p ≤ p ⬝ᵥ A *ᵥ p := by
  by_cases hqp : q = p
  · rw [hqp]
  · rcases h.2 q hq hqp with h1 | h1
    · exact h1.le
    · exact h1.1.le

/-- Against an ESS, every pure strategy earns at most `p · A p`. -/
private theorem IsESS.mulVec_le {A : Matrix ι ι ℝ} {p : ι → ℝ} (h : IsESS A p) (j : ι) :
    (A *ᵥ p) j ≤ p ⬝ᵥ A *ᵥ p := by
  classical
  have hj : (Pi.single j 1 : ι → ℝ) ∈ simplex ι :=
    ⟨fun i => by by_cases hij : i = j <;> simp [hij], by simp⟩
  simpa [single_dotProduct] using h.le_of_mem_simplex hj

/-- Strategies in the support of an ESS earn exactly `p · A p` against `p`. -/
private theorem IsESS.mulVec_eq_of_ne_zero {A : Matrix ι ι ℝ} {p : ι → ℝ} (h : IsESS A p)
    {i : ι} (hi : p i ≠ 0) : (A *ᵥ p) i = p ⬝ᵥ A *ᵥ p := by
  classical
  have hp0 : ∀ j, 0 ≤ p j := h.1.1
  have hp1 : ∑ j, p j = 1 := h.1.2
  have hle : ∀ j, (A *ᵥ p) j ≤ p ⬝ᵥ A *ᵥ p := fun j => h.mulVec_le j
  have hsum : ∑ j, p j * ((A *ᵥ p) j - p ⬝ᵥ A *ᵥ p) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp1, one_mul]
    exact sub_self _
  have hterm := (Finset.sum_eq_zero_iff_of_nonpos fun j _ =>
    mul_nonpos_of_nonneg_of_nonpos (hp0 j) (sub_nonpos.2 (hle j))).1 hsum i
    (Finset.mem_univ i)
  rcases mul_eq_zero.1 hterm with h0 | h0
  · exact absurd h0 hi
  · exact sub_eq_zero.1 h0

/-- The `i`-th coordinate of `A *ᵥ ·` as a continuous linear map. -/
private def rowCLM (A : Matrix ι ι ℝ) (i : ι) : (ι → ℝ) →L[ℝ] ℝ :=
  ∑ j, A i j • ContinuousLinearMap.proj j

private theorem rowCLM_apply (A : Matrix ι ι ℝ) (i : ι) (x : ι → ℝ) :
    rowCLM A i x = (A *ᵥ x) i := by
  simp [rowCLM, Matrix.mulVec, dotProduct]

/-- The quadratic form `x ↦ x ⬝ᵥ A *ᵥ x`. -/
private def quadForm (A : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ := x ⬝ᵥ A *ᵥ x

/-- The derivative of the quadratic form at `p`. -/
private def quadDeriv (A : Matrix ι ι ℝ) (p : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  ∑ j, ((p j) • rowCLM A j + (rowCLM A j p) • ContinuousLinearMap.proj j)

private theorem hasDeriv_quad (A : Matrix ι ι ℝ) (p : ι → ℝ) :
    HasFDerivAt (quadForm A) (quadDeriv A p) p := by
  have hfun : quadForm A = fun x : ι → ℝ =>
      ∑ j, ((ContinuousLinearMap.proj j : (ι → ℝ) →L[ℝ] ℝ) x) * (rowCLM A j x) := by
    funext x
    simp [quadForm, dotProduct, rowCLM_apply]
  rw [hfun]
  exact HasFDerivAt.fun_sum (fun j _ =>
    (ContinuousLinearMap.proj j).hasFDerivAt.mul (rowCLM A j).hasFDerivAt)

/-- The derivative of the quadratic form sends `h` to `h ⬝ᵥ A *ᵥ p + p ⬝ᵥ A *ᵥ h`. -/
private theorem quadDeriv_apply (A : Matrix ι ι ℝ) (p h : ι → ℝ) :
    quadDeriv A p h = h ⬝ᵥ A *ᵥ p + p ⬝ᵥ A *ᵥ h := by
  have e1 : ∀ j : ι, ((p j) • rowCLM A j +
      (rowCLM A j p) • (ContinuousLinearMap.proj j : (ι → ℝ) →L[ℝ] ℝ)) h
      = h j * (A *ᵥ p) j + p j * (A *ᵥ h) j := fun j => by
    simp [rowCLM_apply, add_comm, mul_comm]
  have e2 : quadDeriv A p h = ∑ j, (h j * (A *ᵥ p) j + p j * (A *ᵥ h) j) := by
    simp [quadDeriv, e1]
  rw [e2, Finset.sum_add_distrib]
  simp [dotProduct]

/-- The derivative of the replicator field at `p`, as a continuous linear map. -/
private def repDeriv (A : Matrix ι ι ℝ) (p : ι → ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi fun i =>
    (((ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ) p) • (rowCLM A i - quadDeriv A p) +
      ((rowCLM A i p) - quadForm A p) • ContinuousLinearMap.proj i)

private theorem hasDeriv_rep (A : Matrix ι ι ℝ) (p : ι → ℝ) :
    HasFDerivAt (replicatorField A) (repDeriv A p) p := by
  refine hasFDerivAt_pi.mpr fun i => ?_
  have hfun : (fun x : ι → ℝ => replicatorField A x i) =
      (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ) *
        (⇑(rowCLM A i) - quadForm A) := by
    funext x
    simp [replicatorField, rowCLM_apply, quadForm]
  rw [hfun]
  exact (ContinuousLinearMap.proj i).hasFDerivAt.mul
    ((rowCLM A i).hasFDerivAt.sub (hasDeriv_quad A p))

/-- The derivative of the replicator field at `p` sends `h` to
`h i * ((A p) i - p · A p) + p i * ((A h) i - h · A p - p · A h)` in coordinate `i`. -/
private theorem repDeriv_apply (A : Matrix ι ι ℝ) (p h : ι → ℝ) (i : ι) :
    repDeriv A p h i
      = h i * ((A *ᵥ p) i - p ⬝ᵥ A *ᵥ p) +
        p i * ((A *ᵥ h) i - h ⬝ᵥ A *ᵥ p - p ⬝ᵥ A *ᵥ h) := by
  simp [repDeriv, rowCLM_apply, quadDeriv_apply, quadForm]
  ring

/-- The Fréchet derivative of the replicator field at `p` equals `repDeriv`. -/
private theorem fderiv_rep (A : Matrix ι ι ℝ) (p : ι → ℝ) :
    fderiv ℝ (replicatorField A) p = repDeriv A p :=
  (hasDeriv_rep A p).fderiv

/-- The `i`-th coordinate of `A` applied to the `j`-th basis vector is `A i j`. -/
private theorem mulVec_single_one [DecidableEq ι] (A : Matrix ι ι ℝ) (i j : ι) :
    (A *ᵥ Pi.single j (1 : ℝ)) i = A i j := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/-- The `j`-th basis vector dotted against `A p` is `(A p) j`. -/
private theorem single_dotProduct_mulVec [DecidableEq ι] (A : Matrix ι ι ℝ) (p : ι → ℝ)
    (j : ι) : (Pi.single j (1 : ℝ)) ⬝ᵥ A *ᵥ p = (A *ᵥ p) j := by
  simp [single_dotProduct]

/-- `p · A e_j` expands as `∑ k, p k * A k j`. -/
private theorem dotProduct_mulVec_single [DecidableEq ι] (A : Matrix ι ι ℝ) (p : ι → ℝ)
    (j : ι) : p ⬝ᵥ A *ᵥ Pi.single j (1 : ℝ) = ∑ k, p k * A k j := by
  simp [dotProduct]

/-- The entries of the replicator Jacobian at `p`. -/
private theorem jacobian_entry [DecidableEq ι] (A : Matrix ι ι ℝ) (p : ι → ℝ) (i j : ι) :
    (replicatorJacobian A p) i j
      = (if i = j then (1 : ℝ) else 0) * ((A *ᵥ p) i - p ⬝ᵥ A *ᵥ p) +
        p i * (A i j - (A *ᵥ p) j - ∑ k, p k * A k j) := by
  have hJ : ∀ a b : ι, (replicatorJacobian A p) a b
      = repDeriv A p (Pi.single b 1) a := fun a b => by
    unfold replicatorJacobian
    rw [fderiv_rep, LinearMap.toMatrix'_apply]
    rfl
  rw [hJ, repDeriv_apply, Pi.single_apply, mulVec_single_one,
    single_dotProduct_mulVec, dotProduct_mulVec_single]

/-- The complexified Jacobian acts in coordinate `i` by the complexified derivative formula. -/
private theorem jacobian_apply [DecidableEq ι] (A : Matrix ι ι ℝ) (p : ι → ℝ) (v : ι → ℂ)
    (i : ι) :
    (((replicatorJacobian A p).map (fun a : ℝ => (a : ℂ))) *ᵥ v) i
      = ((((A *ᵥ p) i - p ⬝ᵥ A *ᵥ p : ℝ)) : ℂ) * v i +
        (p i : ℂ) * ((((A.map (fun a : ℝ => (a : ℂ))) *ᵥ v) i
          - v ⬝ᵥ (fun j => ((A *ᵥ p) j : ℂ))
          - (fun k => (p k : ℂ)) ⬝ᵥ ((A.map (fun a : ℝ => (a : ℂ))) *ᵥ v))) := by
  have d1 : ∑ j, ((A i j : ℂ)) * v j
      = ((((A.map (fun a : ℝ => (a : ℂ))) *ᵥ v)) i) := by
    simp [Matrix.mulVec, dotProduct, Matrix.map_apply]
  have d2 : ∑ j, (((A *ᵥ p) j : ℂ)) * v j
      = v ⬝ᵥ (fun j => ((A *ᵥ p) j : ℂ)) := by
    rw [dotProduct]
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  have d3 : ∑ j, (((∑ k, p k * A k j : ℝ)) : ℂ) * v j
      = (fun k => (p k : ℂ)) ⬝ᵥ ((((A.map (fun a : ℝ => (a : ℂ))) *ᵥ v))) := by
    have w_eq : ∀ k, (((((A.map (fun a : ℝ => (a : ℂ))) *ᵥ v))) k)
        = ∑ j, ((A k j : ℂ)) * v j := fun k => by
      simp [Matrix.mulVec, dotProduct, Matrix.map_apply]
    have hcast : ∀ j, ((((∑ k, p k * A k j : ℝ))) : ℂ)
        = ∑ k, (p k : ℂ) * ((A k j : ℂ)) := fun j => by
      push_cast
      rfl
    simp only [hcast, Finset.sum_mul]
    change ∑ j, ∑ k, ((p k : ℂ) * (A k j : ℂ)) * v j = _
    rw [Finset.sum_comm]
    change ∑ k, ∑ j, ((p k : ℂ) * (A k j : ℂ)) * v j = _
    rw [dotProduct]
    apply Finset.sum_congr rfl
    intro k _
    rw [w_eq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hentryC : ∀ j, ((((replicatorJacobian A p) i j : ℝ)) : ℂ)
      = (if i = j then (1 : ℂ) else 0) * ((((A *ᵥ p) i - p ⬝ᵥ A *ᵥ p : ℝ)) : ℂ) +
        (p i : ℂ) * (((A i j : ℂ)) - (((A *ᵥ p) j : ℂ))
          - ((((∑ k, p k * A k j : ℝ))) : ℂ)) := fun j => by
    rw [jacobian_entry]
    by_cases hij : i = j <;> simp [hij]
  calc ((((replicatorJacobian A p).map (fun a : ℝ => (a : ℂ))) *ᵥ v) i)
        = ∑ j, ((((replicatorJacobian A p) i j : ℝ)) : ℂ) * v j := by
          simp [Matrix.mulVec, dotProduct, Matrix.map_apply]
      _ = ∑ j, ((if i = j then (1 : ℂ) else 0)
            * ((((A *ᵥ p) i - p ⬝ᵥ A *ᵥ p : ℝ)) : ℂ) +
            (p i : ℂ) * (((A i j : ℂ)) - (((A *ᵥ p) j : ℂ))
              - ((((∑ k, p k * A k j : ℝ))) : ℂ))) * v j := by
          apply Finset.sum_congr rfl
          intro j _
          rw [hentryC j]
      _ = (∑ j, ((if i = j then (1 : ℂ) else 0)
            * ((((A *ᵥ p) i - p ⬝ᵥ A *ᵥ p : ℝ)) : ℂ)) * v j) +
            (∑ j, ((p i : ℂ) * (((A i j : ℂ)) - (((A *ᵥ p) j : ℂ))
              - ((((∑ k, p k * A k j : ℝ))) : ℂ))) * v j) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro j _
          ring
      _ = ((((A *ᵥ p) i - p ⬝ᵥ A *ᵥ p : ℝ)) : ℂ) * v i +
            (p i : ℂ) * (∑ j, (((A i j : ℂ)) - (((A *ᵥ p) j : ℂ))
              - ((((∑ k, p k * A k j : ℝ))) : ℂ)) * v j) := by
          congr 1
          · calc (∑ j, ((if i = j then (1 : ℂ) else 0)
                  * ((((A *ᵥ p) i - p ⬝ᵥ A *ᵥ p : ℝ)) : ℂ)) * v j)
                  = ((((A *ᵥ p) i - p ⬝ᵥ A *ᵥ p : ℝ)) : ℂ) *
                    (∑ j, (if i = j then v j else 0)) := by
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro j _
                    split_ifs <;> ring
                _ = ((((A *ᵥ p) i - p ⬝ᵥ A *ᵥ p : ℝ)) : ℂ) * v i := by
                    rw [Fintype.sum_ite_eq]
          · calc (∑ j, ((p i : ℂ) * (((A i j : ℂ)) - (((A *ᵥ p) j : ℂ))
                  - ((((∑ k, p k * A k j : ℝ))) : ℂ))) * v j)
                  = ∑ j, (p i : ℂ) * (((((A i j : ℂ)) - (((A *ᵥ p) j : ℂ))
                    - ((((∑ k, p k * A k j : ℝ))) : ℂ))) * v j) := by
                    apply Finset.sum_congr rfl
                    intro j _
                    ring
              _ = (p i : ℂ) * (∑ j, (((A i j : ℂ)) - (((A *ᵥ p) j : ℂ))
                  - ((((∑ k, p k * A k j : ℝ))) : ℂ)) * v j) := by
                    rw [Finset.mul_sum]
      _ = ((((A *ᵥ p) i - p ⬝ᵥ A *ᵥ p : ℝ)) : ℂ) * v i +
            (p i : ℂ) * ((((A.map (fun a : ℝ => (a : ℂ))) *ᵥ v) i
              - v ⬝ᵥ (fun j => ((A *ᵥ p) j : ℂ))
              - (fun k => (p k : ℂ)) ⬝ᵥ ((A.map (fun a : ℝ => (a : ℂ))) *ᵥ v))) := by
          congr 1
          congr 1
          calc (∑ j, (((A i j : ℂ)) - (((A *ᵥ p) j : ℂ))
                  - ((((∑ k, p k * A k j : ℝ))) : ℂ)) * v j)
                = (∑ j, ((A i j : ℂ)) * v j) - (∑ j, (((A *ᵥ p) j : ℂ)) * v j)
                  - (∑ j, ((((∑ k, p k * A k j : ℝ))) : ℂ) * v j) := by
                  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
                  apply Finset.sum_congr rfl
                  intro j _
                  ring
            _ = ((((A.map (fun a : ℝ => (a : ℂ))) *ᵥ v) i)
                - v ⬝ᵥ (fun j => ((A *ᵥ p) j : ℂ))
                - (fun k => (p k : ℂ)) ⬝ᵥ ((A.map (fun a : ℝ => (a : ℂ))) *ᵥ v)) := by
                rw [d1, d2, d3]

/-- For a supported `v` with `∑ v = 0`, `v · A p = 0` when support strategies earn equally. -/
private theorem supported_dotProduct_eq_zero (A : Matrix ι ι ℝ) (p : ι → ℝ) (v : ι → ℂ)
    (hsupp : ∀ i, p i = 0 → v i = 0)
    (heq : ∀ i, p i ≠ 0 → (A *ᵥ p) i = p ⬝ᵥ A *ᵥ p)
    (hsum : ∑ i, v i = 0) :
    v ⬝ᵥ (fun j => ((A *ᵥ p) j : ℂ)) = 0 := by
  have hterm : ∀ j, v j * (((A *ᵥ p) j : ℂ))
      = v j * ((((p ⬝ᵥ A *ᵥ p : ℝ))) : ℂ) := fun j => by
    by_cases hpj : p j = 0
    · rw [hsupp j hpj]
      simp
    · rw [heq j hpj]
  calc v ⬝ᵥ (fun j => ((A *ᵥ p) j : ℂ))
        = ∑ j, v j * ((((p ⬝ᵥ A *ᵥ p : ℝ))) : ℂ) := by
          rw [dotProduct]
          apply Finset.sum_congr rfl
          intro j _
          exact hterm j
      _ = (∑ j, v j) * ((((p ⬝ᵥ A *ᵥ p : ℝ))) : ℂ) := by
          rw [Finset.sum_mul]
      _ = 0 := by
          rw [hsum, zero_mul]

/-- The real part of `∑ i, star (v i) * (A v) i` is the sum of the real quadratic forms on the
real and imaginary parts of `v`. -/
private theorem star_sum_mul_re (A : Matrix ι ι ℝ) (v : ι → ℂ) :
    (∑ i, star (v i) * ((((A.map (fun a : ℝ => (a : ℂ))) *ᵥ v)) i)).re
      = (fun j => (v j).re) ⬝ᵥ A *ᵥ (fun j => (v j).re)
        + (fun j => (v j).im) ⬝ᵥ A *ᵥ (fun j => (v j).im) := by
  have wre : ∀ i, ((((A.map (fun a : ℝ => (a : ℂ))) *ᵥ v)) i).re
      = ∑ j, A i j * (v j).re := fun i => by
    have e : ((((A.map (fun a : ℝ => (a : ℂ))) *ᵥ v)) i)
        = ∑ j, ((A i j : ℂ)) * v j := by
      simp [Matrix.mulVec, dotProduct, Matrix.map_apply]
    rw [e, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp [Complex.mul_re]
  have wim : ∀ i, ((((A.map (fun a : ℝ => (a : ℂ))) *ᵥ v)) i).im
      = ∑ j, A i j * (v j).im := fun i => by
    have e : ((((A.map (fun a : ℝ => (a : ℂ))) *ᵥ v)) i)
        = ∑ j, ((A i j : ℂ)) * v j := by
      simp [Matrix.mulVec, dotProduct, Matrix.map_apply]
    rw [e, Complex.im_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp [Complex.mul_im]
  have m : ∀ i, (star (v i) * ((((A.map (fun a : ℝ => (a : ℂ))) *ᵥ v)) i)).re
      = (v i).re * (((((A.map (fun a : ℝ => (a : ℂ))) *ᵥ v)) i)).re
        + (v i).im * (((((A.map (fun a : ℝ => (a : ℂ))) *ᵥ v)) i)).im := fun i => by
    simp [Complex.mul_re]
  rw [Complex.re_sum, dotProduct, dotProduct, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [m i, wre i, wim i]
  rfl

/-- **A regular ESS is linearly stable** (Taylor and Jonker 1978, §3 Theorem). For every payoff
matrix `A` and every regular ESS `p` of `A`, every complex eigenvalue `μ` of the Jacobian of the
replicator field at `p` with an eigenvector `h ≠ 0` in the tangent space `∑ h = 0` has
`Re μ < 0`.

Source: Taylor and Jonker (1978), §2 (regular ESS, p. 148), §3 Theorem (p. 150). -/
public theorem IsRegularESS.re_lt_zero [DecidableEq ι] {A : Matrix ι ι ℝ} {p : ι → ℝ}
    (h : IsRegularESS A p) (μ : ℂ) (v : ι → ℂ) (hv : v ≠ 0) (hsum : ∑ i, v i = 0)
    (hμ : (replicatorJacobian A p).map (fun a : ℝ => (a : ℂ)) *ᵥ v = μ • v) : μ.re < 0 := by
  classical
  obtain ⟨hESS, hbound, hneg⟩ := h
  have hp0 : ∀ i, 0 ≤ p i := hESS.1.1
  have heq : ∀ i, p i ≠ 0 → (A *ᵥ p) i = p ⬝ᵥ A *ᵥ p :=
    fun i hi => hESS.mulVec_eq_of_ne_zero hi
  have heig : ∀ i, ((((A *ᵥ p) i - p ⬝ᵥ A *ᵥ p : ℝ)) : ℂ) * v i +
      (p i : ℂ) * ((((A.map (fun a : ℝ => (a : ℂ))) *ᵥ v) i
        - v ⬝ᵥ (fun j => ((A *ᵥ p) j : ℂ))
        - (fun k => (p k : ℂ)) ⬝ᵥ ((A.map (fun a : ℝ => (a : ℂ))) *ᵥ v))) = μ * v i := fun i => by
    have e := congrArg (fun w : ι → ℂ => w i) hμ
    rw [jacobian_apply A p v i] at e
    simpa [Pi.smul_apply, smul_eq_mul] using e
  by_cases hnsupp : ∃ i, p i = 0 ∧ v i ≠ 0
  · obtain ⟨i, hpi, hvi⟩ := hnsupp
    have e := heig i
    rw [hpi] at e
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at e
    have hμeq : μ = ((((A *ᵥ p) i - p ⬝ᵥ A *ᵥ p : ℝ)) : ℂ) :=
      (mul_right_cancel₀ hvi e).symm
    have hneg' : ((A *ᵥ p) i - p ⬝ᵥ A *ᵥ p) < 0 := sub_neg.2 (hbound i hpi)
    calc μ.re = ((((A *ᵥ p) i - p ⬝ᵥ A *ᵥ p : ℝ)) : ℂ).re :=
          congrArg Complex.re hμeq
      _ = ((A *ᵥ p) i - p ⬝ᵥ A *ᵥ p) := Complex.ofReal_re _
      _ < 0 := hneg'
  · have hsupp : ∀ i, p i = 0 → v i = 0 :=
      fun i hi => by_contra fun hvi => hnsupp ⟨i, hi, hvi⟩
    have hs1 : v ⬝ᵥ (fun j => ((A *ᵥ p) j : ℂ)) = 0 :=
      supported_dotProduct_eq_zero A p v hsupp heq hsum
    have hkey : ∀ i, star (v i) * ((((A.map (fun a : ℝ => (a : ℂ))) *ᵥ v) i
        - (fun k => (p k : ℂ)) ⬝ᵥ ((A.map (fun a : ℝ => (a : ℂ))) *ᵥ v)))
        = μ * (star (v i) * v i / ((p i : ℝ) : ℂ)) := fun i => by
      by_cases hpi : p i = 0
      · rw [hsupp i hpi]
        simp
      · have e := heig i
        rw [hs1] at e
        have hCi : ((((A *ᵥ p) i - p ⬝ᵥ A *ᵥ p : ℝ)) : ℂ) = 0 := by
          rw [heq i hpi]
          simp
        rw [hCi] at e
        simp only [zero_mul, zero_add, sub_zero] at e
        have hpiC : ((p i : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpi
        have e2 : ((((A.map (fun a : ℝ => (a : ℂ))) *ᵥ v) i
            - (fun k => (p k : ℂ)) ⬝ᵥ ((A.map (fun a : ℝ => (a : ℂ))) *ᵥ v)))
            = μ * v i / ((p i : ℝ) : ℂ) := by
          rw [← e]
          exact (mul_div_cancel_left₀ _ hpiC).symm
        rw [e2, ← mul_div_assoc, ← mul_div_assoc]
        congr 1
        ring
    have hsumkey : (∑ i, star (v i) * ((((A.map (fun a : ℝ => (a : ℂ))) *ᵥ v) i
          - (fun k => (p k : ℂ)) ⬝ᵥ ((A.map (fun a : ℝ => (a : ℂ))) *ᵥ v))))
          = μ * (∑ i, star (v i) * v i / ((p i : ℝ) : ℂ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact hkey i
    have hconj0 : (∑ i, star (v i)) = 0 := by
      have e : (∑ i, star (v i)) = star (∑ i, v i) := by rw [star_sum]
      rw [e, hsum, star_zero]
    have hL : (∑ i, star (v i) * ((((A.map (fun a : ℝ => (a : ℂ))) *ᵥ v) i
          - (fun k => (p k : ℂ)) ⬝ᵥ ((A.map (fun a : ℝ => (a : ℂ))) *ᵥ v))))
          = ∑ i, star (v i) * ((((A.map (fun a : ℝ => (a : ℂ))) *ᵥ v) i)) := by
      calc (∑ i, star (v i) * ((((A.map (fun a : ℝ => (a : ℂ))) *ᵥ v) i
              - (fun k => (p k : ℂ)) ⬝ᵥ ((A.map (fun a : ℝ => (a : ℂ))) *ᵥ v))))
            = ∑ i, (star (v i) * ((((A.map (fun a : ℝ => (a : ℂ))) *ᵥ v)) i)
              - (fun k => (p k : ℂ)) ⬝ᵥ ((A.map (fun a : ℝ => (a : ℂ))) *ᵥ v)
                * star (v i)) := by
              apply Finset.sum_congr rfl
              intro i _
              ring
          _ = (∑ i, star (v i) * ((((A.map (fun a : ℝ => (a : ℂ))) *ᵥ v) i)))
              - ∑ i, (fun k => (p k : ℂ)) ⬝ᵥ ((A.map (fun a : ℝ => (a : ℂ))) *ᵥ v)
                * star (v i) :=
              Finset.sum_sub_distrib _ _
          _ = (∑ i, star (v i) * ((((A.map (fun a : ℝ => (a : ℂ))) *ᵥ v) i)))
              - (fun k => (p k : ℂ)) ⬝ᵥ ((A.map (fun a : ℝ => (a : ℂ))) *ᵥ v)
                * (∑ i, star (v i)) := by
              rw [Finset.mul_sum]
          _ = ∑ i, star (v i) * ((((A.map (fun a : ℝ => (a : ℂ))) *ᵥ v) i)) := by
              rw [hconj0, mul_zero, sub_zero]
    have hLS : (∑ i, star (v i) * ((((A.map (fun a : ℝ => (a : ℂ))) *ᵥ v) i)))
        = μ * (∑ i, star (v i) * v i / ((p i : ℝ) : ℂ)) := by
      rw [← hL, hsumkey]
    have hnorm : ∀ i, star (v i) * v i = ((((‖v i‖ ^ 2 : ℝ))) : ℂ) := fun i => by
      have e0 := Complex.conj_mul' (v i)
      rwa [starRingEnd_apply, ← Complex.ofReal_pow] at e0
    have hterm : ∀ i, (star (v i) * v i / ((p i : ℝ) : ℂ)).re
        = ‖v i‖ ^ 2 / p i := fun i => by
      rw [hnorm i, ← Complex.ofReal_div, Complex.ofReal_re]
    have hterm0 : ∀ i, (star (v i) * v i / ((p i : ℝ) : ℂ)).im = 0 := fun i => by
      rw [hnorm i, ← Complex.ofReal_div, Complex.ofReal_im]
    have hSre : 0 < (∑ i, star (v i) * v i / ((p i : ℝ) : ℂ)).re := by
      have e : (∑ i, star (v i) * v i / ((p i : ℝ) : ℂ)).re
          = ∑ i, ‖v i‖ ^ 2 / p i := by
        rw [Complex.re_sum]
        apply Finset.sum_congr rfl
        intro i _
        exact hterm i
      rw [e]
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
      simp only [Pi.zero_apply] at hj
      have hpjne : p j ≠ 0 := fun h0 => hj (hsupp j h0)
      have hpj : 0 < p j := lt_of_le_of_ne' (hp0 j) hpjne
      have hnormpos : 0 < ‖v j‖ ^ 2 :=
        sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hj)
      have hpos : 0 < ‖v j‖ ^ 2 / p j := div_pos hnormpos hpj
      exact Finset.sum_pos' (fun i _ => div_nonneg (sq_nonneg _) (hp0 i))
        ⟨j, Finset.mem_univ j, hpos⟩
    have hSim : (∑ i, star (v i) * v i / ((p i : ℝ) : ℂ)).im = 0 := by
      have e : (∑ i, star (v i) * v i / ((p i : ℝ) : ℂ)).im = ∑ _i : ι, (0 : ℝ) := by
        rw [Complex.im_sum]
        apply Finset.sum_congr rfl
        intro i _
        exact hterm0 i
      rw [e]
      exact Finset.sum_const_zero
    have husum : ∑ i, (v i).re = 0 := by
      have e : (∑ i, v i).re = (0 : ℂ).re := congrArg Complex.re hsum
      rwa [Complex.re_sum] at e
    have htsum : ∑ i, (v i).im = 0 := by
      have e : (∑ i, v i).im = (0 : ℂ).im := congrArg Complex.im hsum
      rwa [Complex.im_sum] at e
    have husupp : ∀ i, p i = 0 → (v i).re = 0 := fun i hi => by
      simp [hsupp i hi]
    have htsupp : ∀ i, p i = 0 → (v i).im = 0 := fun i hi => by
      simp [hsupp i hi]
    have hU : (fun j => (v j).re) ⬝ᵥ A *ᵥ (fun j => (v j).re) ≤ 0 := by
      by_cases hu0 : (fun j => (v j).re) = 0
      · simp [hu0]
      · exact (hneg _ hu0 husum husupp).le
    have hT : (fun j => (v j).im) ⬝ᵥ A *ᵥ (fun j => (v j).im) ≤ 0 := by
      by_cases ht0 : (fun j => (v j).im) = 0
      · simp [ht0]
      · exact (hneg _ ht0 htsum htsupp).le
    have hcases : (fun j => (v j).re) ≠ 0 ∨ (fun j => (v j).im) ≠ 0 := by
      by_contra hcon
      rw [not_or] at hcon
      simp only [not_not] at hcon
      apply hv
      funext j
      have r : (v j).re = 0 := by
        have hthis := congrFun hcon.1 j
        simpa using hthis
      have s : (v j).im = 0 := by
        have hthis := congrFun hcon.2 j
        simpa using hthis
      exact Complex.ext r s
    have hLre : (∑ i, star (v i) * ((((A.map (fun a : ℝ => (a : ℂ))) *ᵥ v) i))).re
        < 0 := by
      rw [star_sum_mul_re A v]
      rcases hcases with hu0 | ht0
      · have g := hneg _ hu0 husum husupp
        linarith
      · have g := hneg _ ht0 htsum htsupp
        linarith
    have hmul : μ.re * (∑ i, star (v i) * v i / ((p i : ℝ) : ℂ)).re
        = (∑ i, star (v i) * ((((A.map (fun a : ℝ => (a : ℂ))) *ᵥ v) i))).re := by
      have e := congrArg Complex.re hLS
      simp only [Complex.mul_re, hSim, mul_zero, sub_zero] at e
      exact e.symm
    by_contra hcon
    have hle : 0 ≤ μ.re := le_of_not_gt hcon
    have hnn := mul_nonneg hle hSre.le
    rw [hmul] at hnn
    exact absurd hnn (not_le_of_gt hLre)

end WantedExt.Biology.Ecology.BoundaryESSStabilityWanted
