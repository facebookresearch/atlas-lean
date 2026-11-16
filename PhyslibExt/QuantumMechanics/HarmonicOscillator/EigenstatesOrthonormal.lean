/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Physlib.QuantumMechanics.HarmonicOscillator.Eigenstates
public import Physlib.QuantumMechanics.HarmonicOscillator.OneDimension.Eigenfunction
public import PhyslibExt.SpaceAndTime.Space.Integrals.Prod

/-!
# Orthonormality of the QHO eigenstates

## i. Overview

The Cartesian-basis eigenstates of the `d`-dimensional quantum harmonic oscillator are
orthonormal. Each `d`-dimensional eigenfunction is a product of one-dimensional
eigenfunctions (upstream `eigenfunction_eq_prod_oneDim`), so the inner product splits
(`Space.integral_prod_coord`) into one-dimensional inner products, each a Kronecker
delta by the one-dimensional orthonormality result. This fills the
`eigenstates_orthonormal` sorry in
`Physlib.QuantumMechanics.HarmonicOscillator.Eigenstates`.

## ii. Key results

* `QuantumMechanics.HarmonicOscillator.oneDim_factor_integral`: each
  one-dimensional factor integrates to a Kronecker delta.
* `QuantumMechanics.HarmonicOscillator.eigenstates_orthonormal_of_oneDim`: the
  eigenstates are orthonormal.
-/

@[expose] public section

noncomputable section

namespace QuantumMechanics
namespace HarmonicOscillator

open Complex Constants Finset InnerProductSpace Polynomial SchwartzMap Space SpaceDHilbertSpace
open KroneckerDelta MeasureTheory
open scoped Nat Real ComplexConjugate

variable {d : ℕ} (Q : HarmonicOscillator d)

/-- Each one-dimensional factor integrates to a Kronecker delta, by one-dimensional
  orthonormality. -/
lemma oneDim_factor_integral (i : Fin d) (n n' : Fin d → ℕ) :
    (∫ t : ℝ, starRingEnd ℂ ((Q.oneDim i).eigenfunction (n i) t)
      * (Q.oneDim i).eigenfunction (n' i) t) = ((δ[n i, n' i] : ℕ) : ℂ) := by
  have h := orthonormal_iff_ite.mp (Q.oneDim i).eigenfunction_orthonormal (n i) (n' i)
  rw [OneDimension.HilbertSpace.inner_mk_mk] at h
  rw [h]
  by_cases hi : n i = n' i
  · simp [hi, kroneckerDelta]
  · simp [hi, kroneckerDelta]

/-- The eigenstates are orthonormal. -/
theorem eigenstates_orthonormal_of_oneDim (n n' : Fin d → ℕ) :
    ⟪(Q.eigenstate n : Q.HS), Q.eigenstate n'⟫_ℂ = δ[n, n'] := by
  have hinner : ⟪(Q.eigenstate n : Q.HS), Q.eigenstate n'⟫_ℂ
      = ∫ x, starRingEnd ℂ (Q.eigenfunction n x) * Q.eigenfunction n' x ∂volume := by
    change ⟪Q.eigenstate n, Q.eigenstate n'⟫_ℂ = _
    rw [eigenstate_eq, eigenstate_eq,
      SpaceDHilbertSpace.SchwartzSubmodule.schwartzEquiv_inner]
  rw [hinner]
  have hprod : (fun x : Space d => starRingEnd ℂ (Q.eigenfunction n x)
      * Q.eigenfunction n' x)
      = (fun x => ∏ i, starRingEnd ℂ ((Q.oneDim i).eigenfunction (n i) (x i))
        * (Q.oneDim i).eigenfunction (n' i) (x i)) := by
    funext x
    rw [eigenfunction_eq_prod_oneDim, eigenfunction_eq_prod_oneDim,
      map_prod (starRingEnd ℂ), ← Finset.prod_mul_distrib]
  rw [hprod, Space.integral_prod_coord (fun i t => starRingEnd ℂ
    ((Q.oneDim i).eigenfunction (n i) t) * (Q.oneDim i).eigenfunction (n' i) t)]
  simp only [oneDim_factor_integral Q _ n n']
  rw [← Nat.cast_prod]
  congr 1
  by_cases h : n = n'
  · subst h
    simp [kroneckerDelta]
  · have hzero : ∏ i, δ[n i, n' i] = 0 := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp h
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [kroneckerDelta, hi])
    rw [hzero]
    simp [kroneckerDelta, h]

end HarmonicOscillator
end QuantumMechanics
