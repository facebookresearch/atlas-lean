/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.ABBoundaryProfile

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Sharpness.ABBoundaryProfile`

* `abbMag_meanfield` applied under its `φ(S) ≥ 1` hypothesis on `Λ_1 ⊂ ℤ²`;
* `abbMag_aizenmanBarsky_le_envelope` applied under its row-sum and target hypotheses;
* `#check`-style statement of the headline definitions `abbTarget`, `abbMag`, `abbPhi`.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.ABBoundaryProfile

open _root_.StatMech _root_.StatMech.Sharpness

-- The mean-field inequality from `φ(S) ≥ 1`.
example (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (hphi : ∀ S : Finset (Option (sctBox 2 1)), some (sctBoxOrigin 2 1) ∈ S →
      (mpiSurfaceEvent (withGhost (sctBoxGraph 2 1)) (abbTarget 2 1) S).Nonempty →
        1 ≤ abbPhi 2 1 β h S) :
    1 - abbMag 2 1 β h ≤ β * deriv (fun b => abbMag 2 1 b h) β :=
  abbMag_meanfield 2 1 β h hβ hh hphi

-- The Aizenman–Barsky envelope inequality.
example (d n : ℕ) (β h J0 U : ℝ)
    (hrow : ∀ x, abcrIncidentCoupling (sctBoxGraph d n) (abbCoupling d n) x ≤ J0)
    (hβ : 0 ≤ β) (hh : 0 ≤ h) (hU : 0 ≤ U)
    (ht : ∀ x : sctBox d n, probV (abfaParams (sctBoxGraph d n) (abbCoupling d n) β h)
      (connEvent (withGhost (sctBoxGraph d n)) Set.univ (some x) (abbTarget d n)) ≤
        U) :
    deriv (fun b => abbMag d n b h) β ≤ J0 * U * deriv (fun t => abbMag d n β t) h :=
  abbMag_aizenmanBarsky_le_envelope d n β h J0 U hrow hβ hh hU ht

-- The ghost belongs to the boundary target.
example (d n : ℕ) : (none : Option (sctBox d n)) ∈ abbTarget d n := by
  simp [abbTarget]

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.ABBoundaryProfile
