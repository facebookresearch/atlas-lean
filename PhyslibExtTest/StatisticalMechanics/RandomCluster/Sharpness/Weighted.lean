/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.Weighted

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.Weighted`

On the one-dimensional box of radius `1` with unit couplings, `q = 2`, `β = 1`:
* `weighted_wired_box_differential_inequality` gives `c θ / D ≤ ∂θ/∂β` with `c > 0`;
* `weightedWiredActiveDenom_pos`: the OSSS denominator is positive;
* `weighted_wired_box_hasDerivAt`: the crossing mean is differentiable in `β`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.Weighted

open _root_.StatMech _root_.StatMech.OSSS _root_.StatMech.OSSS.FKSharpnessWeighted
open Lattice RevealmentConstruction AdaptiveCovLowerGeom ActiveBoundaryDifferential
open WiredBoxDifferential ActiveEdgeDifferential FK RevealmentTranslation

-- The weighted differential inequality on a concrete box.
example : ∃ c : ℝ, 0 < c ∧
    c * (weightedWiredActiveTheta 1 1 (fun _ => 1) 2 1 /
      weightedWiredActiveDenom 1 1 (fun _ => 1) 2 1) ≤
    deriv (fun b => FK.activeBCProbOf (boxGraph 1 1)
      (wiredBoxBoundaryGraph 1 1) (FK.betaParams (fun _ => 1) b) 2
      (crossEvent (boxActiveEdge 1 1) 0
        (vertexBoundary 1 1))) 1 :=
  weighted_wired_box_differential_inequality 1 1 le_rfl le_rfl (fun _ => 1)
    (fun _ => one_pos) 2 1 1 (by norm_num) one_pos le_rfl

-- The OSSS denominator is positive on the same box.
example : 0 < weightedWiredActiveDenom 1 1 (fun _ => 1) 2 1 :=
  weightedWiredActiveDenom_pos 1 1 le_rfl (fun _ => 1) (fun _ => one_pos) 2 1 (by norm_num) one_pos

-- Differentiability in `β` of the crossing mean, for positive couplings.
example (d n : ℕ) (J : Sym2 (boxVerts d n) → ℝ) (hJ : ∀ e, 0 < J e) :
    ∃ D, HasDerivAt
      (fun b => FK.activeBCMean (boxGraph d n)
        (wiredBoxBoundaryGraph d n) (FK.betaParams J b) 2
        (crossIndG (boxActiveEdge d n) 0 n)) D 1 :=
  ⟨_, weighted_wired_box_hasDerivAt d n J hJ 2 1 (by norm_num) one_pos⟩

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.Weighted
