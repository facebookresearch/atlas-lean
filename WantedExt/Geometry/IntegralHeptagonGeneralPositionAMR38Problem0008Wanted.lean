/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Seven points in general position with integral distances (Geometry Junkyard)

D. Eppstein, The Geometry Junkyard: Open Problems, 'Integer distances': it is open whether there are
even seven points at integer distances in general position (no three in a line and no four on a
circle).
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Sphere.Basic

@[expose] public section

namespace MathlibExt.Geometry.IntegralHeptagonGeneralPositionAMR38Problem0008Wanted

/-!
Source: D. Eppstein, The Geometry Junkyard: Open Problems, Integer distances,
https://ics.uci.edu/~eppstein/junkyard/open.html. UnsolvedMath record UM-03900008 (`AMR-038-0008`),
dataset ulamai/UnsolvedMath v1.8.0.

Points of the Euclidean plane; 'no four on a circle' is `¬ EuclideanGeometry.Cospherical` for four
distinct points (in the plane, cospherical means concyclic); integer distances are natural numbers.
The all-`n` question (Erdős Problem 213) is the open entry
`OpenConjectures/Geometry/IntegralDistanceGeneralPositionArbitrarySize`.
-/

/-- Seven points in the plane in general position (no three on a line, no four on a circle) with
all pairwise distances integers. -/
def integralHeptagonInGeneralPosition : Prop :=
  ∃ P : Fin 7 → EuclideanSpace ℝ (Fin 2),
    (∀ i j k, i ≠ j → i ≠ k → j ≠ k → ¬ Collinear ℝ {P i, P j, P k}) ∧
    (∀ i j k l, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      ¬ EuclideanGeometry.Cospherical {P i, P j, P k, P l}) ∧
    ∀ i j, ∃ d : ℕ, dist (P i) (P j) = d

/--
Resolved true: Kreisel and Kurz found seven points in the plane with all pairwise distances
integral, no three on a line and no four on a circle. Source: D. Eppstein, The Geometry Junkyard:
Open Problems, Integer distances, https://ics.uci.edu/~eppstein/junkyard/open.html; resolution: T.
Kreisel and S. Kurz, There are integral heptagons, no three points on a line, no four on a circle,
Discrete Comput. Geom. 39 (2008), 786-790, DOI 10.1007/s00454-007-9038-6, arXiv:0804.1303, main
result: two explicit seven-point sets in the plane with integral distances, no three on a line and
no four on a circle (exhaustive search; minimum diameter 22270), https://arxiv.org/abs/0804.1303.
-/
public theorem_wanted integralHeptagonInGeneralPosition_holds : integralHeptagonInGeneralPosition

end MathlibExt.Geometry.IntegralHeptagonGeneralPositionAMR38Problem0008Wanted
