/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.Topology.Algebra.Star.Unitary
public import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Local compactness of classical matrix groups

The standard finite-Pi instances make the ambient finite-index matrix spaces
locally compact.  Closedness of the unitary locus then gives the corresponding
instances for rank-`n` complex unitary and real orthogonal groups.
-/

@[expose] public section

noncomputable section

namespace Matrix

/-- The rank-`n` complex unitary group is locally compact in its induced
topology. -/
instance unitaryGroupLocallyCompactSpace (n : ℕ) :
    LocallyCompactSpace (unitaryGroup (Fin n) ℂ) := by
  exact @IsClosed.locallyCompactSpace
    (Matrix (Fin n) (Fin n) ℂ) inferInstance
    (inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))) _
    (isClosed_unitary (R := Matrix (Fin n) (Fin n) ℂ))

/-- The rank-`n` real orthogonal group is locally compact in its induced
topology. -/
instance orthogonalGroupLocallyCompactSpace (n : ℕ) :
    LocallyCompactSpace (orthogonalGroup (Fin n) ℝ) := by
  exact @IsClosed.locallyCompactSpace
    (Matrix (Fin n) (Fin n) ℝ) inferInstance
    (inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℝ))) _
    (isClosed_unitary (R := Matrix (Fin n) (Fin n) ℝ))

end Matrix

end
