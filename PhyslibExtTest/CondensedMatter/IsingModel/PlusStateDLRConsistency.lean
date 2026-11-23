/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.PlusStateDLRConsistency

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.FVConsistencyProve`

* `plusState_isDLR` applies with no hypotheses: the plus state on `ℤ²` is a DLR state
  at `β = 1/2` with zero field, at negative `β` (antiferromagnet) and at
  negative field, so the predicate `IsDLRState` has nontrivial witnesses.
* `fvConsistency_plus`: the finite-volume consistency of the plus box measures holds on `ℤ³`.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.FVConsistencyProve

open MeasureTheory
open _root_.StatMech _root_.StatMech.Ising

-- The plus state on `ℤ²` is a DLR state at `β = 1/2`, `h = 0`.
example : IsDLRState 2 (1 / 2) 0 (plusState 2 (1 / 2) 0 : Measure (ConfigSpace (Lattice.Site 2))) :=
  plusState_isDLR (1 / 2) 0

-- It is also a DLR state for the antiferromagnet with a negative field.
example : IsDLRState 2 (-1) (-1) (plusState 2 (-1) (-1) : Measure (ConfigSpace (Lattice.Site 2))) :=
  plusState_isDLR (-1) (-1)

-- The finite-volume consistency behind the DLR property, on `ℤ³`.
example (β h : ℝ) : FVConsistency 3 β h :=
  fvConsistency_plus β h

end PhyslibExtTest.CondensedMatter.IsingModel.FVConsistencyProve
