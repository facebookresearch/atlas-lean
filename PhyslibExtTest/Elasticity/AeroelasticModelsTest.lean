/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Elasticity.AeroelasticModels
import Mathlib.Tactic.NormNum

/-!
# Tests for `PhyslibExt.Elasticity.AeroelasticModels`

* a positive aerodynamic factor: the divergence pressure, a nonzero neutral twist there, and
  the effective stiffness below it;
* a zero aerodynamic factor: the division formula gives `0`, which is not a divergence
  pressure.
-/

@[expose] public section

namespace PhyslibExtTest.Elasticity.AeroelasticModels

open _root_.Elasticity.AeroelasticModels

/-! ## A. Fixtures -/

-- Positive coupling: `K = 5000`, `S = 2`, `e = 1/10`, `CLα = 5` give `qD = 5000`; the
-- nonzero twist `θ = 1/20` is a neutral displacement there, and at `q = 4000` the effective
-- stiffness is `1000`.
example :
    divergencePressure 5000 2 (1 / 10) 5 = 5000 ∧
      restoringMoment 5000 5000 2 (1 / 10) 5 0 (1 / 20) = 0 ∧
      effectiveStiffness 5000 4000 2 (1 / 10) 5 = 1000 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold divergencePressure
    norm_num
  · unfold restoringMoment aeroMoment
    norm_num
  · unfold effectiveStiffness
    norm_num

-- Zero coupling, aerodynamic centre on the elastic axis (`e = 0`): the division formula
-- gives `0`, while the effective stiffness at that pressure is `K = 5000`, not `0`.
example :
    divergencePressure 5000 2 0 5 = 0 ∧
      effectiveStiffness 5000 (divergencePressure 5000 2 0 5) 2 0 5 = 5000 := by
  constructor
  · unfold divergencePressure
    norm_num
  · unfold effectiveStiffness divergencePressure
    norm_num

end PhyslibExtTest.Elasticity.AeroelasticModels

end
