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
  pressure;
* the circulatory pilot: the neutral and growing witnesses at given times, the loaded stiffness
  at `q = 2` (not symmetric, no static divergence), and the stable, neutral and unstable
  witnesses together.
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

/-! ## B. The circulatory pilot -/

open Filter Matrix

-- The witnesses at given times: the neutral trajectory starts at `(1, 0)` and solves the model
-- at `q = 2`; the growing trajectory solves it at `q = 8` and has Euclidean norm `e` at `t = 1`.
example :
    neutralMode 0 = ![1, 0] ∧ circulatoryResidual 2 neutralMode 0 = 0 ∧
      circulatoryResidual 8 growingMode 1 = 0 ∧
      √(growingMode 1 ⬝ᵥ growingMode 1) = Real.exp 1 := by
  refine ⟨?_, neutralMode_solves 0, growingMode_solves 1, growingMode_norm 1⟩
  ext i
  fin_cases i <;> simp [neutralMode]

-- The loaded stiffness at `q = 2` is `[[1, 2], [-2, 1]]`: not symmetric, and the static balance
-- `(1 - 2 J) v = 0` has only `v = 0`, so the instability at `q = 8` is not static divergence.
example :
    (1 - (2 : ℝ) • circulatoryJ) 0 1 = 2 ∧ (1 - (2 : ℝ) • circulatoryJ) 1 0 = -2 ∧
      ¬ (1 - (2 : ℝ) • circulatoryJ).IsSymm ∧
      ∀ v : Fin 2 → ℝ, (1 - (2 : ℝ) • circulatoryJ) *ᵥ v = 0 → v = 0 := by
  refine ⟨?_, ?_, (loadedStiffness_not_isSymm two_ne_zero).1,
    fun v h => (loadedStiffness_mulVec_eq_zero_iff 2 v).mp h⟩
  · simp [circulatoryJ]
  · simp [circulatoryJ]

-- Stable, neutral and unstable: decay of every `C²` solution at `q = 0`, constant norm `1` at
-- `q = 2`, unbounded norm at `q = 8`.
example :
    (∀ z : ℝ → Fin 2 → ℝ, ContDiff ℝ 2 z → (∀ t, circulatoryResidual 0 z t = 0) →
        Tendsto z atTop (nhds 0)) ∧
      √(neutralMode 5 ⬝ᵥ neutralMode 5) = 1 ∧
      Tendsto (fun t => √(growingMode t ⬝ᵥ growingMode t)) atTop atTop :=
  ⟨circulatory_witnesses.1, (circulatory_witnesses.2.1 5).2, circulatory_witnesses.2.2.2⟩

end PhyslibExtTest.Elasticity.AeroelasticModels

end
