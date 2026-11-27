/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.UBlockFactor

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.UBlockFactor`

* `ubfSplit` evaluates coordinatewise on an explicit vector in `Fin 2 → ℝ`;
* `ubf_pi_block_split`: the cube on `Fin 2` splits as head × tail at `t = 1`;
* `ubf_integral_factor` applied to constant functions;
* the head measure is a probability measure.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.UBlockFactor

open MeasureTheory _root_.StatMech _root_.StatMech.OSSS _root_.StatMech.OSSS.AdaptDisintegration

-- The head part of `![3, 5]` at `t = 1` reads off coordinate `0`.
example : ((ubfSplit 2 1) ![3, 5]).1 ⟨0, by norm_num⟩ = 3 := rfl

-- The tail part of `![3, 5]` at `t = 1` reads off coordinate `1`.
example : ((ubfSplit 2 1) ![3, 5]).2 ⟨1, by norm_num⟩ = 5 := rfl

-- The cube on two coordinates splits as head × tail.
example : MeasurePreserving (ubfSplit 2 1) (StatMech.Probability.cube 2)
    ((ubfHead 2 1).prod (ubfTail 2 1)) :=
  ubf_pi_block_split 2 1

-- Integrals of bounded measurable products factor (constant instance).
example :
    (∫ U, (fun _ => (1 : ℝ)) (((ubfSplit 2 1) U).1) * (fun _ => (2 : ℝ)) U
        ∂(StatMech.Probability.cube 2))
      = ∫ A, (fun _ => (1 : ℝ)) A *
          (∫ B, (fun _ => (2 : ℝ)) ((ubfSplit 2 1).symm (A, B)) ∂(ubfTail 2 1))
            ∂(ubfHead 2 1) :=
  ubf_integral_factor 2 1 measurable_const (Ch := 1) (fun _ => by norm_num)
    measurable_const (CF := 2) (fun _ => by norm_num)

-- The head measure has total mass one.
example : IsProbabilityMeasure (ubfHead 3 2) := inferInstance

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.UBlockFactor
