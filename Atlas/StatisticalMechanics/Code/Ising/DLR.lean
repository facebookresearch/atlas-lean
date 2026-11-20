/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


















































import Mathlib
import Code.Foundations.CondDistribution
import Code.Ising.InfiniteVolume

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

set_option linter.style.longLine false

namespace StatMech

namespace Ising

open StatMech.Lattice

variable {d : ℕ}




















def IsDLRState (d : ℕ) (β h : ℝ) (μ : Measure (ConfigSpace (Site d)))
    [IsFiniteMeasure μ] : Prop :=
  ∀ n : ℕ, ∀ᵐ η ∂μ,
    (gibbsConditional μ (box d n)) η = fvMeasure η n (bondFinsetTouch d n) β h

end Ising

end StatMech
