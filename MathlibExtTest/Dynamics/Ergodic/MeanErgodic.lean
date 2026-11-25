/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Dynamics.Ergodic.MeanErgodic

import Mathlib.Tactic

@[expose] public section

open MeasureTheory Filter Topology
open MathlibExt.Dynamics.Ergodic.MeanErgodic

namespace MathlibExtTest.Dynamics.Ergodic.MeanErgodic

-- The Koopman operator of the identity fixes every `L²` function.
example {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : Lp ℝ 2 μ) :
    koopman (MeasurePreserving.id μ) f = f := by
  ext1
  filter_upwards [koopman_apply_ae_eq (MeasurePreserving.id μ) f] with x hx
  simpa using hx

-- Mean ergodic theorem: the ergodic averages converge in `L²`.
example {α : Type*} [MeasurableSpace α] {μ : Measure α} {T : α → α}
    (hT : MeasurePreserving T μ μ) (f : Lp ℝ 2 μ) :
    ∃ g : Lp ℝ 2 μ, Tendsto (fun N => birkhoffAverage ℝ (koopman hT) _root_.id N f) atTop (𝓝 g) :=
  ⟨_, tendsto_birkhoffAverage_koopman hT f⟩

end MathlibExtTest.Dynamics.Ergodic.MeanErgodic
