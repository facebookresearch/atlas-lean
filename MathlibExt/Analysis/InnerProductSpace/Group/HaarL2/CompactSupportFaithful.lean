/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.InnerProductSpace.Group.HaarL2.CompactSupport
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Faithful compact-support inclusion for an open-positive regular measure

The actual compact-support inclusion retains its original almost-everywhere
vector values. Open positivity and continuity then recover every original
pointwise value, so that inclusion is injective. No global finite measure,
countability, separability or sigma-finiteness is assumed.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open scoped CompactlySupported

namespace MeasureTheory.HaarL2

noncomputable section

universe uG uH

variable {G : Type uG} [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (μ : Measure G) [μ.Regular] [μ.IsOpenPosMeasure]

/-- Let `G` be a topological space with its Borel σ-algebra, let `μ` be a regular measure on `G`,
and let `H` be a complex normed inner-product space. Assume `μ` is positive on every nonempty
open set.

Open positivity recovers every compact-support vector from its L2 image. -/
theorem injective_compactSupportInclusion :
    Function.Injective (compactSupportInclusion (H := H) μ) := by
  intro f g hfg
  have hf := compactSupportInclusion_ae_eq μ f
  have hg := compactSupportInclusion_ae_eq μ g
  rw [hfg] at hf
  have hPointwise : (f : G → H) = (g : G → H) :=
    (f.continuous.ae_eq_iff_eq μ g.continuous).mp (hf.symm.trans hg)
  apply CompactlySupportedContinuousMap.ext
  intro s
  exact congrFun hPointwise s

end

end MeasureTheory.HaarL2
