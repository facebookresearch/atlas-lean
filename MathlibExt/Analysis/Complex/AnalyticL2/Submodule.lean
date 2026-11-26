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

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Analytic representatives in scalar L2

For an arbitrary planar set `G` and measure `μ` on `ℂ`, take those classes
`f ∈ Lp ℂ 2 μ` admitting a globally defined representative `g : ℂ → ℂ`
that is analytic on `G` and equals `f` almost everywhere for the given
measure. These classes form a complex linear submodule, with exactly that
membership criterion. The almost-everywhere equality is for all of `μ`;
restriction to `G` is made only when the chosen measure is itself restricted.
No openness, boundedness, finite measure or nonempty-set hypothesis is used
by this constructor. The norm is inherited from the given L2 space.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory

namespace AnalyticL2

/-- The complex submodule of L2 classes admitting a globally defined representative analytic on `G`
and equal to the class almost everywhere for `μ`. -/
def submodule (G : Set ℂ) (μ : Measure ℂ) : Submodule ℂ (Lp ℂ 2 μ) where
  carrier := {f | ∃ g : ℂ → ℂ, AnalyticOn ℂ g G ∧ ∀ᵐ z ∂μ, f z = g z}
  zero_mem' := by
    refine ⟨fun _ : ℂ => (0 : ℂ), analyticOn_const, ?_⟩
    change (fun z : ℂ => (0 : Lp ℂ 2 μ) z) =ᵐ[μ] fun _ => (0 : ℂ)
    exact Lp.coeFn_zero ℂ 2 μ
  add_mem' := by
    intro f h hf hh
    rcases hf with ⟨g, hg, hfg⟩
    rcases hh with ⟨k, hk, hhk⟩
    refine ⟨g + k, hg.add hk, ?_⟩
    filter_upwards [Lp.coeFn_add f h, hfg, hhk] with z hz hfz hhz
    exact hz.trans (congrArg₂ (fun x y : ℂ => x + y) hfz hhz)
  smul_mem' := by
    intro c f hf
    rcases hf with ⟨g, hg, hfg⟩
    refine ⟨c • g, hg.const_smul, ?_⟩
    filter_upwards [Lp.coeFn_smul c f, hfg] with z hz hfz
    exact hz.trans (congrArg (fun x : ℂ => c • x) hfz)

/-- Membership is precisely existence of an analytic-on-`G` representative with the displayed
almost-everywhere equality for `μ`.

```lean
theorem mem_submodule_iff (G : Set ℂ) (μ : Measure ℂ) (f : Lp ℂ 2 μ) :
    f ∈ submodule G μ ↔ ∃ g : ℂ → ℂ, AnalyticOn ℂ g G ∧ ∀ᵐ z ∂μ, f z = g z
``` -/
theorem mem_submodule_iff (G : Set ℂ) (μ : Measure ℂ) (f : Lp ℂ 2 μ) :
    f ∈ submodule G μ ↔ ∃ g : ℂ → ℂ, AnalyticOn ℂ g G ∧ ∀ᵐ z ∂μ, f z = g z := Iff.rfl

end AnalyticL2

end
