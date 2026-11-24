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

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule

/-!
# Closed subspaces of Lp supported on a measurable set

The carrier is the literal almost everywhere vanishing condition off the
set. Closedness follows from the kernel of the actual restriction map to
its complement. No completeness or finite-measure hypothesis is needed.
-/

@[expose] public section
noncomputable section
open Filter MeasureTheory Set
open scoped ENNReal
namespace MathlibExt.MeasureTheory.Function

universe u v w
variable {X : Type u} [MeasurableSpace X]
variable {𝕜 : Type v} [NormedField 𝕜]
variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual Lp subspace of functions that vanish almost everywhere off a set. -/
def Lp.supportedOn (mu : Measure X) (s : Set X) : Submodule 𝕜 (Lp E p mu) where
  carrier := {f | ∀ᵐ x ∂mu, x ∉ s → f x = 0}
  zero_mem' := by
    filter_upwards [MeasureTheory.Lp.coeFn_zero E p mu] with x hx
    intro _
    exact hx
  add_mem' := by
    intro f g hf hg
    filter_upwards [hf, hg, MeasureTheory.Lp.coeFn_add f g] with x hfx hgx hadd
    intro hx
    exact hadd.trans (by rw [Pi.add_apply, hfx hx, hgx hx, add_zero])
  smul_mem' := by
    intro c f hf
    filter_upwards [hf, MeasureTheory.Lp.coeFn_smul c f] with x hfx hsmul
    intro hx
    exact hsmul.trans (by rw [Pi.smul_apply, hfx hx, smul_zero])

omit [Fact (1 ≤ p)] in
/-- The defining support condition retains the original ambient almost everywhere measure.
This equivalence holds for every exponent `p : ℝ≥0∞`. -/
theorem Lp.mem_supportedOn (mu : Measure X) (s : Set X) (f : Lp E p mu) :
    f ∈ Lp.supportedOn (𝕜 := 𝕜) mu s ↔ ∀ᵐ x ∂mu, x ∉ s → f x = 0 := Iff.rfl

/-- Almost everywhere support is exactly zero under the actual complement restriction map. -/
theorem Lp.supportedOn_eq_ker_restrict (mu : Measure X) (s : Set X) (hs : MeasurableSet s) :
    Lp.supportedOn (𝕜 := 𝕜) (E := E) (p := p) mu s =
      (LpToLpRestrictCLM X E 𝕜 mu p sᶜ).ker := by
  apply Submodule.ext
  intro f
  change (∀ᵐ x ∂mu, x ∉ s → f x = 0) ↔ LpToLpRestrictCLM X E 𝕜 mu p sᶜ f = 0
  rw [MeasureTheory.Lp.eq_zero_iff_ae_eq_zero]
  have hrep := LpToLpRestrictCLM_coeFn 𝕜 sᶜ f
  constructor
  · intro hf
    have hf' : f =ᵐ[mu.restrict sᶜ] 0 := (ae_restrict_iff' hs.compl).2 hf
    exact hrep.trans hf'
  · intro hf
    have hf' : f =ᵐ[mu.restrict sᶜ] 0 := hrep.symm.trans hf
    exact (ae_restrict_iff' hs.compl).1 hf'

/-- Support on a measurable set is a closed Lp subspace, proved by its actual restriction kernel. -/
theorem Lp.isClosed_supportedOn (mu : Measure X) (s : Set X) (hs : MeasurableSet s) :
    IsClosed (Lp.supportedOn (𝕜 := 𝕜) (E := E) (p := p) mu s : Set (Lp E p mu)) := by
  rw [Lp.supportedOn_eq_ker_restrict mu s hs]
  exact (LpToLpRestrictCLM X E 𝕜 mu p sᶜ).isClosed_ker

/-- The actual closed support subspace, with the literal almost everywhere carrier. -/
def Lp.closedSupportedOn (mu : Measure X) (s : Set X) (hs : MeasurableSet s) :
    ClosedSubmodule 𝕜 (Lp E p mu) :=
  ⟨Lp.supportedOn mu s, Lp.isClosed_supportedOn mu s hs⟩

/-- Values of the closed support space still satisfy the original vanishing condition. -/
theorem Lp.mem_closedSupportedOn (mu : Measure X) (s : Set X) (hs : MeasurableSet s)
    (f : Lp E p mu) :
    f ∈ Lp.closedSupportedOn (𝕜 := 𝕜) mu s hs ↔ ∀ᵐ x ∂mu, x ∉ s → f x = 0 := Iff.rfl

end MathlibExt.MeasureTheory.Function
