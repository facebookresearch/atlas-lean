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
# Supported Lp subspaces and complement-restriction kernels

For a normed scalar field and normed vector space, define support on `s` by the condition that
an `Lp` function vanishes almost everywhere outside `s`. This gives a linear subspace for any
exponent `p∈[0,∞]`.

For `p≥1` and measurable `s`, this subspace is the kernel of restriction to `sᶜ`, hence is
closed. The coefficient space need not be complete, and the measure need not be finite.
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

/-- **Lp submodule of almost-everywhere supported functions.** Let `X` be measurable, `μ` any
measure, `𝕜` a normed field and `E` a normed `𝕜`-space. for any exponent `p∈[0,∞]` and set
`s⊆X`, `Lp.supportedOn μ s={f∈Lp E p μ : f(x)=0 almost everywhere outside s}`.
Measurability of `s` is not required for the carrier. -/
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
/-- **Membership in an almost-everywhere supported Lp subspace.** Let `X` be measurable, `μ`
any measure, `𝕜` a normed field and `E` a normed `𝕜`-space. for any exponent `p∈[0,∞]`,
`f∈Lp.supportedOn μ s` exactly when `f(x)=0` for `μ`-almost every `x` outside `s`. -/
theorem Lp.mem_supportedOn (mu : Measure X) (s : Set X) (f : Lp E p mu) :
    f ∈ Lp.supportedOn (𝕜 := 𝕜) mu s ↔ ∀ᵐ x ∂mu, x ∉ s → f x = 0 := Iff.rfl

/-- **Supported Lp subspace as a complement-restriction kernel.** Let `X` be measurable, `μ`
any measure, `𝕜` a normed field and `E` a normed `𝕜`-space. if `p≥1` and `s` is
measurable, `Lp.supportedOn μ s` equals the kernel of the bounded restriction map to `sᶜ`,
with measure `μ.restrict sᶜ`. -/
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

/-- **Norm-closed support subspace for a measurable set.** Let `X` be measurable, `μ` any
measure, `𝕜` a normed field and `E` a normed `𝕜`-space. if `p≥1` and `s` is measurable,
`Lp.supportedOn μ s` is closed in `Lp E p μ`. No completeness of `E` or finiteness of `μ`
is assumed. -/
theorem Lp.isClosed_supportedOn (mu : Measure X) (s : Set X) (hs : MeasurableSet s) :
    IsClosed (Lp.supportedOn (𝕜 := 𝕜) (E := E) (p := p) mu s : Set (Lp E p mu)) := by
  rw [Lp.supportedOn_eq_ker_restrict mu s hs]
  exact (LpToLpRestrictCLM X E 𝕜 mu p sᶜ).isClosed_ker

/-- **Closed Lp support carrier with its inherited norm.** Let `X` be measurable, `μ` any
measure, `𝕜` a normed field and `E` a normed `𝕜`-space. for `p≥1` and measurable `s`,
`Lp.closedSupportedOn μ s` bundles the submodule of functions vanishing almost everywhere
off `s` as a closed submodule. -/
def Lp.closedSupportedOn (mu : Measure X) (s : Set X) (hs : MeasurableSet s) :
    ClosedSubmodule 𝕜 (Lp E p mu) :=
  ⟨Lp.supportedOn mu s, Lp.isClosed_supportedOn mu s hs⟩

/-- **Values of the closed support carrier.** Let `X` be measurable, `μ` any measure, `𝕜` a
normed field and `E` a normed `𝕜`-space. for `p≥1`, measurable `s` and `f∈Lp E p μ`,
membership in `Lp.closedSupportedOn μ s` is equivalent to almost-everywhere vanishing
outside `s`. -/
theorem Lp.mem_closedSupportedOn (mu : Measure X) (s : Set X) (hs : MeasurableSet s)
    (f : Lp E p mu) :
    f ∈ Lp.closedSupportedOn (𝕜 := 𝕜) mu s hs ↔ ∀ᵐ x ∂mu, x ∉ s → f x = 0 := Iff.rfl

end MathlibExt.MeasureTheory.Function
