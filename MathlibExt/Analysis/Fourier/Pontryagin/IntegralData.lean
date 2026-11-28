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

public import MathlibExt.Analysis.Fourier.PontryaginDualIntegral
public import MathlibExt.Analysis.InnerProductSpace.Group.HaarL2.CompactSupport
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Integrable compact-support character Fourier kernels

Let `G` be a group with Borel topology and Haar measure `μ`. For `f∈C_c(G,ℂ)` and continuous
circle-valued character `χ`, the function `s ↦ conj(χ(s)) f(s)` is integrable against `μ`.

This uses unit character modulus and compact support. Commutativity, local compactness,
continuity of group operations and regularity of the measure are not extra hypotheses of this
integrability lemma. No Fourier isometry or dual Haar normalization is asserted.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter
open scoped CompactlySupported

namespace PontryaginDual

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable (mu : Measure G) [mu.IsHaarMeasure] [mu.Regular]

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [mu.Regular] in
/-- **Integrability of a compact-support character Fourier kernel.** Let `G` be a group with
its Borel topological structure and `μ` a Haar measure. For `f∈C_c(G,ℂ)` and continuous
character `χ∈PontryaginDual G`, `s ↦ conj(χ(s)) f(s)` is integrable. No group-operation
continuity, local compactness, regularity of `μ` or abelian hypothesis is required. -/
theorem integrable_haarFourierKernel (f : C_c(G, ℂ)) (chi : PontryaginDual G) :
    Integrable (fun s : G => star (chi s : ℂ) * f s) mu := by
  have hcontinuous : Continuous (fun s : G => star (chi s : ℂ) * f s) :=
    (continuous_subtype_val.comp (map_continuous chi)).star.mul (map_continuous f)
  have hcompact : HasCompactSupport (fun s : G => star (chi s : ℂ) * f s) :=
    HasCompactSupport.intro' f.hasCompactSupport (isClosed_tsupport f) (fun s hs => by
      rw [image_eq_zero_of_notMem_tsupport hs, mul_zero])
  exact hcontinuous.integrable_of_hasCompactSupport hcompact

end PontryaginDual
