/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.FieldTheory.IntermediateField.AdjoinSimpleConstantsSpan

@[expose] public section

-- exactSource consumer: the original binders apply verbatim.
private theorem exactSource {K : Type*} [Field K] [Algebra ℂ K]
    (F : IntermediateField ℚ ℂ) (B S : Set K) (hBS : B ⊆ S) (c : ℂ)
    (hc : IsAlgebraic ↥F c) (y : K)
    (hyS : y ∈ Subfield.closure
      (⇑(algebraMap ℂ K) '' (IntermediateField.adjoin ↥F {c} : Set ℂ) ∪ S))
    (hyB : IsIntegral ↥(Subring.closure
      (⇑(algebraMap ℂ K) '' (IntermediateField.adjoin ↥F {c} : Set ℂ) ∪ B)) y) :
    y ∈ Submodule.span ℂ {z : K | z ∈ Subfield.closure
      (⇑(algebraMap ℂ K) '' (F : Set ℂ) ∪ S) ∧
      IsIntegral ↥(Subring.closure (⇑(algebraMap ℂ K) '' (F : Set ℂ) ∪ B)) z} :=
  IsIntegral.mem_span_of_adjoin_simple_constants F B S hBS c hc y hyS hyB

-- Concrete instance over `ℂ` itself: `0` satisfies both hypotheses for
-- every choice of the remaining data, and lies in every span.
example (F : IntermediateField ℚ ℂ) (B S : Set ℂ) (hBS : B ⊆ S) (c : ℂ)
    (hc : IsAlgebraic ↥F c) :
    (0 : ℂ) ∈ Submodule.span ℂ {z : ℂ | z ∈ Subfield.closure
      (⇑(algebraMap ℂ ℂ) '' (F : Set ℂ) ∪ S) ∧
      IsIntegral ↥(Subring.closure (⇑(algebraMap ℂ ℂ) '' (F : Set ℂ) ∪ B)) z} :=
  exactSource F B S hBS c hc 0 (Subfield.zero_mem _) isIntegral_zero

-- An element already in the generating set lies in the span, with no
-- appeal to the algebraic-extension step.
example {K : Type*} [Field K] [Algebra ℂ K] (F : IntermediateField ℚ ℂ)
    (B S : Set K) {z : K}
    (hz : z ∈ Subfield.closure (⇑(algebraMap ℂ K) '' (F : Set ℂ) ∪ S))
    (hzi : IsIntegral ↥(Subring.closure
      (⇑(algebraMap ℂ K) '' (F : Set ℂ) ∪ B)) z) :
    z ∈ Submodule.span ℂ {w : K | w ∈ Subfield.closure
      (⇑(algebraMap ℂ K) '' (F : Set ℂ) ∪ S) ∧
      IsIntegral ↥(Subring.closure (⇑(algebraMap ℂ K) '' (F : Set ℂ) ∪ B)) w} :=
  Submodule.subset_span ⟨hz, hzi⟩
