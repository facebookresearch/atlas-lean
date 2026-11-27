/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Dynamics.Ergodic.Conservative

/-!
# Poincaré recurrence theorem

The classical statement for maps preserving a finite measure: almost every point of a
measurable set `E` returns to `E` infinitely often. Pinned Mathlib proves the more general
statement for conservative maps (`MeasureTheory.Conservative.ae_mem_imp_frequently_image_mem`)
and that a map preserving a finite measure is conservative
(`MeasureTheory.MeasurePreserving.conservative`); this module records their composition in the
form in which the theorem is taught, so that the graph has a node for it.

## References

* O. Sarig, *Lecture Notes on Ergodic Theory*, Theorem 1.1,
  https://www.weizmann.ac.il/math/sarigo/sites/math.sarigo/files/uploads/ergodicnotes.pdf
-/

@[expose] public section

namespace MathlibExt.Dynamics.Ergodic.PoincareRecurrence

open MeasureTheory Filter

variable {α : Type*} [MeasurableSpace α] {T : α → α} {μ : Measure α}

/-- **Poincaré recurrence theorem.** Let `T` preserve a finite measure `μ` and let `E` be
measurable. Then for `μ`-almost every `x ∈ E` there are infinitely many `n` with `T^[n] x ∈ E`
(O. Sarig, *Lecture Notes on Ergodic Theory*, Theorem 1.1, stated there for probability
preserving transformations). This is Mathlib's `Conservative.ae_mem_imp_frequently_image_mem`
applied to `MeasurePreserving.conservative`. -/
theorem ae_frequently_mem_of_mem [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ)
    {E : Set α} (hE : MeasurableSet E) :
    ∀ᵐ x ∂μ, x ∈ E → ∃ᶠ n in atTop, T^[n] x ∈ E :=
  hT.conservative.ae_mem_imp_frequently_image_mem hE.nullMeasurableSet

end MathlibExt.Dynamics.Ergodic.PoincareRecurrence
