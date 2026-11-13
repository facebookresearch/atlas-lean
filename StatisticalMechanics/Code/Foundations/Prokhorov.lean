/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
























import Code.Foundations.WeakConvergence

open MeasureTheory TopologicalSpace Filter Topology

namespace StatMech

variable {E : Type*} [Countable E]










theorem prokhorov_compactSpace :
    CompactSpace (ProbabilityMeasure (ConfigSpace E)) :=
  inferInstance






theorem prokhorov_metrizableSpace :
    MetrizableSpace (ProbabilityMeasure (ConfigSpace E)) :=
  inferInstance




theorem prokhorov_secondCountableTopology :
    SecondCountableTopology (ProbabilityMeasure (ConfigSpace E)) :=
  inferInstance














theorem prokhorov_seq_compact (μ : ℕ → ProbabilityMeasure (ConfigSpace E)) :
    ∃ (ν : ProbabilityMeasure (ConfigSpace E)) (φ : ℕ → ℕ), StrictMono φ ∧
      WeakConvergesTo (μ ∘ φ) ν := by
  obtain ⟨ν, φ, hφ, htends⟩ := CompactSpace.tendsto_subseq μ
  exact ⟨ν, φ, hφ, htends⟩

end StatMech
