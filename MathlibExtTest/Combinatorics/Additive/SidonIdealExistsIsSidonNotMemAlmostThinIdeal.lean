/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.SidonIdealExistsIsSidonNotMemAlmostThinIdeal

/-! # Tests for a Sidon set outside the almost thin ideal -/

namespace MathlibExtTest.Combinatorics.Additive.SidonIdealExistsIsSidonNotMemAlmostThinIdeal

open MetaMathlibExt

/-- The proved statement keeps its pinned form. -/
example : ∃ A : Set ℕ, A.IsSidon ∧ A ∉ generatedIdeal IsAlmostThinSet :=
  exists_isSidon_not_mem_almostThinIdeal

/-- The witness lies in the Sidon ideal but outside the almost thin ideal,
so the two ideals differ. -/
example : ∃ A : Set ℕ, A ∈ sidonIdeal ∧ A ∉ generatedIdeal IsAlmostThinSet := by
  obtain ⟨A, hSidon, hNotMem⟩ := exists_isSidon_not_mem_almostThinIdeal
  exact ⟨A, mem_generatedIdeal hSidon, hNotMem⟩

/-- The almost thin ideal is strictly contained in the Sidon ideal. -/
example : generatedIdeal IsAlmostThinSet ⊂ sidonIdeal := by
  refine ⟨almostThinIdeal_subset_sidonIdeal, fun h => ?_⟩
  obtain ⟨A, hSidon, hNotMem⟩ := exists_isSidon_not_mem_almostThinIdeal
  exact hNotMem (h (mem_generatedIdeal hSidon))

end MathlibExtTest.Combinatorics.Additive.SidonIdealExistsIsSidonNotMemAlmostThinIdeal
