/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.LocalTests
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.RawMappingWeakDetector

/-!
# Original local Whitehead and empty-family weak equivalences

Both local-fibrant endpoints provide the original raw tests. The actual weak
replacement units transport these tests to the public two-target detector.
For an empty original family, its full all-fibrant-target test is precisely
the actual base weak class, with no fibrancy requirement on the tested map.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u v w i

open CategoryTheory HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen
attribute [local instance] SimplicialPresheaf.InjectiveKan.modelCategory

namespace SimplicialPresheaf.InjectiveKan

variable {D : Type w} [Category.{v} D] [Small.{u} D] [LocallySmall.{u} D]
  {I : Type i}

/-- Between two actual original local-fibrant objects, the local weak test is
exactly the actual injective base weak class on the same original arrow. -/
theorem originalLocalEquivalence_iff_weakEquivalence_of_localFibrant
    (S : I → Arrow (SimplicialPresheaf.{u} D))
    {A B : SimplicialPresheaf.{u} D} (f : A ⟶ B)
    (hA : isOriginalLocalFibrant S A) (hB : isOriginalLocalFibrant S B) :
    originalLocalEquivalences S f ↔
      weakEquivalences (SimplicialPresheaf.{u} D) f := by
  constructor
  · intro hf
    have hRA := (rawPrecomp_weak_iff_of_targetWeak f ((originalRUnit D).app A)
      (originalRUnit_trivialCofibration A).2 hA.1 (originalR_isFibrant A)).mp
      (hf A hA)
    have hRB := (rawPrecomp_weak_iff_of_targetWeak f ((originalRUnit D).app B)
      (originalRUnit_trivialCofibration B).2 hB.1 (originalR_isFibrant B)).mp
      (hf B hB)
    exact (weakEquivalence_iff_rawPrecomp_twoReplacementTargets f).mpr ⟨hRA, hRB⟩
  · intro hf
    exact weakEquivalences_le_originalLocalEquivalences S f hf

/-- An empty original family has the actual base weak class on every original
arrow, without requiring either endpoint to be fibrant. -/
theorem originalLocalEquivalences_eq_weakEquivalences_of_isEmpty
    [IsEmpty I] (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    originalLocalEquivalences S =
      weakEquivalences (SimplicialPresheaf.{u} D) := by
  ext A B f
  exact (originalLocalEquivalences_iff_of_isEmpty S f).trans
    (weakEquivalence_iff_rawPrecomp_all_fibrant f).symm

end SimplicialPresheaf.InjectiveKan
