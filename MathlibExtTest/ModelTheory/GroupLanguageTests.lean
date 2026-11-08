/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Tests for the first-order language of groups in MathlibExt.
-/
module

public import MathlibExt.ModelTheory.GroupLanguage

@[expose] public section

namespace MathlibExtTest.ModelTheory.GroupLanguageTests

open FirstOrder.Language

/-- The function-symbol lemma applies. -/
example (n : ℕ) : groupLanguage.Functions n = GroupFunction n :=
  groupLanguage_functions n

/-- The relation-symbol lemma applies. -/
example (n : ℕ) : groupLanguage.Relations n = Empty :=
  groupLanguage_relations n

/-- The multiplication lemma applies. -/
example (G : Type) [Group G] (x : Fin 2 → G) :
    (groupLanguageStructure G).funMap GroupFunction.mul x = x 0 * x 1 :=
  groupLanguageStructure_mul G x

/-- The inversion lemma applies. -/
example (G : Type) [Group G] (x : Fin 1 → G) :
    (groupLanguageStructure G).funMap GroupFunction.inv x = (x 0)⁻¹ :=
  groupLanguageStructure_inv G x

/-- The unit lemma applies. -/
example (G : Type) [Group G] (x : Fin 0 → G) :
    (groupLanguageStructure G).funMap GroupFunction.one x = 1 :=
  groupLanguageStructure_one G x

end MathlibExtTest.ModelTheory.GroupLanguageTests
