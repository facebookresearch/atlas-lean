/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyCategory

/-!
# Detection of weak equivalences in a localization

These clients detect weak equivalences without any endpoint restrictions,
using both an arbitrary chosen localization and the canonical one.
-/

open CategoryTheory HomotopicalAlgebra MorphismProperty

variable {C : Type*} [Category* C] [ModelCategory C] {X Y Z : C}

example {H : Type*} [Category* H] (L : C ⥤ H) [L.IsLocalization (weakEquivalences C)]
    (f : X ⟶ Y) (g : Y ⟶ Z) [WeakEquivalence g] [IsIso (L.map (f ≫ g))] :
    WeakEquivalence f := by
  have : WeakEquivalence (f ≫ g) := (weakEquivalence_iff _).mpr
    ((weakEquivalence_iff_isIso_map_of_isLocalization L (f ≫ g)).mpr inferInstance)
  exact weakEquivalence_of_postcomp f g

example (f : X ⟶ Y) (g : (weakEquivalences C).Q.obj Y ⟶ (weakEquivalences C).Q.obj X)
    (hfg : (weakEquivalences C).Q.map f ≫ g = 𝟙 _)
    (hgf : g ≫ (weakEquivalences C).Q.map f = 𝟙 _) :
    weakEquivalences C f :=
  (weakEquivalence_iff_isIso_map_of_isLocalization (weakEquivalences C).Q f).mpr
    ⟨⟨g, hfg, hgf⟩⟩
