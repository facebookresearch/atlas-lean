/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyTesting
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.Types.Basic

/-!
# Two-out-of-three for chosen-cylinder testing equivalences

The actual testing class is the intersection of isomorphism-testing
classes pulled back through its native homotopy-class presheaves.
Opposites preserve the contravariant order. Native isomorphism,
inverse-image and opposite closure supply two-out-of-three targetwise.

The construction requires no model category or fibrancy of the three
objects in a composable pair. It applies to the specified functorial
precylinder and anodyne class in any category with a terminal object.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomotopicalAlgebra.Precylinder

variable {C : Type u} [Category.{v} C] (P : Precylinder (𝟭 C))
  (An : MorphismProperty C) [HasTerminal C]

/-- Testing is the intersection, over every actual naive fibrant target,
of the opposite isomorphism classes detected by its class presheaf. -/
lemma testingEquivalences_eq_iInf_isomorphisms :
    P.testingEquivalences An =
      ⨅ T : {T : C // An.naiveFibrantObjects T},
        ((MorphismProperty.isomorphisms (Type v)).inverseImage
          (P.homotopyClassFunctor T.1)).unop := by
  ext X Y f
  rw [MorphismProperty.iInf_iff]
  change (∀ T : C, An.naiveFibrantObjects T →
      Function.Bijective (P.homotopyClassPrecomp f T)) ↔
    ∀ T : {T : C // An.naiveFibrantObjects T},
      IsIso ((P.homotopyClassFunctor T.1).map f.op)
  constructor
  · intro h T
    exact (CategoryTheory.isIso_iff_bijective _).2 (h T.1 T.2)
  · intro h T hT
    exact (CategoryTheory.isIso_iff_bijective _).1 (h ⟨T, hT⟩)

/-- The actual testing class has all three directions of two-out-of-three. -/
instance testingEquivalences.hasTwoOutOfThreeProperty :
    (P.testingEquivalences An).HasTwoOutOfThreeProperty := by
  rw [P.testingEquivalences_eq_iInf_isomorphisms An]
  refine
    { toIsStableUnderComposition := inferInstance
      of_postcomp := ?_
      of_precomp := ?_ }
  · intro X Y Z f g hg hfg
    rw [MorphismProperty.iInf_iff] at hg hfg ⊢
    intro T
    exact (((MorphismProperty.isomorphisms (Type v)).inverseImage
      (P.homotopyClassFunctor T.1)).unop).of_postcomp f g (hg T) (hfg T)
  · intro X Y Z f g hf hfg
    rw [MorphismProperty.iInf_iff] at hf hfg ⊢
    intro T
    exact (((MorphismProperty.isomorphisms (Type v)).inverseImage
      (P.homotopyClassFunctor T.1)).unop).of_precomp f g (hf T) (hfg T)

end HomotopicalAlgebra.Precylinder
