/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyFunctionComplex

/-!
# Strict-to-derived simplicial mapping objects

This file compares the strict simplicial mapping bifunctor with the chosen
derived mapping bifunctor. The component first postcomposes with fibrant
replacement and then precomposes with cofibrant replacement.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory CategoryTheory.MorphismProperty

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [SimplicialCategory C]
  [HasFunctorialFactorization (cofibrations C) (trivialFibrations C)]
  [HasFunctorialFactorization (trivialCofibrations C) (fibrations C)]

set_option backward.isDefEq.respectTransparency false

/-- The canonical comparison from the strict simplicial mapping bifunctor to
the chosen derived mapping bifunctor. -/
noncomputable def strictToDerivedMappingObject :
    SimplicialCategory.sHomFunctor C ⟶ derivedMappingObject (C := C) where
  app X :=
    { app := fun Y ↦
        eHomWhiskerLeft SSet X.unop
            ((fibrantReplacementUnit (C := C)).app Y) ≫
          eHomWhiskerRight SSet
            ((cofibrantReplacementCounit (C := C)).app X.unop)
            ((fibrantReplacement (C := C)).obj Y)
      naturality := by
        intro Y Z g
        change eHomWhiskerLeft SSet X.unop g ≫
            (eHomWhiskerLeft SSet X.unop
                ((fibrantReplacementUnit (C := C)).app Z) ≫
              eHomWhiskerRight SSet
                ((cofibrantReplacementCounit (C := C)).app X.unop)
                ((fibrantReplacement (C := C)).obj Z)) =
          (eHomWhiskerLeft SSet X.unop
                ((fibrantReplacementUnit (C := C)).app Y) ≫
              eHomWhiskerRight SSet
                ((cofibrantReplacementCounit (C := C)).app X.unop)
                ((fibrantReplacement (C := C)).obj Y)) ≫
            eHomWhiskerLeft SSet
              ((cofibrantReplacement (C := C)).obj X.unop)
              ((fibrantReplacement (C := C)).map g)
        have hη := (fibrantReplacementUnit (C := C)).naturality g
        simp only [Functor.id_obj, Functor.id_map] at hη
        rw [← eHomWhiskerLeft_comp_assoc,
          hη]
        rw [eHomWhiskerLeft_comp_assoc, eHom_whisker_exchange]
        simp only [Category.assoc] }
  naturality := by
    intro X Y f
    apply NatTrans.ext
    funext Z
    change eHomWhiskerRight SSet f.unop Z ≫
          (eHomWhiskerLeft SSet Y.unop
                ((fibrantReplacementUnit (C := C)).app Z) ≫
            eHomWhiskerRight SSet
              ((cofibrantReplacementCounit (C := C)).app Y.unop)
              ((fibrantReplacement (C := C)).obj Z)) =
      (eHomWhiskerLeft SSet X.unop
              ((fibrantReplacementUnit (C := C)).app Z) ≫
          eHomWhiskerRight SSet
            ((cofibrantReplacementCounit (C := C)).app X.unop)
            ((fibrantReplacement (C := C)).obj Z)) ≫
        eHomWhiskerRight SSet
          ((cofibrantReplacement (C := C)).map f.unop)
          ((fibrantReplacement (C := C)).obj Z)
    simp only [Category.assoc]
    rw [← eHom_whisker_exchange_assoc]
    slice_lhs 2 3 => rw [← eHomWhiskerRight_comp]
    slice_rhs 2 3 => rw [← eHomWhiskerRight_comp]
    have hε := (cofibrantReplacementCounit (C := C)).naturality f.unop
    simp only [Functor.id_obj, Functor.id_map] at hε
    rw [hε]

/-- Component formula for the strict-to-derived mapping comparison. -/
theorem strictToDerivedMappingObject_app (X Y : C) :
    ((strictToDerivedMappingObject (C := C)).app (.op X)).app Y =
      eHomWhiskerLeft SSet X
          ((fibrantReplacementUnit (C := C)).app Y) ≫
        eHomWhiskerRight SSet
          ((cofibrantReplacementCounit (C := C)).app X)
          ((fibrantReplacement (C := C)).obj Y) :=
  by
    simp only [strictToDerivedMappingObject]

/-- On a cofibrant source and fibrant target, the strict-to-derived
comparison component is a realization weak equivalence. -/
theorem strictToDerivedMappingObject_app_mem_realizationWeakEquivalences
    (data : HomotopyFunctionComplexInvarianceData (C := C))
    (X Y : C) [IsCofibrant X] [IsFibrant Y] :
    SSet.realizationWeakEquivalences
      (((strictToDerivedMappingObject (C := C)).app (.op X)).app Y) := by
  let hX : IsCofibrant X := inferInstance
  let hY : IsFibrant Y := inferInstance
  let hQX : IsCofibrant ((cofibrantReplacement (C := C)).obj X) :=
    inferInstance
  let hRY : IsFibrant ((fibrantReplacement (C := C)).obj Y) :=
    inferInstance
  rw [strictToDerivedMappingObject_app]
  apply SSet.realizationWeakEquivalences.comp_mem
  · exact data.postcompWeakOfWeakEquivalence X hX
        ((fibrantReplacementUnit (C := C)).app Y)
        (by simpa only [Functor.id_obj] using hY) hRY
        (mem_weakEquivalences _)
  · exact data.precompWeakOfWeakEquivalence
        ((cofibrantReplacementCounit (C := C)).app X)
        hQX (by simpa only [Functor.id_obj] using hX)
        (mem_weakEquivalences _)
        ((fibrantReplacement (C := C)).obj Y) hRY

end HomotopicalAlgebra
