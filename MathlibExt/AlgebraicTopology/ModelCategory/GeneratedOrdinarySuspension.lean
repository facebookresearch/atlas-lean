/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedOrdinaryCofiberComparison
import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedOrdinaryPuppe

/-!
# Original Q endpoints in cone suspension

The Q-image of an arrow into the actual zero object targets QZ, whereas
cone suspension of QX targets Z. The original q_Z counit constructs the
natural arrow comparison. Its induced cofiber map is weak at the actual
cofibrant endpoints. The resulting full ordinary-Ho comparison retains
the same canonical homotopy cofiber and every original Q map.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe w u v

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.GeneratedOrdinarySuspension

open OrdinaryHoChosenPuppe GeneratedOrdinaryCofiber

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ) (Z : C) (hZ : IsZero Z)

/-- Keep QX unchanged and use the original q_Z map on the actual target QZ. -/
def zeroArrowComparison :
    zeroArrowFunctor Z hZ ⋙ replacementArrow d ⟶
      GeneratedFunctorialReplacements.Q d ⋙ zeroArrowFunctor Z hZ where
  app X := Arrow.homMk (𝟙 ((GeneratedFunctorialReplacements.Q d).obj X))
    ((GeneratedFunctorialReplacements.counit d).app Z) (hZ.isTerminal.hom_ext _ _)
  naturality X Y f := by
    apply Arrow.hom_ext
    · change (GeneratedFunctorialReplacements.Q d).map f ≫ 𝟙 _ =
        𝟙 _ ≫ (GeneratedFunctorialReplacements.Q d).map f
      simp
    · change (GeneratedFunctorialReplacements.Q d).map (𝟙 Z) ≫
          (GeneratedFunctorialReplacements.counit d).app Z =
        (GeneratedFunctorialReplacements.counit d).app Z ≫ 𝟙 Z
      rw [(GeneratedFunctorialReplacements.Q d).map_id, Category.id_comp]
      exact (Category.comp_id _).symm

/-- The complete original source comparison is identity on QX. -/
theorem zeroArrowComparison_left (X : C) :
    ((zeroArrowComparison d Z hZ).app X).left =
      𝟙 ((GeneratedFunctorialReplacements.Q d).obj X) := rfl

/-- The complete original target comparison is the same original q_Z. -/
theorem zeroArrowComparison_right (X : C) :
    ((zeroArrowComparison d Z hZ).app X).right =
      (GeneratedFunctorialReplacements.counit d).app Z := rfl

/-- The full zero-target square retains the actual Q-image of the collapse map. -/
theorem zeroArrowComparison_square (X : C) :
    (GeneratedFunctorialReplacements.Q d).map (toZero Z hZ X) ≫
        (GeneratedFunctorialReplacements.counit d).app Z =
      toZero Z hZ ((GeneratedFunctorialReplacements.Q d).obj X) :=
  (((zeroArrowComparison d Z hZ).app X).w.symm).trans (Category.id_comp _)

/-- The original two-endpoint Q comparison induces the actual cone-suspension comparison. -/
def coneSuspensionComparison :
    zeroArrowFunctor Z hZ ⋙ derivedCofiber d Z hZ ⟶
      GeneratedFunctorialReplacements.Q d ⋙ GeneratedOrdinaryPuppe.suspension d Z hZ :=
  Functor.whiskerRight (zeroArrowComparison d Z hZ) (cofiber d Z hZ)

/-- Original Q endpoint cofibrancy and q_Z weakness prove the whole cofiber comparison weak. -/
theorem coneSuspensionComparison_weak (X : C) :
    weakEquivalences C ((coneSuspensionComparison d Z hZ).app X) := by
  let _ : IsCofibrant ((zeroArrowFunctor Z hZ ⋙ replacementArrow d).obj X).left :=
    GeneratedFunctorialReplacements.Q_isCofibrant d X
  let _ : IsCofibrant ((zeroArrowFunctor Z hZ ⋙ replacementArrow d).obj X).right :=
    GeneratedFunctorialReplacements.Q_isCofibrant d Z
  let _ : IsCofibrant ((GeneratedFunctorialReplacements.Q d ⋙ zeroArrowFunctor Z hZ).obj X).left :=
    GeneratedFunctorialReplacements.Q_isCofibrant d X
  let _ : IsCofibrant ((GeneratedFunctorialReplacements.Q d ⋙ zeroArrowFunctor Z hZ).obj X).right :=
    (isCofibrant_iff_of_isInitial (𝟙 Z) hZ.isInitial).mpr (by infer_instance)
  exact cofiber_map_weak d Z hZ ((zeroArrowComparison d Z hZ).app X)
    (mem_weakEquivalences (𝟙 ((GeneratedFunctorialReplacements.Q d).obj X)))
    (GeneratedFunctorialReplacements.counit_weak d Z)

/-- The actual q_Z comparison gives a full natural cone-suspension isomorphism in ordinary Ho. -/
def coneSuspensionHoIso :
    zeroArrowFunctor Z hZ ⋙ derivedCofiber d Z hZ ⋙ toHomotopyCategory C ≅
      GeneratedFunctorialReplacements.Q d ⋙ GeneratedOrdinaryPuppe.suspension d Z hZ ⋙
        toHomotopyCategory C := by
  letI (X : C) : IsIso
      ((toHomotopyCategory C).map ((coneSuspensionComparison d Z hZ).app X)) :=
    Localization.inverts (toHomotopyCategory C) (weakEquivalences C) _
      (coneSuspensionComparison_weak d Z hZ X)
  exact NatIso.ofComponents
    (fun X => asIso ((toHomotopyCategory C).map ((coneSuspensionComparison d Z hZ).app X)))
    (fun {X Y} f => by
      change (toHomotopyCategory C).map
          ((zeroArrowFunctor Z hZ ⋙ derivedCofiber d Z hZ).map f) ≫
          (toHomotopyCategory C).map ((coneSuspensionComparison d Z hZ).app Y) =
        (toHomotopyCategory C).map ((coneSuspensionComparison d Z hZ).app X) ≫
          (toHomotopyCategory C).map
            ((GeneratedFunctorialReplacements.Q d ⋙ GeneratedOrdinaryPuppe.suspension d Z hZ).map f)
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact (toHomotopyCategory C).congr_map ((coneSuspensionComparison d Z hZ).naturality f))

/-- Cone suspension after Q computes the original zero-arrow canonical homotopy cofiber naturally. -/
def cofiberComparison :
    GeneratedFunctorialReplacements.Q d ⋙ GeneratedOrdinaryPuppe.suspension d Z hZ ⋙
        toHomotopyCategory C ≅
      zeroArrowFunctor Z hZ ⋙ GeneratedOrdinaryCofiberComparison.canonicalCofiberOfGeneration d ⋙
        toHomotopyCategory C :=
  (coneSuspensionHoIso d Z hZ).symm ≪≫
    Functor.isoWhiskerLeft (zeroArrowFunctor Z hZ)
      (GeneratedOrdinaryCofiberComparison.comparisonOfGeneration d Z hZ)

end HomotopicalAlgebra.GeneratedOrdinarySuspension
