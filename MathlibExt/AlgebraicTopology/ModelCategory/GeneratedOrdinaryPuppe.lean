/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedOrdinaryCofiber
import MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryHoChosenPuppeHomSequence

/-!
# The original generated Puppe tower on all input arrows

The whole original Q-image arrow is followed by the same chosen cone and
cofiber construction. Every stage is an actual functor on Arrow(C). Its
ordinary Hom bifunctor and restriction transformations retain all source
and target maps. The cone hypotheses in the chosen Puppe theorem are earned
from the original I factorization. Ordinary integer shifts and represented
group comparisons require the separate framing and stability constructions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe w u v

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.GeneratedOrdinaryPuppe

open GeneratedOrdinaryCofiber

variable {C : Type u} [Category.{v} C] [ModelCategory C] [HasZeroObject C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ) (Z : C) (hZ : IsZero Z)

/-- Every actual stage uses the original Q arrow and the unchanged target-inclusion functor. -/
def stageFunctor (n : ℕ) : Arrow C ⥤ Arrow C :=
  replacementArrow d ⋙ OrdinaryHoChosenPuppeHomSequence.stageFunctor
    (GeneratedOrdinaryCone.cone d Z hZ) (GeneratedOrdinaryCone.inclusion d Z hZ)
    (GeneratedOrdinaryCone.cofiberCocone d Z hZ)
    (GeneratedOrdinaryCone.cofiberIsColimit d Z hZ) n

/-- The entire original object functor at an arbitrary Puppe stage. -/
def termFunctor (n : ℕ) : Arrow C ⥤ C := stageFunctor d Z hZ n ⋙ Arrow.leftFunc

/-- Consecutive terms retain the same original stage arrows as a full natural transformation. -/
def step (n : ℕ) : termFunctor d Z hZ n ⟶ termFunctor d Z hZ (n + 1) where
  app F := ((stageFunctor d Z hZ n).obj F).hom
  naturality _ _ a := ((stageFunctor d Z hZ n).map a).w

omit [HasZeroObject C] in
/-- Both endpoint cofibrancies are earned from original Q and propagate through every stage. -/
theorem stage_cofibrant (n : ℕ) (F : Arrow C) :
    IsCofibrant ((stageFunctor d Z hZ n).obj F).left ∧
      IsCofibrant ((stageFunctor d Z hZ n).obj F).right := by
  let _ : IsCofibrant ((replacementArrow d).obj F).left :=
    GeneratedFunctorialReplacements.Q_isCofibrant d F.left
  let _ : IsCofibrant ((replacementArrow d).obj F).right :=
    GeneratedFunctorialReplacements.Q_isCofibrant d F.right
  exact OrdinaryHoChosenPuppeHomSequence.stageArrow_cofibrant
    (GeneratedOrdinaryCone.cone d Z hZ) (GeneratedOrdinaryCone.inclusion d Z hZ)
    (GeneratedOrdinaryCone.cofiberCocone d Z hZ)
    (GeneratedOrdinaryCone.cofiberIsColimit d Z hZ)
    (fun X _ => GeneratedOrdinaryCone.inclusion_cofibration d Z hZ X)
    n ((replacementArrow d).obj F)

/-- Ordinary Hom of every original stage carrier into the unchanged target. -/
abbrev homTerm (n : ℕ) (F : Arrow C) (E : C) :=
  (toHomotopyCategory C).obj ((termFunctor d Z hZ n).obj F) ⟶
    (toHomotopyCategory C).obj E

/-- The actual two-variable Hom functor uses canonical coyoneda and original source and target maps. -/
def homFunctor (n : ℕ) : (Arrow C)ᵒᵖ ⥤ C ⥤ Type (max u v) :=
  (termFunctor d Z hZ n ⋙ toHomotopyCategory C).op ⋙ coyoneda ⋙
    (Functor.whiskeringLeft C (HomotopyCategory C) (Type (max u v))).obj
      (toHomotopyCategory C)

/-- Restriction is precomposition by the same original step in both variables. -/
def restriction (n : ℕ) : homFunctor d Z hZ (n + 1) ⟶ homFunctor d Z hZ n :=
  Functor.whiskerRight
    (Functor.whiskerRight (NatTrans.op (Functor.whiskerRight (step d Z hZ n)
      (toHomotopyCategory C))) coyoneda)
    ((Functor.whiskeringLeft C (HomotopyCategory C) (Type (max u v))).obj
      (toHomotopyCategory C))

omit [HasZeroObject C] in
/-- The full Hom functor retains the original ordinary-Ho carrier at every stage. -/
theorem homFunctor_obj (n : ℕ) (F : Arrow C) (E : C) :
    ((homFunctor d Z hZ n).obj (Opposite.op F)).obj E = homTerm d Z hZ n F E := rfl

omit [HasZeroObject C] in
/-- The actual restriction function is the original step precomposition. -/
theorem restriction_apply (n : ℕ) (F : Arrow C) (E : C)
    (g : homTerm d Z hZ (n + 1) F E) :
    (((restriction d Z hZ n).app (Opposite.op F)).app E) g =
      (toHomotopyCategory C).map ((step d Z hZ n).app F) ≫ g := rfl

omit [HasZeroObject C] in
/-- Every full source Arrow acts through the original whole stage map. -/
theorem homFunctor_source (n : ℕ) {F G : Arrow C} (a : F ⟶ G) (E : C)
    (g : homTerm d Z hZ n G E) :
    (((homFunctor d Z hZ n).map a.op).app E) g =
      (toHomotopyCategory C).map ((termFunctor d Z hZ n).map a) ≫ g := rfl

omit [HasZeroObject C] in
/-- Every full target arrow acts by the same ordinary-Ho postcomposition. -/
theorem homFunctor_target (n : ℕ) (F : Arrow C) {E E' : C} (a : E ⟶ E')
    (g : homTerm d Z hZ n F E) :
    (((homFunctor d Z hZ n).obj (Opposite.op F)).map a) g =
      g ≫ (toHomotopyCategory C).map a := rfl

/-- The original generated tower has image equal to the same null kernel at every stage. -/
theorem exact_at (n : ℕ) (F : Arrow C) (E : C) [IsFibrant E]
    (g : homTerm d Z hZ (n + 1) F E) :
    (∃ h : homTerm d Z hZ (n + 2) F E,
      (((restriction d Z hZ (n + 1)).app (Opposite.op F)).app E) h = g) ↔
      (((restriction d Z hZ n).app (Opposite.op F)).app E) g =
        OrdinaryHoCofiberKernel.nullHom ((termFunctor d Z hZ n).obj F) E := by
  let _ : IsCofibrant ((replacementArrow d).obj F).left :=
    GeneratedFunctorialReplacements.Q_isCofibrant d F.left
  let _ : IsCofibrant ((replacementArrow d).obj F).right :=
    GeneratedFunctorialReplacements.Q_isCofibrant d F.right
  exact OrdinaryHoChosenPuppeHomSequence.exact_at Z hZ
    (GeneratedOrdinaryCone.cone d Z hZ) (GeneratedOrdinaryCone.inclusion d Z hZ)
    (GeneratedOrdinaryCone.cofiberCocone d Z hZ)
    (GeneratedOrdinaryCone.cofiberIsColimit d Z hZ)
    (fun X _ => GeneratedOrdinaryCone.inclusion_cofibration d Z hZ X)
    (fun X _ => GeneratedOrdinaryCone.toZero_cone_weak d Z hZ X)
    n ((replacementArrow d).obj F) E g

/-- The original chosen suspension functor retains its cone and actual zero endpoint. -/
def suspension : C ⥤ C :=
  OrdinaryHoChosenPuppe.suspensionFunctor (GeneratedOrdinaryCone.cone d Z hZ)
    (GeneratedOrdinaryCone.inclusion d Z hZ)
    (GeneratedOrdinaryCone.cofiberCocone d Z hZ)
    (GeneratedOrdinaryCone.cofiberIsColimit d Z hZ) Z hZ

/-- The three-step comparison is natural on every entire original input arrow. -/
def shiftComparison (n : ℕ) :
    termFunctor d Z hZ (n + 3) ⟶ termFunctor d Z hZ n ⋙ suspension d Z hZ where
  app F := OrdinaryHoChosenPuppeHomSequence.shiftComparison Z hZ
    (GeneratedOrdinaryCone.cone d Z hZ) (GeneratedOrdinaryCone.inclusion d Z hZ)
    (GeneratedOrdinaryCone.cofiberCocone d Z hZ)
    (GeneratedOrdinaryCone.cofiberIsColimit d Z hZ) n ((replacementArrow d).obj F)
  naturality _ _ a := OrdinaryHoChosenPuppeHomSequence.shiftComparison_naturality Z hZ
    (GeneratedOrdinaryCone.cone d Z hZ) (GeneratedOrdinaryCone.inclusion d Z hZ)
    (GeneratedOrdinaryCone.cofiberCocone d Z hZ)
    (GeneratedOrdinaryCone.cofiberIsColimit d Z hZ) n ((replacementArrow d).map a)

omit [HasZeroObject C] in
/-- Weakness of every complete comparison follows from the original generated cone source. -/
theorem shiftComparison_weak (n : ℕ) (F : Arrow C) :
    weakEquivalences C ((shiftComparison d Z hZ n).app F) := by
  let _ : IsCofibrant ((replacementArrow d).obj F).left :=
    GeneratedFunctorialReplacements.Q_isCofibrant d F.left
  let _ : IsCofibrant ((replacementArrow d).obj F).right :=
    GeneratedFunctorialReplacements.Q_isCofibrant d F.right
  exact OrdinaryHoChosenPuppeHomSequence.shiftComparison_weak Z hZ
    (GeneratedOrdinaryCone.cone d Z hZ) (GeneratedOrdinaryCone.inclusion d Z hZ)
    (GeneratedOrdinaryCone.cofiberCocone d Z hZ)
    (GeneratedOrdinaryCone.cofiberIsColimit d Z hZ)
    (fun X _ => GeneratedOrdinaryCone.inclusion_cofibration d Z hZ X)
    (fun X _ => GeneratedOrdinaryCone.toZero_cone_weak d Z hZ X)
    n ((replacementArrow d).obj F)

/-- The actual boundary is a full natural transformation from the original Q cofiber. -/
def boundary : termFunctor d Z hZ 2 ⟶ termFunctor d Z hZ 0 ⋙ suspension d Z hZ where
  app F := OrdinaryHoChosenPuppe.boundary (GeneratedOrdinaryCone.cone d Z hZ)
    (GeneratedOrdinaryCone.inclusion d Z hZ)
    (GeneratedOrdinaryCone.cofiberCocone d Z hZ)
    (GeneratedOrdinaryCone.cofiberIsColimit d Z hZ) Z hZ ((replacementArrow d).obj F)
  naturality _ _ a := OrdinaryHoChosenPuppe.boundary_naturality
    (GeneratedOrdinaryCone.cone d Z hZ) (GeneratedOrdinaryCone.inclusion d Z hZ)
    (GeneratedOrdinaryCone.cofiberCocone d Z hZ)
    (GeneratedOrdinaryCone.cofiberIsColimit d Z hZ) Z hZ ((replacementArrow d).map a)

omit [HasZeroObject C] in
/-- The next target leg followed by rotation is precisely the original cofiber boundary. -/
theorem boundary_recovered (F : Arrow C) :
    (step d Z hZ 2).app F ≫ (shiftComparison d Z hZ 0).app F = (boundary d Z hZ).app F :=
  OrdinaryHoChosenPuppeRotation.rotationComparison_cofiber (GeneratedOrdinaryCone.cone d Z hZ)
    (GeneratedOrdinaryCone.inclusion d Z hZ)
    (GeneratedOrdinaryCone.cofiberCocone d Z hZ)
    (GeneratedOrdinaryCone.cofiberIsColimit d Z hZ) Z hZ ((replacementArrow d).obj F)

/-- The three-step weak comparison gives the same full natural isomorphism in ordinary Ho. -/
def shiftHoIso (n : ℕ) :
    termFunctor d Z hZ (n + 3) ⋙ toHomotopyCategory C ≅
      termFunctor d Z hZ n ⋙ suspension d Z hZ ⋙ toHomotopyCategory C := by
  letI (F : Arrow C) : IsIso
      ((toHomotopyCategory C).map ((shiftComparison d Z hZ n).app F)) :=
    Localization.inverts (toHomotopyCategory C) (weakEquivalences C) _
      (shiftComparison_weak d Z hZ n F)
  exact NatIso.ofComponents
    (fun F => asIso ((toHomotopyCategory C).map ((shiftComparison d Z hZ n).app F)))
    (fun {F G} a => by
      change (toHomotopyCategory C).map ((termFunctor d Z hZ (n + 3)).map a) ≫
          (toHomotopyCategory C).map ((shiftComparison d Z hZ n).app G) =
        (toHomotopyCategory C).map ((shiftComparison d Z hZ n).app F) ≫
          (toHomotopyCategory C).map ((suspension d Z hZ).map ((termFunctor d Z hZ n).map a))
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact (toHomotopyCategory C).congr_map ((shiftComparison d Z hZ n).naturality a))

/-- Suspension reversal is a full natural automorphism of each original stage suspension. -/
def termReversal (n : ℕ) :
    termFunctor d Z hZ n ⋙ suspension d Z hZ ⋙ toHomotopyCategory C ≅
      termFunctor d Z hZ n ⋙ suspension d Z hZ ⋙ toHomotopyCategory C := by
  refine NatIso.ofComponents (fun F => ?_) (fun {F G} a => ?_)
  · let _ : IsCofibrant ((replacementArrow d).obj F).left :=
      GeneratedFunctorialReplacements.Q_isCofibrant d F.left
    let _ : IsCofibrant ((replacementArrow d).obj F).right :=
      GeneratedFunctorialReplacements.Q_isCofibrant d F.right
    exact OrdinaryHoChosenPuppeHomSequence.termReversal Z hZ
      (GeneratedOrdinaryCone.cone d Z hZ) (GeneratedOrdinaryCone.inclusion d Z hZ)
      (GeneratedOrdinaryCone.cofiberCocone d Z hZ)
      (GeneratedOrdinaryCone.cofiberIsColimit d Z hZ)
      (fun X _ => GeneratedOrdinaryCone.inclusion_cofibration d Z hZ X)
      (fun X _ => GeneratedOrdinaryCone.toZero_cone_weak d Z hZ X)
      n ((replacementArrow d).obj F)
  · let _ : IsCofibrant ((termFunctor d Z hZ n).obj F) := (stage_cofibrant d Z hZ n F).1
    let _ : IsCofibrant ((termFunctor d Z hZ n).obj G) := (stage_cofibrant d Z hZ n G).1
    let _ : Cofibration
        ((GeneratedOrdinaryCone.inclusion d Z hZ).app ((termFunctor d Z hZ n).obj F)) :=
      (cofibration_iff _).mpr (GeneratedOrdinaryCone.inclusion_cofibration d Z hZ _)
    let _ : Cofibration
        ((GeneratedOrdinaryCone.inclusion d Z hZ).app ((termFunctor d Z hZ n).obj G)) :=
      (cofibration_iff _).mpr (GeneratedOrdinaryCone.inclusion_cofibration d Z hZ _)
    exact OrdinaryHoChosenPuppeRotation.suspensionReversal_naturality
      (GeneratedOrdinaryCone.cone d Z hZ) (GeneratedOrdinaryCone.inclusion d Z hZ)
      (GeneratedOrdinaryCone.cofiberCocone d Z hZ)
      (GeneratedOrdinaryCone.cofiberIsColimit d Z hZ) Z hZ ((termFunctor d Z hZ n).map a)
      (GeneratedOrdinaryCone.toZero_cone_weak d Z hZ _)
      (GeneratedOrdinaryCone.toZero_cone_weak d Z hZ _)

omit [HasZeroObject C] in
/-- Every original shift square retains the actual suspension reversal and its boundary sign. -/
theorem signed_shift_square (n : ℕ) :
    Functor.whiskerRight (step d Z hZ (n + 3)) (toHomotopyCategory C) ≫
        Functor.whiskerRight (shiftComparison d Z hZ (n + 1)) (toHomotopyCategory C) =
      Functor.whiskerRight (shiftComparison d Z hZ n) (toHomotopyCategory C) ≫
        Functor.whiskerRight (Functor.whiskerRight (step d Z hZ n) (suspension d Z hZ))
          (toHomotopyCategory C) ≫ (termReversal d Z hZ (n + 1)).hom := by
  ext F
  let _ : IsCofibrant ((replacementArrow d).obj F).left :=
    GeneratedFunctorialReplacements.Q_isCofibrant d F.left
  let _ : IsCofibrant ((replacementArrow d).obj F).right :=
    GeneratedFunctorialReplacements.Q_isCofibrant d F.right
  exact OrdinaryHoChosenPuppeHomSequence.signed_shift_square Z hZ
    (GeneratedOrdinaryCone.cone d Z hZ) (GeneratedOrdinaryCone.inclusion d Z hZ)
    (GeneratedOrdinaryCone.cofiberCocone d Z hZ)
    (GeneratedOrdinaryCone.cofiberIsColimit d Z hZ)
    (fun X _ => GeneratedOrdinaryCone.inclusion_cofibration d Z hZ X)
    (fun X _ => GeneratedOrdinaryCone.toZero_cone_weak d Z hZ X)
    n ((replacementArrow d).obj F)

end HomotopicalAlgebra.GeneratedOrdinaryPuppe
