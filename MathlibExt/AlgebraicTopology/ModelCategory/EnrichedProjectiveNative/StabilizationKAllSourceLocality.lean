/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Functor.CoaugmentedLocalization
public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.IndexCofibrantProperness
public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKLocalLifting

/-!
# SAME original K-unit gluing and L preserving EVERY original level weak map

Push out the actual original K-unit along the SAME original arrow. Its
complete native pushout, both legs, every Arrow input and canonical map to
SAME L(target) are constructed from the original unit and L maps. The
canonical comparison's left leg is literally SAME L of the original arrow.
Original native level left properness makes the pushout's left leg weak;
original all-point Omega invariance then makes its actual target K-local.
The pushed-out K-unit is K-left. One actual original extension across the
target K-unit constructs an inverse to the canonical comparison in level
Ho. Both inverse equations use the proved arbitrary-source relative Ho
uniqueness, preserving both original units and the SAME chosen extension.
This proves L preserves EVERY original level weak map, with no source or
target cofibrancy hypothesis. Whole native input maps and BOTH Ho NatIso
functions are retained. General pi-star K-left acyclicity and the second
stable WFS/model are the next original LQ/L recognition consumers; FS and
old four-map native identities remain separate required obligations.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK
open HomotopicalAlgebra.EnrichedProjective.Native.IndexCofibrantProperness
open HomotopicalAlgebra.EnrichedProjective.Native.Diagrams

variable {I L : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  (s : NativeStabilizationFamily.{u, v} I L)
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- The actual original K-unit is pushed out along the SAME complete caller arrow. -/
def originalKUnitPushout (F : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    (EnrichedFunctorCat PointedCGWH.{u, v} I) :=
  pushout ((localReplacementUnit s).app F.left) F.hom

/-- The actual left leg comes from SAME original L(source), without a new replacement choice. -/
def originalKUnitPushoutLeftLeg (F : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    (localReplacement s).obj F.left ⟶ (originalKUnitPushout s) F :=
  pushout.inl ((localReplacementUnit s).app F.left) F.hom

/-- The actual right leg retains SAME original target of the caller arrow. -/
def originalKUnitPushoutRightLeg (F : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    F.right ⟶ (originalKUnitPushout s) F := pushout.inr ((localReplacementUnit s).app F.left) F.hom

/-- The whole actual square retains SAME original K-unit and original arrow. -/
theorem originalKUnitPushout_isPushout (F : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    IsPushout ((localReplacementUnit s).app F.left) F.hom
      ((originalKUnitPushoutLeftLeg s) F) ((originalKUnitPushoutRightLeg s) F) :=
  IsPushout.of_hasPushout _ _

/-- Every complete original Arrow input constructs the actual native pushout map. -/
def originalKUnitPushoutMap
    {F G : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)} (φ : F ⟶ G) :
    (originalKUnitPushout s) F ⟶ (originalKUnitPushout s) G :=
  pushout.desc ((localReplacement s).map φ.left ≫ (originalKUnitPushoutLeftLeg s) G)
    (φ.right ≫ (originalKUnitPushoutRightLeg s) G) (by
      calc
        _ = ((localReplacementUnit s).app F.left ≫ (localReplacement s).map φ.left) ≫
            (originalKUnitPushoutLeftLeg s) G := (Category.assoc _ _ _).symm
        _ = (φ.left ≫ (localReplacementUnit s).app G.left) ≫ (originalKUnitPushoutLeftLeg s) G :=
          congrArg (fun t => t ≫ (originalKUnitPushoutLeftLeg s) G)
            ((localReplacementUnit_naturality s) φ.left)
        _ = φ.left ≫ (G.hom ≫ (originalKUnitPushoutRightLeg s) G) := by
          rw [Category.assoc, ((originalKUnitPushout_isPushout s) G).w]
        _ = (F.hom ≫ φ.right) ≫ (originalKUnitPushoutRightLeg s) G :=
          (Category.assoc _ _ _).symm.trans
            (congrArg (fun t => t ≫ (originalKUnitPushoutRightLeg s) G) φ.w)
        _ = _ := Category.assoc _ _ _)

/-- Every complete pushout input preserves the literal original L(source) map and left leg. -/
theorem originalKUnitPushoutMap_left
    {F G : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)} (φ : F ⟶ G) :
    (originalKUnitPushoutLeftLeg s) F ≫ (originalKUnitPushoutMap s) φ =
      (localReplacement s).map φ.left ≫ (originalKUnitPushoutLeftLeg s) G := by
  exact pushout.inl_desc _ _ _

/-- Every complete pushout input preserves the literal original target map and right leg. -/
theorem originalKUnitPushoutMap_right
    {F G : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)} (φ : F ⟶ G) :
    (originalKUnitPushoutRightLeg s) F ≫ (originalKUnitPushoutMap s) φ =
      φ.right ≫ (originalKUnitPushoutRightLeg s) G := by
  exact pushout.inr_desc _ _ _

/-- The full native pushout map of the actual identity is the actual identity. -/
theorem originalKUnitPushoutMap_id (F : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    (originalKUnitPushoutMap s) (𝟙 F) = 𝟙 ((originalKUnitPushout s) F) := by
  apply pushout.hom_ext
  · change (originalKUnitPushoutLeftLeg s) F ≫ (originalKUnitPushoutMap s) (𝟙 F) =
      (originalKUnitPushoutLeftLeg s) F ≫ 𝟙 ((originalKUnitPushout s) F)
    rw [(originalKUnitPushoutMap_left s), Category.comp_id]
    change (localReplacement s).map (𝟙 F.left) ≫ _ = _
    rw [(localReplacement s).map_id, Category.id_comp]
  · change (originalKUnitPushoutRightLeg s) F ≫ (originalKUnitPushoutMap s) (𝟙 F) =
      (originalKUnitPushoutRightLeg s) F ≫ 𝟙 ((originalKUnitPushout s) F)
    rw [(originalKUnitPushoutMap_right s), Category.comp_id]
    change 𝟙 F.right ≫ _ = _
    exact Category.id_comp _

/-- Both whole original Arrow components are retained by complete native pushout composition. -/
theorem originalKUnitPushoutMap_comp
    {F G H : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)} (φ : F ⟶ G) (ψ : G ⟶ H) :
    (originalKUnitPushoutMap s) (φ ≫ ψ) = (originalKUnitPushoutMap s) φ ≫ (originalKUnitPushoutMap
      s) ψ := by
  apply pushout.hom_ext
  · change (originalKUnitPushoutLeftLeg s) F ≫ (originalKUnitPushoutMap s) (φ ≫ ψ) =
      (originalKUnitPushoutLeftLeg s) F ≫ ((originalKUnitPushoutMap s) φ ≫
        (originalKUnitPushoutMap s) ψ)
    calc
      _ = (localReplacement s).map (φ.left ≫ ψ.left) ≫ (originalKUnitPushoutLeftLeg s) H :=
        (originalKUnitPushoutMap_left s) (φ ≫ ψ)
      _ = ((localReplacement s).map φ.left ≫ (localReplacement s).map ψ.left) ≫
          (originalKUnitPushoutLeftLeg s) H :=
        congrArg (fun t => t ≫ (originalKUnitPushoutLeftLeg s) H)
          ((localReplacement s).map_comp φ.left ψ.left)
      _ = (localReplacement s).map φ.left ≫
          ((originalKUnitPushoutLeftLeg s) G ≫ (originalKUnitPushoutMap s) ψ) := by
        rw [(originalKUnitPushoutMap_left s), ← Category.assoc]
      _ = ((originalKUnitPushoutLeftLeg s) F ≫ (originalKUnitPushoutMap s) φ) ≫
          (originalKUnitPushoutMap s) ψ :=
        (Category.assoc _ _ _).symm.trans
          (congrArg (fun t => t ≫ (originalKUnitPushoutMap s) ψ)
            ((originalKUnitPushoutMap_left s) φ).symm)
      _ = _ := Category.assoc _ _ _
  · change (originalKUnitPushoutRightLeg s) F ≫ (originalKUnitPushoutMap s) (φ ≫ ψ) =
      (originalKUnitPushoutRightLeg s) F ≫ ((originalKUnitPushoutMap s) φ ≫
        (originalKUnitPushoutMap s) ψ)
    calc
      _ = (φ.right ≫ ψ.right) ≫ (originalKUnitPushoutRightLeg s) H :=
        (originalKUnitPushoutMap_right s) (φ ≫ ψ)
      _ = φ.right ≫ ((originalKUnitPushoutRightLeg s) G ≫ (originalKUnitPushoutMap s) ψ) := by
        rw [(originalKUnitPushoutMap_right s), ← Category.assoc]
      _ = ((originalKUnitPushoutRightLeg s) F ≫ (originalKUnitPushoutMap s) φ) ≫
          (originalKUnitPushoutMap s) ψ :=
        (Category.assoc _ _ _).symm.trans
          (congrArg (fun t => t ≫ (originalKUnitPushoutMap s) ψ)
            ((originalKUnitPushoutMap_right s) φ).symm)
      _ = _ := Category.assoc _ _ _

/-- The SAME actual native unit pushouts assemble into their complete original Arrow functor. -/
def originalKUnitPushoutFunctor : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I) ⥤
    (EnrichedFunctorCat PointedCGWH.{u, v} I) where
  obj := (originalKUnitPushout s)
  map := (originalKUnitPushoutMap s)
  map_id := (originalKUnitPushoutMap_id s)
  map_comp := (originalKUnitPushoutMap_comp s)

/-- The full actual left-leg transformation retains original L and every source Arrow input. -/
def originalKUnitPushoutLeft : Arrow.leftFunc ⋙ (localReplacement s) ⟶
    (originalKUnitPushoutFunctor s) where
  app := (originalKUnitPushoutLeftLeg s)
  naturality _ _ φ := ((originalKUnitPushoutMap_left s) φ).symm

/-- The full actual right-leg transformation retains every original target Arrow input. -/
def originalKUnitPushoutRight : Arrow.rightFunc ⟶ (originalKUnitPushoutFunctor s) where
  app := (originalKUnitPushoutRightLeg s)
  naturality _ _ φ := ((originalKUnitPushoutMap_right s) φ).symm

/-- The actual canonical comparison uses SAME original L map and SAME target K-unit. -/
def originalKUnitPushoutComparison (F : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    (originalKUnitPushout s) F ⟶ (localReplacement s).obj F.right :=
  pushout.desc ((localReplacement s).map F.hom) ((localReplacementUnit s).app F.right)
    ((localReplacementUnit_naturality s) F.hom)

/-- The complete comparison's left leg is L of the literal original caller arrow. -/
theorem originalKUnitPushoutComparison_left (F : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    (originalKUnitPushoutLeftLeg s) F ≫ (originalKUnitPushoutComparison s) F =
      (localReplacement s).map F.hom := pushout.inl_desc _ _ _

/-- The complete comparison's right leg is the SAME literal original target K-unit. -/
theorem originalKUnitPushoutComparison_right (F : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    (originalKUnitPushoutRightLeg s) F ≫ (originalKUnitPushoutComparison s) F =
      (localReplacementUnit s).app F.right := pushout.inr_desc _ _ _

/-- EVERY full original Arrow input commutes with the complete canonical native comparison. -/
theorem originalKUnitPushoutComparison_input
    {F G : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)} (φ : F ⟶ G) :
    (originalKUnitPushoutMap s) φ ≫ (originalKUnitPushoutComparison s) G =
      (originalKUnitPushoutComparison s) F ≫ (localReplacement s).map φ.right := by
  apply pushout.hom_ext
  · change (originalKUnitPushoutLeftLeg s) F ≫
        ((originalKUnitPushoutMap s) φ ≫ (originalKUnitPushoutComparison s) G) =
      (originalKUnitPushoutLeftLeg s) F ≫
        ((originalKUnitPushoutComparison s) F ≫ (localReplacement s).map φ.right)
    calc
      _ = (localReplacement s).map φ.left ≫ (localReplacement s).map G.hom := by
        rw [← Category.assoc, (originalKUnitPushoutMap_left s), Category.assoc,
          (originalKUnitPushoutComparison_left s)]
      _ = (localReplacement s).map (φ.left ≫ G.hom) := ((localReplacement s).map_comp _ _).symm
      _ = (localReplacement s).map (F.hom ≫ φ.right) := (localReplacement s).congr_map φ.w
      _ = (localReplacement s).map F.hom ≫ (localReplacement s).map φ.right :=
        (localReplacement s).map_comp _ _
      _ = _ := by
        rw [← Category.assoc, (originalKUnitPushoutComparison_left s)]
  · change (originalKUnitPushoutRightLeg s) F ≫
        ((originalKUnitPushoutMap s) φ ≫ (originalKUnitPushoutComparison s) G) =
      (originalKUnitPushoutRightLeg s) F ≫
        ((originalKUnitPushoutComparison s) F ≫ (localReplacement s).map φ.right)
    calc
      _ = φ.right ≫ (localReplacementUnit s).app G.right := by
        rw [← Category.assoc, (originalKUnitPushoutMap_right s), Category.assoc,
          (originalKUnitPushoutComparison_right s)]
      _ = (localReplacementUnit s).app F.right ≫ (localReplacement s).map φ.right :=
        ((localReplacementUnit_naturality s) φ.right).symm
      _ = _ := by
        rw [← Category.assoc, (originalKUnitPushoutComparison_right s)]

/-- The ENTIRE original canonical comparison is a genuine native natural transformation. -/
def originalKUnitPushoutComparisonNatTrans : (originalKUnitPushoutFunctor s) ⟶
    Arrow.rightFunc ⋙ (localReplacement s) where
  app := (originalKUnitPushoutComparison s)
  naturality _ _ φ := (originalKUnitPushoutComparison_input s) φ

/-- The pushed-out SAME original unit is actually K-left, with arbitrary original source. -/
theorem originalKUnitPushoutRight_mem_KLeft (F : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    (generators s).rlp.llp ((originalKUnitPushoutRightLeg s) F) :=
  MorphismProperty.of_isPushout ((originalKUnitPushout_isPushout s) F).flip
    ((localReplacementUnit_mem_left s) F.left)

/-- Original native level left properness makes the literal unit-pushout comparison leg weak. -/
theorem originalKUnitPushoutLeft_levelWeak
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b)) (F : Arrow (EnrichedFunctorCat
      PointedCGWH.{u, v} I))
    (hF : weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I) F.hom) :
    weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I) ((originalKUnitPushoutLeftLeg s) F)
      :=
  originalNativePushout_levelWeak hHom _ _ _ _ ((originalKUnitPushout_isPushout s) F)
    ((left_le_cofibrations s) _ ((localReplacementUnit_mem_left s) F.left)) hF

/-- The literal original pushout is Omega by the proved all-point original weak invariance. -/
theorem originalKUnitPushout_isOmega
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b)) (F : Arrow (EnrichedFunctorCat
      PointedCGWH.{u, v} I))
    (hF : weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I) F.hom) :
    IsOmega s ((originalKUnitPushout s) F) :=
  (originalOmega_iff_of_levelWeak s _ ((originalKUnitPushoutLeft_levelWeak s hHom) F hF)).mp
    (((lifting_toZero_iff_isOmega s) _).mp ((localReplacement_isLocal s) F.left))

/-- The SAME native pushout satisfies actual original K-local lifting. -/
theorem originalKUnitPushout_isKLocal
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b)) (F : Arrow (EnrichedFunctorCat
      PointedCGWH.{u, v} I))
    (hF : weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I) F.hom) :
    (generators s).rlp (toZero ((originalKUnitPushout s) F)) :=
  ((lifting_toZero_iff_isOmega s) _).mpr ((originalKUnitPushout_isOmega s hHom) F hF)

/-- One actual original target-unit extension constructs the SAME chosen inverse function. -/
def originalKUnitPushoutRetraction
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b)) (F : Arrow (EnrichedFunctorCat
      PointedCGWH.{u, v} I))
    (hF : weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I) F.hom) :
    (localReplacement s).obj F.right ⟶ (originalKUnitPushout s) F :=
  (originalKLeftExtension s) ((localReplacementUnit s).app F.right)
    ((localReplacementUnit_mem_left s) F.right) ((originalKUnitPushout s) F)
    ((originalKUnitPushout_isKLocal s hHom) F hF) ((originalKUnitPushoutRightLeg s) F)

/-- The chosen inverse retains the SAME original target K-unit and literal original right leg. -/
theorem originalKUnitPushoutRetraction_unit
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b)) (F : Arrow (EnrichedFunctorCat
      PointedCGWH.{u, v} I))
    (hF : weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I) F.hom) :
    (localReplacementUnit s).app F.right ≫ (originalKUnitPushoutRetraction s hHom) F hF =
      (originalKUnitPushoutRightLeg s) F :=
  (originalKLeftExtension_section s) ((localReplacementUnit s).app F.right)
    ((localReplacementUnit_mem_left s) F.right) ((originalKUnitPushout s) F)
    ((originalKUnitPushout_isKLocal s hHom) F hF) _

/-- The complete canonical comparison and actual extension are genuinely inverse in level Ho. -/
def originalKUnitPushoutComparisonHoIso
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b)) (F : Arrow (EnrichedFunctorCat
      PointedCGWH.{u, v} I))
    (hF : weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I) F.hom) :
    (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj ((originalKUnitPushout s)
      F) ≅
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj
        ((localReplacement s).obj F.right) where
  hom := (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
    ((originalKUnitPushoutComparison s) F)
  inv := (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
    ((originalKUnitPushoutRetraction s hHom) F hF)
  hom_inv_id := by
    let H := toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)
    have hAgree : (originalKUnitPushoutRightLeg s) F ≫
        ((originalKUnitPushoutComparison s) F ≫ (originalKUnitPushoutRetraction s hHom) F hF) =
      (originalKUnitPushoutRightLeg s) F ≫ 𝟙 ((originalKUnitPushout s) F) := by
      rw [← Category.assoc, (originalKUnitPushoutComparison_right s),
        (originalKUnitPushoutRetraction_unit s hHom), Category.comp_id]
    exact (H.map_comp _ _).symm.trans
      (((originalKLeft_relative_Ho_eq s) _ ((originalKUnitPushoutRight_mem_KLeft s) F) _
        ((originalKUnitPushout_isKLocal s hHom) F hF) _ _ hAgree).trans (H.map_id _))
  inv_hom_id := by
    let H := toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)
    have hAgree : (localReplacementUnit s).app F.right ≫
        ((originalKUnitPushoutRetraction s hHom) F hF ≫ (originalKUnitPushoutComparison s) F) =
      (localReplacementUnit s).app F.right ≫ 𝟙 ((localReplacement s).obj F.right) := by
      rw [← Category.assoc, (originalKUnitPushoutRetraction_unit s hHom),
        (originalKUnitPushoutComparison_right s), Category.comp_id]
    exact (H.map_comp _ _).symm.trans
      (((originalKLeft_relative_Ho_eq s) _ ((localReplacementUnit_mem_left s) F.right) _
        ((localReplacement_isLocal s) F.right) _ _ hAgree).trans (H.map_id _))

/-- The whole canonical comparison is an original level weak map, with no cofibrancy conditions. -/
theorem originalKUnitPushoutComparison_levelWeak
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b))
    (F : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (hF : weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I) F.hom) :
    weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I) ((originalKUnitPushoutComparison s)
      F) :=
  (weakEquivalence_iff_isIso_toHomotopyCategory_map _).mpr
    ((originalKUnitPushoutComparisonHoIso s hHom) F hF).isIso_hom

/-- SAME L preserves EVERY original native level weak map on arbitrary source and target. -/
theorem originalKReplacement_preservesLevelWeak
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b))
    {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} I)} (f : X ⟶ Y)
    (hf : weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I) f) :
    weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I) ((localReplacement s).map f) := by
  let F : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I) := Arrow.mk f
  have h := (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I)).comp_mem
    ((originalKUnitPushoutLeftLeg s) F) ((originalKUnitPushoutComparison s) F)
    ((originalKUnitPushoutLeft_levelWeak s hHom) F hf) ((originalKUnitPushoutComparison_levelWeak
      s hHom) F hf)
  rw [(originalKUnitPushoutComparison_left s)] at h
  exact h

/-- The ENTIRE original base level weak class is mapped into itself by SAME actual original L. -/
theorem originalLevelWeak_le_KReplacementDetected
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b)) :
    weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I) ≤
      (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I)).inverseImage (localReplacement
        s) :=
  fun _ _ f hf => (originalKReplacement_preservesLevelWeak s hHom) f hf

/-- Full actual original weak Arrow carrier, retaining the complete original native arrow. -/
def originalLevelWeakArrowProperty : ObjectProperty (Arrow (EnrichedFunctorCat PointedCGWH.{u, v}
    I)) :=
  fun F => weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I) F.hom

/-- BOTH complete original canonical comparison functions assemble into their whole level Ho Iso. -/
def originalKUnitPushoutComparisonHoNatIso
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b)) :
    (originalLevelWeakArrowProperty (I := I)).ι ⋙ (originalKUnitPushoutFunctor s) ⋙
        toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I) ≅
      (originalLevelWeakArrowProperty (I := I)).ι ⋙ Arrow.rightFunc ⋙ (localReplacement s) ⋙
        toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I) :=
  NatIso.ofComponents (fun F => (originalKUnitPushoutComparisonHoIso s hHom) F.obj F.property)
    (by
      intro F G φ
      let H := toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)
      exact (H.map_comp _ _).symm.trans
        ((H.congr_map ((originalKUnitPushoutComparison_input s) φ.hom)).trans (H.map_comp _ _)))

/-- The ENTIRE full comparison hom is projection of SAME native pushout comparison. -/
theorem originalKUnitPushoutComparisonHoNatIso_hom
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b))
    (F : (originalLevelWeakArrowProperty (I := I)).FullSubcategory) :
    ((originalKUnitPushoutComparisonHoNatIso s hHom).hom.app F) =
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
        ((originalKUnitPushoutComparison s) F.obj) := rfl

/-- The ENTIRE inverse is projection of the actual chosen original target-unit extension. -/
theorem originalKUnitPushoutComparisonHoNatIso_inv
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b))
    (F : (originalLevelWeakArrowProperty (I := I)).FullSubcategory) :
    ((originalKUnitPushoutComparisonHoNatIso s hHom).inv.app F) =
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
        ((originalKUnitPushoutRetraction s hHom) F.obj F.property) := rfl

/-- EVERY complete original weak Arrow input preserves the full inverse extension in level Ho. -/
theorem originalKUnitPushoutComparisonHoNatIso_inv_input
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b))
    {F G : (originalLevelWeakArrowProperty (I := I)).FullSubcategory} (φ : F ⟶ G) :
    (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
        ((localReplacement s).map φ.hom.right) ≫ (originalKUnitPushoutComparisonHoNatIso s
          hHom).inv.app G =
      (originalKUnitPushoutComparisonHoNatIso s hHom).inv.app F ≫
        (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
          ((originalKUnitPushoutMap s) φ.hom) :=
  (originalKUnitPushoutComparisonHoNatIso s hHom).inv.naturality φ




private abbrev originalQ :=
  HomotopicalAlgebra.EnrichedProjective.Native.Replacement.cofibrantReplacement
    (A := I) (B := B)

private abbrev originalQCounit :=
  HomotopicalAlgebra.EnrichedProjective.Native.Replacement.cofibrantReplacementCounit
    (A := I) (B := B)

/-- The ENTIRE native comparison is SAME original L applied to SAME original I-Q counit. -/
def originalQLComparison : (cofibrantLocalReplacement s) ⟶ (localReplacement s) :=
  Functor.whiskerRight (Replacement.cofibrantReplacementCounit
    (A := I) (B := B)) (localReplacement s)

/-- Every whole comparison component retains the literal actual original I projection function. -/
theorem originalQLComparison_app (X : (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    (originalQLComparison s).app X =
      (localReplacement s).map ((Replacement.cofibrantReplacementCounit
      (A := I) (B := B)).app X) := rfl

/-- EVERY original input comparison is genuinely level weak by actual L base-W preservation. -/
theorem originalQLComparison_levelWeak
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b)) (X : (EnrichedFunctorCat
      PointedCGWH.{u, v} I)) :
    weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I) ((originalQLComparison s).app X) :=
  (originalKReplacement_preservesLevelWeak s hHom) _
    (Replacement.cofibrantReplacementCounit_mem_weakEquivalences X)

/-- EVERY actual input arrow retains the full original LQ/L/counit naturality square. -/
theorem originalQLComparison_input
    {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} I)} (f : X ⟶ Y) :
    (cofibrantLocalReplacement s).map f ≫ (originalQLComparison s).app Y =
      (originalQLComparison s).app X ≫ (localReplacement s).map f := (originalQLComparison
        s).naturality f

/-- BOTH complete original comparison directions give the whole native level Ho NatIso. -/
def originalQLHoNatIso
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b)) :
    (cofibrantLocalReplacement s) ⋙ toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I) ≅
      (localReplacement s) ⋙ toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I) := by
  let α := Functor.whiskerRight (originalQLComparison s)
    (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I))
  let _ : IsIso α := (NatTrans.isIso_iff_isIso_app α).mpr (fun X =>
    (weakEquivalence_iff_isIso_toHomotopyCategory_map _).mp ((originalQLComparison_levelWeak s
      hHom) X))
  exact asIso α

/-- The ENTIRE Ho comparison hom is projection of literal L of original I-Q counit. -/
theorem originalQLHoNatIso_hom
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b)) (X : (EnrichedFunctorCat
      PointedCGWH.{u, v} I)) :
    (originalQLHoNatIso s hHom).hom.app X =
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
        ((localReplacement s).map ((Replacement.cofibrantReplacementCounit
          (A := I) (B := B)).app X)) := rfl

/-- Every full original input preserves the entire inverse Ho comparison function. -/
theorem originalQLHoNatIso_inv_input
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b))
    {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} I)} (f : X ⟶ Y) :
    (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map ((localReplacement s).map
      f) ≫
        (originalQLHoNatIso s hHom).inv.app Y =
      (originalQLHoNatIso s hHom).inv.app X ≫
        (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
          ((cofibrantLocalReplacement s).map f) := (originalQLHoNatIso s hHom).inv.naturality f

/-- BOTH full original L and LQ detectors agree on EVERY actual native input arrow. -/
theorem originalKReplacementMap_weak_iff_IKMap
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b))
    {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} I)} (f : X ⟶ Y) :
    weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I) ((localReplacement s).map f) ↔
      weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I) ((cofibrantLocalReplacement
        s).map f) := by
  let W := weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I)
  have hX := (originalQLComparison_levelWeak s hHom) X
  have hY := (originalQLComparison_levelWeak s hHom) Y
  have hn := (originalQLComparison_input s) f
  constructor
  · intro hf
    have h := W.comp_mem _ _ hX hf
    rw [← hn] at h
    exact W.of_postcomp _ _ hY h
  · intro hf
    have h := W.comp_mem _ _ hf hY
    rw [hn] at h
    exact W.of_precomp _ _ hX h

/-- The literal original I-Q counit retains its full native K-unit square. -/
theorem originalIQCounit_KUnit_square (X : (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    (localReplacementUnit s).app ((Replacement.cofibrantReplacement
      (A := I) (B := B)).obj X) ≫
        (localReplacement s).map ((Replacement.cofibrantReplacementCounit
          (A := I) (B := B)).app X) =
      (Replacement.cofibrantReplacementCounit
        (A := I) (B := B)).app X ≫ (localReplacementUnit s).app X :=
  (localReplacementUnit_naturality s) ((Replacement.cofibrantReplacementCounit
    (A := I) (B := B)).app X)

/-- The complete Hom functions commute through the literal original Q/K unit square. -/
theorem originalQKUnitHoSquare (X Z : (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    (fun g : (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj
        ((localReplacement s).obj X) ⟶
        (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj Z =>
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
          ((localReplacementUnit s).app ((Replacement.cofibrantReplacement
            (A := I) (B := B)).obj X)) ≫
        ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
          ((localReplacement s).map ((Replacement.cofibrantReplacementCounit
            (A := I) (B := B)).app X)) ≫ g)) =
      (fun g : (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj
        ((localReplacement s).obj X) ⟶
        (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj Z =>
        (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
            ((Replacement.cofibrantReplacementCounit
              (A := I) (B := B)).app X) ≫
          ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
            ((localReplacementUnit s).app X) ≫ g)) := by
  funext g
  let H := toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)
  calc
    _ = H.map ((localReplacementUnit s).app ((Replacement.cofibrantReplacement
      (A := I) (B := B)).obj X) ≫
        (localReplacement s).map ((Replacement.cofibrantReplacementCounit
          (A := I) (B := B)).app X)) ≫ g := by
      rw [H.map_comp, Category.assoc]
    _ = H.map ((Replacement.cofibrantReplacementCounit
      (A := I) (B := B)).app X ≫ (localReplacementUnit s).app X) ≫ g :=
      congrArg (fun t => H.map t ≫ g) ((originalIQCounit_KUnit_square s) X)
    _ = _ := by rw [H.map_comp, Category.assoc]

/-- The given original Q-inverse/K-unit comparison followed by literal L(q_X) is the unit. -/
theorem originalQKComparison_unit
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b)) (X : (EnrichedFunctorCat
      PointedCGWH.{u, v} I)) :
    (cofibrantLocalComparison s).app X ≫ (originalQLHoNatIso s hHom).hom.app X =
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
        ((localReplacementUnit s).app X) := by
  let H := toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)
  let e : (Replacement.cofibrantReplacement
    (A := I) (B := B)) ⋙ H ≅ H := Replacement.cofibrantReplacementProjectionIso (B := B)
  have hq : H.map ((Replacement.cofibrantReplacementCounit
    (A := I) (B := B)).app X) = e.hom.app X :=
    (Replacement.cofibrantReplacementProjectionIso_hom_app X).symm
  rw [(cofibrantLocalComparison_app s), (originalQLHoNatIso_hom s hHom)]
  change (e.inv.app X ≫ H.map ((localReplacementUnit s).app ((Replacement.cofibrantReplacement
    (A := I) (B := B)).obj X))) ≫
    H.map ((localReplacement s).map ((Replacement.cofibrantReplacementCounit
      (A := I) (B := B)).app X)) = H.map ((localReplacementUnit s).app
      X)
  rw [Category.assoc, ← H.map_comp, (originalIQCounit_KUnit_square s), H.map_comp, hq,
    ← Category.assoc]
  rw [show e.inv.app X ≫ e.hom.app X = 𝟙 _ from (e.app X).inv_hom_id, Category.id_comp]

/-- The whole original native comparison transformation retains the actual unit function. -/
theorem originalQKComparison_wholeUnit
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b)) :
    (cofibrantLocalComparison s) ≫ (originalQLHoNatIso s hHom).hom =
      Functor.whiskerRight (localReplacementUnit s)
        (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)) := by
  apply NatTrans.ext
  funext X
  exact (originalQKComparison_unit s hHom) X

/-- Conjugacy retains every Hom input, not only the identity or a selected point. -/
theorem originalKUnitHomConjugacy
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b)) (X Z : (EnrichedFunctorCat
      PointedCGWH.{u, v} I)) :
    (fun g : (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj
        ((localReplacement s).obj X) ⟶
        (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj Z =>
      (cofibrantLocalComparison s).app X ≫ ((originalQLHoNatIso s hHom).hom.app X ≫ g)) =
      (fun g : (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj
        ((localReplacement s).obj X) ⟶
        (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj Z =>
        (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
          ((localReplacementUnit s).app X) ≫ g) := by
  funext g
  rw [← Category.assoc, (originalQKComparison_unit s hHom)]

/-- The actual original unit induces bijective level-Ho precomposition at every source. -/
theorem originalKUnit_precomp_bijective_allSource
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b))
    (X Z : (EnrichedFunctorCat PointedCGWH.{u, v} I)) (hZ : (generators s).rlp (toZero Z)) :
    Function.Bijective
      (fun g : (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj
          ((localReplacement s).obj X) ⟶
          (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj Z =>
        (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
          ((localReplacementUnit s).app X) ≫ g) := by
  have hq := (isIso_iff_coyoneda_map_bijective ((originalQLHoNatIso s hHom).hom.app X)).mp
    (by infer_instance)
    ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj Z)
  have h := ((cofibrantLocalComparison_precomp_bijective s) X Z hZ).comp hq
  change Function.Bijective
    (fun g : (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj
      ((localReplacement s).obj X) ⟶
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj Z =>
      (cofibrantLocalComparison s).app X ≫ ((originalQLHoNatIso s hHom).hom.app X ≫ g)) at h
  rw [(originalKUnitHomConjugacy s hHom)] at h
  exact h

/-- Every original source has its actual original unit in the complete K-local Hom-test class. -/
theorem originalKUnit_localTestEquivalence_allSource
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b))
    (X : (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    (localTestEquivalences s) ((localReplacementUnit s).app X) :=
  fun Z hZ => (originalKUnit_precomp_bijective_allSource s hHom) X Z
    ((lifting_toZero_iff_isOmega s Z).mpr hZ)

/-- The all-source original unit carries the entire ordinary level-Ho Hom equivalence. -/
def originalKUnitHomEquiv
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b))
    (X Z : (EnrichedFunctorCat PointedCGWH.{u, v} I)) (hZ : (generators s).rlp (toZero Z)) :
    ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj
        ((localReplacement s).obj X) ⟶
        (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj Z) ≃
      ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj X ⟶
        (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj Z) :=
  Equiv.ofBijective (fun g =>
    (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
      ((localReplacementUnit s).app X) ≫ g) ((originalKUnit_precomp_bijective_allSource s hHom) X
        Z hZ)

/-- The forward Hom function is literal precomposition by the original native unit. -/
theorem originalKUnitHomEquiv_apply
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b))
    (X Z : (EnrichedFunctorCat PointedCGWH.{u, v} I)) (hZ : (generators s).rlp (toZero Z))
    (g : (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj
      ((localReplacement s).obj X) ⟶
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj Z) :
    (originalKUnitHomEquiv s hHom) X Z hZ g =
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
        ((localReplacementUnit s).app X) ≫ g := rfl

/-- The complete inverse Hom function has the prescribed original unit composite. -/
theorem originalKUnitHomEquiv_symm_section
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b))
    (X Z : (EnrichedFunctorCat PointedCGWH.{u, v} I)) (hZ : (generators s).rlp (toZero Z))
    (g : (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj X ⟶
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj Z) :
    (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
        ((localReplacementUnit s).app X) ≫ ((originalKUnitHomEquiv s hHom) X Z hZ).symm g = g :=
  ((originalKUnitHomEquiv s hHom) X Z hZ).apply_symm_apply g

/-- Every actual source map preserves the entire forward unit Hom function. -/
theorem originalKUnitHomEquiv_source
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b))
    {X X' : (EnrichedFunctorCat PointedCGWH.{u, v} I)} (f : X' ⟶ X)
    (Z : (EnrichedFunctorCat PointedCGWH.{u, v} I)) (hZ : (generators s).rlp (toZero Z))
    (g : (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj
      ((localReplacement s).obj X) ⟶
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj Z) :
    (originalKUnitHomEquiv s hHom) X' Z hZ
        ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
          ((localReplacement s).map f) ≫ g) =
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map f ≫
        (originalKUnitHomEquiv s hHom) X Z hZ g := by
  let H := toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)
  change H.map ((localReplacementUnit s).app X') ≫ (H.map ((localReplacement s).map f) ≫ g) =
    H.map f ≫ (H.map ((localReplacementUnit s).app X) ≫ g)
  rw [← Category.assoc, ← H.map_comp, (localReplacementUnit_naturality s), H.map_comp,
    Category.assoc]

/-- Every actual source map also preserves the complete inverse unit Hom function. -/
theorem originalKUnitHomEquiv_source_symm
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b))
    {X X' : (EnrichedFunctorCat PointedCGWH.{u, v} I)} (f : X' ⟶ X)
    (Z : (EnrichedFunctorCat PointedCGWH.{u, v} I)) (hZ : (generators s).rlp (toZero Z))
    (g : (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj X ⟶
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj Z) :
    ((originalKUnitHomEquiv s hHom) X' Z hZ).symm
        ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map f ≫ g) =
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
        ((localReplacement s).map f) ≫ ((originalKUnitHomEquiv s hHom) X Z hZ).symm g := by
  apply ((originalKUnitHomEquiv s hHom) X' Z hZ).injective
  rw [Equiv.apply_symm_apply, (originalKUnitHomEquiv_source s hHom), Equiv.apply_symm_apply]

/-- Arbitrary ordinary Ho target maps preserve the complete original forward Hom function. -/
theorem originalKUnitHomEquiv_target
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b))
    (X Z Z' : (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (hZ : (generators s).rlp (toZero Z)) (hZ' : (generators s).rlp (toZero Z'))
    (f : (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj Z ⟶
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj Z')
    (g : (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj
      ((localReplacement s).obj X) ⟶
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj Z) :
    (originalKUnitHomEquiv s hHom) X Z' hZ' (g ≫ f) = (originalKUnitHomEquiv s hHom) X Z hZ g ≫ f
      := by
  rw [(originalKUnitHomEquiv_apply s hHom) X Z' hZ', (originalKUnitHomEquiv_apply s hHom) X Z hZ]
  exact (Category.assoc _ _ _).symm

/-- Arbitrary ordinary Ho target maps also preserve the entire inverse Hom function. -/
theorem originalKUnitHomEquiv_target_symm
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b))
    (X Z Z' : (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (hZ : (generators s).rlp (toZero Z)) (hZ' : (generators s).rlp (toZero Z'))
    (f : (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj Z ⟶
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj Z')
    (g : (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj X ⟶
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj Z) :
    ((originalKUnitHomEquiv s hHom) X Z' hZ').symm (g ≫ f) =
      ((originalKUnitHomEquiv s hHom) X Z hZ).symm g ≫ f := by
  apply ((originalKUnitHomEquiv s hHom) X Z' hZ').injective
  rw [Equiv.apply_symm_apply, (originalKUnitHomEquiv_target s hHom) X Z Z' hZ hZ' f,
    Equiv.apply_symm_apply]

/-- Literal L maps detect exactly the original local Hom tests on arbitrary endpoints. -/
theorem originalKReplacementMap_weak_iff_localTests
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b))
    {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} I)} (f : X ⟶ Y) :
    weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I) ((localReplacement s).map f) ↔
      (localTestEquivalences s) f :=
  ((originalKReplacementMap_weak_iff_IKMap s hHom) f).trans
    ((cofibrantLocalReplacement_map_weak_iff s) f)

/-- The whole original bare-L detected class is the same complete local Hom-test class. -/
theorem originalKDetectedWeak_eq_localTests
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b)) :
    (originalKDetectedWeakEquivalences s) = (localTestEquivalences s) := by
  funext X Y f
  exact propext ((originalKReplacementMap_weak_iff_localTests s hHom) f)

/-- The original local Hom tests use precisely the actual native Omega objects. -/
theorem originalLocalTestEquivalence_iff_omegaTests
    {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} I)} (f : X ⟶ Y) :
    (localTestEquivalences s) f ↔
      ∀ Z : (EnrichedFunctorCat PointedCGWH.{u, v} I), IsOmega s Z → Function.Bijective
        (fun g : (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj Y ⟶
            (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj Z =>
          (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map f ≫ g) :=
  Iff.rfl

/-- Every original unit has the complete native Omega-target tests, at every original source. -/
theorem originalKUnit_omegaTests_allSource
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b))
    (X Z : (EnrichedFunctorCat PointedCGWH.{u, v} I)) (hZ : IsOmega s Z) :
    Function.Bijective
      (fun g : (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj
          ((localReplacement s).obj X) ⟶
          (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj Z =>
        (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
          ((localReplacementUnit s).app X) ≫ g) :=
  (originalKUnit_precomp_bijective_allSource s hHom) X Z (((lifting_toZero_iff_isOmega s) Z).mpr hZ)

/-- Every actual original K-left arrow satisfies all local tests on arbitrary endpoints. -/
theorem originalKLeft_localTests
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b))
    {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} I)} (f : X ⟶ Y)
    (hf : (generators s).rlp.llp f) : (localTestEquivalences s) f :=
  ((originalKReplacementMap_weak_iff_localTests s hHom) f).mp
    ((originalKReplacementMap_modelWeak_of_KLeft s) f hf)

/-- The whole original K-left class lies in the complete all-source local Hom-test class. -/
theorem originalKLeft_le_localTests
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b)) : (generators s).rlp.llp ≤
      (localTestEquivalences s) :=
  fun _ _ f hf => (originalKLeft_localTests s hHom) f hf

/-- Every original K-left arrow has all native Omega-target Hom tests without source cofibrancy. -/
theorem originalKLeft_omegaTests
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b))
    {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} I)} (f : X ⟶ Y)
    (hf : (generators s).rlp.llp f) (Z : (EnrichedFunctorCat PointedCGWH.{u, v} I)) (hZ : IsOmega
      s Z) :
    Function.Bijective
      (fun g : (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj Y ⟶
          (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj Z =>
        (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map f ≫ g) :=
  ((originalLocalTestEquivalence_iff_omegaTests s) f).mp ((originalKLeft_localTests s hHom) f hf)
    Z hZ

/-- Every actual K factorization injection has those same complete local tests. -/
theorem originalKFactorization_i_localTests
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b))
    (F : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    (localTestEquivalences s) ((factorizationData s).i.app F) :=
  (originalKLeft_localTests s hHom) _ ((factorizationData s).hi F)

/-- The original full K generator family lies in the same local Hom-test class. -/
theorem originalKGenerators_le_localTests
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b)) : (generators s) ≤
      (localTestEquivalences s) :=
  fun _ _ f hf => (originalKLeft_localTests s hHom) f ((generators s).le_llp_rlp f hf)

end HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK

namespace HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK

open HomotopicalAlgebra.EnrichedProjective.Native.Diagrams

variable {I L : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  (s : NativeStabilizationFamily.{u, v} I L)
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- The actual bare K action on every original level-Ho morphism, from proved weak preservation. -/
def originalBareKReplacementHo
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b)) :
    HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I) ⥤
      HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I) :=
  CategoryTheory.Functor.CoaugmentedLocalization.localizedFunctor
    (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I)) (localReplacement s)
    (fun {X Y} f hf =>
      originalKReplacement_preservesLevelWeak s hHom (X := X) (Y := Y) f hf)

/-- Every projected source arrow retains its original bare K replacement map. -/
theorem originalBareKReplacementHo_map_projected
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b))
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y) :
    (originalBareKReplacementHo s hHom).map
        ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map f) =
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
        ((localReplacement s).map f) :=
  CategoryTheory.Functor.CoaugmentedLocalization.localizedFunctor_map
    (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I)) (localReplacement s)
    (fun {X Y} f hf =>
      originalKReplacement_preservesLevelWeak s hHom (X := X) (Y := Y) f hf) f

/-- The original raw K unit descends naturally on all ordinary level-Ho source arrows. -/
def originalBareKReplacementHoUnit
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b)) :
    𝟭 (HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)) ⟶
      originalBareKReplacementHo s hHom :=
  CategoryTheory.Functor.CoaugmentedLocalization.localizedUnit
    (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I)) (localReplacement s)
    (localReplacementUnit s) (fun {X Y} f hf =>
      originalKReplacement_preservesLevelWeak s hHom (X := X) (Y := Y) f hf)

/-- Every original source object keeps the same original K-unit under level projection. -/
theorem originalBareKReplacementHoUnit_app_projected
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b))
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    (originalBareKReplacementHoUnit s hHom).app
        ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj X) =
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
        ((localReplacementUnit s).app X) :=
  CategoryTheory.Functor.CoaugmentedLocalization.localizedUnit_app
    (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I)) (localReplacement s)
    (localReplacementUnit s) (fun {X Y} f hf =>
      originalKReplacement_preservesLevelWeak s hHom (X := X) (Y := Y) f hf) X

/-- Arbitrary ordinary-Ho source morphisms keep the complete original unit square. -/
theorem originalBareKReplacementHoUnit_naturality
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b))
    {X Y : HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)} (f : X ⟶ Y) :
    f ≫ (originalBareKReplacementHoUnit s hHom).app Y =
      (originalBareKReplacementHoUnit s hHom).app X ≫
        (originalBareKReplacementHo s hHom).map f :=
  (originalBareKReplacementHoUnit s hHom).naturality f

/-- The complete two actual iterated unit functions agree on all ordinary Ho objects. -/
theorem originalBareKReplacementHo_wholeUnitCoherence
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b)) :
    (fun X => (originalBareKReplacementHo s hHom).map
        ((originalBareKReplacementHoUnit s hHom).app X)) =
      fun X => (originalBareKReplacementHoUnit s hHom).app
        ((originalBareKReplacementHo s hHom).obj X) := by
  funext X
  exact CategoryTheory.Functor.CoaugmentedLocalization.localizedFunctor_unit_eq
    (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I)) (localReplacement s)
    (localReplacementUnit s) (fun {X Y} f hf =>
      originalKReplacement_preservesLevelWeak s hHom (X := X) (Y := Y) f hf)
    (originalKUnitAtLocalReplacement_modelWeak s) (originalKReplacementMapUnit_modelWeak s) X

/-- The actual unit Iso at a local target retains the same original K-unit arrow. -/
def originalBareKTargetUnitHoIso
    (Z : EnrichedFunctorCat PointedCGWH.{u, v} I) (hZ : (generators s).rlp (toZero Z)) :
    (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj Z ≅
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj
        ((localReplacement s).obj Z) :=
  Localization.Construction.wIso ((localReplacementUnit s).app Z)
    (originalKUnitOnOmega_modelWeak s Z ((lifting_toZero_iff_isOmega s Z).mp hZ))

/-- The full original all-source Equiv equals the computed localization Equiv, without new
choice. -/
theorem originalKUnitHomEquiv_eq_bareKLocalizedHomEquiv
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b))
    (X Z : EnrichedFunctorCat PointedCGWH.{u, v} I) (hZ : (generators s).rlp (toZero Z)) :
    originalKUnitHomEquiv s hHom X Z hZ =
      CategoryTheory.Functor.CoaugmentedLocalization.unitHomEquiv
        (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I)) (localReplacement s)
        (localReplacementUnit s) (fun {X Y} f hf =>
      originalKReplacement_preservesLevelWeak s hHom (X := X) (Y := Y) f hf)
        (originalKUnitAtLocalReplacement_modelWeak s) (originalKReplacementMapUnit_modelWeak s)
        X Z (originalKUnitOnOmega_modelWeak s Z ((lifting_toZero_iff_isOmega s Z).mp hZ)) := by
  apply Equiv.ext
  intro g
  rw [originalKUnitHomEquiv_apply,
    CategoryTheory.Functor.CoaugmentedLocalization.unitHomEquiv_apply]

/-- The complete original inverse uses the actual bare K action on every ordinary Ho input. -/
theorem originalKUnitHomEquiv_wholeComputedInverse
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b))
    (X Z : EnrichedFunctorCat PointedCGWH.{u, v} I) (hZ : (generators s).rlp (toZero Z)) :
    (fun g => ((originalKUnitHomEquiv s hHom X Z hZ).symm g)) =
      fun g => (originalBareKReplacementHo s hHom).map g ≫
        (originalBareKTargetUnitHoIso s Z hZ).inv := by
  funext g
  rw [originalKUnitHomEquiv_eq_bareKLocalizedHomEquiv]
  exact CategoryTheory.Functor.CoaugmentedLocalization.unitHomEquiv_symm_apply
    (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I)) (localReplacement s)
    (localReplacementUnit s) (fun {X Y} f hf =>
      originalKReplacement_preservesLevelWeak s hHom (X := X) (Y := Y) f hf)
    (originalKUnitAtLocalReplacement_modelWeak s) (originalKReplacementMapUnit_modelWeak s)
    X Z (originalKUnitOnOmega_modelWeak s Z ((lifting_toZero_iff_isOmega s Z).mp hZ)) g

/-- Every arbitrary ordinary-Ho source arrow preserves the original complete forward Hom
function. -/
theorem originalKUnitHomEquiv_source_Ho
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b))
    (X X' Z : EnrichedFunctorCat PointedCGWH.{u, v} I)
    (a : (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj X' ⟶
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj X)
    (hZ : (generators s).rlp (toZero Z))
    (g : (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj
        ((localReplacement s).obj X) ⟶
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj Z) :
    originalKUnitHomEquiv s hHom X' Z hZ
        ((originalBareKReplacementHo s hHom).map a ≫ g) =
      a ≫ originalKUnitHomEquiv s hHom X Z hZ g := by
  rw [originalKUnitHomEquiv_eq_bareKLocalizedHomEquiv,
    originalKUnitHomEquiv_eq_bareKLocalizedHomEquiv]
  exact CategoryTheory.Functor.CoaugmentedLocalization.unitHomEquiv_source_hom
    (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I)) (localReplacement s)
    (localReplacementUnit s) (fun {X Y} f hf =>
      originalKReplacement_preservesLevelWeak s hHom (X := X) (Y := Y) f hf)
    (originalKUnitAtLocalReplacement_modelWeak s) (originalKReplacementMapUnit_modelWeak s)
    X X' Z a (originalKUnitOnOmega_modelWeak s Z ((lifting_toZero_iff_isOmega s Z).mp hZ)) g

/-- Every arbitrary ordinary-Ho source arrow preserves the full original inverse Hom function. -/
theorem originalKUnitHomEquiv_source_Ho_symm
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b))
    (X X' Z : EnrichedFunctorCat PointedCGWH.{u, v} I)
    (a : (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj X' ⟶
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj X)
    (hZ : (generators s).rlp (toZero Z))
    (g : (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj X ⟶
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj Z) :
    (originalKUnitHomEquiv s hHom X' Z hZ).symm (a ≫ g) =
      (originalBareKReplacementHo s hHom).map a ≫
        (originalKUnitHomEquiv s hHom X Z hZ).symm g := by
  rw [originalKUnitHomEquiv_eq_bareKLocalizedHomEquiv,
    originalKUnitHomEquiv_eq_bareKLocalizedHomEquiv]
  exact CategoryTheory.Functor.CoaugmentedLocalization.unitHomEquiv_source_hom_symm
    (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I)) (localReplacement s)
    (localReplacementUnit s) (fun {X Y} f hf =>
      originalKReplacement_preservesLevelWeak s hHom (X := X) (Y := Y) f hf)
    (originalKUnitAtLocalReplacement_modelWeak s) (originalKReplacementMapUnit_modelWeak s)
    X X' Z a (originalKUnitOnOmega_modelWeak s Z ((lifting_toZero_iff_isOmega s Z).mp hZ)) g

/-- The original full inverse is characterized by the same original unit composite. -/
theorem originalKUnitHomEquiv_characteristic
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b))
    (X Z : EnrichedFunctorCat PointedCGWH.{u, v} I) (hZ : (generators s).rlp (toZero Z))
    (f : (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj X ⟶
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj Z)
    (g : (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj
        ((localReplacement s).obj X) ⟶
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj Z) :
    (originalKUnitHomEquiv s hHom X Z hZ).symm f = g ↔
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
        ((localReplacementUnit s).app X) ≫ g = f := by
  rw [originalKUnitHomEquiv_eq_bareKLocalizedHomEquiv]
  exact CategoryTheory.Functor.CoaugmentedLocalization.unitHomEquiv_characteristic
    (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I)) (localReplacement s)
    (localReplacementUnit s) (fun {X Y} f hf =>
      originalKReplacement_preservesLevelWeak s hHom (X := X) (Y := Y) f hf)
    (originalKUnitAtLocalReplacement_modelWeak s) (originalKReplacementMapUnit_modelWeak s)
    X Z (originalKUnitOnOmega_modelWeak s Z ((lifting_toZero_iff_isOmega s Z).mp hZ)) f g

end HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK
