/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.NativeFilteredDeRhamOutputs
public import MathlibExt.CategoryTheory.SheafScalarQuotients
public import Mathlib.CategoryTheory.Sites.Pullback

/-!
# Original inverse-image rings and differential section units

The relative base ring is the actual native inverse image of the
original base ring sheaf. Its ring arrow to the source is the native
adjunction mate of the original ringed-site scalar map. No replacement
relative scalar ring is supplied.

The exterior unit is the original native sheafification unit of the
completed semilinear exterior presheaf.

Sources: native Mathlib site and module adjunctions, Apache 2.0, revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`; completed exterior source
port from AxiomMath/Stacks `c496df0d9beea9deaeabcea8492605f9a0a2313b`,
Apache 2.0. Scholze, arXiv:1205.3463v2, Definitions 6.8 and 7.4.
-/

set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.NativeRingInverseImages

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.CategoryTheory.MonoidalCategory
open RingedDerivedCoefficientOperations RingSheafModuleTensors

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {T : GrothendieckTopology D}
  (G : C ⥤ D) [G.IsContinuous J T]
  [(G.sheafPushforwardContinuous CommRingCat.{1} J T).IsRightAdjoint]
  (S : Sheaf J CommRingCat.{1})

def inverseRing : Sheaf T CommRingCat.{1} :=
  (G.sheafPullback CommRingCat.{1} J T).obj S

def inverseUnit : S ⟶
    (G.sheafPushforwardContinuous CommRingCat.{1} J T).obj (inverseRing G S) :=
  (G.sheafAdjunctionContinuous CommRingCat.{1} J T).unit.app S

/-- The original scalar ring arrow is the native inverse-image adjunction mate. -/
def inverseScalar (O : Sheaf T CommRingCat.{1})
    (φ : S ⟶ (G.sheafPushforwardContinuous CommRingCat.{1} J T).obj O) :
    inverseRing G S ⟶ O :=
  ((G.sheafAdjunctionContinuous CommRingCat.{1} J T).homEquiv S O).symm φ

section Constants

variable [HasSheafify J CommRingCat.{1}] [HasSheafify T CommRingCat.{1}]
  (A : Type) [CommRing A]

/-- The original constant sections on every G-image object, followed by native sheafification. -/
def constantPushRaw : ((Functor.const Cᵒᵖ).obj (CommRingCat.of (ULift.{1} A))) ⟶
    ((G.sheafPushforwardContinuous CommRingCat.{1} J T).obj
      (SheafScalarQuotients.constantRing (J := T) A)).obj where
  app U := (toSheafify T ((Functor.const Dᵒᵖ).obj (CommRingCat.of (ULift.{1} A)))).app (G.op.obj U)
  naturality {U V} f := by
    simpa [SheafScalarQuotients.constantRing] using (toSheafify T ((Functor.const Dᵒᵖ).obj
      (CommRingCat.of (ULift.{1} A)))).naturality (G.op.map f)

def constantPush : SheafScalarQuotients.constantRing (J := J) A ⟶
    (G.sheafPushforwardContinuous CommRingCat.{1} J T).obj
      (SheafScalarQuotients.constantRing (J := T) A) :=
  ((sheafificationAdjunction J CommRingCat.{1}).homEquiv
    ((Functor.const Cᵒᵖ).obj (CommRingCat.of (ULift.{1} A)))
    ((G.sheafPushforwardContinuous CommRingCat.{1} J T).obj
      (SheafScalarQuotients.constantRing (J := T) A))).symm
        (constantPushRaw (J := J) (T := T) G A)

/-- The constant inverse-image map is the native adjunction mate, before its IsIso source proof. -/
def constantInverseMap : inverseRing G (SheafScalarQuotients.constantRing (J := J) A) ⟶
    SheafScalarQuotients.constantRing (J := T) A :=
  inverseScalar G (SheafScalarQuotients.constantRing (J := J) A)
    (SheafScalarQuotients.constantRing (J := T) A) (constantPush (J := J) (T := T) G A)

end Constants

section ModuleInverseImages

variable [UnivLE.{max u₁ v₁, 1}] [UnivLE.{max u₂ v₂, 1}]
  (R : Sheaf T CommRingCat.{1})
  (φ : S ⟶ (G.sheafPushforwardContinuous CommRingCat.{1} J T).obj R)

/-- Native module inverse images also retain DIFFERENT etale and formal pro-site universes. -/
def moduleScalar : moduleRing.{v₁, u₁} S ⟶
    (G.sheafPushforwardContinuous RingCat.{1} J T).obj (moduleRing.{v₂, u₂} R) :=
  ObjectProperty.homMk
    { app U := (forget₂ CommRingCat.{1} RingCat.{1}).map (φ.hom.app U)
      naturality {U V} f := by
        ext x
        exact congrArg (fun g => g.hom x) (φ.hom.naturality f) }

def modulePushforward : Modules.{v₂, u₂} R ⥤ Modules.{v₁, u₁} S :=
  SheafOfModules.pushforward.{1} (moduleScalar G S R φ)

instance modulePushforward_additive : (modulePushforward G S R φ).Additive where
  map_add := by intros; rfl

variable [(modulePushforward G S R φ).IsRightAdjoint]

local instance nativeModulePushforwardRightAdjoint :
    (SheafOfModules.pushforward.{1} (moduleScalar G S R φ)).IsRightAdjoint := by
  change (modulePushforward G S R φ).IsRightAdjoint
  infer_instance

def modulePullback : Modules.{v₁, u₁} S ⥤ Modules.{v₂, u₂} R :=
  SheafOfModules.pullback.{1} (moduleScalar G S R φ)

def moduleAdjunction : modulePullback G S R φ ⊣ modulePushforward G S R φ :=
  SheafOfModules.pullbackPushforwardAdjunction.{1} (moduleScalar G S R φ)

instance modulePullback_additive : (modulePullback G S R φ).Additive :=
  (moduleAdjunction G S R φ).left_adjoint_additive

end ModuleInverseImages

section Exterior

variable [UnivLE.{max u₁ v₁, 1}]
  [HasSheafify J AddCommGrpCat.{1}] [J.WEqualsLocallyBijective AddCommGrpCat.{1}]
  (O : Sheaf J CommRingCat.{1}) (Ω : Modules O)

/-- Native sheafified tensor map on both original factors. -/
def tensorMap {M M' N N' : Modules O} (m : M ⟶ M') (n : N ⟶ N') :
    tensor O M N ⟶ tensor O M' N' :=
  (moduleSheafification O).map
    (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := O.obj) m.val n.val)

/-- The exact sectionwise exterior unit, before any affinoid source identification. -/
def exteriorUnit (n : ℕ) (U : Cᵒᵖ) :
    (⋀[O.obj.obj U]^n (Ω.val.obj U)) →ₗ[O.obj.obj U] (exterior O Ω n).val.obj U :=
  (((PresheafOfModules.sheafificationAdjunction (R := moduleRing O)
    (𝟙 (moduleRing O).obj)).unit.app
      (PresheafOfModules.extPow.{v₁, u₁, 1, 0} (O := O.obj) n Ω.val)).app U).hom

end Exterior

end MathlibExt.CategoryTheory.NativeRingInverseImages
