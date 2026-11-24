/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.NativeRingInverseImages

/-!
# Source-normalized etale/pro inverse-image transfer of original complexes

The ring inverse-image square is fixed by every original native
adjunction unit and the actual site-functor square. Its ring arrow is
then the native adjunction mate. Module transfer and filtered transfer
are the actual native inverse image at the COCHAIN level. No higher
de Rham output or replacement coefficient complex is supplied.

The four site categories may have different universes; this is needed
for original etale objects and full formal pro-morphisms.

References: Scholze, arXiv:1205.3463v2, Definition 6.8 and Remark 7.12;
native Mathlib site/module adjunctions, Apache 2.0, revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`.
-/

set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.RingedComplexInverseImageSources

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open RingedDerivedCoefficientOperations NativeRingInverseImages NativeFilteredDeRhamOutputs

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C₁ : Type u₁} [Category.{v₁} C₁] {D₁ : Type u₂} [Category.{v₂} D₁]
  {C₂ : Type u₃} [Category.{v₃} C₂] {D₂ : Type u₄} [Category.{v₄} D₂]
  {J₁ : GrothendieckTopology C₁} {T₁ : GrothendieckTopology D₁}
  {J₂ : GrothendieckTopology C₂} {T₂ : GrothendieckTopology D₂}
  (G₁ : C₁ ⥤ D₁) (G₂ : C₂ ⥤ D₂) (FY : C₁ ⥤ C₂) (FX : D₁ ⥤ D₂)
  [G₁.IsContinuous J₁ T₁] [G₂.IsContinuous J₂ T₂] [FY.IsContinuous J₁ J₂] [FX.IsContinuous T₁ T₂]
  [(G₁.sheafPushforwardContinuous CommRingCat.{1} J₁ T₁).IsRightAdjoint]
  [(G₂.sheafPushforwardContinuous CommRingCat.{1} J₂ T₂).IsRightAdjoint]
  [(FY.sheafPushforwardContinuous CommRingCat.{1} J₁ J₂).IsRightAdjoint]
  [(FX.sheafPushforwardContinuous CommRingCat.{1} T₁ T₂).IsRightAdjoint]

abbrev ringInverse (F : C₁ ⥤ D₁) [F.IsContinuous J₁ T₁]
    [(F.sheafPushforwardContinuous CommRingCat.{1} J₁ T₁).IsRightAdjoint] :=
  F.sheafPullback CommRingCat.{1} J₁ T₁

/-- The original ring inverse images and actual site square, fixed on ALL original ring sections. -/
structure RingSquare where
  site : FY ⋙ G₂ ≅ G₁ ⋙ FX
  ordinary : FY.sheafPullback CommRingCat.{1} J₁ J₂ ⋙ G₂.sheafPullback CommRingCat.{1} J₂ T₂ ≅
    G₁.sheafPullback CommRingCat.{1} J₁ T₁ ⋙ FX.sheafPullback CommRingCat.{1} T₁ T₂
  unit_source : ∀ (S : Sheaf J₁ CommRingCat.{1}) (U : C₁ᵒᵖ) (a : S.obj.obj U),
    ((ordinary.hom.app S).hom.app (op (G₂.obj (FY.obj U.unop)))).hom
      (((inverseUnit (J := J₂) (T := T₂) G₂ (inverseRing (J := J₁) (T := J₂) FY S)).hom.app (op (FY.obj U.unop))).hom
        (((inverseUnit (J := J₁) (T := J₂) FY S).hom.app U).hom a)) =
      ((inverseRing (J := T₁) (T := T₂) FX (inverseRing (J := J₁) (T := T₁) G₁ S)).obj.map (site.hom.app U.unop).op).hom
        (((inverseUnit (J := T₁) (T := T₂) FX (inverseRing (J := J₁) (T := T₁) G₁ S)).hom.app (op (G₁.obj U.unop))).hom
          (((inverseUnit (J := J₁) (T := T₁) G₁ S).hom.app U).hom a))

variable (Q : RingSquare (J₁ := J₁) (T₁ := T₁) (J₂ := J₂) (T₂ := T₂) G₁ G₂ FY FX) (S : Sheaf J₁ CommRingCat.{1})

/-- The actual ring arrow for COCHAIN inverse image, formed from the original native ring unit. -/
def transferScalar : inverseRing (J := J₁) (T := T₁) G₁ S ⟶
    (FX.sheafPushforwardContinuous CommRingCat.{1} T₁ T₂).obj (inverseRing (J := J₂) (T := T₂) G₂ (inverseRing (J := J₁) (T := J₂) FY S)) :=
  inverseUnit (J := T₁) (T := T₂) FX (inverseRing (J := J₁) (T := T₁) G₁ S) ≫
    (FX.sheafPushforwardContinuous CommRingCat.{1} T₁ T₂).map (Q.ordinary.inv.app S)

variable [UnivLE.{max u₂ v₂, 1}] [UnivLE.{max u₄ v₄, 1}]
  [(modulePushforward FX (inverseRing (J := J₁) (T := T₁) G₁ S) (inverseRing (J := J₂) (T := T₂) G₂ (inverseRing (J := J₁) (T := J₂) FY S))
    (transferScalar (J₁ := J₁) (T₁ := T₁) (J₂ := J₂) (T₂ := T₂) G₁ G₂ FY FX Q S)).IsRightAdjoint]

def moduleTransfer := modulePullback FX (inverseRing (J := J₁) (T := T₁) G₁ S) (inverseRing (J := J₂) (T := T₂) G₂ (inverseRing (J := J₁) (T := J₂) FY S))
  (transferScalar (J₁ := J₁) (T₁ := T₁) (J₂ := J₂) (T₂ := T₂) G₁ G₂ FY FX Q S)

local instance moduleTransferAdditive :
    (moduleTransfer (J₁ := J₁) (T₁ := T₁) (J₂ := J₂) (T₂ := T₂) G₁ G₂ FY FX Q S).Additive := by
  unfold moduleTransfer
  infer_instance

variable [HasSheafify T₁ AddCommGrpCat.{1}] [T₁.WEqualsLocallyBijective AddCommGrpCat.{1}]
  [HasSheafify T₂ AddCommGrpCat.{1}] [T₂.WEqualsLocallyBijective AddCommGrpCat.{1}]

def cochainTransfer := (moduleTransfer (J₁ := J₁) (T₁ := T₁) (J₂ := J₂) (T₂ := T₂) G₁ G₂ FY FX Q S).mapCochainComplexPlus

variable [(cochainTransfer (J₁ := J₁) (T₁ := T₁) (J₂ := J₂) (T₂ := T₂) G₁ G₂ FY FX Q S).PreservesMonomorphisms]

/-- Native transfer of the ORIGINAL filtered complex, before derived pushforward and cohomology. -/
def filteredTransfer (F : FilteredComplex.{v₂, u₂} (inverseRing (J := J₁) (T := T₁) G₁ S)) :
    FilteredComplex.{v₄, u₄} (inverseRing (J := J₂) (T := T₂) G₂ (inverseRing (J := J₁) (T := J₂) FY S)) where
  total := (cochainTransfer (J₁ := J₁) (T₁ := T₁) (J₂ := J₂) (T₂ := T₂) G₁ G₂ FY FX Q S).obj F.total
  filtered := F.filtered ⋙ cochainTransfer (J₁ := J₁) (T₁ := T₁) (J₂ := J₂) (T₂ := T₂) G₁ G₂ FY FX Q S
  inclusion :=
    { app j := (cochainTransfer (J₁ := J₁) (T₁ := T₁) (J₂ := J₂) (T₂ := T₂) G₁ G₂ FY FX Q S).map (F.inclusion.app j)
      naturality {j k} h := by
        have q := F.inclusion.naturality h
        simpa using congrArg (cochainTransfer (J₁ := J₁) (T₁ := T₁) (J₂ := J₂) (T₂ := T₂) G₁ G₂ FY FX Q S).map q }
  mono j := by
    letI := F.mono j
    infer_instance

end MathlibExt.CategoryTheory.RingedComplexInverseImageSources
