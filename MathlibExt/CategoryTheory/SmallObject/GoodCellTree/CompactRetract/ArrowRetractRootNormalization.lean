/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.CompactRetract.OriginalRetractSplitIso
public import MathlibExt.CategoryTheory.SmallObject.CoherentRetracts.SuccessorGeometry
public import Mathlib.CategoryTheory.MorphismProperty.Retract
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Original Arrow retracts with the original source fixed

Push out the original source projection of an actual Arrow retract. The
original two squares and retract equations construct the new inclusion,
projection and root-fixed idempotent. Pasting preserves the same original
compact arrow. Both selected endpoint isomorphisms use these actual maps.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe u v

namespace CategoryTheory.SmallObject.ArrowRetractRootNormalization

open Limits

variable {C : Type u} [Category.{v} C] [HasPushouts C]
  {A B X Y : C} {i : A ⟶ B} {g : X ⟶ Y} (R : RetractArrow g i)

/-- The idempotent is formed from the same actual normalized split maps. -/
abbrev idempotent : obj R ⟶ obj R := projection R ≫ inclusion R

/-- The original target retract equation proves actual idempotence. -/
theorem idempotent_idempotent : idempotent R ≫ idempotent R = idempotent R :=
  OriginalRetractSplitIso.idempotent_idempotent
    (inclusion R) (projection R) (inclusion_projection R)

/-- The original source is fixed, without an identity-source input premise. -/
theorem root_idempotent : root R ≫ idempotent R = root R := by
  rw [idempotent, ← Category.assoc, root_projection, arrow_inclusion]

variable {D E : C} (u : D ⟶ A) (f : D ⟶ E) (c : E ⟶ B)
  (H : IsPushout u f i c)

include H in
/-- Pasting gives a pushout of the SAME original f along the original source projection. -/
theorem originalPushout :
    IsPushout (u ≫ R.r.left) f (root R) (c ≫ oldTargetMap R) :=
  H.paste_horiz (IsPushout.of_hasPushout R.r.left i)

/-- The original pasted UP constructs the complete native comparison Iso. -/
def nativeIso : pushout (u ≫ R.r.left) f ≅ obj R :=
  (originalPushout R u f c H).isoPushout.symm

/-- Its actual root component is the same original normalized source map. -/
theorem nativeIso_root :
    pushout.inl (u ≫ R.r.left) f ≫ (nativeIso R u f c H).hom = root R :=
  (originalPushout R u f c H).inl_isoPushout_inv

/-- Its actual local component retains the original f-target map c. -/
theorem nativeIso_local :
    pushout.inr (u ≫ R.r.left) f ≫ (nativeIso R u f c H).hom = c ≫ oldTargetMap R :=
  (originalPushout R u f c H).inr_isoPushout_inv

/-- The inverse comparison retains the original normalized root function. -/
theorem root_nativeIso_inv :
    root R ≫ (nativeIso R u f c H).inv = pushout.inl (u ≫ R.r.left) f :=
  (originalPushout R u f c H).inl_isoPushout_hom

/-- The inverse local comparison recovers the same original native f inclusion. -/
theorem local_nativeIso_inv :
    (c ≫ oldTargetMap R) ≫ (nativeIso R u f c H).inv =
      pushout.inr (u ≫ R.r.left) f :=
  (originalPushout R u f c H).inr_isoPushout_hom

/-- The exact old projection transported through this derived native Iso. -/
def nativeProjection : pushout (u ≫ R.r.left) f ⟶ Y :=
  (nativeIso R u f c H).hom ≫ projection R

/-- The exact old inclusion transported through the inverse derived Iso. -/
def nativeInclusion : Y ⟶ pushout (u ≫ R.r.left) f :=
  inclusion R ≫ (nativeIso R u f c H).inv

/-- The same original actual split survives native endpoint transport. -/
theorem nativeInclusion_projection :
    nativeInclusion R u f c H ≫ nativeProjection R u f c H = 𝟙 Y := by
  calc
    _ = inclusion R ≫
        (((nativeIso R u f c H).inv ≫ (nativeIso R u f c H).hom) ≫ projection R) := by
      simp only [nativeInclusion, nativeProjection, Category.assoc]
    _ = inclusion R ≫ projection R := by rw [Iso.inv_hom_id, Category.id_comp]
    _ = _ := inclusion_projection R

/-- The original given arrow is the exact native-root/projection composite. -/
theorem nativeRoot_projection :
    pushout.inl (u ≫ R.r.left) f ≫ nativeProjection R u f c H = g := by
  rw [nativeProjection, ← Category.assoc, nativeIso_root, root_projection]

/-- The original given arrow followed by the exact native inclusion is the native root. -/
theorem arrow_nativeInclusion :
    g ≫ nativeInclusion R u f c H = pushout.inl (u ≫ R.r.left) f := by
  rw [nativeInclusion, ← Category.assoc, arrow_inclusion, root_nativeIso_inv]

/-- The native idempotent still uses the same original split through the derived Iso. -/
abbrev nativeIdempotent : pushout (u ≫ R.r.left) f ⟶ pushout (u ≫ R.r.left) f :=
  nativeProjection R u f c H ≫ nativeInclusion R u f c H

/-- Its idempotence is derived from the actual transported original retract. -/
theorem nativeIdempotent_idempotent :
    nativeIdempotent R u f c H ≫ nativeIdempotent R u f c H =
      nativeIdempotent R u f c H :=
  OriginalRetractSplitIso.idempotent_idempotent
    (nativeInclusion R u f c H) (nativeProjection R u f c H)
    (nativeInclusion_projection R u f c H)

/-- The native idempotent fixes the same original source root. -/
theorem nativeRoot_idempotent :
    pushout.inl (u ≫ R.r.left) f ≫ nativeIdempotent R u f c H =
      pushout.inl (u ≫ R.r.left) f := by
  rw [nativeIdempotent, ← Category.assoc, nativeRoot_projection, arrow_nativeInclusion]

section Coequalizers

variable [HasCoequalizers C]

/-- The selected coequalizer of the original normalized idempotent is the ACTUAL given target. -/
def endpointIso : IdempotentCoequalizerSplit.obj (idempotent R) ≅ Y :=
  OriginalRetractSplitIso.iso (inclusion R) (projection R) (inclusion_projection R)

/-- The whole endpoint comparison recovers the same original normalized projection. -/
theorem endpoint_projection :
    IdempotentCoequalizerSplit.projection (idempotent R) ≫ (endpointIso R).hom =
      projection R :=
  OriginalRetractSplitIso.projection_iso_hom
    (inclusion R) (projection R) (inclusion_projection R)

/-- Its root equation recovers the original given arrow g, with its original target Y. -/
theorem root_endpoint :
    root R ≫ IdempotentCoequalizerSplit.projection (idempotent R) ≫
      (endpointIso R).hom = g := by
  rw [endpoint_projection, root_projection]

/-- The native selected coequalizer is also identified by the same original transported split. -/
def nativeEndpointIso :
    IdempotentCoequalizerSplit.obj (nativeIdempotent R u f c H) ≅ Y :=
  OriginalRetractSplitIso.iso
    (nativeInclusion R u f c H) (nativeProjection R u f c H)
    (nativeInclusion_projection R u f c H)

/-- Its whole projection comparison remains the actual original transported projection. -/
theorem nativeEndpoint_projection :
    IdempotentCoequalizerSplit.projection (nativeIdempotent R u f c H) ≫
      (nativeEndpointIso R u f c H).hom = nativeProjection R u f c H :=
  OriginalRetractSplitIso.projection_iso_hom
    (nativeInclusion R u f c H) (nativeProjection R u f c H)
    (nativeInclusion_projection R u f c H)

end Coequalizers

end CategoryTheory.SmallObject.ArrowRetractRootNormalization
