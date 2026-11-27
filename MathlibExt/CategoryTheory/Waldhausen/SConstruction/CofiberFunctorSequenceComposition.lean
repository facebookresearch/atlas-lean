/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberFunctorSequence

/-!
# Exact composition of Waldhausen cofiber-functor sequences

Let B,C carry chosen zeros and Waldhausen structures without gluing. A cofiber-functor sequence
consists of exact F₀,F₁,F₂:B→C and natural i,p that give objectwise cofiber sequences, with a
cofibration base corner for each source cofibration.

Exact precomposition by L:A→B preserves this condition. For exact J:C→D, the image of each
source base pushout is compared to the selected target pushout by the canonical isomorphism
preserving both legs. The target corner is the transported source corner, hence a cofibration
for each source cofibration. This gives exact postcomposition of the whole sequence.

The object and Hom universes of A,B,C,D, and their chosen zero objects, are independent.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uA vA uB vB uC vC uD vD

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace CategoryTheory.Waldhausen.SConstruction.IsWaldhausenCofiberFunctorSequence

variable {B : Type uB} [Category.{vB} B] [HasZeroObject B] [WaldhausenCategoryWithoutGluing B]
variable {C : Type uC} [Category.{vC} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]
variable {D : Type uD} [Category.{vD} D] [HasZeroObject D] [WaldhausenCategoryWithoutGluing D]
variable {F₀ F₁ F₂ : B ⥤ C} {i : F₀ ⟶ F₁} {p : F₁ ⟶ F₂}

omit [HasZeroObject B] [WaldhausenCategoryWithoutGluing B] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]
  [HasZeroObject D] [WaldhausenCategoryWithoutGluing D] in
/-- For a natural transformation i:F₀→F₁ of B→C and any functor J:C→D, mapping its naturality square
for f:a→a′ gives J(i_a)≫J(F₁f)=J(F₀f)≫J(i_a′). -/
theorem mappedBaseNaturality {J : C ⥤ D} {A A' : B} (f : A ⟶ A') :
    J.map (i.app A) ≫ J.map (F₁.map f) = J.map (F₀.map f) ≫ J.map (i.app A') := by
  rw [← J.map_comp, ← J.map_comp]
  exact congrArg J.map (i.naturality f).symm

variable (H : IsWaldhausenCofiberFunctorSequence F₀ F₁ F₂ i p)
include H

/-- Let B,C have chosen zeros and Waldhausen structures without gluing. Let F₀,F₁,F₂:B→C be
Waldhausen exact, with natural i:F₀→F₁ and p:F₁→F₂ forming objectwise cofiber sequences and
satisfying the relative base-corner cofibration condition. For a Waldhausen-exact L:A→B, where A
has a zero and no-gluing Waldhausen structure, the precomposed functors L⋙F₀,L⋙F₁,L⋙F₂ with the
induced natural maps form the same cofiber-functor condition. -/
theorem precomp {A : Type uA} [Category.{vA} A] [HasZeroObject A] [WaldhausenCategoryWithoutGluing A]
    (L : A ⥤ B) (hL : L.IsWaldhausenExact) :
    IsWaldhausenCofiberFunctorSequence (L ⋙ F₀) (L ⋙ F₁) (L ⋙ F₂)
      (Functor.whiskerLeft L i) (Functor.whiskerLeft L p) := by
  refine ⟨hL.comp H.sourceExact, hL.comp H.middleExact, hL.comp H.quotientExact,
    fun X => H.objectwise (L.obj X), ?_⟩
  intro X Y f hf
  exact H.baseCofibration (L.map f) (hL.map_cofibration f hf)

/-- Let B,C have chosen zeros and Waldhausen structures without gluing. Let F₀,F₁,F₂:B→C be
Waldhausen exact, with natural i:F₀→F₁ and p:F₁→F₂ forming objectwise cofiber sequences and
satisfying the relative base-corner cofibration condition. For any f:a→a′, the span
i_a:F₀(a)→F₁(a) and F₀(f):F₀(a)→F₀(a′) has a pushout, since i_a is a cofibration. -/
theorem baseHasPushout {A A' : B} (f : A ⟶ A') : HasPushout (i.app A) (F₀.map f) := by
  obtain ⟨_, _, _, hP, _⟩ := WaldhausenCategoryWithoutGluing.cofibration_pushout (C := C)
    (i.app A) (H.objectwise A).1 (F₀.obj A') (F₀.map f)
  exact hP.flip.hasPushout

variable {J : C ⥤ D} (hJ : J.IsWaldhausenExact)
include hJ

/-- Let B,C have chosen zeros and Waldhausen structures without gluing. Let F₀,F₁,F₂:B→C be
Waldhausen exact, with natural i:F₀→F₁ and p:F₁→F₂ forming objectwise cofiber sequences and
satisfying the relative base-corner cofibration condition. Let J:C→D be Waldhausen exact, with D
also carrying a zero and a no-gluing Waldhausen structure. For any f:a→a′, the mapped span
J(i_a),J(F₀(f)) has a pushout in D. -/
theorem mappedBaseHasPushout {A A' : B} (f : A ⟶ A') :
    HasPushout (J.map (i.app A)) (J.map (F₀.map f)) := by
  obtain ⟨_, _, _, hP, _⟩ := WaldhausenCategoryWithoutGluing.cofibration_pushout (C := D)
    (J.map (i.app A)) (hJ.map_cofibration (i.app A) (H.objectwise A).1)
    (J.obj (F₀.obj A')) (J.map (F₀.map f))
  exact hP.flip.hasPushout

/-- Let B,C have chosen zeros and Waldhausen structures without gluing. Let F₀,F₁,F₂:B→C be
Waldhausen exact, with natural i:F₀→F₁ and p:F₁→F₂ forming objectwise cofiber sequences and
satisfying the relative base-corner cofibration condition. Let J:C→D be Waldhausen exact, with D
also carrying a zero and a no-gluing Waldhausen structure. For f:a→a′, put
P_f=F₁(a)⊔_(F₀(a))F₀(a′) and Q_f=J(F₁(a))⊔_(J(F₀(a)))J(F₀(a′)). Applying J to the source pushout
square gives a pushout with apex J(P_f) and both source legs mapped by J. -/
theorem mappedBasePushoutIsPushout {A A' : B} (f : A ⟶ A') :
    letI := H.baseHasPushout f
    IsPushout (J.map (i.app A)) (J.map (F₀.map f))
      (J.map (pushout.inl (i.app A) (F₀.map f)))
      (J.map (pushout.inr (i.app A) (F₀.map f))) := by
  let _ := H.baseHasPushout f
  exact (hJ.map_pushout (i.app A) (F₀.map f)
    (pushout.inr (i.app A) (F₀.map f)) (pushout.inl (i.app A) (F₀.map f))
    (H.objectwise A).1 (IsPushout.of_hasPushout _ _).flip).flip

/-- Let B,C have chosen zeros and Waldhausen structures without gluing. Let F₀,F₁,F₂:B→C be
Waldhausen exact, with natural i:F₀→F₁ and p:F₁→F₂ forming objectwise cofiber sequences and
satisfying the relative base-corner cofibration condition. Let J:C→D be Waldhausen exact, with D
also carrying a zero and a no-gluing Waldhausen structure. For f:a→a′, put
P_f=F₁(a)⊔_(F₀(a))F₀(a′) and Q_f=J(F₁(a))⊔_(J(F₀(a)))J(F₀(a′)). The two pushout universal
properties give the canonical chart χ:J(P_f)≅Q_f preserving both mapped legs. -/
@[implicit_reducible]
def mappedBasePushoutIso {A A' : B} (f : A ⟶ A') :
    letI := H.baseHasPushout f
    letI := H.mappedBaseHasPushout hJ f
    J.obj (pushout (i.app A) (F₀.map f)) ≅ pushout (J.map (i.app A)) (J.map (F₀.map f)) := by
  letI := H.baseHasPushout f
  letI := H.mappedBaseHasPushout hJ f
  exact (H.mappedBasePushoutIsPushout hJ f).isoIsPushout
    (J.obj (F₁.obj A)) (J.obj (F₀.obj A')) (IsPushout.of_hasPushout _ _)

/-- Let B,C have chosen zeros and Waldhausen structures without gluing. Let F₀,F₁,F₂:B→C be
Waldhausen exact, with natural i:F₀→F₁ and p:F₁→F₂ forming objectwise cofiber sequences and
satisfying the relative base-corner cofibration condition. Let J:C→D be Waldhausen exact, with D
also carrying a zero and a no-gluing Waldhausen structure. For f:a→a′, put
P_f=F₁(a)⊔_(F₀(a))F₀(a′) and Q_f=J(F₁(a))⊔_(J(F₀(a)))J(F₀(a′)). The first source pushout leg,
mapped by J and followed by χ, equals the first selected target leg. -/
theorem mappedBasePushoutIso_inl_hom {A A' : B} (f : A ⟶ A') :
    letI := H.baseHasPushout f
    letI := H.mappedBaseHasPushout hJ f
    J.map (pushout.inl (i.app A) (F₀.map f)) ≫ (H.mappedBasePushoutIso hJ f).hom =
      pushout.inl (J.map (i.app A)) (J.map (F₀.map f)) := by
  let _ := H.baseHasPushout f
  let _ := H.mappedBaseHasPushout hJ f
  exact (H.mappedBasePushoutIsPushout hJ f).inl_isoIsPushout_hom
    (J.obj (F₁.obj A)) (J.obj (F₀.obj A')) (IsPushout.of_hasPushout _ _)

/-- Let B,C have chosen zeros and Waldhausen structures without gluing. Let F₀,F₁,F₂:B→C be
Waldhausen exact, with natural i:F₀→F₁ and p:F₁→F₂ forming objectwise cofiber sequences and
satisfying the relative base-corner cofibration condition. Let J:C→D be Waldhausen exact, with D
also carrying a zero and a no-gluing Waldhausen structure. For f:a→a′, put
P_f=F₁(a)⊔_(F₀(a))F₀(a′) and Q_f=J(F₁(a))⊔_(J(F₀(a)))J(F₀(a′)). The second source pushout leg,
mapped by J and followed by χ, equals the second selected target leg. -/
theorem mappedBasePushoutIso_inr_hom {A A' : B} (f : A ⟶ A') :
    letI := H.baseHasPushout f
    letI := H.mappedBaseHasPushout hJ f
    J.map (pushout.inr (i.app A) (F₀.map f)) ≫ (H.mappedBasePushoutIso hJ f).hom =
      pushout.inr (J.map (i.app A)) (J.map (F₀.map f)) := by
  let _ := H.baseHasPushout f
  let _ := H.mappedBaseHasPushout hJ f
  exact (H.mappedBasePushoutIsPushout hJ f).inr_isoIsPushout_hom
    (J.obj (F₁.obj A)) (J.obj (F₀.obj A')) (IsPushout.of_hasPushout _ _)

/-- Let B,C have chosen zeros and Waldhausen structures without gluing. Let F₀,F₁,F₂:B→C be
Waldhausen exact, with natural i:F₀→F₁ and p:F₁→F₂ forming objectwise cofiber sequences and
satisfying the relative base-corner cofibration condition. Let J:C→D be Waldhausen exact, with D
also carrying a zero and a no-gluing Waldhausen structure. For f:a→a′, put
P_f=F₁(a)⊔_(F₀(a))F₀(a′) and Q_f=J(F₁(a))⊔_(J(F₀(a)))J(F₀(a′)). The first selected target leg
followed by χ⁻¹ equals J of the first source pushout leg. -/
theorem mappedBasePushoutIso_inl_inv {A A' : B} (f : A ⟶ A') :
    letI := H.baseHasPushout f
    letI := H.mappedBaseHasPushout hJ f
    pushout.inl (J.map (i.app A)) (J.map (F₀.map f)) ≫ (H.mappedBasePushoutIso hJ f).inv =
      J.map (pushout.inl (i.app A) (F₀.map f)) := by
  let _ := H.baseHasPushout f
  let _ := H.mappedBaseHasPushout hJ f
  rw [← H.mappedBasePushoutIso_inl_hom hJ f]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Let B,C have chosen zeros and Waldhausen structures without gluing. Let F₀,F₁,F₂:B→C be
Waldhausen exact, with natural i:F₀→F₁ and p:F₁→F₂ forming objectwise cofiber sequences and
satisfying the relative base-corner cofibration condition. Let J:C→D be Waldhausen exact, with D
also carrying a zero and a no-gluing Waldhausen structure. For f:a→a′, put
P_f=F₁(a)⊔_(F₀(a))F₀(a′) and Q_f=J(F₁(a))⊔_(J(F₀(a)))J(F₀(a′)). The second selected target leg
followed by χ⁻¹ equals J of the second source pushout leg. -/
theorem mappedBasePushoutIso_inr_inv {A A' : B} (f : A ⟶ A') :
    letI := H.baseHasPushout f
    letI := H.mappedBaseHasPushout hJ f
    pushout.inr (J.map (i.app A)) (J.map (F₀.map f)) ≫ (H.mappedBasePushoutIso hJ f).inv =
      J.map (pushout.inr (i.app A) (F₀.map f)) := by
  let _ := H.baseHasPushout f
  let _ := H.mappedBaseHasPushout hJ f
  rw [← H.mappedBasePushoutIso_inr_hom hJ f]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Let B,C have chosen zeros and Waldhausen structures without gluing. Let F₀,F₁,F₂:B→C be
Waldhausen exact, with natural i:F₀→F₁ and p:F₁→F₂ forming objectwise cofiber sequences and
satisfying the relative base-corner cofibration condition. Let J:C→D be Waldhausen exact, with D
also carrying a zero and a no-gluing Waldhausen structure. For f:a→a′, put
P_f=F₁(a)⊔_(F₀(a))F₀(a′) and Q_f=J(F₁(a))⊔_(J(F₀(a)))J(F₀(a′)). The target base corner
Q_f→J(F₁(a′)) equals χ⁻¹ followed by J of the source corner P_f→F₁(a′). -/
theorem mappedBaseCorner_eq {A A' : B} (f : A ⟶ A') :
    letI := H.baseHasPushout f
    letI := H.mappedBaseHasPushout hJ f
    pushout.desc (J.map (F₁.map f)) (J.map (i.app A'))
        (mappedBaseNaturality (J := J) (i := i) f) =
      (H.mappedBasePushoutIso hJ f).inv ≫
        J.map (pushout.desc (F₁.map f) (i.app A') (i.naturality f).symm) := by
  let _ := H.baseHasPushout f
  let _ := H.mappedBaseHasPushout hJ f
  apply pushout.hom_ext
  · rw [pushout.inl_desc, ← Category.assoc, H.mappedBasePushoutIso_inl_inv hJ f,
      ← J.map_comp, pushout.inl_desc]
  · rw [pushout.inr_desc, ← Category.assoc, H.mappedBasePushoutIso_inr_inv hJ f,
      ← J.map_comp, pushout.inr_desc]

/-- Let B,C have chosen zeros and Waldhausen structures without gluing. Let F₀,F₁,F₂:B→C be
Waldhausen exact, with natural i:F₀→F₁ and p:F₁→F₂ forming objectwise cofiber sequences and
satisfying the relative base-corner cofibration condition. Let J:C→D be Waldhausen exact, with D
also carrying a zero and a no-gluing Waldhausen structure. For f:a→a′, put
P_f=F₁(a)⊔_(F₀(a))F₀(a′) and Q_f=J(F₁(a))⊔_(J(F₀(a)))J(F₀(a′)). If f is a cofibration in B, the
target base corner is a cofibration in D. -/
theorem mappedBaseCorner_isCofibration {A A' : B} (f : A ⟶ A') (hf : IsCofibration f) :
    letI := H.mappedBaseHasPushout hJ f
    IsCofibration (pushout.desc (J.map (F₁.map f)) (J.map (i.app A'))
      (mappedBaseNaturality (J := J) (i := i) f)) := by
  let _ := H.baseHasPushout f
  let _ := H.mappedBaseHasPushout hJ f
  rw [H.mappedBaseCorner_eq hJ f]
  exact (WaldhausenCategoryWithoutGluing.cofibrations (C := D)).comp_mem _ _
    ((WaldhausenCategoryWithoutGluing.cofibrations (C := D)).of_isIso (H.mappedBasePushoutIso hJ f).inv)
    (hJ.map_cofibration _ (H.baseCofibration f hf))

/-- Let B,C have chosen zeros and Waldhausen structures without gluing. Let F₀,F₁,F₂:B→C be
Waldhausen exact, with natural i:F₀→F₁ and p:F₁→F₂ forming objectwise cofiber sequences and
satisfying the relative base-corner cofibration condition. Let J:C→D be Waldhausen exact, with D
also carrying a zero and a no-gluing Waldhausen structure. The functors F₀⋙J,F₁⋙J,F₂⋙J, with the
natural maps J(i),J(p), form a Waldhausen cofiber-functor sequence. -/
theorem postcomp :
    IsWaldhausenCofiberFunctorSequence (F₀ ⋙ J) (F₁ ⋙ J) (F₂ ⋙ J)
      (Functor.whiskerRight i J) (Functor.whiskerRight p J) := by
  refine ⟨H.sourceExact.comp hJ, H.middleExact.comp hJ, H.quotientExact.comp hJ,
    fun X => hJ.map_cofibrationSequence (H.objectwise X), ?_⟩
  intro X Y f hf
  exact H.mappedBaseCorner_isCofibration hJ f hf

end CategoryTheory.Waldhausen.SConstruction.IsWaldhausenCofiberFunctorSequence

end
