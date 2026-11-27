/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.Projective.HorseshoeComparison
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Algebra.Homology.Homotopy

/- Proof implementation note.
# Homotopies between comparisons of projective and horseshoe resolutions

Two morphisms of projective resolutions over the same morphism are
homotopic, by Mathlib's `ProjectiveResolution.liftHomotopy` applied to
their augmentation equations.  More substantially, two strict horseshoe
comparisons over the same map of short exact sequences, whose endpoint
resolution maps are related by specified homotopies, are related by a
homotopy of the middle chain maps which is compatible with the endpoint
homotopies through the horseshoe inclusions and projections.  The
endpoint compatibility is essential for assembling homotopies of nested
horseshoe constructions, such as Cartan--Eilenberg bicomplexes; a bare
homotopy of the middle maps, which already follows from the
projective-resolution statement, does not suffice for that purpose.
-/

/-!
# Homotopies of projective and horseshoe comparisons

In an abelian category `C`, two projective-resolution morphisms over
the same resolved-object map have homotopic chain maps. For horseshoe
comparisons over the same short-exact-sequence map, prescribed homotopies
at both projective endpoints extend to a middle homotopy preserving
the endpoint inclusion and projection squares.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ProjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C]

section HomHomotopy

variable {Z Z' : C} {P : ProjectiveResolution Z}
  {Q : ProjectiveResolution Z'} {f : Z ⟶ Z'}

/-- In an abelian category `C`, let `P`, `Q` be projective resolutions
of `Z`, `Z′` and `f : Z → Z′`. Any two augmentation-compatible
resolution maps `φ,ψ : P → Q` over `f` have homotopic chain maps
`φ.hom ~ ψ.hom`. -/
noncomputable def Hom.homotopy (φ ψ : Hom P Q f) : Homotopy φ.hom ψ.hom :=
  ProjectiveResolution.liftHomotopy f _ _ φ.hom_comp_π ψ.hom_comp_π

end HomHomotopy

variable {S S' : ShortComplex C} {hS : S.ShortExact} {hS' : S'.ShortExact}
variable {P₁ : ProjectiveResolution S.X₁} {P₃ : ProjectiveResolution S.X₃}
variable {P₁' : ProjectiveResolution S'.X₁} {P₃' : ProjectiveResolution S'.X₃}
variable {H : HorseshoeData hS P₁ P₃} {H' : HorseshoeData hS' P₁' P₃'}
variable (sH : H.Spec) (sH' : H'.Spec)
variable {φ : S ⟶ S'}
variable {u u' : ProjectiveResolution.Hom P₁ P₁' φ.τ₁}
variable {w w' : ProjectiveResolution.Hom P₃ P₃' φ.τ₃}
variable (hu : Homotopy u.hom u'.hom) (hw : Homotopy w.hom w'.hom)
variable (F : HorseshoeData.Hom (H := H) (H' := H') (φ := φ) (u := u) (w := w))
variable (G : HorseshoeData.Hom (H := H) (H' := H') (φ := φ) (u := u') (w := w'))

namespace HorseshoeData

/-- A component of a morphism between horseshoe middle objects,
conjugated into the stored endpoint biproduct coordinates. -/
private def conjHom (a b : ℕ)
    (x : H.middle.complex.X a ⟶ H'.middle.complex.X b) :
    P₁.complex.X a ⊞ P₃.complex.X a ⟶
      P₁'.complex.X b ⊞ P₃'.complex.X b :=
  (sH.middleXIso a).inv ≫ x ≫ (sH'.middleXIso b).hom

/-- The source middle differential in endpoint biproduct coordinates. -/
private def conjDSource (a : ℕ) :
    P₁.complex.X (a + 1) ⊞ P₃.complex.X (a + 1) ⟶
      P₁.complex.X a ⊞ P₃.complex.X a :=
  (sH.middleXIso (a + 1)).inv ≫ H.middle.complex.d (a + 1) a ≫
    (sH.middleXIso a).hom

/-- The target middle differential in endpoint biproduct coordinates. -/
private def conjDTarget (a : ℕ) :
    P₁'.complex.X (a + 1) ⊞ P₃'.complex.X (a + 1) ⟶
      P₁'.complex.X a ⊞ P₃'.complex.X a :=
  (sH'.middleXIso (a + 1)).inv ≫ H'.middle.complex.d (a + 1) a ≫
    (sH'.middleXIso a).hom

/-- The right-endpoint component of the source middle augmentation in
endpoint coordinates. -/
private def rightAugSource : P₃.complex.X 0 ⟶ S.X₂ :=
  biprod.inr ≫ (sH.middleXIso 0).inv ≫ H.middle.π.f 0

/-- The right-endpoint component of the target middle augmentation in
endpoint coordinates. -/
private def rightAugTarget : P₃'.complex.X 0 ⟶ S'.X₂ :=
  biprod.inr ≫ (sH'.middleXIso 0).inv ≫ H'.middle.π.f 0

private theorem inl_ofComponents_fst {X₁ X₂ Y₁ Y₂ : C}
    (f₁₁ : X₁ ⟶ Y₁) (f₁₂ : X₁ ⟶ Y₂) (f₂₁ : X₂ ⟶ Y₁) (f₂₂ : X₂ ⟶ Y₂) :
    biprod.inl ≫ Biprod.ofComponents f₁₁ f₁₂ f₂₁ f₂₂ ≫ biprod.fst = f₁₁ := by
  simp

private theorem inl_ofComponents_snd {X₁ X₂ Y₁ Y₂ : C}
    (f₁₁ : X₁ ⟶ Y₁) (f₁₂ : X₁ ⟶ Y₂) (f₂₁ : X₂ ⟶ Y₁) (f₂₂ : X₂ ⟶ Y₂) :
    biprod.inl ≫ Biprod.ofComponents f₁₁ f₁₂ f₂₁ f₂₂ ≫ biprod.snd = f₁₂ := by
  simp

private theorem inr_ofComponents_fst {X₁ X₂ Y₁ Y₂ : C}
    (f₁₁ : X₁ ⟶ Y₁) (f₁₂ : X₁ ⟶ Y₂) (f₂₁ : X₂ ⟶ Y₁) (f₂₂ : X₂ ⟶ Y₂) :
    biprod.inr ≫ Biprod.ofComponents f₁₁ f₁₂ f₂₁ f₂₂ ≫ biprod.fst = f₂₁ := by
  simp

private theorem inr_ofComponents_snd {X₁ X₂ Y₁ Y₂ : C}
    (f₁₁ : X₁ ⟶ Y₁) (f₁₂ : X₁ ⟶ Y₂) (f₂₁ : X₂ ⟶ Y₁) (f₂₂ : X₂ ⟶ Y₂) :
    biprod.inr ≫ Biprod.ofComponents f₁₁ f₁₂ f₂₁ f₂₂ ≫ biprod.snd = f₂₂ := by
  simp

/-- The free cross component of a horseshoe comparison in endpoint
coordinates: the component from the right endpoint resolution to the
target left endpoint resolution. -/
private def homCross {uu : ProjectiveResolution.Hom P₁ P₁' φ.τ₁}
    {ww : ProjectiveResolution.Hom P₃ P₃' φ.τ₃}
    (Φ : HorseshoeData.Hom (H := H) (H' := H') (φ := φ) (u := uu) (w := ww))
    (a : ℕ) : P₃.complex.X a ⟶ P₁'.complex.X a :=
  biprod.inr ≫ conjHom sH sH' a a (Φ.hom.f a) ≫ biprod.fst

/-- The free cross component of the source middle differential. -/
private def middleCrossSource (a : ℕ) :
    P₃.complex.X (a + 1) ⟶ P₁.complex.X a :=
  biprod.inr ≫ conjDSource sH a ≫ biprod.fst

/-- The free cross component of the target middle differential. -/
private def middleCrossTarget (a : ℕ) :
    P₃'.complex.X (a + 1) ⟶ P₁'.complex.X a :=
  biprod.inr ≫ conjDTarget sH' a ≫ biprod.fst

private theorem conjHom_hom {uu : ProjectiveResolution.Hom P₁ P₁' φ.τ₁}
    {ww : ProjectiveResolution.Hom P₃ P₃' φ.τ₃}
    (Φ : HorseshoeData.Hom (H := H) (H' := H') (φ := φ) (u := uu) (w := ww))
    (a : ℕ) :
    conjHom sH sH' a a (Φ.hom.f a) =
      Biprod.ofComponents (uu.hom.f a) 0 (homCross sH sH' Φ a) (ww.hom.f a) := by
  have h := (Φ.spec (sH := sH) (sH' := sH')).middle_f a
  simpa only [conjHom, homCross, Category.assoc] using h

private theorem conjDSource_eq (a : ℕ) :
    conjDSource sH a =
      Biprod.ofComponents (P₁.complex.d (a + 1) a) 0
        (middleCrossSource sH a) (P₃.complex.d (a + 1) a) := by
  have h := sH.middle_d a
  simpa only [conjDSource, middleCrossSource, Category.assoc] using h

private theorem conjDTarget_eq (a : ℕ) :
    conjDTarget sH' a =
      Biprod.ofComponents (P₁'.complex.d (a + 1) a) 0
        (middleCrossTarget sH' a) (P₃'.complex.d (a + 1) a) := by
  have h := sH'.middle_d a
  simpa only [conjDTarget, middleCrossTarget, Category.assoc] using h

private theorem conjHom_comp_dTarget (a : ℕ)
    (x : H.middle.complex.X (a + 1) ⟶ H'.middle.complex.X (a + 1)) :
    conjHom sH sH' (a + 1) a (x ≫ H'.middle.complex.d (a + 1) a) =
      conjHom sH sH' (a + 1) (a + 1) x ≫ conjDTarget sH' a := by
  simp only [conjHom, conjDTarget, Category.assoc, Iso.hom_inv_id_assoc]

private theorem dSource_comp_conjHom (a : ℕ)
    (x : H.middle.complex.X a ⟶ H'.middle.complex.X a) :
    conjHom sH sH' (a + 1) a (H.middle.complex.d (a + 1) a ≫ x) =
      conjDSource sH a ≫ conjHom sH sH' a a x := by
  simp only [conjHom, conjDSource, Category.assoc, Iso.hom_inv_id_assoc]

private theorem conjDSource_comp (a : ℕ) :
    conjDSource sH (a + 1) ≫ conjDSource sH a = 0 := by
  simp only [conjDSource, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc (H.middle.complex.d (a + 1 + 1) (a + 1))
    (H.middle.complex.d (a + 1) a) ((sH.middleXIso a).hom),
    H.middle.complex.d_comp_d]
  simp

private theorem conjDTarget_comp (a : ℕ) :
    conjDTarget sH' (a + 1) ≫ conjDTarget sH' a = 0 := by
  simp only [conjDTarget, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc (H'.middle.complex.d (a + 1 + 1) (a + 1))
    (H'.middle.complex.d (a + 1) a) ((sH'.middleXIso a).hom),
    H'.middle.complex.d_comp_d]
  simp

private theorem hu_f_zero :
    u.hom.f 0 = hu.hom 0 1 ≫ P₁'.complex.d 1 0 + u'.hom.f 0 := by
  have h := hu.comm 0
  rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex] at h
  simpa using h

private theorem hu_f_succ (a : ℕ) :
    u.hom.f (a + 1) =
      P₁.complex.d (a + 1) a ≫ hu.hom a (a + 1) +
        hu.hom (a + 1) (a + 2) ≫ P₁'.complex.d (a + 2) (a + 1) +
        u'.hom.f (a + 1) := by
  have h := hu.comm (a + 1)
  rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] at h
  exact h

private theorem hw_f_zero :
    w.hom.f 0 = hw.hom 0 1 ≫ P₃'.complex.d 1 0 + w'.hom.f 0 := by
  have h := hw.comm 0
  rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex] at h
  simpa using h

private theorem hw_f_succ (a : ℕ) :
    w.hom.f (a + 1) =
      P₃.complex.d (a + 1) a ≫ hw.hom a (a + 1) +
        hw.hom (a + 1) (a + 2) ≫ P₃'.complex.d (a + 2) (a + 1) +
        w'.hom.f (a + 1) := by
  have h := hw.comm (a + 1)
  rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] at h
  exact h

private theorem homCross_chain {uu : ProjectiveResolution.Hom P₁ P₁' φ.τ₁}
    {ww : ProjectiveResolution.Hom P₃ P₃' φ.τ₃}
    (Φ : HorseshoeData.Hom (H := H) (H' := H') (φ := φ) (u := uu) (w := ww))
    (a : ℕ) :
    homCross sH sH' Φ (a + 1) ≫ P₁'.complex.d (a + 1) a +
        ww.hom.f (a + 1) ≫ middleCrossTarget sH' a =
      middleCrossSource sH a ≫ uu.hom.f a +
        P₃.complex.d (a + 1) a ≫ homCross sH sH' Φ a := by
  have hcomm : Φ.hom.f (a + 1) ≫ H'.middle.complex.d (a + 1) a =
      H.middle.complex.d (a + 1) a ≫ Φ.hom.f a :=
    Φ.hom.comm (a + 1) a
  have hconj :
      conjHom sH sH' (a + 1) (a + 1) (Φ.hom.f (a + 1)) ≫ conjDTarget sH' a =
        conjDSource sH a ≫ conjHom sH sH' a a (Φ.hom.f a) := by
    rw [← conjHom_comp_dTarget, ← dSource_comp_conjHom, hcomm]
  rw [conjHom_hom sH sH' Φ (a + 1), conjHom_hom sH sH' Φ a,
    conjDTarget_eq, conjDSource_eq] at hconj
  have h21 := congrArg (fun k => biprod.inr ≫ k ≫ biprod.fst) hconj
  simp only [Biprod.ofComponents_comp, inr_ofComponents_fst] at h21
  exact h21

private theorem middleCrossSource_comp (a : ℕ) :
    middleCrossSource sH (a + 1) ≫ P₁.complex.d (a + 1) a +
        P₃.complex.d (a + 2) (a + 1) ≫ middleCrossSource sH a = 0 := by
  have h := conjDSource_comp sH a
  rw [conjDSource_eq sH (a + 1), conjDSource_eq sH a] at h
  have h21 := congrArg (fun k => biprod.inr ≫ k ≫ biprod.fst) h
  simp only [Biprod.ofComponents_comp, inr_ofComponents_fst,
    zero_comp, comp_zero] at h21
  exact h21

private theorem middleCrossTarget_comp (a : ℕ) :
    middleCrossTarget sH' (a + 1) ≫ P₁'.complex.d (a + 1) a +
        P₃'.complex.d (a + 2) (a + 1) ≫ middleCrossTarget sH' a = 0 := by
  have h := conjDTarget_comp sH' a
  rw [conjDTarget_eq sH' (a + 1), conjDTarget_eq sH' a] at h
  have h21 := congrArg (fun k => biprod.inr ≫ k ≫ biprod.fst) h
  simp only [Biprod.ofComponents_comp, inr_ofComponents_fst,
    zero_comp, comp_zero] at h21
  exact h21

set_option backward.isDefEq.respectTransparency false in
private theorem leftAugTarget :
    biprod.inl ≫ (sH'.middleXIso 0).inv ≫ H'.middle.π.f 0 =
      P₁'.π.f 0 ≫ S'.f := by
  have hi := HomologicalComplex.congr_hom H'.i_augmentation 0
  simp only [HomologicalComplex.comp_f, ChainComplex.single₀_map_f_zero] at hi
  calc
    biprod.inl ≫ (sH'.middleXIso 0).inv ≫ H'.middle.π.f 0 =
        (H'.i.f 0 ≫ (sH'.middleXIso 0).hom) ≫
          (sH'.middleXIso 0).inv ≫ H'.middle.π.f 0 := by rw [← sH'.i_f]
    _ = H'.i.f 0 ≫ H'.middle.π.f 0 := by simp [Category.assoc]
    _ = P₁'.π.f 0 ≫ S'.f := hi

set_option backward.isDefEq.respectTransparency false in
private theorem homCross_augmentation {uu : ProjectiveResolution.Hom P₁ P₁' φ.τ₁}
    {ww : ProjectiveResolution.Hom P₃ P₃' φ.τ₃}
    (Φ : HorseshoeData.Hom (H := H) (H' := H') (φ := φ) (u := uu) (w := ww)) :
    homCross sH sH' Φ 0 ≫ (P₁'.π.f 0 : P₁'.complex.X 0 ⟶ S'.X₁) ≫ S'.f +
        ww.hom.f 0 ≫ rightAugTarget sH' =
      rightAugSource sH ≫ φ.τ₂ := by
  have haug : Φ.hom.f 0 ≫ H'.middle.π.f 0 = H.middle.π.f 0 ≫ φ.τ₂ := by
    have h := HomologicalComplex.congr_hom Φ.augmentation 0
    simpa only [HomologicalComplex.comp_f,
      ChainComplex.single₀_map_f_zero] using h
  have hconj : conjHom sH sH' 0 0 (Φ.hom.f 0) ≫
        ((sH'.middleXIso 0).inv ≫ H'.middle.π.f 0) =
      ((sH.middleXIso 0).inv ≫ H.middle.π.f 0) ≫ φ.τ₂ := by
    simp only [conjHom, Category.assoc, Iso.hom_inv_id_assoc]
    rw [haug]
  rw [conjHom_hom] at hconj
  have hinr := congrArg (fun k => biprod.inr ≫ k) hconj
  rw [← Category.assoc, Biprod.inr_ofComponents] at hinr
  simp only [Preadditive.add_comp, Category.assoc] at hinr
  rw [leftAugTarget (sH' := sH')] at hinr
  simpa only [rightAugSource, rightAugTarget, Category.assoc] using hinr

set_option backward.isDefEq.respectTransparency false in
private theorem middleCrossTarget_augmentation :
    middleCrossTarget sH' 0 ≫ (P₁'.π.f 0 : P₁'.complex.X 0 ⟶ S'.X₁) ≫ S'.f +
        P₃'.complex.d 1 0 ≫ rightAugTarget sH' = 0 := by
  have hπ : H'.middle.complex.d 1 0 ≫ H'.middle.π.f 0 = 0 := by
    have h := H'.middle.π.comm 1 0
    simpa only [HomologicalComplex.single_obj_d, comp_zero] using h.symm
  have hconj : conjDTarget sH' 0 ≫
      ((sH'.middleXIso 0).inv ≫ H'.middle.π.f 0) = 0 := by
    simp only [conjDTarget, Category.assoc, Iso.hom_inv_id_assoc, hπ,
      comp_zero]
  rw [conjDTarget_eq] at hconj
  have hinr := congrArg (fun k => biprod.inr ≫ k) hconj
  rw [← Category.assoc, Biprod.inr_ofComponents] at hinr
  simp only [Preadditive.add_comp, Category.assoc] at hinr
  rw [leftAugTarget (sH' := sH')] at hinr
  simpa [rightAugTarget] using hinr

/-- The degree-zero defect whose lift through the target left resolution
differential is the cross component of the horseshoe homotopy in
degree zero. -/
private def defectZero : P₃.complex.X 0 ⟶ P₁'.complex.X 0 :=
  (homCross sH sH' F 0 - homCross sH sH' G 0) -
    hw.hom 0 1 ≫ middleCrossTarget sH' 0

/-- The successor defect: the cross component of the difference of the
two horseshoe comparisons, corrected by the endpoint homotopies and by
the previously chosen cross component of the homotopy. -/
private def defectSucc (a : ℕ) (l : P₃.complex.X a ⟶ P₁'.complex.X (a + 1)) :
    P₃.complex.X (a + 1) ⟶ P₁'.complex.X (a + 1) :=
  (homCross sH sH' F (a + 1) - homCross sH sH' G (a + 1)) -
    hw.hom (a + 1) (a + 2) ≫ middleCrossTarget sH' (a + 1) -
    middleCrossSource sH a ≫ hu.hom a (a + 1) -
    P₃.complex.d (a + 1) a ≫ l

/-- The correction term in the invariant below, recording the previous
cross-differential contribution. -/
private def invTerm : (a : ℕ) → (P₃.complex.X (a + 1) ⟶ P₁'.complex.X a)
  | 0 => 0
  | a + 1 => P₃.complex.d (a + 2) (a + 1) ≫ middleCrossSource sH a ≫
      hu.hom a (a + 1)

private theorem invTerm_zero : invTerm sH hu 0 = 0 :=
  rfl

private theorem invTerm_succ (a : ℕ) :
    invTerm sH hu (a + 1) =
      P₃.complex.d (a + 2) (a + 1) ≫ middleCrossSource sH a ≫
        hu.hom a (a + 1) :=
  rfl

/-- The invariant maintained by the chosen cross components of the
horseshoe homotopy: after precomposing with the source right-endpoint
differential, the defect equation holds up to the recorded correction
term.  Only this consequence of the defect equation is needed to prove
the next defect is a cycle. -/
private abbrev Inv (a : ℕ) (l : P₃.complex.X a ⟶ P₁'.complex.X (a + 1)) :
    Prop :=
  P₃.complex.d (a + 1) a ≫ l ≫ P₁'.complex.d (a + 1) a =
    P₃.complex.d (a + 1) a ≫ (homCross sH sH' F a - homCross sH sH' G a) -
      P₃.complex.d (a + 1) a ≫ hw.hom a (a + 1) ≫ middleCrossTarget sH' a -
      invTerm sH hu a

set_option backward.isDefEq.respectTransparency false in
private theorem defectZero_comp_π :
    defectZero sH sH' hw F G ≫ P₁'.π.f 0 = 0 := by
  have eF : homCross sH sH' F 0 ≫ (P₁'.π.f 0 : P₁'.complex.X 0 ⟶ S'.X₁) ≫
        S'.f =
      rightAugSource sH ≫ φ.τ₂ - w.hom.f 0 ≫ rightAugTarget sH' :=
    eq_sub_iff_add_eq.mpr (homCross_augmentation sH sH' F)
  have eG : homCross sH sH' G 0 ≫ (P₁'.π.f 0 : P₁'.complex.X 0 ⟶ S'.X₁) ≫
        S'.f =
      rightAugSource sH ≫ φ.τ₂ - w'.hom.f 0 ≫ rightAugTarget sH' :=
    eq_sub_iff_add_eq.mpr (homCross_augmentation sH sH' G)
  have hww : w.hom.f 0 ≫ rightAugTarget sH' -
        w'.hom.f 0 ≫ rightAugTarget sH' =
      hw.hom 0 1 ≫ P₃'.complex.d 1 0 ≫ rightAugTarget sH' := by
    have hw0 : w.hom.f 0 - w'.hom.f 0 = hw.hom 0 1 ≫ P₃'.complex.d 1 0 := by
      rw [hw_f_zero hw]
      abel
    rw [← Preadditive.sub_comp, hw0, Category.assoc]
  have key : (defectZero sH sH' hw F G ≫
        (P₁'.π.f 0 : P₁'.complex.X 0 ⟶ S'.X₁)) ≫ S'.f = 0 := by
    calc
      (defectZero sH sH' hw F G ≫
          (P₁'.π.f 0 : P₁'.complex.X 0 ⟶ S'.X₁)) ≫ S'.f =
        homCross sH sH' F 0 ≫ (P₁'.π.f 0 : P₁'.complex.X 0 ⟶ S'.X₁) ≫ S'.f -
          homCross sH sH' G 0 ≫ (P₁'.π.f 0 : P₁'.complex.X 0 ⟶ S'.X₁) ≫
            S'.f -
          hw.hom 0 1 ≫ (middleCrossTarget sH' 0 ≫
            (P₁'.π.f 0 : P₁'.complex.X 0 ⟶ S'.X₁) ≫ S'.f) := by
        simp only [defectZero, Preadditive.sub_comp, Category.assoc]
    _ = - (hw.hom 0 1 ≫ (middleCrossTarget sH' 0 ≫
          (P₁'.π.f 0 : P₁'.complex.X 0 ⟶ S'.X₁) ≫ S'.f +
          P₃'.complex.d 1 0 ≫ rightAugTarget sH')) := by
        rw [eF, eG]
        simp only [Preadditive.comp_add]
        rw [← hww]
        abel
    _ = 0 := by
        rw [middleCrossTarget_augmentation sH']
        simp
  have hmono : Mono S'.f := hS'.mono_f
  apply (cancel_mono S'.f).mp
  rw [zero_comp]
  exact key

private theorem inv_zero (l : P₃.complex.X 0 ⟶ P₁'.complex.X 1)
    (hl : l ≫ P₁'.complex.d 1 0 = defectZero sH sH' hw F G) :
    Inv sH sH' hu hw F G 0 l := by
  change P₃.complex.d 1 0 ≫ l ≫ P₁'.complex.d 1 0 =
    P₃.complex.d 1 0 ≫ (homCross sH sH' F 0 - homCross sH sH' G 0) -
      P₃.complex.d 1 0 ≫ hw.hom 0 1 ≫ middleCrossTarget sH' 0 -
      invTerm sH hu 0
  rw [invTerm_zero, sub_zero, hl]
  simp only [defectZero, Preadditive.comp_sub]

private theorem inv_succ (a : ℕ)
    (l : P₃.complex.X a ⟶ P₁'.complex.X (a + 1))
    (l' : P₃.complex.X (a + 1) ⟶ P₁'.complex.X (a + 2))
    (hl : l' ≫ P₁'.complex.d (a + 2) (a + 1) =
      defectSucc sH sH' hu hw F G a l) :
    Inv sH sH' hu hw F G (a + 1) l' := by
  change P₃.complex.d (a + 2) (a + 1) ≫ l' ≫ P₁'.complex.d (a + 2) (a + 1) =
    P₃.complex.d (a + 2) (a + 1) ≫
        (homCross sH sH' F (a + 1) - homCross sH sH' G (a + 1)) -
      P₃.complex.d (a + 2) (a + 1) ≫ hw.hom (a + 1) (a + 2) ≫
        middleCrossTarget sH' (a + 1) -
      invTerm sH hu (a + 1)
  rw [invTerm_succ, hl]
  simp only [defectSucc, Preadditive.comp_sub]
  rw [← Category.assoc (P₃.complex.d (a + 2) (a + 1)) (P₃.complex.d (a + 1) a)
    l, P₃.complex.d_comp_d]
  simp

private theorem defectSucc_cycle (a : ℕ)
    (l : P₃.complex.X a ⟶ P₁'.complex.X (a + 1))
    (hl : Inv sH sH' hu hw F G a l) :
    defectSucc sH sH' hu hw F G a l ≫ P₁'.complex.d (a + 1) a = 0 := by
  have eF : homCross sH sH' F (a + 1) ≫ P₁'.complex.d (a + 1) a =
      middleCrossSource sH a ≫ u.hom.f a +
        P₃.complex.d (a + 1) a ≫ homCross sH sH' F a -
        w.hom.f (a + 1) ≫ middleCrossTarget sH' a :=
    eq_sub_iff_add_eq.mpr (homCross_chain sH sH' F a)
  have eG : homCross sH sH' G (a + 1) ≫ P₁'.complex.d (a + 1) a =
      middleCrossSource sH a ≫ u'.hom.f a +
        P₃.complex.d (a + 1) a ≫ homCross sH sH' G a -
        w'.hom.f (a + 1) ≫ middleCrossTarget sH' a :=
    eq_sub_iff_add_eq.mpr (homCross_chain sH sH' G a)
  have eT : middleCrossTarget sH' (a + 1) ≫ P₁'.complex.d (a + 1) a =
      - (P₃'.complex.d (a + 2) (a + 1) ≫ middleCrossTarget sH' a) :=
    eq_neg_of_add_eq_zero_left (middleCrossTarget_comp sH' a)
  have hHw : hw.hom (a + 1) (a + 2) ≫ P₃'.complex.d (a + 2) (a + 1) =
      (w.hom.f (a + 1) - w'.hom.f (a + 1)) -
        P₃.complex.d (a + 1) a ≫ hw.hom a (a + 1) := by
    rw [hw_f_succ hw a]
    abel
  have hl' : P₃.complex.d (a + 1) a ≫ l ≫ P₁'.complex.d (a + 1) a =
      P₃.complex.d (a + 1) a ≫ (homCross sH sH' F a - homCross sH sH' G a) -
        P₃.complex.d (a + 1) a ≫ hw.hom a (a + 1) ≫ middleCrossTarget sH' a -
        invTerm sH hu a :=
    hl
  simp only [defectSucc, Preadditive.sub_comp, Category.assoc]
  rw [eF, eG, eT, Preadditive.comp_neg,
    ← Category.assoc (hw.hom (a + 1) (a + 2)) (P₃'.complex.d (a + 2) (a + 1))
      (middleCrossTarget sH' a), hHw, hl']
  cases a with
  | zero =>
      have eHu : hu.hom 0 (0 + 1) ≫ P₁'.complex.d (0 + 1) 0 =
          u.hom.f 0 - u'.hom.f 0 := by
        change hu.hom 0 1 ≫ P₁'.complex.d 1 0 = u.hom.f 0 - u'.hom.f 0
        rw [hu_f_zero hu]
        abel
      rw [invTerm_zero, eHu]
      simp only [Preadditive.comp_sub, Preadditive.sub_comp, sub_zero,
        Category.assoc]
      abel
  | succ b =>
      have eHu : hu.hom (b + 1) (b + 2) ≫ P₁'.complex.d (b + 2) (b + 1) =
          (u.hom.f (b + 1) - u'.hom.f (b + 1)) -
            P₁.complex.d (b + 1) b ≫ hu.hom b (b + 1) := by
        rw [hu_f_succ hu b]
        abel
      have eS : middleCrossSource sH (b + 1) ≫ P₁.complex.d (b + 1) b =
          - (P₃.complex.d (b + 2) (b + 1) ≫ middleCrossSource sH b) :=
        eq_neg_of_add_eq_zero_left (middleCrossSource_comp sH b)
      rw [invTerm_succ, eHu]
      simp only [Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc]
      rw [← Category.assoc (middleCrossSource sH (b + 1))
        (P₁.complex.d (b + 1) b) (hu.hom b (b + 1)), eS]
      simp only [Preadditive.neg_comp, Category.assoc]
      abel

private theorem exists_lambda_zero :
    ∃ l : P₃.complex.X 0 ⟶ P₁'.complex.X 1,
      l ≫ P₁'.complex.d 1 0 = defectZero sH sH' hw F G :=
  ⟨P₁'.exact₀.liftFromProjective _ (defectZero_comp_π sH sH' hw F G),
    P₁'.exact₀.liftFromProjective_comp _ _⟩

private theorem exists_lambda_succ (a : ℕ)
    (l : P₃.complex.X a ⟶ P₁'.complex.X (a + 1))
    (hl : Inv sH sH' hu hw F G a l) :
    ∃ l' : P₃.complex.X (a + 1) ⟶ P₁'.complex.X (a + 2),
      l' ≫ P₁'.complex.d (a + 2) (a + 1) = defectSucc sH sH' hu hw F G a l :=
  ⟨(P₁'.exact_succ a).liftFromProjective _
      (defectSucc_cycle sH sH' hu hw F G a l hl),
    (P₁'.exact_succ a).liftFromProjective_comp _ _⟩

open scoped Classical in
/-- The cross components of the horseshoe homotopy, chosen inductively
by lifting the defects through the target left resolution.  At each
step a lift exists by `defectZero_comp_π` and `defectSucc_cycle`; the
`if` form merely makes the choice total. -/
private noncomputable def lambda (a : ℕ) :
    P₃.complex.X a ⟶ P₁'.complex.X (a + 1) :=
  Nat.rec (motive := fun a => P₃.complex.X a ⟶ P₁'.complex.X (a + 1))
    (if h : ∃ l : P₃.complex.X 0 ⟶ P₁'.complex.X 1,
        l ≫ P₁'.complex.d 1 0 = defectZero sH sH' hw F G then h.choose else 0)
    (fun a l => if h : ∃ l' : P₃.complex.X (a + 1) ⟶ P₁'.complex.X (a + 2),
        l' ≫ P₁'.complex.d (a + 2) (a + 1) =
          defectSucc sH sH' hu hw F G a l then h.choose else 0) a

private theorem lambda_zero_comp :
    lambda sH sH' hu hw F G 0 ≫ P₁'.complex.d 1 0 =
      defectZero sH sH' hw F G := by
  classical
  change (if h : ∃ l : P₃.complex.X 0 ⟶ P₁'.complex.X 1,
      l ≫ P₁'.complex.d 1 0 = defectZero sH sH' hw F G then h.choose else 0) ≫
    P₁'.complex.d 1 0 = defectZero sH sH' hw F G
  split
  · rename_i h
    exact h.choose_spec
  · rename_i h
    exact absurd (exists_lambda_zero sH sH' hw F G) h

private theorem lambda_succ_comp (a : ℕ)
    (hl : Inv sH sH' hu hw F G a (lambda sH sH' hu hw F G a)) :
    lambda sH sH' hu hw F G (a + 1) ≫ P₁'.complex.d (a + 2) (a + 1) =
      defectSucc sH sH' hu hw F G a (lambda sH sH' hu hw F G a) := by
  classical
  change (if h : ∃ l' : P₃.complex.X (a + 1) ⟶ P₁'.complex.X (a + 2),
      l' ≫ P₁'.complex.d (a + 2) (a + 1) =
        defectSucc sH sH' hu hw F G a (lambda sH sH' hu hw F G a)
    then h.choose else 0) ≫ P₁'.complex.d (a + 2) (a + 1) =
      defectSucc sH sH' hu hw F G a (lambda sH sH' hu hw F G a)
  split
  · rename_i h
    exact h.choose_spec
  · rename_i h
    exact absurd (exists_lambda_succ sH sH' hu hw F G a _ hl) h

private theorem inv_lambda (a : ℕ) :
    Inv sH sH' hu hw F G a (lambda sH sH' hu hw F G a) := by
  induction a with
  | zero =>
      exact inv_zero sH sH' hu hw F G _ (lambda_zero_comp sH sH' hu hw F G)
  | succ a ih =>
      exact inv_succ sH sH' hu hw F G a _ _
        (lambda_succ_comp sH sH' hu hw F G a ih)

private theorem lambda_succ_comp' (a : ℕ) :
    lambda sH sH' hu hw F G (a + 1) ≫ P₁'.complex.d (a + 2) (a + 1) =
      defectSucc sH sH' hu hw F G a (lambda sH sH' hu hw F G a) :=
  lambda_succ_comp sH sH' hu hw F G a (inv_lambda sH sH' hu hw F G a)

/-- The components of the endpoint-controlled homotopy, in endpoint
coordinates the block matrix with the endpoint homotopy components on
the diagonal and the chosen cross component below. -/
private noncomputable def sMap (a : ℕ) :
    H.middle.complex.X a ⟶ H'.middle.complex.X (a + 1) :=
  (sH.middleXIso a).hom ≫
    Biprod.ofComponents (hu.hom a (a + 1)) 0 (lambda sH sH' hu hw F G a)
      (hw.hom a (a + 1)) ≫
    (sH'.middleXIso (a + 1)).inv

private theorem conj_sMap (a : ℕ) :
    conjHom sH sH' a (a + 1) (sMap sH sH' hu hw F G a) =
      Biprod.ofComponents (hu.hom a (a + 1)) 0 (lambda sH sH' hu hw F G a)
        (hw.hom a (a + 1)) := by
  simp only [sMap, conjHom, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id, Category.comp_id]

private theorem sMap_comp_i (a : ℕ) :
    H.i.f a ≫ sMap sH sH' hu hw F G a = hu.hom a (a + 1) ≫ H'.i.f (a + 1) := by
  apply (cancel_mono (sH'.middleXIso (a + 1)).hom).mp
  simp only [sMap, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [reassoc_of% (sH.i_f a), sH'.i_f]
  simp only [Biprod.inl_ofComponents, zero_comp, add_zero]

private theorem sMap_comp_p (a : ℕ) :
    sMap sH sH' hu hw F G a ≫ H'.p.f (a + 1) =
      H.p.f a ≫ hw.hom a (a + 1) := by
  apply (cancel_epi (sH.middleXIso a).inv).mp
  simp only [sMap, Category.assoc, Iso.inv_hom_id_assoc]
  rw [sH'.p_f, reassoc_of% (sH.p_f a)]
  simp only [Biprod.ofComponents_snd, comp_zero, zero_add]

private theorem eq_of_conj_eq {a : ℕ}
    {x y : H.middle.complex.X a ⟶ H'.middle.complex.X a}
    (h : conjHom sH sH' a a x = conjHom sH sH' a a y) : x = y := by
  have h1 := congrArg
    (fun k => (sH.middleXIso a).hom ≫ k ≫ (sH'.middleXIso a).inv) h
  simpa [conjHom] using h1

private theorem conjHom_sub_f (a : ℕ) :
    conjHom sH sH' a a ((F.hom - G.hom).f a) =
      conjHom sH sH' a a (F.hom.f a) - conjHom sH sH' a a (G.hom.f a) := by
  simp only [HomologicalComplex.sub_f_apply, conjHom, Preadditive.comp_sub,
    Preadditive.sub_comp]

private theorem conjHom_add {a b : ℕ}
    {x y : H.middle.complex.X a ⟶ H'.middle.complex.X b} :
    conjHom sH sH' a b (x + y) = conjHom sH sH' a b x + conjHom sH sH' a b y := by
  simp only [conjHom, Preadditive.comp_add, Preadditive.add_comp]

private theorem conjHom_d_comp (a b : ℕ)
    (x : H.middle.complex.X a ⟶ H'.middle.complex.X b) :
    conjHom sH sH' (a + 1) b (H.middle.complex.d (a + 1) a ≫ x) =
      conjDSource sH a ≫ conjHom sH sH' a b x := by
  simp only [conjHom, conjDSource, Category.assoc, Iso.hom_inv_id_assoc]

private theorem conjHom_comp_dTarget' (a b : ℕ)
    (x : H.middle.complex.X a ⟶ H'.middle.complex.X (b + 1)) :
    conjHom sH sH' a b (x ≫ H'.middle.complex.d (b + 1) b) =
      conjHom sH sH' a (b + 1) x ≫ conjDTarget sH' b := by
  simp only [conjHom, conjDTarget, Category.assoc, Iso.hom_inv_id_assoc]

private theorem sub_f_zero :
    (F.hom - G.hom).f 0 =
      sMap sH sH' hu hw F G 0 ≫ H'.middle.complex.d 1 0 := by
  apply eq_of_conj_eq (sH := sH) (sH' := sH')
  rw [conjHom_sub_f, conjHom_hom sH sH' F 0, conjHom_hom sH sH' G 0,
    conjHom_comp_dTarget' sH sH' 0 0 (sMap sH sH' hu hw F G 0), conj_sMap,
    conjDTarget_eq, Biprod.ofComponents_comp]
  apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
    simp only [inl_ofComponents_fst, inl_ofComponents_snd,
      inr_ofComponents_fst, inr_ofComponents_snd, Preadditive.sub_comp,
      Preadditive.comp_sub, Category.assoc]
  · simp only [zero_comp, add_zero]
    rw [hu_f_zero hu]
    abel
  · rw [comp_zero, zero_comp, add_zero, sub_self]
  · rw [lambda_zero_comp sH sH' hu hw F G]
    simp only [defectZero]
    abel
  · simp only [comp_zero, zero_add]
    rw [hw_f_zero hw]
    abel

private theorem sub_f_succ (a : ℕ) :
    (F.hom - G.hom).f (a + 1) =
      H.middle.complex.d (a + 1) a ≫ sMap sH sH' hu hw F G a +
        sMap sH sH' hu hw F G (a + 1) ≫ H'.middle.complex.d (a + 2) (a + 1) := by
  apply eq_of_conj_eq (sH := sH) (sH' := sH')
  rw [conjHom_sub_f, conjHom_hom sH sH' F (a + 1), conjHom_hom sH sH' G (a + 1),
    conjHom_add, conjHom_d_comp sH sH' a (a + 1) (sMap sH sH' hu hw F G a),
    conjHom_comp_dTarget' sH sH' (a + 1) (a + 1)
      (sMap sH sH' hu hw F G (a + 1)),
    conjDSource_eq, conjDTarget_eq, conj_sMap, conj_sMap]
  simp only [Biprod.ofComponents_comp]
  apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
    simp only [inl_ofComponents_fst, inl_ofComponents_snd,
      inr_ofComponents_fst, inr_ofComponents_snd, Preadditive.sub_comp,
      Preadditive.comp_sub, Preadditive.add_comp, Preadditive.comp_add,
      Category.assoc]
  · simp only [zero_comp, add_zero]
    rw [hu_f_succ hu a]
    abel
  · simp only [zero_comp, comp_zero, add_zero, sub_self]
  · rw [lambda_succ_comp' sH sH' hu hw F G a]
    simp only [defectSucc]
    abel
  · simp only [comp_zero, zero_add]
    rw [hw_f_succ hw a]
    abel

/-- The difference of the two horseshoe comparisons is null-homotopic
via the endpoint-controlled components `sMap`. -/
private noncomputable def homotopySubZero : Homotopy (F.hom - G.hom) 0 where
  hom a b := if h : a + 1 = b then
      sMap sH sH' hu hw F G a ≫
        eqToHom (congrArg (fun k => H'.middle.complex.X k) h)
    else 0
  zero a b hb := by
    split
    · rename_i h
      exact absurd h hb
    · rfl
  comm a := by
    cases a with
    | zero =>
        rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex,
          HomologicalComplex.zero_f_apply]
        simpa using sub_f_zero sH sH' hu hw F G
    | succ a =>
        rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex,
          HomologicalComplex.zero_f_apply]
        simpa using sub_f_succ sH sH' hu hw F G a

private theorem homotopySubZero_hom_succ (a : ℕ) :
    (homotopySubZero sH sH' hu hw F G).hom a (a + 1) =
      sMap sH sH' hu hw F G a := by
  change (if h : a + 1 = a + 1 then
      sMap sH sH' hu hw F G a ≫
        eqToHom (congrArg (fun k => H'.middle.complex.X k) h) else 0) =
    sMap sH sH' hu hw F G a
  simp

namespace Hom

include sH sH' in
/-- In an abelian category `C`, let `H,H′` be horseshoes with chosen
endpoint biproduct specifications, and let `F,G` be comparisons
over the same short-exact-sequence map. If their left and right
endpoint maps have supplied homotopies `hu`, `hw`, a middle
homotopy `h : F.hom ~ G.hom` exists with
`H.i_a ≫ h_ab = hu_ab ≫ H′.i_b` and
`h_ab ≫ H′.p_b = H.p_a ≫ hw_ab` for every `a,b ∈ ℕ`. -/
theorem nonempty_homotopy :
    ∃ h : Homotopy F.hom G.hom,
      (∀ a b : ℕ, H.i.f a ≫ h.hom a b = hu.hom a b ≫ H'.i.f b) ∧
        ∀ a b : ℕ, h.hom a b ≫ H'.p.f b = H.p.f a ≫ hw.hom a b := by
  refine ⟨Homotopy.equivSubZero.invFun (homotopySubZero sH sH' hu hw F G),
    ?_, ?_⟩
  · intro a b
    by_cases hb : a + 1 = b
    · subst hb
      change H.i.f a ≫ (homotopySubZero sH sH' hu hw F G).hom a (a + 1) =
        hu.hom a (a + 1) ≫ H'.i.f (a + 1)
      rw [homotopySubZero_hom_succ]
      exact sMap_comp_i sH sH' hu hw F G a
    · have hz : (homotopySubZero sH sH' hu hw F G).hom a b = 0 :=
        (homotopySubZero sH sH' hu hw F G).zero a b hb
      change H.i.f a ≫ (homotopySubZero sH sH' hu hw F G).hom a b =
        hu.hom a b ≫ H'.i.f b
      rw [hz, hu.zero a b hb]
      simp
  · intro a b
    by_cases hb : a + 1 = b
    · subst hb
      change (homotopySubZero sH sH' hu hw F G).hom a (a + 1) ≫ H'.p.f (a + 1) =
        H.p.f a ≫ hw.hom a (a + 1)
      rw [homotopySubZero_hom_succ]
      exact sMap_comp_p sH sH' hu hw F G a
    · have hz : (homotopySubZero sH sH' hu hw F G).hom a b = 0 :=
        (homotopySubZero sH sH' hu hw F G).zero a b hb
      change (homotopySubZero sH sH' hu hw F G).hom a b ≫ H'.p.f b =
        H.p.f a ≫ hw.hom a b
      rw [hz, hw.zero a b hb]
      simp

end Hom

end HorseshoeData

end CategoryTheory.ProjectiveResolution

end
