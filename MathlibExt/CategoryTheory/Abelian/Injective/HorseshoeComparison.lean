/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.Projective.HorseshoeComparison
public import MathlibExt.CategoryTheory.Abelian.Injective.ResolutionComparison
public import MathlibExt.CategoryTheory.Abelian.RightDerived.HorseshoeData

/-!
# Comparison maps of injective horseshoe resolutions

In an abelian category `C`, a morphism `α : S → T` of short exact
sequences, with supplied maps between their endpoint injective resolutions,
extends to a comparison between the canonical injective horseshoes. The
comparison restricts to the prescribed endpoint maps.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory.Limits

namespace CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace Functor.RightDerived.HorseshoeData

private abbrev opComplexFunctor (C : Type u) [Category.{v} C] [Abelian C] :=
  HomologicalComplex.opFunctor C (ComplexShape.up ℕ)

private abbrev unopComplexFunctor (C : Type u) [Category.{v} C] [Abelian C] :=
  HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)

private noncomputable abbrev opSingleFunctor (C : Type u) [Category.{v} C] [Abelian C] :=
  @ChainComplex.single₀ Cᵒᵖ Category.opposite
    (@Preadditive.preadditiveHasZeroMorphisms Cᵒᵖ Category.opposite
      (@Abelian.toPreadditive Cᵒᵖ Category.opposite inferInstance))
    (@Abelian.hasZeroObject Cᵒᵖ Category.opposite inferInstance)

private theorem opSingleMapZero {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    ((opSingleFunctor C).map f).f 0 = f :=
  @ChainComplex.single₀_map_f_zero Cᵒᵖ Category.opposite
    (@Preadditive.preadditiveHasZeroMorphisms Cᵒᵖ Category.opposite
      (@Abelian.toPreadditive Cᵒᵖ Category.opposite inferInstance))
    (@Abelian.hasZeroObject Cᵒᵖ Category.opposite inferInstance) X Y f

private theorem opLeftPiZero {S : ShortComplex C} (I : InjectiveResolution S.X₃) :
    (InjectiveResolution.opProjLeft I).π.f 0 = (I.ι.f 0).op := by
  change (I.ι.f 0).op ≫ (single₀OpIso S.X₃).hom.f 0 = (I.ι.f 0).op
  exact (congrArg (fun f => (I.ι.f 0).op ≫ f)
    (single₀OpIso_hom_f_zero S.X₃)).trans (Category.comp_id _)

private theorem opRightPiZero {S : ShortComplex C} (I : InjectiveResolution S.X₁) :
    (InjectiveResolution.opProjRight I).π.f 0 = (I.ι.f 0).op := by
  change (I.ι.f 0).op ≫ (single₀OpIso S.X₁).hom.f 0 = (I.ι.f 0).op
  exact (congrArg (fun f => (I.ι.f 0).op ≫ f)
    (single₀OpIso_hom_f_zero S.X₁)).trans (Category.comp_id _)

private noncomputable def opLeftHom {S T : ShortComplex C}
    {I : InjectiveResolution S.X₃} {J : InjectiveResolution T.X₃}
    (α : S ⟶ T) (w : InjectiveResolution.Hom I J α.τ₃) :
    ProjectiveResolution.Hom (InjectiveResolution.opProjLeft J)
      (InjectiveResolution.opProjLeft I) (ShortComplex.opMap α).τ₁ where
  hom := (opComplexFunctor C).map w.hom.op
  hom_f_zero_comp_π_f_zero := by
    have hw := congrArg Quiver.Hom.op w.ι_f_zero_comp_hom_f_zero
    simp only [CochainComplex.single₀_map_f_zero, op_comp] at hw
    have hm := opSingleMapZero (C := C) (X := T.op.X₁) (Y := S.op.X₁)
      (ShortComplex.opMap α).τ₁
    have ho : ((opComplexFunctor C).map w.hom.op).f 0 = (w.hom.f 0).op := rfl
    have h₁ : @Eq ((InjectiveResolution.opProjLeft J).complex.X 0 ⟶ S.op.X₁)
        (((opComplexFunctor C).map w.hom.op).f 0 ≫
          (InjectiveResolution.opProjLeft I).π.f 0)
        ((w.hom.f 0).op ≫ (I.ι.f 0).op) :=
      congrArg₂ (fun f g => f ≫ g) ho (opLeftPiZero I)
    have h₂ : @Eq ((InjectiveResolution.opProjLeft J).complex.X 0 ⟶ S.op.X₁)
        ((w.hom.f 0).op ≫ (I.ι.f 0).op)
        ((J.ι.f 0).op ≫ (ShortComplex.opMap α).τ₁) := hw
    have h₃ : @Eq ((InjectiveResolution.opProjLeft J).complex.X 0 ⟶ S.op.X₁)
        ((J.ι.f 0).op ≫ (ShortComplex.opMap α).τ₁)
        ((InjectiveResolution.opProjLeft J).π.f 0 ≫
          ((opSingleFunctor C).map (ShortComplex.opMap α).τ₁).f 0) :=
      (congrArg₂ (fun f g => f ≫ g) (opLeftPiZero J) hm).symm
    exact h₁.trans (h₂.trans h₃)

private noncomputable def opRightHom {S T : ShortComplex C}
    {I : InjectiveResolution S.X₁} {J : InjectiveResolution T.X₁}
    (α : S ⟶ T) (u : InjectiveResolution.Hom I J α.τ₁) :
    ProjectiveResolution.Hom (InjectiveResolution.opProjRight J)
      (InjectiveResolution.opProjRight I) (ShortComplex.opMap α).τ₃ where
  hom := (opComplexFunctor C).map u.hom.op
  hom_f_zero_comp_π_f_zero := by
    have hu := congrArg Quiver.Hom.op u.ι_f_zero_comp_hom_f_zero
    simp only [CochainComplex.single₀_map_f_zero, op_comp] at hu
    have hm := opSingleMapZero (C := C) (X := T.op.X₃) (Y := S.op.X₃)
      (ShortComplex.opMap α).τ₃
    have ho : ((opComplexFunctor C).map u.hom.op).f 0 = (u.hom.f 0).op := rfl
    have h₁ : @Eq ((InjectiveResolution.opProjRight J).complex.X 0 ⟶ S.op.X₃)
        (((opComplexFunctor C).map u.hom.op).f 0 ≫
          (InjectiveResolution.opProjRight I).π.f 0)
        ((u.hom.f 0).op ≫ (I.ι.f 0).op) :=
      congrArg₂ (fun f g => f ≫ g) ho (opRightPiZero I)
    have h₂ : @Eq ((InjectiveResolution.opProjRight J).complex.X 0 ⟶ S.op.X₃)
        ((u.hom.f 0).op ≫ (I.ι.f 0).op)
        ((J.ι.f 0).op ≫ (ShortComplex.opMap α).τ₃) := hu
    have h₃ : @Eq ((InjectiveResolution.opProjRight J).complex.X 0 ⟶ S.op.X₃)
        ((J.ι.f 0).op ≫ (ShortComplex.opMap α).τ₃)
        ((InjectiveResolution.opProjRight J).π.f 0 ≫
          ((opSingleFunctor C).map (ShortComplex.opMap α).τ₃).f 0) :=
      (congrArg₂ (fun f g => f ≫ g) (opRightPiZero J) hm).symm
    exact h₁.trans (h₂.trans h₃)

/-- In an abelian category `C`, let `S,T` be short exact sequences
with injective endpoint resolutions `I₁,I₃` and `J₁,J₃`. Given
`α : S → T` and resolution maps `u : I₁ → J₁`, `w : I₃ → J₃`
over `α₁`, `α₃`, there exists a horseshoe comparison over `α`
whose endpoint cochain maps are exactly `u` and `w`. -/
theorem nonempty_hom_ofEndpoints {S T : ShortComplex C}
    (hS : S.ShortExact) (hT : T.ShortExact)
    (I₁ : InjectiveResolution S.X₁) (I₃ : InjectiveResolution S.X₃)
    (J₁ : InjectiveResolution T.X₁) (J₃ : InjectiveResolution T.X₃)
    (α : S ⟶ T)
    (u : InjectiveResolution.Hom I₁ J₁ α.τ₁)
    (w : InjectiveResolution.Hom I₃ J₃ α.τ₃) :
    Nonempty { e : Hom (ofEndpoints S hS I₁ I₃) (ofEndpoints T hT J₁ J₃) α //
      e.ψ₁ = u.hom ∧ e.ψ₃ = w.hom } := by
  let P := InjectiveResolution.HorseshoeData.opHorseshoe (hS := hS)
    (I₁ := I₁) (I₃ := I₃)
  let Q := InjectiveResolution.HorseshoeData.opHorseshoe (hS := hT)
    (I₁ := J₁) (I₃ := J₃)
  let uO := opRightHom α u
  let wO := opLeftHom α w
  have sP : P.Spec := ProjectiveResolution.horseshoe_spec hS.op _ _
  have sQ : Q.Spec := ProjectiveResolution.horseshoe_spec hT.op _ _
  obtain ⟨q⟩ := ProjectiveResolution.HorseshoeData.nonempty_hom
    (hS := hT.op) (hS' := hS.op)
    (P₁ := InjectiveResolution.opProjLeft J₃)
    (P₃ := InjectiveResolution.opProjRight J₁)
    (P₁' := InjectiveResolution.opProjLeft I₃)
    (P₃' := InjectiveResolution.opProjRight I₁)
    (H := Q) (H' := P) (sH := sQ) (sH' := sP)
    (φ := ShortComplex.opMap α) (u := wO) (w := uO)
  let H := InjectiveResolution.horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)
  let K := InjectiveResolution.horseshoe (hS := hT) (I₁ := J₁) (I₃ := J₃)
  let b : H.middle.cocomplex ⟶ K.middle.cocomplex :=
    (unopComplexFunctor C).map q.hom.op
  have hcommI : H.i ≫ b = u.hom ≫ K.i := by
    apply HomologicalComplex.Hom.ext
    funext n
    have hp := congrArg Quiver.Hom.unop (HomologicalComplex.congr_hom q.comm_p n)
    simp only [HomologicalComplex.comp_f, unop_comp] at hp
    have huO : (uO.hom.f n).unop = u.hom.f n := rfl
    have hI : H.i.f n = (P.p.f n).unop := by
      change 𝟙 _ ≫ (P.p.f n).unop = (P.p.f n).unop
      exact Category.id_comp _
    have hJ : K.i.f n = (Q.p.f n).unop := by
      change 𝟙 _ ≫ (Q.p.f n).unop = (Q.p.f n).unop
      exact Category.id_comp _
    have hb : b.f n = (q.hom.f n).unop := rfl
    change H.i.f n ≫ b.f n = u.hom.f n ≫ K.i.f n
    have h₁ : @Eq (I₁.cocomplex.X n ⟶ K.middle.cocomplex.X n)
        (H.i.f n ≫ b.f n) ((P.p.f n).unop ≫ (q.hom.f n).unop) :=
      congrArg₂ (fun f g => f ≫ g) hI hb
    have h₂ : @Eq (I₁.cocomplex.X n ⟶ K.middle.cocomplex.X n)
        ((P.p.f n).unop ≫ (q.hom.f n).unop)
        ((uO.hom.f n).unop ≫ (Q.p.f n).unop) := hp
    have h₃ : @Eq (I₁.cocomplex.X n ⟶ K.middle.cocomplex.X n)
        ((uO.hom.f n).unop ≫ (Q.p.f n).unop) (u.hom.f n ≫ K.i.f n) :=
      congrArg₂ (fun f g => f ≫ g) huO hJ.symm
    exact h₁.trans (h₂.trans h₃)
  have hcommP : H.p ≫ w.hom = b ≫ K.p := by
    apply HomologicalComplex.Hom.ext
    funext n
    have hi := congrArg Quiver.Hom.unop (HomologicalComplex.congr_hom q.comm_i n)
    simp only [HomologicalComplex.comp_f, unop_comp] at hi
    have hwO : (wO.hom.f n).unop = w.hom.f n := rfl
    have hI : H.p.f n = (P.i.f n).unop := by
      change (P.i.f n).unop ≫ 𝟙 _ = (P.i.f n).unop
      exact Category.comp_id _
    have hJ : K.p.f n = (Q.i.f n).unop := by
      change (Q.i.f n).unop ≫ 𝟙 _ = (Q.i.f n).unop
      exact Category.comp_id _
    have hb : b.f n = (q.hom.f n).unop := rfl
    change H.p.f n ≫ w.hom.f n = b.f n ≫ K.p.f n
    have h₁ : @Eq (H.middle.cocomplex.X n ⟶ J₃.cocomplex.X n)
        (H.p.f n ≫ w.hom.f n) ((P.i.f n).unop ≫ (wO.hom.f n).unop) :=
      congrArg₂ (fun f g => f ≫ g) hI hwO.symm
    have h₂ : @Eq (H.middle.cocomplex.X n ⟶ J₃.cocomplex.X n)
        ((P.i.f n).unop ≫ (wO.hom.f n).unop)
        ((q.hom.f n).unop ≫ (Q.i.f n).unop) := hi.symm
    have h₃ : @Eq (H.middle.cocomplex.X n ⟶ J₃.cocomplex.X n)
        ((q.hom.f n).unop ≫ (Q.i.f n).unop) (b.f n ≫ K.p.f n) :=
      congrArg₂ (fun f g => f ≫ g) hb.symm hJ.symm
    exact h₁.trans (h₂.trans h₃)
  have hmiddle : H.middle.ι.f 0 ≫ b.f 0 = α.τ₂ ≫ K.middle.ι.f 0 := by
    have ha := congrArg Quiver.Hom.unop (HomologicalComplex.congr_hom q.augmentation 0)
    simp only [HomologicalComplex.comp_f, unop_comp] at ha
    have hm := congrArg Quiver.Hom.unop
      (opSingleMapZero (C := C) (X := T.op.X₂) (Y := S.op.X₂)
        (ShortComplex.opMap α).τ₂)
    have hm' : (((opSingleFunctor C).map (ShortComplex.opMap α).τ₂).f 0).unop =
        α.τ₂ := hm
    have hI : H.middle.ι.f 0 = (P.middle.π.f 0).unop := by
      change (single₀UnopIso (C := C) S.X₂).hom.f 0 ≫ (P.middle.π.f 0).unop = _
      exact (congrArg (fun f => f ≫ (P.middle.π.f 0).unop)
        (single₀UnopIso_hom_f_zero S.X₂)).trans (Category.id_comp _)
    have hJ : K.middle.ι.f 0 = (Q.middle.π.f 0).unop := by
      change (single₀UnopIso (C := C) T.X₂).hom.f 0 ≫ (Q.middle.π.f 0).unop = _
      exact (congrArg (fun f => f ≫ (Q.middle.π.f 0).unop)
        (single₀UnopIso_hom_f_zero T.X₂)).trans (Category.id_comp _)
    have hb : b.f 0 = (q.hom.f 0).unop := rfl
    have h₁ : @Eq (S.X₂ ⟶ K.middle.cocomplex.X 0)
        (H.middle.ι.f 0 ≫ b.f 0) ((P.middle.π.f 0).unop ≫ (q.hom.f 0).unop) :=
      congrArg₂ (fun f g => f ≫ g) hI hb
    have h₂ : @Eq (S.X₂ ⟶ K.middle.cocomplex.X 0)
        ((P.middle.π.f 0).unop ≫ (q.hom.f 0).unop)
        ((((opSingleFunctor C).map (ShortComplex.opMap α).τ₂).f 0).unop ≫
          (Q.middle.π.f 0).unop) := ha
    have h₃ : @Eq (S.X₂ ⟶ K.middle.cocomplex.X 0)
        ((((opSingleFunctor C).map (ShortComplex.opMap α).τ₂).f 0).unop ≫
          (Q.middle.π.f 0).unop) (α.τ₂ ≫ K.middle.ι.f 0) :=
      congrArg₂ (fun f g => f ≫ g) hm' hJ.symm
    exact h₁.trans (h₂.trans h₃)
  refine ⟨⟨{
    ψ₁ := u.hom
    ψ₂ := b
    ψ₃ := w.hom
    lift₁ := ?_
    lift₂ := hmiddle
    lift₃ := ?_
    comm_φf := hcommI
    comm_φg := hcommP }, rfl, rfl⟩⟩
  · change I₁.ι.f 0 ≫ u.hom.f 0 = α.τ₁ ≫ J₁.ι.f 0
    have hmap := CochainComplex.single₀_map_f_zero
      (V := C) (A := S.X₁) (B := T.X₁) α.τ₁
    have h₁ : @Eq (S.X₁ ⟶ J₁.cocomplex.X 0) (I₁.ι.f 0 ≫ u.hom.f 0)
        (((CochainComplex.single₀ C).map α.τ₁).f 0 ≫ J₁.ι.f 0) :=
      u.ι_f_zero_comp_hom_f_zero
    have h₂ : @Eq (S.X₁ ⟶ J₁.cocomplex.X 0)
        (((CochainComplex.single₀ C).map α.τ₁).f 0 ≫ J₁.ι.f 0) (α.τ₁ ≫ J₁.ι.f 0) :=
      congrArg (fun f => f ≫ J₁.ι.f 0) hmap
    exact h₁.trans h₂
  · change I₃.ι.f 0 ≫ w.hom.f 0 = α.τ₃ ≫ J₃.ι.f 0
    have hmap := CochainComplex.single₀_map_f_zero
      (V := C) (A := S.X₃) (B := T.X₃) α.τ₃
    have h₁ : @Eq (S.X₃ ⟶ J₃.cocomplex.X 0) (I₃.ι.f 0 ≫ w.hom.f 0)
        (((CochainComplex.single₀ C).map α.τ₃).f 0 ≫ J₃.ι.f 0) :=
      w.ι_f_zero_comp_hom_f_zero
    have h₂ : @Eq (S.X₃ ⟶ J₃.cocomplex.X 0)
        (((CochainComplex.single₀ C).map α.τ₃).f 0 ≫ J₃.ι.f 0) (α.τ₃ ≫ J₃.ι.f 0) :=
      congrArg (fun f => f ≫ J₃.ι.f 0) hmap
    exact h₁.trans h₂

end Functor.RightDerived.HorseshoeData
end CategoryTheory
