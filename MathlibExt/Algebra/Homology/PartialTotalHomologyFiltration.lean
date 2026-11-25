/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.PartialTotalEIntFiltration
public import Mathlib.CategoryTheory.Filtration.Basic
import Mathlib.Algebra.Homology.Refinements

/-!
# The homology filtration of partial totals

The images of the maps from partial-total homology to total homology
form an increasing filtration. In degree n it is zero at ⊥, full at ⊤
and exhaustive at stage n.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

/-- Degree-`n` homology of the extended partial-total filtration. -/
abbrev partialTotalHomologyFunctor (n : ℕ) : EInt ⥤ C :=
  B.partialTotalEIntFiltration ⋙
    HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n

/-- The extended partial-total filtration maps naturally to its full total
object at `⊤`. -/
noncomputable def partialTotalEIntToTotal :
    B.partialTotalEIntFiltration ⟶
      (Functor.const EInt).obj (B.total (ComplexShape.down ℕ)) :=
  let toTop : B.partialTotalEIntFiltration ⟶
      (Functor.const EInt).obj (B.partialTotalEIntFiltration.obj ⊤) :=
    { app := fun a => B.partialTotalEIntFiltration.map
        (homOfLE (show a ≤ (⊤ : EInt) by simp))
      naturality := fun {a b} f => by
        change B.partialTotalEIntFiltration.map f ≫
            B.partialTotalEIntFiltration.map
              (homOfLE (show b ≤ (⊤ : EInt) by simp)) =
          B.partialTotalEIntFiltration.map
              (homOfLE (show a ≤ (⊤ : EInt) by simp)) ≫ 𝟙 _
        rw [Category.comp_id, ← Functor.map_comp]
        rw [Subsingleton.elim
          (f ≫ homOfLE (show b ≤ (⊤ : EInt) by simp))
          (homOfLE (show a ≤ (⊤ : EInt) by simp))] }
  toTop ≫
    (Functor.const EInt).map
      (eqToHom (show B.partialTotalEIntFiltration.obj ⊤ =
        B.total (ComplexShape.down ℕ) from
          B.partialTotalEIntFiltration_obj_top))

/-- The natural transformation from homology of the extended partial-total
filtration to the constant homology of the full total complex. -/
noncomputable def partialTotalHomologyToTotal (n : ℕ) :
    B.partialTotalHomologyFunctor n ⟶
      (Functor.const EInt).obj
        ((B.total (ComplexShape.down ℕ)).homology n) where
  app a := (HomologicalComplex.homologyFunctor C
    (ComplexShape.down ℕ) n).map
      ((partialTotalEIntToTotal B).app a)
  naturality {a b} f := by
    let H := HomologicalComplex.homologyFunctor C
      (ComplexShape.down ℕ) n
    change H.map (B.partialTotalEIntFiltration.map f) ≫
        H.map ((partialTotalEIntToTotal B).app b) =
      H.map ((partialTotalEIntToTotal B).app a) ≫ 𝟙 _
    calc
      _ = H.map (B.partialTotalEIntFiltration.map f ≫
          (partialTotalEIntToTotal B).app b) :=
        (H.map_comp _ _).symm
      _ = H.map ((partialTotalEIntToTotal B).app a ≫
          ((Functor.const EInt).obj
            (B.total (ComplexShape.down ℕ))).map f) :=
        congrArg (fun k => H.map k)
          ((partialTotalEIntToTotal B).naturality f)
      _ = H.map ((partialTotalEIntToTotal B).app a) ≫
          H.map (((Functor.const EInt).obj
            (B.total (ComplexShape.down ℕ))).map f) :=
        H.map_comp _ _
      _ = H.map ((partialTotalEIntToTotal B).app a) := by
        rw [Functor.const_obj_map]
        rw [show H.map (𝟙 (B.total (ComplexShape.down ℕ))) = 𝟙 _ from
          H.map_id _]
        exact Category.comp_id _
      _ = H.map ((partialTotalEIntToTotal B).app a) ≫ 𝟙 _ :=
        (Category.comp_id _).symm

/-- The degree-`n` partial-total homology maps, regarded as objects over the
homology of the full total complex. -/
noncomputable def partialTotalHomologyOverFunctor (n : ℕ) :
    EInt ⥤ Over ((B.total (ComplexShape.down ℕ)).homology n) :=
  (B.partialTotalHomologyFunctor n).toOver _
    (fun a => (B.partialTotalHomologyToTotal n).app a)
    (fun f => by simpa using (B.partialTotalHomologyToTotal n).naturality f)

/-- The image filtration on degree-`n` homology induced by the partial-total
tower. -/
noncomputable def partialTotalHomologyFiltration (n : ℕ) :
    Filtration ((B.total (ComplexShape.down ℕ)).homology n) EInt where
  toMonoOver := B.partialTotalHomologyOverFunctor n ⋙
    MonoOver.image

/-- The filtration inclusion is the image inclusion of the corresponding
partial-total homology map. -/
@[simp]
theorem partialTotalHomologyFiltration_ι_app (n : ℕ) (a : EInt) :
    (B.partialTotalHomologyFiltration n).ι.app a =
      image.ι ((B.partialTotalHomologyToTotal n).app a) :=
  rfl

/-- Maps between filtration steps commute with their inclusions into total
homology. -/
@[reassoc]
theorem partialTotalHomologyFiltration_map_comp_ι
    (n : ℕ) {a b : EInt} (h : a ≤ b) :
    (B.partialTotalHomologyFiltration n).diagram.map (homOfLE h) ≫
        (B.partialTotalHomologyFiltration n).ι.app b =
      (B.partialTotalHomologyFiltration n).ι.app a := by
  have hnat := (B.partialTotalHomologyFiltration n).ι.naturality (homOfLE h)
  change
    (B.partialTotalHomologyFiltration n).diagram.map (homOfLE h) ≫
        (B.partialTotalHomologyFiltration n).ι.app b =
      (B.partialTotalHomologyFiltration n).ι.app a ≫ 𝟙 _ at hnat
  simpa only [Category.comp_id] using hnat

/-- In degrees retained by a partial total, its componentwise inclusion into
the full total complex is an isomorphism. -/
theorem partialTotalι_f_isIso_of_le (p k : ℕ) (hkp : k ≤ p) :
    IsIso ((B.partialTotalι p).f k) := by
  let e := ComplexShape.embeddingDownNatInitialSegment p
  let φ := B.ιStupidTrunc e
  let π := ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)
  let θ := HomologicalComplex₂.toGradedObjectMap φ
  let hEpi : ∀ x : π ⁻¹' {k}, Epi (θ x.1) := fun x => by
    rcases x with ⟨⟨i, j⟩, hij⟩
    change i + j = k at hij
    let a : Fin (p + 1) := ⟨i, by omega⟩
    change Epi ((φ.f i).f j)
    let : IsIso (φ.f i) := HomologicalComplex.isIso_ιStupidTrunc_f B e
      (show e.f a = i from rfl)
    change Epi ((HomologicalComplex.eval C (ComplexShape.down ℕ) j).map (φ.f i))
    infer_instance
  have hEpi' : Epi ((B.partialTotalι p).f k) := by
    change Epi (GradedObject.mapMap θ π k)
    apply (Preadditive.epi_iff_cancel_zero _).2
    intro Z g hg
    apply GradedObject.mapObj_ext
    intro i hi
    let _ : Epi (θ i) := hEpi ⟨i, hi⟩
    rw [← cancel_epi (θ i)]
    simp only [comp_zero]
    rw [← GradedObject.ι_mapMap_assoc, hg, comp_zero]
  let _ : Epi ((B.partialTotalι p).f k) := hEpi'
  exact isIso_of_mono_of_epi _

private theorem epi_homologyMap_partialTotalι_degree (n : ℕ) :
    Epi (HomologicalComplex.homologyMap (B.partialTotalι n) n) := by
  let _ : IsIso ((B.partialTotalι n).f n) :=
    B.partialTotalι_f_isIso_of_le n n le_rfl
  have hnext : (ComplexShape.down ℕ).next n ≤ n := by
    rcases n with _ | n
    · simpa only [ChainComplex.next_nat_zero] using (le_rfl : 0 ≤ 0)
    · simp only [ChainComplex.next_nat_succ]
      omega
  let _ : IsIso
      ((B.partialTotalι n).f ((ComplexShape.down ℕ).next n)) :=
    B.partialTotalι_f_isIso_of_le n _ hnext
  rw [HomologicalComplex.epi_homologyMap_iff_up_to_refinements
    (φ := B.partialTotalι n)
    ((ComplexShape.down ℕ).prev n) n
    ((ComplexShape.down ℕ).next n) rfl rfl]
  intro A y₂ hy₂
  let x₂ : A ⟶ (B.partialTotal n).X n :=
    y₂ ≫ inv ((B.partialTotalι n).f n)
  have hx₂ : x₂ ≫ (B.partialTotal n).d n
      ((ComplexShape.down ℕ).next n) = 0 := by
    rw [← cancel_mono
      ((B.partialTotalι n).f ((ComplexShape.down ℕ).next n))]
    simp only [x₂, Category.assoc]
    rw [← (B.partialTotalι n).comm]
    slice_lhs 2 3 => rw [IsIso.inv_hom_id]
    simpa only [Category.id_comp, zero_comp] using hy₂
  exact ⟨A, 𝟙 A, inferInstance, x₂, hx₂, 0, by simp [x₂]⟩

/-- The finite-stage image coordinate of the partial-total homology
filtration. -/
noncomputable def partialTotalHomologyFiltrationObjIsoImage
    (n p : ℕ) :
    (B.partialTotalHomologyFiltration n).obj ((p : ℤ) : EInt) ≅
      image (HomologicalComplex.homologyMap (B.partialTotalι p) n) := by
  let H := HomologicalComplex.homologyFunctor C
    (ComplexShape.down ℕ) n
  let e := H.mapIso (B.partialTotalEIntFiltrationObjIso p)
  let f : H.obj (B.partialTotal p) ⟶
      H.obj (B.total (ComplexShape.down ℕ)) :=
    H.map (B.partialTotalι p)
  let stage : H.obj (B.partialTotalEIntFiltration.obj ((p : ℤ) : EInt)) ⟶
      H.obj (B.total (ComplexShape.down ℕ)) :=
    (B.partialTotalHomologyToTotal n).app ((p : ℤ) : EInt)
  have hstageRaw :
      (B.partialTotalEIntFiltrationObjIso p).hom ≫
          B.partialTotalι p =
        (B.partialTotalEIntToTotal).app ((p : ℤ) : EInt) := by
    rw [← cancel_epi (B.partialTotalEIntFiltrationObjIso p).inv]
    change
      (B.partialTotalEIntFiltrationObjIso p).inv ≫
          ((B.partialTotalEIntFiltrationObjIso p).hom ≫
            B.partialTotalι p) =
        (B.partialTotalEIntFiltrationObjIso p).inv ≫
          (B.partialTotalEIntFiltration.map
            (homOfLE (show ((p : ℤ) : EInt) ≤ ⊤ by simp)) ≫ 𝟙 _)
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp,
      ← Category.assoc,
      B.partialTotalEIntFiltrationObjIso_inv_comp_toTop p,
      Category.comp_id]
  have hstage : stage = e.hom ≫ f := by
    change H.map ((B.partialTotalEIntToTotal).app ((p : ℤ) : EInt)) =
      H.map (B.partialTotalEIntFiltrationObjIso p).hom ≫
        H.map (B.partialTotalι p)
    simpa only [Functor.map_comp] using
      (congrArg (fun k => H.map k) hstageRaw).symm
  exact image.eqToIso hstage ≪≫
    asIso (image.preComp e.hom f)

/-- The finite-stage image coordinate commutes with the filtration inclusion. -/
@[reassoc]
theorem partialTotalHomologyFiltrationObjIsoImage_hom_comp_ι
    (n p : ℕ) :
    (B.partialTotalHomologyFiltrationObjIsoImage n p).hom ≫
        image.ι (HomologicalComplex.homologyMap (B.partialTotalι p) n) =
      (B.partialTotalHomologyFiltration n).ι.app ((p : ℤ) : EInt) := by
  let H := HomologicalComplex.homologyFunctor C
    (ComplexShape.down ℕ) n
  let e := H.mapIso (B.partialTotalEIntFiltrationObjIso p)
  let f : H.obj (B.partialTotal p) ⟶
      H.obj (B.total (ComplexShape.down ℕ)) :=
    H.map (B.partialTotalι p)
  let stage : H.obj (B.partialTotalEIntFiltration.obj ((p : ℤ) : EInt)) ⟶
      H.obj (B.total (ComplexShape.down ℕ)) :=
    (B.partialTotalHomologyToTotal n).app ((p : ℤ) : EInt)
  have hstageRaw :
      (B.partialTotalEIntFiltrationObjIso p).hom ≫
          B.partialTotalι p =
        (B.partialTotalEIntToTotal).app ((p : ℤ) : EInt) := by
    rw [← cancel_epi (B.partialTotalEIntFiltrationObjIso p).inv]
    change
      (B.partialTotalEIntFiltrationObjIso p).inv ≫
          ((B.partialTotalEIntFiltrationObjIso p).hom ≫
            B.partialTotalι p) =
        (B.partialTotalEIntFiltrationObjIso p).inv ≫
          (B.partialTotalEIntFiltration.map
            (homOfLE (show ((p : ℤ) : EInt) ≤ ⊤ by simp)) ≫ 𝟙 _)
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp,
      ← Category.assoc,
      B.partialTotalEIntFiltrationObjIso_inv_comp_toTop p,
      Category.comp_id]
  have hstage : stage = e.hom ≫ f := by
    change H.map ((B.partialTotalEIntToTotal).app ((p : ℤ) : EInt)) =
      H.map (B.partialTotalEIntFiltrationObjIso p).hom ≫
        H.map (B.partialTotalι p)
    simpa only [Functor.map_comp] using
      (congrArg (fun k => H.map k) hstageRaw).symm
  change ((image.eqToIso hstage).hom ≫
      (asIso (image.preComp e.hom f)).hom) ≫ image.ι f =
    image.ι stage
  rw [Category.assoc]
  change (image.eqToIso hstage).hom ≫
      (image.preComp e.hom f ≫ image.ι f) = image.ι stage
  rw [image.preComp_ι]
  exact (image.eq_fac hstage).symm

/-- The bottom stage of the partial-total homology filtration is zero. -/
theorem isZero_partialTotalHomologyFiltration_obj_bot (n : ℕ) :
    IsZero ((B.partialTotalHomologyFiltration n).obj ⊥) := by
  let H := HomologicalComplex.homologyFunctor C
    (ComplexShape.down ℕ) n
  have hsource : IsZero
      (H.obj (B.partialTotalEIntFiltration.obj ⊥)) := by
    rw [B.partialTotalEIntFiltration_obj_bot]
    exact H.map_isZero (isZero_zero _)
  have hzero : (B.partialTotalHomologyToTotal n).app ⊥ = 0 :=
    hsource.eq_of_src _ _
  change IsZero (image ((B.partialTotalHomologyToTotal n).app ⊥))
  exact IsZero.of_iso (isZero_zero C) (imageZero' hzero)

/-- The top filtration inclusion is an isomorphism. -/
theorem partialTotalHomologyFiltration_ι_app_top_isIso (n : ℕ) :
    IsIso ((B.partialTotalHomologyFiltration n).ι.app ⊤) := by
  let f := (B.partialTotalHomologyToTotal n).app ⊤
  have hToTop : IsIso (B.partialTotalEIntFiltration.map
      (homOfLE (show (⊤ : EInt) ≤ ⊤ by simp))) := by
    rw [Subsingleton.elim
      (homOfLE (show (⊤ : EInt) ≤ ⊤ by simp)) (𝟙 (⊤ : EInt))]
    exact Functor.map_isIso _ _
  let _ : IsIso (B.partialTotalEIntFiltration.map
      (homOfLE (show (⊤ : EInt) ≤ ⊤ by simp))) := hToTop
  have hChain : IsIso ((B.partialTotalEIntToTotal).app ⊤) := by
    change IsIso (B.partialTotalEIntFiltration.map
      (homOfLE (show (⊤ : EInt) ≤ ⊤ by simp)) ≫
        eqToHom (show B.partialTotalEIntFiltration.obj ⊤ =
          B.total (ComplexShape.down ℕ) from
            B.partialTotalEIntFiltration_obj_top))
    infer_instance
  let _ : IsIso ((B.partialTotalEIntToTotal).app ⊤) := hChain
  have hf : IsIso f := by
    change IsIso ((HomologicalComplex.homologyFunctor C
      (ComplexShape.down ℕ) n).map
        ((B.partialTotalEIntToTotal).app ⊤))
    infer_instance
  let _ : IsIso f := hf
  have hEpi : Epi (image.ι f) := epi_image_of_epi f
  let _ : Epi (image.ι f) := hEpi
  change IsIso (image.ι f)
  exact isIso_of_mono_of_epi _

/-- In homological degree `n`, the image filtration is already exhaustive at
filtration stage `n`. -/
theorem partialTotalHomologyFiltration_exhaustive_at_degree (n : ℕ) :
    IsIso ((B.partialTotalHomologyFiltration n).ι.app
      (((n : ℤ) : EInt))) := by
  let f := HomologicalComplex.homologyMap (B.partialTotalι n) n
  let _ : Epi f := B.epi_homologyMap_partialTotalι_degree n
  have hImageEpi : Epi (image.ι f) := epi_image_of_epi f
  let e := B.partialTotalHomologyFiltrationObjIsoImage n n
  let _ : Epi (image.ι f) := hImageEpi
  let _ : IsIso (image.ι f) := isIso_of_mono_of_epi _
  have hComp : IsIso (e.hom ≫ image.ι f) :=
    IsIso.comp_isIso' inferInstance inferInstance
  rw [B.partialTotalHomologyFiltrationObjIsoImage_hom_comp_ι n n] at hComp
  exact hComp

end HomologicalComplex₂

end
