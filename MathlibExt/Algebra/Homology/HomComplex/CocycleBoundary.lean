/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Authors: @toskua, Avocado
module
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.CategoryTheory.Triangulated.Yoneda

@[expose] public section

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe u v
namespace CochainComplex.HomComplex.Cocycle
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {K L M : CochainComplex C ℤ} {q : ℤ}

set_option backward.isDefEq.respectTransparency false in
/-- Removing the target shift is the original inverse shift-add map. -/
theorem equivHomShift_symm_rightUnshift
    (z : Cocycle K (M⟦(1 : ℤ)⟧) q) :
    equivHomShift.symm (z.rightUnshift (q + 1) rfl) =
      equivHomShift.symm z ≫
        (CategoryTheory.shiftFunctorAdd' (CochainComplex C ℤ) 1 q (q + 1)
          (by omega)).inv.app M := by
  apply equivHomShift.injective
  simp only [AddEquiv.apply_symm_apply]
  apply Cocycle.ext
  ext p r hpr
  rw [equivHomShift_apply]
  change (z.val.rightUnshift (q + 1) rfl).v p r hpr =
    ((Cochain.ofHom (equivHomShift.symm z ≫
      (CategoryTheory.shiftFunctorAdd' (CochainComplex C ℤ) 1 q (q + 1)
        (by omega)).inv.app M)).rightUnshift (q + 1) (zero_add _)).v p r hpr
  rw [Cochain.rightUnshift_v _ (q + 1) rfl p r hpr (p + q) rfl,
    Cochain.rightUnshift_v _ (q + 1) (zero_add _) p r hpr p (add_zero p),
    Cochain.ofHom_v, HomologicalComplex.comp_f,
    CochainComplex.shiftFunctorAdd'_inv_app_f']
  simp only [equivHomShift_symm_apply, homOf_f]
  change z.val.v p (p + q) rfl ≫ _ =
    ((z.val.rightShift q 0 (zero_add q)).v p p (add_zero p) ≫ _) ≫ _
  rw [Cochain.rightShift_v z.val q 0 (zero_add q) p p (add_zero p) (p + q) rfl]
  simp [shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq, Category.assoc]

/--
The degree-one shifted representative has the same covariant composition and the original
shift-add order 1,q.
-/
theorem equivHomShift_symm_postcomp_rightUnshift
    (z : Cocycle K L q) (d : L ⟶ M⟦(1 : ℤ)⟧) :
    equivHomShift.symm ((z.postcomp d).rightUnshift (q + 1) rfl) =
      equivHomShift.symm z ≫ d⟦q⟧' ≫
        (CategoryTheory.shiftFunctorAdd' (CochainComplex C ℤ) 1 q (q + 1)
          (by omega)).inv.app M := by
  rw [equivHomShift_symm_rightUnshift, equivHomShift_symm_postcomp]
  exact Category.assoc _ _ _

end CochainComplex.HomComplex.Cocycle

end

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
universe u v
namespace CochainComplex.HomComplex
variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The quotient representative transported to the shifted object. -/
def Cocycle.shiftedHom {K L : CochainComplex C ℤ} {q : ℤ} (z : Cocycle K L q) :
    (HomotopyCategory.quotient C (.up ℤ)).obj K ⟶
      ((HomotopyCategory.quotient C (.up ℤ)).obj L)⟦q⟧ :=
  (HomotopyCategory.quotient C (.up ℤ)).map (Cocycle.equivHomShift.symm z) ≫
    ((HomotopyCategory.quotient C (.up ℤ)).commShiftIso q).hom.app L

/--
The original grade-one triangle boundary acts by the exact shifted cocycle representative, with
the quotient's shift transport.
-/
theorem Cocycle.shiftedHom_boundary
    (T : Triangle (CochainComplex C ℤ)) {K : CochainComplex C ℤ}
    (q : ℤ) (z : Cocycle K T.obj₃ q) :
    (preadditiveCoyoneda.obj (op ((HomotopyCategory.quotient C (.up ℤ)).obj K))).homologySequenceδ
        ((HomotopyCategory.quotient C (.up ℤ)).mapTriangle.obj T) q (q + 1) rfl
        z.shiftedHom =
      ((z.postcomp T.mor₃).rightUnshift (q + 1) rfl).shiftedHom := by
  rw [Pretriangulated.preadditiveCoyoneda_homologySequenceδ_apply]
  dsimp only [Cocycle.shiftedHom]
  rw [Cocycle.equivHomShift_symm_postcomp_rightUnshift]
  simp only [Functor.map_comp, Category.assoc]
  let Q := HomotopyCategory.quotient C (.up ℤ)
  have hc := congrArg (fun e => e.hom.app T.obj₁)
    (Q.commShiftIso_add' (a := (1 : ℤ)) (b := q) (c := q + 1) (by omega))
  simp only [Functor.CommShift.isoAdd'_hom_app] at hc
  have hn := Q.commShiftIso_hom_naturality T.mor₃ q
  change Q.map (Cocycle.equivHomShift.symm z) ≫
      (Q.commShiftIso q).hom.app T.obj₃ ≫
      (Q.map T.mor₃ ≫ (Q.commShiftIso 1).hom.app T.obj₁)⟦q⟧' ≫
      (CategoryTheory.shiftFunctorAdd' (HomotopyCategory C (.up ℤ)) 1 q (q + 1)
        (by omega)).inv.app (Q.obj T.obj₁) = _
  rw [Functor.map_comp]
  let A := (CategoryTheory.shiftFunctorAdd' (HomotopyCategory C (.up ℤ)) 1 q (q + 1)
        (by omega)).inv.app (Q.obj T.obj₁)
  have hn' := congrArg (fun a =>
    a ≫ ((Q.commShiftIso 1).hom.app T.obj₁)⟦q⟧' ≫ A) hn
  simp only [Category.assoc] at hn'
  simp only [Category.assoc]
  change Q.map (Cocycle.equivHomShift.symm z) ≫
    ((Q.commShiftIso q).hom.app T.obj₃ ≫ (Q.map T.mor₃)⟦q⟧' ≫
      ((Q.commShiftIso 1).hom.app T.obj₁)⟦q⟧' ≫ A) = _
  rw [← hn']
  rw [hc]
  let e := CategoryTheory.shiftFunctorAdd' (CochainComplex C ℤ) 1 q (q + 1)
    (by omega)
  have he : Q.map (e.inv.app T.obj₁) ≫ Q.map (e.hom.app T.obj₁) = 𝟙 _ := by
    rw [← Q.map_comp, e.inv_hom_id_app, Q.map_id]
  change Q.map (Cocycle.equivHomShift.symm z) ≫
      Q.map (T.mor₃⟦q⟧') ≫ (Q.commShiftIso q).hom.app (T.obj₁⟦(1 : ℤ)⟧) ≫
      ((Q.commShiftIso 1).hom.app T.obj₁)⟦q⟧' ≫ A =
    Q.map (Cocycle.equivHomShift.symm z) ≫ Q.map (T.mor₃⟦q⟧') ≫
      Q.map (e.inv.app T.obj₁) ≫ Q.map (e.hom.app T.obj₁) ≫
      (Q.commShiftIso q).hom.app (T.obj₁⟦(1 : ℤ)⟧) ≫
      ((Q.commShiftIso 1).hom.app T.obj₁)⟦q⟧' ≫ A
  rw [reassoc_of% he]


end CochainComplex.HomComplex

end

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
universe u v u' v'
namespace CochainComplex.HomComplex
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasShift D ℤ]
variable (F : CochainComplex C ℤ ⥤ D) [F.CommShift ℤ]

/-- The SAME original cocycle representative mapped through a functor with its shift transport. -/
def Cocycle.mappedShiftedHom {K L : CochainComplex C ℤ} {q : ℤ} (z : Cocycle K L q) :
    F.obj K ⟶ (F.obj L)⟦q⟧ :=
  F.map (Cocycle.equivHomShift.symm z) ≫ (F.commShiftIso q).hom.app L

/--
The original grade-one triangle boundary acts by the exact shifted cocycle representative, with
the given functor's shift transport.
-/
theorem Cocycle.mappedShiftedHom_boundary
    (T : Triangle (CochainComplex C ℤ)) {K : CochainComplex C ℤ}
    (q : ℤ) (z : Cocycle K T.obj₃ q) :
    (preadditiveCoyoneda.obj (op (F.obj K))).homologySequenceδ
        (F.mapTriangle.obj T) q (q + 1) rfl
        (Cocycle.mappedShiftedHom F z) =
      Cocycle.mappedShiftedHom F ((z.postcomp T.mor₃).rightUnshift (q + 1) rfl) := by
  rw [Pretriangulated.preadditiveCoyoneda_homologySequenceδ_apply]
  dsimp only [Cocycle.mappedShiftedHom]
  rw [Cocycle.equivHomShift_symm_postcomp_rightUnshift]
  simp only [Functor.map_comp, Category.assoc]
  let Q := F
  have hc := congrArg (fun e => e.hom.app T.obj₁)
    (Q.commShiftIso_add' (a := (1 : ℤ)) (b := q) (c := q + 1) (by omega))
  simp only [Functor.CommShift.isoAdd'_hom_app] at hc
  have hn := Q.commShiftIso_hom_naturality T.mor₃ q
  change Q.map (Cocycle.equivHomShift.symm z) ≫
      (Q.commShiftIso q).hom.app T.obj₃ ≫
      (Q.map T.mor₃ ≫ (Q.commShiftIso 1).hom.app T.obj₁)⟦q⟧' ≫
      (CategoryTheory.shiftFunctorAdd' D 1 q (q + 1)
        (by omega)).inv.app (Q.obj T.obj₁) = _
  rw [Functor.map_comp]
  let A := (CategoryTheory.shiftFunctorAdd' D 1 q (q + 1)
        (by omega)).inv.app (Q.obj T.obj₁)
  have hn' := congrArg (fun a =>
    a ≫ ((Q.commShiftIso 1).hom.app T.obj₁)⟦q⟧' ≫ A) hn
  simp only [Category.assoc] at hn'
  simp only [Category.assoc]
  change Q.map (Cocycle.equivHomShift.symm z) ≫
    ((Q.commShiftIso q).hom.app T.obj₃ ≫ (Q.map T.mor₃)⟦q⟧' ≫
      ((Q.commShiftIso 1).hom.app T.obj₁)⟦q⟧' ≫ A) = _
  rw [← hn']
  rw [hc]
  let e := CategoryTheory.shiftFunctorAdd' (CochainComplex C ℤ) 1 q (q + 1)
    (by omega)
  have he : Q.map (e.inv.app T.obj₁) ≫ Q.map (e.hom.app T.obj₁) = 𝟙 _ := by
    rw [← Q.map_comp, e.inv_hom_id_app, Q.map_id]
  change Q.map (Cocycle.equivHomShift.symm z) ≫
      Q.map (T.mor₃⟦q⟧') ≫ (Q.commShiftIso q).hom.app (T.obj₁⟦(1 : ℤ)⟧) ≫
      ((Q.commShiftIso 1).hom.app T.obj₁)⟦q⟧' ≫ A =
    Q.map (Cocycle.equivHomShift.symm z) ≫ Q.map (T.mor₃⟦q⟧') ≫
      Q.map (e.inv.app T.obj₁) ≫ Q.map (e.hom.app T.obj₁) ≫
      (Q.commShiftIso q).hom.app (T.obj₁⟦(1 : ℤ)⟧) ≫
      ((Q.commShiftIso 1).hom.app T.obj₁)⟦q⟧' ≫ A
  rw [reassoc_of% he]


end CochainComplex.HomComplex

end

noncomputable section
set_option autoImplicit false
open CategoryTheory
universe u v u' v'
namespace CochainComplex.HomComplex.Cocycle
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasShift D ℤ]

omit [Preadditive D] in
/--
The SAME mapped original cocycle representative is natural under every chain map, using the given
functor's original shift comparison.
-/
theorem mappedShiftedHom_postcomp (F : CochainComplex C ℤ ⥤ D) [F.CommShift ℤ]
    {K L M : CochainComplex C ℤ} {q : ℤ} (z : Cocycle K L q) (g : L ⟶ M) :
    mappedShiftedHom F (z.postcomp g) = mappedShiftedHom F z ≫ (F.map g)⟦q⟧' := by
  dsimp only [mappedShiftedHom]
  rw [equivHomShift_symm_postcomp, Functor.map_comp, Category.assoc,
    F.commShiftIso_hom_naturality]
  exact (Category.assoc _ _ _).symm

end CochainComplex.HomComplex.Cocycle

end

noncomputable section
set_option autoImplicit false
open CategoryTheory
universe u v
namespace CochainComplex.HomComplex.Cocycle
variable {C : Type u} [Category.{v} C] [Preadditive C]

set_option backward.isDefEq.respectTransparency false in
/-- A literal grade-one cocycle acts by original graded composition after
the SAME target unshift. This includes the stock mapping-cone minus. -/
theorem postcomp_equivHomShift_rightUnshift
    {K L M : CochainComplex C ℤ} {q : ℤ} (z : Cocycle K L q) (a : Cocycle L M 1) :
    ((z.postcomp (equivHomShift.symm a)).rightUnshift (q + 1) rfl).val = z.val.comp a.val rfl := by
  change (z.val.comp (Cochain.ofHom (equivHomShift.symm a)) (add_zero q)).rightUnshift
      (q + 1) rfl = z.val.comp a.val rfl
  rw [Cochain.rightUnshift_comp _ _ (add_zero q) (q + 1) rfl 1 (zero_add 1)]
  have h := congrArg Subtype.val (equivHomShift.apply_symm_apply a)
  change (Cochain.ofHom (equivHomShift.symm a)).rightUnshift 1 (zero_add 1) = a.val at h
  rw [h]

end CochainComplex.HomComplex.Cocycle

end

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe u v
namespace CochainComplex.HomComplex.Cochain
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Target right-unshift preserves the literal single-source morphism. -/
theorem fromSingleMk_rightUnshift (Z : C) (K : CochainComplex C ℤ) (a q : ℤ)
    (f : Z ⟶ K.X (q + a)) :
    (fromSingleMk (X := Z) (K := K⟦a⟧) (p := 0) (q := q) (n := q) f (zero_add q)).rightUnshift (q + a) rfl =
      fromSingleMk (X := Z) (K := K) (p := 0) (q := q + a) (n := q + a) f (zero_add (q + a)) := by
  apply (fromSingleEquiv (X := Z) (K := K) (p := 0) (q := q + a)
    (n := q + a) (zero_add (q + a))).injective
  rw [fromSingleEquiv_fromSingleMk]
  change (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Z).inv ≫
    ((fromSingleMk (X := Z) (K := K⟦a⟧) (p := 0) (q := q) (n := q) f (zero_add q)).rightUnshift
      (q + a) rfl).v 0 (q + a) (zero_add (q + a)) = f
  rw [rightUnshift_v _ (q + a) rfl 0 (q + a) (zero_add (q + a)) q (zero_add q)]
  rw [fromSingleMk_v]
  simp [CochainComplex.shiftFunctorObjXIso]


end CochainComplex.HomComplex.Cochain

end

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
universe u v
namespace CategoryTheory
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasShift C ℤ]

omit [Preadditive C] in
/--
Endpoint isomorphisms transport a grade-one triangle boundary on every original shifted morphism,
with the original shift-add order.
-/
theorem triangle_boundary_transport
    {X Y A B Z : C} (e : X ≅ A) (f : Y ≅ B)
    (d : X ⟶ Y⟦(1 : ℤ)⟧) (d' : A ⟶ B⟦(1 : ℤ)⟧)
    (hd : d ≫ f.hom⟦(1 : ℤ)⟧' = e.hom ≫ d') (q : ℤ)
    (x : Z ⟶ A⟦q⟧) :
    (x ≫ e.inv⟦q⟧') ≫ d⟦q⟧' ≫
        (shiftFunctorAdd' C 1 q (q + 1) (by omega)).inv.app Y =
    (x ≫ d'⟦q⟧' ≫
        (shiftFunctorAdd' C 1 q (q + 1) (by omega)).inv.app B) ≫
      f.inv⟦q + 1⟧' := by
  have h : e.inv ≫ d ≫ f.hom⟦(1 : ℤ)⟧' = d' := by
    rw [hd, Iso.inv_hom_id_assoc]
  have h' := congrArg (fun a => (shiftFunctor C q).map a) h
  simp only [Functor.map_comp] at h'
  apply (cancel_mono (f.hom⟦q + 1⟧')).mp
  simp only [Category.assoc, ← Functor.map_comp, f.inv_hom_id, Functor.map_id, Category.comp_id]
  rw [← (shiftFunctorAdd' C 1 q (q + 1) (by omega)).inv.naturality]
  change x ≫ (shiftFunctor C q).map e.inv ≫ (shiftFunctor C q).map d ≫
      (shiftFunctor C q).map ((shiftFunctor C 1).map f.hom) ≫
      (shiftFunctorAdd' C 1 q (q + 1) (by omega)).inv.app B = _
  simpa only [Category.assoc] using congrArg (fun t => x ≫ t ≫
    (shiftFunctorAdd' C 1 q (q + 1) (by omega)).inv.app B) h'


end CategoryTheory

end
