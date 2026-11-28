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
public import Mathlib.CategoryTheory.Shift.ShiftedHom

/-!
# Cocycle boundaries and shifted morphisms

For integer cochain complexes in a preadditive category, a degree-q cocycle represents a
map to a q-shift. Removing a target shift by one raises its degree to q+1 without an
extra sign. Postcomposition by a degree-one morphism uses the shift-add order 1,q;
the sign of that morphism is retained.

A functor F commuting with shifts sends the cocycle z to the shifted morphism
F(ẑ) followed by the shift comparison. This assignment carries the triangle-boundary
expression to postcomposition followed by removal of the target shift. The quotient
into the homotopy category is one such functor. Shifted composition also commutes with
transport along isomorphisms of its two intermediate endpoints.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
universe u v u' v'

namespace CochainComplex.HomComplex

section CocycleShift
variable {C : Type u} [Category.{v} C] [Preadditive C]
namespace Cocycle
variable {K L M : CochainComplex C ℤ} {q : ℤ}

set_option backward.isDefEq.respectTransparency false in
/-- Let C be preadditive, K,M integer cochain complexes and q ∈ ℤ. For a degree-q cocycle z from K
to M[1], let ẑ : K → (M[1])[q] be its corresponding cochain map. Removing the target shift gives
a degree-(q+1) cocycle to M whose corresponding map is ẑ followed by the inverse shift-add
isomorphism M[q+1] ≅ (M[1])[q]. The shift-add order is 1,q. -/
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

/-- Let C be preadditive, K,L,M integer cochain complexes, q ∈ ℤ, z a degree-q cocycle from K to L,
and d : L → M[1] a cochain map. The map corresponding to the target-unshifted cocycle z
postcomposed with d is ẑ ≫ d[q] ≫ α_{1,q,M}⁻¹ : K → M[q+1], where ẑ : K → L[q] represents z and
α_{1,q,M} : M[q+1] ≅ (M[1])[q]. -/
theorem equivHomShift_symm_postcomp_rightUnshift
    (z : Cocycle K L q) (d : L ⟶ M⟦(1 : ℤ)⟧) :
    equivHomShift.symm ((z.postcomp d).rightUnshift (q + 1) rfl) =
      ShiftedHom.comp (equivHomShift.symm z) d (by omega) := by
  dsimp only [ShiftedHom.comp]
  rw [equivHomShift_symm_rightUnshift, equivHomShift_symm_postcomp]
  exact Category.assoc _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- Let C be preadditive, K,L,M integer cochain complexes, q ∈ ℤ, z a degree-q cocycle K → L and a a
degree-one cocycle L → M. Postcomposing z with the cochain map L → M[1] represented by a and
then removing the target shift gives the homogeneous cochain z.comp(a) of degree q+1. There is
no additional sign; a minus already present in a, including a negative mapping-cone boundary, is
retained. -/
theorem postcomp_equivHomShift_rightUnshift
    {K L M : CochainComplex C ℤ} {q : ℤ} (z : Cocycle K L q) (a : Cocycle L M 1) :
    ((z.postcomp (equivHomShift.symm a)).rightUnshift (q + 1) rfl).val = z.val.comp a.val rfl := by
  change (z.val.comp (Cochain.ofHom (equivHomShift.symm a)) (add_zero q)).rightUnshift
      (q + 1) rfl = z.val.comp a.val rfl
  rw [Cochain.rightUnshift_comp _ _ (add_zero q) (q + 1) rfl 1 (zero_add 1)]
  have h := congrArg Subtype.val (equivHomShift.apply_symm_apply a)
  change (Cochain.ofHom (equivHomShift.symm a)).rightUnshift 1 (zero_add 1) = a.val at h
  rw [h]

end Cocycle
end CocycleShift

section Mapped
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {D : Type u'} [Category.{v'} D] [HasShift D ℤ]
namespace Cocycle

/-- Let C be preadditive, D a category with integer shifts, and F : CochainComplex C ℤ → D
commute with shifts. A degree-q cocycle z from K to L defines F(ẑ) followed by the shift
comparison, as a morphism F(K) → F(L)[q]. -/
abbrev mappedShiftedHom (F : CochainComplex C ℤ ⥤ D) [F.CommShift ℤ]
    {K L : CochainComplex C ℤ} {q : ℤ} (z : Cocycle K L q) :
    F.obj K ⟶ (F.obj L)⟦q⟧ :=
  ShiftedHom.map (equivHomShift.symm z) F

/-- Let C be preadditive, D a category with integer shifts and F : CochainComplex C ℤ → D commute
with shifts. For a degree-q cocycle z from K to L and a cochain map g : L → M,
mappedShiftedHom(F,z postcomposed with g) = mappedShiftedHom(F,z) ≫ F(g)[q] as maps F(K) →
F(M)[q]. -/
theorem mappedShiftedHom_postcomp (F : CochainComplex C ℤ ⥤ D) [F.CommShift ℤ]
    {K L M : CochainComplex C ℤ} {q : ℤ} (z : Cocycle K L q) (g : L ⟶ M) :
    mappedShiftedHom F (z.postcomp g) = mappedShiftedHom F z ≫ (F.map g)⟦q⟧' := by
  dsimp only [mappedShiftedHom, ShiftedHom.map]
  rw [equivHomShift_symm_postcomp, Functor.map_comp, Category.assoc,
    F.commShiftIso_hom_naturality]
  exact (Category.assoc _ _ _).symm

variable [Preadditive D]

/-- Native shifted composition carries a cocycle boundary through a shift-compatible functor.
The triangle need not be distinguished and no additional boundary sign is introduced. -/
theorem mappedShiftedHom_boundary (F : CochainComplex C ℤ ⥤ D) [F.CommShift ℤ]
    (T : Triangle (CochainComplex C ℤ)) {K : CochainComplex C ℤ}
    (q : ℤ) (z : Cocycle K T.obj₃ q) :
    (preadditiveCoyoneda.obj (op (F.obj K))).homologySequenceδ
        (F.mapTriangle.obj T) q (q + 1) rfl (mappedShiftedHom F z) =
      mappedShiftedHom F ((z.postcomp T.mor₃).rightUnshift (q + 1) rfl) := by
  rw [Pretriangulated.preadditiveCoyoneda_homologySequenceδ_apply]
  dsimp only [mappedShiftedHom]
  rw [equivHomShift_symm_postcomp_rightUnshift]
  change (ShiftedHom.map (equivHomShift.symm z) F).comp
      (ShiftedHom.map T.mor₃ F) (by omega) =
    ShiftedHom.map (ShiftedHom.comp (equivHomShift.symm z) T.mor₃ (by omega)) F
  exact (ShiftedHom.map_comp (equivHomShift.symm z) T.mor₃ (by omega) F).symm

end Cocycle
end Mapped

section Quotient
variable {C : Type u} [Category.{v} C] [Preadditive C]
namespace Cocycle

/-- The cocycle's canonical shifted morphism in the homotopy category. -/
abbrev shiftedHom {K L : CochainComplex C ℤ} {q : ℤ} (z : Cocycle K L q) :
    (HomotopyCategory.quotient C (.up ℤ)).obj K ⟶
      ((HomotopyCategory.quotient C (.up ℤ)).obj L)⟦q⟧ :=
  mappedShiftedHom (HomotopyCategory.quotient C (.up ℤ)) z

/-- The homotopy-category boundary is the generic mapped boundary specialization. -/
theorem shiftedHom_boundary
    (T : Triangle (CochainComplex C ℤ)) {K : CochainComplex C ℤ}
    (q : ℤ) (z : Cocycle K T.obj₃ q) :
    (preadditiveCoyoneda.obj (op ((HomotopyCategory.quotient C (.up ℤ)).obj K))).homologySequenceδ
        ((HomotopyCategory.quotient C (.up ℤ)).mapTriangle.obj T) q (q + 1) rfl z.shiftedHom =
      ((z.postcomp T.mor₃).rightUnshift (q + 1) rfl).shiftedHom := by
  simpa only [shiftedHom] using
    mappedShiftedHom_boundary (HomotopyCategory.quotient C (.up ℤ)) T q z

end Cocycle
end Quotient

section Single
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
namespace Cochain

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Let C be preadditive with a zero object, Z an object, K an integer cochain complex, and a,q ∈ ℤ.
A map f : Z → K^{q+a} defines a degree-q cochain from Z[0] to K[a]. Removing the target shift
produces exactly the degree-(q+a) cochain from Z[0] to K defined by the same map f. -/
theorem fromSingleMk_rightUnshift (Z : C) (K : CochainComplex C ℤ) (a q : ℤ)
    (f : Z ⟶ K.X (q + a)) :
    (fromSingleMk (X := Z) (K := K⟦a⟧) (p := 0) (q := q) (n := q)
      f (zero_add q)).rightUnshift (q + a) rfl =
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

end Cochain
end Single
end CochainComplex.HomComplex

namespace CategoryTheory.ShiftedHom
variable {C : Type u} [Category.{v} C] [HasShift C ℤ]

/-- Let C be a category with integer shifts, e : X ≅ A and f : Y ≅ B isomorphisms, and d : X → Y[1],
d′ : A → B[1] maps satisfying d ≫ f.hom[1] = e.hom ≫ d′. For q ∈ ℤ and x : Z → A[q], define
δ_d^q(y) = y ≫ d[q] ≫ α_{1,q,Y}⁻¹, where α_{1,q,Y} : Y[q+1] ≅ (Y[1])[q]. Then δ_d^q(x ≫
e.inv[q]) = δ_d′^q(x) ≫ f.inv[q+1], as maps Z → Y[q+1]. -/
theorem comp_iso_transport
    {X Y A B Z : C} (e : X ≅ A) (f : Y ≅ B)
    (d : X ⟶ Y⟦(1 : ℤ)⟧) (d' : A ⟶ B⟦(1 : ℤ)⟧)
    (hd : d ≫ f.hom⟦(1 : ℤ)⟧' = e.hom ≫ d') (q : ℤ)
    (x : Z ⟶ A⟦q⟧) :
    ShiftedHom.comp (x ≫ e.inv⟦q⟧') d (by omega) =
      ShiftedHom.comp x d' (by omega) ≫ f.inv⟦q + 1⟧' := by
  dsimp only [ShiftedHom.comp]
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

end CategoryTheory.ShiftedHom
end
