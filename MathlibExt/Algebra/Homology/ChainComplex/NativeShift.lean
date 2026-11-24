/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.CochainComplexOpposite
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-!
# Signed shifts of integer chain complexes

The negative-index equivalence transports the signed cochain shift to
integer chain complexes. At shift parameter `a`, the term in degree `i` is
`K.X (-(-i + a))`, identified with `K.X (i - a)`. The differential carries
the integer unit `a.negOnePow`.

The zero and addition isomorphisms are transported from the cochain shift
using the unit and counit of the negative-index equivalence. In the
translation convention with terms `K.X (i + p)`, the parameter is `a = -p`.

The sign convention follows Weibel, *An Introduction to Homological
Algebra* (1994), §1.2.8.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor HomologicalComplex

namespace ChainComplex

universe u v

variable (C : Type u) [Category.{v} C] [Preadditive C]

/-- The actual native cochain shift transported through the negative-index equivalence. -/
noncomputable def nativeShift (a : ℤ) : ChainComplex C ℤ ⥤ ChainComplex C ℤ :=
  (cochainComplexEquivalence C).functor ⋙
    CategoryTheory.shiftFunctor (CochainComplex C ℤ) a ⋙
      (cochainComplexEquivalence C).inverse

/-- Additivity is inherited from the native restriction and cochain-shift functors. -/
instance nativeShift_additive (a : ℤ) : (nativeShift C a).Additive := by
  dsimp only [nativeShift, cochainComplexEquivalence]
  infer_instance

variable {C}

/-- The literal native term, before simplifying the two negative indices. -/
@[simp]
lemma nativeShift_obj_X (K : ChainComplex C ℤ) (a i : ℤ) :
    ((nativeShift C a).obj K).X i = K.X (-(-i + a)) := rfl

/-- The native differential has the actual `a.negOnePow` sign. -/
@[simp]
lemma nativeShift_obj_d (K : ChainComplex C ℤ) (a i j : ℤ) :
    ((nativeShift C a).obj K).d i j =
      a.negOnePow • K.d (-(-i + a)) (-(-j + a)) := rfl

/-- Morphism transport keeps the native negative-index components, without an extra sign. -/
@[simp]
lemma nativeShift_map_f {K L : ChainComplex C ℤ} (f : K ⟶ L) (a i : ℤ) :
    ((nativeShift C a).map f).f i = f.f (-(-i + a)) := rfl

/-- The native term identifies with the source term in degree `i - a`. -/
noncomputable def nativeShiftObjXIso (K : ChainComplex C ℤ) (a i : ℤ) :
    ((nativeShift C a).obj K).X i ≅ K.X (i - a) :=
  K.XIsoOfEq (show -(-i + a) = i - a by omega)

/-- The native term in any specified source degree equal to `i - a`. -/
noncomputable def nativeShiftObjXIso' (K : ChainComplex C ℤ) (a i j : ℤ)
    (h : i - a = j) : ((nativeShift C a).obj K).X i ≅ K.X j :=
  nativeShiftObjXIso K a i ≪≫ K.XIsoOfEq h

/-- The canonical term isomorphism intertwines the actual signed differentials. -/
lemma nativeShiftObjXIso_d (K : ChainComplex C ℤ) (a i j : ℤ) :
    ((nativeShift C a).obj K).d i j =
      (nativeShiftObjXIso K a i).hom ≫
        (a.negOnePow • K.d (i - a) (j - a)) ≫
          (nativeShiftObjXIso K a j).inv := by
  have hi : -(-i + a) = i - a := by omega
  have hj : -(-j + a) = j - a := by omega
  change a.negOnePow • K.d (-(-i + a)) (-(-j + a)) =
    (K.XIsoOfEq hi).hom ≫ (a.negOnePow • K.d (i - a) (j - a)) ≫ (K.XIsoOfEq hj).inv
  have h := (K.XIsoOfEq_hom_comp_d_assoc hi (j - a) (K.XIsoOfEq hj).inv).trans
    (K.d_comp_XIsoOfEq_inv hj (-(-i + a)))
  simpa only [Linear.comp_units_smul, Linear.units_smul_comp] using
    congrArg (fun f : K.X (-(-i + a)) ⟶ K.X (-(-j + a)) => a.negOnePow • f) h.symm

/-- The native signed differential in any specified pair of source coordinates. -/
lemma nativeShiftObjXIso'_d (K : ChainComplex C ℤ) (a i j i' j' : ℤ)
    (hi : i - a = i') (hj : j - a = j') :
    ((nativeShift C a).obj K).d i j =
      (nativeShiftObjXIso' K a i i' hi).hom ≫
        (a.negOnePow • K.d i' j') ≫ (nativeShiftObjXIso' K a j j' hj).inv := by
  subst i'
  subst j'
  simpa only [nativeShiftObjXIso', XIsoOfEq_rfl, Iso.trans_refl] using
    nativeShiftObjXIso_d K a i j

/-- Conjugation by the actual native term coordinates recovers the signed differential. -/
lemma nativeShiftObjXIso'_inv_d_hom (K : ChainComplex C ℤ) (a i j i' j' : ℤ)
    (hi : i - a = i') (hj : j - a = j') :
    (nativeShiftObjXIso' K a i i' hi).inv ≫
        ((nativeShift C a).obj K).d i j ≫ (nativeShiftObjXIso' K a j j' hj).hom =
      a.negOnePow • K.d i' j' := by
  rw [nativeShiftObjXIso'_d K a i j i' j' hi hj]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

/-- The native term isomorphisms are natural in chain-complex morphisms. -/
@[reassoc]
lemma nativeShiftObjXIso_naturality {K L : ChainComplex C ℤ}
    (f : K ⟶ L) (a i : ℤ) :
    ((nativeShift C a).map f).f i ≫ (nativeShiftObjXIso L a i).hom =
      (nativeShiftObjXIso K a i).hom ≫ f.f (i - a) := by
  change f.f (-(-i + a)) ≫
      (L.XIsoOfEq (show -(-i + a) = i - a by omega)).hom =
    (K.XIsoOfEq (show -(-i + a) = i - a by omega)).hom ≫ f.f (i - a)
  exact XIsoOfEq_hom_naturality f (show -(-i + a) = i - a by omega)

/-- Specified native term coordinates are natural in the original complex morphism. -/
@[reassoc]
lemma nativeShiftObjXIso'_naturality {K L : ChainComplex C ℤ}
    (f : K ⟶ L) (a i j : ℤ) (h : i - a = j) :
    ((nativeShift C a).map f).f i ≫ (nativeShiftObjXIso' L a i j h).hom =
      (nativeShiftObjXIso' K a i j h).hom ≫ f.f j := by
  subst j
  simpa only [nativeShiftObjXIso', XIsoOfEq_rfl, Iso.trans_refl] using
    nativeShiftObjXIso_naturality f a i

/-- Coordinate conjugation of the native shifted map retains the unsigned source component. -/
lemma nativeShiftObjXIso'_inv_map_f_hom {K L : ChainComplex C ℤ}
    (f : K ⟶ L) (a i j : ℤ) (h : i - a = j) :
    (nativeShiftObjXIso' K a i j h).inv ≫
        ((nativeShift C a).map f).f i ≫ (nativeShiftObjXIso' L a i j h).hom = f.f j := by
  rw [nativeShiftObjXIso'_naturality]
  exact (nativeShiftObjXIso' K a i j h).inv_hom_id_assoc _

variable (C)

/-- The native cochain zero isomorphism, followed by the inverse of the native unit. -/
noncomputable def nativeShiftZero : nativeShift C 0 ≅ 𝟭 (ChainComplex C ℤ) :=
  let E := cochainComplexEquivalence C
  isoWhiskerRight
      (isoWhiskerLeft E.functor
        (CategoryTheory.shiftFunctorZero (CochainComplex C ℤ) ℤ)) E.inverse ≪≫
    isoWhiskerRight (Functor.rightUnitor E.functor) E.inverse ≪≫ E.unitIso.symm

/-- Transport native addition and insert the inverse native counit between the shifts. -/
noncomputable def nativeShiftAdd' (a b ab : ℤ) (h : a + b = ab) :
    nativeShift C ab ≅ nativeShift C a ⋙ nativeShift C b :=
  let E := cochainComplexEquivalence C
  let Sa := CategoryTheory.shiftFunctor (CochainComplex C ℤ) a
  let Sb := CategoryTheory.shiftFunctor (CochainComplex C ℤ) b
  isoWhiskerRight
      (isoWhiskerLeft E.functor
        (CategoryTheory.shiftFunctorAdd' (CochainComplex C ℤ) a b ab h)) E.inverse ≪≫
    isoWhiskerRight
      ((Functor.rightUnitor (E.functor ⋙ Sa)).symm ≪≫
        isoWhiskerLeft (E.functor ⋙ Sa) E.counitIso.symm) (Sb ⋙ E.inverse)

/-- The native addition isomorphism with its sum index written literally. -/
noncomputable def nativeShiftAdd (a b : ℤ) :
    nativeShift C (a + b) ≅ nativeShift C a ⋙ nativeShift C b :=
  nativeShiftAdd' C a b (a + b) rfl

variable {C}

/-- The zero isomorphism retains the native equality map in every degree. -/
lemma nativeShiftZero_hom_app_f (K : ChainComplex C ℤ) (i : ℤ) :
    ((nativeShiftZero C).hom.app K).f i =
      (K.XIsoOfEq (show -(-i + 0) = i by omega)).hom := by
  have h₁ : -(-i + 0) = -(-i) := by omega
  have h₂ : -(-i) = i := by omega
  change (K.XIsoOfEq h₁).hom ≫ 𝟙 (K.X (-(-i))) ≫ (K.XIsoOfEq h₂).hom = _
  simp only [Category.id_comp, XIsoOfEq, eqToIso, eqToHom_trans]

/-- The inverse zero isomorphism retains the reverse equality map. -/
lemma nativeShiftZero_inv_app_f (K : ChainComplex C ℤ) (i : ℤ) :
    ((nativeShiftZero C).inv.app K).f i =
      (K.XIsoOfEq (show i = -(-i + 0) by omega)).hom := by
  have h₁ : i = -(-i) := by omega
  have h₂ : -(-i) = -(-i + 0) := by omega
  change ((K.XIsoOfEq h₁).hom ≫ 𝟙 (K.X (-(-i)))) ≫ (K.XIsoOfEq h₂).hom = _
  simp only [Category.comp_id, XIsoOfEq, eqToIso, eqToHom_trans]

/-- The transported addition component is the native reindexing equality map. -/
lemma nativeShiftAdd'_hom_app_f (K : ChainComplex C ℤ)
    (a b ab : ℤ) (h : a + b = ab) (i : ℤ) :
    ((nativeShiftAdd' C a b ab h).hom.app K).f i =
      (K.XIsoOfEq (show -(-i + ab) = -(-(-(-i + b)) + a) by omega)).hom := by
  unfold nativeShiftAdd'
  rw [CochainComplex.shiftFunctorAdd'_eq]
  have h₁ : -(-i + ab) = -((-i + b) + a) := by omega
  have h₂ : -((-i + b) + a) = -(-(-(-i + b)) + a) := by omega
  change (K.XIsoOfEq h₁).hom ≫ 𝟙 (K.X (-((-i + b) + a))) ≫ (K.XIsoOfEq h₂).hom = _
  simp only [Category.id_comp, XIsoOfEq, eqToIso, eqToHom_trans]

/-- The inverse transported addition component has the reverse equality map. -/
lemma nativeShiftAdd'_inv_app_f (K : ChainComplex C ℤ)
    (a b ab : ℤ) (h : a + b = ab) (i : ℤ) :
    ((nativeShiftAdd' C a b ab h).inv.app K).f i =
      (K.XIsoOfEq (show -(-(-(-i + b)) + a) = -(-i + ab) by omega)).hom := by
  unfold nativeShiftAdd'
  rw [CochainComplex.shiftFunctorAdd'_eq]
  have h₁ : -(-(-(-i + b)) + a) = -((-i + b) + a) := by omega
  have h₂ : -((-i + b) + a) = -(-i + ab) := by omega
  change ((K.XIsoOfEq h₁).hom ≫ 𝟙 (K.X (-((-i + b) + a)))) ≫ (K.XIsoOfEq h₂).hom = _
  simp only [Category.comp_id, XIsoOfEq, eqToIso, eqToHom_trans]

/-- The literal-sum addition isomorphism has the same native component equality map. -/
lemma nativeShiftAdd_hom_app_f (K : ChainComplex C ℤ) (a b i : ℤ) :
    ((nativeShiftAdd C a b).hom.app K).f i =
      (K.XIsoOfEq (show -(-i + (a + b)) = -(-(-(-i + b)) + a) by omega)).hom :=
  nativeShiftAdd'_hom_app_f K a b (a + b) rfl i

/-- Its inverse has the reverse native component equality map. -/
lemma nativeShiftAdd_inv_app_f (K : ChainComplex C ℤ) (a b i : ℤ) :
    ((nativeShiftAdd C a b).inv.app K).f i =
      (K.XIsoOfEq (show -(-(-(-i + b)) + a) = -(-i + (a + b)) by omega)).hom :=
  nativeShiftAdd'_inv_app_f K a b (a + b) rfl i

variable (C)

/-- Native addition coheres with the transported zero isomorphism on the left. -/
lemma nativeShiftAdd'_zero_add (a : ℤ) :
    nativeShiftAdd' C 0 a a (zero_add a) =
      (Functor.leftUnitor (nativeShift C a)).symm ≪≫
        isoWhiskerRight (nativeShiftZero C).symm (nativeShift C a) := by
  ext K i
  change ((nativeShiftAdd' C 0 a a (zero_add a)).hom.app K).f i =
    (HomologicalComplex.id ((nativeShift C a).obj K)).f i ≫
      ((nativeShift C a).map ((nativeShiftZero C).inv.app K)).f i
  dsimp only [HomologicalComplex.id]
  rw [Category.id_comp, nativeShiftAdd'_hom_app_f,
    nativeShift_map_f, nativeShiftZero_inv_app_f]

/-- Native addition coheres with the transported zero isomorphism on the right. -/
lemma nativeShiftAdd'_add_zero (a : ℤ) :
    nativeShiftAdd' C a 0 a (add_zero a) =
      (Functor.rightUnitor (nativeShift C a)).symm ≪≫
        isoWhiskerLeft (nativeShift C a) (nativeShiftZero C).symm := by
  ext K i
  change ((nativeShiftAdd' C a 0 a (add_zero a)).hom.app K).f i =
    (HomologicalComplex.id ((nativeShift C a).obj K)).f i ≫ ((nativeShiftZero C).inv.app ((nativeShift C a).obj K)).f i
  dsimp only [HomologicalComplex.id]
  rw [Category.id_comp, nativeShiftAdd'_hom_app_f,
    nativeShiftZero_inv_app_f]
  rfl

/-- The two ways of transporting native addition to three chain shifts agree. -/
lemma nativeShiftAdd_assoc (a b c : ℤ) :
    nativeShiftAdd C (a + b) c ≪≫
        isoWhiskerRight (nativeShiftAdd C a b) (nativeShift C c) ≪≫
          Functor.associator (nativeShift C a) (nativeShift C b) (nativeShift C c) =
      nativeShiftAdd' C a (b + c) ((a + b) + c) (add_assoc a b c).symm ≪≫
        isoWhiskerLeft (nativeShift C a) (nativeShiftAdd C b c) := by
  ext K i
  change ((nativeShiftAdd C (a + b) c).hom.app K).f i ≫
      ((nativeShift C c).map ((nativeShiftAdd C a b).hom.app K)).f i ≫
        (HomologicalComplex.id (((nativeShift C a ⋙ nativeShift C b) ⋙ nativeShift C c).obj K)).f i =
    ((nativeShiftAdd' C a (b + c) ((a + b) + c) (add_assoc a b c).symm).hom.app K).f i ≫
      ((nativeShiftAdd C b c).hom.app ((nativeShift C a).obj K)).f i
  dsimp only [HomologicalComplex.id]
  have hid := congrArg
    (fun f => ((nativeShiftAdd C (a + b) c).hom.app K).f i ≫ f)
    (Category.comp_id (((nativeShift C c).map ((nativeShiftAdd C a b).hom.app K)).f i))
  refine hid.trans ?_
  rw [nativeShiftAdd_hom_app_f,
    nativeShift_map_f, nativeShiftAdd_hom_app_f, nativeShiftAdd'_hom_app_f,
    nativeShiftAdd_hom_app_f]
  simp only [XIsoOfEq, eqToIso]
  exact (eqToHom_trans _ _).trans (eqToHom_trans _ _).symm

end ChainComplex
