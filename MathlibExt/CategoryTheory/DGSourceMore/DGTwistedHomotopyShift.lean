/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
This completed proof port retains the original Apache 2.0 license and author credit.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/CategoryTheory/DG/Twisted/HomotopyShift.lean
Original license: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
Modifications: only module/namespace paths are adapted for Atlas.
Mathematical operations, hypotheses and proof bodies are retained.
-/

public import MathlibExt.CategoryTheory.DGSourceMore.DGTwistedShift
public import Mathlib.CategoryTheory.Shift.Basic

/-!
# The shift on the homotopy category of twisted objects

Let `C` be a differential graded category and let `H⁰` be the homotopy category of the twisted
objects `(⊕ᵢ Xᵢ[rᵢ], δ)` of the additive closure of the shift closure of `C`.  The DG shift
functors `MathlibExt.DGSource.DGTwistedObject.shiftFunctor n`, which send `(⊕ᵢ Xᵢ[rᵢ], δ)` to
`(⊕ᵢ Xᵢ[rᵢ + n], δ)`, induce functors on `H⁰`.  This file makes them a shift `HasShift H⁰ ℤ` in
the sense of Mathlib, the structure that Mathlib's triangles `X ⟶ Y ⟶ Z ⟶ X⟦1⟧` and
pretriangulated categories are formulated with.

The shifts do not compose strictly: `P⟦a⟧⟦b⟧` has summands `Xᵢ[rᵢ + a + b]` and `P⟦a + b⟧` has
summands `Xᵢ[rᵢ + (a + b)]`.  The isomorphisms `P⟦0⟧ ≅ P` and `P⟦a + b⟧ ≅ P⟦a⟧⟦b⟧` of the shift are
the classes of the comparison morphism `MathlibExt.DGSource.DGTwistedObject.fromShift P 0` and of the closed
degree-zero isomorphism `MathlibExt.DGSource.DGTwistedObject.shiftAddHom P a b` of
`MathlibExt/CategoryTheory/DGSourceMore/DGTwistedShift.lean`, whose associativity and unit coherences hold already
at the level of DG morphisms.

## Main definitions

* `MathlibExt.DGSource.DGTwistedObject.homotopyCategoryShiftMkCore`: the shift functors on `H⁰` and their
  compatibility isomorphisms.
* `MathlibExt.DGSource.DGTwistedObject.hasShiftHomotopyCategory`: the shift `HasShift H⁰ ℤ`.

## Main results

* `MathlibExt.DGSource.DGTwistedObject.shiftFunctor_map_homOf`,
  `MathlibExt.DGSource.DGTwistedObject.shiftFunctorZero_hom_app_of` and
  `MathlibExt.DGSource.DGTwistedObject.shiftFunctorAdd_hom_app_of`: the shift of `H⁰` and its isomorphisms
  are induced by the DG shift and the comparison morphisms.
* `MathlibExt.DGSource.DGTwistedObject.shiftFunctorComm_hom_app_of`: the isomorphism `P⟦a⟧⟦b⟧ ≅ P⟦b⟧⟦a⟧`
  commuting the shifts is the class of `MathlibExt.DGSource.DGTwistedObject.shiftCommHom`.

## References

* A. I. Bondal and M. M. Kapranov, *Enhanced triangulated categories*, Section 1.
* V. Drinfeld, *DG quotients of DG categories*, Section 2.4.
-/

public section

open CategoryTheory

namespace MathlibExt.DGSource

universe v u

namespace DGTwistedObject

variable {R : Type v} [CommRing R] {C : Type u} [DGCategory R C]

/-! ### The shift on the homotopy category -/

section homotopy

open DGHomotopyCategory

variable (P : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))

private theorem dgDifferential_dgComp_fromShift_toShift (a b : ℤ) (h : a + -b = 0) :
    dgDifferential R 0 (dgComp R (fromShift P a) (toShift P b) h) = 0 := by
  simp -proj only [dgDifferential_dgComp, dgDifferential_fromShift, dgDifferential_toShift,
    zero_dgComp, dgComp_zero, smul_zero, add_zero]

variable {P} in
/-- An identity `P⟦a⟧ = P⟦b⟧` in the homotopy category, for `a = b`, is represented by the
comparison morphisms `P⟦a⟧ ⟶ P ⟶ P⟦b⟧`. -/
private theorem eqToHom_mapDGHomotopyCategory_shiftFunctor {a b : ℤ} (h : a = b)
    (h' : (shiftFunctor R a).mapDGHomotopyCategory.obj (DGHomotopyCategory.of R P) =
      (shiftFunctor R b).mapDGHomotopyCategory.obj (DGHomotopyCategory.of R P)) :
    eqToHom h' = homOf R (dgComp R (fromShift P a) (toShift P b) (by omega))
      ((mem_dgCycles R).mpr (dgDifferential_dgComp_fromShift_toShift P a b _)) := by
  subst h
  rw [eqToHom_refl]
  refine (homOf_dgId R _).symm.trans ?_
  congr 1
  exact (dgComp_fromShift_toShift P a).symm

variable {P} in
private theorem homOf_fromShift_zero_naturality
    {Q : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))}
    (f : DGHom R 0 P Q) (hf : f ∈ dgCycles R P Q) :
    homOf R ((shiftFunctor R 0).dgMap 0 f) ((shiftFunctor R 0).dgMap_mem_dgCycles hf) ≫
        homOf R (fromShift Q 0) ((mem_dgCycles R).mpr (dgDifferential_fromShift Q 0)) =
      homOf R (fromShift P 0) ((mem_dgCycles R).mpr (dgDifferential_fromShift P 0)) ≫
        homOf R f hf := by
  conv_rhs => simp only [homOf_comp, dgCompZero_def]
  exact homOf_comp_eq_homOf_of_dgComp_eq R _ _ _ (by
    rw [dgComp_fromShift 0 f, mul_zero, Int.negOnePow_zero, one_smul])

variable {P} in
private theorem homOf_shiftAddHom_naturality
    {Q : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))}
    (a b : ℤ) (f : DGHom R 0 P Q) (hf : f ∈ dgCycles R P Q) :
    homOf R ((shiftFunctor R (a + b)).dgMap 0 f)
          ((shiftFunctor R (a + b)).dgMap_mem_dgCycles hf) ≫
        homOf R (shiftAddHom Q a b) ((mem_dgCycles R).mpr (dgDifferential_shiftAddHom Q a b)) =
      homOf R (shiftAddHom P a b) ((mem_dgCycles R).mpr (dgDifferential_shiftAddHom P a b)) ≫
        homOf R ((shiftFunctor R b).dgMap 0 ((shiftFunctor R a).dgMap 0 f))
          ((shiftFunctor R b).dgMap_mem_dgCycles ((shiftFunctor R a).dgMap_mem_dgCycles hf)) := by
  conv_rhs => simp only [homOf_comp, dgCompZero_def]
  exact homOf_comp_eq_homOf_of_dgComp_eq R _ _ _ (dgMap_dgComp_shiftAddHom a b f)

private theorem homOf_shiftAddHom_assoc (a b c : ℤ) :
    homOf R (shiftAddHom P (a + b) c)
          ((mem_dgCycles R).mpr (dgDifferential_shiftAddHom P (a + b) c)) ≫
        homOf R ((shiftFunctor R c).dgMap 0 (shiftAddHom P a b))
          ((shiftFunctor R c).dgMap_mem_dgCycles
            ((mem_dgCycles R).mpr (dgDifferential_shiftAddHom P a b))) =
      homOf R (dgComp R (fromShift P (a + b + c)) (toShift P (a + (b + c))) (by omega))
          ((mem_dgCycles R).mpr (dgDifferential_dgComp_fromShift_toShift P _ _ _)) ≫
        homOf R (shiftAddHom P a (b + c))
            ((mem_dgCycles R).mpr (dgDifferential_shiftAddHom P a (b + c))) ≫
          homOf R (shiftAddHom ((shiftFunctor R a).obj P) b c)
            ((mem_dgCycles R).mpr (dgDifferential_shiftAddHom _ b c)) := by
  conv_rhs => simp only [homOf_comp, dgCompZero_def]
  exact homOf_comp_eq_homOf_of_dgComp_eq R _ _ _ (shiftAddHom_assoc P a b c)

private theorem homOf_shiftAddHom_zero_add (n : ℤ) :
    homOf R (shiftAddHom P 0 n) ((mem_dgCycles R).mpr (dgDifferential_shiftAddHom P 0 n)) =
      homOf R (dgComp R (fromShift P (0 + n)) (toShift P n) (by omega))
          ((mem_dgCycles R).mpr (dgDifferential_dgComp_fromShift_toShift P _ _ _)) ≫
        homOf R ((shiftFunctor R n).dgMap 0 (toShift P 0))
          ((shiftFunctor R n).dgMap_mem_dgCycles
            ((mem_dgCycles R).mpr (dgDifferential_toShift P 0))) :=
  (homOf_comp_eq_homOf_of_dgComp_eq R _ _ _ (shiftAddHom_zero_add P n).symm).symm

private theorem homOf_shiftAddHom_add_zero (n : ℤ) :
    homOf R (shiftAddHom P n 0) ((mem_dgCycles R).mpr (dgDifferential_shiftAddHom P n 0)) =
      homOf R (dgComp R (fromShift P (n + 0)) (toShift P n) (by omega))
          ((mem_dgCycles R).mpr (dgDifferential_dgComp_fromShift_toShift P _ _ _)) ≫
        homOf R (toShift ((shiftFunctor R n).obj P) 0)
          ((mem_dgCycles R).mpr (dgDifferential_toShift _ 0)) :=
  (homOf_comp_eq_homOf_of_dgComp_eq R _ _ _ (shiftAddHom_add_zero P n).symm).symm

variable (R C) in
/-- The shift of the homotopy category of twisted objects: the shift by `n` is induced by the DG
shift functor `MathlibExt.DGSource.DGTwistedObject.shiftFunctor n`, and the isomorphisms `P⟦0⟧ ≅ P` and
`P⟦a + b⟧ ≅ P⟦a⟧⟦b⟧` are the classes of the comparison morphism `P⟦0⟧ ⟶ P` and of
`MathlibExt.DGSource.DGTwistedObject.shiftAddHom`. -/
@[expose]
noncomputable def homotopyCategoryShiftMkCore :
    ShiftMkCore
      (DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))) ℤ where
  F n := (shiftFunctor R n).mapDGHomotopyCategory
  -- The private naturality and coherence lemmas are only accessible from tactic blocks in this
  -- exposed definition.
  zero := NatIso.ofComponents (fun X ↦
      { hom := homOf R (fromShift (underlying R X) 0)
          ((mem_dgCycles R).mpr (dgDifferential_fromShift _ 0))
        inv := homOf R (toShift (underlying R X) 0)
          ((mem_dgCycles R).mpr (dgDifferential_toShift _ 0))
        hom_inv_id := homOf_comp_eq_id_of_dgComp_eq_dgId R _ _ (dgComp_fromShift_toShift _ 0)
        inv_hom_id := homOf_comp_eq_id_of_dgComp_eq_dgId R _ _ (dgComp_toShift_fromShift _ 0) })
      fun {X Y} f ↦ by
    obtain ⟨P, rfl⟩ := of_surjective R X
    obtain ⟨Q, rfl⟩ := of_surjective R Y
    obtain ⟨f, hf, rfl⟩ := exists_dgHomotopyClass_eq R (X := P) (Y := Q) f
    rw [← homOf_def]
    exact (congrArg (· ≫ _) (EnrichedFunctor.mapDGHomotopyCategory_map_homOf _ f hf)).trans
      (homOf_fromShift_zero_naturality f hf)
  add a b := NatIso.ofComponents (fun X ↦
      { hom := homOf R (shiftAddHom (underlying R X) a b)
          ((mem_dgCycles R).mpr (dgDifferential_shiftAddHom _ a b))
        inv := homOf R (shiftAddInv (underlying R X) a b)
          ((mem_dgCycles R).mpr (dgDifferential_shiftAddInv _ a b))
        hom_inv_id :=
          homOf_comp_eq_id_of_dgComp_eq_dgId R _ _ (dgComp_shiftAddHom_shiftAddInv _ a b)
        inv_hom_id :=
          homOf_comp_eq_id_of_dgComp_eq_dgId R _ _ (dgComp_shiftAddInv_shiftAddHom _ a b) })
      fun {X Y} f ↦ by
    obtain ⟨P, rfl⟩ := of_surjective R X
    obtain ⟨Q, rfl⟩ := of_surjective R Y
    obtain ⟨f, hf, rfl⟩ := exists_dgHomotopyClass_eq R (X := P) (Y := Q) f
    rw [← homOf_def]
    refine (congrArg (· ≫ _) (EnrichedFunctor.mapDGHomotopyCategory_map_homOf _ f hf)).trans
      ((homOf_shiftAddHom_naturality a b f hf).trans ?_)
    exact congrArg (_ ≫ ·) ((EnrichedFunctor.mapDGHomotopyCategory_map_homOf _ _ _).symm.trans
      (congrArg _ (EnrichedFunctor.mapDGHomotopyCategory_map_homOf _ f hf).symm))
  assoc_hom_app m₁ m₂ m₃ X := by
    obtain ⟨P, rfl⟩ := of_surjective R X
    refine (congrArg (_ ≫ ·) (EnrichedFunctor.mapDGHomotopyCategory_map_homOf _ _ _)).trans
      ((homOf_shiftAddHom_assoc P m₁ m₂ m₃).trans ?_)
    exact congrArg (· ≫ _)
      (eqToHom_mapDGHomotopyCategory_shiftFunctor (add_assoc m₁ m₂ m₃) _).symm
  zero_add_hom_app n X := by
    obtain ⟨P, rfl⟩ := of_surjective R X
    refine (homOf_shiftAddHom_zero_add P n).trans ?_
    exact congrArg₂ (· ≫ ·)
      (eqToHom_mapDGHomotopyCategory_shiftFunctor (zero_add n) _).symm
      (EnrichedFunctor.mapDGHomotopyCategory_map_homOf _ _ _).symm
  add_zero_hom_app n X := by
    obtain ⟨P, rfl⟩ := of_surjective R X
    exact (homOf_shiftAddHom_add_zero P n).trans (congrArg (· ≫ _)
      (eqToHom_mapDGHomotopyCategory_shiftFunctor (add_zero n) _).symm)

/-- **The homotopy category of twisted objects has a shift by `ℤ`**, induced by the DG shift
functors `MathlibExt.DGSource.DGTwistedObject.shiftFunctor`. -/
noncomputable instance hasShiftHomotopyCategory :
    HasShift (DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))) ℤ :=
  hasShiftMk _ _ (homotopyCategoryShiftMkCore R C)

variable (R C) in
/-- The shift by `n` of the homotopy category of twisted objects is the functor induced by the DG
shift functor `MathlibExt.DGSource.DGTwistedObject.shiftFunctor n`. -/
theorem shiftFunctor_eq_mapDGHomotopyCategory (n : ℤ) :
    CategoryTheory.shiftFunctor
        (DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))) n =
      (shiftFunctor R n).mapDGHomotopyCategory :=
  (rfl)

instance (n : ℤ) :
    (CategoryTheory.shiftFunctor
      (DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))))
        n).Additive :=
  inferInstanceAs (shiftFunctor R n).mapDGHomotopyCategory.Additive

instance (n : ℤ) :
    (CategoryTheory.shiftFunctor
      (DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))) n).Linear
        R :=
  inferInstanceAs ((shiftFunctor R n).mapDGHomotopyCategory.Linear R)

/-- The shift of a twisted object in the homotopy category is its DG shift. -/
@[simp]
theorem shiftFunctor_obj_of (n : ℤ) :
    (CategoryTheory.shiftFunctor
        (DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))) n).obj
        (DGHomotopyCategory.of R P) =
      DGHomotopyCategory.of R ((shiftFunctor R n).obj P) :=
  (rfl)

variable {P} in
/-- The shift of the class of a closed degree-zero morphism is the class of its DG shift. -/
@[simp]
theorem shiftFunctor_map_homOf {Q : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))}
    (n : ℤ) (f : DGHom R 0 P Q) (hf : f ∈ dgCycles R P Q) :
    (CategoryTheory.shiftFunctor
        (DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))) n).map
        (homOf R f hf) =
      homOf R ((shiftFunctor R n).dgMap 0 f) ((shiftFunctor R n).dgMap_mem_dgCycles hf) :=
  EnrichedFunctor.mapDGHomotopyCategory_map_homOf _ f hf

/-- The isomorphism `P⟦0⟧ ≅ P` of the shift is the class of the comparison morphism. -/
@[simp]
theorem shiftFunctorZero_hom_app_of :
    (shiftFunctorZero
        (DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))) ℤ).hom.app
        (DGHomotopyCategory.of R P) =
      homOf R (fromShift P 0) ((mem_dgCycles R).mpr (dgDifferential_fromShift P 0)) := by
  rw [ShiftMkCore.shiftFunctorZero_eq]
  rfl

/-- The inverse isomorphism `P ≅ P⟦0⟧` of the shift is the class of the comparison morphism. -/
@[simp]
theorem shiftFunctorZero_inv_app_of :
    (shiftFunctorZero
        (DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))) ℤ).inv.app
        (DGHomotopyCategory.of R P) =
      homOf R (toShift P 0) ((mem_dgCycles R).mpr (dgDifferential_toShift P 0)) := by
  rw [ShiftMkCore.shiftFunctorZero_eq]
  rfl

/-- The isomorphism `P⟦a + b⟧ ≅ P⟦a⟧⟦b⟧` of the shift is the class of
`MathlibExt.DGSource.DGTwistedObject.shiftAddHom`. -/
@[simp]
theorem shiftFunctorAdd_hom_app_of (a b : ℤ) :
    (shiftFunctorAdd
        (DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))) a
          b).hom.app (DGHomotopyCategory.of R P) =
      homOf R (shiftAddHom P a b) ((mem_dgCycles R).mpr (dgDifferential_shiftAddHom P a b)) := by
  rw [ShiftMkCore.shiftFunctorAdd_eq]
  rfl

/-- The isomorphism `P⟦a⟧⟦b⟧ ≅ P⟦a + b⟧` of the shift is the class of
`MathlibExt.DGSource.DGTwistedObject.shiftAddInv`. -/
@[simp]
theorem shiftFunctorAdd_inv_app_of (a b : ℤ) :
    (shiftFunctorAdd
        (DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))) a
          b).inv.app (DGHomotopyCategory.of R P) =
      homOf R (shiftAddInv P a b) ((mem_dgCycles R).mpr (dgDifferential_shiftAddInv P a b)) := by
  rw [ShiftMkCore.shiftFunctorAdd_eq]
  rfl

/-- The isomorphism `P⟦a⟧⟦b⟧ ≅ P⟦b⟧⟦a⟧` commuting the shifts is the class of
`MathlibExt.DGSource.DGTwistedObject.shiftCommHom`. -/
@[simp]
theorem shiftFunctorComm_hom_app_of (a b : ℤ) :
    (shiftFunctorComm
        (DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))) a
          b).hom.app (DGHomotopyCategory.of R P) =
      homOf R (shiftCommHom P a b) ((mem_dgCycles R).mpr (dgDifferential_shiftCommHom P a b)) := by
  rw [shiftFunctorComm, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, shiftFunctorAdd',
    Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app, shiftFunctorAdd_inv_app_of,
    shiftFunctorAdd_hom_app_of]
  have h : homOf R (shiftAddInv P a b) ((mem_dgCycles R).mpr (dgDifferential_shiftAddInv P a b)) ≫
      homOf R (dgComp R (fromShift P (a + b)) (toShift P (b + a)) (by omega))
        ((mem_dgCycles R).mpr (dgDifferential_dgComp_fromShift_toShift P _ _ _)) ≫
      homOf R (shiftAddHom P b a) ((mem_dgCycles R).mpr (dgDifferential_shiftAddHom P b a)) =
      homOf R (shiftCommHom P a b) ((mem_dgCycles R).mpr (dgDifferential_shiftCommHom P a b)) := by
    simp only [homOf_comp, dgCompZero_def]
    congr 1
    exact (shiftCommHom_eq_dgComp_shiftAddInv P a b).symm
  -- The identity `P⟦a + b⟧ = P⟦b + a⟧` is rewritten only up to the definitional unfolding of the
  -- shift of the homotopy category, so it is substituted by `exact`.
  exact (congrArg (fun t ↦ _ ≫ t ≫ _)
    (eqToHom_mapDGHomotopyCategory_shiftFunctor (add_comm a b) _)).trans h

/-- The inverse of the isomorphism `P⟦a⟧⟦b⟧ ≅ P⟦b⟧⟦a⟧` commuting the shifts is the class of
`MathlibExt.DGSource.DGTwistedObject.shiftCommHom P b a`. -/
@[simp]
theorem shiftFunctorComm_inv_app_of (a b : ℤ) :
    (shiftFunctorComm
        (DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))) a
          b).inv.app (DGHomotopyCategory.of R P) =
      homOf R (shiftCommHom P b a) ((mem_dgCycles R).mpr (dgDifferential_shiftCommHom P b a)) := by
  rw [← Iso.symm_hom, shiftFunctorComm_symm, shiftFunctorComm_hom_app_of]

end homotopy

end DGTwistedObject

end MathlibExt.DGSource
