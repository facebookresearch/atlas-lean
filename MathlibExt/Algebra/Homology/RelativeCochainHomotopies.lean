/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.LiftingProperties.Basic

/-!
# Native relative cochain-cylinder lifts

The cylinder is the actual cone of (id,-id):K→K⊕K.
Its endpoints, collapse and degree-minus-one homotopy are native cone
maps. A relative homotopy is constructed from the actual lifting square
over a fixed coefficient projection, rather than supplied freely.

Reference: standard cochain homotopies; PTVV1111.3209v4 §2.2.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.Algebra.Homology.RelativeCochainHomotopies

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The actual signed diagonal defining the cochain cylinder. -/
def signedDiagonal (K : CochainComplex C ℤ) : K ⟶ K ⊞ K :=
  biprod.lift (𝟙 K) (-𝟙 K)

/-- The actual native cochain cylinder. -/
def cylinder (K : CochainComplex C ℤ) : CochainComplex C ℤ :=
  CochainComplex.mappingCone (signedDiagonal K)

/-- The actual endpoint-boundary inclusion. -/
def boundary (K : CochainComplex C ℤ) : K ⊞ K ⟶ cylinder K :=
  CochainComplex.mappingCone.inr (signedDiagonal K)

/-- The actual first cylinder endpoint. -/
def first (K : CochainComplex C ℤ) : K ⟶ cylinder K := biprod.inl ≫ boundary K

/-- The actual second cylinder endpoint. -/
def second (K : CochainComplex C ℤ) : K ⟶ cylinder K := biprod.inr ≫ boundary K

/-- The literal native cone collapse. -/
def collapse (K : CochainComplex C ℤ) : cylinder K ⟶ K :=
  CochainComplex.mappingCone.desc (signedDiagonal K) 0 (biprod.desc (𝟙 K) (𝟙 K)) (by
    simp [signedDiagonal])

/-- The actual collapse fixes the boundary sum. -/
theorem boundary_collapse (K : CochainComplex C ℤ) :
    boundary K ≫ collapse K = biprod.desc (𝟙 K) (𝟙 K) :=
  CochainComplex.mappingCone.inr_desc _ _ _ _

/-- A genuine relative projection with lifting against all cochain monomorphisms. -/
def IsTrivialMonoFibration {P K : CochainComplex C ℤ} (r : P ⟶ K) : Prop :=
  ∀ (A B : CochainComplex C ℤ) (i : A ⟶ B), Mono i → HasLiftingProperty i r

/-- The native endpoint inclusion is a monomorphism of cochain complexes. -/
instance boundary_mono (K : CochainComplex C ℤ) : Mono (boundary K) := by
  apply HomologicalComplex.mono_of_mono_f
  intro i
  change Mono (HomologicalComplex.homotopyCofiber.inrX (signedDiagonal K) i)
  constructor
  intro A f g h
  have hh := congrArg (fun t => t ≫ HomologicalComplex.homotopyCofiber.sndX (signedDiagonal K) i) h
  simpa only [Category.assoc, HomologicalComplex.homotopyCofiber.inrX_sndX,
    Category.comp_id] using hh

/-- The whole relative lifting square has the actual endpoint and collapse maps. -/
theorem liftingSquare {K P : CochainComplex C ℤ} (r : P ⟶ K) (a b : K ⟶ P)
    (ha : a ≫ r = 𝟙 K) (hb : b ≫ r = 𝟙 K) :
    CommSq (biprod.desc a b) (boundary K) r (collapse K) :=
  ⟨by
    rw [boundary_collapse]
    apply biprod.hom_ext'
    · simpa only [biprod.inl_desc_assoc, biprod.inl_desc] using ha
    · simpa only [biprod.inr_desc_assoc, biprod.inr_desc] using hb⟩

/-- The relative cylinder map is the actual lift of this fixed square. -/
def relativeLift {K P : CochainComplex C ℤ} (r : P ⟶ K)
    (hr : IsTrivialMonoFibration r) (a b : K ⟶ P)
    (ha : a ≫ r = 𝟙 K) (hb : b ≫ r = 𝟙 K) : cylinder K ⟶ P := by
  have := hr _ _ (boundary K) inferInstance
  exact (liftingSquare r a b ha hb).lift

/-- Its boundary is exactly the pair of source maps. -/
theorem relativeLift_boundary {K P : CochainComplex C ℤ} (r : P ⟶ K)
    (hr : IsTrivialMonoFibration r) (a b : K ⟶ P)
    (ha : a ≫ r = 𝟙 K) (hb : b ≫ r = 𝟙 K) :
    boundary K ≫ relativeLift r hr a b ha hb = biprod.desc a b := by
  have := hr _ _ (boundary K) inferInstance
  exact (liftingSquare r a b ha hb).fac_left

/-- Its entire projection is the native cylinder collapse. -/
theorem relativeLift_projection {K P : CochainComplex C ℤ} (r : P ⟶ K)
    (hr : IsTrivialMonoFibration r) (a b : K ⟶ P)
    (ha : a ≫ r = 𝟙 K) (hb : b ≫ r = 𝟙 K) :
    relativeLift r hr a b ha hb ≫ r = collapse K := by
  let := hr _ _ (boundary K) inferInstance
  exact (liftingSquare r a b ha hb).fac_right

/-- The actual relative homotopy, with differential b-a. -/
def relativeHomotopy {K P : CochainComplex C ℤ} (r : P ⟶ K)
    (hr : IsTrivialMonoFibration r) (a b : K ⟶ P)
    (ha : a ≫ r = 𝟙 K) (hb : b ≫ r = 𝟙 K) : Cochain K P (-1) :=
  -((CochainComplex.mappingCone.inl (signedDiagonal K)).comp
    (Cochain.ofHom (relativeLift r hr a b ha hb)) (add_zero (-1)))

/-- Its differential is precisely the source endpoint difference b-a. -/
theorem relativeHomotopy_d {K P : CochainComplex C ℤ} (r : P ⟶ K)
    (hr : IsTrivialMonoFibration r) (a b : K ⟶ P)
    (ha : a ≫ r = 𝟙 K) (hb : b ≫ r = 𝟙 K) :
    δ (-1) 0 (relativeHomotopy r hr a b ha hb) = Cochain.ofHom b - Cochain.ofHom a := by
  let l : CochainComplex.mappingCone (signedDiagonal K) ⟶ P := relativeLift r hr a b ha hb
  have hl : CochainComplex.mappingCone.inr (signedDiagonal K) ≫ l = biprod.desc a b :=
    relativeLift_boundary r hr a b ha hb
  change δ (-1) 0 (-((CochainComplex.mappingCone.inl (signedDiagonal K)).comp
    (Cochain.ofHom l) (add_zero (-1)))) = _
  rw [δ_neg, δ_comp_zero_cochain, CochainComplex.mappingCone.δ_inl]
  simp only [δ_ofHom, ← Cochain.ofHom_comp]
  rw [Category.assoc, hl]
  simp [signedDiagonal, sub_eq_add_neg]
  all_goals omega

/-- The relative homotopy becomes exactly constant after the prescribed projection. -/
theorem relativeHomotopy_projection {K P : CochainComplex C ℤ} (r : P ⟶ K)
    (hr : IsTrivialMonoFibration r) (a b : K ⟶ P)
    (ha : a ≫ r = 𝟙 K) (hb : b ≫ r = 𝟙 K) :
    (relativeHomotopy r hr a b ha hb).comp (Cochain.ofHom r) (add_zero (-1)) = 0 := by
  let l : CochainComplex.mappingCone (signedDiagonal K) ⟶ P := relativeLift r hr a b ha hb
  have hl : l ≫ r = collapse K := relativeLift_projection r hr a b ha hb
  change (-((CochainComplex.mappingCone.inl (signedDiagonal K)).comp
    (Cochain.ofHom l) (add_zero (-1)))).comp (Cochain.ofHom r) (add_zero (-1)) = _
  rw [Cochain.neg_comp, Cochain.comp_assoc_of_second_is_zero_cochain, ← Cochain.ofHom_comp, hl]
  simp [collapse]

end MathlibExt.Algebra.Homology.RelativeCochainHomotopies
