/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
This completed source port retains the original Apache 2.0 license and author credit.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/CategoryTheory/DG/Functor/Basic.lean
Only module/namespace paths are adapted for Atlas; source operations and hypotheses are retained.
-/

public import MathlibExt.CategoryTheory.DGSource.DGClosedCategory

/-!
# Differential graded functors and their homotopy functors

A DG functor between differential graded categories is an enriched functor
`CategoryTheory.EnrichedFunctor (CochainComplex (ModuleCat R) ℤ) C D`: a chain map
`Hom(X, Y) ⟶ Hom(F X, F Y)` for every pair of objects, compatible with the enriched identities and
compositions.  This file unpacks that data into the calculus of homogeneous morphisms used
throughout `MathlibExt.CategoryTheory.DGSource.DGCategory`: a DG functor acts on morphisms of each degree, and
this action commutes with the differential and preserves identities and composition.  Conversely,
such an action on homogeneous morphisms determines a DG functor.

Consequently a DG functor sends closed degree-zero morphisms to closed ones and boundaries to
boundaries, and it induces a linear functor `H⁰(F) : H⁰(C) ⥤ H⁰(D)` between homotopy categories.
Its action on the morphisms `H⁰(Hom(X, Y))` is the map induced on degree-zero cohomology by the
chain map `F.map X Y`, so the quasi-isomorphism conditions on DG functors translate directly into
statements about `H⁰(F)`.

## Main definitions

* `CategoryTheory.EnrichedFunctor.dgMap`: the action of a DG functor on morphisms of degree `n`.
* `CategoryTheory.EnrichedFunctor.ofDGMap`: the DG functor with a prescribed action on homogeneous
  morphisms commuting with the differential, identities, and composition.
* `CategoryTheory.EnrichedFunctor.mapDGHomotopyCategory`: the functor `H⁰(F)` induced on homotopy
  categories.
* `CategoryTheory.EnrichedFunctor.mapDGHomotopyCategoryIdIso` and
  `CategoryTheory.EnrichedFunctor.mapDGHomotopyCategoryCompIso`: `H⁰` of the identity DG functor and
  of a composite.

## Main results

* `CategoryTheory.EnrichedFunctor.dgMap_dgDifferential` and
  `CategoryTheory.EnrichedFunctor.dgMap_d`: a DG functor commutes with the differential.
* `CategoryTheory.EnrichedFunctor.dgMap_castDeg`: a DG functor commutes with degree transport.
* `CategoryTheory.EnrichedFunctor.dgMap_dgId` and `CategoryTheory.EnrichedFunctor.dgMap_dgComp`:
  a DG functor preserves identities and composition of homogeneous morphisms.
* `CategoryTheory.EnrichedFunctor.mapDGHomotopyCategory_map_homOf`: `H⁰(F)` sends the class of a
  closed degree-zero morphism `f` to the class of `F f`.

## References

* B. Keller, *Deriving DG categories*, Sections 1 and 2.
* V. Drinfeld, *DG quotients of DG categories*, Section 2.
-/

public section

open CategoryTheory MonoidalCategory HomologicalComplex MathlibExt.DGSource

universe v u₁ u₂ u₃

namespace CategoryTheory.EnrichedFunctor

variable {R : Type v} [CommRing R] {C : Type u₁} {D : Type u₂} {E : Type u₃}
variable [DGCategory R C] [DGCategory R D] [DGCategory R E]
variable (F : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D)
  (G : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) D E)

noncomputable section

/-! ### The action on homogeneous morphisms -/

/-- The action of a DG functor on morphisms of degree `n`: the degree-`n` component of its chain
map on Hom complexes. -/
def dgMap {X Y : C} (n : ℤ) : DGHom R n X Y →ₗ[R] DGHom R n (F.obj X) (F.obj Y) :=
  ((F.map X Y).f n).hom

/-- The action of a DG functor on degree-`n` morphisms is the degree-`n` component of its map on
Hom complexes. -/
theorem dgMap_apply {X Y : C} {n : ℤ} (f : DGHom R n X Y) :
    F.dgMap n f = ((F.map X Y).f n).hom f :=
  (rfl)

/-- A DG functor commutes with the differential of the Hom complexes. -/
@[simp]
theorem dgMap_dgDifferential {X Y : C} {n : ℤ} (f : DGHom R n X Y) :
    F.dgMap (n + 1) (dgDifferential R n f) = dgDifferential R n (F.dgMap n f) := by
  simp only [dgMap_apply, ← ModuleCat.comp_apply, (F.map X Y).comm]

/-- A DG functor commutes with the differential of the Hom complexes between arbitrary indices. -/
theorem dgMap_d {X Y : C} (a b : ℤ) (f : DGHom R a X Y) :
    F.dgMap b (((dgHomComplex R X Y).d a b).hom f) =
      ((dgHomComplex R (F.obj X) (F.obj Y)).d a b).hom (F.dgMap a f) := by
  simp only [dgMap_apply, ← ModuleCat.comp_apply, (F.map X Y).comm]

/-- A DG functor commutes with degree transport. -/
@[simp]
theorem dgMap_castDeg {X Y : C} {p p' : ℤ} (hp : p = p') (f : DGHom R p X Y) :
    F.dgMap p' (castDeg R hp f) = castDeg R hp (F.dgMap p f) := by
  subst hp
  simp only [castDeg_self]

/-- A DG functor preserves identities. -/
@[simp]
theorem dgMap_dgId (X : C) : F.dgMap 0 (dgId R X) = dgId R (F.obj X) := by
  rw [dgMap_apply, dgId_def, dgId_def, ← ModuleCat.comp_apply, ← HomologicalComplex.comp_f,
    F.map_id]

/-- The bidegree component of enriched composition is natural under a DG functor. -/
theorem dgCompMap_naturality {X Y Z : C} (p q n : ℤ) (h : p + q = n) :
    dgCompMap R X Y Z p q n h ≫ (F.map X Z).f n =
      ((F.map X Y).f p ⊗ₘ (F.map Y Z).f q) ≫
        dgCompMap R (F.obj X) (F.obj Y) (F.obj Z) p q n h := by
  rw [dgCompMap_def, dgCompMap_def, Category.assoc, ← HomologicalComplex.comp_f, F.map_comp,
    tensorHom_def, HomologicalComplex.comp_f, HomologicalComplex.comp_f, Category.assoc,
    ι_whiskerRight_assoc, ι_whiskerLeft_assoc, tensorHom_def_assoc]

/-- A DG functor preserves the composition of homogeneous morphisms. -/
@[simp]
theorem dgMap_dgComp {X Y Z : C} {p q n : ℤ} (f : DGHom R p X Y) (g : DGHom R q Y Z)
    (h : p + q = n) :
    F.dgMap n (dgComp R f g h) = dgComp R (F.dgMap p f) (F.dgMap q g) h := by
  simpa only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply, dgCompMap_tmul,
    ModuleCat.MonoidalCategory.tensorHom_tmul, dgMap_apply] using
    LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (F.dgCompMap_naturality p q n h)) (f ⊗ₜ g)

/-- The images of degree-zero morphisms composing to the identity compose to the identity, in
front of any further morphism `x`. -/
theorem dgMap_dgComp_dgMap_assoc_of_eq_dgId {X Y : C} {Z : D} {f : DGHom R 0 X Y}
    {g : DGHom R 0 Y X} (hfg : dgComp R f g (add_zero 0) = dgId R X) {m : ℤ}
    (x : DGHom R m (F.obj X) Z) :
    dgComp R (F.dgMap 0 f) (dgComp R (F.dgMap 0 g) x (zero_add m)) (zero_add m) = x := by
  rw [← dgComp_assoc R _ _ x (add_zero 0) (zero_add m) (by omega), ← dgMap_dgComp, hfg, dgMap_dgId,
    dgId_dgComp]

/-- The images of degree-zero morphisms composing to zero compose to zero, in front of any
further morphism `x`. -/
theorem dgMap_dgComp_dgMap_assoc_of_eq_zero {X Y Y' : C} {Z : D} {f : DGHom R 0 X Y}
    {g : DGHom R 0 Y Y'} (hfg : dgComp R f g (add_zero 0) = 0) {m : ℤ}
    (x : DGHom R m (F.obj Y') Z) :
    dgComp R (F.dgMap 0 f) (dgComp R (F.dgMap 0 g) x (zero_add m)) (zero_add m) = 0 := by
  rw [← dgComp_assoc R _ _ x (add_zero 0) (zero_add m) (by omega), ← dgMap_dgComp, hfg, map_zero,
    zero_dgComp]

/-- The identity DG functor acts as the identity on homogeneous morphisms. -/
@[simp]
theorem id_dgMap {X Y : C} {n : ℤ} (f : DGHom R n X Y) :
    (EnrichedFunctor.id (CochainComplex (ModuleCat.{v} R) ℤ) C).dgMap n f = f :=
  (rfl)

/-- A composite of DG functors acts on homogeneous morphisms by composing the two actions. -/
@[simp]
theorem comp_dgMap {X Y : C} {n : ℤ} (f : DGHom R n X Y) :
    (F.comp (CochainComplex (ModuleCat.{v} R) ℤ) G).dgMap n f = G.dgMap n (F.dgMap n f) :=
  (rfl)

/-! ### DG functors from their action on homogeneous morphisms -/

section OfDGMap

variable (obj : C → D)
  (map : ∀ {X Y : C} (n : ℤ), DGHom R n X Y →ₗ[R] DGHom R n (obj X) (obj Y))
  (map_dgDifferential : ∀ {X Y : C} (n : ℤ) (f : DGHom R n X Y),
    map (n + 1) (dgDifferential R n f) = dgDifferential R n (map n f))
  (map_dgId : ∀ X : C, map 0 (dgId R X) = dgId R (obj X))
  (map_dgComp : ∀ {X Y Z : C} {p q n : ℤ} (f : DGHom R p X Y) (g : DGHom R q Y Z)
    (h : p + q = n), map n (dgComp R f g h) = dgComp R (map p f) (map q g) h)

/-- The DG functor with a prescribed action on homogeneous morphisms: linear maps on the
morphisms of each degree which commute with the differential and preserve identities and
composition.  This is the converse of `CategoryTheory.EnrichedFunctor.dgMap_dgDifferential`,
`CategoryTheory.EnrichedFunctor.dgMap_dgId` and `CategoryTheory.EnrichedFunctor.dgMap_dgComp`:
the chain maps on Hom complexes and the enriched functor axioms are assembled from these
elementwise laws. -/
-- The body is exposed so that `(ofDGMap obj map …).obj X` is definitionally `obj X`; otherwise
-- the homogeneous morphisms of the two sides of `dgMap_ofDGMap` would have different types.
@[expose]
def ofDGMap : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D where
  obj := obj
  map X Y :=
    { f n := ModuleCat.ofHom (map n)
      comm' n m hnm := by
        obtain rfl : n + 1 = m := hnm
        ext f
        simpa using (map_dgDifferential n f).symm }
  map_id X := by
    -- A map out of the tensor unit is determined by its degree-zero component, evaluated at `1`.
    apply HomologicalComplex.from_single_hom_ext
    rw [← cancel_epi (singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat.{v} R))).inv]
    ext
    have key := map_dgId X
    rw [dgId_def, dgId_def] at key
    simpa using key
  map_comp X Y Z := by
    -- Both chain maps out of the tensor product are compared on each bidegree summand and on
    -- pure tensors, where they are the two sides of `map_dgComp`.
    ext n : 1
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q h
    rw [comp_f, comp_f, tensorHom_eq_mapBifunctorMap, ι_mapBifunctorMap_assoc]
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro f g
    have key := map_dgComp f g h
    rw [← dgCompMap_tmul, ← dgCompMap_tmul, dgCompMap_def, dgCompMap_def] at key
    simpa using key

/-- The DG functor with a prescribed action on homogeneous morphisms acts on objects by the
prescribed map. -/
@[simp]
theorem ofDGMap_obj (X : C) :
    (ofDGMap obj map map_dgDifferential map_dgId map_dgComp).obj X = obj X :=
  (rfl)

/-- The DG functor with a prescribed action on homogeneous morphisms acts on them by that
action. -/
@[simp]
theorem dgMap_ofDGMap {X Y : C} (n : ℤ) (f : DGHom R n X Y) :
    (ofDGMap obj map map_dgDifferential map_dgId map_dgComp).dgMap n f = map n f :=
  (rfl)

end OfDGMap

/-- A DG functor sends closed degree-zero morphisms to closed degree-zero morphisms. -/
theorem dgMap_mem_dgCycles {X Y : C} {f : DGHom R 0 X Y} (hf : f ∈ dgCycles R X Y) :
    F.dgMap 0 f ∈ dgCycles R (F.obj X) (F.obj Y) :=
  map_mem_dgCycles R (F.map X Y) hf

/-- A DG functor sends closed morphisms to closed morphisms. -/
theorem dgDifferential_dgMap_eq_zero {X Y : C} {n : ℤ} {f : DGHom R n X Y}
    (hf : dgDifferential R n f = 0) : dgDifferential R n (F.dgMap n f) = 0 := by
  rw [← dgMap_dgDifferential, hf, map_zero]

/-- The underlying functor of a DG functor acts on closed morphisms by its degree-zero map. -/
@[simp]
theorem dgClosedHom_forget_map
    {X Y : ForgetEnrichment (CochainComplex (ModuleCat.{v} R) ℤ) C} (f : X ⟶ Y) :
    dgClosedHom R (ForgetEnrichment.homOf _
      (ForgetEnrichment.homTo _ f ≫
        F.map (ForgetEnrichment.to _ X) (ForgetEnrichment.to _ Y))) =
      F.dgMap 0 (dgClosedHom R f) := by
  simp only [dgClosedHom_def, ForgetEnrichment.homTo_homOf,
    HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    EnrichedFunctor.dgMap_apply]

/-- The underlying functor sends a morphism represented by a cocycle to the morphism
represented by its image under the DG functor. -/
@[simp]
theorem forget_map_dgClosedHomOf
    {X Y : C} (f : DGHom R 0 X Y) (hf : f ∈ dgCycles R X Y) :
    ForgetEnrichment.homOf _
      (ForgetEnrichment.homTo _ (dgClosedHomOf R f hf) ≫ F.map X Y) =
      dgClosedHomOf R (F.dgMap 0 f) (F.dgMap_mem_dgCycles hf) := by
  apply dgClosedHom_injective R
  have h := F.dgClosedHom_forget_map (f := dgClosedHomOf R f hf)
  simp only [ForgetEnrichment.to_of] at h
  rw [h, dgClosedHom_dgClosedHomOf, dgClosedHom_dgClosedHomOf]

/-- A DG functor sends degree-zero boundaries to degree-zero boundaries. -/
theorem dgMap_mem_dgBoundaries {X Y : C} {f : DGHom R 0 X Y} (hf : f ∈ dgBoundaries R X Y) :
    F.dgMap 0 f ∈ dgBoundaries R (F.obj X) (F.obj Y) := by
  obtain ⟨h, rfl⟩ := (mem_dgBoundaries R).1 hf
  exact (mem_dgBoundaries R).2 ⟨F.dgMap (-1) h, (F.dgMap_dgDifferential h).symm⟩

/-! ### The induced functor on homotopy categories -/

/-- The map induced by a DG functor on degree-zero cohomology of Hom complexes is compatible with
the composition of homotopy classes. -/
theorem homologyMap_dgHomotopyComp {X Y Z : C} (a : DGHomotopyClass R X Y)
    (b : DGHomotopyClass R Y Z) :
    (homologyMap (F.map X Z) 0).hom (dgHomotopyComp R X Y Z a b) =
      dgHomotopyComp R (F.obj X) (F.obj Y) (F.obj Z) ((homologyMap (F.map X Y) 0).hom a)
        ((homologyMap (F.map Y Z) 0).hom b) := by
  obtain ⟨f, hf, rfl⟩ := exists_dgHomotopyClass_eq R a
  obtain ⟨g, hg, rfl⟩ := exists_dgHomotopyClass_eq R b
  simp_rw [dgHomotopyComp_dgHomotopyClass, homologyMap_dgHomotopyClass, ← dgMap_apply,
    dgHomotopyComp_dgHomotopyClass, dgCompZero_def, dgMap_dgComp]

/-- The functor `H⁰(F) : H⁰(C) ⥤ H⁰(D)` induced by a DG functor `F`.  On morphisms it is the map
induced by `F.map X Y` on degree-zero cohomology of Hom complexes; by
`CategoryTheory.EnrichedFunctor.mapDGHomotopyCategory_map_homOf` it sends the class of a closed
morphism `f` to the class of `F f`. -/
@[expose]
def mapDGHomotopyCategory : DGHomotopyCategory R C ⥤ DGHomotopyCategory R D where
  obj X := DGHomotopyCategory.of R (F.obj (DGHomotopyCategory.underlying R X))
  map {X Y} f := (homologyMap (F.map (DGHomotopyCategory.underlying R X)
    (DGHomotopyCategory.underlying R Y)) 0).hom f
  map_id X := by
    rw [DGHomotopyCategory.id_def, DGHomotopyCategory.id_def, homologyMap_dgHomotopyClass]
    simp_rw [← dgMap_apply, dgMap_dgId]
    -- `DGHomotopyCategory.underlying` of `DGHomotopyCategory.of` reduces to the object itself.
    rfl
  map_comp {X Y Z} f g := F.homologyMap_dgHomotopyComp f g

/-- `H⁰(F)` sends an object `X` of `H⁰(C)` to `F X`. -/
@[simp]
theorem mapDGHomotopyCategory_obj_of (X : C) :
    F.mapDGHomotopyCategory.obj (DGHomotopyCategory.of R X) = DGHomotopyCategory.of R (F.obj X) :=
  (rfl)

/-- `H⁰(F)` acts on morphisms by the map induced by `F` on degree-zero cohomology of Hom
complexes. -/
theorem mapDGHomotopyCategory_map {X Y : DGHomotopyCategory R C} (f : X ⟶ Y) :
    F.mapDGHomotopyCategory.map f = (homologyMap (F.map (DGHomotopyCategory.underlying R X)
      (DGHomotopyCategory.underlying R Y)) 0).hom f :=
  (rfl)

/-- `H⁰(F)` sends the class of a closed degree-zero morphism `f` to the class of `F f`. -/
@[simp]
theorem mapDGHomotopyCategory_map_homOf {X Y : C} (f : DGHom R 0 X Y) (hf : f ∈ dgCycles R X Y) :
    F.mapDGHomotopyCategory.map (DGHomotopyCategory.homOf R f hf) =
      DGHomotopyCategory.homOf R (F.dgMap 0 f) (F.dgMap_mem_dgCycles hf) := by
  rw [DGHomotopyCategory.homOf_def, DGHomotopyCategory.homOf_def]
  exact homologyMap_dgHomotopyClass R (F.map X Y) hf

/-- Taking the homotopy class of a closed morphism commutes with a DG functor. -/
@[expose]
def forgetCompDgClosedToHomotopyIso :
    F.forget ⋙ dgClosedToHomotopy (C := D) R ≅
      dgClosedToHomotopy (C := C) R ⋙ F.mapDGHomotopyCategory :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun f => by
    refine (Category.comp_id _).trans (Eq.trans ?_ (Category.id_comp _).symm)
    simp only [Functor.comp_map, dgClosedToHomotopy_map, EnrichedFunctor.forget_map,
      F.dgClosedHom_forget_map]
    exact (F.mapDGHomotopyCategory_map_homOf (dgClosedHom R f)
      (dgClosedHom_mem_dgCycles R f)).symm

/-- The forward component of the comparison between `Z⁰(F)` followed by the quotient and
the quotient followed by `H⁰(F)` is the identity. -/
@[simp]
theorem forgetCompDgClosedToHomotopyIso_hom_app
    (X : ForgetEnrichment (CochainComplex (ModuleCat.{v} R) ℤ) C) :
    F.forgetCompDgClosedToHomotopyIso.hom.app X = 𝟙 _ :=
  rfl

/-- The inverse component of the comparison between `Z⁰(F)` followed by the quotient and
the quotient followed by `H⁰(F)` is the identity. -/
@[simp]
theorem forgetCompDgClosedToHomotopyIso_inv_app
    (X : ForgetEnrichment (CochainComplex (ModuleCat.{v} R) ℤ) C) :
    F.forgetCompDgClosedToHomotopyIso.inv.app X = 𝟙 _ :=
  rfl

instance : F.mapDGHomotopyCategory.Additive where
  map_add {X Y} f g := map_add (homologyMap (F.map (DGHomotopyCategory.underlying R X)
    (DGHomotopyCategory.underlying R Y)) 0).hom f g

instance : F.mapDGHomotopyCategory.Linear R where
  map_smul {X Y} f r := map_smul (homologyMap (F.map (DGHomotopyCategory.underlying R X)
    (DGHomotopyCategory.underlying R Y)) 0).hom r f

/-- `H⁰` of the identity DG functor is the identity functor. -/
def mapDGHomotopyCategoryIdIso :
    (EnrichedFunctor.id (CochainComplex (ModuleCat.{v} R) ℤ) C).mapDGHomotopyCategory ≅
      𝟭 (DGHomotopyCategory R C) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun f ↦ by
    -- Both functors have the same objects; the identity DG functor acts on Hom complexes by
    -- identities, so `H⁰` of it acts by `homologyMap (𝟙 _) 0`.
    refine (Category.comp_id _).trans (Eq.trans ?_ (Category.id_comp _).symm)
    exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (homologyMap_id (dgHomComplex R
      (DGHomotopyCategory.underlying R _) (DGHomotopyCategory.underlying R _)) 0)) f

/-- `H⁰` of a composite of DG functors is the composite of the induced functors. -/
def mapDGHomotopyCategoryCompIso :
    (F.comp (CochainComplex (ModuleCat.{v} R) ℤ) G).mapDGHomotopyCategory ≅
      F.mapDGHomotopyCategory ⋙ G.mapDGHomotopyCategory :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun f ↦ by
    -- Both functors have the same objects; the composite DG functor acts on Hom complexes by
    -- `F.map _ _ ≫ G.map _ _`, so the claim is `homologyMap_comp`.
    refine (Category.comp_id _).trans (Eq.trans ?_ (Category.id_comp _).symm)
    exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (homologyMap_comp (F.map _ _)
      (G.map _ _) 0)) f

end

end CategoryTheory.EnrichedFunctor
