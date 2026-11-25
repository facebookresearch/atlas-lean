/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
This completed source port retains the original Apache 2.0 license and author credit.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/CategoryTheory/DG/HomComplexData.lean
Only module/namespace paths are adapted for Atlas; source operations and hypotheses are retained.
-/

public import MathlibExt.CategoryTheory.DGSource.DGCategory

/-!
# Differential graded categories from explicit Hom-complex data

A differential graded category is defined as a category enriched in cochain complexes of
`R`-modules, and `MathlibExt/CategoryTheory/DGSource/DGCategory.lean` unpacks that enrichment into homogeneous
morphisms, their differential, and their composition.  This file goes the other way.  Explicit
Hom-complex data, `MathlibExt.DGSource.DGCategoryData`, consists of a Hom complex for every pair of objects,
bilinear composition maps on homogeneous degrees, and identities, subject to the graded Leibniz
rule, associativity, and the unit laws stated on elements.  Such data determines a differential
graded category, `MathlibExt.DGSource.DGCategoryData.toDGCategory`, whose homogeneous morphisms, differential,
identities and composition are the given ones.

The two presentations are equivalent: extracting the explicit data from a differential graded
category and rebuilding the enrichment recovers the enrichment, and rebuilding the data from the
enrichment of explicit data recovers the data.  Hence a differential graded category may be
specified by elementwise formulas, and a differential graded category built from homogeneous
morphisms, such as the one-object category of a differential graded algebra or the category of
differential graded modules, needs no monoidal plumbing of its own.

Composition in `MathlibExt.DGSource.DGCategoryData` is in Mathlib's enriched factor order, so `comp f g` is
`f` followed by `g` and the Leibniz sign is carried by the degree of `f`, exactly as for
`MathlibExt.DGSource.dgComp`.  Keller's convention, in which `g ∘ f` carries the Leibniz sign of `g`, differs
by the Koszul sign `(-1) ^ (|f| * |g|)`; `MathlibExt.DGSource.DGCategoryData.ofKeller` converts data given in
that convention.

## Main definitions

* `MathlibExt.DGSource.DGCategoryData`: explicit Hom-complex data for a differential graded category.
* `MathlibExt.DGSource.DGCategoryData.toDGCategory`: the differential graded category it determines.
* `MathlibExt.DGSource.DGCategoryData.ofKeller`: the same data from Keller-ordered composition.
* `MathlibExt.DGSource.dgCategoryData`: the explicit Hom-complex data of a differential graded category.
* `MathlibExt.DGSource.DGCategoryData.equivDGCategory`: the two presentations are equivalent.

## Main results

* `MathlibExt.DGSource.DGCategoryData.dgComp_toDGCategory`, `MathlibExt.DGSource.DGCategoryData.dgId_toDGCategory`,
  `MathlibExt.DGSource.DGCategoryData.dgDifferential_toDGCategory`: the homogeneous calculus of the
  constructed category is the given data.
* `MathlibExt.DGSource.DGCategoryData.toDGCategory_dgCategoryData` and
  `MathlibExt.DGSource.DGCategoryData.dgCategoryData_toDGCategory`: the two round trips.

## References

* B. Keller, *Deriving DG categories*, Section 1.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1, for the sign
  conventions and the comparison sign between the two factor orders.
* `MathlibExt/CategoryTheory/DGSource/LinearHomComplexComposition.lean`.
* `MathlibExt/CategoryTheory/DGSource/LinearHomComplexEnrichment.lean`.
-/

public section

open CategoryTheory MonoidalCategory HomologicalComplex

namespace MathlibExt.DGSource

universe v u

/-- **Explicit Hom-complex data** for a differential graded category over `R` on the objects
`C`: a Hom complex `hom X Y` for every pair of objects, bilinear composition
`comp p q n h : (hom X Y).X p →ₗ[R] (hom Y Z).X q →ₗ[R] (hom X Z).X n` for `p + q = n`, in
Mathlib's enriched factor order, and identities `id X` of degree zero, satisfying the graded
Leibniz rule, associativity, and the unit laws on homogeneous elements.  Such data determines the
differential graded category `MathlibExt.DGSource.DGCategoryData.toDGCategory`. -/
structure DGCategoryData (R : Type v) [CommRing R] (C : Type u) where
  /-- The Hom complex from `X` to `Y`. -/
  hom : C → C → CochainComplex (ModuleCat.{v} R) ℤ
  /-- Composition of a degree-`p` morphism `X ⟶ Y` with a degree-`q` morphism `Y ⟶ Z`, in
  Mathlib's enriched factor order: `comp p q n h f g` is `f` followed by `g`. -/
  comp {X Y Z : C} (p q n : ℤ) (h : p + q = n) :
    (hom X Y).X p →ₗ[R] (hom Y Z).X q →ₗ[R] (hom X Z).X n
  /-- The identity of `X`, a morphism of degree zero. -/
  id (X : C) : (hom X X).X 0
  /-- The graded Leibniz rule, with the Koszul sign carried by the degree of the first factor. -/
  d_comp {X Y Z : C} {p q n : ℤ} (h : p + q = n) (f : (hom X Y).X p) (g : (hom Y Z).X q) :
    ((hom X Z).d n (n + 1)).hom (comp p q n h f g) =
      comp (p + 1) q (n + 1) (by omega) (((hom X Y).d p (p + 1)).hom f) g +
        p.negOnePow • comp p (q + 1) (n + 1) (by omega) f (((hom Y Z).d q (q + 1)).hom g)
  /-- Composition is associative. -/
  comp_assoc {W X Y Z : C} {p q r pq qr n : ℤ} (hpq : p + q = pq) (hqr : q + r = qr)
      (h : p + q + r = n) (f : (hom W X).X p) (g : (hom X Y).X q) (k : (hom Y Z).X r) :
    comp pq r n (by omega) (comp p q pq hpq f g) k = comp p qr n (by omega) f (comp q r qr hqr g k)
  /-- The identity is a left unit. -/
  id_comp {X Y : C} {q : ℤ} (g : (hom X Y).X q) : comp 0 q q (zero_add q) (id X) g = g
  /-- The identity is a right unit. -/
  comp_id {X Y : C} {p : ℤ} (f : (hom X Y).X p) : comp p 0 p (add_zero p) f (id Y) = f

attribute [simp] DGCategoryData.id_comp DGCategoryData.comp_id

namespace DGCategoryData

variable {R : Type v} [CommRing R] {C : Type u} (D : DGCategoryData R C)

/-- The identity is a cycle. -/
@[simp]
theorem d_id (X : C) : ((D.hom X X).d 0 1).hom (D.id X) = 0 := by
  have key := D.d_comp (zero_add 0) (D.id X) (D.id X)
  simp only [D.id_comp, D.comp_id, Int.negOnePow_zero, one_smul] at key
  exact left_eq_add.mp key

/-! ### The enriched composition and identity -/

/-- The bidegree-`(p, q)` component of composition, as a morphism out of the tensor product of
the two homogeneous modules. -/
noncomputable def compMap (X Y Z : C) (p q n : ℤ) (h : p + q = n) :
    (D.hom X Y).X p ⊗ (D.hom Y Z).X q ⟶ (D.hom X Z).X n :=
  ModuleCat.ofHom (TensorProduct.lift (D.comp p q n h))

@[simp]
theorem compMap_tmul (X Y Z : C) (p q n : ℤ) (h : p + q = n) (f : (D.hom X Y).X p)
    (g : (D.hom Y Z).X q) :
    (D.compMap X Y Z p q n h).hom (f ⊗ₜ g) = D.comp p q n h f g :=
  (rfl)

/-- Composition as a morphism of cochain complexes out of the totalized tensor product of the two
Hom complexes.  The Leibniz rule makes it a chain map. -/
noncomputable def enrichedComp (X Y Z : C) : D.hom X Y ⊗ D.hom Y Z ⟶ D.hom X Z where
  f n := mapBifunctorDesc (fun p q h => D.compMap X Y Z p q n h)
  comm' n m hnm := by
    obtain rfl : m = n + 1 := hnm.symm
    apply mapBifunctor.hom_ext
    intro p q h
    rw [ι_mapBifunctorDesc_assoc, ← Category.assoc, ι_tensorObj_d]
    simp only [curriedTensor_map_app, curriedTensor_obj_map, Preadditive.add_comp,
      Linear.units_smul_comp, Category.assoc, ι_mapBifunctorDesc]
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro f g
    have hn : p + q = n := h
    subst hn
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply, compMap_tmul,
      ModuleCat.hom_add, ModuleCat.hom_smul, LinearMap.add_apply, LinearMap.smul_apply]
    exact D.d_comp rfl f g

/-- The degree-`n` component of the enriched composition is assembled from the bidegree
components. -/
theorem enrichedComp_f (X Y Z : C) (n : ℤ) :
    (D.enrichedComp X Y Z).f n = mapBifunctorDesc (fun p q h => D.compMap X Y Z p q n h) :=
  (rfl)

/-- On the bidegree-`(p, q)` summand, the enriched composition is the bilinear composition of the
data. -/
@[reassoc (attr := simp)]
theorem ι_enrichedComp (X Y Z : C) (p q n : ℤ) (h : p + q = n) :
    ιTensorObj (D.hom X Y) (D.hom Y Z) p q n h ≫ (D.enrichedComp X Y Z).f n =
      D.compMap X Y Z p q n h := by
  rw [enrichedComp_f]
  exact ι_mapBifunctorDesc _ _ _ _

/-- The identity of `X`, as a morphism from the tensor unit to the Hom complex of `X` with
itself. -/
noncomputable def enrichedId (X : C) : 𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ) ⟶ D.hom X X :=
  mkHomFromSingle (ModuleCat.ofHom (LinearMap.toSpanSingleton R _ (D.id X))) fun k hk => by
    obtain rfl : k = 0 + 1 := hk.symm
    ext
    simp

/-- The degree-zero component of the enriched identity. -/
theorem enrichedId_f_zero (X : C) :
    (D.enrichedId X).f 0 =
      (singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat.{v} R))).hom ≫
        ModuleCat.ofHom (LinearMap.toSpanSingleton R _ (D.id X)) :=
  mkHomFromSingle_f _ _

/-- The degree-zero component of the enriched identity sends a scalar to that multiple of the
identity. -/
@[simp]
theorem enrichedId_f_zero_apply (X : C) (r : R) :
    ((D.enrichedId X).f 0).hom
        ((singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat.{v} R))).inv r) = r • D.id X := by
  rw [enrichedId_f_zero, ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    Iso.inv_hom_id_apply]
  -- After the round trip through `singleObjXSelf`, the scalar is an element of the tensor unit,
  -- which is the ground ring only after unfolding, so the evaluation lemma is applied by hand.
  exact LinearMap.toSpanSingleton_apply R _ (D.id X) r

/-! ### The differential graded category -/

/-- The enriched identity is a left unit for the enriched composition. -/
@[reassoc (attr := simp)]
theorem leftUnitor_inv_enrichedId_enrichedComp (X Y : C) :
    (λ_ (D.hom X Y)).inv ≫ D.enrichedId X ▷ D.hom X Y ≫ D.enrichedComp X X Y = 𝟙 _ := by
  ext j : 1
  rw [comp_f, comp_f, leftUnitor_inv_f, leftUnitor'_inv, Category.assoc, Category.assoc,
    ι_whiskerRight_assoc, ι_enrichedComp, id_f]
  ext f
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    ModuleCat.MonoidalCategory.leftUnitor_inv_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply, compMap_tmul, ModuleCat.hom_id,
    LinearMap.id_coe, id_eq]
  rw [enrichedId_f_zero_apply, one_smul, D.id_comp]

/-- The enriched identity is a right unit for the enriched composition. -/
@[reassoc (attr := simp)]
theorem rightUnitor_inv_enrichedId_enrichedComp (X Y : C) :
    (ρ_ (D.hom X Y)).inv ≫ D.hom X Y ◁ D.enrichedId Y ≫ D.enrichedComp X Y Y = 𝟙 _ := by
  ext j : 1
  rw [comp_f, comp_f, rightUnitor_inv_f, rightUnitor'_inv, Category.assoc, Category.assoc,
    ι_whiskerLeft_assoc, ι_enrichedComp, id_f]
  ext f
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    ModuleCat.MonoidalCategory.rightUnitor_inv_apply,
    ModuleCat.MonoidalCategory.whiskerLeft_apply, compMap_tmul, ModuleCat.hom_id,
    LinearMap.id_coe, id_eq]
  rw [enrichedId_f_zero_apply, one_smul, D.comp_id]

/- The left-associated composite, restricted to a tridegree summand. -/
private theorem ι₁₂_enrichedComp_whiskerRight_enrichedComp (W X Y Z : C) (p q r j : ℤ)
    (h : p + q + r = j) :
    mapBifunctor₁₂.ι (curriedTensor (ModuleCat.{v} R)) (curriedTensor (ModuleCat.{v} R))
        (D.hom W X) (D.hom X Y) (D.hom Y Z) (ComplexShape.up ℤ) (ComplexShape.up ℤ) p q r j h ≫
      (D.enrichedComp W X Y ▷ D.hom Y Z ≫ D.enrichedComp W Y Z).f j =
    (D.compMap W X Y p q (p + q) rfl ▷ (D.hom Y Z).X r) ≫
      D.compMap W Y Z (p + q) r j h := by
  rw [comp_f, ← Category.assoc, whiskerRight_eq_mapBifunctorMap,
    mapBifunctor₁₂.ι_eq (curriedTensor (ModuleCat.{v} R)) (curriedTensor (ModuleCat.{v} R))
      (D.hom W X) (D.hom X Y) (D.hom Y Z) (ComplexShape.up ℤ) (ComplexShape.up ℤ) p q r (p + q) j
      rfl h, Category.assoc, Category.assoc, ι_mapBifunctorMap_assoc, ι_enrichedComp]
  simp only [id_f, CategoryTheory.Functor.map_id, curriedTensor_map_app, Category.id_comp]
  rw [← comp_whiskerRight_assoc, ι_enrichedComp]

/- The associator followed by the right-associated composite, restricted to a tridegree
summand. -/
private theorem ι₁₂_associator_whiskerLeft_enrichedComp (W X Y Z : C) (p q r j : ℤ)
    (h : p + q + r = j) :
    mapBifunctor₁₂.ι (curriedTensor (ModuleCat.{v} R)) (curriedTensor (ModuleCat.{v} R))
        (D.hom W X) (D.hom X Y) (D.hom Y Z) (ComplexShape.up ℤ) (ComplexShape.up ℤ) p q r j h ≫
      ((α_ (D.hom W X) (D.hom X Y) (D.hom Y Z)).hom ≫ D.hom W X ◁ D.enrichedComp X Y Z ≫
        D.enrichedComp W X Z).f j =
    (α_ ((D.hom W X).X p) ((D.hom X Y).X q) ((D.hom Y Z).X r)).hom ≫
      ((D.hom W X).X p ◁ D.compMap X Y Z q r (q + r) rfl) ≫
        D.compMap W X Z p (q + r) j (by omega) := by
  -- The left-associated inclusion of the tridegree summand, in the whiskered form in which
  -- `HomologicalComplex.ι_ι_associator_hom` computes the associator.
  have e : mapBifunctor₁₂.ι (curriedTensor (ModuleCat.{v} R)) (curriedTensor (ModuleCat.{v} R))
      (D.hom W X) (D.hom X Y) (D.hom Y Z) (ComplexShape.up ℤ) (ComplexShape.up ℤ) p q r j h =
      (ιTensorObj (D.hom W X) (D.hom X Y) p q (p + q) rfl ▷ (D.hom Y Z).X r) ≫
        ιTensorObj (D.hom W X ⊗ D.hom X Y) (D.hom Y Z) (p + q) r j h := by
    rw [mapBifunctor₁₂.ι_eq (curriedTensor (ModuleCat.{v} R)) (curriedTensor (ModuleCat.{v} R))
      (D.hom W X) (D.hom X Y) (D.hom Y Z) (ComplexShape.up ℤ) (ComplexShape.up ℤ) p q r (p + q) j
      rfl h]
    rfl
  rw [comp_f, comp_f, e, Category.assoc,
    ι_ι_associator_hom_assoc _ _ _ p q r (p + q) (q + r) j rfl rfl h (by omega),
    ι_whiskerLeft_assoc,
    ι_enrichedComp, ← whiskerLeft_comp_assoc, ι_enrichedComp]

/-- The enriched composition is associative, with the tensor products identified by the monoidal
associator. -/
@[reassoc (attr := simp)]
theorem enrichedComp_assoc (W X Y Z : C) :
    (α_ (D.hom W X) (D.hom X Y) (D.hom Y Z)).inv ≫ D.enrichedComp W X Y ▷ D.hom Y Z ≫
        D.enrichedComp W Y Z =
      D.hom W X ◁ D.enrichedComp X Y Z ≫ D.enrichedComp W X Z := by
  rw [Iso.inv_comp_eq]
  ext j : 1
  apply mapBifunctor₁₂.hom_ext
  intro p q r h
  have h' : p + q + r = j := h
  rw [D.ι₁₂_enrichedComp_whiskerRight_enrichedComp W X Y Z p q r j h',
    D.ι₁₂_associator_whiskerLeft_enrichedComp W X Y Z p q r j h']
  apply ModuleCat.MonoidalCategory.tensor_ext₃'
  intro f g k
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply, ModuleCat.MonoidalCategory.associator_hom_apply,
    compMap_tmul]
  exact D.comp_assoc rfl rfl h' f g k

/-- The differential graded category determined by explicit Hom-complex data.  Its body is exposed
so that its homogeneous morphisms `MathlibExt.DGSource.DGHom` remain definitionally the given
`(D.hom X Y).X n`. -/
@[expose, instance_reducible]
noncomputable def toDGCategory : DGCategory R C where
  Hom := D.hom
  id := D.enrichedId
  comp := D.enrichedComp
  id_comp := D.leftUnitor_inv_enrichedId_enrichedComp
  comp_id := D.rightUnitor_inv_enrichedId_enrichedComp
  assoc := D.enrichedComp_assoc

/-- The Hom complex of the constructed category is the given one. -/
@[simp]
theorem dgHomComplex_toDGCategory (X Y : C) :
    letI := D.toDGCategory
    dgHomComplex R X Y = D.hom X Y :=
  (rfl)

/-- The enriched identity of the constructed category is the given one. -/
@[simp]
theorem eId_toDGCategory (X : C) :
    letI := D.toDGCategory
    eId (CochainComplex (ModuleCat.{v} R) ℤ) X = D.enrichedId X :=
  (rfl)

/-- The enriched composition of the constructed category is the given one. -/
@[simp]
theorem eComp_toDGCategory (X Y Z : C) :
    letI := D.toDGCategory
    eComp (CochainComplex (ModuleCat.{v} R) ℤ) X Y Z = D.enrichedComp X Y Z :=
  (rfl)

/-- The differential of the constructed category is the differential of the given Hom
complexes. -/
@[simp]
theorem dgDifferential_toDGCategory {X Y : C} (n : ℤ) (f : (D.hom X Y).X n) :
    letI := D.toDGCategory
    dgDifferential R (X := X) (Y := Y) n f = ((D.hom X Y).d n (n + 1)).hom f :=
  (rfl)

/-- The bidegree components of composition in the constructed category are the given ones. -/
@[simp]
theorem dgCompMap_toDGCategory (X Y Z : C) (p q n : ℤ) (h : p + q = n) :
    letI := D.toDGCategory
    dgCompMap R X Y Z p q n h = D.compMap X Y Z p q n h :=
  (@dgCompMap_def R _ C D.toDGCategory X Y Z p q n h).trans (D.ι_enrichedComp X Y Z p q n h)

/-- Composition in the constructed category is the given composition. -/
@[simp]
theorem dgComp_toDGCategory {X Y Z : C} {p q n : ℤ} (f : (D.hom X Y).X p) (g : (D.hom Y Z).X q)
    (h : p + q = n) :
    letI := D.toDGCategory
    dgComp R (X := X) (Y := Y) (Z := Z) f g h = D.comp p q n h f g :=
  (@dgCompMap_tmul R _ C D.toDGCategory X Y Z p q n h f g).symm.trans
    (congrArg (fun φ => ModuleCat.Hom.hom φ (f ⊗ₜ g)) (D.dgCompMap_toDGCategory X Y Z p q n h))

/-- The identity of the constructed category is the given identity. -/
@[simp]
theorem dgId_toDGCategory (X : C) :
    letI := D.toDGCategory
    dgId R X = D.id X :=
  (@dgId_def R _ C D.toDGCategory X).trans
    ((D.enrichedId_f_zero_apply X 1).trans (one_smul R (D.id X)))

/-! ### Keller-ordered data -/

section Keller

variable (hom : C → C → CochainComplex (ModuleCat.{v} R) ℤ)
  (comp : ∀ {X Y Z : C} (q p n : ℤ), q + p = n →
    (hom Y Z).X q →ₗ[R] (hom X Y).X p →ₗ[R] (hom X Z).X n)
  (id : ∀ X : C, (hom X X).X 0)

/-- Explicit Hom-complex data from **Keller-ordered** composition.  Here `comp q p n h g f` is
`g ∘ f` for `g : Y ⟶ Z` of degree `q` and `f : X ⟶ Y` of degree `p`, the Leibniz rule
`d (g ∘ f) = d g ∘ f + (-1) ^ q • g ∘ d f` carries the sign of `g`, and associativity and the unit
laws are the usual ones.  The enriched-order composition of the resulting data is
`(-1) ^ (p * q) • g ∘ f`, the Koszul sign converting between the two factor orders.  The body is
exposed so that the homogeneous morphisms of the resulting data remain definitionally the given
`(hom X Y).X n`. -/
@[expose]
noncomputable def ofKeller
    (d_comp : ∀ {X Y Z : C} {q p n : ℤ} (h : q + p = n) (g : (hom Y Z).X q) (f : (hom X Y).X p),
      ((hom X Z).d n (n + 1)).hom (comp q p n h g f) =
        comp (q + 1) p (n + 1) (by omega) (((hom Y Z).d q (q + 1)).hom g) f +
          q.negOnePow • comp q (p + 1) (n + 1) (by omega) g (((hom X Y).d p (p + 1)).hom f))
    (comp_assoc : ∀ {W X Y Z : C} {r q p rq qp n : ℤ} (hrq : r + q = rq) (hqp : q + p = qp)
      (h : r + q + p = n) (k : (hom Y Z).X r) (g : (hom X Y).X q) (f : (hom W X).X p),
      comp rq p n (by omega) (comp r q rq hrq k g) f =
        comp r qp n (by omega) k (comp q p qp hqp g f))
    (comp_id : ∀ {X Y : C} {q : ℤ} (g : (hom X Y).X q), comp q 0 q (add_zero q) g (id X) = g)
    (id_comp : ∀ {X Y : C} {p : ℤ} (f : (hom X Y).X p), comp 0 p p (zero_add p) (id Y) f = f) :
    DGCategoryData R C where
  hom := hom
  comp p q n h := (p * q).negOnePow • (comp q p n (by omega)).flip
  id := id
  d_comp {X Y Z p q n} h f g := by
    have hd (z : (hom X Z).X n) (u : ℤˣ) :
        ((hom X Z).d n (n + 1)).hom (u • z) = u • ((hom X Z).d n (n + 1)).hom z := by
      rw [Units.smul_def, map_zsmul, ← Units.smul_def]
    -- The two Koszul signs produced by differentiating each factor.
    have h₁ : (p * q).negOnePow * q.negOnePow = ((p + 1) * q).negOnePow := by
      rw [← Int.negOnePow_add]
      congr 1
      ring
    have h₂ : p.negOnePow * (p * (q + 1)).negOnePow = (p * q).negOnePow := by
      rw [← Int.negOnePow_add, Int.negOnePow_eq_iff]
      exact ⟨p, by ring⟩
    simp only [LinearMap.smul_apply, LinearMap.flip_apply]
    rw [hd, d_comp, smul_add, smul_smul, smul_smul, h₁, h₂]
    exact add_comm _ _
  comp_assoc {W X Y Z p q r pq qr n} hpq hqr h f g k := by
    subst hpq hqr
    have hin (z : (hom W Y).X (p + q)) (u : ℤˣ) :
        comp r (p + q) n (by omega) k (u • z) = u • comp r (p + q) n (by omega) k z := by
      rw [Units.smul_def, map_zsmul, ← Units.smul_def]
    have hout (z : (hom X Z).X (q + r)) (u : ℤˣ) :
        comp (q + r) p n (by omega) (u • z) f = u • comp (q + r) p n (by omega) z f := by
      rw [Units.smul_def, map_zsmul, ← Units.smul_def, LinearMap.smul_apply]
    -- The Koszul signs of the two bracketings agree.
    have hsign : ((p + q) * r).negOnePow * (p * q).negOnePow =
        (p * (q + r)).negOnePow * (q * r).negOnePow := by
      rw [← Int.negOnePow_add, ← Int.negOnePow_add]
      congr 1
      ring
    simp only [LinearMap.smul_apply, LinearMap.flip_apply]
    rw [hin, hout, smul_smul, smul_smul, comp_assoc (add_comm r q) (add_comm q p) (by omega) k g f,
      hsign]
  id_comp g := by
    simp only [LinearMap.flip_apply, zero_mul, Int.negOnePow_zero, one_smul, comp_id]
  comp_id f := by
    simp only [LinearMap.flip_apply, mul_zero, Int.negOnePow_zero, one_smul, id_comp]

variable {hom comp id}
variable {d_comp : ∀ {X Y Z : C} {q p n : ℤ} (h : q + p = n) (g : (hom Y Z).X q)
    (f : (hom X Y).X p),
    ((hom X Z).d n (n + 1)).hom (comp q p n h g f) =
      comp (q + 1) p (n + 1) (by omega) (((hom Y Z).d q (q + 1)).hom g) f +
        q.negOnePow • comp q (p + 1) (n + 1) (by omega) g (((hom X Y).d p (p + 1)).hom f)}
  {comp_assoc : ∀ {W X Y Z : C} {r q p rq qp n : ℤ} (hrq : r + q = rq) (hqp : q + p = qp)
    (h : r + q + p = n) (k : (hom Y Z).X r) (g : (hom X Y).X q) (f : (hom W X).X p),
    comp rq p n (by omega) (comp r q rq hrq k g) f =
      comp r qp n (by omega) k (comp q p qp hqp g f)}
  {comp_id : ∀ {X Y : C} {q : ℤ} (g : (hom X Y).X q), comp q 0 q (add_zero q) g (id X) = g}
  {id_comp : ∀ {X Y : C} {p : ℤ} (f : (hom X Y).X p), comp 0 p p (zero_add p) (id Y) f = f}

@[simp]
theorem ofKeller_hom (X Y : C) :
    (ofKeller hom comp id d_comp comp_assoc comp_id id_comp).hom X Y = hom X Y :=
  (rfl)

/-- The enriched-order composition of Keller-ordered data is Keller composition in reversed order,
with the Koszul sign `(-1) ^ (p * q)`. -/
@[simp]
theorem ofKeller_comp {X Y Z : C} (p q n : ℤ) (h : p + q = n) (f : (hom X Y).X p)
    (g : (hom Y Z).X q) :
    (ofKeller hom comp id d_comp comp_assoc comp_id id_comp).comp p q n h f g =
      (p * q).negOnePow • comp q p n (by omega) g f :=
  (rfl)

@[simp]
theorem ofKeller_id (X : C) :
    (ofKeller hom comp id d_comp comp_assoc comp_id id_comp).id X = id X :=
  (rfl)

end Keller

end DGCategoryData

/-! ### The explicit data of a differential graded category -/

section OfDGCategory

variable (R : Type v) [CommRing R] (C : Type u) [DGCategory R C]

/-- The explicit Hom-complex data of a differential graded category: its Hom complexes,
homogeneous composition, and identities.  Its body is exposed so that its Hom complexes remain
definitionally those of the category. -/
@[expose]
noncomputable def dgCategoryData : DGCategoryData R C where
  hom := dgHomComplex R
  comp _ _ _ h := LinearMap.mk₂ R (fun f g => dgComp R f g h)
    (fun f f' g => add_dgComp R f f' g h) (fun r f g => smul_dgComp R r f g h)
    (fun f g g' => dgComp_add R f g g' h) (fun r f g => dgComp_smul R r f g h)
  id := dgId R
  d_comp h f g := dgDifferential_dgComp R f g h
  comp_assoc hpq hqr h f g k := dgComp_assoc R f g k hpq hqr h
  id_comp g := dgId_dgComp R g
  comp_id f := dgComp_dgId R f

@[simp]
theorem dgCategoryData_hom (X Y : C) : (dgCategoryData R C).hom X Y = dgHomComplex R X Y :=
  (rfl)

@[simp]
theorem dgCategoryData_comp {X Y Z : C} (p q n : ℤ) (h : p + q = n) (f : DGHom R p X Y)
    (g : DGHom R q Y Z) : (dgCategoryData R C).comp p q n h f g = dgComp R f g h :=
  (rfl)

@[simp]
theorem dgCategoryData_id (X : C) : (dgCategoryData R C).id X = dgId R X :=
  (rfl)

end OfDGCategory

namespace DGCategoryData

variable {R : Type v} [CommRing R] {C : Type u}

/-- The enriched identity of a differential graded category is the enriched identity of its
explicit data. -/
@[simp]
theorem enrichedId_dgCategoryData [DGCategory R C] (X : C) :
    (dgCategoryData R C).enrichedId X = eId (CochainComplex (ModuleCat.{v} R) ℤ) X := by
  apply from_single_hom_ext
  rw [enrichedId_f_zero, ← cancel_epi (singleObjXSelf (ComplexShape.up ℤ) 0
    (𝟙_ (ModuleCat.{v} R))).inv, Iso.inv_hom_id_assoc]
  -- Both sides are now maps out of the ground ring, so they agree once they agree at `1`.
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  rw [ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply_one, dgCategoryData_id, dgId_def,
    ModuleCat.hom_comp, LinearMap.comp_apply]
  rfl

/-- The enriched composition of a differential graded category is the enriched composition of its
explicit data. -/
@[simp]
theorem enrichedComp_dgCategoryData [DGCategory R C] (X Y Z : C) :
    (dgCategoryData R C).enrichedComp X Y Z = eComp (CochainComplex (ModuleCat.{v} R) ℤ) X Y Z := by
  ext n : 1
  apply mapBifunctor.hom_ext
  intro p q h
  refine ((dgCategoryData R C).ι_enrichedComp X Y Z p q n h).trans
    (Eq.trans ?_ (dgCompMap_def R X Y Z p q n h))
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro f g
  exact (dgCategoryData_comp R C p q n h f g).trans (dgCompMap_tmul R h f g).symm

/-- Rebuilding a differential graded category from its explicit Hom-complex data recovers the
category. -/
@[simp]
theorem toDGCategory_dgCategoryData [inst : DGCategory R C] :
    (dgCategoryData R C).toDGCategory = inst := by
  have hid : ∀ X, (dgCategoryData R C).enrichedId X = eId (CochainComplex (ModuleCat.{v} R) ℤ) X :=
    enrichedId_dgCategoryData
  have hcomp : ∀ X Y Z, (dgCategoryData R C).enrichedComp X Y Z =
      eComp (CochainComplex (ModuleCat.{v} R) ℤ) X Y Z :=
    enrichedComp_dgCategoryData
  obtain ⟨Hom, id, comp, _, _, _⟩ := inst
  unfold toDGCategory
  congr 1
  · exact funext hid
  · exact funext fun X => funext fun Y => funext fun Z => hcomp X Y Z

/-- Extracting the explicit Hom-complex data of the category built from explicit data recovers the
data. -/
@[simp]
theorem dgCategoryData_toDGCategory (D : DGCategoryData R C) :
    letI := D.toDGCategory
    dgCategoryData R C = D := by
  have hcomp : ∀ {X Y Z : C} (p q n : ℤ) (h : p + q = n) (f : (D.hom X Y).X p)
      (g : (D.hom Y Z).X q), (@dgCategoryData R _ C D.toDGCategory).comp p q n h f g =
        D.comp p q n h f g :=
    fun p q n h f g => D.dgComp_toDGCategory f g h
  have hid : ∀ X, (@dgCategoryData R _ C D.toDGCategory).id X = D.id X := D.dgId_toDGCategory
  obtain ⟨hom, comp, id, _, _, _, _⟩ := D
  unfold dgCategoryData
  congr 1
  · exact funext fun X => funext fun Y => funext fun Z => funext fun p => funext fun q =>
      funext fun n => funext fun h => LinearMap.ext₂ (hcomp p q n h)
  · exact funext hid

/-- **The two presentations of a differential graded category agree**: explicit Hom-complex data
on `C` is the same as an enrichment of `C` in cochain complexes of `R`-modules. -/
noncomputable def equivDGCategory : DGCategoryData R C ≃ DGCategory R C where
  toFun D := D.toDGCategory
  invFun inst := @dgCategoryData R _ C inst
  left_inv D := dgCategoryData_toDGCategory D
  right_inv _ := toDGCategory_dgCategoryData

@[simp]
theorem equivDGCategory_apply (D : DGCategoryData R C) : equivDGCategory D = D.toDGCategory :=
  (rfl)

@[simp]
theorem equivDGCategory_symm_apply [inst : DGCategory R C] :
    equivDGCategory.symm inst = dgCategoryData R C :=
  (rfl)

end DGCategoryData

end MathlibExt.DGSource
