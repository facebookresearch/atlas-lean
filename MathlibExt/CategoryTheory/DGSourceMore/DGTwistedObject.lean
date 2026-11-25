/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
This completed proof port retains the original Apache 2.0 license and author credit.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/CategoryTheory/DG/Twisted/Basic.lean
Original license: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
Modifications: only module/namespace paths are adapted for Atlas.
Mathematical operations, hypotheses and proof bodies are retained.
-/

public import MathlibExt.CategoryTheory.DGSource.DGFunctor
public import MathlibExt.CategoryTheory.DGSource.DGFunctorHomComplex

/-!
# Twisted objects of a differential graded category

A **twisted object** of a differential graded category `C` is an object `X` together with a
degree-one endomorphism `δ` satisfying the Maurer–Cartan equation.  In Mathlib's enriched factor
order, where `dgComp f g` is `f` followed by `g`, that equation reads

`d δ = dgComp δ δ`.

In Keller's order, `δ ∘ δ = (-1)^(1 * 1) • dgComp δ δ = -dgComp δ δ`, so it is the familiar
`d δ + δ ∘ δ = 0`
(`MathlibExt.DGSource.DGTwistedObject.dgDifferential_twist_add_negOnePow_smul_dgComp_eq_zero`).

The twisted objects form a differential graded category `MathlibExt.DGSource.DGTwistedObject R C`.  A morphism
`(X, δ_X) ⟶ (Y, δ_Y)` of degree `n` is a morphism `f : X ⟶ Y` of degree `n` in `C`, composition
and identities are those of `C`, and the differential is twisted:

`D f = d f + (-1)^n • dgComp f δ_Y - dgComp δ_X f`.

In Keller's order this is `D f = d f + δ_Y ∘ f - (-1)^n • f ∘ δ_X`.  The twisted differential
squares to zero exactly because of the Maurer–Cartan equations of `δ_X` and `δ_Y`: expanding
`D (D f)` with the Leibniz rule and associativity leaves
`dgComp f (d δ_Y - dgComp δ_Y δ_Y) - dgComp (d δ_X - dgComp δ_X δ_X) f`.  The Leibniz rule for `D`
holds for arbitrary degree-one endomorphisms, by associativity alone.

Twisted objects are the formal analogue of perturbing the differential of a complex by a
degree-one endomorphism.  Applied to the additive
closure of the shift closure of `C`, whose objects are formal sums `⊕ᵢ Xᵢ[rᵢ]`, the twisted
objects with strictly upper-triangular twisting matrix are the one-sided twisted complexes of
Bondal and Kapranov, which form the pretriangulated envelope of `C`.

Every object `X` of `C` is a twisted object with zero twist, and `X ↦ (X, 0)` is a DG functor
`MathlibExt.DGSource.DGTwistedObject.embedding` which is an isomorphism on Hom complexes.  A DG functor
`F : C ⥤ D` preserves the Maurer–Cartan equation, so it induces a DG functor
`F.mapDGTwistedObject` sending `(X, δ)` to `(F X, F δ)`.

## Main definitions

* `MathlibExt.DGSource.DGTwistedObject`: an object with a degree-one endomorphism satisfying the
  Maurer–Cartan equation.
* `MathlibExt.DGSource.DGTwistedObject.homComplexData`: the explicit Hom-complex data of twisted objects,
  with the twisted differential.
* `MathlibExt.DGSource.DGTwistedObject.dgHomEquiv`: degree-`n` morphisms of twisted objects are degree-`n`
  morphisms of the underlying objects.
* `MathlibExt.DGSource.DGTwistedObject.embedding`: the DG functor `X ↦ (X, 0)`.
* `CategoryTheory.EnrichedFunctor.mapDGTwistedObject`: the DG functor `(X, δ) ↦ (F X, F δ)`
  induced by a DG functor `F`.

## Main results

* `MathlibExt.DGSource.DGTwistedObject.dgHomEquiv_dgDifferential`: the differential is the twisted
  differential `d f + (-1)^n • dgComp f δ_Y - dgComp δ_X f`.
* `MathlibExt.DGSource.DGTwistedObject.dgHomEquiv_dgComp` and `MathlibExt.DGSource.DGTwistedObject.dgHomEquiv_dgId`:
  composition and identities are those of `C`.
* `MathlibExt.DGSource.DGTwistedObject.isIso_embedding_map`: the embedding is an isomorphism on Hom
  complexes.

## References

* A. I. Bondal and M. M. Kapranov, *Enhanced triangulated categories*, Section 1.
* V. Drinfeld, *DG quotients of DG categories*, Section 2.4.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 7.6, for the twisting
  equation `d δ + δ ∘ δ = 0` in Keller's order.
-/

public section

open CategoryTheory HomologicalComplex

namespace MathlibExt.DGSource

universe v u

/-- A **twisted object** of a differential graded category: an object `obj` with a degree-one
endomorphism `twist` satisfying the Maurer–Cartan equation `d δ = dgComp δ δ`, which in Keller's
order is `d δ + δ ∘ δ = 0`.  The twisted objects form a differential graded category whose Hom
complexes carry the twisted differential; see `MathlibExt.DGSource.DGTwistedObject.homComplexData`. -/
structure DGTwistedObject (R : Type v) [CommRing R] (C : Type u) [DGCategory R C] where
  /-- The underlying object. -/
  obj : C
  /-- The twisting endomorphism `δ`, of degree one. -/
  twist : DGHom R 1 obj obj
  /-- The Maurer–Cartan equation `d δ = dgComp δ δ`, in Mathlib's enriched factor order. -/
  dgDifferential_twist : dgDifferential R 1 twist = dgComp R twist twist rfl

namespace DGTwistedObject

attribute [simp] dgDifferential_twist

variable (R : Type v) [CommRing R] {C : Type u} [DGCategory R C]

/-- **The Maurer–Cartan equation in Keller's order**: `d δ + δ ∘ δ = 0`, where the
Keller-ordered composite is `δ ∘ δ = (-1)^(1 * 1) • dgComp δ δ`. -/
theorem dgDifferential_twist_add_negOnePow_smul_dgComp_eq_zero (X : DGTwistedObject R C) :
    dgDifferential R 1 X.twist + ((1 : ℤ) * 1).negOnePow • dgComp R X.twist X.twist rfl = 0 := by
  rw [dgDifferential_twist]
  simp

/-! ### The twisted differential -/

/-- The twisted differential `D f = d f + (-1)^n • dgComp f δ_Y - dgComp δ_X f` on morphisms
`X ⟶ Y` of degree `n`. -/
private noncomputable def twistedDifferential (X Y : DGTwistedObject R C) (n : ℤ) :
    DGHom R n X.obj Y.obj →ₗ[R] DGHom R (n + 1) X.obj Y.obj where
  toFun f := dgDifferential R n f + n.negOnePow • dgComp R f Y.twist rfl -
    dgComp R X.twist f (add_comm 1 n)
  map_add' f g := by
    simp only [map_add, add_dgComp, dgComp_add, smul_add]
    abel
  map_smul' r f := by
    simp only [map_smul, smul_dgComp, dgComp_smul, smul_sub, smul_add, RingHom.id_apply]
    rw [smul_comm]

private theorem twistedDifferential_apply {X Y : DGTwistedObject R C} (n : ℤ)
    (f : DGHom R n X.obj Y.obj) :
    twistedDifferential R X Y n f = dgDifferential R n f +
      n.negOnePow • dgComp R f Y.twist rfl - dgComp R X.twist f (add_comm 1 n) :=
  (rfl)

/-- The twisted differential squares to zero: after the Leibniz rule and associativity, what
remains is the Maurer–Cartan defect `d δ - dgComp δ δ` of the two twists, composed with `f`. -/
private theorem twistedDifferential_twistedDifferential {X Y : DGTwistedObject R C} (n : ℤ)
    (f : DGHom R n X.obj Y.obj) :
    twistedDifferential R X Y (n + 1) (twistedDifferential R X Y n f) = 0 := by
  simp only [twistedDifferential_apply, sub_eq_add_neg, map_add, map_neg, map_zsmul_unit,
    dgDifferential_dgComp, dgDifferential_dgDifferential, dgDifferential_twist]
  rw [dgComp_assoc R f Y.twist Y.twist rfl rfl rfl,
    ← dgComp_assoc R X.twist X.twist f rfl (add_comm 1 n) (by omega),
    ← dgComp_assoc R X.twist f Y.twist (add_comm 1 n) rfl (by omega)]
  simp only [Int.negOnePow_succ, Int.negOnePow_one, Units.neg_smul, smul_add, smul_neg, smul_smul,
    Int.units_mul_self, one_smul]
  abel

/-- The Leibniz rule for the twisted differential, which holds by associativity alone. -/
private theorem twistedDifferential_dgComp {X Y Z : DGTwistedObject R C} {p q n : ℤ}
    (h : p + q = n) (f : DGHom R p X.obj Y.obj) (g : DGHom R q Y.obj Z.obj) :
    twistedDifferential R X Z n (dgComp R f g h) =
      dgComp R (twistedDifferential R X Y p f) g (by omega) +
        p.negOnePow • dgComp R f (twistedDifferential R Y Z q g) (by omega) := by
  subst h
  simp only [twistedDifferential_apply, sub_eq_add_neg, add_dgComp, neg_dgComp, units_smul_dgComp,
    dgComp_add, dgComp_neg, dgComp_units_smul, dgDifferential_dgComp]
  rw [dgComp_assoc R f g Z.twist rfl rfl (by omega), dgComp_assoc R X.twist f g (add_comm 1 p) rfl
      (by omega), dgComp_assoc R f Y.twist g rfl (add_comm 1 q) (by omega)]
  simp only [smul_add, smul_neg, smul_smul, ← Int.negOnePow_add]
  abel

/-! ### The Hom-complex data -/

/-- The Hom complex `Hom((X, δ_X), (Y, δ_Y))`: the graded module of morphisms `X ⟶ Y` of `C`,
with the twisted differential. -/
private noncomputable def homComplex (X Y : DGTwistedObject R C) :
    CochainComplex (ModuleCat.{v} R) ℤ :=
  CochainComplex.of (fun n ↦ (dgHomComplex R X.obj Y.obj).X n)
    (fun n ↦ ModuleCat.ofHom (twistedDifferential R X Y n))
    (fun n ↦ by
      ext f
      exact twistedDifferential_twistedDifferential R n f)

private theorem homComplex_d (X Y : DGTwistedObject R C) (n : ℤ) :
    ((homComplex R X Y).d n (n + 1)).hom = twistedDifferential R X Y n := by
  simp only [homComplex, CochainComplex.of_d, ModuleCat.hom_ofHom]
  -- The two sides differ only in writing the degree components as `ModuleCat.of R _`.
  rfl

/-- Composition of twisted objects: the composition of `C` on the underlying morphisms. -/
private noncomputable def comp {X Y Z : DGTwistedObject R C} (p q n : ℤ) (h : p + q = n) :
    (homComplex R X Y).X p →ₗ[R] (homComplex R Y Z).X q →ₗ[R] (homComplex R X Z).X n :=
  (dgCategoryData R C).comp (X := X.obj) (Y := Y.obj) (Z := Z.obj) p q n h

private theorem comp_apply {X Y Z : DGTwistedObject R C} (p q n : ℤ) (h : p + q = n)
    (f : (homComplex R X Y).X p) (g : (homComplex R Y Z).X q) :
    comp R p q n h f g = dgComp R (X := X.obj) (Y := Y.obj) (Z := Z.obj) f g h :=
  (rfl)

/-- The **explicit Hom-complex data of twisted objects**: the morphisms of `C` with the twisted
differential `d f + (-1)^n • dgComp f δ_Y - dgComp δ_X f`, and the composition and identities of
`C`. -/
noncomputable def homComplexData : DGCategoryData R (DGTwistedObject R C) where
  hom := homComplex R
  comp := comp R
  id X := dgId R X.obj
  d_comp {X Y Z p q n} h f g := by
    simp only [homComplex_d, comp_apply]
    exact twistedDifferential_dgComp R h f g
  comp_assoc hpq hqr h f g k := by
    simp only [comp_apply]
    exact dgComp_assoc R f g k hpq hqr h
  id_comp g := (comp_apply R _ _ _ _ _ g).trans (dgId_dgComp R g)
  comp_id f := (comp_apply R _ _ _ _ f _).trans (dgComp_dgId R f)

/-- The differential graded category of **twisted objects** of a differential graded category,
with the twisted differential on Hom complexes. -/
noncomputable instance : DGCategory R (DGTwistedObject R C) :=
  (homComplexData R).toDGCategory

/-! ### Morphisms, differential, composition and identity -/

/-- A morphism `(X, δ_X) ⟶ (Y, δ_Y)` of degree `n` of twisted objects is a morphism `X ⟶ Y` of
degree `n` in `C`. -/
noncomputable def dgHomEquiv (X Y : DGTwistedObject R C) (n : ℤ) :
    DGHom R n X Y ≃ₗ[R] DGHom R n X.obj Y.obj :=
  LinearEquiv.refl R _

/-- **The twisted differential**: the differential of a degree-`n` morphism of twisted objects
is `d f + (-1)^n • dgComp f δ_Y - dgComp δ_X f`. -/
@[simp↓]
theorem dgHomEquiv_dgDifferential {X Y : DGTwistedObject R C} (n : ℤ) (f : DGHom R n X Y) :
    dgHomEquiv R X Y (n + 1) (dgDifferential R n f) =
      dgDifferential R n (dgHomEquiv R X Y n f) +
        n.negOnePow • dgComp R (dgHomEquiv R X Y n f) Y.twist rfl -
          dgComp R X.twist (dgHomEquiv R X Y n f) (add_comm 1 n) :=
  ((homComplexData R).dgDifferential_toDGCategory n f).trans
    (LinearMap.congr_fun (homComplex_d R X Y n) f)

/-- Composition of twisted objects is the composition of `C`. -/
@[simp↓]
theorem dgHomEquiv_dgComp {X Y Z : DGTwistedObject R C} {p q n : ℤ} (f : DGHom R p X Y)
    (g : DGHom R q Y Z) (h : p + q = n) :
    dgHomEquiv R X Z n (dgComp R f g h) =
      dgComp R (dgHomEquiv R X Y p f) (dgHomEquiv R Y Z q g) h :=
  ((homComplexData R).dgComp_toDGCategory f g h).trans (comp_apply R p q n h f g)

/-- The identity of a twisted object is the identity of its underlying object. -/
@[simp↓]
theorem dgHomEquiv_dgId (X : DGTwistedObject R C) : dgHomEquiv R X X 0 (dgId R X) = dgId R X.obj :=
  (homComplexData R).dgId_toDGCategory X

/-! ### The embedding `X ↦ (X, 0)` -/

/-- An object of `C` with the zero twist, which satisfies the Maurer–Cartan equation since both
sides vanish. -/
-- This is reducible so that `(ofObj R X).obj` is reducibly `X`: the morphisms of the embedding
-- `X ↦ (X, 0)` are then literally the morphisms of `C`.
abbrev ofObj (X : C) : DGTwistedObject R C where
  obj := X
  twist := 0
  dgDifferential_twist := by simp

/-- A twisted object with zero twist is its underlying object with the zero twist. -/
theorem eq_ofObj_of_twist_eq_zero {X : DGTwistedObject R C} (h : X.twist = 0) :
    X = ofObj R X.obj := by
  obtain ⟨obj, twist, _⟩ := X
  rw [DGTwistedObject.mk.injEq]
  exact ⟨rfl, heq_of_eq h⟩

/-- The action of the embedding on morphisms of degree `n`: a degree-`n` morphism `X ⟶ Y` of `C`
is a degree-`n` morphism `(X, 0) ⟶ (Y, 0)` of twisted objects. -/
noncomputable def embeddingHomEquiv (X Y : C) (n : ℤ) :
    DGHom R n X Y ≃ₗ[R] DGHom R n (ofObj R X) (ofObj R Y) :=
  (dgHomEquiv R (ofObj R X) (ofObj R Y) n).symm

/-- The embedding does not change the underlying morphism. -/
@[simp]
theorem dgHomEquiv_embeddingHomEquiv {X Y : C} {n : ℤ} (f : DGHom R n X Y) :
    dgHomEquiv R (ofObj R X) (ofObj R Y) n (embeddingHomEquiv R X Y n f) = f :=
  (rfl)

/-- With zero twists, the twisted differential is the differential of `C`. -/
theorem embeddingHomEquiv_dgDifferential {X Y : C} (n : ℤ) (f : DGHom R n X Y) :
    embeddingHomEquiv R X Y (n + 1) (dgDifferential R n f) =
      dgDifferential R n (embeddingHomEquiv R X Y n f) :=
  (dgHomEquiv R _ _ (n + 1)).injective <| by
    rw [dgHomEquiv_dgDifferential, dgHomEquiv_embeddingHomEquiv, dgHomEquiv_embeddingHomEquiv]
    simp

/-- The DG functor from a differential graded category to its twisted objects sending `X` to the
twisted object `(X, 0)`. -/
-- The body is exposed so that `(embedding R).obj X` is definitionally `ofObj R X`, as for
-- `CategoryTheory.EnrichedFunctor.ofDGMap`.
@[expose]
noncomputable def embedding :
    EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C (DGTwistedObject R C) :=
  EnrichedFunctor.ofDGMap (ofObj R) (fun {X Y} n ↦ (embeddingHomEquiv R X Y n).toLinearMap)
    (fun n f ↦ embeddingHomEquiv_dgDifferential R n f)
    (fun X ↦ (dgHomEquiv R _ _ 0).injective <| by
      rw [LinearEquiv.coe_coe, dgHomEquiv_embeddingHomEquiv, dgHomEquiv_dgId])
    (fun {X Y Z p q n} f g h ↦ (dgHomEquiv R _ _ n).injective <| by
      rw [LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.coe_coe, dgHomEquiv_dgComp,
        dgHomEquiv_embeddingHomEquiv, dgHomEquiv_embeddingHomEquiv, dgHomEquiv_embeddingHomEquiv])

/-- The embedding sends `X` to the twisted object `(X, 0)`. -/
@[simp]
theorem embedding_obj (X : C) : (embedding R).obj X = ofObj R X :=
  (rfl)

/-- The embedding acts on morphisms by `MathlibExt.DGSource.DGTwistedObject.embeddingHomEquiv`. -/
@[simp]
theorem dgMap_embedding {X Y : C} {n : ℤ} (f : DGHom R n X Y) :
    (embedding R).dgMap n f = embeddingHomEquiv R X Y n f :=
  (EnrichedFunctor.dgMap_apply _ f).trans rfl

/-- The embedding is an isomorphism on Hom complexes: `C` is a full DG subcategory of its twisted
objects. -/
instance isIso_embedding_map (X Y : C) : IsIso ((embedding R).map X Y) :=
  have (n : ℤ) : IsIso (((embedding R).map X Y).f n) :=
    (embeddingHomEquiv R X Y n).toModuleIso.isIso_hom
  HomologicalComplex.Hom.isIso_of_components _

end DGTwistedObject

end MathlibExt.DGSource

namespace CategoryTheory.EnrichedFunctor

open MathlibExt.DGSource DGTwistedObject

universe v u u₂

/-! ### Functoriality -/

variable {R : Type v} [CommRing R] {C : Type u} {D : Type u₂} [DGCategory R C] [DGCategory R D]
  (F : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D)

/-- The image `(F X, F δ)` of a twisted object under a DG functor: `F` preserves the
Maurer–Cartan equation since it commutes with the differential and with composition. -/
-- This is reducible so that `(F.mapDGTwistedObjectObj X).obj` is reducibly `F.obj X.obj`: the
-- morphisms of the image are then literally the morphisms of `D` between the images.
noncomputable abbrev mapDGTwistedObjectObj (X : DGTwistedObject R C) : DGTwistedObject R D where
  obj := F.obj X.obj
  twist := F.dgMap 1 X.twist
  dgDifferential_twist := by
    rw [← EnrichedFunctor.dgMap_dgDifferential, dgDifferential_twist, EnrichedFunctor.dgMap_dgComp]

/-- The action of a DG functor on morphisms of twisted objects of degree `n`: its action on the
underlying morphisms. -/
noncomputable def mapDGTwistedObjectHom (X Y : DGTwistedObject R C) (n : ℤ) :
    DGHom R n X Y →ₗ[R] DGHom R n (F.mapDGTwistedObjectObj X) (F.mapDGTwistedObjectObj Y) :=
  (dgHomEquiv R _ _ n).symm.toLinearMap ∘ₗ F.dgMap n ∘ₗ (dgHomEquiv R X Y n).toLinearMap

/-- The underlying morphism of the image of a morphism is the image of its underlying
morphism. -/
@[simp]
theorem dgHomEquiv_mapDGTwistedObjectHom {X Y : DGTwistedObject R C} {n : ℤ}
    (f : DGHom R n X Y) :
    dgHomEquiv R _ _ n (F.mapDGTwistedObjectHom X Y n f) = F.dgMap n (dgHomEquiv R X Y n f) := by
  simp [mapDGTwistedObjectHom]

/-- The DG functor between twisted objects induced by a DG functor `F`, sending `(X, δ)` to
`(F X, F δ)` and acting by `F` on the underlying morphisms. -/
-- This is reducible, with the object map given explicitly, so that the image of a twisted object
-- is reducibly `F.mapDGTwistedObjectObj X`, whose underlying object is reducibly `F.obj X.obj`.
noncomputable abbrev mapDGTwistedObject :
    EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) (DGTwistedObject R C)
      (DGTwistedObject R D) :=
  letI G := EnrichedFunctor.ofDGMap F.mapDGTwistedObjectObj
    (fun {X Y} n ↦ F.mapDGTwistedObjectHom X Y n)
    (fun n f ↦ (dgHomEquiv R _ _ (n + 1)).injective <| by
      rw [dgHomEquiv_mapDGTwistedObjectHom, dgHomEquiv_dgDifferential, dgHomEquiv_dgDifferential,
        dgHomEquiv_mapDGTwistedObjectHom, map_sub, map_add, map_zsmul_unit,
        EnrichedFunctor.dgMap_dgDifferential, EnrichedFunctor.dgMap_dgComp,
        EnrichedFunctor.dgMap_dgComp])
    (fun X ↦ (dgHomEquiv R _ _ 0).injective <| by
      rw [dgHomEquiv_mapDGTwistedObjectHom, dgHomEquiv_dgId, dgHomEquiv_dgId,
        EnrichedFunctor.dgMap_dgId])
    (fun f g h ↦ (dgHomEquiv R _ _ _).injective <| by
      rw [dgHomEquiv_mapDGTwistedObjectHom, dgHomEquiv_dgComp, dgHomEquiv_dgComp,
        dgHomEquiv_mapDGTwistedObjectHom, dgHomEquiv_mapDGTwistedObjectHom,
        EnrichedFunctor.dgMap_dgComp])
  { obj := F.mapDGTwistedObjectObj
    map := G.map
    map_id := G.map_id
    map_comp := G.map_comp }

/-- The induced DG functor acts on morphisms by
`CategoryTheory.EnrichedFunctor.mapDGTwistedObjectHom`. -/
@[simp]
theorem dgMap_mapDGTwistedObject {X Y : DGTwistedObject R C} {n : ℤ} (f : DGHom R n X Y) :
    F.mapDGTwistedObject.dgMap n f = F.mapDGTwistedObjectHom X Y n f :=
  (EnrichedFunctor.dgMap_apply _ f).trans rfl

/-- The underlying morphism of the image of a morphism under the induced DG functor is the image of
its underlying morphism. -/
theorem dgHomEquiv_dgMap_mapDGTwistedObject {X Y : DGTwistedObject R C} {n : ℤ}
    (f : DGHom R n X Y) :
    dgHomEquiv R _ _ n (F.mapDGTwistedObject.dgMap n f) = F.dgMap n (dgHomEquiv R X Y n f) := by
  rw [dgMap_mapDGTwistedObject, dgHomEquiv_mapDGTwistedObjectHom]

end CategoryTheory.EnrichedFunctor
