/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
This completed proof port retains the original Apache 2.0 license and author credit.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/CategoryTheory/DG/AdditiveClosure/Basic.lean
Original license: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
Modifications: only module/namespace paths are adapted for Atlas.
Mathematical operations, hypotheses and proof bodies are retained.
-/

public import MathlibExt.CategoryTheory.DGSource.DGFunctor
public import MathlibExt.CategoryTheory.DGSource.DGFunctorHomComplex

/-!
# The additive closure of a differential graded category

For a differential graded category `C`, the additive closure `MathlibExt.DGSource.DGAdditiveClosure C` adjoins
formal finite direct sums `⊕ᵢ Xᵢ` of objects of `C`.  An object is a finite family of objects of
`C`, and the Hom complex between two of them is the complex of matrices of morphisms,

`Hom(⊕ᵢ Xᵢ, ⊕ⱼ Yⱼ) = ∏ᵢ ∏ⱼ Hom(Xᵢ, Yⱼ)`,

with the differential applied entrywise.  Composition is matrix multiplication,
`(f ≫ g)ᵢₖ = ∑ⱼ fᵢⱼ ≫ gⱼₖ`, in Mathlib's enriched factor order, and the identity is the diagonal
matrix of identities.  Since composition in `C` is bilinear, the Leibniz rule, associativity and
the unit laws hold entrywise; no Koszul sign is introduced.  This is the DG analogue of Mathlib's
`CategoryTheory.Mat_`.

Every object of `C` is a one-term sum, and `X ↦ X` is a DG functor
`MathlibExt.DGSource.DGAdditiveClosure.embedding` which is an isomorphism on Hom complexes.  Every object
`M = ⊕ᵢ Xᵢ` of the additive closure is the direct sum of its summands in the DG sense: the
inclusions `MathlibExt.DGSource.DGAdditiveClosure.single` and projections `MathlibExt.DGSource.DGAdditiveClosure.proj`
are closed of degree zero, `proj j ∘ single i` is the identity for `i = j` and zero otherwise, and
`∑ᵢ single i ∘ proj i` is the identity of `M`.

A DG functor `F : C ⥤ D` induces a DG functor `F.mapDGAdditiveClosure` between the additive
closures, sending `⊕ᵢ Xᵢ` to `⊕ᵢ F Xᵢ` and applying `F` to every matrix entry.

The additive closure of the shift closure is the home of the underlying objects `⊕ᵢ Xᵢ[rᵢ]` of
the one-sided twisted complexes of Bondal and Kapranov, whose twisting differential is a
degree-one matrix of this kind.

## Main definitions

* `MathlibExt.DGSource.DGAdditiveClosure`: the objects `⊕ᵢ Xᵢ` of the additive closure.
* `MathlibExt.DGSource.DGAdditiveClosure.homComplexData`: its explicit Hom-complex data.
* `MathlibExt.DGSource.DGAdditiveClosure.dgHomEquiv`: degree-`n` morphisms `⊕ᵢ Xᵢ ⟶ ⊕ⱼ Yⱼ` are matrices of
  degree-`n` morphisms `Xᵢ ⟶ Yⱼ`.
* `MathlibExt.DGSource.DGAdditiveClosure.embedding`: the DG functor sending `X` to the one-term sum.
* `MathlibExt.DGSource.DGAdditiveClosure.single`, `MathlibExt.DGSource.DGAdditiveClosure.proj`: the inclusion of and the
  projection to a summand.
* `MathlibExt.DGSource.DGAdditiveClosure.sum`: the direct sum `M ⊕ N` of two objects, the concatenation of
  their families of summands.
* `CategoryTheory.EnrichedFunctor.mapDGAdditiveClosure`: the DG functor between additive closures
  induced by a DG functor, applied summandwise and entrywise.

## Main results

* `MathlibExt.DGSource.DGAdditiveClosure.dgHomEquiv_dgDifferential`: the differential is entrywise.
* `MathlibExt.DGSource.DGAdditiveClosure.dgHomEquiv_dgComp`: composition is matrix multiplication.
* `MathlibExt.DGSource.DGAdditiveClosure.dgHomEquiv_dgId`: the identity is the diagonal matrix of identities.
* `MathlibExt.DGSource.DGAdditiveClosure.isIso_embedding_map`: the embedding is an isomorphism on Hom
  complexes.
* `MathlibExt.DGSource.DGAdditiveClosure.dgComp_single_proj_self`,
  `MathlibExt.DGSource.DGAdditiveClosure.dgComp_single_proj_of_ne` and
  `MathlibExt.DGSource.DGAdditiveClosure.sum_dgComp_proj_single`: the biproduct equations.

## References

* A. I. Bondal and M. M. Kapranov, *Enhanced triangulated categories*, Section 1.
* V. Drinfeld, *DG quotients of DG categories*, Section 2.4.
* Kim Morrison and the Mathlib contributors, `Mathlib.CategoryTheory.Preadditive.Mat`, for the
  matrix category `CategoryTheory.Mat_` of a preadditive category, whose object structure and
  matrix composition are followed here.
-/

public section

open CategoryTheory HomologicalComplex

namespace MathlibExt.DGSource

universe v u

/-- The objects of the **additive closure** of a differential graded category on the objects
`C`: a finite family `X : ι → C`, standing for the formal direct sum `⊕ᵢ Xᵢ`.  The Hom complexes
are the complexes of matrices of morphisms; see `MathlibExt.DGSource.DGAdditiveClosure.homComplexData`. -/
structure DGAdditiveClosure (C : Type u) where
  /-- The index type of the summands. -/
  ι : Type
  [fintype : Fintype ι]
  /-- The summands. -/
  X : ι → C

attribute [instance] DGAdditiveClosure.fintype

namespace DGAdditiveClosure

variable (R : Type v) [CommRing R] {C : Type u} [DGCategory R C]

/-! ### The Hom-complex data -/

/-- The Hom complex `Hom(⊕ᵢ Xᵢ, ⊕ⱼ Yⱼ) = ∏ᵢ ∏ⱼ Hom(Xᵢ, Yⱼ)` of the additive closure, with the
entrywise differential. -/
private noncomputable def homComplex (M N : DGAdditiveClosure C) :
    CochainComplex (ModuleCat.{v} R) ℤ where
  X n := ModuleCat.of R (∀ i j, DGHom R n (M.X i) (N.X j))
  d n m := ModuleCat.ofHom <| LinearMap.piMap fun i ↦ LinearMap.piMap fun j ↦
    ((dgHomComplex R (M.X i) (N.X j)).d n m).hom
  shape n m h := by
    ext f i j
    simp [(dgHomComplex R (M.X i) (N.X j)).shape n m h]
    -- The zero of `ModuleCat.of R _` is the zero function only after unfolding the carrier.
    rfl
  d_comp_d' n m l _ _ := by
    ext f i j
    simp [← ModuleCat.comp_apply]
    -- As for `shape`, the zero of the carrier is the zero function after unfolding.
    rfl

/-- Composition in the additive closure: matrix multiplication of matrices of homogeneous
morphisms. -/
private noncomputable def comp {M N K : DGAdditiveClosure C} (p q n : ℤ) (h : p + q = n) :
    (∀ i j, DGHom R p (M.X i) (N.X j)) →ₗ[R] (∀ j k, DGHom R q (N.X j) (K.X k)) →ₗ[R]
      ∀ i k, DGHom R n (M.X i) (K.X k) :=
  LinearMap.mk₂ R (fun f g i k ↦ ∑ j, dgComp R (f i j) (g j k) h)
    (fun f f' g ↦ by
      funext i k
      simp [Finset.sum_add_distrib])
    (fun r f g ↦ by
      funext i k
      simp [Finset.smul_sum])
    (fun f g g' ↦ by
      funext i k
      simp [Finset.sum_add_distrib])
    (fun r f g ↦ by
      funext i k
      simp [Finset.smul_sum])

private theorem comp_apply {M N K : DGAdditiveClosure C} (p q n : ℤ) (h : p + q = n)
    (f : ∀ i j, DGHom R p (M.X i) (N.X j)) (g : ∀ j k, DGHom R q (N.X j) (K.X k)) (i : M.ι)
    (k : K.ι) :
    comp R p q n h f g i k = ∑ j, dgComp R (f i j) (g j k) h :=
  (rfl)

/-- The Leibniz rule for matrix multiplication, entrywise. -/
private theorem dgDifferential_comp_apply {M N K : DGAdditiveClosure C} {p q n : ℤ}
    (h : p + q = n) (f : ∀ i j, DGHom R p (M.X i) (N.X j)) (g : ∀ j k, DGHom R q (N.X j) (K.X k))
    (i : M.ι) (k : K.ι) :
    dgDifferential R n (comp R p q n h f g i k) =
      comp R (p + 1) q (n + 1) (by omega) (fun i j ↦ dgDifferential R p (f i j)) g i k +
        p.negOnePow • comp R p (q + 1) (n + 1) (by omega) f
          (fun j k ↦ dgDifferential R q (g j k)) i k := by
  simp only [comp_apply, map_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ ↦ dgDifferential_dgComp R (f i j) (g j k) h

open scoped Classical in
/-- The identity of `⊕ᵢ Xᵢ`: the diagonal matrix of identities. -/
private noncomputable def id (M : DGAdditiveClosure C) : ∀ i j, DGHom R 0 (M.X i) (M.X j) :=
  fun i ↦ Pi.single i (dgId R (M.X i))

open scoped Classical in
private theorem id_apply (M : DGAdditiveClosure C) (i j : M.ι) :
    id R M i j = Pi.single (M := fun j ↦ DGHom R 0 (M.X i) (M.X j)) i (dgId R (M.X i)) j :=
  (rfl)

private theorem comp_assoc' {W X Y Z : DGAdditiveClosure C} {p q r pq qr n : ℤ}
    (hpq : p + q = pq) (hqr : q + r = qr) (h : p + q + r = n)
    (f : ∀ i j, DGHom R p (W.X i) (X.X j)) (g : ∀ j k, DGHom R q (X.X j) (Y.X k))
    (k : ∀ k l, DGHom R r (Y.X k) (Z.X l)) :
    comp R pq r n (by omega) (comp R p q pq hpq f g) k =
      comp R p qr n (by omega) f (comp R q r qr hqr g k) := by
  funext i m
  simp only [comp_apply, sum_dgComp, dgComp_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun j _ ↦
    dgComp_assoc R (f i l) (g l j) (k j m) hpq hqr h

private theorem id_comp' {M N : DGAdditiveClosure C} {q : ℤ}
    (g : ∀ i j, DGHom R q (M.X i) (N.X j)) : comp R 0 q q (zero_add q) (id R M) g = g := by
  classical
  funext i k
  rw [comp_apply, Finset.sum_eq_single i]
  · rw [id_apply, Pi.single_eq_same, dgId_dgComp]
  · intro j _ hj
    rw [id_apply, Pi.single_eq_of_ne hj, zero_dgComp]
  · simp

private theorem comp_id' {M N : DGAdditiveClosure C} {p : ℤ}
    (f : ∀ i j, DGHom R p (M.X i) (N.X j)) : comp R p 0 p (add_zero p) f (id R N) = f := by
  classical
  funext i k
  rw [comp_apply, Finset.sum_eq_single k]
  · rw [id_apply, Pi.single_eq_same, dgComp_dgId]
  · intro j _ hj
    rw [id_apply, Pi.single_eq_of_ne (Ne.symm hj), dgComp_zero]
  · simp

/-- The **explicit Hom-complex data of the additive closure**: matrices of morphisms with the
entrywise differential, matrix multiplication as composition, and the diagonal matrix of
identities as identity. -/
noncomputable def homComplexData : DGCategoryData R (DGAdditiveClosure C) where
  hom := homComplex R
  comp := comp R
  id := id R
  -- The laws hold for the underlying matrices: the module operations of `ModuleCat.of R _` are
  -- the pointwise ones after unfolding the carrier.
  d_comp h f g := funext fun i ↦ funext fun k ↦ dgDifferential_comp_apply R h f g i k
  comp_assoc hpq hqr h f g k := comp_assoc' R hpq hqr h f g k
  id_comp g := id_comp' R g
  comp_id f := comp_id' R f

/-- The **additive closure** of a differential graded category: formal finite direct sums
`⊕ᵢ Xᵢ`, with the complexes of matrices of morphisms as Hom complexes. -/
noncomputable instance : DGCategory R (DGAdditiveClosure C) :=
  (homComplexData R).toDGCategory

/-! ### Morphisms, differential, composition and identity -/

/-- A morphism `⊕ᵢ Xᵢ ⟶ ⊕ⱼ Yⱼ` of degree `n` in the additive closure is a matrix of morphisms
`Xᵢ ⟶ Yⱼ` of degree `n` in `C`. -/
noncomputable def dgHomEquiv (M N : DGAdditiveClosure C) (n : ℤ) :
    DGHom R n M N ≃ₗ[R] ∀ i j, DGHom R n (M.X i) (N.X j) :=
  LinearEquiv.refl R _

/-- Morphisms of the additive closure are determined by their matrix entries. -/
theorem dgHom_ext {M N : DGAdditiveClosure C} {n : ℤ} {f g : DGHom R n M N}
    (h : ∀ i j, dgHomEquiv R M N n f i j = dgHomEquiv R M N n g i j) : f = g :=
  (dgHomEquiv R M N n).injective (funext fun i ↦ funext (h i))

/-- The differential of the additive closure is the differential of `C`, applied entrywise. -/
@[simp↓]
theorem dgHomEquiv_dgDifferential {M N : DGAdditiveClosure C} (n : ℤ) (f : DGHom R n M N)
    (i : M.ι) (j : N.ι) :
    dgHomEquiv R M N (n + 1) (dgDifferential R n f) i j =
      dgDifferential R n (dgHomEquiv R M N n f i j) :=
  congrFun (congrFun ((homComplexData R).dgDifferential_toDGCategory n f) i) j

/-- **Composition in the additive closure is matrix multiplication**: the `(i, k)` entry of `f`
followed by `g` is `∑ⱼ fᵢⱼ` followed by `gⱼₖ`. -/
@[simp↓]
theorem dgHomEquiv_dgComp {M N K : DGAdditiveClosure C} {p q n : ℤ} (f : DGHom R p M N)
    (g : DGHom R q N K) (h : p + q = n) (i : M.ι) (k : K.ι) :
    dgHomEquiv R M K n (dgComp R f g h) i k =
      ∑ j, dgComp R (dgHomEquiv R M N p f i j) (dgHomEquiv R N K q g j k) h :=
  congrFun (congrFun ((homComplexData R).dgComp_toDGCategory f g h) i) k

/-- **The identity of the additive closure is the diagonal matrix of identities.** -/
theorem dgHomEquiv_dgId (M : DGAdditiveClosure C) [DecidableEq M.ι] (i : M.ι) :
    dgHomEquiv R M M 0 (dgId R M) i = Pi.single i (dgId R (M.X i)) := by
  have e : dgHomEquiv R M M 0 (dgId R M) = id R M := (homComplexData R).dgId_toDGCategory M
  ext j
  rw [e, id_apply]
  congr

/-- The diagonal entries of the identity are identities. -/
@[simp↓]
theorem dgHomEquiv_dgId_self (M : DGAdditiveClosure C) (i : M.ι) :
    dgHomEquiv R M M 0 (dgId R M) i i = dgId R (M.X i) := by
  classical
  rw [dgHomEquiv_dgId, Pi.single_eq_same]

/-- The off-diagonal entries of the identity vanish. -/
@[simp↓]
theorem dgHomEquiv_dgId_of_ne (M : DGAdditiveClosure C) {i j : M.ι} (h : i ≠ j) :
    dgHomEquiv R M M 0 (dgId R M) i j = 0 := by
  classical
  rw [dgHomEquiv_dgId, Pi.single_eq_of_ne (Ne.symm h)]

/-! ### The embedding of `C` -/

/-- The action of the embedding on morphisms of degree `n`: a degree-`n` morphism `X ⟶ Y` of `C`
is the one-by-one matrix it fills. -/
noncomputable def embeddingHomEquiv (X Y : C) (n : ℤ) :
    DGHom R n X Y ≃ₗ[R]
      DGHom R n (⟨PUnit, fun _ ↦ X⟩ : DGAdditiveClosure C) ⟨PUnit, fun _ ↦ Y⟩ :=
  ((LinearEquiv.funUnique PUnit R _).trans (LinearEquiv.funUnique PUnit R _)).symm.trans
    (dgHomEquiv R ⟨PUnit, fun _ ↦ X⟩ ⟨PUnit, fun _ ↦ Y⟩ n).symm

/-- The one-by-one matrix filled by a morphism has that morphism as its entry. -/
@[simp]
theorem dgHomEquiv_embeddingHomEquiv {X Y : C} {n : ℤ} (f : DGHom R n X Y) (i j : PUnit) :
    dgHomEquiv R ⟨PUnit, fun _ ↦ X⟩ ⟨PUnit, fun _ ↦ Y⟩ n (embeddingHomEquiv R X Y n f) i j = f :=
  (rfl)

/-- The one-by-one matrix filled by a morphism commutes with the differential. -/
theorem embeddingHomEquiv_dgDifferential {X Y : C} (n : ℤ) (f : DGHom R n X Y) :
    embeddingHomEquiv R X Y (n + 1) (dgDifferential R n f) =
      dgDifferential R n (embeddingHomEquiv R X Y n f) :=
  dgHom_ext R fun i j ↦ by
    rw [dgHomEquiv_dgDifferential, dgHomEquiv_embeddingHomEquiv, dgHomEquiv_embeddingHomEquiv]

/-- The one-by-one matrix filled by the identity is the identity. -/
theorem embeddingHomEquiv_dgId (X : C) : embeddingHomEquiv R X X 0 (dgId R X) = dgId R _ :=
  dgHom_ext R fun i j ↦ by
    obtain rfl : i = j := Subsingleton.elim i j
    rw [dgHomEquiv_embeddingHomEquiv, dgHomEquiv_dgId_self]

/-- One-by-one matrices compose by the composition of their entries. -/
theorem embeddingHomEquiv_dgComp {X Y Z : C} {p q n : ℤ} (f : DGHom R p X Y)
    (g : DGHom R q Y Z) (h : p + q = n) :
    embeddingHomEquiv R X Z n (dgComp R f g h) =
      dgComp R (embeddingHomEquiv R X Y p f) (embeddingHomEquiv R Y Z q g) h :=
  dgHom_ext R fun i k ↦ by
    rw [dgHomEquiv_dgComp, Fintype.sum_unique, dgHomEquiv_embeddingHomEquiv,
      dgHomEquiv_embeddingHomEquiv, dgHomEquiv_embeddingHomEquiv]

/-- The DG functor from a differential graded category to its additive closure sending `X` to
the one-term sum. -/
-- The body is exposed so that `(embedding R).obj X` is definitionally the one-term sum, as for
-- `CategoryTheory.EnrichedFunctor.ofDGMap`.
@[expose]
noncomputable def embedding :
    EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C (DGAdditiveClosure C) :=
  EnrichedFunctor.ofDGMap (fun X ↦ ⟨PUnit, fun _ ↦ X⟩)
    (fun {X Y} n ↦ (embeddingHomEquiv R X Y n).toLinearMap)
    (fun n f ↦ embeddingHomEquiv_dgDifferential R n f)
    (fun X ↦ embeddingHomEquiv_dgId R X)
    (fun f g h ↦ embeddingHomEquiv_dgComp R f g h)

/-- The embedding sends `X` to the one-term sum. -/
@[simp]
theorem embedding_obj (X : C) : (embedding R).obj X = ⟨PUnit, fun _ ↦ X⟩ :=
  (rfl)

/-- The embedding acts on morphisms by `MathlibExt.DGSource.DGAdditiveClosure.embeddingHomEquiv`. -/
@[simp]
theorem dgMap_embedding {X Y : C} {n : ℤ} (f : DGHom R n X Y) :
    (embedding R).dgMap n f = embeddingHomEquiv R X Y n f :=
  (EnrichedFunctor.dgMap_apply _ f).trans rfl

/-- The embedding is an isomorphism on Hom complexes: `C` is a full DG subcategory of its
additive closure. -/
instance isIso_embedding_map (X Y : C) : IsIso ((embedding R).map X Y) :=
  have (n : ℤ) : IsIso (((embedding R).map X Y).f n) :=
    (embeddingHomEquiv R X Y n).toModuleIso.isIso_hom
  HomologicalComplex.Hom.isIso_of_components _

/-! ### Summands -/

/-- The inclusion of the summand `Xᵢ`, as the one-term sum `(embedding R).obj (M.X i)`, into
`⊕ᵢ Xᵢ`: the `i`-th row of the identity matrix. -/
noncomputable def single (M : DGAdditiveClosure C) (i : M.ι) :
    DGHom R 0 (⟨PUnit, fun _ ↦ M.X i⟩ : DGAdditiveClosure C) M :=
  (dgHomEquiv R _ M 0).symm fun _ ↦ dgHomEquiv R M M 0 (dgId R M) i

/-- The projection of `⊕ᵢ Xᵢ` onto the summand `Xᵢ`, as the one-term sum
`(embedding R).obj (M.X i)`: the `i`-th column of the identity matrix. -/
noncomputable def proj (M : DGAdditiveClosure C) (i : M.ι) :
    DGHom R 0 M (⟨PUnit, fun _ ↦ M.X i⟩ : DGAdditiveClosure C) :=
  (dgHomEquiv R M _ 0).symm fun j _ ↦ dgHomEquiv R M M 0 (dgId R M) j i

/-- The entries of the inclusion of the summand `Xᵢ` are the entries of the `i`-th row of the
identity. -/
@[simp]
theorem dgHomEquiv_single (M : DGAdditiveClosure C) (i : M.ι) (u : PUnit) (j : M.ι) :
    dgHomEquiv R _ M 0 (single R M i) u j = dgHomEquiv R M M 0 (dgId R M) i j :=
  (rfl)

/-- The entries of the projection onto the summand `Xᵢ` are the entries of the `i`-th column of
the identity. -/
@[simp]
theorem dgHomEquiv_proj (M : DGAdditiveClosure C) (i : M.ι) (j : M.ι) (u : PUnit) :
    dgHomEquiv R M _ 0 (proj R M i) j u = dgHomEquiv R M M 0 (dgId R M) j i :=
  (rfl)

/-- The entries of the identity are closed. -/
@[simp↓]
theorem dgDifferential_dgHomEquiv_dgId (M : DGAdditiveClosure C) (i j : M.ι) :
    dgDifferential R 0 (dgHomEquiv R M M 0 (dgId R M) i j) = 0 := by
  rw [← dgHomEquiv_dgDifferential, dgDifferential_dgId, map_zero, Pi.zero_apply, Pi.zero_apply]

/-- Multiplying a row of morphisms out of the summands of `M` on the left by a row of the identity
of `M` picks out one of them. -/
@[simp↓]
theorem sum_dgHomEquiv_dgId_dgComp {M : DGAdditiveClosure C} {Z : C} {q : ℤ}
    (F : ∀ j, DGHom R q (M.X j) Z) (i : M.ι) :
    ∑ j, dgComp R (dgHomEquiv R M M 0 (dgId R M) i j) (F j) (zero_add q) = F i := by
  classical
  rw [Finset.sum_eq_single i (fun j _ hj ↦ by rw [dgHomEquiv_dgId_of_ne R M (Ne.symm hj),
    zero_dgComp]) (by simp), dgHomEquiv_dgId_self, dgId_dgComp]

/-- Multiplying a column of morphisms into the summands of `M` on the right by a column of the
identity of `M` picks out one of them. -/
@[simp↓]
theorem sum_dgComp_dgHomEquiv_dgId {M : DGAdditiveClosure C} {Z : C} {p : ℤ}
    (F : ∀ j, DGHom R p Z (M.X j)) (k : M.ι) :
    ∑ j, dgComp R (F j) (dgHomEquiv R M M 0 (dgId R M) j k) (add_zero p) = F k := by
  classical
  rw [Finset.sum_eq_single k (fun j _ hj ↦ by rw [dgHomEquiv_dgId_of_ne R M hj, dgComp_zero])
    (by simp), dgHomEquiv_dgId_self, dgComp_dgId]

/- The entries of `single` and `proj` are entries of the identity of `M`, whose types agree with
the types of the entries of `single` and `proj` only after reducing the projections of the
one-term sum `⟨PUnit, fun _ ↦ M.X i⟩`.  The proofs below therefore close the entrywise goals with
`exact`, which performs that reduction. -/

/-- The inclusion of a summand is closed. -/
@[simp↓]
theorem dgDifferential_single (M : DGAdditiveClosure C) (i : M.ι) :
    dgDifferential R 0 (single R M i) = 0 :=
  dgHom_ext R fun _ j ↦ by
    rw [dgHomEquiv_dgDifferential, map_zero]
    exact dgDifferential_dgHomEquiv_dgId R M i j

/-- The projection to a summand is closed. -/
@[simp↓]
theorem dgDifferential_proj (M : DGAdditiveClosure C) (i : M.ι) :
    dgDifferential R 0 (proj R M i) = 0 :=
  dgHom_ext R fun j _ ↦ by
    rw [dgHomEquiv_dgDifferential, map_zero]
    exact dgDifferential_dgHomEquiv_dgId R M j i

/-- The inclusion of a summand followed by the projection to it is the identity. -/
@[simp↓]
theorem dgComp_single_proj_self (M : DGAdditiveClosure C) (i : M.ι) :
    dgComp R (single R M i) (proj R M i) (add_zero 0) = dgId R _ :=
  dgHom_ext R fun u u' ↦ by
    cases u
    cases u'
    rw [dgHomEquiv_dgComp, dgHomEquiv_dgId_self]
    exact (sum_dgComp_dgHomEquiv_dgId R (dgHomEquiv R M M 0 (dgId R M) i) i).trans
      (dgHomEquiv_dgId_self R M i)

/-- The inclusion of a summand followed by the projection to a different summand vanishes. -/
@[simp↓]
theorem dgComp_single_proj_of_ne (M : DGAdditiveClosure C) {i j : M.ι} (h : i ≠ j) :
    dgComp R (single R M i) (proj R M j) (add_zero 0) = 0 :=
  dgHom_ext R fun _ _ ↦ by
    rw [dgHomEquiv_dgComp, map_zero]
    exact (sum_dgComp_dgHomEquiv_dgId R (dgHomEquiv R M M 0 (dgId R M) i) j).trans
      (dgHomEquiv_dgId_of_ne R M h)

/-- **`⊕ᵢ Xᵢ` is the direct sum of its summands**: the sum over all summands of the projection
followed by the inclusion is the identity. -/
theorem sum_dgComp_proj_single (M : DGAdditiveClosure C) :
    ∑ i, dgComp R (proj R M i) (single R M i) (add_zero 0) = dgId R M :=
  dgHom_ext R fun j k ↦ by
    rw [map_sum, Finset.sum_apply, Finset.sum_apply]
    simp only [dgHomEquiv_dgComp, Fintype.sum_unique]
    exact sum_dgComp_dgHomEquiv_dgId R (dgHomEquiv R M M 0 (dgId R M) j) k

/-- If `M` has at most one summand, the projection onto the summand `Xᵢ` followed by the
inclusion of it is the identity of `M`. -/
theorem dgComp_proj_single_of_subsingleton (M : DGAdditiveClosure C) [Subsingleton M.ι]
    (i : M.ι) : dgComp R (proj R M i) (single R M i) (add_zero 0) = dgId R M :=
  (Fintype.sum_subsingleton (fun j ↦ dgComp R (proj R M j) (single R M j) (add_zero 0))
    i).symm.trans (sum_dgComp_proj_single R M)

/-! ### Restriction to a set of summands -/

/-- The identity of the sum of the summands of `M` satisfying `q` is the restriction of the
identity of `M`. -/
@[simp↓]
theorem dgHomEquiv_dgId_subtype (M : DGAdditiveClosure C) (q : M.ι → Prop) [DecidablePred q]
    (i j : {i // q i}) :
    dgHomEquiv R _ _ 0 (dgId R (⟨{i // q i}, fun i ↦ M.X i⟩ : DGAdditiveClosure C)) i j =
      dgHomEquiv R M M 0 (dgId R M) i j := by
  rcases eq_or_ne i j with rfl | h
  · rw [dgHomEquiv_dgId_self, dgHomEquiv_dgId_self]
  · rw [dgHomEquiv_dgId_of_ne R _ h, dgHomEquiv_dgId_of_ne R _ (Subtype.val_injective.ne h)]

/-! ### Binary sums -/

/-- The **direct sum** `M ⊕ N` of two objects of the additive closure: the concatenation of their
families of summands. -/
-- The family is defined by pattern matching rather than by `Sum.elim`, so that its values at
-- `Sum.inl i` and `Sum.inr j` reduce at reducible transparency: the matrix entries of morphisms
-- out of and into `M ⊕ N` are then reducibly morphisms between summands of `M` and `N`.
abbrev sum (M N : DGAdditiveClosure C) : DGAdditiveClosure C :=
  ⟨M.ι ⊕ N.ι, fun | .inl i => M.X i | .inr j => N.X j⟩

/-- The block of the identity of `M ⊕ N` on the summands of `M` is the identity of `M`. -/
@[simp↓]
theorem dgHomEquiv_dgId_sum_inl_inl (M N : DGAdditiveClosure C) (i j : M.ι) :
    dgHomEquiv R _ _ 0 (dgId R (M.sum N)) (.inl i) (.inl j) =
      dgHomEquiv R M M 0 (dgId R M) i j := by
  rcases eq_or_ne i j with rfl | h
  · rw [dgHomEquiv_dgId_self, dgHomEquiv_dgId_self]
  · rw [dgHomEquiv_dgId_of_ne R _ (Sum.inl_injective.ne h), dgHomEquiv_dgId_of_ne R _ h]

/-- The block of the identity of `M ⊕ N` from the summands of `M` to those of `N` vanishes. -/
@[simp↓]
theorem dgHomEquiv_dgId_sum_inl_inr (M N : DGAdditiveClosure C) (i : M.ι) (j : N.ι) :
    dgHomEquiv R _ _ 0 (dgId R (M.sum N)) (.inl i) (.inr j) = 0 :=
  dgHomEquiv_dgId_of_ne R _ Sum.inl_ne_inr

/-- The block of the identity of `M ⊕ N` from the summands of `N` to those of `M` vanishes. -/
@[simp↓]
theorem dgHomEquiv_dgId_sum_inr_inl (M N : DGAdditiveClosure C) (i : N.ι) (j : M.ι) :
    dgHomEquiv R _ _ 0 (dgId R (M.sum N)) (.inr i) (.inl j) = 0 :=
  dgHomEquiv_dgId_of_ne R _ Sum.inr_ne_inl

/-- The block of the identity of `M ⊕ N` on the summands of `N` is the identity of `N`. -/
@[simp↓]
theorem dgHomEquiv_dgId_sum_inr_inr (M N : DGAdditiveClosure C) (i j : N.ι) :
    dgHomEquiv R _ _ 0 (dgId R (M.sum N)) (.inr i) (.inr j) =
      dgHomEquiv R N N 0 (dgId R N) i j := by
  rcases eq_or_ne i j with rfl | h
  · rw [dgHomEquiv_dgId_self, dgHomEquiv_dgId_self]
  · rw [dgHomEquiv_dgId_of_ne R _ (Sum.inr_injective.ne h), dgHomEquiv_dgId_of_ne R _ h]

end DGAdditiveClosure

end MathlibExt.DGSource

namespace CategoryTheory.EnrichedFunctor

open MathlibExt.DGSource DGAdditiveClosure

universe v u u₂

/-! ### Functoriality -/

variable {R : Type v} [CommRing R] {C : Type u} {D : Type u₂} [DGCategory R C] [DGCategory R D]
  (F : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D)

/-- The action of a DG functor on matrices of morphisms of degree `n`: it is applied entrywise. -/
noncomputable def mapDGAdditiveClosureHom (M N : DGAdditiveClosure C) (n : ℤ) :
    DGHom R n M N →ₗ[R]
      DGHom R n (⟨M.ι, fun i ↦ F.obj (M.X i)⟩ : DGAdditiveClosure D) ⟨N.ι, fun j ↦ F.obj (N.X j)⟩ :=
  (dgHomEquiv R _ _ n).symm.toLinearMap ∘ₗ
    (LinearMap.piMap fun _ ↦ LinearMap.piMap fun _ ↦ F.dgMap n) ∘ₗ
      (dgHomEquiv R M N n).toLinearMap

/-- The entries of the image of a matrix are the images of its entries. -/
@[simp]
theorem dgHomEquiv_mapDGAdditiveClosureHom {M N : DGAdditiveClosure C} {n : ℤ}
    (f : DGHom R n M N) (i : M.ι) (j : N.ι) :
    dgHomEquiv R _ _ n (F.mapDGAdditiveClosureHom M N n f) i j =
      F.dgMap n (dgHomEquiv R M N n f i j) := by
  simp [mapDGAdditiveClosureHom]

/-- The DG functor between additive closures induced by a DG functor `F`, sending `⊕ᵢ Xᵢ` to
`⊕ᵢ F Xᵢ` and applying `F` to every matrix entry. -/
-- This is reducible, with the object map given explicitly, so that the index type of the image of
-- `M` is reducibly `M.ι`: the matrix entries of morphisms between images are then indexed by the
-- summands of the original objects.
noncomputable abbrev mapDGAdditiveClosure :
    EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) (DGAdditiveClosure C)
      (DGAdditiveClosure D) :=
  letI G := EnrichedFunctor.ofDGMap
    (fun M ↦ (⟨M.ι, fun i ↦ F.obj (M.X i)⟩ : DGAdditiveClosure D))
    (fun {M N} n ↦ F.mapDGAdditiveClosureHom M N n)
    (fun n f ↦ dgHom_ext R fun i j ↦ by
      rw [dgHomEquiv_mapDGAdditiveClosureHom, dgHomEquiv_dgDifferential,
        dgHomEquiv_dgDifferential, dgHomEquiv_mapDGAdditiveClosureHom,
        EnrichedFunctor.dgMap_dgDifferential])
    (fun M ↦ dgHom_ext R fun i j ↦ by
      rw [dgHomEquiv_mapDGAdditiveClosureHom]
      rcases eq_or_ne i j with rfl | h
      · rw [dgHomEquiv_dgId_self R M, dgHomEquiv_dgId_self, EnrichedFunctor.dgMap_dgId]
      · rw [dgHomEquiv_dgId_of_ne R M h, dgHomEquiv_dgId_of_ne R _ h, map_zero])
    (fun f g h ↦ dgHom_ext R fun i k ↦ by
      rw [dgHomEquiv_mapDGAdditiveClosureHom, dgHomEquiv_dgComp, dgHomEquiv_dgComp, map_sum]
      exact Finset.sum_congr rfl fun j _ ↦ by
        rw [dgHomEquiv_mapDGAdditiveClosureHom, dgHomEquiv_mapDGAdditiveClosureHom,
          EnrichedFunctor.dgMap_dgComp])
  { obj := fun M ↦ (⟨M.ι, fun i ↦ F.obj (M.X i)⟩ : DGAdditiveClosure D)
    -- The tactic block postpones elaborating `G.map` until the expected type, which mentions the
    -- object map above, is known; the two object maps then agree by unfolding `G`.
    map := by exact G.map
    map_id := G.map_id
    map_comp := G.map_comp }

/-- The induced DG functor acts on matrices by
`CategoryTheory.EnrichedFunctor.mapDGAdditiveClosureHom`. -/
@[simp]
theorem dgMap_mapDGAdditiveClosure {M N : DGAdditiveClosure C} {n : ℤ} (f : DGHom R n M N) :
    F.mapDGAdditiveClosure.dgMap n f = F.mapDGAdditiveClosureHom M N n f :=
  (EnrichedFunctor.dgMap_apply _ f).trans rfl

end CategoryTheory.EnrichedFunctor
