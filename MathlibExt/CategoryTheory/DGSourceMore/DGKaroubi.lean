/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
This completed proof port retains the original Apache 2.0 license and author credit.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/CategoryTheory/DG/Karoubi.lean
Original license: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
Modifications: only module/namespace paths are adapted for Atlas.
Mathematical operations, hypotheses and proof bodies are retained.
-/

public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Retract
public import MathlibExt.CategoryTheory.DGSource.DGClosedCategory
public import MathlibExt.CategoryTheory.DGSource.DGFunctorHomComplex
public import MathlibExt.CategoryTheory.DGSource.DGQuasiEquivalence

/-!
# The Karoubi envelope of a differential graded category

An object of the DG Karoubi envelope of a DG category `C` is a pair `(X, p)` of an object `X`
of `C` and a closed idempotent `p : X ⟶ X` of degree zero.  The Hom complex from `(X, p)` to
`(Y, q)` is the subcomplex of `Hom(X, Y)` of the morphisms `f` with `p ≫ f = f = f ≫ q`.  It is
closed under the differential because `p` and `q` are closed of degree zero, so the Leibniz rule
gives `p ≫ d f = d (p ≫ f)`.  Composition is that of `C` and the identity of `(X, p)` is `p`.

This is the chain-level counterpart of Mathlib's `CategoryTheory.Idempotents.Karoubi`, whose
construction it follows: the idempotents are split at the level of Hom complexes rather than only
in an underlying category.  Applied to a pretriangulated envelope it is the candidate DG model of
an idempotent completion, as for perfect derived categories.  Only closed idempotents are split
here; comparing `H⁰` of the envelope with the idempotent completion of `H⁰`, which requires
lifting idempotents up to homotopy, is not treated in this file.

The embedding `X ↦ (X, 1)` is a DG functor which is an isomorphism on every Hom complex, hence
quasi-fully faithful.  Every object of the envelope is a retract, in the category `Z⁰` of closed
degree-zero morphisms, of an object in the image of this embedding, and every idempotent of `Z⁰`
of the envelope splits: `Z⁰` of the envelope is idempotent complete.

## Main definitions

* `MathlibExt.DGSource.DGKaroubi`: the objects of the DG Karoubi envelope.
* `MathlibExt.DGSource.DGKaroubi.homSubmodule`: its morphisms of a fixed degree, as morphisms of `C`.
* `MathlibExt.DGSource.DGKaroubi.instDGCategory`: the DG category structure.
* `MathlibExt.DGSource.DGKaroubi.dgHomVal` and `MathlibExt.DGSource.DGKaroubi.dgHomMk`: the underlying morphism of `C`
  of a morphism of the envelope, and the morphism of the envelope with a given underlying one.
* `MathlibExt.DGSource.DGKaroubi.toDGKaroubi`: the embedding `X ↦ (X, 1)`.
* `MathlibExt.DGSource.DGKaroubi.closedHomMk`: the closed degree-zero morphism of the envelope with a given
  underlying morphism, and `MathlibExt.DGSource.DGKaroubi.closedHom_ext` its extensionality lemma.
  Composition and identities in `Z⁰` are computed by `MathlibExt.DGSource.DGKaroubi.dgHomVal_dgClosedHom_comp`
  and `MathlibExt.DGSource.DGKaroubi.dgHomVal_dgClosedHom_id`.
* `MathlibExt.DGSource.DGKaroubi.retract`: an object `(X, p)` as a retract of `(X, 1)` in `Z⁰`.
* `MathlibExt.DGSource.DGKaroubi.ofIdempotent` and `MathlibExt.DGSource.DGKaroubi.retractOfIdempotent`: the object
  `(X, e)` cut out by an idempotent `e` of `Z⁰` on `(X, p)`, as a retract of `(X, p)`.

## Main results

* `MathlibExt.DGSource.DGKaroubi.dgHomVal_dgComp`, `MathlibExt.DGSource.DGKaroubi.dgHomVal_dgDifferential` and
  `MathlibExt.DGSource.DGKaroubi.dgHomVal_dgId`: composition and the differential are those of `C`, and the
  identity of `(X, p)` is `p`.
* `MathlibExt.DGSource.DGKaroubi.isIso_map_toDGKaroubi` and
  `MathlibExt.DGSource.DGKaroubi.isQuasiFullyFaithful_toDGKaroubi`: the embedding is an isomorphism on Hom
  complexes, hence quasi-fully faithful.
* `MathlibExt.DGSource.DGKaroubi.retractOfIdempotent_r_i` and `MathlibExt.DGSource.DGKaroubi.isIdempotentComplete`:
  idempotents split in `Z⁰` of the envelope.

## References

* P. Balmer and M. Schlichting, *Idempotent completion of triangulated categories*, Journal of
  Algebra 236 (2001), Section 1.
* Joël Riou and the Mathlib contributors, `Mathlib.CategoryTheory.Idempotents.Karoubi`, the
  ordinary Karoubi envelope whose objects, morphisms and identities are mirrored here.
-/

public section

open CategoryTheory

namespace MathlibExt.DGSource

universe v u

variable (R : Type v) [CommRing R] (C : Type u) [DGCategory R C]

/-- An object of the **DG Karoubi envelope** of a DG category `C`: an object `X` of `C` with a
closed idempotent `p : X ⟶ X` of degree zero. -/
@[ext]
structure DGKaroubi where
  /-- The underlying object. -/
  X : C
  /-- The idempotent. -/
  p : DGHom R 0 X X
  /-- The idempotent is closed. -/
  dgDifferential_p : dgDifferential R 0 p = 0
  /-- The idempotent is idempotent. -/
  idem : dgComp R p p (zero_add 0) = p

namespace DGKaroubi

attribute [simp] dgDifferential_p idem

variable {R C}

/-! ### Morphisms of a fixed degree -/

/-- The morphisms of degree `n` from `P` to `Q` in the Karoubi envelope: the morphisms
`f : P.X ⟶ Q.X` of degree `n` with `P.p ≫ f = f` and `f ≫ Q.p = f`. -/
def homSubmodule (P Q : DGKaroubi R C) (n : ℤ) : Submodule R (DGHom R n P.X Q.X) where
  carrier := {f | dgComp R P.p f (zero_add n) = f ∧ dgComp R f Q.p (add_zero n) = f}
  add_mem' hf hg := ⟨by rw [dgComp_add, hf.1, hg.1], by rw [add_dgComp, hf.2, hg.2]⟩
  zero_mem' := ⟨dgComp_zero R _ _, zero_dgComp R _ _⟩
  smul_mem' r _ hf := ⟨by rw [dgComp_smul, hf.1], by rw [smul_dgComp, hf.2]⟩

@[simp]
theorem mem_homSubmodule {P Q : DGKaroubi R C} {n : ℤ} {f : DGHom R n P.X Q.X} :
    f ∈ homSubmodule P Q n ↔
      dgComp R P.p f (zero_add n) = f ∧ dgComp R f Q.p (add_zero n) = f :=
  Iff.rfl

/-- The idempotent of `P` is a degree-zero endomorphism of `P` in the Karoubi envelope. -/
theorem p_mem_homSubmodule (P : DGKaroubi R C) : P.p ∈ homSubmodule P P 0 :=
  ⟨P.idem, P.idem⟩

/-- The differentials of the Hom complex of the underlying objects preserve the morphisms of the
Karoubi envelope, since the idempotents are closed of degree zero. -/
theorem d_mem_homSubmodule {P Q : DGKaroubi R C} {i j : ℤ} {f : DGHom R i P.X Q.X}
    (hf : f ∈ homSubmodule P Q i) :
    ((dgHomComplex R P.X Q.X).d i j).hom f ∈ homSubmodule P Q j := by
  by_cases hij : i + 1 = j
  · subst hij
    refine ⟨?_, ?_⟩
    · have key := dgDifferential_dgComp R P.p f (zero_add i)
      rw [hf.1, P.dgDifferential_p, zero_dgComp, zero_add, Int.negOnePow_zero, one_smul] at key
      exact key.symm
    · have key := dgDifferential_dgComp R f Q.p (add_zero i)
      rw [hf.2, Q.dgDifferential_p, dgComp_zero, smul_zero, add_zero] at key
      exact key.symm
  · rw [(dgHomComplex R P.X Q.X).shape i j hij]
    exact zero_mem _

/-- Composition of `C` preserves the morphisms of the Karoubi envelope. -/
theorem dgComp_mem_homSubmodule {P Q S : DGKaroubi R C} {p q n : ℤ} {f : DGHom R p P.X Q.X}
    {g : DGHom R q Q.X S.X} (hf : f ∈ homSubmodule P Q p) (hg : g ∈ homSubmodule Q S q)
    (h : p + q = n) : dgComp R f g h ∈ homSubmodule P S n :=
  ⟨by rw [← dgComp_assoc R P.p f g (zero_add p) h (by omega), hf.1],
    by rw [dgComp_assoc R f g S.p h (add_zero q) (by omega), hg.2]⟩

/-! ### The DG category structure -/

/-- The differential of the Hom complex of the Karoubi envelope between arbitrary indices. -/
private noncomputable def dHom (P Q : DGKaroubi R C) (i j : ℤ) :
    homSubmodule P Q i →ₗ[R] homSubmodule P Q j :=
  ((dgHomComplex R P.X Q.X).d i j).hom.restrict fun _ hf ↦ d_mem_homSubmodule hf

private theorem dHom_apply (P Q : DGKaroubi R C) (i j : ℤ) (f : homSubmodule P Q i) :
    (dHom P Q i j f).1 = ((dgHomComplex R P.X Q.X).d i j).hom f.1 :=
  (rfl)

private theorem dHom_eq_zero (P Q : DGKaroubi R C) {i j : ℤ}
    (h : ¬(ComplexShape.up ℤ).Rel i j) : dHom P Q i j = 0 :=
  LinearMap.ext fun f ↦ Subtype.ext <| by
    rw [dHom_apply, HomologicalComplex.shape _ i j h]
    rfl

private theorem dHom_comp_dHom (P Q : DGKaroubi R C) (i j k : ℤ) :
    dHom P Q j k ∘ₗ dHom P Q i j = 0 :=
  LinearMap.ext fun f ↦ Subtype.ext <| by
    rw [LinearMap.comp_apply, dHom_apply, dHom_apply, ← LinearMap.comp_apply,
      ← ModuleCat.hom_comp, HomologicalComplex.d_comp_d]
    rfl

/-- The Hom complex of the Karoubi envelope: the subcomplex of the Hom complex of the underlying
objects consisting of the morphisms absorbing both idempotents. -/
private noncomputable def homComplex (P Q : DGKaroubi R C) :
    CochainComplex (ModuleCat.{v} R) ℤ where
  X n := ModuleCat.of R (homSubmodule P Q n)
  d i j := ModuleCat.ofHom (dHom P Q i j)
  shape i j h := by rw [dHom_eq_zero P Q h]; rfl
  d_comp_d' i j k _ _ := by rw [← ModuleCat.ofHom_comp, dHom_comp_dHom]; rfl

/-- Composition of morphisms of the Karoubi envelope, computed in `C`. -/
private noncomputable def comp {P Q S : DGKaroubi R C} (p q n : ℤ) (h : p + q = n) :
    homSubmodule P Q p →ₗ[R] homSubmodule Q S q →ₗ[R] homSubmodule P S n :=
  LinearMap.mk₂ R (fun f g ↦ ⟨dgComp R f.1 g.1 h, dgComp_mem_homSubmodule f.2 g.2 h⟩)
    (fun f f' g ↦ Subtype.ext (add_dgComp R f.1 f'.1 g.1 h))
    (fun r f g ↦ Subtype.ext (smul_dgComp R r f.1 g.1 h))
    (fun f g g' ↦ Subtype.ext (dgComp_add R f.1 g.1 g'.1 h))
    (fun r f g ↦ Subtype.ext (dgComp_smul R r f.1 g.1 h))

variable (R C) in
/-- The **Hom-complex data of the DG Karoubi envelope**: the subcomplexes of morphisms absorbing
the idempotents, with the composition of `C` and the idempotent of each object as its
identity. -/
noncomputable def homComplexData : DGCategoryData R (DGKaroubi R C) where
  hom := homComplex
  comp := comp
  id P := ⟨P.p, p_mem_homSubmodule P⟩
  d_comp h f g := Subtype.ext (dgDifferential_dgComp R f.1 g.1 h)
  comp_assoc hpq hqr h f g k := Subtype.ext (dgComp_assoc R f.1 g.1 k.1 hpq hqr h)
  id_comp g := Subtype.ext g.2.1
  comp_id f := Subtype.ext f.2.2

/-- **The DG Karoubi envelope is a differential graded category.** -/
noncomputable instance instDGCategory : DGCategory R (DGKaroubi R C) :=
  (homComplexData R C).toDGCategory

/-! ### Morphisms, differential, composition and identity -/

/-- A morphism of degree `n` in the Karoubi envelope is a morphism of degree `n` of the
underlying objects absorbing both idempotents. -/
noncomputable def dgHomEquiv (P Q : DGKaroubi R C) (n : ℤ) :
    DGHom R n P Q ≃ₗ[R] homSubmodule P Q n :=
  LinearEquiv.refl R _

/-- The underlying morphism of `C` of a morphism of the Karoubi envelope. -/
noncomputable def dgHomVal {P Q : DGKaroubi R C} (n : ℤ) :
    DGHom R n P Q →ₗ[R] DGHom R n P.X Q.X :=
  (homSubmodule P Q n).subtype ∘ₗ (dgHomEquiv P Q n).toLinearMap

theorem dgHomVal_apply {P Q : DGKaroubi R C} {n : ℤ} (f : DGHom R n P Q) :
    dgHomVal n f = (dgHomEquiv P Q n f).1 :=
  (rfl)

/-- The morphism of the Karoubi envelope determined by a morphism absorbing the idempotents has
that morphism as its underlying morphism. -/
@[simp]
theorem dgHomVal_dgHomEquiv_symm_apply {P Q : DGKaroubi R C} {n : ℤ}
    (f : homSubmodule P Q n) : dgHomVal n ((dgHomEquiv P Q n).symm f) = f.1 :=
  (rfl)

/-- The underlying morphism of a morphism of the Karoubi envelope absorbs both idempotents. -/
theorem dgHomVal_mem {P Q : DGKaroubi R C} {n : ℤ} (f : DGHom R n P Q) :
    dgHomVal n f ∈ homSubmodule P Q n :=
  (dgHomEquiv P Q n f).2

@[simp]
theorem p_dgComp_dgHomVal {P Q : DGKaroubi R C} {n : ℤ} (f : DGHom R n P Q) :
    dgComp R P.p (dgHomVal n f) (zero_add n) = dgHomVal n f :=
  (dgHomVal_mem f).1

@[simp]
theorem dgHomVal_dgComp_p {P Q : DGKaroubi R C} {n : ℤ} (f : DGHom R n P Q) :
    dgComp R (dgHomVal n f) Q.p (add_zero n) = dgHomVal n f :=
  (dgHomVal_mem f).2

theorem dgHomVal_injective {P Q : DGKaroubi R C} {n : ℤ} :
    Function.Injective (dgHomVal (P := P) (Q := Q) n) := fun _ _ h ↦
  (dgHomEquiv P Q n).injective (Subtype.ext h)

/-- Morphisms of the Karoubi envelope are determined by their underlying morphisms. -/
theorem dgHom_ext {P Q : DGKaroubi R C} {n : ℤ} {f g : DGHom R n P Q}
    (h : dgHomVal n f = dgHomVal n g) : f = g :=
  dgHomVal_injective h

/-- The differential of the Karoubi envelope is the differential of `C`. -/
@[simp↓]
theorem dgHomVal_dgDifferential {P Q : DGKaroubi R C} {n : ℤ} (f : DGHom R n P Q) :
    dgHomVal (n + 1) (dgDifferential R n f) = dgDifferential R n (dgHomVal n f) :=
  (congrArg Subtype.val ((homComplexData R C).dgDifferential_toDGCategory n f)).trans
    (dHom_apply P Q n (n + 1) _)

/-- Composition in the Karoubi envelope is composition in `C`. -/
@[simp↓]
theorem dgHomVal_dgComp {P Q S : DGKaroubi R C} {p q n : ℤ} (f : DGHom R p P Q)
    (g : DGHom R q Q S) (h : p + q = n) :
    dgHomVal n (dgComp R f g h) = dgComp R (dgHomVal p f) (dgHomVal q g) h :=
  congrArg Subtype.val ((homComplexData R C).dgComp_toDGCategory f g h)

/-- The identity of `P` in the Karoubi envelope is its idempotent. -/
@[simp↓]
theorem dgHomVal_dgId (P : DGKaroubi R C) : dgHomVal 0 (dgId R P) = P.p :=
  congrArg Subtype.val ((homComplexData R C).dgId_toDGCategory P)

/-- The morphism of the Karoubi envelope with underlying morphism `f`, a morphism of `C` absorbing
both idempotents. -/
noncomputable def dgHomMk {P Q : DGKaroubi R C} {n : ℤ} (f : DGHom R n P.X Q.X)
    (hf : f ∈ homSubmodule P Q n) : DGHom R n P Q :=
  (dgHomEquiv P Q n).symm ⟨f, hf⟩

@[simp]
theorem dgHomVal_dgHomMk {P Q : DGKaroubi R C} {n : ℤ} (f : DGHom R n P.X Q.X)
    (hf : f ∈ homSubmodule P Q n) : dgHomVal n (dgHomMk f hf) = f :=
  (rfl)

@[simp]
theorem dgHomMk_dgHomVal {P Q : DGKaroubi R C} {n : ℤ} (f : DGHom R n P Q) :
    dgHomMk (dgHomVal n f) (dgHomVal_mem f) = f :=
  (rfl)

theorem dgHomMk_add {P Q : DGKaroubi R C} {n : ℤ} (f g : DGHom R n P.X Q.X)
    (hf : f ∈ homSubmodule P Q n) (hg : g ∈ homSubmodule P Q n) :
    dgHomMk (f + g) (add_mem hf hg) = dgHomMk f hf + dgHomMk g hg :=
  (rfl)

theorem dgHomMk_smul {P Q : DGKaroubi R C} {n : ℤ} (r : R) (f : DGHom R n P.X Q.X)
    (hf : f ∈ homSubmodule P Q n) :
    dgHomMk (r • f) (Submodule.smul_mem _ r hf) = r • dgHomMk f hf :=
  (rfl)

/-- The differential of a morphism built from a morphism of `C` is built from its differential. -/
theorem dgHomMk_dgDifferential {P Q : DGKaroubi R C} {n : ℤ} (f : DGHom R n P.X Q.X)
    (hf : f ∈ homSubmodule P Q n) :
    dgHomMk (dgDifferential R n f) (d_mem_homSubmodule hf) = dgDifferential R n (dgHomMk f hf) :=
  dgHom_ext (by rw [dgHomVal_dgDifferential, dgHomVal_dgHomMk, dgHomVal_dgHomMk])

/-- The composite of morphisms built from morphisms of `C` is built from their composite. -/
theorem dgHomMk_dgComp {P Q S : DGKaroubi R C} {p q n : ℤ} (f : DGHom R p P.X Q.X)
    (g : DGHom R q Q.X S.X) (hf : f ∈ homSubmodule P Q p) (hg : g ∈ homSubmodule Q S q)
    (h : p + q = n) :
    dgHomMk (dgComp R f g h) (dgComp_mem_homSubmodule hf hg h) =
      dgComp R (dgHomMk f hf) (dgHomMk g hg) h :=
  dgHom_ext (by rw [dgHomVal_dgComp, dgHomVal_dgHomMk, dgHomVal_dgHomMk, dgHomVal_dgHomMk])

/-- The idempotent of `P`, as an endomorphism of `P`, is the identity of `P`. -/
theorem dgHomMk_p (P : DGKaroubi R C) : dgHomMk P.p (p_mem_homSubmodule P) = dgId R P :=
  dgHom_ext (by rw [dgHomVal_dgHomMk, dgHomVal_dgId])

/-! ### The embedding -/

variable (R C) in
/-- The **embedding of a DG category into its Karoubi envelope**, `X ↦ (X, 1)`, acting on
morphisms by the identity. -/
-- The body is exposed so that `((toDGKaroubi R C).obj X).X` is definitionally `X`; otherwise the
-- morphisms of `C` out of `X` could not be used as morphisms out of the underlying object.
@[expose]
noncomputable def toDGKaroubi :
    EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C (DGKaroubi R C) :=
  let obj (X : C) : DGKaroubi R C := ⟨X, dgId R X, dgDifferential_dgId R X, dgId_dgComp R _⟩
  EnrichedFunctor.ofDGMap obj
    (fun {X Y} _ ↦
      { toFun f := dgHomMk (P := obj X) (Q := obj Y) f
          (mem_homSubmodule.2 ⟨dgId_dgComp R f, dgComp_dgId R f⟩)
        map_add' f g := dgHomMk_add (P := obj X) (Q := obj Y) f g _ _
        map_smul' r f := dgHomMk_smul (P := obj X) (Q := obj Y) r f _ })
    (fun {X Y} _ f ↦ dgHomMk_dgDifferential (P := obj X) (Q := obj Y) f _)
    (fun X ↦ dgHomMk_p (obj X))
    (fun {X Y Z} _ _ _ f g h ↦ dgHomMk_dgComp (P := obj X) (Q := obj Y) (S := obj Z) f g _ _ h)

@[simp]
theorem toDGKaroubi_obj_X (X : C) : ((toDGKaroubi R C).obj X).X = X :=
  (rfl)

@[simp]
theorem toDGKaroubi_obj_p (X : C) : ((toDGKaroubi R C).obj X).p = dgId R X :=
  (rfl)

/-- The embedding acts on morphisms by the identity. -/
@[simp]
theorem dgHomVal_dgMap_toDGKaroubi {X Y : C} {n : ℤ} (f : DGHom R n X Y) :
    dgHomVal n ((toDGKaroubi R C).dgMap n f) = f := by
  rw [EnrichedFunctor.dgMap_apply]
  exact dgHomVal_dgHomMk _ _

/-- Every morphism of the Karoubi envelope between objects in the image of the embedding is the
image of its underlying morphism. -/
@[simp]
theorem dgMap_toDGKaroubi_dgHomVal {X Y : C} {n : ℤ}
    (f : DGHom R n ((toDGKaroubi R C).obj X) ((toDGKaroubi R C).obj Y)) :
    (toDGKaroubi R C).dgMap n (dgHomVal n f) = f :=
  dgHom_ext (dgHomVal_dgMap_toDGKaroubi _)

variable (R C) in
/-- **The embedding into the Karoubi envelope is an isomorphism on every Hom complex.** -/
theorem isIso_map_toDGKaroubi (X Y : C) : IsIso ((toDGKaroubi R C).map X Y) := by
  have (n : ℤ) : IsIso (((toDGKaroubi R C).map X Y).f n) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact Function.bijective_iff_has_inverse.2
      ⟨⇑(dgHomVal (P := (toDGKaroubi R C).obj X) (Q := (toDGKaroubi R C).obj Y) n),
        fun f ↦ (congrArg _ (EnrichedFunctor.dgMap_apply _ f).symm).trans
          (dgHomVal_dgMap_toDGKaroubi f),
        fun f ↦ (EnrichedFunctor.dgMap_apply _ _).symm.trans (dgMap_toDGKaroubi_dgHomVal f)⟩
  exact HomologicalComplex.Hom.isIso_of_components _

variable (R C) in
/-- The embedding into the Karoubi envelope is quasi-fully faithful. -/
theorem isQuasiFullyFaithful_toDGKaroubi :
    (toDGKaroubi R C).IsQuasiFullyFaithful :=
  EnrichedFunctor.isQuasiFullyFaithful_of_isIso_map (isIso_map_toDGKaroubi R C)

/-! ### Retracts and splitting of idempotents in `Z⁰` -/

/-- The closed degree-zero morphism of the Karoubi envelope with underlying morphism `f`. -/
noncomputable def closedHomMk {P Q : DGKaroubi R C} (f : DGHom R 0 P.X Q.X)
    (hf : f ∈ homSubmodule P Q 0) (hdf : dgDifferential R 0 f = 0) :
    ForgetEnrichment.of (CochainComplex (ModuleCat.{v} R) ℤ) P ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat.{v} R) ℤ) Q :=
  dgClosedHomOf R (dgHomMk f hf) <| (mem_dgCycles R).2 <|
    dgHom_ext (by rw [dgHomVal_dgDifferential, dgHomVal_dgHomMk, hdf, map_zero])

@[simp]
theorem dgHomVal_dgClosedHom_closedHomMk {P Q : DGKaroubi R C} (f : DGHom R 0 P.X Q.X)
    (hf : f ∈ homSubmodule P Q 0) (hdf : dgDifferential R 0 f = 0) :
    dgHomVal (P := P) (Q := Q) 0 (dgClosedHom R (closedHomMk f hf hdf)) = f := by
  rw [closedHomMk, dgClosedHom_dgClosedHomOf, dgHomVal_dgHomMk]

/-- Two closed degree-zero morphisms of the Karoubi envelope with the same underlying morphism
are equal. -/
theorem closedHom_ext
    {P Q : ForgetEnrichment (CochainComplex (ModuleCat.{v} R) ℤ) (DGKaroubi R C)} {f g : P ⟶ Q}
    (h : dgHomVal 0 (dgClosedHom R f) = dgHomVal 0 (dgClosedHom R g)) : f = g :=
  dgClosedHom_injective R (dgHom_ext h)

/-- The underlying morphism of a closed degree-zero morphism of the Karoubi envelope is closed. -/
@[simp]
theorem dgDifferential_dgHomVal_dgClosedHom
    {P Q : ForgetEnrichment (CochainComplex (ModuleCat.{v} R) ℤ) (DGKaroubi R C)} (f : P ⟶ Q) :
    dgDifferential R 0 (dgHomVal 0 (dgClosedHom R f)) = 0 := by
  have key := congrArg (dgHomVal (0 + 1)) ((mem_dgCycles R).1 (dgClosedHom_mem_dgCycles R f))
  rwa [dgHomVal_dgDifferential, map_zero] at key

/-- The underlying morphism of a composite in `Z⁰` of the Karoubi envelope is the composite of the
underlying morphisms. -/
@[simp↓]
theorem dgHomVal_dgClosedHom_comp
    {P Q S : ForgetEnrichment (CochainComplex (ModuleCat.{v} R) ℤ) (DGKaroubi R C)}
    (f : P ⟶ Q) (g : Q ⟶ S) :
    dgHomVal 0 (dgClosedHom R (f ≫ g)) =
      dgComp R (dgHomVal 0 (dgClosedHom R f)) (dgHomVal 0 (dgClosedHom R g)) (zero_add 0) := by
  rw [dgClosedHom_comp, dgCompZero_def, dgHomVal_dgComp]

/-- The underlying morphism of an identity in `Z⁰` of the Karoubi envelope is the idempotent. -/
@[simp↓]
theorem dgHomVal_dgClosedHom_id
    (P : ForgetEnrichment (CochainComplex (ModuleCat.{v} R) ℤ) (DGKaroubi R C)) :
    dgHomVal 0 (dgClosedHom R (𝟙 P)) =
      (ForgetEnrichment.to (CochainComplex (ModuleCat.{v} R) ℤ) P).p := by
  rw [dgClosedHom_id, dgHomVal_dgId]

/-- The composite of two closed degree-zero morphisms built from morphisms of `C` is built from
the composite of those morphisms. -/
theorem closedHomMk_comp {P Q S : DGKaroubi R C} (f : DGHom R 0 P.X Q.X)
    (hf : f ∈ homSubmodule P Q 0) (hdf : dgDifferential R 0 f = 0) (g : DGHom R 0 Q.X S.X)
    (hg : g ∈ homSubmodule Q S 0) (hdg : dgDifferential R 0 g = 0) :
    closedHomMk f hf hdf ≫ closedHomMk g hg hdg =
      closedHomMk (dgComp R f g (zero_add 0)) (dgComp_mem_homSubmodule hf hg _)
        (by rw [dgDifferential_dgComp, hdf, hdg, zero_dgComp, dgComp_zero, smul_zero, add_zero]) :=
  closedHom_ext <| by
    rw [dgHomVal_dgClosedHom_comp, dgHomVal_dgClosedHom_closedHomMk,
      dgHomVal_dgClosedHom_closedHomMk, dgHomVal_dgClosedHom_closedHomMk]

/-- The closed degree-zero morphism with underlying morphism the idempotent of `P` is the identity
of `P`. -/
theorem closedHomMk_p (P : DGKaroubi R C) :
    closedHomMk P.p (p_mem_homSubmodule P) P.dgDifferential_p = 𝟙 _ :=
  closedHom_ext <| by rw [dgHomVal_dgClosedHom_closedHomMk, dgHomVal_dgClosedHom_id]; rfl

/-- An object `(X, p)` of the Karoubi envelope is a retract of `(X, 1)` in the category `Z⁰` of
closed degree-zero morphisms, through the two morphisms with underlying morphism `p`. -/
noncomputable def retract (P : DGKaroubi R C) :
    Retract (ForgetEnrichment.of (CochainComplex (ModuleCat.{v} R) ℤ) P)
      (ForgetEnrichment.of (CochainComplex (ModuleCat.{v} R) ℤ) ((toDGKaroubi R C).obj P.X)) where
  i := closedHomMk (Q := (toDGKaroubi R C).obj P.X) P.p ⟨P.idem, dgComp_dgId R P.p⟩
    P.dgDifferential_p
  r := closedHomMk (P := (toDGKaroubi R C).obj P.X) P.p ⟨dgId_dgComp R P.p, P.idem⟩
    P.dgDifferential_p
  retract := (closedHomMk_comp _ _ _ _ _ _).trans <| closedHom_ext <|
    (dgHomVal_dgClosedHom_closedHomMk _ _ _).trans <| P.idem.trans (dgHomVal_dgClosedHom_id _).symm

/-- The split monomorphism of `retract P` has underlying morphism `p`. -/
@[simp]
theorem dgHomVal_dgClosedHom_retract_i (P : DGKaroubi R C) :
    dgHomVal (P := P) (Q := (toDGKaroubi R C).obj P.X) 0 (dgClosedHom R (retract P).i) = P.p :=
  dgHomVal_dgClosedHom_closedHomMk (Q := (toDGKaroubi R C).obj P.X) P.p
    ⟨P.idem, dgComp_dgId R P.p⟩ P.dgDifferential_p

/-- The split epimorphism of `retract P` has underlying morphism `p`. -/
@[simp]
theorem dgHomVal_dgClosedHom_retract_r (P : DGKaroubi R C) :
    dgHomVal (P := (toDGKaroubi R C).obj P.X) (Q := P) 0 (dgClosedHom R (retract P).r) = P.p :=
  dgHomVal_dgClosedHom_closedHomMk (P := (toDGKaroubi R C).obj P.X) P.p
    ⟨dgId_dgComp R P.p, P.idem⟩ P.dgDifferential_p

section OfIdempotent

variable (P : DGKaroubi R C)
  (e : ForgetEnrichment.of (CochainComplex (ModuleCat.{v} R) ℤ) P ⟶
    ForgetEnrichment.of (CochainComplex (ModuleCat.{v} R) ℤ) P) (he : e ≫ e = e)

include he in
/-- The underlying morphism of an idempotent of `Z⁰` of the Karoubi envelope is idempotent. -/
theorem dgComp_dgHomVal_dgClosedHom_self :
    dgComp R (dgHomVal 0 (dgClosedHom R e)) (dgHomVal 0 (dgClosedHom R e)) (zero_add 0) =
      dgHomVal 0 (dgClosedHom R e) := by
  rw [← dgHomVal_dgClosedHom_comp, he]

include he in
/-- The object `(X, e)` of the Karoubi envelope cut out by a closed idempotent `e` of degree zero
on `(X, p)`. -/
-- The body is exposed so that `(ofIdempotent P e he).X` is definitionally `P.X`; otherwise the
-- morphisms out of `P.X` could not be used as morphisms out of the underlying object.
@[expose]
noncomputable def ofIdempotent : DGKaroubi R C :=
  ⟨P.X, dgHomVal 0 (dgClosedHom R e), dgDifferential_dgHomVal_dgClosedHom e,
    dgComp_dgHomVal_dgClosedHom_self P e he⟩

@[simp]
theorem ofIdempotent_X : (ofIdempotent P e he).X = P.X :=
  (rfl)

@[simp]
theorem ofIdempotent_p : (ofIdempotent P e he).p = dgHomVal 0 (dgClosedHom R e) :=
  (rfl)

private theorem mem_homSubmodule_ofIdempotent_left :
    dgHomVal (P := P) (Q := P) 0 (dgClosedHom R e) ∈ homSubmodule (ofIdempotent P e he) P 0 :=
  ⟨dgComp_dgHomVal_dgClosedHom_self P e he, (dgHomVal_mem _).2⟩

private theorem mem_homSubmodule_ofIdempotent_right :
    dgHomVal (P := P) (Q := P) 0 (dgClosedHom R e) ∈ homSubmodule P (ofIdempotent P e he) 0 :=
  ⟨(dgHomVal_mem _).1, dgComp_dgHomVal_dgClosedHom_self P e he⟩

/-- The object `(X, e)` cut out by a closed idempotent `e` on `(X, p)` is a retract of `(X, p)`
in `Z⁰`, through the two morphisms with underlying morphism `e`. -/
noncomputable def retractOfIdempotent :
    Retract (ForgetEnrichment.of (CochainComplex (ModuleCat.{v} R) ℤ) (ofIdempotent P e he))
      (ForgetEnrichment.of (CochainComplex (ModuleCat.{v} R) ℤ) P) where
  i := closedHomMk _ (mem_homSubmodule_ofIdempotent_left P e he)
    (dgDifferential_dgHomVal_dgClosedHom e)
  r := closedHomMk _ (mem_homSubmodule_ofIdempotent_right P e he)
    (dgDifferential_dgHomVal_dgClosedHom e)
  retract := (closedHomMk_comp _ _ _ _ _ _).trans <| closedHom_ext <|
    (dgHomVal_dgClosedHom_closedHomMk _ _ _).trans <|
      (dgComp_dgHomVal_dgClosedHom_self P e he).trans
        (dgHomVal_dgClosedHom_id (ForgetEnrichment.of _ (ofIdempotent P e he))).symm

/-- The split monomorphism of `retractOfIdempotent P e he` has underlying morphism `e`. -/
@[simp]
theorem dgHomVal_dgClosedHom_retractOfIdempotent_i :
    dgHomVal (P := ofIdempotent P e he) (Q := P) 0 (dgClosedHom R (retractOfIdempotent P e he).i) =
      dgHomVal 0 (dgClosedHom R e) :=
  dgHomVal_dgClosedHom_closedHomMk _ (mem_homSubmodule_ofIdempotent_left P e he)
    (dgDifferential_dgHomVal_dgClosedHom e)

/-- The split epimorphism of `retractOfIdempotent P e he` has underlying morphism `e`. -/
@[simp]
theorem dgHomVal_dgClosedHom_retractOfIdempotent_r :
    dgHomVal (P := P) (Q := ofIdempotent P e he) 0 (dgClosedHom R (retractOfIdempotent P e he).r) =
      dgHomVal 0 (dgClosedHom R e) :=
  dgHomVal_dgClosedHom_closedHomMk _ (mem_homSubmodule_ofIdempotent_right P e he)
    (dgDifferential_dgHomVal_dgClosedHom e)

/-- The idempotent `e` factors through the retract `(X, e)` of `(X, p)`. -/
theorem retractOfIdempotent_r_i :
    (retractOfIdempotent P e he).r ≫ (retractOfIdempotent P e he).i = e :=
  (closedHomMk_comp _ (mem_homSubmodule_ofIdempotent_right P e he)
    (dgDifferential_dgHomVal_dgClosedHom e) _ (mem_homSubmodule_ofIdempotent_left P e he)
    (dgDifferential_dgHomVal_dgClosedHom e)).trans <| closedHom_ext <|
      (dgHomVal_dgClosedHom_closedHomMk _ _ _).trans (dgComp_dgHomVal_dgClosedHom_self P e he)

end OfIdempotent

/-- **Idempotents split in `Z⁰` of the Karoubi envelope.**  A closed idempotent `e` of degree zero
on `(X, p)` splits through `(X, e)`, by the two morphisms with underlying morphism `e`. -/
instance isIdempotentComplete :
    IsIdempotentComplete
      (ForgetEnrichment (CochainComplex (ModuleCat.{v} R) ℤ) (DGKaroubi R C)) where
  idempotents_split P e he :=
    let P' := ForgetEnrichment.to (CochainComplex (ModuleCat.{v} R) ℤ) P
    ⟨_, (retractOfIdempotent P' e he).i, (retractOfIdempotent P' e he).r,
      (retractOfIdempotent P' e he).retract, retractOfIdempotent_r_i P' e he⟩

end DGKaroubi

end MathlibExt.DGSource
