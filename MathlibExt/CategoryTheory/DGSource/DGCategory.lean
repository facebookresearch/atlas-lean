/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
This completed source port retains the original Apache 2.0 license and author credit.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/CategoryTheory/DG/Basic.lean
Only module/namespace paths are adapted for Atlas; source operations and hypotheses are retained.
-/

public import Mathlib.CategoryTheory.Enriched.Basic
public import MathlibExt.CategoryTheory.DGSource.CochainTensorSummands
public import MathlibExt.CategoryTheory.DGSource.CochainTensorDifferential

/-!
# Differential graded categories

A differential graded category over a commutative ring `R` is a category enriched in cochain
complexes of `R`-modules: every Hom object is a complex `Hom(X, Y)`, and composition is a closed
degree-zero map out of the tensor product of two Hom complexes.

This file fixes that definition and unpacks the enriched data into the calculus one actually
computes with: the `R`-module `DGHom R n X Y` of morphisms of degree `n`, the differential raising
the degree by one, the composition of two homogeneous morphisms, and the identity.  The enriched
axioms then become the associativity and unit laws for that composition, and the fact that
composition is a chain map out of the tensor product becomes the graded Leibniz rule

`d (dgComp f g) = dgComp (d f) g + (-1) ^ |f| • dgComp f (d g)`.

The factor order is Mathlib's: `CategoryTheory.eComp` composes
`Hom(X, Y) ⊗ Hom(Y, Z) ⟶ Hom(X, Z)`, so `dgComp f g` is `f` followed by `g` and the Leibniz sign
is carried by the degree of the *first* argument, exactly as in
`CochainComplex.HomComplex.δ_comp`.

The identity is a degree-zero cycle, so the closed degree-zero morphisms form an ordinary
category; that category and its quotient by homotopy are not built here.

## Main definitions

* `MathlibExt.DGSource.DGCategory`: a differential graded category over `R`.
* `MathlibExt.DGSource.dgHomComplex`: its Hom complex.
* `MathlibExt.DGSource.DGHom`: the `R`-module of morphisms of a fixed degree.
* `MathlibExt.DGSource.dgDifferential`: the differential of the Hom complex.
* `MathlibExt.DGSource.dgComp`: composition of two homogeneous morphisms.
* `MathlibExt.DGSource.dgId`: the identity, a degree-zero morphism.

## Main results

* `MathlibExt.DGSource.dgDifferential_dgComp`: the graded Leibniz rule.
* `MathlibExt.DGSource.dgComp_assoc`: composition of homogeneous morphisms is associative.
* `MathlibExt.DGSource.dgDifferential_negOnePow_smul_dgComp` and `MathlibExt.DGSource.negOnePow_smul_dgComp_assoc`: the
  Leibniz rule and associativity for Keller-ordered composition
  `g ∘ f = (-1) ^ (p * q) • dgComp f g`.
* `MathlibExt.DGSource.dgId_dgComp` and `MathlibExt.DGSource.dgComp_dgId`: the identity is a two-sided unit.
* `MathlibExt.DGSource.dgDifferential_dgId`: the identity is a cycle.
* `MathlibExt.DGSource.dgDifferential_eq_zero_of_dgComp_eq_dgId`: a two-sided inverse of a cycle is a cycle.
* `MathlibExt.DGSource.castDeg`: transport a homogeneous morphism along an equality of degrees.
* `MathlibExt.DGSource.castDeg_dgId_dgComp` and `MathlibExt.DGSource.dgComp_castDeg_dgId`: a degree transport of the
  identity is still a unit for composition.

## References

* B. Keller, *Deriving DG categories*, Section 1.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1, for the sign
  conventions.
* V. Drinfeld, *DG quotients of DG categories*, Section 2.
-/

public section

open CategoryTheory MonoidalCategory HomologicalComplex

namespace MathlibExt.DGSource

universe v u

/-- A **differential graded category** over a commutative ring `R`: a category enriched in
cochain complexes of `R`-modules.  Its Hom complexes are `MathlibExt.DGSource.dgHomComplex`, and the
morphisms of a fixed degree, their differential, and their composition are `MathlibExt.DGSource.DGHom`,
`MathlibExt.DGSource.dgDifferential` and `MathlibExt.DGSource.dgComp`. -/
abbrev DGCategory (R : Type v) [CommRing R] (C : Type u) :=
  EnrichedCategory (CochainComplex (ModuleCat.{v} R) ℤ) C

variable (R : Type v) [CommRing R] {C : Type u} [DGCategory R C]

/-- The Hom complex of a differential graded category. -/
abbrev dgHomComplex (X Y : C) : CochainComplex (ModuleCat.{v} R) ℤ :=
  X ⟶[CochainComplex (ModuleCat.{v} R) ℤ] Y

/-- The `R`-module of morphisms `X ⟶ Y` of degree `n` in a differential graded category. -/
abbrev DGHom (n : ℤ) (X Y : C) : Type v := (dgHomComplex R X Y).X n

/-- The differential of a differential graded category, raising the degree of a morphism by
one. -/
noncomputable abbrev dgDifferential {X Y : C} (n : ℤ) :
    DGHom R n X Y →ₗ[R] DGHom R (n + 1) X Y :=
  ((dgHomComplex R X Y).d n (n + 1)).hom

/-- The differential of a differential graded category squares to zero. -/
@[simp]
theorem dgDifferential_dgDifferential {X Y : C} {n : ℤ} (f : DGHom R n X Y) :
    dgDifferential R (n + 1) (dgDifferential R n f) = 0 := by
  rw [← ModuleCat.comp_apply, (dgHomComplex R X Y).d_comp_d]
  simp

/-! ### Degree transport -/

/-- Transport a homogeneous morphism along an equality of degrees. -/
noncomputable def castDeg {X Y : C} {p p' : ℤ} (hp : p = p') :
    DGHom R p X Y →ₗ[R] DGHom R p' X Y :=
  ((dgHomComplex R X Y).XIsoOfEq hp).hom.hom

/-- Degree transport is the isomorphism `HomologicalComplex.XIsoOfEq` between the two degree
components of the Hom complex. -/
theorem castDeg_def {X Y : C} {p p' : ℤ} (hp : p = p') :
    castDeg R (X := X) (Y := Y) hp = ((dgHomComplex R X Y).XIsoOfEq hp).hom.hom :=
  (rfl)

/-- Transport along a self-equality of degrees leaves a homogeneous morphism unchanged. -/
@[simp]
theorem castDeg_self {X Y : C} {p : ℤ} (hp : p = p) (f : DGHom R p X Y) :
    castDeg R hp f = f := by
  simp [castDeg]

/-- Two successive degree transports are a single degree transport. -/
@[simp]
theorem castDeg_castDeg {X Y : C} {p p' p'' : ℤ} (hp : p = p') (hp' : p' = p'')
    (f : DGHom R p X Y) : castDeg R hp' (castDeg R hp f) = castDeg R (hp.trans hp') f := by
  subst hp hp'
  simp

/-- Degree transport commutes with a differential between arbitrary equal indices. -/
theorem d_castDeg {X Y : C} {a b a' b' : ℤ} (h : a = b) (h' : a' = b')
    (f : DGHom R a X Y) :
    ((dgHomComplex R X Y).d b b').hom (castDeg R h f) =
      castDeg R h' (((dgHomComplex R X Y).d a a').hom f) := by
  subst h h'
  simp [castDeg]

/-! ### Composition -/

/-- The bidegree-`(p, q)` component of the enriched composition of a differential graded
category: it computes `MathlibExt.DGSource.dgComp` on a pure tensor. -/
noncomputable def dgCompMap (X Y Z : C) (p q n : ℤ) (h : p + q = n) :
    (dgHomComplex R X Y).X p ⊗ (dgHomComplex R Y Z).X q ⟶ (dgHomComplex R X Z).X n :=
  ιTensorObj (dgHomComplex R X Y) (dgHomComplex R Y Z) p q n h ≫
    (eComp (CochainComplex (ModuleCat.{v} R) ℤ) X Y Z).f n

/-- The bidegree component of enriched composition is the inclusion of that summand of the tensor
product of the two Hom complexes, followed by the enriched composition. -/
theorem dgCompMap_def (X Y Z : C) (p q n : ℤ) (h : p + q = n) :
    dgCompMap R X Y Z p q n h =
      ιTensorObj (dgHomComplex R X Y) (dgHomComplex R Y Z) p q n h ≫
        (eComp (CochainComplex (ModuleCat.{v} R) ℤ) X Y Z).f n :=
  (rfl)

/-- Composition of a morphism of degree `p` from `X` to `Y` with a morphism of degree `q` from
`Y` to `Z`, in Mathlib's enriched factor order: `dgComp f g` is `f` followed by `g`. -/
noncomputable def dgComp {X Y Z : C} {p q n : ℤ} (f : DGHom R p X Y) (g : DGHom R q Y Z)
    (h : p + q = n) : DGHom R n X Z :=
  (dgCompMap R X Y Z p q n h).hom (f ⊗ₜ g)

@[simp]
theorem dgCompMap_tmul {X Y Z : C} {p q n : ℤ} (h : p + q = n) (f : DGHom R p X Y)
    (g : DGHom R q Y Z) :
    (dgCompMap R X Y Z p q n h).hom (f ⊗ₜ g) = dgComp R f g h :=
  (rfl)

@[simp]
theorem zero_dgComp {X Y Z : C} {p q n : ℤ} (g : DGHom R q Y Z) (h : p + q = n) :
    dgComp R (0 : DGHom R p X Y) g h = 0 := by
  rw [dgComp, TensorProduct.zero_tmul, map_zero]

@[simp]
theorem dgComp_zero {X Y Z : C} {p q n : ℤ} (f : DGHom R p X Y) (h : p + q = n) :
    dgComp R f (0 : DGHom R q Y Z) h = 0 := by
  rw [dgComp, TensorProduct.tmul_zero, map_zero]

@[simp]
theorem add_dgComp {X Y Z : C} {p q n : ℤ} (f f' : DGHom R p X Y) (g : DGHom R q Y Z)
    (h : p + q = n) : dgComp R (f + f') g h = dgComp R f g h + dgComp R f' g h := by
  rw [dgComp, dgComp, dgComp, TensorProduct.add_tmul, map_add]

@[simp]
theorem dgComp_add {X Y Z : C} {p q n : ℤ} (f : DGHom R p X Y) (g g' : DGHom R q Y Z)
    (h : p + q = n) : dgComp R f (g + g') h = dgComp R f g h + dgComp R f g' h := by
  rw [dgComp, dgComp, dgComp, TensorProduct.tmul_add, map_add]

@[simp]
theorem neg_dgComp {X Y Z : C} {p q n : ℤ} (f : DGHom R p X Y) (g : DGHom R q Y Z)
    (h : p + q = n) : dgComp R (-f) g h = -dgComp R f g h := by
  rw [dgComp, dgComp, TensorProduct.neg_tmul, map_neg]

@[simp]
theorem dgComp_neg {X Y Z : C} {p q n : ℤ} (f : DGHom R p X Y) (g : DGHom R q Y Z)
    (h : p + q = n) : dgComp R f (-g) h = -dgComp R f g h := by
  rw [dgComp, dgComp, TensorProduct.tmul_neg, map_neg]

@[simp]
theorem smul_dgComp {X Y Z : C} {p q n : ℤ} (r : R) (f : DGHom R p X Y) (g : DGHom R q Y Z)
    (h : p + q = n) : dgComp R (r • f) g h = r • dgComp R f g h := by
  rw [dgComp, dgComp, ← TensorProduct.smul_tmul', map_smul]

@[simp]
theorem dgComp_smul {X Y Z : C} {p q n : ℤ} (r : R) (f : DGHom R p X Y) (g : DGHom R q Y Z)
    (h : p + q = n) : dgComp R f (r • g) h = r • dgComp R f g h := by
  rw [dgComp, dgComp, TensorProduct.tmul_smul, map_smul]

/-- Composition commutes with a sign `u : ℤˣ` on its first factor. -/
theorem units_smul_dgComp {X Y Z : C} {p q n : ℤ} (u : ℤˣ) (f : DGHom R p X Y)
    (g : DGHom R q Y Z) (h : p + q = n) : dgComp R (u • f) g h = u • dgComp R f g h := by
  simp only [Units.smul_def, ← Int.cast_smul_eq_zsmul R, smul_dgComp]

/-- Composition commutes with a sign `u : ℤˣ` on its second factor. -/
theorem dgComp_units_smul {X Y Z : C} {p q n : ℤ} (u : ℤˣ) (f : DGHom R p X Y)
    (g : DGHom R q Y Z) (h : p + q = n) : dgComp R f (u • g) h = u • dgComp R f g h := by
  simp only [Units.smul_def, ← Int.cast_smul_eq_zsmul R, dgComp_smul]

/-- Degree transport in the first argument commutes with DG composition. -/
theorem castDeg_dgComp {X Y Z : C} {p p' q n n' : ℤ} (hp : p = p') (hn : n = n')
    (f : DGHom R p X Y) (g : DGHom R q Y Z) (h : p' + q = n') :
    dgComp R (castDeg R hp f) g h = castDeg R hn (dgComp R f g (by omega)) := by
  subst hp hn
  simp [castDeg]

/-- Degree transport in the second argument commutes with DG composition. -/
theorem dgComp_castDeg {X Y Z : C} {p q q' n n' : ℤ} (hq : q = q') (hn : n = n')
    (f : DGHom R p X Y) (g : DGHom R q Y Z) (h : p + q' = n') :
    dgComp R f (castDeg R hq g) h = castDeg R hn (dgComp R f g (by omega)) := by
  subst hq hn
  simp [castDeg]

/-- A composite is the degree transport of the composite taken in the sum of the degrees of its
factors. -/
theorem dgComp_eq_castDeg_dgComp {X Y Z : C} {p q n : ℤ} (f : DGHom R p X Y) (g : DGHom R q Y Z)
    (h : p + q = n) : dgComp R f g h = castDeg R h (dgComp R f g rfl) := by
  subst h
  rw [castDeg_self]

/-- Degree transport in the first argument commutes with DG composition, the composite being
taken in the sum of the degrees of its factors. -/
theorem castDeg_dgComp_eq_castDeg {X Y Z : C} {p p' q n : ℤ} (hp : p = p') (f : DGHom R p X Y)
    (g : DGHom R q Y Z) (h : p' + q = n) :
    dgComp R (castDeg R hp f) g h = castDeg R (by omega) (dgComp R f g rfl) :=
  castDeg_dgComp R hp _ f g h

/-- Degree transport in the second argument commutes with DG composition, the composite being
taken in the sum of the degrees of its factors. -/
theorem dgComp_castDeg_eq_castDeg {X Y Z : C} {p q q' n : ℤ} (hq : q = q') (f : DGHom R p X Y)
    (g : DGHom R q Y Z) (h : p + q' = n) :
    dgComp R f (castDeg R hq g) h = castDeg R (by omega) (dgComp R f g rfl) :=
  dgComp_castDeg R hq _ f g h

theorem sum_dgComp {ι : Type*} (s : Finset ι) {X Y Z : C} {p q n : ℤ} (f : ι → DGHom R p X Y)
    (g : DGHom R q Y Z) (h : p + q = n) :
    dgComp R (∑ i ∈ s, f i) g h = ∑ i ∈ s, dgComp R (f i) g h := by
  rw [dgComp, TensorProduct.sum_tmul, map_sum]
  rfl

theorem dgComp_sum {ι : Type*} (s : Finset ι) {X Y Z : C} {p q n : ℤ} (f : DGHom R p X Y)
    (g : ι → DGHom R q Y Z) (h : p + q = n) :
    dgComp R f (∑ i ∈ s, g i) h = ∑ i ∈ s, dgComp R f (g i) h := by
  rw [dgComp, TensorProduct.tmul_sum, map_sum]
  rfl

/-! ### The Leibniz rule -/

/- Composition is a chain map out of the tensor product of the two Hom complexes; restricting
that equation to a bidegree summand is the Leibniz rule before evaluation. -/
private lemma dgCompMap_comp_d (X Y Z : C) (p q n : ℤ) (h : p + q = n) :
    dgCompMap R X Y Z p q n h ≫ (dgHomComplex R X Z).d n (n + 1) =
      ((dgHomComplex R X Y).d p (p + 1) ▷ (dgHomComplex R Y Z).X q) ≫
          dgCompMap R X Y Z (p + 1) q (n + 1) (by omega) +
        p.negOnePow • (((dgHomComplex R X Y).X p ◁ (dgHomComplex R Y Z).d q (q + 1)) ≫
          dgCompMap R X Y Z p (q + 1) (n + 1) (by omega)) := by
  rw [dgCompMap, Category.assoc,
    (eComp (CochainComplex (ModuleCat.{v} R) ℤ) X Y Z).comm n (n + 1), ← Category.assoc,
    ι_tensorObj_d]
  simp [dgCompMap]

/-- **The graded Leibniz rule** in a differential graded category: the differential of a
composite differentiates each factor, with the Koszul sign carried by the degree of the first
factor. -/
theorem dgDifferential_dgComp {X Y Z : C} {p q n : ℤ} (f : DGHom R p X Y) (g : DGHom R q Y Z)
    (h : p + q = n) :
    dgDifferential R n (dgComp R f g h) =
      dgComp R (dgDifferential R p f) g (by omega) +
        p.negOnePow • dgComp R f (dgDifferential R q g) (by omega) := by
  have key := LinearMap.congr_fun
    (congrArg ModuleCat.Hom.hom (dgCompMap_comp_d R X Y Z p q n h)) (f ⊗ₜ g)
  simpa only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply, dgCompMap_tmul,
    ModuleCat.hom_add, ModuleCat.hom_smul, LinearMap.add_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply, LinearMap.smul_apply,
    ModuleCat.MonoidalCategory.whiskerLeft_apply] using key

/-- The graded Leibniz rule for the differentials of the Hom complexes between arbitrary consecutive
indices `p ⟶ p'`, `q ⟶ q'` and `n ⟶ n'`, so that the degrees need not be written as `p + 1`. -/
theorem dgHomComplex_d_dgComp {X Y Z : C} {p q n p' q' n' : ℤ} (hp : p + 1 = p')
    (hq : q + 1 = q') (hn : n + 1 = n') (f : DGHom R p X Y) (g : DGHom R q Y Z) (h : p + q = n) :
    ((dgHomComplex R X Z).d n n').hom (dgComp R f g h) =
      dgComp R (((dgHomComplex R X Y).d p p').hom f) g (by omega) +
        p.negOnePow • dgComp R f (((dgHomComplex R Y Z).d q q').hom g) (by omega) := by
  subst hp hq hn
  exact dgDifferential_dgComp R f g h

/-! ### Associativity -/

/- The enriched associativity axiom, restricted to a summand of the triple tensor product of Hom
complexes. -/
private lemma dgCompMap_assoc (W X Y Z : C) (p q r n : ℤ) (h : p + q + r = n) :
    (dgCompMap R W X Y p q (p + q) rfl ▷ (dgHomComplex R Y Z).X r) ≫
        dgCompMap R W Y Z (p + q) r n h =
      (α_ ((dgHomComplex R W X).X p) ((dgHomComplex R X Y).X q)
          ((dgHomComplex R Y Z).X r)).hom ≫
        ((dgHomComplex R W X).X p ◁ dgCompMap R X Y Z q r (q + r) rfl) ≫
          dgCompMap R W X Z p (q + r) n (by omega) := by
  rw [dgCompMap, dgCompMap, comp_whiskerRight, Category.assoc, ← ι_whiskerRight_assoc,
    ← HomologicalComplex.comp_f, ← e_assoc' (CochainComplex (ModuleCat.{v} R) ℤ) W X Y Z,
    HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    ι_ι_associator_hom_assoc _ _ _ p q r (p + q) (q + r) n rfl rfl h (by omega),
    dgCompMap, dgCompMap]
  simp only [ι_whiskerLeft_assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc]

/-- Composition of homogeneous morphisms in a differential graded category is associative. -/
theorem dgComp_assoc {W X Y Z : C} {p q r pq qr n : ℤ} (f : DGHom R p W X) (g : DGHom R q X Y)
    (k : DGHom R r Y Z) (hpq : p + q = pq) (hqr : q + r = qr) (hn : p + q + r = n) :
    dgComp R (dgComp R f g hpq) k (by omega : pq + r = n) =
      dgComp R f (dgComp R g k hqr) (by rw [← hqr, ← hn, add_assoc]) := by
  subst hpq
  subst hqr
  have key := LinearMap.congr_fun
    (congrArg ModuleCat.Hom.hom (dgCompMap_assoc R W X Y Z p q r n hn)) ((f ⊗ₜ g) ⊗ₜ k)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    ModuleCat.MonoidalCategory.associator_hom_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply, dgCompMap_tmul] at key
  exact key

/-- Associativity of composition with arbitrary degree proofs: a left-associated composite is the
degree transport of the right-associated composite whose intermediate degrees are the sums of the
degrees of the factors. -/
theorem dgComp_assoc_eq_castDeg {W X Y Z : C} {p q r pq n : ℤ} (f : DGHom R p W X)
    (g : DGHom R q X Y) (k : DGHom R r Y Z) (hpq : p + q = pq) (h : pq + r = n) :
    dgComp R (dgComp R f g hpq) k h =
      castDeg R (by omega) (dgComp R f (dgComp R g k rfl) rfl) := by
  subst hpq h
  rw [dgComp_assoc R f g k rfl rfl rfl, dgComp_eq_castDeg_dgComp R (n := p + q + r)]

/-! ### Keller-ordered composition

Composition in Keller's order, `g ∘ f` for `f` of degree `p` followed by `g` of degree `q`, is
the enriched composite twisted by the Koszul sign: `g ∘ f = (-1) ^ (p * q) • dgComp f g`.  The
two lemmas below state the Leibniz rule and associativity for these signed composites. -/

/-- **The Leibniz rule in Keller's order**: for the Keller-ordered composite
`g ∘ f = (-1) ^ (p * q) • dgComp f g`, `d (g ∘ f) = d g ∘ f + (-1) ^ |g| • g ∘ d f`. -/
theorem dgDifferential_negOnePow_smul_dgComp {X Y Z : C} {p q n : ℤ} (f : DGHom R p X Y)
    (g : DGHom R q Y Z) (h : p + q = n) :
    dgDifferential R n ((p * q).negOnePow • dgComp R f g h) =
      (p * (q + 1)).negOnePow • dgComp R f (dgDifferential R q g) (by omega) +
        q.negOnePow • ((p + 1) * q).negOnePow • dgComp R (dgDifferential R p f) g (by omega) := by
  rw [map_zsmul_unit, dgDifferential_dgComp, smul_add, smul_smul, smul_smul]
  have e₁ : (p * q).negOnePow * p.negOnePow = (p * (q + 1)).negOnePow := by
    rw [← Int.negOnePow_add, Int.negOnePow_eq_iff]
    exact ⟨0, by ring⟩
  have e₂ : q.negOnePow * ((p + 1) * q).negOnePow = (p * q).negOnePow := by
    rw [← Int.negOnePow_add, Int.negOnePow_eq_iff]
    exact ⟨q, by ring⟩
  rw [e₁, e₂]
  exact add_comm _ _

/-- **Keller-ordered composition is associative**: the Koszul signs of the two bracketings
`(k ∘ g) ∘ f` and `k ∘ (g ∘ f)` agree. -/
theorem negOnePow_smul_dgComp_assoc {W X Y Z : C} {p q r pq qr n : ℤ} (f : DGHom R p W X)
    (g : DGHom R q X Y) (k : DGHom R r Y Z) (hpq : p + q = pq) (hqr : q + r = qr)
    (hn : p + q + r = n) :
    (pq * r).negOnePow • dgComp R ((p * q).negOnePow • dgComp R f g hpq) k
        (by omega : pq + r = n) =
      (p * qr).negOnePow • dgComp R f ((q * r).negOnePow • dgComp R g k hqr)
        (by omega : p + qr = n) := by
  subst hpq hqr
  simp only [Units.smul_def, ← Int.cast_smul_eq_zsmul R, smul_dgComp, dgComp_smul, smul_smul,
    ← Int.cast_mul]
  rw [dgComp_assoc R f g k rfl rfl hn]
  congr 1
  rw [← Units.val_mul, ← Units.val_mul, ← Int.negOnePow_add, ← Int.negOnePow_add]
  congr 3
  ring

/-! ### The identity -/

/-- The identity morphism of an object of a differential graded category: the degree-zero
morphism named by the enriched identity, that is, the image of `1` under the degree-zero
component of `CategoryTheory.eId`. -/
noncomputable def dgId (X : C) : DGHom R 0 X X :=
  ((eId (CochainComplex (ModuleCat.{v} R) ℤ) X).f 0).hom
    ((singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat.{v} R))).inv 1)

/-- The identity is the image of `1` under the degree-zero component of the enriched identity. -/
theorem dgId_def (X : C) :
    dgId R X = ((eId (CochainComplex (ModuleCat.{v} R) ℤ) X).f 0).hom
      ((singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat.{v} R))).inv 1) :=
  (rfl)

/-- The identity of a differential graded category is a cycle, so it is a morphism of the
underlying category of closed degree-zero morphisms. -/
@[simp]
theorem dgDifferential_dgId (X : C) : dgDifferential R 0 (dgId R X) = 0 := by
  have hu : (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ)).d 0 (0 + 1) = 0 :=
    HomologicalComplex.single_obj_d (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat.{v} R)) 0 (0 + 1)
  rw [dgId, ← ModuleCat.comp_apply,
    (eId (CochainComplex (ModuleCat.{v} R) ℤ) X).comm 0 (0 + 1), hu, Limits.zero_comp]
  simp

/-- The identity is a left unit for composition. -/
@[simp]
theorem dgId_dgComp {X Y : C} {q : ℤ} (g : DGHom R q X Y) :
    dgComp R (dgId R X) g (zero_add q) = g := by
  have h := HomologicalComplex.congr_hom
    (e_id_comp (CochainComplex (ModuleCat.{v} R) ℤ) X Y) q
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, leftUnitor_inv_f,
    HomologicalComplex.leftUnitor'_inv, Category.assoc, Category.assoc,
    ι_whiskerRight_assoc, HomologicalComplex.id_f] at h
  have key := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) g
  simpa only [dgComp, dgCompMap, ModuleCat.hom_comp, dgId, LinearMap.coe_comp,
    Function.comp_apply, ModuleCat.MonoidalCategory.leftUnitor_inv_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply, ModuleCat.hom_id, LinearMap.id_coe,
    id_eq] using key

/-- The identity is a right unit for composition. -/
@[simp]
theorem dgComp_dgId {X Y : C} {p : ℤ} (f : DGHom R p X Y) :
    dgComp R f (dgId R Y) (add_zero p) = f := by
  have h := HomologicalComplex.congr_hom
    (e_comp_id (CochainComplex (ModuleCat.{v} R) ℤ) X Y) p
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, rightUnitor_inv_f,
    HomologicalComplex.rightUnitor'_inv, Category.assoc, Category.assoc,
    ι_whiskerLeft_assoc, HomologicalComplex.id_f] at h
  have key := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) f
  simpa only [dgComp, dgCompMap, ModuleCat.hom_comp, dgId, LinearMap.coe_comp,
    Function.comp_apply, ModuleCat.MonoidalCategory.rightUnitor_inv_apply,
    ModuleCat.MonoidalCategory.whiskerLeft_apply, ModuleCat.hom_id, LinearMap.id_coe,
    id_eq] using key

/-- A degree transport of the identity is a cycle, for the differential between arbitrary
indices. -/
@[simp]
theorem d_castDeg_dgId (X : C) {a b : ℤ} (ha : 0 = a) :
    ((dgHomComplex R X X).d a b).hom (castDeg R ha (dgId R X)) = 0 := by
  subst ha
  rw [castDeg_self]
  by_cases hb : 0 + 1 = b
  · subst hb
    exact dgDifferential_dgId R X
  · rw [(dgHomComplex R X X).shape _ _ hb]
    rfl

/-- A degree transport of the identity is a left unit for composition, up to degree transport. -/
@[simp]
theorem castDeg_dgId_dgComp {X Y : C} {a q n : ℤ} (ha : 0 = a) (g : DGHom R q X Y)
    (h : a + q = n) : dgComp R (castDeg R ha (dgId R X)) g h = castDeg R (by omega) g := by
  subst ha
  obtain rfl : n = q := by omega
  rw [castDeg_self, castDeg_self, dgId_dgComp]

/-- The identity is a left unit for composition with an arbitrary degree proof, up to degree
transport. -/
theorem dgId_dgComp_eq_castDeg {X Y : C} {q n : ℤ} (g : DGHom R q X Y) (h : 0 + q = n) :
    dgComp R (dgId R X) g h = castDeg R (by omega) g := by
  simpa only [castDeg_self] using castDeg_dgId_dgComp R rfl g h

/-- A degree transport of the identity is a right unit for composition, up to degree
transport. -/
@[simp]
theorem dgComp_castDeg_dgId {X Y : C} {a p n : ℤ} (ha : 0 = a) (f : DGHom R p X Y)
    (h : p + a = n) : dgComp R f (castDeg R ha (dgId R Y)) h = castDeg R (by omega) f := by
  subst ha
  obtain rfl : n = p := by omega
  rw [castDeg_self, castDeg_self, dgComp_dgId]

/-- The identity is a right unit for composition with an arbitrary degree proof, up to degree
transport. -/
theorem dgComp_dgId_eq_castDeg {X Y : C} {p n : ℤ} (f : DGHom R p X Y) (h : p + 0 = n) :
    dgComp R f (dgId R Y) h = castDeg R (by omega) f := by
  simpa only [castDeg_self] using dgComp_castDeg_dgId R rfl f h

/-- **A two-sided inverse of a closed morphism is closed**: if `f : X ⟶ Y` of degree `p` is a
cycle and `g : Y ⟶ X` of degree `q` is inverse to it on both sides, then `g` is a cycle. -/
theorem dgDifferential_eq_zero_of_dgComp_eq_dgId {X Y : C} {p q : ℤ} {f : DGHom R p X Y}
    {g : DGHom R q Y X} (hf : dgDifferential R p f = 0) (hpq : p + q = 0)
    (hfg : dgComp R f g hpq = dgId R X) (hgf : dgComp R g f (by omega) = dgId R Y) :
    dgDifferential R q g = 0 := by
  -- Differentiating `dgComp f g = dgId X` shows that `f` followed by `d g` vanishes.
  have h : dgComp R f (dgDifferential R q g) (by omega : p + (q + 1) = 0 + 1) = 0 := by
    have key := congrArg (dgDifferential R 0) hfg
    rw [dgDifferential_dgComp, hf, zero_dgComp, dgDifferential_dgId] at key
    exact (smul_eq_zero_iff_eq _).mp ((zero_add _).symm.trans key)
  calc dgDifferential R q g
      = dgComp R (dgId R Y) (dgDifferential R q g) (zero_add (q + 1)) := (dgId_dgComp R _).symm
    _ = dgComp R (dgComp R g f (by omega)) (dgDifferential R q g) (zero_add (q + 1)) := by
      rw [hgf]
    _ = dgComp R g (dgComp R f (dgDifferential R q g) (by omega : p + (q + 1) = 0 + 1))
          (by omega) := dgComp_assoc R g f _ (by omega) _ (by omega)
    _ = 0 := by rw [h, dgComp_zero]

end MathlibExt.DGSource
