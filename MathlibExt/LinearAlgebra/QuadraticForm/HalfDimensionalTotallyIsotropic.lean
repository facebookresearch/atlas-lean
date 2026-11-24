/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.LinearAlgebra.QuadraticForm.Prod

/-!
# Half-dimensional totally isotropic subspaces

This file develops a weak, characteristic-free quadratic-form property: the
existence of a half-dimensional subspace on which a quadratic map vanishes.
It provides transport under isometry equivalences, product and scalar
constructions, similarity graphs, a roundness-based recursive step, and the
rank-two base case.

The property includes no nondegeneracy, perpendicular-equality, Lagrangian,
metabolic, or hyperbolic assertion.

## Main declarations

* `QuadraticMap.IsTotallyIsotropic`
* `QuadraticMap.IsRound`
* `QuadraticForm.HasHalfDimensionalTotallyIsotropicSubspace`
* `QuadraticForm.hasHalfDimensionalTotallyIsotropicSubspace_prod_neg_smul_of_not_anisotropic`
* `QuadraticForm.hasHalfDimensionalTotallyIsotropicSubspace_of_not_anisotropic_finrank_two`
-/

@[expose] public section

set_option autoImplicit false

universe u v w v'

namespace QuadraticMap

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {M' : Type v'} [AddCommMonoid M'] [Module R M']
variable {N : Type w} [AddCommMonoid N] [Module R N]

/-- A submodule on which a quadratic map vanishes identically. -/
def IsTotallyIsotropic (Q : QuadraticMap R M N) (H : Submodule R M) : Prop :=
  ∀ x ∈ H, Q x = 0

namespace IsTotallyIsotropic

/-- Total isotropy is preserved by mapping a submodule through an isometry
equivalence. -/
theorem map_isometryEquiv {Q : QuadraticMap R M N}
    {Q' : QuadraticMap R M' N} {H : Submodule R M}
    (hH : Q.IsTotallyIsotropic H) (e : Q.IsometryEquiv Q') :
    Q'.IsTotallyIsotropic (H.map e.toLinearEquiv.toLinearMap) := by
  rintro y ⟨x, hx, rfl⟩
  change Q' (e x) = 0
  rw [e.map_app]
  exact hH x hx

/-- The product of two totally isotropic submodules is totally isotropic for
the product quadratic map. -/
theorem prod {Q : QuadraticMap R M N} {Q' : QuadraticMap R M' N}
    {H : Submodule R M} {H' : Submodule R M'}
    (hH : Q.IsTotallyIsotropic H) (hH' : Q'.IsTotallyIsotropic H') :
    (Q.prod Q').IsTotallyIsotropic (H.prod H') := by
  rintro ⟨x, y⟩ hxy
  change x ∈ H ∧ y ∈ H' at hxy
  rw [QuadraticMap.prod_apply, hH x hxy.1, hH' y hxy.2, zero_add]

/-- A totally isotropic submodule remains so after scaling the quadratic
map. -/
theorem smul (c : R) {Q : QuadraticMap R M N} {H : Submodule R M}
    (hH : Q.IsTotallyIsotropic H) :
    (c • Q).IsTotallyIsotropic H := by
  intro x hx
  simp [hH x hx]

end IsTotallyIsotropic

/-- A quadratic map is round when its nonzero represented values are exactly
its similarity factors. -/
def IsRound (Q : QuadraticMap R M R) : Prop :=
  ∀ c : R, c ≠ 0 →
    ((∃ x, Q x = c) ↔ (c • Q).Equivalent Q)

namespace IsometryEquiv

/-- Scalar multiplication transports an isometry equivalence. -/
def smul {Q : QuadraticMap R M N} {Q' : QuadraticMap R M' N}
    (c : R) (e : Q.IsometryEquiv Q') :
    (c • Q).IsometryEquiv (c • Q') where
  toLinearEquiv := e.toLinearEquiv
  map_app' x := by simp [e.map_app]

/-- Equality of quadratic maps gives an isometry equivalence with identity
underlying linear equivalence. -/
def ofEq {Q Q' : QuadraticMap R M N} (h : Q = Q') :
    Q.IsometryEquiv Q' where
  toLinearEquiv := LinearEquiv.refl R M
  map_app' x := by cases h; rfl

/-- An isometry equivalence preserves and reflects anisotropy. -/
theorem anisotropic_iff {Q : QuadraticMap R M N}
    {Q' : QuadraticMap R M' N} (e : Q.IsometryEquiv Q') :
    Q.Anisotropic ↔ Q'.Anisotropic := by
  constructor
  · intro hQ y hy
    have hx : Q (e.symm y) = 0 := by
      rw [← e.map_app]
      simpa
    have hzero := hQ _ hx
    simpa using congrArg e hzero
  · intro hQ x hx
    have he0 : Q' (e x) = 0 := by rw [e.map_app, hx]
    have hex : e x = 0 := hQ _ he0
    exact e.injective (by simpa using hex)

end IsometryEquiv

namespace IsRound

variable {F : Type u} [Field F]
variable {V : Type v} [AddCommGroup V] [Module F V]

/-- In a round form, the ratio of two nonzero represented values is a
similarity factor. -/
theorem ratio_equivalent (Q : QuadraticForm F V) (hQ : Q.IsRound)
    {x y : V} (hx : Q x ≠ 0) (hy : Q y ≠ 0) :
    ((Q x / Q y) • Q).Equivalent Q := by
  obtain ⟨ex⟩ := (hQ (Q x) hx).mp ⟨x, rfl⟩
  obtain ⟨ey⟩ := (hQ (Q y) hy).mp ⟨y, rfl⟩
  let e₀ := ey.symm.smul (Q x / Q y)
  have hforms :
      (Q x / Q y) • (Q y • Q) = Q x • Q := by
    ext z
    simp only [smul_apply, smul_eq_mul]
    field_simp
  exact ⟨(e₀.trans (IsometryEquiv.ofEq hforms)).trans ex⟩

end IsRound

end QuadraticMap

namespace QuadraticForm

open _root_.QuadraticMap

universe u₁ v₁

variable {F : Type u₁} [Field F]
variable {V : Type v₁} [AddCommGroup V] [Module F V]

/-- A finite-dimensional quadratic form has a half-dimensional totally isotropic subspace.
This includes no nondegeneracy or perpendicular-equality claim. -/
def HasHalfDimensionalTotallyIsotropicSubspace
    (Q : QuadraticForm F V) : Prop :=
  Module.Finite F V ∧ ∃ H : Submodule F V,
    Q.IsTotallyIsotropic H ∧
      2 * Module.finrank F H = Module.finrank F V

private theorem finrank_prodSubmodule
    {W : Type*} [AddCommGroup W] [Module F W]
    [FiniteDimensional F V] [FiniteDimensional F W]
    (H : Submodule F V) (K : Submodule F W) :
    Module.finrank F (H.prod K) =
      Module.finrank F H + Module.finrank F K := by
  rw [(Submodule.prodEquiv H K).finrank_eq, Module.finrank_prod]

private def similarityGraphLinearMap (Q : QuadraticForm F V) (c : F)
    (e : (c • Q).IsometryEquiv Q) : V →ₗ[F] V × V :=
  e.toLinearEquiv.toLinearMap.prod LinearMap.id

private theorem similarityGraphLinearMap_injective
    (Q : QuadraticForm F V) (c : F)
    (e : (c • Q).IsometryEquiv Q) :
    Function.Injective (similarityGraphLinearMap Q c e) := by
  intro x y hxy
  exact congrArg Prod.snd hxy

private def similarityGraph (Q : QuadraticForm F V) (c : F)
    (e : (c • Q).IsometryEquiv Q) : Submodule F (V × V) :=
  LinearMap.range (similarityGraphLinearMap Q c e)

private theorem finrank_similarityGraph
    (Q : QuadraticForm F V) (c : F)
    (e : (c • Q).IsometryEquiv Q) :
    Module.finrank F (similarityGraph Q c e) = Module.finrank F V := by
  exact LinearMap.finrank_range_of_inj
    (similarityGraphLinearMap_injective Q c e)

private theorem similarityGraph_isTotallyIsotropic
    (Q : QuadraticForm F V) (c : F)
    (e : (c • Q).IsometryEquiv Q) :
    (Q.prod ((-c) • Q)).IsTotallyIsotropic (similarityGraph Q c e) := by
  rintro y ⟨x, rfl⟩
  rw [QuadraticMap.prod_apply]
  change Q (e x) + (-c • Q) x = 0
  rw [e.map_app]
  change c * Q x + -c * Q x = 0
  simp

namespace HasHalfDimensionalTotallyIsotropicSubspace

/-- The half-dimensional totally isotropic-subspace property is preserved by
isometry equivalence. -/
theorem map_isometryEquiv
    {W : Type*} [AddCommGroup W] [Module F W]
    [FiniteDimensional F W]
    {Q : QuadraticForm F V} {Q' : QuadraticForm F W}
    (hQ : Q.HasHalfDimensionalTotallyIsotropicSubspace)
    (e : Q.IsometryEquiv Q') :
    Q'.HasHalfDimensionalTotallyIsotropicSubspace := by
  obtain ⟨hfinite, H, hHiso, hHdim⟩ := hQ
  let : Module.Finite F V := hfinite
  refine ⟨inferInstance, H.map e.toLinearEquiv.toLinearMap,
    hHiso.map_isometryEquiv e, ?_⟩
  rw [e.toLinearEquiv.finrank_map_eq, hHdim,
    e.toLinearEquiv.finrank_eq]

/-- A product with a scalar multiple inherits a half-dimensional totally
isotropic subspace from the left form. -/
theorem prod_neg_smul_of_left
    (Q : QuadraticForm F V) (c : F)
    (hQ : Q.HasHalfDimensionalTotallyIsotropicSubspace) :
    HasHalfDimensionalTotallyIsotropicSubspace
      (Q.prod ((-c) • Q)) := by
  obtain ⟨hfinite, H, hHiso, hHdim⟩ := hQ
  let : Module.Finite F V := hfinite
  refine ⟨inferInstance, H.prod H, hHiso.prod (hHiso.smul (-c)), ?_⟩
  rw [finrank_prodSubmodule, Module.finrank_prod]
  omega

/-- A similarity equivalence supplies a half-dimensional totally isotropic
graph in `Q.prod ((-c) • Q)`. -/
theorem prod_neg_smul_of_equivalent [FiniteDimensional F V]
    (Q : QuadraticForm F V) (c : F) (h : (c • Q).Equivalent Q) :
    HasHalfDimensionalTotallyIsotropicSubspace
      (Q.prod ((-c) • Q)) := by
  obtain ⟨e⟩ := h
  refine ⟨inferInstance, similarityGraph Q c e,
    similarityGraph_isTotallyIsotropic Q c e, ?_⟩
  rw [finrank_similarityGraph, Module.finrank_prod]
  omega

end HasHalfDimensionalTotallyIsotropicSubspace

private theorem hasHalfDimensionalTotallyIsotropicSubspace_prod_neg_smul_of_left_or_equivalent
    [FiniteDimensional F V] (Q : QuadraticForm F V) (c : F)
    (h : Q.HasHalfDimensionalTotallyIsotropicSubspace ∨
      (c • Q).Equivalent Q) :
    HasHalfDimensionalTotallyIsotropicSubspace
      (Q.prod ((-c) • Q)) := by
  rcases h with hQ | he
  · exact hQ.prod_neg_smul_of_left Q c
  · exact HasHalfDimensionalTotallyIsotropicSubspace.prod_neg_smul_of_equivalent
      Q c he

/-- Recursive induction step once lower-rank roundness and the
lower-isotropic induction hypothesis are available. -/
theorem hasHalfDimensionalTotallyIsotropicSubspace_prod_neg_smul_of_not_anisotropic
    [FiniteDimensional F V] (Q : QuadraticForm F V) (c : F) (hc : c ≠ 0)
    (hround : Q.IsRound)
    (hind : ¬ Q.Anisotropic →
      Q.HasHalfDimensionalTotallyIsotropicSubspace)
    (hprod : ¬ (Q.prod ((-c) • Q)).Anisotropic) :
    HasHalfDimensionalTotallyIsotropicSubspace
      (Q.prod ((-c) • Q)) := by
  by_cases hQ : Q.Anisotropic
  · obtain ⟨⟨x, y⟩, hxy0, hiso⟩ :=
      (QuadraticMap.not_anisotropic_iff_exists _).1 hprod
    change Q x + -c * Q y = 0 at hiso
    have hrel : Q x = c * Q y := by
      calc
        Q x = (Q x + -c * Q y) + c * Q y := by ring
        _ = c * Q y := by rw [hiso, zero_add]
    have hy : Q y ≠ 0 := by
      intro hy0
      have hyv : y = 0 := hQ y hy0
      have hxq : Q x = 0 := by rw [hrel, hy0, mul_zero]
      have hxv : x = 0 := hQ x hxq
      exact hxy0 (Prod.ext hxv hyv)
    have hx : Q x ≠ 0 := hrel.symm ▸ mul_ne_zero hc hy
    have he := hround.ratio_equivalent Q hx hy
    have hratio : Q x / Q y = c := by
      rw [hrel]
      exact mul_div_cancel_right₀ c hy
    rw [hratio] at he
    exact HasHalfDimensionalTotallyIsotropicSubspace.prod_neg_smul_of_equivalent
      Q c he
  · exact (hind hQ).prod_neg_smul_of_left Q c

/-- Every non-anisotropic rank-two form has an isotropic line, hence the
half-dimensional totally isotropic-subspace property. -/
theorem hasHalfDimensionalTotallyIsotropicSubspace_of_not_anisotropic_finrank_two
    [FiniteDimensional F V] (Q : QuadraticForm F V)
    (hdim : Module.finrank F V = 2) (hQ : ¬ Q.Anisotropic) :
    Q.HasHalfDimensionalTotallyIsotropicSubspace := by
  obtain ⟨x, hx0, hxQ⟩ :=
    (QuadraticMap.not_anisotropic_iff_exists Q).1 hQ
  refine ⟨inferInstance, Submodule.span F {x}, ?_, ?_⟩
  · intro y hy
    rw [Submodule.mem_span_singleton] at hy
    obtain ⟨d, rfl⟩ := hy
    rw [Q.map_smul, hxQ, smul_zero]
  · rw [finrank_span_singleton hx0, hdim]

end QuadraticForm

end
