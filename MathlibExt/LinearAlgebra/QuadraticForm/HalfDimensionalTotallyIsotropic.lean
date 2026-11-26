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

Let F be a field, V an F-vector space, and Q : V → F a quadratic form. Say that Q has a
half-dimensional totally isotropic subspace if V is finite-dimensional and there exists H ⊆ V
with Q|H = 0 and 2 dim_F H = dim_F V. Total isotropy is also defined for module-valued
quadratic maps by Q(x) = 0 for every x in the submodule. It is preserved by isometries,
products and scalar multiplication. A similarity cQ ≃ Q gives a half-dimensional isotropic
graph in Q ⊕ (−cQ); roundness supplies such a similarity when a nonzero ratio of represented
values occurs. Every isotropic two-dimensional quadratic form has an isotropic line. These
statements apply over arbitrary fields.
-/

@[expose] public section

set_option autoImplicit false

universe u v w v'

namespace QuadraticMap

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {M' : Type v'} [AddCommMonoid M'] [Module R M']
variable {N : Type w} [AddCommMonoid N] [Module R N]

/-- **Total isotropy of a submodule.**

Let R be a commutative semiring, M,N R-modules, Q : M → N a quadratic map and H ⊆ M a
submodule. H is totally isotropic for Q precisely when Q(x) = 0 for every x ∈ H.
-/
def IsTotallyIsotropic (Q : QuadraticMap R M N) (H : Submodule R M) : Prop :=
  ∀ x ∈ H, Q x = 0

namespace IsTotallyIsotropic

/-- **Transport of a totally isotropic submodule.**

Let R be a commutative semiring, M,M′,N R-modules, and Q : M → N and Q′ : M′ → N quadratic
maps. Let H ⊆ M satisfy Q|H = 0 and let e : M ≃ M′ be an R-linear isometry, so Q′(e(x)) =
Q(x). Then e(H) is totally isotropic for Q′.
-/
theorem map_isometryEquiv {Q : QuadraticMap R M N}
    {Q' : QuadraticMap R M' N} {H : Submodule R M}
    (hH : Q.IsTotallyIsotropic H) (e : Q.IsometryEquiv Q') :
    Q'.IsTotallyIsotropic (H.map e.toLinearEquiv.toLinearMap) := by
  rintro y ⟨x, hx, rfl⟩
  change Q' (e x) = 0
  rw [e.map_app]
  exact hH x hx

/-- **Products of totally isotropic submodules.**

Let R be a commutative semiring, M,M′,N R-modules, and Q : M → N and Q′ : M′ → N quadratic
maps. If Q vanishes on H ⊆ M and Q′ vanishes on H′ ⊆ M′, then the quadratic map (x,y) ↦ Q(x) +
Q′(y) vanishes on H × H′.
-/
theorem prod {Q : QuadraticMap R M N} {Q' : QuadraticMap R M' N}
    {H : Submodule R M} {H' : Submodule R M'}
    (hH : Q.IsTotallyIsotropic H) (hH' : Q'.IsTotallyIsotropic H') :
    (Q.prod Q').IsTotallyIsotropic (H.prod H') := by
  rintro ⟨x, y⟩ hxy
  change x ∈ H ∧ y ∈ H' at hxy
  rw [QuadraticMap.prod_apply, hH x hxy.1, hH' y hxy.2, zero_add]

/-- **Scalar multiples preserve total isotropy.**

Let R be a commutative semiring, M,N R-modules, Q : M → N a quadratic map and H ⊆ M with Q|H =
0. For every c ∈ R, the quadratic map cQ also vanishes on H.
-/
theorem smul (c : R) {Q : QuadraticMap R M N} {H : Submodule R M}
    (hH : Q.IsTotallyIsotropic H) :
    (c • Q).IsTotallyIsotropic H := by
  intro x hx
  simp [hH x hx]

end IsTotallyIsotropic

/-- **Roundness of a quadratic map.**

Let R be a commutative semiring, M an R-module and Q : M → R a quadratic map. Q is round when,
for every c ≠ 0, the existence of x with Q(x) = c is equivalent to the existence of an
R-linear isometry cQ ≃ Q.
-/
def IsRound (Q : QuadraticMap R M R) : Prop :=
  ∀ c : R, c ≠ 0 →
    ((∃ x, Q x = c) ↔ (c • Q).Equivalent Q)

namespace IsometryEquiv

/-- **Scaling a quadratic isometry.**

Let R be a commutative semiring, M,M′,N R-modules, and Q : M → N and Q′ : M′ → N quadratic
maps. For an R-linear isometry e : Q ≃ Q′ and any c ∈ R, the same linear equivalence gives an
isometry cQ ≃ cQ′.
-/
def smul {Q : QuadraticMap R M N} {Q' : QuadraticMap R M' N}
    (c : R) (e : Q.IsometryEquiv Q') :
    (c • Q).IsometryEquiv (c • Q') where
  toLinearEquiv := e.toLinearEquiv
  map_app' x := by simp [e.map_app]

/-- **The isometry associated to equality.**

Let R be a commutative semiring, M,N R-modules and Q,Q′ : M → N quadratic maps. If Q = Q′, the
identity linear equivalence on M gives an isometry Q ≃ Q′.
-/
def ofEq {Q Q' : QuadraticMap R M N} (h : Q = Q') :
    Q.IsometryEquiv Q' where
  toLinearEquiv := LinearEquiv.refl R M
  map_app' x := by cases h; rfl

/-- **Anisotropy is invariant under isometry.**

Let R be a commutative semiring, M,M′,N R-modules, and Q : M → N and Q′ : M′ → N quadratic
maps. If e : Q ≃ Q′ is an R-linear isometry, Q is anisotropic if and only if Q′ is
anisotropic, where anisotropy means Q(x) = 0 implies x = 0.
-/
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

/-- **Ratios of represented values in a round form.**

Let F be a field, V an F-vector space, and Q : V → F a quadratic form. Roundness means that,
for every nonzero c, c is represented by Q if and only if cQ is isometric to Q. If Q(x) ≠ 0
and Q(y) ≠ 0, then (Q(x)/Q(y))Q is isometric to Q.
-/
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

/-- **The half-dimensional total-isotropy property.**

Let F be a field, V an F-vector space, and Q : V → F a quadratic form. Say that Q has a
half-dimensional totally isotropic subspace if V is finite-dimensional and there exists H ⊆ V
with Q|H = 0 and 2 dim_F H = dim_F V. Thus the predicate asserts finite-dimensionality,
vanishing on H, and the exact dimension equality.
-/
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

/-- **Isometry invariance of half-dimensional total isotropy.**

Let F be a field, V an F-vector space, and Q : V → F a quadratic form. Say that Q has a
half-dimensional totally isotropic subspace if V is finite-dimensional and there exists H ⊆ V
with Q|H = 0 and 2 dim_F H = dim_F V. Let W be a finite-dimensional F-vector space and Q′ a
quadratic form on W. If Q has this property and e : Q ≃ Q′ is an isometry, then Q′ has the
same property.
-/
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

/-- **A product inheriting half-dimensional total isotropy.**

Let F be a field, V an F-vector space, and Q : V → F a quadratic form. Say that Q has a
half-dimensional totally isotropic subspace if V is finite-dimensional and there exists H ⊆ V
with Q|H = 0 and 2 dim_F H = dim_F V. If Q has this property, then Q ⊕ (−cQ) on V × V has it
for every c ∈ F. A suitable subspace is H × H, where H is the subspace for Q.
-/
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

/-- **An isotropic graph from a similarity.**

Let F be a field, V an F-vector space, and Q : V → F a quadratic form. Assume V is
finite-dimensional and cQ is isometric to Q. For an isometry e : cQ ≃ Q, the graph {(e(v),v) :
v ∈ V} is totally isotropic for Q ⊕ (−cQ), with dimension dim V, half the dimension of V × V.
-/
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

/-- **The roundness step for an isotropic product.**

Let F be a field, V an F-vector space, and Q : V → F a quadratic form. Assume V is
finite-dimensional, Q is round and c ≠ 0. Suppose that isotropy of Q implies that Q has a
half-dimensional totally isotropic subspace. If Q ⊕ (−cQ) is not anisotropic, it has a
subspace H on which it vanishes and with 2 dim H = dim(V × V).
-/
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

/-- **An isotropic line in dimension two.**

Let F be a field, V an F-vector space, and Q : V → F a quadratic form. Assume V is
finite-dimensional with dim V = 2 and Q is not anisotropic. Then there exists H ⊆ V with Q|H =
0 and dim H = 1; equivalently, Q has a half-dimensional totally isotropic subspace.
-/
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
