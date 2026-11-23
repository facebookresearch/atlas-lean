/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.AffineSpace.Combination
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Basic.Real.Basic

/-!
# Affine dependences and Gale transforms

For a configuration of `n` points `v_1, …, v_n` in a real vector space `E`, the affine
dependences are the coefficient vectors `λ ∈ ℝ^n` with `∑ λ_i v_i = 0` and `∑ λ_i = 0`. When the
points affinely span a `d`-dimensional space, they form a subspace of dimension `n - d - 1`. A
Gale transform of the configuration lists, for each `i`, the `i`-th coordinates of a basis of
that subspace: `n` vectors in `ℝ^{n-d-1}`. Gale diagrams are a main tool for polytopes with few
vertices and for analysing projections of polytopes (G. M. Ziegler, with R. Sanyal and
T. Schröder, "Projected polytopes, Gale diagrams, and polyhedral surfaces", Oberwolfach workshop
report, https://www.mi.fu-berlin.de/math/groups/discgeom/ziegler/Preprintfiles/102a-PREPRINT.pdf).
-/

@[expose] public section

namespace MathlibExt.Geometry.Polytope

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- **The affine dependence map of a point configuration.** For points `v : Fin n → E`, the linear
map `ℝ^n → E × ℝ` sending `λ` to `(∑ λ_i v_i, ∑ λ_i)`. -/
def affineDependenceMap {n : ℕ} (v : Fin n → E) : (Fin n → ℝ) →ₗ[ℝ] E × ℝ where
  toFun c := (∑ i, c i • v i, ∑ i, c i)
  map_add' a b := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, Prod.mk_add_mk]
  map_smul' r a := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, Prod.smul_mk,
      Finset.smul_sum, Finset.mul_sum]

/-- **Space of affine dependences.** For points `v : Fin n → E`, the subspace of `λ ∈ ℝ^n` with
`∑ λ_i v_i = 0` and `∑ λ_i = 0`. Its elements are the affine dependences of the configuration;
it is zero exactly when the points are affinely independent. -/
def affineDependences {n : ℕ} (v : Fin n → E) : Submodule ℝ (Fin n → ℝ) :=
  LinearMap.ker (affineDependenceMap v)

/-- **Membership in the space of affine dependences.** -/
theorem mem_affineDependences {n : ℕ} {v : Fin n → E} {c : Fin n → ℝ} :
    c ∈ affineDependences v ↔ ∑ i, c i • v i = 0 ∧ ∑ i, c i = 0 := by
  simp [affineDependences, affineDependenceMap, Prod.ext_iff]

/-- **Points of an affine span as affine combinations.** Every point of the affine span of
`v_1, …, v_n` is `∑ λ_i v_i` for some `λ` with `∑ λ_i = 1`. -/
theorem exists_sum_eq_one_of_mem_affineSpan {n : ℕ} {v : Fin n → E} {x : E}
    (hx : x ∈ affineSpan ℝ (Set.range v)) :
    ∃ c : Fin n → ℝ, ∑ i, c i • v i = x ∧ ∑ i, c i = 1 := by
  classical
  obtain ⟨s, w, hw, rfl⟩ := (mem_affineSpan_iff_eq_affineCombination ℝ (V := E)).1 hx
  refine ⟨fun i => if i ∈ s then w i else 0, ?_, ?_⟩
  · rw [Finset.affineCombination_eq_linear_combination s v w hw]
    simp [ite_smul, Finset.sum_ite_mem]
  · simpa [Finset.sum_ite_mem] using hw

/-- **The affine dependence map of a spanning configuration is surjective.** If `v_1, …, v_n`
affinely span `E`, every `(x, c) ∈ E × ℝ` is `(∑ λ_i v_i, ∑ λ_i)` for some `λ`. -/
theorem affineDependenceMap_surjective {n : ℕ} {v : Fin n → E}
    (h : affineSpan ℝ (Set.range v) = ⊤) : Function.Surjective (affineDependenceMap v) := by
  rintro ⟨x, c⟩
  obtain ⟨a, ha, ha1⟩ := exists_sum_eq_one_of_mem_affineSpan (v := v) (x := x) (by simp [h])
  obtain ⟨b, hb, hb1⟩ := exists_sum_eq_one_of_mem_affineSpan (v := v) (x := 0) (by simp [h])
  refine ⟨a + (c - 1) • b, ?_⟩
  simp only [affineDependenceMap, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, add_smul, mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.mul_sum,
    ha, hb, ha1, hb1, smul_zero, add_zero, Prod.mk.injEq, true_and]
  ring

/-- **Dimension of the space of affine dependences.** If `n` points affinely span a real vector
space of dimension `d`, their affine dependences form a subspace of dimension `n - d - 1`; this is
the dimension of the space `ℝ^{n-d-1}` in which a Gale diagram of the configuration lives. -/
theorem finrank_affineDependences [FiniteDimensional ℝ E] {n : ℕ} {v : Fin n → E}
    (h : affineSpan ℝ (Set.range v) = ⊤) :
    Module.finrank ℝ (affineDependences v) = n - Module.finrank ℝ E - 1 := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (affineDependenceMap v)
  rw [LinearMap.range_eq_top.2 (affineDependenceMap_surjective h), finrank_top,
    Module.finrank_prod, Module.finrank_self, Module.finrank_fin_fun] at hrn
  change Module.finrank ℝ (LinearMap.ker (affineDependenceMap v)) = _
  omega

/-- **Gale transform.** Given a basis `b` of the space of affine dependences of `v : Fin n → E`,
the Gale transform sends the index `i` to the vector `(b_k i)_k`: the `i`-th row of the matrix
whose columns are the basis vectors. For an affinely spanning configuration in dimension `d`
these are `n` vectors in a space of dimension `n - d - 1` (`finrank_affineDependences`). -/
noncomputable def galeTransform {n : ℕ} {ι : Type*} {v : Fin n → E}
    (b : Module.Basis ι ℝ (affineDependences v)) :
    Fin n → ι → ℝ :=
  fun i k => (b k : Fin n → ℝ) i

/-- **The vectors of a Gale transform sum to zero.** Every affine dependence has coefficient
sum zero, so the rows of a Gale transform add up to the zero vector. -/
theorem sum_galeTransform {n : ℕ} {ι : Type*} {v : Fin n → E}
    (b : Module.Basis ι ℝ (affineDependences v)) : ∑ i, galeTransform b i = 0 := by
  funext k
  simp only [galeTransform, Finset.sum_apply, Pi.zero_apply]
  exact (mem_affineDependences.1 (b k).2).2

end MathlibExt.Geometry.Polytope
