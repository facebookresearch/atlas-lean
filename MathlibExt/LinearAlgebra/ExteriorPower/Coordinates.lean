/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import MathlibExt.LinearAlgebra.ExteriorPower.ContractionWedge

/-!
# Coordinates of left wedge by a basis vector

Let `b : Basis I R M` over a commutative ring, with `I` linearly ordered. The degree-`n+1`
exterior basis is indexed by subsets of `I` of cardinality `n+1`.

If a coordinate subset `s` omits `i`, the `s`-coordinate of `b_i ∧ x` is zero for every `x ∈
Λ^n_R M`. The coefficient determinant has a zero first row at these columns.

Reference: Bourbaki, *Algebra*, Chapter III.
-/

public section
noncomputable section

namespace exteriorPower

open Set Set.powersetCard

universe u v w
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {I : Type w} [LinearOrder I] (b : Module.Basis I R M)

/-- Let `R` be a commutative ring, `M` an `R`-module, and `b : Basis I R M` a basis indexed by a
linearly ordered type `I`. Let `n : ℕ`, `s : Set.powersetCard I (n+1)`, `i ∉ s`, and `v : Fin
n → M`. The `s`-coordinate of `b_i ∧ ιMulti_R(v)` in the basis `b.exteriorPower(n+1)` is zero. -/
theorem exteriorBasis_coord_wedge_word_of_not_mem (i : I) (n : ℕ)
    (s : Set.powersetCard I (n + 1)) (hi : i ∉ (s : Set I)) (v : Fin n → M) :
    (b.exteriorPower (n + 1)).repr
      (exteriorPower.wedgeLeft R M (b i) n (exteriorPower.ιMulti R n v)) s = 0 := by
  rw [exteriorPower.wedgeLeft_apply_ιMulti, exteriorPower.basis_repr_apply,
    exteriorPower.ιMultiDual_apply_ιMulti]
  apply Matrix.det_eq_zero_of_row_eq_zero 0
  intro j
  change b.coord (Set.powersetCard.ofFinEmbEquiv.symm s j) (b i) = 0
  rw [Module.Basis.coord_apply, Module.Basis.repr_self]
  apply Finsupp.single_eq_of_ne
  intro he
  apply hi
  rw [← he]
  exact (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s _).mp ⟨j, rfl⟩

/-- Let `R` be a commutative ring, `M` an `R`-module, and `b : Basis I R M` a basis indexed by a
linearly ordered type `I`. Let `n : ℕ`, `s : Set.powersetCard I (n+1)`, `i ∉ s`, and `x :
Λ^n_R M`. Then `(b.exteriorPower(n+1)).repr (wedgeLeft R M (b i) n x) s = 0`. -/
theorem exteriorBasis_coord_wedge_of_not_mem (i : I) (n : ℕ)
    (s : Set.powersetCard I (n + 1)) (hi : i ∉ (s : Set I)) (x : ⋀[R]^n M) :
    (b.exteriorPower (n + 1)).repr (exteriorPower.wedgeLeft R M (b i) n x) s = 0 := by
  let f : (⋀[R]^n M) →ₗ[R] R :=
    ((Finsupp.lapply s).comp (b.exteriorPower (n + 1)).repr.toLinearMap).comp
      (exteriorPower.wedgeLeft R M (b i) n)
  have hf : f = 0 := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change (b.exteriorPower (n + 1)).repr
      (exteriorPower.wedgeLeft R M (b i) n (exteriorPower.ιMulti R n v)) s = 0
    exact exteriorBasis_coord_wedge_word_of_not_mem b i n s hi v
  exact DFunLike.congr_fun hf x

end exteriorPower
