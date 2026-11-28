/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.LinearAlgebra.ExteriorPower.LeadingCoefficient

/-!
# Missing-coordinate vanishing for a leading determinant

For a basis indexed by a linearly ordered type, the leading functional uses the dual
coordinates indexed by `{j} ∪ s`. If a vector in the exterior basis tail `t` has an index
outside both `s` and `{j}`, its determinant row is zero.

The resulting vanishing holds for any leading vector `x`; other positions of `t` may contain
`j`.

Reference: Bourbaki, *Algebra*, Chapter III.
-/

public section
noncomputable section
namespace exteriorPower

universe u v w
variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
variable {I : Type w} [LinearOrder I] (b : Module.Basis I R M)

/-- Let `R` be a commutative ring, `M` an `R`-module, and `b : Basis I R M` indexed by a linearly
ordered type `I`. For `n : ℕ` and `s : Set.powersetCard I n`, let `e_s : Fin n ↪o I` enumerate
`s` in order. Let `j : I`, `s,t : Set.powersetCard I n`, `x : M`, and `r : Fin n`. If `e_t r ∉
s` and `e_t r ≠ j`, then `leadingCoefficient b j s (x ∧ (b.exteriorPower n t))=0`. -/
theorem leadingCoefficient_wedge_basis_zero_of_missing_index {n : ℕ}
    (j : I) (s t : Set.powersetCard I n) (x : M) (r : Fin n)
    (hr : Set.powersetCard.ofFinEmbEquiv.symm t r ∉ s)
    (hrj : Set.powersetCard.ofFinEmbEquiv.symm t r ≠ j) :
    leadingCoefficient b j s (wedgeLeft R M x n (b.exteriorPower n t)) = 0 := by
  classical
  rw [basis_apply, ιMulti_family, wedgeLeft_apply_ιMulti]
  change leadingCoefficient b j s (ιMulti R (n + 1)
    (Fin.cons x (b ∘ Set.powersetCard.ofFinEmbEquiv.symm t))) = 0
  rw [leadingCoefficient_ιMulti]
  apply Matrix.det_eq_zero_of_row_eq_zero r.succ
  intro k
  induction k using Fin.cases with
  | zero =>
    simp only [Matrix.of_apply, Fin.cons_zero, Fin.cons_succ, Function.comp_apply]
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, ite_eq_right hrj]
  | succ k =>
    simp only [Matrix.of_apply, Fin.cons_succ, Function.comp_apply]
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    apply ite_eq_right
    intro he
    apply hr
    exact (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s _).mp ⟨k, he.symm⟩

end exteriorPower
