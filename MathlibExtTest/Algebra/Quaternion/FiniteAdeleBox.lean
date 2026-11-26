/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import MathlibExt.Algebra.Quaternion.FiniteAdeleBox

@[expose] public section

open scoped TensorProduct Pointwise
open IsDedekindDomain NumberField

noncomputable section

variable {D : Type*} [Ring D] [Algebra ℚ D] (Λ : Submodule ℤ D)

private theorem exactSource_finiteAdeleBox (z : D) :
    z ∈ Submodule.ofFiniteIdele Λ
        (1 : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) ↔
      z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈
        (Submodule.finiteAdeleBox Λ).map
          (AddMonoidHom.mulLeft (1 : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
  Submodule.mem_ofFiniteIdele_iff Λ 1 z

example : (0 : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ :=
  zero_mem _

example (d : Dˣ) :
    ((Submodule.finiteIdeleDiagonal D d :
      (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
        D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
      (d : D) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) :=
  Submodule.val_finiteIdeleDiagonal_apply d

example (u : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    u ∈ Submodule.finiteIdeleStabilizer Λ ↔
      u • ((Submodule.finiteAdeleBox Λ : AddSubgroup (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) :
          Set (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) =
        ((Submodule.finiteAdeleBox Λ : AddSubgroup (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) :
          Set (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
  Submodule.mem_finiteIdeleStabilizer_iff Λ u

/-! ### The box of the integer lattice in `ℚ`

For `D = ℚ` and `Λ = ℤ`, the finite adelic box is a proper subgroup of `ℚ ⊗[ℚ] 𝔸_f`: it contains
`1 ⊗ 1` but not `(1 / 2) ⊗ 1`, whose `2`-adic component is not integral. The non-membership
checks below fail if the integrality condition is dropped from `Submodule.finiteAdeleBox`. -/

/-- The integer lattice `ℤ · 1` in `ℚ`. -/
private abbrev intLattice : Submodule ℤ ℚ := Submodule.span ℤ {1}

/-- The `2`-adic place of `ℚ`, via `primesEquiv`. -/
private abbrev vTwo : HeightOneSpectrum (𝓞 ℚ) :=
  Rat.HeightOneSpectrum.primesEquiv.symm ⟨2, Nat.prime_two⟩

private theorem two_mem_vTwo : (2 : 𝓞 ℚ) ∈ vTwo.asIdeal := by
  show (2 : 𝓞 ℚ) ∈ (Ideal.span {((2 : ℕ) : ℤ)}).map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm
  simpa using Ideal.mem_map_of_mem (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm
    (Ideal.mem_span_singleton_self ((2 : ℕ) : ℤ))

/-- Every element of the box of `ℤ` is integral at every finite place of `ℚ`. -/
private theorem lid_mem_adicCompletionIntegers {x : ℚ ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ}
    (hx : x ∈ Submodule.finiteAdeleBox intLattice) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Algebra.TensorProduct.lid ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) x v ∈ v.adicCompletionIntegers ℚ := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨z, hz, a, ha, rfl⟩ := hx
    obtain ⟨n, rfl⟩ := Submodule.mem_span_singleton.mp hz
    rw [Algebra.TensorProduct.lid_tmul, smul_one_smul]
    exact zsmul_mem (ha v) n
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

/-- The diagonal `1 ⊗ 1` lies in the box of `ℤ`. -/
private theorem one_tmul_one_mem_finiteAdeleBox :
    (1 : ℚ) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox intLattice :=
  AddSubgroup.subset_closure
    ⟨1, Submodule.mem_span_singleton_self 1, 1, fun _ => one_mem _, rfl⟩

/-- The diagonal `(1 / 2) ⊗ 1` does not: its `2`-adic component `1 / 2` is not integral. -/
private theorem half_tmul_one_notMem_finiteAdeleBox :
    (1 / 2 : ℚ) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) ∉ Submodule.finiteAdeleBox intLattice := by
  intro h
  have h2 := lid_mem_adicCompletionIntegers h vTwo
  rw [Algebra.TensorProduct.lid_tmul, ← Algebra.algebraMap_eq_smul_one,
    FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.mem_adicCompletionIntegers,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation', Rat.valuation_le_one_iff_den] at h2
  exact h2 (by simpa using two_mem_vTwo)

/-- At the trivial idele, the lattice of the box of `ℤ` contains `1` but not `1 / 2`. -/
example : (1 : ℚ) ∈ Submodule.ofFiniteIdele intLattice 1 ∧
    (1 / 2 : ℚ) ∉ Submodule.ofFiniteIdele intLattice 1 := by
  simp only [Submodule.mem_ofFiniteIdele_iff, Units.val_one, AddSubgroup.mem_map,
    AddMonoidHom.coe_mulLeft, one_mul, exists_eq_right]
  exact ⟨one_tmul_one_mem_finiteAdeleBox, half_tmul_one_notMem_finiteAdeleBox⟩

/-- So does the conjugate of `ℤ` by the trivial idele. -/
example : (1 : ℚ) ∈ Submodule.conjByFiniteIdele intLattice 1 ∧
    (1 / 2 : ℚ) ∉ Submodule.conjByFiniteIdele intLattice 1 := by
  simp only [Submodule.mem_conjByFiniteIdele_iff, inv_one, Units.val_one, AddSubgroup.mem_map,
    AddMonoidHom.coe_comp, AddMonoidHom.coe_mulLeft, AddMonoidHom.coe_mulRight,
    Function.comp_apply, one_mul, mul_one, exists_eq_right]
  exact ⟨one_tmul_one_mem_finiteAdeleBox, half_tmul_one_notMem_finiteAdeleBox⟩

/-- The diagonal idele `2` does not stabilize the box of `ℤ`: its inverse would move `1 ⊗ 1` to
`(1 / 2) ⊗ 1`. -/
example : Submodule.finiteIdeleDiagonal ℚ (Units.mk0 2 two_ne_zero) ∉
    Submodule.finiteIdeleStabilizer intLattice := by
  intro h
  have h' := (Submodule.mem_finiteIdeleStabilizer_iff intLattice _).mp (inv_mem h)
  have hmem := Set.smul_mem_smul_set (a := (Submodule.finiteIdeleDiagonal ℚ
    (Units.mk0 2 two_ne_zero))⁻¹) one_tmul_one_mem_finiteAdeleBox
  rw [h'] at hmem
  apply half_tmul_one_notMem_finiteAdeleBox
  simpa [Units.smul_def, ← map_inv, Algebra.TensorProduct.tmul_mul_tmul] using hmem

end
