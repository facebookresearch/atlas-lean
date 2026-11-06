/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1ResidueM22QuadraticCertificates
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Algebra.Module.ZMod

/-! Quadratic polynomials on the eleven-coordinate original point images
are determined by their values at those points, in any binary target module. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- A quadratic polynomial with the eleven squares and fifty-five mixed coefficients. -/
def co1ResidueM22QuadraticPolynomial {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (c : Fin 66 → V) (x : Fin 11 → ZMod 2) : V :=
  ∑ k, (x (co1ResidueM22QuadraticTerms k).1 * x (co1ResidueM22QuadraticTerms k).2) • c k

private theorem decode_single {n : Nat} (i : Fin n) :
    monsterCo1GeometryBinaryMaskDecode (n := n) (2 ^ i.val) = Pi.single i (1 : ZMod 2) := by
  ext j
  simp only [monsterCo1GeometryBinaryMaskDecode, Nat.testBit_two_pow]
  by_cases h : i = j
  · subst j
    simp
  · have hv : i.val ≠ j.val := fun hh => h (Fin.ext hh)
    simp [hv, h]

/-- Every quadratic coefficient is zero if the polynomial vanishes on all original point rows. -/
theorem co1ResidueM22Quadratic_coefficients_zero {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] (c : Fin 66 → V)
    (hzero : ∀ i : Fin 231, co1ResidueM22QuadraticPolynomial c
      (monsterCo1GeometryBinaryMaskDecode (n := 11) (co1ResidueM22LinearCoordinates i)) = 0) :
    c = 0 := by
  let F : (Fin 66 → ZMod 2) →ₗ[ZMod 2] V :=
    (Pi.basisFun (ZMod 2) (Fin 66)).constr (ZMod 2) c
  have hv (i : Fin 231) : F (monsterCo1GeometryBinaryMaskDecode (n := 66)
      (co1ResidueM22QuadraticMasks i)) = 0 := by
    rw [co1ResidueM22QuadraticMasks_correct]
    simpa only [co1ResidueM22QuadraticPolynomial, F, Module.Basis.constr_apply_fintype,
      Pi.basisFun_equivFun,
      LinearEquiv.refl_apply] using hzero i
  funext k
  have hc := congrArg (fun a : Nat => F (monsterCo1GeometryBinaryMaskDecode (n := 66) a))
    (co1ResidueM22QuadraticInverse_correct k)
  have hz : F (monsterCo1GeometryBinaryMaskDecode (n := 66)
      (monsterCo1GeometryBinaryMaskSum
        ((co1ResidueM22QuadraticInverseRow k).map co1ResidueM22QuadraticMasks))) = 0 := by
    rw [monsterCo1GeometryBinaryMaskDecode_sum, map_list_sum]
    simp only [List.map_map]
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact hv i
  rw [hz, decode_single] at hc
  have hsingle : F (Pi.single k (1 : ZMod 2)) = c k := by
    simpa only [F, Pi.basisFun_apply] using
      (Pi.basisFun (ZMod 2) (Fin 66)).constr_basis (ZMod 2) c k
  exact (hc.trans hsingle).symm

/-- A quadratic polynomial vanishing on all original point rows vanishes everywhere. -/
theorem co1ResidueM22Quadratic_zero {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (c : Fin 66 → V)
    (hzero : ∀ i : Fin 231, co1ResidueM22QuadraticPolynomial c
      (monsterCo1GeometryBinaryMaskDecode (n := 11) (co1ResidueM22LinearCoordinates i)) = 0) :
    ∀ x, co1ResidueM22QuadraticPolynomial c x = 0 := by
  rw [co1ResidueM22Quadratic_coefficients_zero c hzero]
  intro x
  simp only [co1ResidueM22QuadraticPolynomial, Pi.zero_apply, smul_zero, Finset.sum_const_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
