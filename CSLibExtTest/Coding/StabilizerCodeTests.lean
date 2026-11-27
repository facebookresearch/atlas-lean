/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Coding.StabilizerCode
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
# Tests: Dimension of a stabilizer code
-/

@[expose] public section

open Cslib.CodingTheory.CSS
open scoped Matrix
namespace CslibTest.CodingTheory.StabilizerCode

set_option autoImplicit false

open Cslib.CodingTheory.StabilizerCode

#print axioms finrank_stabilizerCode
#print axioms trace_codeProjector
#print axioms pauli_eq_pauliXZ

/-- The all-zero `X` parts of a witness family. -/
def wA (n r : ℕ) : Fin r → Fin n → ZMod 2 := fun _ _ => 0

/-- The constant `Z` parts of a witness family. -/
def wB (n r : ℕ) (b : Fin n → ZMod 2) : Fin r → Fin n → ZMod 2 := fun _ => b

/-- The all-`1` scalars of a witness family. -/
def wC (r : ℕ) : Fin r → ℂ := fun _ => 1

/-- The all-`-1` scalars of a witness family. -/
def wCNeg (r : ℕ) : Fin r → ℂ := fun _ => -1

/-- `Z` on the first of two qubits. -/
def wB0 : Fin 2 → ZMod 2 := fun i => if i = 0 then 1 else 0

/-- The identity Pauli operator is `1`. -/
theorem test_pauli_zero_one {n : ℕ} : pauli (0 : Fin n → ZMod 2) 0 = 1 := by
  ext u v
  simp only [pauli, Matrix.of_apply, add_zero, zero_dotProduct, sign_zero, Matrix.one_apply]

/-- A pure phase Pauli operator is Hermitian. -/
theorem test_pauli_zero_herm {n : ℕ} (b : Fin n → ZMod 2) :
    (pauli (0 : Fin n → ZMod 2) b)ᴴ = pauli 0 b := by
  ext u v
  simp only [Matrix.conjTranspose_apply, pauli, Matrix.of_apply, add_zero]
  by_cases huv : u = v
  · subst huv
    simp only [ite_true, star_sign]
  · have huv' : ¬ v = u := fun h => huv h.symm
    rw [ite_eq_right huv', ite_eq_right huv, star_zero]

/-- A single unsigned `Z`-type generator squares to `1`. -/
theorem single_hsq {n : ℕ} (b : Fin n → ZMod 2) :
    ∀ j : Fin 1, ((1 : ℂ) • pauli (0 : Fin n → ZMod 2) b)
      * ((1 : ℂ) • pauli 0 b) = 1 := by
  intro j
  have hH : (pauli (0 : Fin n → ZMod 2) b)ᴴ = pauli 0 b := test_pauli_zero_herm b
  have hP := Cslib.CodingTheory.QuantumCode.conjTranspose_pauli_mul_pauli
    (0 : Fin n → ZMod 2) b 0 b
  simp only [add_zero, dotProduct_zero, sign_zero] at hP
  have hbb : b + b = 0 := add_self_eq_zero b
  rw [hbb, test_pauli_zero_one, one_smul] at hP
  rw [one_smul]
  rw [hH] at hP
  exact hP

/-- A single generator commutes with itself. -/
theorem single_hcomm {n : ℕ} (b : Fin n → ZMod 2) :
    ∀ j k : Fin 1, Commute ((1 : ℂ) • pauli (0 : Fin n → ZMod 2) b)
      ((1 : ℂ) • pauli 0 b) := fun _ _ => rfl

/-- A single nonzero pair is independent. -/
theorem single_hind {n : ℕ} (b : Fin n → ZMod 2) (hb : b ≠ 0) :
    LinearIndependent (ZMod 2) (fun _ : Fin 1 => ((0 : Fin n → ZMod 2), b)) := by
  rw [linearIndependent_unique_iff]
  intro h
  exact hb (congrArg Prod.snd h)

/-- Witness: the single `Z` generator on one qubit squares to `1`. -/
theorem singleZ_hsq (j : Fin 1) :
    (wC 1 j • pauli (wA 1 1 j) (wB 1 1 (fun _ => (1 : ZMod 2)) j))
      * (wC 1 j • pauli (wA 1 1 j) (wB 1 1 (fun _ => (1 : ZMod 2)) j)) = 1 :=
  single_hsq (fun _ => (1 : ZMod 2)) j

/-- Witness: the single `Z` generator on one qubit commutes with itself. -/
theorem singleZ_hcomm (j k : Fin 1) :
    Commute (wC 1 j • pauli (wA 1 1 j) (wB 1 1 (fun _ => (1 : ZMod 2)) j))
      (wC 1 k • pauli (wA 1 1 k) (wB 1 1 (fun _ => (1 : ZMod 2)) k)) :=
  single_hcomm (fun _ => (1 : ZMod 2)) j k

/-- Witness: the single `Z` generator on one qubit is independent. -/
theorem singleZ_hind :
    LinearIndependent (ZMod 2)
      (fun j : Fin 1 => (wA 1 1 j, wB 1 1 (fun _ => (1 : ZMod 2)) j)) := by
  have hb : (fun _ => (1 : ZMod 2)) ≠ (0 : Fin 1 → ZMod 2) := by
    intro h
    have h1 := congrFun h 0
    simp only [Pi.zero_apply] at h1
    exact one_ne_zero h1
  exact single_hind (fun _ => (1 : ZMod 2)) hb

/-- Witness: the single `Z` generator on one qubit cuts out a 1-dimensional code. -/
theorem singleZ_finrank : Module.finrank ℂ
    (⨅ j : Fin 1, LinearMap.ker (Matrix.toLin' (wC 1 j
      • pauli (wA 1 1 j) (wB 1 1 (fun _ => (1 : ZMod 2)) j)) - LinearMap.id) :
      Submodule ℂ ((Fin 1 → ZMod 2) → ℂ)) = 1 := by
  have hb : (fun _ => (1 : ZMod 2)) ≠ (0 : Fin 1 → ZMod 2) := by
    intro h
    have h1 := congrFun h 0
    simp only [Pi.zero_apply] at h1
    exact one_ne_zero h1
  have h := finrank_stabilizerCode (wA 1 1) (wB 1 1 (fun _ => (1 : ZMod 2))) (wC 1)
    (single_hsq (fun _ => (1 : ZMod 2))) (single_hcomm (fun _ => (1 : ZMod 2)))
    (single_hind (fun _ => (1 : ZMod 2)) hb)
  rw [show (1 : ℕ) - 1 = 0 from rfl, pow_zero] at h
  exact h

/-- Witness: the empty generator family gives the whole space, of dimension `2 ^ n`. -/
theorem empty_finrank (n : ℕ) : Module.finrank ℂ
    (⨅ j : Fin 0, LinearMap.ker (Matrix.toLin' (wC 0 j
      • pauli (wA n 0 j) (wB n 0 (0 : Fin n → ZMod 2) j)) - LinearMap.id) :
      Submodule ℂ ((Fin n → ZMod 2) → ℂ)) = 2 ^ n := by
  have hind0 : LinearIndependent (ZMod 2)
      (fun j : Fin 0 => (wA n 0 j, wB n 0 (0 : Fin n → ZMod 2) j)) := by
    rw [Fintype.linearIndependent_iff]
    intro g _ i
    exact Fin.elim0 i
  have h := finrank_stabilizerCode (wA n 0) (wB n 0 0) (wC 0)
    (fun j => Fin.elim0 j) (fun j _ => Fin.elim0 j) hind0
  rw [Nat.sub_zero] at h
  exact h

/-- `Z` on the first qubit is nonzero. -/
theorem wB0_ne_zero : wB0 ≠ 0 := by
  intro h
  have h1 := congrFun h 0
  simp only [wB0, ite_true, Pi.zero_apply] at h1
  exact one_ne_zero h1

/-- Witness: repeating a generator breaks independence. -/
theorem dep_pair_not_independent : ¬ LinearIndependent (ZMod 2)
    (fun j : Fin 2 => (wA 2 2 j, wB 2 2 wB0 j)) := by
  intro hind
  have hsum : ∑ j : Fin 2, (fun _ => (1 : ZMod 2)) j • (wA 2 2 j, wB 2 2 wB0 j) = 0 := by
    have e0 : (wA 2 2 0, wB 2 2 wB0 0) = ((0 : Fin 2 → ZMod 2), wB0) := rfl
    have e1 : (wA 2 2 1, wB 2 2 wB0 1) = ((0 : Fin 2 → ZMod 2), wB0) := rfl
    rw [Fin.sum_univ_two]
    simp only [one_smul]
    rw [e0, e1, Prod.mk_add_mk, Cslib.CodingTheory.CSS.add_self_eq_zero,
      Cslib.CodingTheory.CSS.add_self_eq_zero]
    rfl
  have h01 := linearIndependent_iff'.mp hind Finset.univ (fun _ => (1 : ZMod 2)) hsum 0
    (Finset.mem_univ 0)
  exact one_ne_zero h01

/-- Witness: a repeated generator leaves a `2`-dimensional code, not `2 ^ (2 - 2)`. -/
theorem dep_pair_finrank : Module.finrank ℂ
    (⨅ j : Fin 2, LinearMap.ker (Matrix.toLin' (wC 2 j
      • pauli (wA 2 2 j) (wB 2 2 wB0 j)) - LinearMap.id) :
      Submodule ℂ ((Fin 2 → ZMod 2) → ℂ)) = 2 := by
  have h1 := finrank_stabilizerCode (wA 2 1) (wB 2 1 wB0) (wC 1)
    (single_hsq wB0) (single_hcomm wB0) (single_hind wB0 wB0_ne_zero)
  rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one] at h1
  have e1 : (⨅ j : Fin 1, LinearMap.ker (Matrix.toLin' (wC 1 j
      • pauli (wA 2 1 j) (wB 2 1 wB0 j)) - LinearMap.id))
      = LinearMap.ker (Matrix.toLin' ((1 : ℂ)
        • pauli (0 : Fin 2 → ZMod 2) wB0) - LinearMap.id) := by
    rw [show (fun j : Fin 1 => LinearMap.ker (Matrix.toLin' (wC 1 j
        • pauli (wA 2 1 j) (wB 2 1 wB0 j)) - LinearMap.id))
      = fun _ => LinearMap.ker (Matrix.toLin' ((1 : ℂ)
        • pauli (0 : Fin 2 → ZMod 2) wB0) - LinearMap.id) from rfl,
      iInf_const]
  have e2 : (⨅ j : Fin 2, LinearMap.ker (Matrix.toLin' (wC 2 j
      • pauli (wA 2 2 j) (wB 2 2 wB0 j)) - LinearMap.id))
      = LinearMap.ker (Matrix.toLin' ((1 : ℂ)
        • pauli (0 : Fin 2 → ZMod 2) wB0) - LinearMap.id) := by
    rw [show (fun j : Fin 2 => LinearMap.ker (Matrix.toLin' (wC 2 j
        • pauli (wA 2 2 j) (wB 2 2 wB0 j)) - LinearMap.id))
      = fun _ => LinearMap.ker (Matrix.toLin' ((1 : ℂ)
        • pauli (0 : Fin 2 → ZMod 2) wB0) - LinearMap.id) from rfl,
      iInf_const]
  rw [e2]
  rw [e1] at h1
  exact h1

/-- Witness: minus identity has zero Pauli part, so independence excludes it. -/
theorem neg_scalar_not_independent : ¬ LinearIndependent (ZMod 2)
    (fun j : Fin 1 => (wA 1 1 j, wB 1 1 (0 : Fin 1 → ZMod 2) j)) := by
  intro hind
  have hsum : ∑ i : Fin 1, (fun _ => (1 : ZMod 2)) i
      • (wA 1 1 i, wB 1 1 (0 : Fin 1 → ZMod 2) i) = 0 := by
    rw [Fin.sum_univ_one]
    show (1 : ZMod 2) • ((0 : Fin 1 → ZMod 2), (0 : Fin 1 → ZMod 2)) = 0
    rw [one_smul]
    rfl
  have h0 := Fintype.linearIndependent_iff.mp hind _ hsum 0
  exact one_ne_zero h0

/-- Witness: the `-1` scalar generator has trivial (`⊥`) code space. -/
theorem neg_scalar_codespace_bot :
    (⨅ j : Fin 1, LinearMap.ker (Matrix.toLin' (wCNeg 1 j
      • pauli (wA 1 1 j) (wB 1 1 (0 : Fin 1 → ZMod 2) j)) - LinearMap.id) :
      Submodule ℂ ((Fin 1 → ZMod 2) → ℂ)) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  rw [Submodule.mem_iInf] at hx
  have hx0 := hx 0
  rw [LinearMap.mem_ker, LinearMap.sub_apply] at hx0
  have hM : Matrix.toLin' (wCNeg 1 0
      • pauli (wA 1 1 0) (wB 1 1 (0 : Fin 1 → ZMod 2) 0)) x = -x := by
    have hP1 : pauli (0 : Fin 1 → ZMod 2) 0 = 1 := test_pauli_zero_one
    show Matrix.toLin' ((-1 : ℂ) • pauli (0 : Fin 1 → ZMod 2) 0) x = -x
    rw [Matrix.toLin'_apply, hP1, Matrix.smul_mulVec, Matrix.one_mulVec,
      neg_smul, one_smul]
  have hid : (LinearMap.id : ((Fin 1 → ZMod 2) → ℂ) →ₗ[ℂ]
      ((Fin 1 → ZMod 2) → ℂ)) x = x := rfl
  rw [hid, sub_eq_zero] at hx0
  rw [hM] at hx0
  have h2 : ∀ u : Fin 1 → ZMod 2, x u = 0 := by
    intro u
    have hu := congrFun hx0 u
    have h2a : x u + x u = 0 := by
      have h3 : x u + x u = x u + (-x) u := congrArg (x u + ·) hu.symm
      rw [h3]
      show x u + -(x u) = 0
      exact add_neg_cancel _
    have h4 : (2 : ℂ) * x u = 0 := by
      rw [two_mul]
      exact h2a
    exact (mul_eq_zero.mp h4).resolve_left two_ne_zero
  funext u
  simpa using h2 u

end CslibTest.CodingTheory.StabilizerCode
