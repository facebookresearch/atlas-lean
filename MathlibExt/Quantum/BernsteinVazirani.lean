/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import MathlibExt.Analysis.Fourier.BooleanCube
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Tactic.FieldSimp
import MathlibExt.Analysis.Fourier.BooleanCubeInfluence

/-!
# Bernstein–Vazirani amplitude identity

Bitstrings are `x : Fin n → Bool`, with `true` for the bit `1`. For a hidden string `s` and a
bit `β`, the Bernstein–Vazirani algorithm queries the phase oracle of the affine function
`f x = (x · s) ⊕ β`, which multiplies the basis state `|x⟩` by `(-1) ^ f x`, between two
layers of Hadamard gates applied to `|0⟩`. The resulting amplitude of `|t⟩` is
`2⁻ⁿ ∑ₓ (-1) ^ (x · t) (-1) ^ f x`. This module proves that this sum is `(-1) ^ β` when `t = s`
and `0` otherwise (`bv_amplitude`). The Hadamard gates, the circuit, and measurement are not
formalized; the theorem is stated for the sum above.

The sign `(-1) ^ (x · s)` is `chi x s`, the Boolean-cube character `BooleanCube.cubeChi` of the
support of `s` evaluated at the complement of `x` (`cubeChi` reads `true` as `1` and `false` as
`-1`). Its orthogonality relation `chi_sum` is derived from
`BooleanCube.sum_cubeChi_mul_cubeChi_eq_ite`.

## References

* E. Bernstein and U. Vazirani, *Quantum complexity theory*, SIAM Journal on Computing 26(5)
  (1997).
-/

@[expose] public section

namespace MathlibExt.Quantum.BernsteinVazirani

open BooleanCube

/-- The sign `(-1) ^ (x · s)` of bitstrings `x` and `s`: the character `cubeChi` of the
support of `s`, evaluated at the complement of `x`, as a complex number. -/
def chi {n : ℕ} (x s : Fin n → Bool) : ℂ :=
  (cubeChi n (Finset.univ.filter fun i => s i = true) (fun i => !x i) : ℂ)

/-- `chi x s` is the product over positions of `-1` where both bits are `1`, and `1`
elsewhere, so it is `(-1) ^ (x · s)`. -/
theorem chi_eq_prod {n : ℕ} (x s : Fin n → Bool) :
    chi x s = ∏ i, if s i then (if x i then (-1 : ℂ) else 1) else 1 := by
  unfold chi cubeChi
  push_cast
  rw [Finset.prod_filter]
  refine Finset.prod_congr rfl fun i _ => ?_
  cases s i <;> cases x i <;> simp

/-- Character orthogonality: summing over all inputs gives `2^n` when the characters agree and
`0` otherwise. -/
theorem chi_sum {n : ℕ} (s t : Fin n → Bool) :
    ∑ x : Fin n → Bool, chi x s * chi x t
      = if s = t then (2 : ℂ) ^ n else 0 := by
  have hsupp : (Finset.univ.filter fun i => s i = true) =
      (Finset.univ.filter fun i => t i = true) ↔ s = t := by
    refine ⟨fun h => funext fun i => ?_, fun h => h ▸ rfl⟩
    have hi := congrArg (fun A => i ∈ A) h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, eq_iff_iff] at hi
    cases hs : s i <;> cases ht : t i <;> simp_all
  have hsum : ∑ x : Fin n → Bool, chi x s * chi x t
      = ((∑ y : BoolCube n, cubeChi n (Finset.univ.filter fun i => s i = true) y *
          cubeChi n (Finset.univ.filter fun i => t i = true) y : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    refine Fintype.sum_bijective (fun x i => !x i)
      (Function.Involutive.bijective fun x => funext fun i => Bool.not_not (x i)) _ _
      fun x => ?_
    simp [chi]
  rw [hsum, sum_cubeChi_mul_cubeChi_eq_ite]
  by_cases h : s = t
  · simp [h]
  · simp [h, mt hsupp.1 h]

/-- Phase `(-1) ^ f x` of the affine function `f x = (x · s) ⊕ β`, as a sign. -/
def affinePhase {n : ℕ} (s : Fin n → Bool) (β : Bool) (x : Fin n → Bool) : ℂ :=
  (if β then -1 else 1) * chi x s

/-- Bernstein–Vazirani amplitude: for the phase oracle of the affine function with hidden
string `s`, the normalized sum `2⁻ⁿ ∑ₓ (-1) ^ (x · t) (-1) ^ f x` is `(-1) ^ β` when `t = s` and
`0` otherwise. -/
theorem bv_amplitude {n : ℕ} (s t : Fin n → Bool) (β : Bool) :
    ((2 : ℂ) ^ n)⁻¹ * ∑ x : Fin n → Bool, chi x t * affinePhase s β x
      = if t = s then (if β then -1 else 1) else 0 := by
  have hfactor : ∀ x : Fin n → Bool, chi x t * affinePhase s β x
      = (if β then (-1 : ℂ) else 1) * (chi x t * chi x s) := by
    intro x
    unfold affinePhase
    ring
  have hsum : (∑ x : Fin n → Bool, chi x t * affinePhase s β x)
      = (if β then (-1 : ℂ) else 1) * (∑ x : Fin n → Bool, chi x t * chi x s) := by
    rw [Finset.sum_congr rfl (fun x _ => hfactor x)]
    rw [← Finset.mul_sum]
  rw [hsum, chi_sum]
  by_cases h : t = s
  · simp only [ite_eq_left h]
    have h2 : ((2 : ℂ) ^ n) ≠ 0 := pow_ne_zero n (by norm_num)
    field_simp
  · simp only [ite_eq_right h, mul_zero]

end MathlibExt.Quantum.BernsteinVazirani

end
