/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Quantum.BernsteinVazirani

@[expose] public section

open MathlibExt.Quantum.BernsteinVazirani

/-- For one bit, `chi x s = (-1) ^ (x · s)` is `-1` when both bits are `1`. -/
example : chi (fun _ : Fin 1 => true) (fun _ => true) = -1 := by
  simp [chi, BooleanCube.cubeChi]

/-- For one bit, `chi x s` is `1` when the input bit is `0`. -/
example : chi (fun _ : Fin 1 => false) (fun _ => true) = 1 := by
  simp [chi, BooleanCube.cubeChi]

/-- For one bit, `chi x s` is `1` when the hidden bit is `0`. -/
example : chi (fun _ : Fin 1 => true) (fun _ => false) = 1 := by
  simp [chi, BooleanCube.cubeChi]

/-- The two inputs of one bit. -/
private theorem univ_fin_one_bool :
    (Finset.univ : Finset (Fin 1 → Bool)) = {fun _ => false, fun _ => true} := by
  decide

/-- Hidden string `1`, `β = true`: the amplitude at `t = s`, evaluated term by term, is `-1`. -/
example : ((2 : ℂ) ^ 1)⁻¹ * ∑ x : Fin 1 → Bool,
    chi x (fun _ => true) * affinePhase (fun _ => true) true x = -1 := by
  rw [univ_fin_one_bool, Finset.sum_pair (by decide)]
  simp [chi, affinePhase, BooleanCube.cubeChi]
  norm_num

/-- Hidden string `1`, `β = true`: the amplitude at `t = 0`, evaluated term by term, is `0`. -/
example : ((2 : ℂ) ^ 1)⁻¹ * ∑ x : Fin 1 → Bool,
    chi x (fun _ => false) * affinePhase (fun _ => true) true x = 0 := by
  rw [univ_fin_one_bool, Finset.sum_pair (by decide)]
  simp [chi, affinePhase, BooleanCube.cubeChi]

/-- `bv_amplitude` at the hidden string with `β = false` gives `1`. -/
example : ((2 : ℂ) ^ 1)⁻¹ * ∑ x : Fin 1 → Bool,
    chi x (fun _ => true) * affinePhase (fun _ => true) false x = 1 := by
  rw [bv_amplitude]
  simp

/-- `bv_amplitude` at the hidden string with `β = true` gives `-1`. -/
example : ((2 : ℂ) ^ 1)⁻¹ * ∑ x : Fin 1 → Bool,
    chi x (fun _ => true) * affinePhase (fun _ => true) true x = -1 := by
  rw [bv_amplitude]
  simp

/-- `bv_amplitude` off the hidden string gives `0`, also for `β = true`. -/
example : ((2 : ℂ) ^ 1)⁻¹ * ∑ x : Fin 1 → Bool,
    chi x (fun _ => false) * affinePhase (fun _ => true) true x = 0 := by
  rw [bv_amplitude, ite_eq_right]
  intro h
  simpa using congrFun h 0

/-- For one bit, distinct characters are orthogonal. -/
example : ∑ x : Fin 1 → Bool, chi x (fun _ => true) * chi x (fun _ => false) = 0 := by
  rw [chi_sum, ite_eq_right]
  intro h
  simpa using congrFun h 0

/-- For `n = 0`, orthogonality gives `2^0 = 1`. -/
example (s : Fin 0 → Bool) :
    ∑ x : Fin 0 → Bool, chi x s * chi x s = 1 := by
  rw [chi_sum]
  simp

end
