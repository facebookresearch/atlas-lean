/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinFastQMaskCentral

/-! Four exact XOR folds replace the variable-index twelve-bit parity lookup.
Both arbitrary input masks and every original central coefficient are retained. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The even parity of precisely the twelve low bits, using four exact XOR folds. -/
def generatedNinthLowerSpinParityCircuitTwelve (n : ℕ) : Bool :=
  let v := n % 4096
  let a := Nat.xor v (v / 256)
  let b := Nat.xor a (a / 16)
  let c := Nat.xor b (b / 4)
  let d := Nat.xor c (c / 2)
  !d.testBit 0

set_option maxHeartbeats 10000000 in
-- Check all 4,096 twelve-bit values in sixteen complete 256-value blocks.
private theorem parity_certificate : ∀ n : Fin 4096,
    generatedNinthLowerSpinParityCircuitTwelve n.val =
      generatedAxisGlobalFastParityTwelve n.val := by
  have h : ∀ a : Fin 16, ∀ b : Fin 256,
      generatedNinthLowerSpinParityCircuitTwelve (256 * a.val + b.val) =
        generatedAxisGlobalFastParityTwelve (256 * a.val + b.val) := by
    decide +kernel
  intro n
  have hb : n.val / 256 < 16 := by have hn := n.isLt; omega
  have hp := h ⟨n.val / 256, hb⟩ ⟨n.val % 256, Nat.mod_lt _ (by decide)⟩
  have he : 256 * (n.val / 256) + n.val % 256 = n.val := by omega
  simpa only [he] using hp

/-- The circuit equals the original complete twelve-bit lookup for every natural number. -/
theorem generatedNinth_lower_spin_parity_circuit_actual (n : ℕ) :
    generatedNinthLowerSpinParityCircuitTwelve n =
      generatedAxisGlobalFastParityTwelve (n % 4096) := by
  have h := parity_certificate ⟨n % 4096, Nat.mod_lt _ (by decide)⟩
  simpa only [generatedNinthLowerSpinParityCircuitTwelve, Nat.mod_mod] using h

/-- Circuit parity evaluates the exact original twelve-bit natural-number dot. -/
def generatedNinthLowerSpinCircuitDotTwelve (a b : ℕ) : ℕ :=
  if !(generatedNinthLowerSpinParityCircuitTwelve (a &&& b)) then 1 else 0

/-- Two complete circuit parities retain the exact twenty-four-bit dot. -/
def generatedNinthLowerSpinCircuitDot24 (a b : ℕ) : ℕ :=
  if Bool.xor (generatedNinthLowerSpinParityCircuitTwelve (a &&& b))
      (generatedNinthLowerSpinParityCircuitTwelve ((a >>> 12) &&& (b >>> 12)))
    then 1 else 0

/-- The circuit dot equals the previously verified complete twelve-bit dot. -/
theorem generatedNinth_lower_spin_circuit_dot_twelve (a b : ℕ) :
    generatedNinthLowerSpinCircuitDotTwelve a b = generatedNinthLowerSpinFastDotTwelve a b := by
  unfold generatedNinthLowerSpinCircuitDotTwelve generatedNinthLowerSpinFastDotTwelve
  rw [generatedNinth_lower_spin_parity_circuit_actual]

/-- The circuit dot equals the previously verified complete twenty-four-bit dot. -/
theorem generatedNinth_lower_spin_circuit_dot24 (a b : ℕ) :
    generatedNinthLowerSpinCircuitDot24 a b = generatedNinthLowerSpinFastDot24 a b := by
  unfold generatedNinthLowerSpinCircuitDot24 generatedNinthLowerSpinFastDot24
  simp_rw [generatedNinth_lower_spin_parity_circuit_actual]

/-- Every selected original triangular row is evaluated by the exact circuit dot. -/
def generatedNinthLowerSpinCircuitQMaskPhase (rows : Fin 24 → ℕ) (v : ℕ) : ℕ :=
  monsterCo1GeometryBinaryMaskSum (List.ofFn (fun i : Fin 24 =>
    if v.testBit i.val then generatedNinthLowerSpinCircuitDot24 (rows i) v else 0))

/-- The entire central polynomial retains every triangular row and linear correction bit. -/
def generatedNinthLowerSpinCircuitQMaskCentral (rows : Fin 24 → ℕ) (coeff v : ℕ) : ℕ :=
  Nat.xor (generatedNinthLowerSpinCircuitQMaskPhase rows v)
    (generatedNinthLowerSpinCircuitDot24 coeff v)

/-- The circuit evaluates the full original central value for arbitrary masks and rows. -/
theorem generatedNinth_lower_spin_circuit_q_mask_central
    (rows : Fin 24 → ℕ) (coeff v : ℕ) :
    generatedNinthLowerSpinCircuitQMaskCentral rows coeff v =
      generatedAxisGlobalQMaskCentral rows coeff v := by
  rw [← generatedNinth_lower_spin_fast_q_mask_central]
  unfold generatedNinthLowerSpinCircuitQMaskCentral generatedNinthLowerSpinFastQMaskCentral
    generatedNinthLowerSpinCircuitQMaskPhase generatedNinthLowerSpinFastQMaskPhase
  simp_rw [generatedNinth_lower_spin_circuit_dot24]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
