/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PathSignature.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

open MeasureTheory MathlibExt.Analysis.PathSignature

namespace MathlibExtTest.Analysis.PathSignature.Basic

/-- The velocity of the path of Chevyrev–Kormilitzin, arXiv:1603.03788v2, Example 1.18: up by
`e₂` on `[0, 1]`, then left by `3 e₁` on `[1, 2]` (letters `0 = e₁`, `1 = e₂`). -/
noncomputable def lPath (i : Fin 2) (u : ℝ) : ℝ :=
  if u ≤ 1 then (if i = 1 then 1 else 0) else (if i = 0 then -3 else 0)

theorem lPath_antitone (i : Fin 2) : Antitone (lPath i) := by
  intro a b hab
  by_cases ha : a ≤ 1 <;> by_cases hb : b ≤ 1 <;> fin_cases i <;> simp [lPath, ha, hb] <;>
    linarith

theorem lPath_integrable (i : Fin 2) (a b : ℝ) : IntervalIntegrable (lPath i) volume a b :=
  (lPath_antitone i).intervalIntegrable

/-- Chen's identity and the linear-segment formula reproduce the Lévy-area computation of
Example 1.18: `S^{21}_{0,2} = −3`. -/
example : signature lPath 0 2 [1, 0] = -3 := by
  have h1 : signature lPath 0 1 = tensorExp (((1 : ℝ) - 0) • ![0, 1]) :=
    signature_of_eqOn_Ioc (v := lPath) (s := 0) (t := 1) ![0, 1] (by norm_num) fun i u hu => by
      fin_cases i <;> simp [lPath, hu.2]
  have h2 : signature lPath 1 2 = tensorExp (((2 : ℝ) - 1) • ![-3, 0]) :=
    signature_of_eqOn_Ioc (v := lPath) (s := 1) (t := 2) ![-3, 0] (by norm_num) fun i u hu => by
      fin_cases i <;> simp [lPath, not_le.mpr hu.1]
  rw [signature_chen lPath_integrable 0 1 2, h1, h2]
  norm_num [Finset.sum_range_succ, tensorExp]

/-- The same value through the piecewise-linear formula `S = exp(Δ₀) ⊗ exp(Δ₁)`. -/
example : signature lPath 0 2 [1, 0] = -3 := by
  have hx : ∀ (j : ℕ) (i : Fin 2), ∀ u ∈ Set.Ioc ((j : ℕ) : ℝ) ((j + 1 : ℕ) : ℝ),
      lPath i u = (if j = 0 then ![0, 1] else ![-3, 0]) i := by
    intro j i u hu
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · have : u ≤ 1 := by simpa using hu.2
      fin_cases i <;> simp [lPath, this]
    · have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
      have : ¬ u ≤ 1 := not_le.mpr (lt_of_le_of_lt hj' hu.1)
      fin_cases i <;> simp [lPath, this, hj.ne']
  have h := signature_piecewise_linear lPath_integrable (fun j : ℕ => (j : ℝ)) Nat.mono_cast
    (fun j => if j = 0 then ![0, 1] else ![-3, 0]) hx 2
  have h2 : signature lPath 0 2 = signature lPath ((0 : ℕ) : ℝ) ((2 : ℕ) : ℝ) := by norm_num
  rw [h2, h]
  simp [List.range_succ, tensorMul, tensorOne, tensorExp, Finset.sum_range_succ]

/-- Chen's identity is not vacuous: on the zero path every nonempty word has signature `0`. -/
example (w : List (Fin 3)) (hw : w ≠ []) :
    signature (fun _ _ => (0 : ℝ)) 0 5 w = 0 := by
  have h := signature_of_eqOn_Ioc (v := fun (_ : Fin 3) (_ : ℝ) => (0 : ℝ)) (s := 0) (t := 5) 0
    (by norm_num)
    (fun _ _ _ => rfl)
  rw [h, tensorExp]
  obtain ⟨i, w', rfl⟩ := List.exists_cons_of_ne_nil hw
  simp

/-- The first level of the signature is the increment: for the unit-speed path along `e₀`,
`S^{0}_{0,t} = t`. -/
example (t : ℝ) : signature (fun (_ : Fin 1) (_ : ℝ) => (1 : ℝ)) 0 t [0] = t := by
  simp [signature_singleton]

/-- Example 1.6: for the unit-speed path `X_t = t`, `S^{1…1}_{0,t} = t^k / k!`. -/
example (k : ℕ) (t : ℝ) :
    signature (fun (_ : Fin 1) (_ : ℝ) => (1 : ℝ)) 0 t (List.replicate k 0) =
      t ^ k / k.factorial := by
  rw [signature_replicate continuous_const]
  simp

/-- `S(X)_{s,·}` solves `dS = S ⊗ dX`: `d/dt S^{01}_{s,t} = S^0_{s,t} v¹(t)`. -/
example (v : Fin 2 → ℝ → ℝ) (hv : ∀ i, Continuous (v i)) (s t : ℝ) :
    HasDerivAt (fun t => signature v s t [0, 1]) (signature v s t [0] * v 1 t) t :=
  hasDerivAt_signature_concat hv s [0] 1 t

/-- Theorem 1.25 for the L-shaped path of Example 1.18: its signature times that of its reversal
is `1`; at the word `21` this is `S^{21}_{0,2} + S^2_{0,2} S(←X)^1_{0,2} + S(←X)^{21}_{0,2} = 0`. -/
example : tensorMul (signature lPath 0 2) (signature (fun i u => -lPath i (0 + 2 - u)) 0 2)
    [1, 0] = 0 := by
  rw [tensorMul_signature_reverse lPath_integrable 0 2]
  simp [tensorOne]

/-- The reversed path runs the original backwards: `S(←X)^w_{a,t} = S(X)^w_{b,a+b−t}`. -/
example (v : Fin 2 → ℝ → ℝ) : signature (fun i u => -v i (0 + 1 - u)) 0 1 [0] =
    signature v 1 0 [0] := by
  rw [signature_reverse_eq]
  norm_num

/-- Reparametrisation: running a path at double speed, `S(X_{2·})_{0,1} = S(X)_{0,2}`. -/
example (v : Fin 2 → ℝ → ℝ) (hv : ∀ i, Continuous (v i)) (w : List (Fin 2)) :
    signature (fun i u => v i (2 * u) * 2) 0 1 w = signature v 0 2 w := by
  have h := signature_comp hv (ψ := fun u => 2 * u) (ψ' := fun _ => 2)
    (fun x => by simpa using HasDerivAt.const_mul (2 : ℝ) (hasDerivAt_id x)) continuous_const 0 1 w
  simpa using h

/-- Equation (22) at the word `12`: `S(←X)^{12}_{a,b} = S(X)^{21}_{a,b}`. -/
example (v : Fin 2 → ℝ → ℝ) (hv : ∀ i, Continuous (v i)) (a b : ℝ) :
    signature (fun i u => -v i (a + b - u)) a b [0, 1] = signature v a b [1, 0] := by
  rw [signature_reverse hv]
  simp

/-- First-letter recursion at a two-letter word. -/
example (v : Fin 2 → ℝ → ℝ) (hv : ∀ i, Continuous (v i)) (c b : ℝ) :
    signature v c b [0, 1] = ∫ r in c..b, v 0 r * signature v r b [1] :=
  signature_cons hv c b 0 [1]

end MathlibExtTest.Analysis.PathSignature.Basic
