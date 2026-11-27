/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.ODE.PWMPrimitiveBound

@[expose] public section

open MathlibExt.Analysis.ODE.PWMPrimitiveBound

namespace MathlibExtTest.Analysis.ODE.PWMPrimitiveBound

/-- The half-duty primitive at half period is exactly `1/4`. -/
example : pwmPrimitive 1 (fun _ => 1 / 2) (1 / 2) = 1 / 4 :=
  pwmPrimitive_half_half

/-- Duty `2` (outside `[0, 1]`) gives primitive `-t`, breaking the envelope. -/
example (ε t : ℝ) (hε : 0 < ε) : pwmPrimitive ε (fun _ => 2) t = -t :=
  pwmPrimitive_two ε t hε

/-- The headline bound on a constant half duty: the primitive at
half period (`1/4`) is within the envelope `1 * (1 + 0) = 1`. -/
example : |pwmPrimitive 1 (fun _ => 1 / 2) (1 / 2)| ≤ 1 * (1 + 0 * 1 / 2) :=
  abs_pwmPrimitive_le 1 1 0 (fun _ => 1 / 2) (by norm_num) (by norm_num)
    (fun _ _ => ⟨by norm_num, by norm_num⟩) (LipschitzWith.const (1 / 2 : ℝ)).lipschitzOnWith
    (1 / 2) ⟨by norm_num, by norm_num⟩

/-- One full constant-duty cycle has zero discrepancy integral,
meeting the cycle bound `0 * 1^2 / 2 = 0`. -/
example : |∫ u in (0 : ℝ)..(1 : ℝ), (pwmSignal 1 (fun _ => 1 / 2) u - (fun _ => 1 / 2) u)| ≤
    (0 : ℝ) * 1 ^ 2 / 2 := by
  have h := abs_pwmPrimitive_cycle_le 1 1 0 (fun _ => 1 / 2) 0 (by norm_num)
    (fun _ _ => ⟨by norm_num, by norm_num⟩) (LipschitzWith.const (1 / 2 : ℝ)).lipschitzOnWith
    (by norm_num)
  norm_num at h
  have h2 : (∫ u in (0 : ℝ)..(1 : ℝ), (pwmSignal 1 (fun _ => 1 / 2) u - (fun _ => 1 / 2) u)) = 0 := h
  rw [h2]
  norm_num

/-- The sharp constant-duty envelope at half duty and `ε = 1`:
the primitive stays in `[0, 1/4]` for every `t ≥ 0`. -/
example (t : ℝ) (ht : 0 ≤ t) : pwmPrimitive 1 (fun _ => 1 / 2) t ∈ Set.Icc 0 (1 / 4) := by
  have h := pwmPrimitive_const_mem_Icc 1 (1 / 2) t (by norm_num) ⟨by norm_num, by norm_num⟩ ht
  norm_num at h ⊢
  exact h

/-- The PWM signal is interval integrable, for any carrier length and duty. -/
example (ε : ℝ) (d : ℝ → ℝ) (a b : ℝ) :
    IntervalIntegrable (pwmSignal ε d) MeasureTheory.volume a b :=
  intervalIntegrable_pwmSignal ε d a b

end MathlibExtTest.Analysis.ODE.PWMPrimitiveBound
