/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Epidemiology.SIRAsymptotics

/-! Tests for SIR long-time behaviour: the constructed solution at a concrete epidemic initial
state has limits obeying the final-size equation, with a uniquely determined `S∞`; the `β = 0`
root; and the explicit decaying solution `I = e^{-t}`. -/

open Real Set Filter
open scoped Topology

namespace MathlibExtTest.Biology.Epidemiology.SIRAsymptotics

open MathlibExt.Biology.Epidemiology.SIR

/-- At `(S₀, I₀, R₀) = (99/100, 1/100, 0)`, `N = 1`, `β = 2`, `γ = 1`: the constructed solution
converges, the epidemic dies out, `S∞` solves `S∞ = 0.99 e^{-2 (1 - S∞)}`, and it is the only
root `≤ 0.99`. -/
example : ∃ S I R : ℝ → ℝ, IsSolution 2 1 1 S I R ∧ S 0 = 99 / 100 ∧ ∃ Sinf : ℝ,
    Tendsto S atTop (𝓝 Sinf) ∧ Tendsto I atTop (𝓝 0) ∧
    Sinf = 99 / 100 * exp (-(2 * (1 - Sinf))) ∧
    ∀ x ≤ 99 / 100, x = 99 / 100 * exp (-(2 * (1 - x))) → x = Sinf := by
  obtain ⟨S, I, R, h, hS, hI, hR, -⟩ :=
    exists_isSolution_nonneg (β := 2) (N := 1) zero_le_one (S₀ := 99 / 100) (I₀ := 1 / 100)
      (R₀ := 0) (by norm_num) (by norm_num) le_rfl
  obtain ⟨Sinf, Rinf, hSl, hIl, -, -, hle, -, hfs⟩ := h.tendsto_final_size (by norm_num)
    one_pos zero_le_one (by rw [hS]; norm_num) (by rw [hI]; norm_num) (by rw [hR])
  rw [hS, hI] at hfs
  rw [hS] at hle
  have hform : ∀ x : ℝ, -(2 / 1 * (99 / 100 + 1 / 100 - x) / 1) = -(2 * (1 - x)) :=
    fun x => by ring
  rw [hform] at hfs
  refine ⟨S, I, R, h, hS, Sinf, hSl, hIl, hfs, fun x hx hxe => ?_⟩
  refine final_size_root_unique (β := 2) (γ := 1) (N := 1) (S₀ := 99 / 100) (I₀ := 1 / 100)
    (by norm_num) one_pos one_pos (by norm_num) (by norm_num) hx hle ?_ ?_
  · rwa [hform]
  · rwa [hform]

/-- No transmission: the only root `≤ S₀` of the final-size equation is `S₀`. -/
example (S₀ x : ℝ) (hS₀ : 0 ≤ S₀) (hx : x ≤ S₀)
    (hxe : x = S₀ * exp (-(0 / 1 * (S₀ + 1 - x) / 1))) : x = S₀ :=
  final_size_root_unique le_rfl one_pos one_pos hS₀ one_pos hx le_rfl hxe (by simp)

/-- On the explicit solution `S = 1`, `I = e^{-t}`, `R = 1 - e^{-t}` (`β = 0`, `γ = 1`, `N = 1`)
the theorem gives `S∞ = 1` and `I → 0`. -/
example : Tendsto (fun t : ℝ => exp (-t)) atTop (𝓝 0) ∧ ∃ Sinf : ℝ,
    Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 Sinf) ∧ Sinf = 1 := by
  have h : IsSolution 0 1 1 (fun _ => 1) (fun t => exp (-t)) (fun t => 1 - exp (-t)) :=
    ⟨fun t _ => by simpa using hasDerivAt_const t (1 : ℝ),
      fun t _ => by simpa using (hasDerivAt_neg t).exp,
      fun t _ => by simpa using ((hasDerivAt_neg t).exp).const_sub 1⟩
  obtain ⟨Sinf, -, hSl, hIl, -, -, -, -, hfs⟩ :=
    h.tendsto_final_size le_rfl one_pos zero_le_one zero_le_one (by simp) (by simp)
  refine ⟨hIl, Sinf, hSl, ?_⟩
  simpa using hfs

/-- `S` is antitone for the constructed solution at the concrete state. -/
example : ∃ S I R : ℝ → ℝ, IsSolution 2 1 1 S I R ∧ S 0 = 99 / 100 ∧ AntitoneOn S (Ici 0) := by
  obtain ⟨S, I, R, h, hS, hI, hR, -⟩ :=
    exists_isSolution_nonneg (β := 2) (N := 1) zero_le_one (S₀ := 99 / 100) (I₀ := 1 / 100)
      (R₀ := 0) (by norm_num) (by norm_num) le_rfl
  exact ⟨S, I, R, h, hS, h.antitoneOn_susceptible (by norm_num) zero_le_one zero_le_one
    (by rw [hS]; norm_num) (by rw [hI]; norm_num) (by rw [hR])⟩

end MathlibExtTest.Biology.Epidemiology.SIRAsymptotics
