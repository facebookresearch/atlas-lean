/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.DiophantineApproximation.Basic
import MathlibExt.NumberTheory.DiophantineApproximation.BakerDavenportNearestIntegerCore

namespace MetaMathlibExt

@[expose] public section

/-- Baker–Davenport reduction, absolute-value form, with only the hypotheses the argument
uses: if `ε = ‖μq‖ - M‖κq‖` is positive, no `r ≤ M` and `w ≥ log (Aq/ε) / log B` satisfy
`|rκ - s + μ| < A B⁻ʷ`. `bakerDavenport_reduction_absolute` is the source-shaped form. -/
theorem bakerDavenport_reduction_absolute_general
    (M q : ℕ) (hq : 0 < q)
    (kappa A mu B epsilon : ℝ)
    (hA : 0 < A) (hB : 1 < B)
    (hepsilon : epsilon = |mu * (q : ℝ) - (round (mu * (q : ℝ)) : ℝ)| -
      (M : ℝ) * |kappa * (q : ℝ) - (round (kappa * (q : ℝ)) : ℝ)|)
    (hepsilonpos : 0 < epsilon) :
    ¬∃ (r s w : ℕ), r ≤ M ∧
      (w : ℝ) ≥ Real.log (A * (q : ℝ) / epsilon) / Real.log B ∧
      |(r : ℝ) * kappa - (s : ℝ) + mu| < A * (B⁻¹) ^ w := by
  rintro ⟨r, s, w, hle, hwlog, hlt⟩
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hlogB : 0 < Real.log B := Real.log_pos hB
  have hAq : 0 < A * (q : ℝ) / epsilon := by positivity
  have h1 : Real.log (A * (q : ℝ) / epsilon) ≤ (w : ℝ) * Real.log B := by
    rw [ge_iff_le, div_le_iff₀ hlogB] at hwlog
    exact hwlog
  have h2 : Real.log (A * (q : ℝ) / epsilon) ≤ Real.log (B ^ w) := by
    rw [Real.log_pow]
    exact h1
  have hBpos : (0 : ℝ) < B := by linarith
  have hBwpos : (0 : ℝ) < B ^ w := pow_pos hBpos w
  have hBw : A * (q : ℝ) / epsilon ≤ B ^ w :=
    (Real.log_le_log_iff hAq hBwpos).mp h2
  have hexp : A * (B⁻¹) ^ w ≤ epsilon / (q : ℝ) := by
    rw [inv_pow, le_div_iff₀ hqR]
    have h3 : A * (q : ℝ) ≤ (B ^ w) * epsilon := by
      rw [div_le_iff₀ hepsilonpos] at hBw
      linarith
    have hBwne : (B ^ w) ≠ 0 := ne_of_gt hBwpos
    have h5 : A * (B ^ w)⁻¹ * (q : ℝ) = (A * (q : ℝ)) * (B ^ w)⁻¹ := by ring
    have h6 : (A * (q : ℝ)) * (B ^ w)⁻¹ ≤ ((B ^ w) * epsilon) * (B ^ w)⁻¹ :=
      mul_le_mul_of_nonneg_right h3 (le_of_lt (inv_pos.mpr hBwpos))
    have h7 : ((B ^ w) * epsilon) * (B ^ w)⁻¹ = epsilon := by
      field_simp
    linarith
  have hLamlt : |(r : ℝ) * kappa - (s : ℝ) + mu| < epsilon / (q : ℝ) :=
    lt_of_lt_of_le hlt hexp
  have hcore := nearestInteger_reduction_core q M r kappa mu s hle epsilon hepsilon
  push_cast at hcore
  rw [lt_div_iff₀ hqR] at hLamlt
  linarith


set_option linter.unusedVariables false in
/-- Absolute-value Baker–Davenport reduction lemma.

Concept `baker_davenport_reduction_absolute`, semantic id
`jis_grounded_3d649f47290c78b9a73677c9`.
Source: Eric F. Bravo, Carlos A. Gomez, and Florian Luca, "Product of
Consecutive Tribonacci Numbers With Only One Distinct Digit," Journal of
Integer Sequences 22 (2019), Article 19.6.3, Lemma `bd`, lines 285–292.
Source URL `https://cs.uwaterloo.ca/journals/JIS/VOL22/Gomez/gomez3.tex`.
Source-file SHA-256
`06ab2807874c97cf44007c561d48576611214b0fa0ab6ed55c61470d8ba7c0e6`;
exact-span SHA-256
`cc488ea946e7229300ad0b1a00befe1e523c8a5b97331a1d79e04c8f40429fe4`.

Here `|x - round x|` formalizes distance to the nearest integer, and this
declaration is the absolute-value variant of the cited lemma: the final linear
form `(r : ℝ) * kappa - (s : ℝ) + mu` appears inside absolute-value bars with
a two-sided strict inequality.
It follows from `bakerDavenport_reduction_absolute_general`. The hypotheses `hM`,
`hkappa`, `j` and `hq`, and the positivity conditions on `r`, `s`, `w` and the linear form,
are unused and keep the source's shape; `hqM` only supplies `0 < q`.
Proves `Wanted` entry `bakerDavenport_reduction_absolute`.
-/
@[nolint unusedArguments] -- `hkappa` keeps the `Wanted` entry's statement
theorem bakerDavenport_reduction_absolute
    (M : ℕ) (hM : 0 < M)
    (kappa : ℝ) (hkappa : Irrational kappa)
    (j : ℕ) (q : ℕ)
    (hq : q = (kappa.convergent j).den)
    (hqM : 6 * M < q)
    (A mu B epsilon : ℝ)
    (hA : 0 < A) (hB : 1 < B)
    (hepsilon : epsilon = |mu * (q : ℝ) - (round (mu * (q : ℝ)) : ℝ)| -
      (M : ℝ) * |kappa * (q : ℝ) - (round (kappa * (q : ℝ)) : ℝ)|)
    (hepsilonpos : 0 < epsilon) :
    ¬∃ (r s w : ℕ), 0 < r ∧ 0 < s ∧ 0 < w ∧ r ≤ M ∧
      (w : ℝ) ≥ Real.log (A * (q : ℝ) / epsilon) / Real.log B ∧
      0 < |(r : ℝ) * kappa - (s : ℝ) + mu| ∧
      |(r : ℝ) * kappa - (s : ℝ) + mu| < A * (B⁻¹) ^ w := by
  rintro ⟨r, s, w, -, -, -, hle, hwlog, -, hlt⟩
  exact bakerDavenport_reduction_absolute_general M q (by omega) kappa A mu B epsilon hA hB
    hepsilon hepsilonpos ⟨r, s, w, hle, hwlog, hlt⟩

end

end MetaMathlibExt
