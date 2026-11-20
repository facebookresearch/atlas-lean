/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace StatMech.Onsager


abbrev ons_V (L : ℕ) := ZMod L × ZMod L


def ons_dirStep (L : ℕ) (μ : Fin 4) (s : ZMod L × ZMod L) : ZMod L × ZMod L :=
  match μ with
  | 0 => (s.1 + 1, s.2)
  | 1 => (s.1, s.2 + 1)
  | 2 => (s.1 - 1, s.2)
  | 3 => (s.1, s.2 - 1)


abbrev ons_Dart (L : ℕ) := (ZMod L × ZMod L) × Fin 4



noncomputable def ons_turnW (ω : ℂ) (μ ν : Fin 4) : ℂ :=
  if ν = μ then 1
  else if ν = μ + 1 then ω
  else if ν = μ + 2 then 0
  else ω⁻¹



noncomputable def ons_KWmat (L : ℕ) (x ω : ℂ) : Matrix (ons_Dart L) (ons_Dart L) ℂ :=
  fun d₂ d₁ => if d₂.1 = ons_dirStep L d₁.2 d₁.1 then x * ons_turnW ω d₁.2 d₂.2 else 0


def ons_shiftDart (L : ℕ) (t : ZMod L × ZMod L) (d : ons_Dart L) : ons_Dart L :=
  ((d.1.1 + t.1, d.1.2 + t.2), d.2)



theorem ons_turnW_straight (ω : ℂ) (μ : Fin 4) : ons_turnW ω μ μ = 1 := by
  simp [ons_turnW]

theorem ons_turnW_uturn (ω : ℂ) (μ : Fin 4) : ons_turnW ω μ (μ + 2) = 0 := by
  have h1 : ¬ (μ + 2 = μ) := by fin_cases μ <;> decide
  have h2 : ¬ (μ + 2 = μ + 1) := by fin_cases μ <;> decide
  simp [ons_turnW, h1, h2]



theorem ons_dirStep_shift (L : ℕ) (μ : Fin 4) (t s : ZMod L × ZMod L) :
    ons_dirStep L μ (s.1 + t.1, s.2 + t.2)
      = ((ons_dirStep L μ s).1 + t.1, (ons_dirStep L μ s).2 + t.2) := by
  fin_cases μ <;>
    simp [ons_dirStep] <;>
    ring



theorem ons_KWmat_translation_invariant (L : ℕ) (x ω : ℂ)
    (t : ZMod L × ZMod L) (d₁ d₂ : ons_Dart L) :
    ons_KWmat L x ω (ons_shiftDart L t d₂) (ons_shiftDart L t d₁)
      = ons_KWmat L x ω d₂ d₁ := by
  unfold ons_KWmat ons_shiftDart
  simp only
  have hstep : ons_dirStep L d₁.2 (d₁.1.1 + t.1, d₁.1.2 + t.2)
      = ((ons_dirStep L d₁.2 d₁.1).1 + t.1, (ons_dirStep L d₁.2 d₁.1).2 + t.2) :=
    ons_dirStep_shift L d₁.2 t d₁.1
  rw [hstep]
  have hiff : ((d₂.1.1 + t.1, d₂.1.2 + t.2)
      = ((ons_dirStep L d₁.2 d₁.1).1 + t.1, (ons_dirStep L d₁.2 d₁.1).2 + t.2))
      ↔ (d₂.1 = ons_dirStep L d₁.2 d₁.1) := by
    rw [Prod.ext_iff, Prod.ext_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨add_right_cancel h1, add_right_cancel h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by rw [h1], by rw [h2]⟩
  by_cases hc : d₂.1 = ons_dirStep L d₁.2 d₁.1
  · rw [if_pos (hiff.mpr hc), if_pos hc]
  · rw [if_neg (fun h => hc (hiff.mp h)), if_neg hc]

end StatMech.Onsager
