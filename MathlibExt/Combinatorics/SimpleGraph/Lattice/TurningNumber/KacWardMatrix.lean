/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.ZMod.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Tactic.FinCases

/-!
# The Kac-Ward matrix of the square-lattice torus

Directed edges of the `L × L` torus and the Kac-Ward transition matrix with turning phases.

A dart of the torus `ℤ_L × ℤ_L` is a site together with one of the four lattice directions
`0, 1, 2, 3` (east, north, west, south). The Kac-Ward matrix `ons_KWmat L x ω` has entry `x · w`
from a dart `d₁` to a dart `d₂` starting at the head of `d₁`, where the turn weight `w` is `1` for
going straight, `ω` for a left turn, `ω⁻¹` for a right turn, and `0` for a U-turn. With
`ω = e^{iπ/4}` this is the matrix of Kac and Ward, whose loop expansion attaches to each closed
non-backtracking walk the phase `e^{iθ/2}` of its total turning angle `θ`. The matrix commutes with
lattice translations.

## Main definitions

* `ons_KWmat`: the Kac-Ward transition matrix on darts
* `ons_turnW`: the turn weight

## Main results

* `ons_KWmat_translation_invariant`: translation invariance of the Kac-Ward matrix

## References

* M. Kac and J. C. Ward, *A combinatorial solution of the two-dimensional Ising model*, Phys. Rev.
  88 (1952) 1332-1337
* S. Sherman, *Combinatorial aspects of the Ising model for ferromagnetism. I. A conjecture of
  Feynman on paths and graphs*, J. Math. Phys. 1 (1960) 202-217
-/

@[expose] public section

namespace StatMech.Onsager

/-! ### Sites, directions and darts -/

/-- The sites `ℤ_L × ℤ_L` of the `L × L` square-lattice torus. -/
abbrev ons_V (L : ℕ) := ZMod L × ZMod L

/-- The neighbor of a site in direction `μ`: `0` east, `1` north, `2` west, `3` south. -/
def ons_dirStep (L : ℕ) (μ : Fin 4) (s : ZMod L × ZMod L) : ZMod L × ZMod L :=
  match μ with
  | 0 => (s.1 + 1, s.2)
  | 1 => (s.1, s.2 + 1)
  | 2 => (s.1 - 1, s.2)
  | 3 => (s.1, s.2 - 1)

/-- Darts (directed edges) of the torus: a starting site and a direction. -/
abbrev ons_Dart (L : ℕ) := (ZMod L × ZMod L) × Fin 4

/-! ### Turn weights and the Kac-Ward matrix -/

/-- The turn weight from direction `μ` to direction `ν`: `1` straight, `ω` for a left turn, `0` for
a U-turn, `ω⁻¹` for a right turn. -/
noncomputable def ons_turnW (ω : ℂ) (μ ν : Fin 4) : ℂ :=
  if ν = μ then 1
  else if ν = μ + 1 then ω
  else if ν = μ + 2 then 0
  else ω⁻¹

/-- The Kac-Ward matrix: the entry from `d₁` to `d₂` is `x * ons_turnW ω d₁.2 d₂.2` when `d₂` starts
at the head of `d₁`, and `0` otherwise. -/
noncomputable def ons_KWmat (L : ℕ) (x ω : ℂ) : Matrix (ons_Dart L) (ons_Dart L) ℂ :=
  fun d₂ d₁ => if d₂.1 = ons_dirStep L d₁.2 d₁.1 then x * ons_turnW ω d₁.2 d₂.2 else 0

/-- Translation of a dart by a lattice vector `t`. -/
def ons_shiftDart (L : ℕ) (t : ZMod L × ZMod L) (d : ons_Dart L) : ons_Dart L :=
  ((d.1.1 + t.1, d.1.2 + t.2), d.2)

/-! ### Translation invariance -/

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
  · rw [ite_eq_left (hiff.mpr hc), ite_eq_left hc]
  · rw [ite_eq_right (fun h => hc (hiff.mp h)), ite_eq_right hc]

end StatMech.Onsager
