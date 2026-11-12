/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FK.TwoPointPositiveFull

namespace StatMech

namespace IsingFK

open StatMech.Lattice

variable {d : ℕ}



def HasLongRangeOrder (corr : ℝ → Site d → ℝ) (beta : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ x : Site d, c ≤ corr beta x



def HasSpatialDecay (corr : ℝ → Site d → ℝ) (beta : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∃ n : ℕ, ∀ x : Site d,
    x ∉ box d n → corr beta x < epsilon












theorem longRangeOrder_across_critical_of_fk
    (corr : ℝ → Site d → ℝ) (tau : ℝ → Site d → ℝ)
    (pMap : ℝ → ℝ) (scale pc betaC : ℝ)
    (hscale : 0 < scale)
    (hcorr : ∀ beta x, corr beta x = scale * tau (pMap beta) x)
    (habove : ∀ {beta}, betaC < beta → pc < pMap beta)
    (hbelow : ∀ {beta}, beta < betaC → pMap beta < pc)
    (hsuper : ∀ {p}, pc < p → ∃ c : ℝ, 0 < c ∧ ∀ x : Site d, c ≤ tau p x)
    (hsub : ∀ {p}, p < pc → ∀ epsilon : ℝ, 0 < epsilon →
      ∃ n : ℕ, ∀ x : Site d, x ∉ box d n → tau p x < epsilon) :
    (∀ {beta}, betaC < beta → HasLongRangeOrder corr beta) ∧
      (∀ {beta}, beta < betaC → HasSpatialDecay corr beta) := by
  constructor
  · intro beta hbeta
    obtain ⟨c, hc, hbound⟩ := hsuper (habove hbeta)
    refine ⟨scale * c, mul_pos hscale hc, ?_⟩
    intro x
    rw [hcorr]
    exact mul_le_mul_of_nonneg_left (hbound x) hscale.le
  · intro beta hbeta epsilon hepsilon
    have hepsScale : 0 < epsilon / scale := div_pos hepsilon hscale
    obtain ⟨n, hn⟩ := hsub (hbelow hbeta) (epsilon / scale) hepsScale
    refine ⟨n, ?_⟩
    intro x hx
    rw [hcorr]
    calc
      scale * tau (pMap beta) x < scale * (epsilon / scale) :=
        mul_lt_mul_of_pos_left (hn x hx) hscale
      _ = epsilon := by field_simp

end IsingFK

end StatMech
