/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Calculus.GreensTheorem

open MeasureTheory

-- Check the full original statement, including every public binder name.
example
    (U D : Set (ℝ × ℝ))
    (a b : ℝ)
    (γ : ℝ → ℝ × ℝ)
    (L M : ℝ × ℝ → ℝ)
    (hU : IsOpen U)
    (hDU : D ⊆ U)
    (hD_bdd : Bornology.IsBounded D)
    (hD_meas : MeasurableSet D)
    (hL : ContDiffOn ℝ 1 L U)
    (hM : ContDiffOn ℝ 1 M U)
    (hab : a < b)
    (hγcont : ContinuousOn γ (Set.Icc a b))
    (hγclosed : γ a = γ b)
    (hγinj : Set.InjOn γ (Set.Ico a b))
    (hγsimple : ∀ t ∈ Set.Ioo a b, γ t ≠ γ a)
    (hγtrace : γ '' Set.Icc a b = frontier D)
    (hγU : ∀ t ∈ Set.Icc a b, γ t ∈ U)
    (hγpw : ∃ S : Finset ℝ, a ∈ S ∧ b ∈ S ∧ ↑S ⊆ Set.Icc a b ∧
      ContDiffOn ℝ 1 γ (Set.Icc a b \ ↑S) ∧
      (∀ u v : ℝ, u ∈ S → v ∈ S → u < v → Set.Ioo u v ∩ ↑S = ∅ →
        ContDiffOn ℝ 1 γ (Set.Icc u v)) ∧
      ∀ t ∈ Set.Ioo a b \ ↑S, deriv γ t ≠ 0 ∧
        ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ →
          γ t + ε • (-(deriv γ t).2, (deriv γ t).1) ∈ D) :
    (∫ t in a..b,
      (L (γ t) * deriv (fun t => (γ t).1) t +
        M (γ t) * deriv (fun t => (γ t).2) t)) =
    ∫ p in D,
      (deriv (fun x => M (x, p.2)) p.1 -
        deriv (fun y => L (p.1, y)) p.2) ∂volume :=
  MetaMathlibExt.greens_theorem (U := U) (D := D) (a := a) (b := b) (γ := γ) (L := L) (M := M)
    (hU := hU) (hDU := hDU) (hD_bdd := hD_bdd) (hD_meas := hD_meas) (hL := hL) (hM := hM)
    (hab := hab) (hγcont := hγcont) (hγclosed := hγclosed) (hγinj := hγinj)
    (hγsimple := hγsimple) (hγtrace := hγtrace) (hγU := hγU) (hγpw := hγpw)
