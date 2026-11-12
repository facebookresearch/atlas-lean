/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Mathlib
import Code.Foundations.Ergodicity
import Code.Lattice.HypercubicLattice

open MeasureTheory
open scoped ENNReal

namespace StatMech.FrontierA

open StatMech.Lattice StatMech.ConfigSpace

variable {d : ℕ} {E : Type*}




def IsDiagonallyInvariantTransport
    [MulAction (Multiplicative (Site d)) E]
    (F : Site d → Site d → ConfigSpace E → ℝ≥0∞) : Prop :=
  ∀ (g : Multiplicative (Site d)) (x y : Site d) (omega : ConfigSpace E),
    F (g • x) (g • y) (shift g omega) = F x y omega


theorem translate_zero_y_by_neg (y : Site d) :
    let g : Multiplicative (Site d) := Multiplicative.ofAdd (-y)
    g • (0 : Site d) = -y ∧ g • y = 0 := by
  change (-y + 0 = -y) ∧ (-y + y = 0)
  simp





theorem lattice_mass_transport
    [MulAction (Multiplicative (Site d)) E]
    (mu : Measure (ConfigSpace E))
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) mu)
    (F : Site d → Site d → ConfigSpace E → ℝ≥0∞)
    (hF : ∀ x y, Measurable (F x y))
    (hdiag : IsDiagonallyInvariantTransport F) :
    ∫⁻ omega, ∑' y : Site d, F 0 y omega ∂mu =
      ∫⁻ omega, ∑' x : Site d, F x 0 omega ∂mu := by
  have hterm : ∀ y : Site d,
      (∫⁻ omega, F 0 y omega ∂mu) = ∫⁻ omega, F (-y) 0 omega ∂mu := by
    intro y
    let g : Multiplicative (Site d) := Multiplicative.ofAdd (-y)
    have hg : g • (0 : Site d) = -y ∧ g • y = 0 :=
      translate_zero_y_by_neg y
    calc
      (∫⁻ omega, F 0 y omega ∂mu) =
          ∫⁻ omega, F (g • (0 : Site d)) (g • y) (shift g omega) ∂mu := by
            apply lintegral_congr
            intro omega
            exact (hdiag g 0 y omega).symm
      _ = ∫⁻ omega, F (g • (0 : Site d)) (g • y) omega ∂mu :=
        (hinv g).lintegral_comp (hF (g • (0 : Site d)) (g • y))
      _ = ∫⁻ omega, F (-y) 0 omega ∂mu := by
        rw [hg.1, hg.2]
  calc
    (∫⁻ omega, ∑' y : Site d, F 0 y omega ∂mu) =
        ∑' y : Site d, ∫⁻ omega, F 0 y omega ∂mu := by
      rw [lintegral_tsum]
      exact fun y => (hF 0 y).aemeasurable
    _ = ∑' y : Site d, ∫⁻ omega, F (-y) 0 omega ∂mu :=
      tsum_congr hterm
    _ = ∑' x : Site d, ∫⁻ omega, F x 0 omega ∂mu := by
      rw [← (Equiv.neg (Site d)).tsum_eq]
      simp
    _ = ∫⁻ omega, ∑' x : Site d, F x 0 omega ∂mu := by
      rw [lintegral_tsum]
      exact fun x => (hF x 0).aemeasurable




theorem lattice_mass_transport_infinite_receiver_null
    [MulAction (Multiplicative (Site d)) E]
    (mu : Measure (ConfigSpace E)) [IsProbabilityMeasure mu]
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) mu)
    (F : Site d → Site d → ConfigSpace E → ℝ≥0∞)
    (hF : ∀ x y, Measurable (F x y))
    (hdiag : IsDiagonallyInvariantTransport F)
    (hout : ∀ omega, ∑' y : Site d, F 0 y omega ≤ 1) :
    mu {omega | ∑' x : Site d, F x 0 omega = ⊤} = 0 := by
  have hmass := lattice_mass_transport mu hinv F hF hdiag
  have houtIntegral : (∫⁻ omega, ∑' y : Site d, F 0 y omega ∂mu) ≤ 1 := by
    calc
      (∫⁻ omega, ∑' y : Site d, F 0 y omega ∂mu) ≤
          ∫⁻ _omega, (1 : ℝ≥0∞) ∂mu := lintegral_mono hout
      _ = 1 := by simp
  have hinIntegral : (∫⁻ omega, ∑' x : Site d, F x 0 omega ∂mu) ≠ ⊤ := by
    exact ne_top_of_le_ne_top ENNReal.one_ne_top (hmass ▸ houtIntegral)
  exact measure_eq_top_of_lintegral_ne_top
    ((Measurable.tsum fun x => hF x 0).aemeasurable) hinIntegral



theorem lattice_mass_transport_forbidden_event_null
    [MulAction (Multiplicative (Site d)) E]
    (mu : Measure (ConfigSpace E)) [IsProbabilityMeasure mu]
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) mu)
    (F : Site d → Site d → ConfigSpace E → ℝ≥0∞)
    (hF : ∀ x y, Measurable (F x y))
    (hdiag : IsDiagonallyInvariantTransport F)
    (hout : ∀ omega, ∑' y : Site d, F 0 y omega ≤ 1)
    (bad : Set (ConfigSpace E))
    (hbad : bad ⊆ {omega | ∑' x : Site d, F x 0 omega = ⊤}) :
    mu bad = 0 :=
  measure_mono_null hbad
    (lattice_mass_transport_infinite_receiver_null mu hinv F hF hdiag hout)

end StatMech.FrontierA
