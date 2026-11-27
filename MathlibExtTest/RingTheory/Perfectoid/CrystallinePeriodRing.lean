/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.RingTheory.Perfectoid.CrystallinePeriodRing

/-! Tests for Fontaine's ring `A_cris` and its map to `B_dR^+`, at the generator `ξ = p - [p♭]` of
the kernel of `θ`: the map is injective, agrees with the canonical map on
`W(𝓞_ℂ_[p]♭)[ξ^n/n!]`, sends the element of a restricted series to the value of its
divided-power series, and has the expected image; the divided powers satisfy their defining
identities. -/

open Ideal PowerSeries WittVector

variable (p : ℕ) [Fact p.Prime]

local notation "𝔸" => WittVector p (PreTilt 𝓞_ℂ_[p] p)

example : Function.Injective
    (PadicComplexInt.toBDeRhamPlus (PadicComplexInt.ker_fontaineTheta_eq_span_xi p)) :=
  PadicComplexInt.toBDeRhamPlus_injective _

example (x : PadicComplexInt.finiteDividedPowers p (PadicComplexInt.xi p)) :
    PadicComplexInt.toBDeRhamPlus (PadicComplexInt.ker_fontaineTheta_eq_span_xi p)
        (algebraMap _ (PadicComplexInt.CrystallineCompletion p (PadicComplexInt.xi p)) x) =
      PadicComplexInt.localizationToBDeRhamPlus p x :=
  PadicComplexInt.toBDeRhamPlus_algebraMap _ x

-- The constant series `1` is restricted, and its element maps to the value at `ξ` of the
-- divided-power series of `1`.
example : PadicComplexInt.toBDeRhamPlus (PadicComplexInt.ker_fontaineTheta_eq_span_xi p)
      (PadicComplexInt.ofRestricted (PadicComplexInt.xi p)
        (Subring.one_mem (PadicComplexInt.restrictedPowerSeries p))) =
    PadicComplexInt.evalBDeRhamPlus p
      (PadicComplexInt.algebraMap_mem_ker_fontaineThetaInvertP p
        (PadicComplexInt.fontaineTheta_xi p))
      (PadicComplexInt.dividedPowerSeries p 1) :=
  PadicComplexInt.toBDeRhamPlus_ofRestricted _ _

-- A generator of the kernel of `θ` lies in the kernel of `θ` with `p` inverted.
example : algebraMap 𝔸 (Localization.Away (p : 𝔸)) (PadicComplexInt.xi p) ∈
    RingHom.ker (fontaineThetaInvertP 𝓞_ℂ_[p] p) :=
  PadicComplexInt.algebraMap_mem_ker_of_ker_eq_span
    (PadicComplexInt.ker_fontaineTheta_eq_span_xi p)

-- The image is the set of values at `ξ` of the divided-power series of the restricted series.
example : Set.range (PadicComplexInt.toBDeRhamPlus
      (PadicComplexInt.ker_fontaineTheta_eq_span_xi p)) =
    {y | ∃ f ∈ PadicComplexInt.restrictedPowerSeries p,
      y = PadicComplexInt.evalBDeRhamPlus p
        (PadicComplexInt.algebraMap_mem_ker_fontaineThetaInvertP p
          (PadicComplexInt.fontaineTheta_xi p))
        (PadicComplexInt.dividedPowerSeries p f)} :=
  PadicComplexInt.range_toBDeRhamPlus _

-- Fontaine's theorem at `ξ` needs only that `ξ` generates the kernel of `θ`.
example : ∃ j : PadicComplexInt.CrystallineCompletion p (PadicComplexInt.xi p) →+*
      BDeRhamPlus 𝓞_ℂ_[p] p, Function.Injective j ∧
      Set.range j = {y | ∃ f ∈ PadicComplexInt.restrictedPowerSeries p,
        y = PadicComplexInt.evalBDeRhamPlus p
          (PadicComplexInt.algebraMap_mem_ker_fontaineThetaInvertP p
            (PadicComplexInt.fontaineTheta_xi p))
          (PadicComplexInt.dividedPowerSeries p f)} :=
  (PadicComplexInt.exists_injective_crystallineCompletion_bDeRhamPlus
    (PadicComplexInt.ker_fontaineTheta_eq_span_xi p)).imp fun _ h => ⟨h.1, h.2.2⟩

example : ∃ j : PadicComplexInt.CrystallineCompletion p (PadicComplexInt.xi p) →+*
      BDeRhamPlus 𝓞_ℂ_[p] p, Function.Injective j :=
  ⟨_, PadicComplexInt.toBDeRhamPlus_injective (PadicComplexInt.ker_fontaineTheta_eq_span_xi p)⟩

-- Every unit multiple of `ξ` also generates the kernel, so the construction applies to it.
example (c : 𝔸ˣ) : Function.Injective (PadicComplexInt.toBDeRhamPlus
    (w := PadicComplexInt.xi p * (c : 𝔸)) (by
      rw [PadicComplexInt.ker_fontaineTheta_eq_span_xi]
      exact (Ideal.span_singleton_mul_right_unit c.isUnit _).symm)) :=
  PadicComplexInt.toBDeRhamPlus_injective _

example (w : 𝔸) (n : ℕ) :
    ((n.factorial : ℕ) : Localization.Away (p : 𝔸)) * PadicComplexInt.dividedPower w n =
      algebraMap 𝔸 (Localization.Away (p : 𝔸)) w ^ n :=
  PadicComplexInt.factorial_mul_dividedPower w n

example (w : 𝔸) : PadicComplexInt.dividedPower w 0 = 1 := PadicComplexInt.dividedPower_zero w

-- A generator of `ker θ` is a non-zero-divisor modulo `p ^ k`.
example (k : ℕ) (u : 𝔸) (h : (p : 𝔸) ^ k ∣ PadicComplexInt.xi p * u) : (p : 𝔸) ^ k ∣ u :=
  PadicComplexInt.p_pow_dvd_of_dvd_mul (PadicComplexInt.ker_fontaineTheta_eq_span_xi p) k h
