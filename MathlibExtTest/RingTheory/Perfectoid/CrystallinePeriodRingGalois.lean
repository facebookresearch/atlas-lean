/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.RingTheory.Perfectoid.CrystallinePeriodRingGalois
import MathlibExt.RingTheory.Perfectoid.DeRhamPeriodRingUniformizer

/-! Tests for the Galois action on Fontaine's ring `A_cris`: the map `A_cris → B_dR^+` is
equivariant, the action is a group action extending the action on `W(𝓞_ℂ_[p]♭)[ξ^n/n!]`, the image
`A_cris ⊆ B_dR^+` is the same for every generator of the kernel of `θ` (such as a unit multiple of
`ξ`), is Galois stable, contains `log [ε]` for Fontaine's `ε` and lies in `A_max`, and the period
`log [ε] ∈ A_cris` maps to `log [ε]`, is nonzero and is permuted by the action. -/

open Ideal WittVector PowerSeries PadicComplexInt

variable (p : ℕ) [Fact p.Prime]

local notation "𝔸" => WittVector p (PreTilt 𝓞_ℂ_[p] p)
local notation "𝔸ₚ" => Localization.Away (p : WittVector p (PreTilt 𝓞_ℂ_[p] p))
local notation "𝔹⁺" => BDeRhamPlus 𝓞_ℂ_[p] p

-- The map `A_cris → B_dR^+` is Galois equivariant, for every generator of the kernel of `θ`.
example (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : CrystallineCompletion p (xi p)) :
    toBDeRhamPlus (ker_fontaineTheta_eq_span_xi p)
        (galoisCrystallineCompletion p (ker_fontaineTheta_eq_span_xi p) σ x) =
      galoisBDeRhamPlus p σ (toBDeRhamPlus (ker_fontaineTheta_eq_span_xi p) x) :=
  toBDeRhamPlus_galoisCrystallineCompletion _ σ x

example {w : 𝔸} (hgen : RingHom.ker (fontaineTheta 𝓞_ℂ_[p] p) = span {w})
    (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : CrystallineCompletion p w) :
    toBDeRhamPlus hgen (galoisCrystallineCompletion p hgen σ x) =
      galoisBDeRhamPlus p σ (toBDeRhamPlus hgen x) :=
  toBDeRhamPlus_galoisCrystallineCompletion hgen σ x

-- The action laws: `σ τ` acts as `τ` followed by `σ`, and `1` acts trivially.
example (σ τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : CrystallineCompletion p (xi p)) :
    galoisCrystallineCompletion p (ker_fontaineTheta_eq_span_xi p) (σ * τ) x =
      galoisCrystallineCompletion p (ker_fontaineTheta_eq_span_xi p) σ
        (galoisCrystallineCompletion p (ker_fontaineTheta_eq_span_xi p) τ x) := by
  rw [galoisCrystallineCompletion_mul, RingHom.comp_apply]

example (x : CrystallineCompletion p (xi p)) :
    galoisCrystallineCompletion p (ker_fontaineTheta_eq_span_xi p) 1 x = x := by
  rw [galoisCrystallineCompletion_one, RingHom.id_apply]

-- On `W(𝓞_ℂ_[p]♭) ⊆ W(𝓞_ℂ_[p]♭)[ξ^n/n!]` the action is the map of Witt vectors, and the action
-- on `A_cris` extends the action on `W(𝓞_ℂ_[p]♭)[ξ^n/n!]`.
example (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (a : 𝔸) :
    (galoisFiniteDividedPowers p (ker_fontaineTheta_eq_span_xi p) σ
        ⟨algebraMap 𝔸 𝔸ₚ a, algebraMap_mem_finiteDividedPowers (xi p) a⟩ : 𝔸ₚ) =
      algebraMap 𝔸 𝔸ₚ (WittVector.map (PreTilt.map p (integralGalois p σ).toRingHom) a) := by
  rw [coe_galoisFiniteDividedPowers, Localization.awayMapNatCast_algebraMap]

example (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : finiteDividedPowers p (xi p)) :
    galoisCrystallineCompletion p (ker_fontaineTheta_eq_span_xi p) σ
        (algebraMap _ (CrystallineCompletion p (xi p)) x) =
      algebraMap _ (CrystallineCompletion p (xi p))
        (galoisFiniteDividedPowers p (ker_fontaineTheta_eq_span_xi p) σ x) :=
  galoisCrystallineCompletion_algebraMap _ σ x

-- The image of `A_cris` in `B_dR^+` is the same for the generator `ξ c` of the kernel of `θ`,
-- for a unit `c`.
example (c : 𝔸ˣ) :
    (toBDeRhamPlus (w := xi p * (c : 𝔸)) (by
      rw [ker_fontaineTheta_eq_span_xi]
      exact (Ideal.span_singleton_mul_right_unit c.isUnit _).symm)).range = aCris p :=
  range_toBDeRhamPlus_eq_aCris p _

-- `A_cris` is the set of values `Σ aₙ ξⁿ/n!` of restricted series; it contains
-- `W(𝓞_ℂ_[p]♭)` and `Σ pⁿ ξⁿ/n!`.
example : algebraMap 𝔸 𝔹⁺ (xi p) ∈ aCris p := algebraMap_mem_aCris p (xi p)

example : evalBDeRhamPlus p (algebraMap_mem_ker_fontaineThetaInvertP p (fontaineTheta_xi p))
    (dividedPowerSeries p (PowerSeries.mk fun n => (p : 𝔸) ^ n)) ∈ aCris p := by
  refine (mem_aCris_iff p).2 ⟨_, ?_, rfl⟩
  intro k
  exact ⟨k, fun n hn => by rw [PowerSeries.coeff_mk]; exact pow_dvd_pow _ hn⟩

-- `A_cris` is stable under `Gal(ℚ̄_p/ℚ_p)`.
example (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) {y : 𝔹⁺} (hy : y ∈ aCris p) :
    galoisBDeRhamPlus p σ y ∈ aCris p :=
  galoisBDeRhamPlus_mem_aCris p σ hy

-- `log [ε] ∈ A_cris` for Fontaine's `ε`, and `A_cris ⊆ A_max`.
example : logTeichmuller p (untilt_epsilon p) ∈ aCris p := logTeichmuller_mem_aCris p _

example {y : 𝔹⁺} (hy : y ∈ aCris p) : y ∈ aMax p := aCris_le_aMax p hy

-- The period `t = log [ε] ∈ A_cris`: its image in `B_dR^+` is `log [ε]`, it is nonzero, and
-- `σ(t) = log [σ ε]`.
example : toBDeRhamPlus (ker_fontaineTheta_eq_span_xi p)
    (logTeichmullerCrystalline p (untilt_epsilon p)) = logTeichmuller p (untilt_epsilon p) :=
  toBDeRhamPlus_logTeichmullerCrystalline p _

example : logTeichmullerCrystalline p (untilt_epsilon p) ≠ 0 := fun h =>
  logTeichmuller_ne_zero p (untilt_epsilon p) (epsilon_ne_one p) (by
    rw [← toBDeRhamPlus_logTeichmullerCrystalline, h, map_zero])

example (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    galoisCrystallineCompletion p (ker_fontaineTheta_eq_span_xi p) σ
        (logTeichmullerCrystalline p (untilt_epsilon p)) =
      logTeichmullerCrystalline p (ε := PreTilt.map p (integralGalois p σ).toRingHom (epsilon p))
        (by rw [PreTilt.untilt_map, untilt_epsilon, map_one]) :=
  galoisCrystallineCompletion_logTeichmullerCrystalline p σ _ _
