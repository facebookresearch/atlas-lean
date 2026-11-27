/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.RingTheory.Perfectoid.CrystallineFrobenius
import MathlibExt.RingTheory.Perfectoid.DeRhamPeriodRingUniformizer

/-! Tests for the Frobenius of Fontaine's ring `A_cris`: `φ(ξ) ≡ ξ^p` modulo `p`, `φ` preserves
`W(𝓞_ℂ_[p]♭)[w^n/n!]` for every `w`, the Frobenius of `A_cris` extends it and commutes with the
Galois action, `φ(log [ε]) = log [ε^p] = p log [ε]` (in particular `φ(t) = p t`), and `φ` is
injective on `W(𝓞_ℂ_[p]♭)`, on `W(𝓞_ℂ_[p]♭)[1/p]` and on `W(𝓞_ℂ_[p]♭)[w^n/n!]`. -/

open Ideal PowerSeries PadicComplexInt
open WittVector (fontaineTheta)

variable (p : ℕ) [Fact p.Prime]

local notation "𝔸" => WittVector p (PreTilt 𝓞_ℂ_[p] p)
local notation "𝔸ₚ" => Localization.Away (p : WittVector p (PreTilt 𝓞_ℂ_[p] p))

-- `φ(ξ) = ξ^p + p a`, and explicitly `φ(ξ) = p - [p♭^p]`.
example : ∃ a : 𝔸, WittVector.frobenius (xi p) = xi p ^ p + (p : 𝔸) * a :=
  exists_frobenius_eq_pow_add p (xi p)

example : WittVector.frobenius (xi p) = (p : 𝔸) - WittVector.teichmuller p (pFlat p ^ p) :=
  frobenius_xi p

-- `θ(φ(ξ)) = p - p^p`: unlike `ξ`, `φ(ξ)` is not sent to `0` by `θ` (as `p^p ≠ p`).
example :
    fontaineTheta 𝓞_ℂ_[p] p (WittVector.frobenius (xi p)) = (p : 𝓞_ℂ_[p]) - (p : 𝓞_ℂ_[p]) ^ p := by
  rw [frobenius_xi, map_sub, map_natCast, WittVector.fontaineTheta_teichmuller, map_pow,
    untilt_pFlat]

example : fontaineTheta 𝓞_ℂ_[p] p (WittVector.frobenius (xi p)) ≠ 0 := by
  rw [frobenius_xi, map_sub, map_natCast, WittVector.fontaineTheta_teichmuller, map_pow,
    untilt_pFlat, sub_ne_zero, ← Nat.cast_pow, Ne, Nat.cast_inj]
  intro h
  have hp1 := (Fact.out : p.Prime).one_lt
  have h1 : p ^ 1 < p ^ p := Nat.pow_lt_pow_right hp1 hp1
  rw [pow_one, ← h] at h1
  exact lt_irrefl _ h1

-- The Witt vector Frobenius is natural, hence commutes with the Galois action on `A_inf`.
example (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : 𝔸) :
    WittVector.frobenius (WittVector.map (PreTilt.map p (integralGalois p σ).toRingHom) x) =
      WittVector.map (PreTilt.map p (integralGalois p σ).toRingHom) (WittVector.frobenius x) :=
  (WittVector.map_frobenius _ x).symm

-- `φ([x]) = [x^p]`.
example (x : PreTilt 𝓞_ℂ_[p] p) :
    WittVector.frobenius (WittVector.teichmuller p x) = WittVector.teichmuller p (x ^ p) :=
  WittVector.frobenius_teichmuller x

-- `φ(D) ⊆ D` for every `w`, not only for generators of `ker θ`.
example (w : 𝔸) (n : ℕ) : frobeniusLocalization p (dividedPower w n) ∈ finiteDividedPowers p w :=
  frobeniusLocalization_mem_finiteDividedPowers p w (dividedPower_mem w n)

example (w : 𝔸) (x : finiteDividedPowers p w) :
    frobeniusCrystallineCompletion p w
        (algebraMap (finiteDividedPowers p w) (CrystallineCompletion p w) x) =
      algebraMap (finiteDividedPowers p w) (CrystallineCompletion p w)
        (frobeniusFiniteDividedPowers p w x) :=
  frobeniusCrystallineCompletion_algebraMap p w x

-- On `W(𝓞_ℂ_[p]♭)`, the Frobenius of `D` is the Witt vector Frobenius.
example (a : 𝔸) :
    (frobeniusFiniteDividedPowers p (xi p)
        ⟨algebraMap 𝔸 𝔸ₚ a, algebraMap_mem_finiteDividedPowers (xi p) a⟩ : 𝔸ₚ) =
      algebraMap 𝔸 𝔸ₚ (WittVector.frobenius a) := by
  rw [coe_frobeniusFiniteDividedPowers, frobeniusLocalization_algebraMap]

-- The Frobenius of `A_cris` commutes with the Galois action, for every generator of `ker θ`.
example {w : 𝔸} (hgen : RingHom.ker (fontaineTheta 𝓞_ℂ_[p] p) = span {w})
    (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : CrystallineCompletion p w) :
    frobeniusCrystallineCompletion p w (galoisCrystallineCompletion p hgen σ x) =
      galoisCrystallineCompletion p hgen σ (frobeniusCrystallineCompletion p w x) :=
  frobeniusCrystallineCompletion_galoisCrystallineCompletion p hgen σ x

-- `φ(log [ε]) = log [ε^p] = p log [ε]`, and `φ(t) = p t` for Fontaine's `ε`.
example {ε : PreTilt 𝓞_ℂ_[p] p} (h : ε.untilt = 1) (h' : (ε ^ p).untilt = 1) :
    frobeniusCrystallineCompletion p (xi p) (logTeichmullerCrystalline p h) =
      logTeichmullerCrystalline p h' :=
  frobeniusCrystallineCompletion_logTeichmullerCrystalline_eq p h h'

example :
    frobeniusCrystallineCompletion p (xi p) (logTeichmullerCrystalline p (untilt_epsilon p)) =
      (p : CrystallineCompletion p (xi p)) * logTeichmullerCrystalline p (untilt_epsilon p) :=
  frobeniusCrystallineCompletion_logTeichmullerCrystalline p (untilt_epsilon p)

-- `φ^2(t) = p^2 t`.
example :
    frobeniusCrystallineCompletion p (xi p) (frobeniusCrystallineCompletion p (xi p)
        (logTeichmullerCrystalline p (untilt_epsilon p))) =
      (p : CrystallineCompletion p (xi p)) ^ 2 *
        logTeichmullerCrystalline p (untilt_epsilon p) := by
  rw [frobeniusCrystallineCompletion_logTeichmullerCrystalline, map_mul, map_natCast,
    frobeniusCrystallineCompletion_logTeichmullerCrystalline, ← mul_assoc, sq]

-- `log [ε^n] = n log [ε]` in `A_cris`.
example {ε : PreTilt 𝓞_ℂ_[p] p} (h : ε.untilt = 1) (h₂ : (ε ^ 2).untilt = 1) :
    logTeichmullerCrystalline p h₂ = 2 * logTeichmullerCrystalline p h := by
  rw [logTeichmullerCrystalline_pow p h 2 h₂, Nat.cast_ofNat]

-- Injectivity of `φ` on `W(𝓞_ℂ_[p]♭)` (Mathlib), on `W(𝓞_ℂ_[p]♭)[1/p]` and on `D`.
example : Function.Injective (WittVector.frobenius : 𝔸 →+* 𝔸) :=
  (WittVector.frobenius_bijective p (PreTilt 𝓞_ℂ_[p] p)).injective

example : Function.Injective (frobeniusLocalization p) :=
  frobeniusLocalization_injective p

example (w : 𝔸) : Function.Injective (frobeniusFiniteDividedPowers p w) :=
  frobeniusFiniteDividedPowers_injective p w
