/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Dimension.IntegralDimension
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Order.KrullDimension
import Mathlib.Order.RelSeries
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Spectrum.Prime.Defs
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Catenary formula for polynomial rings
For `R = MvPolynomial (Fin s) K` with `[Field K]`, the catenary formula
(`C-cat` in the original unmixedness plan §2) states that every prime `P` satisfies
`P.height + ringKrullDim (R ⧸ P) = ringKrullDim R` (which equals `s`).

## What this file proves

* `mvPolynomial_ringKrullDim`: `ringKrullDim (MvPolynomial (Fin s) K) = s`.
* `coheight_primeSpectrum_eq_ringKrullDim_quotient`: for prime `P` of any ring,
  `Order.coheight ⟨P, _⟩ = ringKrullDim (R ⧸ P)` (prime-chain bridge between
  spectrum coheight and quotient dimension).
* `height_add_ringKrullDim_quotient_le`: for prime `P` of any ring of finite
  dimension, `P.height + ringKrullDim (R ⧸ P) ≤ ringKrullDim R` (the easy half
  of catenary, by concatenating a below-`P` series with an above-`P` series).
* `mvPolynomial_height_add_ringKrullDim_quotient_le`: the MvPolynomial-over-field
  specialization `P.height + ringKrullDim (R ⧸ P) ≤ m` (upper half of catenary
  at `MvPolynomial` shape; the form the k=2 endgame consumes).
* `catenary_bot_mvPolynomial`: full equality for `P = ⊥`.
* `polynomial_catenary`: full equality for univariate `Polynomial K`
  (the `s = 1` base case: for `P ≠ ⊥`, `P.height ≥ 1` and the quotient
  dimension is nonnegative, so the upper bound forces equality).
* `quotient_maximal_dim_zero` / `height_maximal_le`: for maximal `M`,
  `ringKrullDim (R ⧸ M) = 0` hence `M.height ≤ s`.
* `dim_quotient_eq_normalization_index`: `ringKrullDim (R ⧸ P)` equals the
  Noether-normalization index `s ≤ n` (via chunk B2,
  `ringKrullDim_eq_of_algHom_isIntegral`).
* `mvPolynomial_catenary_eq_of_lower_bound`: the full formula conditional on
  the single missing lower bound — the exact consumption shape for chunk B4.

## Obstruction (the missing lower bound)

The reverse inequality `s ≤ P.height + ringKrullDim (R ⧸ P)` for arbitrary `P`
(`s ≥ 2`) is not proved here. The plan route (induction on `s` via
`Polynomial.height_eq_height_add_one`, peeling one variable) stalls on prime
bookkeeping Mathlib v4.34.0 cannot supply:

* `height_eq_height_add_one` applies only to *maximal* ideals lying over a
  prime of the base; the induction step for a general prime `P` splits into an
  "extended" case (needs height preservation `ht (pR) = ht p`, i.e. contraction
  injectivity for polynomial extensions) and a "fiber" case (needs minimal
  primes over `pR + (f)` to have height exactly `ht p + 1`: Krull hit gives
  `≤`, while `≥` needs the Noether-normalization coordinate change made monic,
  whose generic-linear-change step needs an infinite field, resp. the
  `Xᵢ + Xₙ ^ dᵢ` trick over finite fields).
* Going-down alone does not close the gap: `Algebra.HasGoingDown` holds for
  flat maps and for integral extensions of integrally closed domains, and the
  normalization map `A → R ⧸ P` qualifies — but lifting chains through it only
  reproduces the `≤` direction (chains below `P` concatenated with lifted
  chains above `P` have total length `≤ s`). The `≥` direction needs *long*
  chains below `P`, which is the catenary content itself.

Deviation note: the original unmixedness plan §2 routes B3 through induction on `s`
with B2 "at the base". The upper bound here instead uses prime-chain
concatenation (`RelSeries.smash`), which is the direction that goes through
with available API; B2 is used for the normalization-index description
(`dim_quotient_eq_normalization_index`), which pins the remaining goal to
`P.height = n - s` for the normalization index `s`.

## References

* `Mathlib/Order/KrullDimension.lean`, `Order.krullDim`, `Order.height`,
  `Order.coheight`, `exists_series_of_height_eq_coe`,
  `exists_series_of_le_coheight`, `coheight_eq_of_strictMono`,
  `coheight_bot_eq_krullDim`, `height_eq_zero`, `LTSeries.length_le_krullDim`,
  `krullDim_nonneg`, `one_le_iff_ne_zero`.
* `Mathlib/Order/RelSeries.lean`, `RelSeries.smash`, `RelSeries.smash_length`.
* `Mathlib/RingTheory/Ideal/Height.lean`, `Ideal.height`,
  `PrimeSpectrum.height_eq_orderHeight`,
  `Ideal.height_le_ringKrullDim_of_isPrime`.
* `Mathlib/RingTheory/Ideal/Maps.lean`, `Ideal.map_isPrime_of_surjective`,
  `Ideal.map_comap_of_surjective`, `Ideal.comap_map_of_surjective`,
  `Ideal.ker_le_comap`, `Ideal.map_mono`.
* `Mathlib/RingTheory/Ideal/Quotient/Defs.lean`, `Ideal.Quotient.mk`,
  `Ideal.Quotient.mk_surjective`.
* `Mathlib/RingTheory/Ideal/Quotient/Operations.lean`,
  `RingEquiv.quotientBot`, `Ideal.mk_ker`.
* `Mathlib/RingTheory/Ideal/Quotient/Basic.lean`, `Ideal.Quotient.isDomain`
  instance, `Field (R ⧸ I)` instance for maximal `I`.
* `Mathlib/RingTheory/Spectrum/Prime/Basic.lean`, `OrderBot` instance for
  spectra of domains, `PrimeSpectrum.asIdeal_bot`,
  `PrimeSpectrum.nonempty_iff_nontrivial`.
* `Mathlib/RingTheory/Spectrum/Prime/RingHom.lean`,
  `PrimeSpectrum.comap_asIdeal`, `PrimeSpectrum.asIdeal_lt_asIdeal`,
  `RingHom.strictMono_comap_of_surjective`.
* `Mathlib/RingTheory/Spectrum/Prime/Defs.lean`, `PrimeSpectrum.ext_iff`.
* `Mathlib/RingTheory/KrullDimension/Basic.lean`, `ringKrullDim`,
  `ringKrullDim_quotient_le`, `ringKrullDim_eq_of_ringEquiv`.
* `Mathlib/RingTheory/KrullDimension/Field.lean`,
  `ringKrullDim_eq_zero_of_field`.
* `Mathlib/RingTheory/KrullDimension/Polynomial.lean`,
  `Polynomial.height_eq_height_add_one`,
  `Polynomial.ringKrullDim_of_isNoetherianRing`,
  `MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite`.
* `Mathlib/RingTheory/NoetherNormalization.lean`,
  `exists_integral_inj_algHom_of_quotient`.
* `Mathlib/RingTheory/Ideal/GoingDown.lean`, `Algebra.HasGoingDown`
  (flat maps only, `of_flat`).
* `Mathlib/RingTheory/IntegralClosure/GoingDown.lean`, going-down for
  integral extensions of integrally closed domains.
* `Formalization/Appendix_FixedPoint/BezoutChain/
  Dimension/IntegralDimension.lean` (chunk B2),
  `ringKrullDim_eq_of_algHom_isIntegral`.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
/-- Krull dimension of a multivariate polynomial ring over a field:
`ringKrullDim (MvPolynomial (Fin s) K) = s`.

Route: `MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite` gives
`ringKrullDim K + Nat.card (Fin s)`; the field has dimension zero
(`ringKrullDim_eq_zero_of_field`).

## References

* `Mathlib/RingTheory/KrullDimension/Polynomial.lean`,
  `MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite`.
* `Mathlib/RingTheory/KrullDimension/Field.lean`,
  `ringKrullDim_eq_zero_of_field`. -/
theorem mvPolynomial_ringKrullDim (K : Type*) [Field K] (s : ℕ) :
    ringKrullDim (MvPolynomial (Fin s) K) = (s : WithBot ℕ∞) := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
    ringKrullDim_eq_zero_of_field, zero_add, Nat.card_fin]

/-- Spectrum coheight of a prime equals the Krull dimension of its quotient:
`Order.coheight ⟨P, _⟩ = ringKrullDim (R ⧸ P)`.

Route: `Order.coheight_eq_of_strictMono` applied to
`PrimeSpectrum.comap (Ideal.Quotient.mk P)` (strictly monotone for surjective
maps by `RingHom.strictMono_comap_of_surjective`). The coverage condition
holds because every prime above the contraction is hit: for
`comap a < b`, the ideal `b.asIdeal.map (mk P)` is prime
(`Ideal.map_isPrime_of_surjective`, using `ker mk = P ≤ b.asIdeal`) and maps
back to `b` (`Ideal.comap_map_of_surjective`).

## References

* `Mathlib/Order/KrullDimension.lean`, `coheight_eq_of_strictMono`,
  `coheight_bot_eq_krullDim`.
* `Mathlib/RingTheory/Spectrum/Prime/RingHom.lean`,
  `RingHom.strictMono_comap_of_surjective`, `PrimeSpectrum.comap_asIdeal`.
* `Mathlib/RingTheory/Spectrum/Prime/Basic.lean`,
  `PrimeSpectrum.asIdeal_bot`.
* `Mathlib/RingTheory/Ideal/Maps.lean`, `Ideal.map_isPrime_of_surjective`,
  `Ideal.comap_map_of_surjective`, `Ideal.map_comap_of_surjective`,
  `Ideal.ker_le_comap`, `Ideal.map_mono`.
* `Mathlib/RingTheory/Ideal/Quotient/Operations.lean`, `Ideal.mk_ker`.
* `Mathlib/RingTheory/Spectrum/Prime/Defs.lean`, `PrimeSpectrum.ext_iff`. -/
theorem coheight_primeSpectrum_eq_ringKrullDim_quotient {R : Type*} [CommRing R]
    (P : Ideal R) [P.IsPrime] :
    (Order.coheight (⟨P, ‹P.IsPrime›⟩ : PrimeSpectrum R) : WithBot ℕ∞) =
      ringKrullDim (R ⧸ P) := by
  have hsurj : Function.Surjective (Ideal.Quotient.mk P) :=
    Ideal.Quotient.mk_surjective
  have hcomapBot : (⊥ : Ideal (R ⧸ P)).comap (Ideal.Quotient.mk P) = P := by
    rw [← RingHom.ker_eq_comap_bot]
    exact P.mk_ker
  have hmono : StrictMono (PrimeSpectrum.comap (Ideal.Quotient.mk P)) :=
    RingHom.strictMono_comap_of_surjective hsurj
  have hcond : ∀ a : PrimeSpectrum (R ⧸ P), ∀ b : PrimeSpectrum R,
      PrimeSpectrum.comap (Ideal.Quotient.mk P) a < b →
      ∃ a' : PrimeSpectrum (R ⧸ P), a < a' ∧
        PrimeSpectrum.comap (Ideal.Quotient.mk P) a' = b := by
    intro a b hab
    have hlt : a.asIdeal.comap (Ideal.Quotient.mk P) < b.asIdeal := by
      have h : (PrimeSpectrum.comap (Ideal.Quotient.mk P) a).asIdeal < b.asIdeal :=
        hab
      rwa [PrimeSpectrum.comap_asIdeal] at h
    have hker : RingHom.ker (Ideal.Quotient.mk P) ≤ b.asIdeal := by
      have h1 : RingHom.ker (Ideal.Quotient.mk P) ≤
          a.asIdeal.comap (Ideal.Quotient.mk P) :=
        Ideal.ker_le_comap _
      exact h1.trans hlt.le
    have hJ : (b.asIdeal.map (Ideal.Quotient.mk P)).IsPrime :=
      (b.asIdeal).map_isPrime_of_surjective hsurj hker
    refine ⟨⟨b.asIdeal.map (Ideal.Quotient.mk P), hJ⟩, ?_, ?_⟩
    · rw [← PrimeSpectrum.asIdeal_lt_asIdeal]
      change a.asIdeal < b.asIdeal.map (Ideal.Quotient.mk P)
      have hle : a.asIdeal ≤ b.asIdeal.map (Ideal.Quotient.mk P) := by
        have h := Ideal.map_mono (f := Ideal.Quotient.mk P) hlt.le
        rwa [a.asIdeal.map_comap_of_surjective (Ideal.Quotient.mk P) hsurj] at h
      refine lt_of_le_of_ne hle ?_
      intro heq
      apply hlt.ne
      calc a.asIdeal.comap (Ideal.Quotient.mk P)
          = (b.asIdeal.map (Ideal.Quotient.mk P)).comap
              (Ideal.Quotient.mk P) := by rw [heq]
        _ = b.asIdeal ⊔ (⊥ : Ideal (R ⧸ P)).comap (Ideal.Quotient.mk P) :=
            b.asIdeal.comap_map_of_surjective (Ideal.Quotient.mk P) hsurj
        _ = b.asIdeal := by
            rw [hcomapBot]
            exact sup_eq_left.mpr (by rw [← P.mk_ker]; exact hker)
    · have e : (b.asIdeal.map (Ideal.Quotient.mk P)).comap
          (Ideal.Quotient.mk P) = b.asIdeal := by
        rw [b.asIdeal.comap_map_of_surjective (Ideal.Quotient.mk P) hsurj,
          hcomapBot]
        exact sup_eq_left.mpr (by rw [← P.mk_ker]; exact hker)
      apply PrimeSpectrum.ext_iff.mpr
      rw [PrimeSpectrum.comap_asIdeal]
      exact e
  have hcoh := Order.coheight_eq_of_strictMono
    (PrimeSpectrum.comap (Ideal.Quotient.mk P)) hmono hcond
    (⊥ : PrimeSpectrum (R ⧸ P))
  have hcohW : ((Order.coheight (⊥ : PrimeSpectrum (R ⧸ P))) : WithBot ℕ∞) =
      ((Order.coheight (PrimeSpectrum.comap (Ideal.Quotient.mk P) ⊥)) :
        WithBot ℕ∞) :=
    congrArg _ hcoh
  rw [Order.coheight_bot_eq_krullDim] at hcohW
  have hbot : PrimeSpectrum.comap (Ideal.Quotient.mk P) ⊥ =
      (⟨P, ‹P.IsPrime›⟩ : PrimeSpectrum R) := by
    apply PrimeSpectrum.ext_iff.mpr
    rw [PrimeSpectrum.comap_asIdeal, PrimeSpectrum.asIdeal_bot]
    exact hcomapBot
  rw [hbot] at hcohW
  change (Order.coheight (⟨P, ‹P.IsPrime›⟩ : PrimeSpectrum R) : WithBot ℕ∞) =
    Order.krullDim (PrimeSpectrum (R ⧸ P))
  exact_mod_cast hcohW.symm

/-- Easy half of catenary, for any ring of finite Krull dimension: prime height
plus quotient dimension is at most the ambient dimension.

Route: both sides are finite, so write `P.height = n`, get a length-`n` prime
series ending at `P` (`exists_series_of_height_eq_coe` via
`PrimeSpectrum.height_eq_orderHeight`), get a length-`m` series starting at
`P` (`exists_series_of_le_coheight` with `m` from the coheight bridge
`coheight_primeSpectrum_eq_ringKrullDim_quotient`), concatenate with
`RelSeries.smash`, and apply `LTSeries.length_le_krullDim`.

## References

* `Mathlib/Order/KrullDimension.lean`, `exists_series_of_height_eq_coe`,
  `exists_series_of_le_coheight`, `LTSeries.length_le_krullDim`.
* `Mathlib/Order/RelSeries.lean`, `RelSeries.smash`, `RelSeries.smash_length`.
* `Mathlib/RingTheory/Ideal/Height.lean`,
  `PrimeSpectrum.height_eq_orderHeight`,
  `Ideal.height_le_ringKrullDim_of_isPrime`.
* `Mathlib/RingTheory/KrullDimension/Basic.lean`,
  `ringKrullDim_quotient_le`. -/
theorem height_add_ringKrullDim_quotient_le {R : Type*} [CommRing R]
    (P : Ideal R) [P.IsPrime] (hfin : ringKrullDim R < ⊤) :
    (P.height : WithBot ℕ∞) + ringKrullDim (R ⧸ P) ≤ ringKrullDim R := by
  have hPle : (P.height : WithBot ℕ∞) ≤ ringKrullDim R :=
    Ideal.height_le_ringKrullDim_of_isPrime
  have hQle : ringKrullDim (R ⧸ P) ≤ ringKrullDim R := ringKrullDim_quotient_le P
  have hne : P.height ≠ ⊤ := by
    intro hcon
    have e₂ : (P.height : WithBot ℕ∞) = (⊤ : WithBot ℕ∞) := by
      rw [hcon]
      exact WithBot.coe_eq_top.mpr rfl
    have hle : (⊤ : WithBot ℕ∞) ≤ ringKrullDim R := by
      calc (⊤ : WithBot ℕ∞) = (P.height : WithBot ℕ∞) := e₂.symm
        _ ≤ ringKrullDim R := hPle
    exact lt_irrefl _ (lt_of_le_of_lt hle hfin)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne
  have hbridge := coheight_primeSpectrum_eq_ringKrullDim_quotient P
  have hcone : Order.coheight (⟨P, ‹P.IsPrime›⟩ : PrimeSpectrum R) ≠ ⊤ := by
    intro hcon
    have e : ((⊤ : ℕ∞) : WithBot ℕ∞) = ringKrullDim (R ⧸ P) := by
      rw [← hbridge, hcon]
    have hle : (⊤ : WithBot ℕ∞) ≤ ringKrullDim R := by
      calc (⊤ : WithBot ℕ∞) = ((⊤ : ℕ∞) : WithBot ℕ∞) :=
            (WithBot.coe_eq_top.mpr rfl).symm
        _ = ringKrullDim (R ⧸ P) := e
        _ ≤ ringKrullDim R := hQle
    exact lt_irrefl _ (lt_of_le_of_lt hle hfin)
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hcone
  have hht : Order.height (⟨P, ‹P.IsPrime›⟩ : PrimeSpectrum R) = n := by
    have h2 := PrimeSpectrum.height_eq_orderHeight
      (⟨P, ‹P.IsPrime›⟩ : PrimeSpectrum R)
    have hPAS : (⟨P, ‹P.IsPrime›⟩ : PrimeSpectrum R).asIdeal = P := rfl
    rw [hPAS, ← hn] at h2
    exact h2.symm
  have hmle : (m : ℕ∞) ≤
      Order.coheight (⟨P, ‹P.IsPrime›⟩ : PrimeSpectrum R) := by
    rw [hm]
  obtain ⟨q₁, hlast₁, hlen₁⟩ := Order.exists_series_of_height_eq_coe _ hht
  obtain ⟨q₂, hhead₂, hlen₂⟩ := Order.exists_series_of_le_coheight _ hmle
  have hconn : q₁.last = q₂.head := hlast₁.trans hhead₂.symm
  have hS := Order.LTSeries.length_le_krullDim (q₁.smash q₂ hconn)
  rw [RelSeries.smash_length, hlen₁, hlen₂] at hS
  have eH : (P.height : WithBot ℕ∞) = ((n : ℕ) : WithBot ℕ∞) := by
    rw [← hn, WithBot.coe_natCast]
  have eQ : ringKrullDim (R ⧸ P) = ((m : ℕ) : WithBot ℕ∞) := by
    rw [← hbridge, ← hm, WithBot.coe_natCast]
  have hadd : ((n : WithBot ℕ∞) + (m : WithBot ℕ∞)) =
      (((n + m : ℕ)) : WithBot ℕ∞) :=
    (Nat.cast_add n m).symm
  rw [eH, eQ, hadd]
  exact hS

/-- A nonzero prime of a domain has nonzero height: `P ≠ ⊥ → P.height ≠ 0`.

Route: `P.height = Order.height ⟨P, _⟩`
(`PrimeSpectrum.height_eq_orderHeight`); height zero would make `P` minimal
(`Order.height_eq_zero`), forcing `P = ⊥` (in a domain `⊥` is the least
prime, via `bot_le` and `PrimeSpectrum.asIdeal_bot`).

Note: the domain hypothesis is essential — in a non-domain a nonzero prime
can be minimal, hence of height zero. -/
theorem height_ne_zero_of_ne_bot {R : Type*} [CommRing R] [IsDomain R]
    (P : Ideal R) [P.IsPrime] (hne : P ≠ ⊥) : P.height ≠ 0 := by
  intro hz
  apply hne
  have h2 := PrimeSpectrum.height_eq_orderHeight
    (⟨P, ‹P.IsPrime›⟩ : PrimeSpectrum R)
  have hPAS : (⟨P, ‹P.IsPrime›⟩ : PrimeSpectrum R).asIdeal = P := rfl
  rw [hPAS, hz] at h2
  have hmin : IsMin (⟨P, ‹P.IsPrime›⟩ : PrimeSpectrum R) :=
    Order.height_eq_zero.mp h2.symm
  have hbot : (⊥ : PrimeSpectrum R) = ⟨P, ‹P.IsPrime›⟩ := hmin.eq_of_le bot_le
  have hass : (⊥ : Ideal R) =
      (⟨P, ‹P.IsPrime›⟩ : PrimeSpectrum R).asIdeal :=
    congrArg PrimeSpectrum.asIdeal hbot
  exact hass.symm

/-- The bottom prime has height zero. -/
theorem height_bot_eq_zero {R : Type*} [CommRing R] [IsDomain R] :
    (⊥ : Ideal R).height = 0 := by
  have hprime : (⊥ : Ideal R).IsPrime := Ideal.isPrime_bot
  have h2 := PrimeSpectrum.height_eq_orderHeight
    (⟨⊥, hprime⟩ : PrimeSpectrum R)
  have hPAS : (⟨⊥, hprime⟩ : PrimeSpectrum R).asIdeal =
      (⊥ : Ideal R) := rfl
  have hz : Order.height (⟨⊥, hprime⟩ : PrimeSpectrum R) = 0 :=
    Order.height_eq_zero.mpr isMin_bot
  rw [hPAS] at h2
  rw [hz] at h2
  exact h2

/-- Catenary formula at the bottom prime: `⊥.height + dim (R ⧸ ⊥) = s`.

Route: height is zero (`height_bot_eq_zero`); `R ⧸ ⊥ ≃+* R`
(`RingEquiv.quotientBot`) preserves dimension
(`ringKrullDim_eq_of_ringEquiv`); conclude with `mvPolynomial_ringKrullDim`.

## References

* `Mathlib/RingTheory/Ideal/Quotient/Operations.lean`,
  `RingEquiv.quotientBot`.
* `Mathlib/RingTheory/KrullDimension/Basic.lean`,
  `ringKrullDim_eq_of_ringEquiv`. -/
theorem catenary_bot_mvPolynomial (K : Type*) [Field K] (s : ℕ) :
    ((⊥ : Ideal (MvPolynomial (Fin s) K)).height : WithBot ℕ∞) +
      ringKrullDim
        (MvPolynomial (Fin s) K ⧸ (⊥ : Ideal (MvPolynomial (Fin s) K))) =
      (s : WithBot ℕ∞) := by
  have h0 : ((⊥ : Ideal (MvPolynomial (Fin s) K)).height : WithBot ℕ∞) = 0 :=
    by exact_mod_cast height_bot_eq_zero
  rw [h0, zero_add, ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
    mvPolynomial_ringKrullDim]

/-- Full catenary formula for univariate polynomial rings over a field
(the `s = 1` base case): every prime `P` of `Polynomial K` satisfies
`P.height + ringKrullDim (K[X] ⧸ P) = 1`.

Route: dimension of `K[X]` is `0 + 1` (`ringKrullDim_eq_zero_of_field`).
For `P = ⊥`, use height zero plus `R ⧸ ⊥ ≃+* R`. For `P ≠ ⊥`,
`P.height ≥ 1` (`height_ne_zero_of_ne_bot` plus
`Order.one_le_iff_ne_zero`) and the quotient dimension is nonnegative
(`Order.krullDim_nonneg`), so the upper bound
`height_add_ringKrullDim_quotient_le` forces equality.

## References

* `Mathlib/RingTheory/KrullDimension/Polynomial.lean`,
  `Polynomial.ringKrullDim_of_isNoetherianRing`.
* `Mathlib/RingTheory/KrullDimension/Field.lean`,
  `ringKrullDim_eq_zero_of_field`.
* `Mathlib/Order/KrullDimension.lean`, `one_le_iff_ne_zero`,
  `krullDim_nonneg`.
* `Mathlib/RingTheory/Spectrum/Prime/Basic.lean`,
  `PrimeSpectrum.nonempty_iff_nontrivial`. -/
theorem polynomial_catenary (K : Type*) [Field K] (P : Ideal (Polynomial K))
    [P.IsPrime] :
    (P.height : WithBot ℕ∞) + ringKrullDim (Polynomial K ⧸ P) = 1 := by
  have hdim : ringKrullDim (Polynomial K) = 1 := by
    simp [Polynomial.ringKrullDim_of_isNoetherianRing]
  have hfin : ringKrullDim (Polynomial K) < ⊤ := by
    rw [hdim]
    have h1 : ((1 : ℕ) : WithBot ℕ∞) < ⊤ := by
      rw [← WithBot.coe_natCast, ← WithBot.coe_top, WithBot.coe_lt_coe]
      exact ENat.natCast_lt_top 1
    exact_mod_cast h1
  have hle := height_add_ringKrullDim_quotient_le P hfin
  rw [hdim] at hle
  refine le_antisymm hle ?_
  rcases eq_or_ne P ⊥ with rfl | hne
  · have h0 : ((⊥ : Ideal (Polynomial K)).height : WithBot ℕ∞) = 0 :=
      by exact_mod_cast height_bot_eq_zero
    rw [h0, zero_add, ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
      hdim]
  · have h1 : (1 : WithBot ℕ∞) ≤ (P.height : WithBot ℕ∞) := by
      have hne0 : P.height ≠ 0 := height_ne_zero_of_ne_bot P hne
      have hle1 : 1 ≤ P.height := Order.one_le_iff_ne_zero.mpr hne0
      exact_mod_cast hle1
    have hne2 : Nonempty (PrimeSpectrum (Polynomial K ⧸ P)) :=
      PrimeSpectrum.nonempty_iff_nontrivial.mpr
        (Ideal.Quotient.nontrivial_iff.mpr Ideal.IsPrime.ne_top')
    have hnn : (0 : WithBot ℕ∞) ≤ ringKrullDim (Polynomial K ⧸ P) :=
      Order.krullDim_nonneg_iff.mpr hne2
    calc (1 : WithBot ℕ∞) = 1 + 0 := by simp
      _ ≤ (P.height : WithBot ℕ∞) + ringKrullDim (Polynomial K ⧸ P) :=
        add_le_add h1 hnn

/-- Quotients by maximal ideals have dimension zero (they are fields).

## References

* `Mathlib/RingTheory/Ideal/Quotient/Basic.lean`, `Field (R ⧸ I)` instance.
* `Mathlib/RingTheory/KrullDimension/Field.lean`,
  `ringKrullDim_eq_zero_of_field`. -/
theorem quotient_maximal_dim_zero (K : Type*) [Field K] (s : ℕ)
    (M : Ideal (MvPolynomial (Fin s) K)) [M.IsMaximal] :
    ringKrullDim (MvPolynomial (Fin s) K ⧸ M) = 0 :=
  @ringKrullDim_eq_zero_of_field _ (Ideal.Quotient.field M)

/-- Maximal ideals have height at most `s` (half of catenary at `M`). -/
theorem height_maximal_le (K : Type*) [Field K] (s : ℕ)
    (M : Ideal (MvPolynomial (Fin s) K)) [M.IsMaximal] :
    (M.height : WithBot ℕ∞) ≤ (s : WithBot ℕ∞) := by
  have hfin : ringKrullDim (MvPolynomial (Fin s) K) < ⊤ := by
    rw [mvPolynomial_ringKrullDim, ← WithBot.coe_natCast, ← WithBot.coe_top,
      WithBot.coe_lt_coe]
    exact ENat.natCast_lt_top s
  have hle := height_add_ringKrullDim_quotient_le M hfin
  rw [quotient_maximal_dim_zero, mvPolynomial_ringKrullDim] at hle
  simpa using hle

/-- Additive catenary upper bound for multivariate polynomial rings over a field:
for prime `P` of `MvPolynomial (Fin m) K`,
`P.height + ringKrullDim (R ⧸ P) ≤ m`.

Route: the general upper bound `height_add_ringKrullDim_quotient_le` (finite
dimension from `mvPolynomial_ringKrullDim`), rewritten by
`mvPolynomial_ringKrullDim`.

## References

* `height_add_ringKrullDim_quotient_le` above.
* `mvPolynomial_ringKrullDim` above.
* `Mathlib/RingTheory/KrullDimension/Polynomial.lean`,
  `MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite`. -/
theorem mvPolynomial_height_add_ringKrullDim_quotient_le (K : Type*) [Field K]
    (m : ℕ) (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime] :
    (P.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial (Fin m) K ⧸ P) ≤
      (m : WithBot ℕ∞) := by
  have hfin : ringKrullDim (MvPolynomial (Fin m) K) < ⊤ := by
    rw [mvPolynomial_ringKrullDim, ← WithBot.coe_natCast, ← WithBot.coe_top,
      WithBot.coe_lt_coe]
    exact ENat.natCast_lt_top m
  have hle := height_add_ringKrullDim_quotient_le P hfin
  rwa [mvPolynomial_ringKrullDim] at hle

/-- Noether-normalization description of quotient dimension: for `P ≠ ⊤`,
`ringKrullDim (R ⧸ P)` equals the normalization index `s ≤ n`.

Route: `exists_integral_inj_algHom_of_quotient` presents `R ⧸ P` as integral
over `MvPolynomial (Fin s) K`; B2 (`ringKrullDim_eq_of_algHom_isIntegral`)
preserves dimension along it; `mvPolynomial_ringKrullDim` evaluates it.

## References

* `Mathlib/RingTheory/NoetherNormalization.lean`,
  `exists_integral_inj_algHom_of_quotient`.
* `Formalization/Appendix_FixedPoint/BezoutChain/
  Dimension/IntegralDimension.lean` (chunk B2),
  `ringKrullDim_eq_of_algHom_isIntegral`. -/
theorem dim_quotient_eq_normalization_index (K : Type*) [Field K] (n : ℕ)
    (P : Ideal (MvPolynomial (Fin n) K)) (hP : P ≠ ⊤) :
    ∃ s ≤ n, ringKrullDim (MvPolynomial (Fin n) K ⧸ P) = (s : WithBot ℕ∞) := by
  obtain ⟨s, hsn, g, hinj, hint⟩ :=
    exists_integral_inj_algHom_of_quotient P hP
  refine ⟨s, hsn, ?_⟩
  rw [ringKrullDim_eq_of_algHom_isIntegral g hinj hint, mvPolynomial_ringKrullDim]

/-- Full catenary formula conditional on the lower bound (consumption shape
for chunk B4 `HeightLowerBound.lean`): once
`s ≤ P.height + ringKrullDim (R ⧸ P)` is supplied, the upper bound
`height_add_ringKrullDim_quotient_le` closes the equality. -/
theorem mvPolynomial_catenary_eq_of_lower_bound (K : Type*) [Field K] (s : ℕ)
    (P : Ideal (MvPolynomial (Fin s) K)) [P.IsPrime]
    (hlow : (s : WithBot ℕ∞) ≤
      (P.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial (Fin s) K ⧸ P)) :
    (P.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial (Fin s) K ⧸ P) =
      (s : WithBot ℕ∞) := by
  have hfin : ringKrullDim (MvPolynomial (Fin s) K) < ⊤ := by
    rw [mvPolynomial_ringKrullDim, ← WithBot.coe_natCast, ← WithBot.coe_top,
      WithBot.coe_lt_coe]
    exact ENat.natCast_lt_top s
  have hle := height_add_ringKrullDim_quotient_le P hfin
  rw [mvPolynomial_ringKrullDim] at hle
  exact le_antisymm hle hlow

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
