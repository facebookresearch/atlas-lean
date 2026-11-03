/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.AssociatedGradedRing
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedSurjection
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.MultiplicityNonvanishing
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedLift
import Appendix_FixedPoint.BezoutChain.Regularity.Grade.GradedDimEq
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.IrreducibleCoreDimTheory
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.Order.KrullDimension
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic

/-!
# Graded lower bound via Noether normalization
Attack `HgrDimLowerMinAtAss` (`GradedDimEq.lean`), the per-Ass-prime
lower bound `dim R_Q ≤ dim gr`, through Noether normalization
(`exists_finite_inj_algHom_of_fg` /
`exists_integral_inj_algHom_of_fg`). Since the lower bound is
goal-strength (iff with `ker = ⊥`, `GradedLowerBound` §§1–2), no
unconditional proof exists below that strength; this file proves the
maximal package: Noether data in the exact project shapes (§1),
integral-extensions-preserve-dimension in both directions (§2, new),
the Noether-number bounds (§3), and a new exact address for the
remainder — `NoetherGeAtAss`, "some/every Noether datum has `s ≥ d`"
— with the lower bound iff it (§4).

## What this file proves

* (§1) Noether data, unconditional: per-minimal-family integral
  (`noether_integral_data_of_quotKer`) and finite
  (`noether_finite_data_of_quotKer`) data for `S ⧸ ker` (nontrivial
  via `quotKerEquiv` + `koszulDim_nontrivial_gr`), plus integral and
  finite data for the fg domain `R ⧸ Q` at `Q` prime
  (`noether_integral_data_of_prime_quot`,
  `noether_finite_data_of_prime_quot`).
* (§2) Integral extensions preserve Krull dimension, unconditional and
  new (absent from Mathlib v4.34.0): `dim P ≤ dim T` for integral
  injective maps (`noetherDim_lift_le`, via going-up chain lifting
  `exists_ltSeries_of_hasGoingUp` over a lying-over base prime),
  `dim T ≤ dim P` for integral maps (`noetherDim_contract_le`, via
  `IsIntegral.under_lt_under` contraction of chains), hence equality
  (`noetherDim_eq`).
* (§3) Noether-number bounds, unconditional: every integral datum for
  `S ⧸ ker` has `s ≤ dim (S ⧸ ker)` (`noetherNum_le_dim_quotKer`),
  hence `s ≤ dim gr` (`noetherNum_le_dim_gr`) and `s ≤ d`
  (`noetherNum_le_embdim`, via `mult_ringKrullDim_quot_le`).
* (§4) New exact remainder address, unconditional iff:
  `NoetherGeAtAss` (per Ass prime, per minimal family, some Noether
  datum has `d ≤ s`) with `hgrDimLower_of_noetherGe`
  (conditional-exact on `[hGe]`), `noetherGe_of_hgrDimLower`
  (unconditional converse), hence `hgrDimLower_iff_noetherGe`
  (unconditional iff) and `noetherNum_eq_embdim_of_ge` (`s = d` on the
  residual). Minimal sop data is unconditional in-tree
  (`grlift_sop_exists`), so no s.o.p. hypothesis is needed.
* (§5, doc-only) Residual register: the verbatim open item
  (`NoetherGeAtAss` at minimal `d ≥ 2`), why it is minimal and exact,
  and the scoped routes (Hilbert comparison needs graded
  finite-map theory, absent; s.o.p. suitableness is the L4 lane).

## Scope coordination (no duplication)

* `GradedDimEq.lean`: owns `HgrDimLowerMinAtAss` (SPEC, consumed).
* `GradedLowerBound.lean` §§1–2: owns the `ker = ⊥` exact remainder
  (consumed for the verdict, never restated).
* `MultiplicityNonvanishing.lean` §2: owns `mult_ringKrullDim_poly`,
  `mult_ringKrullDim_quot_le`, `mult_quotKerEquiv_dim`,
  `mult_ringKrullDim_atPrime_eq_of_minimal` (all consumed).
* `GradedLift.lean`: owns `grlift_sop_exists` (consumed).
* `IrreducibleCoreDimTheory.lean`: owns `koszulDim_nontrivial_gr` (consumed).
* `DimensionToMultiplicity.lean` §§6–7: owns the supply-chain consumers
  (`hgrDimEqMin_of_lower`, `hwitMin_of_lower`,...); §4 here feeds
  `HgrDimLowerMinAtAss`, which they consume — no overlap.
* Mathlib (v4.34.0, all read-only, re-verified by grep):
  `exists_integral_inj_algHom_of_fg` /
  `exists_finite_inj_algHom_of_fg`
  (`RingTheory/NoetherNormalization.lean`);
  `exists_ltSeries_of_hasGoingUp`
  (`RingTheory/Ideal/HasGoingUp.lean`);
  `exists_ideal_over_prime_of_isIntegral`,
  `IsIntegral.under_lt_under`
  (`RingTheory/Ideal/GoingUp.lean`);
  `algebraMap_isIntegral_iff`
  (`RingTheory/IntegralClosure/Algebra/Defs.lean`);
  `LTSeries.length_le_krullDim`, `LTSeries.map`
  (`Order/KrullDimension.lean`, `Order/RelSeries.lean`).
  Integral-preserves-dimension is absent (this file §2 is new).

## Status

* §§1–3: unconditional.
* §4 forward: conditional-exact on `[hGe]`; converse + iff:
  unconditional (iff).
* Overall: partial toward `HgrDimLowerMinAtAss`
  (remainder = `NoetherGeAtAss` only, §5).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace NoetherNormalizationBound

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AssociatedGradedRing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjection
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.MultiplicityNonvanishing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedLift
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedDimEq
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.IrreducibleCoreDimTheory
open NoetherNormalization

/-- The residue field at `Q` (statement shorthand for Noether data). -/
abbrev NoetherResKl {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] :=
  IsLocalRing.ResidueField (Localization.AtPrime Q)

/-- The Noether target `S ⧸ ker` at `(Q, d, g)` (statement shorthand). -/
abbrev NoetherQuotKer {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] (d : ℕ)
    (g : Fin d → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q)) :=
  MvPolynomial (Fin d) (NoetherResKl Q) ⧸
    RingHom.ker (polySurjResidue Q d g hgen)

/-! ## §1. Noether data in the project shapes -/

/-- `S ⧸ ker` is nontrivial: it is ring-isomorphic to `gr` via
`quotKerEquiv`, and `gr` is nontrivial (`koszulDim_nontrivial_gr`).
-/
theorem noether_quotKer_nontrivial {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] (d : ℕ)
    (g : Fin d → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q)) :
    Nontrivial (NoetherQuotKer Q d g hgen) := by
  have : Nontrivial (grRegular Q) := inferInstance
  obtain ⟨a, b, hab⟩ := exists_pair_ne (grRegular Q)
  refine ⟨(polySurjResidue_quotKerEquiv Q d g hgen).symm a,
    (polySurjResidue_quotKerEquiv Q d g hgen).symm b, ?_⟩
  intro h
  exact hab ((polySurjResidue_quotKerEquiv Q d g hgen).toEquiv.symm.injective h)

#print axioms noether_quotKer_nontrivial

/-- Integral Noether data for `S ⧸ ker`: a finite injective polynomial
map in integral form. Feeds the §2 dimension lemmas.
-/
theorem noether_integral_data_of_quotKer {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] (d : ℕ)
    (g : Fin d → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q)) :
    ∃ s, ∃ gN : MvPolynomial (Fin s) (NoetherResKl Q) →ₐ[NoetherResKl Q]
      (NoetherQuotKer Q d g hgen),
      Function.Injective gN ∧ gN.IsIntegral := by
  have := noether_quotKer_nontrivial Q d g hgen
  exact exists_integral_inj_algHom_of_fg _ _

#print axioms noether_integral_data_of_quotKer

/-- Finite Noether data for `S ⧸ ker`: the same map in finite-module
form, for Hilbert-comparison consumers (L5).
-/
theorem noether_finite_data_of_quotKer {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] (d : ℕ)
    (g : Fin d → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q)) :
    ∃ s, ∃ gN : MvPolynomial (Fin s) (NoetherResKl Q) →ₐ[NoetherResKl Q]
      (NoetherQuotKer Q d g hgen),
      Function.Injective gN ∧ gN.Finite := by
  have := noether_quotKer_nontrivial Q d g hgen
  exact exists_finite_inj_algHom_of_fg _ _

#print axioms noether_finite_data_of_quotKer

/-- Integral Noether data for the fg domain `R ⧸ Q` at `Q` prime.
-/
theorem noether_integral_data_of_prime_quot {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] :
    ∃ s, ∃ gN : MvPolynomial (Fin s) K →ₐ[K]
        (MvPolynomial (Fin m) K ⧸ Q),
      Function.Injective gN ∧ gN.IsIntegral := by
  have hQ : Q ≠ ⊤ := Ideal.IsPrime.ne_top inferInstance
  have : Nontrivial (MvPolynomial (Fin m) K ⧸ Q) :=
    Ideal.Quotient.nontrivial_iff.mpr hQ
  exact exists_integral_inj_algHom_of_fg _ _

#print axioms noether_integral_data_of_prime_quot

/-- Finite Noether data for the fg domain `R ⧸ Q` at `Q` prime.
-/
theorem noether_finite_data_of_prime_quot {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] :
    ∃ s, ∃ gN : MvPolynomial (Fin s) K →ₐ[K]
        (MvPolynomial (Fin m) K ⧸ Q),
      Function.Injective gN ∧ gN.Finite := by
  have hQ : Q ≠ ⊤ := Ideal.IsPrime.ne_top inferInstance
  have : Nontrivial (MvPolynomial (Fin m) K ⧸ Q) :=
    Ideal.Quotient.nontrivial_iff.mpr hQ
  exact exists_finite_inj_algHom_of_fg _ _

#print axioms noether_finite_data_of_prime_quot

/-! ## §2. Integral extensions preserve Krull dimension -/

/-- Lifting direction: `dim P ≤ dim T` for an integral injective map.
Every prime chain in `P` lifts to one of the same length in `T`:
lying-over gives a base prime over the head
(`exists_ideal_over_prime_of_isIntegral` with `ker = ⊥` from
injectivity), and going-up (`exists_ltSeries_of_hasGoingUp`, via the
`of_isIntegral` instance) lifts the chain.
-/
theorem noetherDim_lift_le {P T : Type*} [CommRing P] [CommRing T]
    (g : P →+* T) (hint : g.IsIntegral)
    (hinj : Function.Injective g) :
    ringKrullDim P ≤ ringKrullDim T := by
  let : Algebra P T := g.toAlgebra
  have : Algebra.IsIntegral P T := algebraMap_isIntegral_iff.mp hint
  have hker : RingHom.ker (algebraMap P T) = ⊥ := by
    have h1 : algebraMap P T = g := RingHom.algebraMap_toAlgebra g
    rw [h1]
    exact (RingHom.injective_iff_ker_eq_bot g).mp hinj
  rw [ringKrullDim, ringKrullDim, Order.krullDim, Order.krullDim, iSup_le_iff]
  intro l
  have : (RelSeries.head l).asIdeal.IsPrime := (RelSeries.head l).isPrime
  have hIP : Ideal.under P (⊥ : Ideal T) ≤ (RelSeries.head l).asIdeal := by
    have hbot : Ideal.under P (⊥ : Ideal T) = ⊥ := by
      change Ideal.comap (algebraMap P T) ⊥ = ⊥
      rw [← RingHom.ker_eq_comap_bot, hker]
    rw [hbot]
    exact bot_le
  obtain ⟨Q, -, hQprime, hQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
    (RelSeries.head l).asIdeal (⊥ : Ideal T) hIP
  have := hQprime
  have : Q.LiesOver (RelSeries.head l).asIdeal := ⟨hQ.symm⟩
  obtain ⟨L, hlen, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l Q
  calc (l.length : WithBot ℕ∞) = (L.length : WithBot ℕ∞) := by rw [hlen]
    _ ≤ Order.krullDim (PrimeSpectrum T) :=
      Order.LTSeries.length_le_krullDim L

#print axioms noetherDim_lift_le

/-- Contraction direction: `dim T ≤ dim P` for an integral map (no
injectivity needed). Every prime chain in `T` contracts to one of the
same length in `P`: comap preserves primality
(`Ideal.IsPrime.comap`) and strictness
(`IsIntegral.under_lt_under`, incomparability).
-/
theorem noetherDim_contract_le {P T : Type*} [CommRing P] [CommRing T]
    (g : P →+* T) (hint : g.IsIntegral) :
    ringKrullDim T ≤ ringKrullDim P := by
  let : Algebra P T := g.toAlgebra
  have : Algebra.IsIntegral P T := algebraMap_isIntegral_iff.mp hint
  have hprime : ∀ Q : PrimeSpectrum T, (Ideal.under P Q.asIdeal).IsPrime := by
    intro Q
    have := Q.isPrime
    exact Ideal.IsPrime.comap (algebraMap P T)
  have hmono : StrictMono (fun Q : PrimeSpectrum T =>
      (⟨Ideal.under P Q.asIdeal, hprime Q⟩ : PrimeSpectrum P)) := by
    intro a b hab
    have := a.isPrime
    have hlt : a.asIdeal < b.asIdeal := by
      refine lt_of_le_of_ne
        ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr hab.le) ?_
      intro con
      exact hab.ne (PrimeSpectrum.ext_iff.mpr con)
    have hunder := Ideal.IsIntegral.under_lt_under (R := P) hlt
    refine lt_of_le_of_ne
      ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mp hunder.le) ?_
    intro con
    have con' : Ideal.under P a.asIdeal = Ideal.under P b.asIdeal :=
      congrArg PrimeSpectrum.asIdeal con
    exact ne_of_lt hunder con'
  rw [ringKrullDim, ringKrullDim, Order.krullDim, Order.krullDim, iSup_le_iff]
  intro L
  refine le_trans ?_ (Order.LTSeries.length_le_krullDim (L.map _ hmono))
  have hlen : (L.map (fun Q : PrimeSpectrum T =>
      (⟨Ideal.under P Q.asIdeal, hprime Q⟩ : PrimeSpectrum P))
      hmono).length = L.length := rfl
  rw [hlen]

#print axioms noetherDim_contract_le

/-- Integral injective maps preserve Krull dimension (both §2
directions). New: absent from Mathlib v4.34.0.
-/
theorem noetherDim_eq {P T : Type*} [CommRing P] [CommRing T]
    (g : P →+* T) (hint : g.IsIntegral)
    (hinj : Function.Injective g) :
    ringKrullDim T = ringKrullDim P :=
  le_antisymm (noetherDim_contract_le g hint)
    (noetherDim_lift_le g hint hinj)

#print axioms noetherDim_eq

/-! ## §3. Noether-number bounds -/

/-- Every integral Noether datum for `S ⧸ ker` has `s ≤ dim (S ⧸ ker)`:
`s = dim κ[u]` (`mult_ringKrullDim_poly`) and the lifting direction §2.
-/
theorem noetherNum_le_dim_quotKer {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] (d : ℕ)
    (g : Fin d → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (s : ℕ)
    (gN : MvPolynomial (Fin s) (NoetherResKl Q) →ₐ[NoetherResKl Q]
      (NoetherQuotKer Q d g hgen))
    (hinj : Function.Injective gN) (hint : gN.IsIntegral) :
    (s : WithBot ℕ∞) ≤ ringKrullDim (NoetherQuotKer Q d g hgen) := by
  have h := noetherDim_lift_le gN.toRingHom hint hinj
  rwa [mult_ringKrullDim_poly] at h

#print axioms noetherNum_le_dim_quotKer

/-- Every integral Noether datum for `S ⧸ ker` has `s ≤ dim gr`
(`quotKerEquiv` transfer of `noetherNum_le_dim_quotKer`).
-/
theorem noetherNum_le_dim_gr {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] (d : ℕ)
    (g : Fin d → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (s : ℕ)
    (gN : MvPolynomial (Fin s) (NoetherResKl Q) →ₐ[NoetherResKl Q]
      (NoetherQuotKer Q d g hgen))
    (hinj : Function.Injective gN) (hint : gN.IsIntegral) :
    (s : WithBot ℕ∞) ≤ ringKrullDim (grRegular Q) := by
  rw [← mult_quotKerEquiv_dim Q d g hgen]
  exact noetherNum_le_dim_quotKer Q d g hgen s gN hinj hint

#print axioms noetherNum_le_dim_gr

/-- Every integral Noether datum for `S ⧸ ker` has `s ≤ d`
(`noetherNum_le_dim_quotKer` + `mult_ringKrullDim_quot_le`). The
complementary bound to the §4 residual: on `NoetherGeAtAss`, `s = d`.
-/
theorem noetherNum_le_embdim {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] (d : ℕ)
    (g : Fin d → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (s : ℕ)
    (gN : MvPolynomial (Fin s) (NoetherResKl Q) →ₐ[NoetherResKl Q]
      (NoetherQuotKer Q d g hgen))
    (hinj : Function.Injective gN) (hint : gN.IsIntegral) :
    s ≤ d := by
  have h1 := noetherNum_le_dim_quotKer Q d g hgen s gN hinj hint
  have h2 := mult_ringKrullDim_quot_le
    (IsLocalRing.ResidueField (Localization.AtPrime Q)) d
    (RingHom.ker (polySurjResidue Q d g hgen))
  have hsd : (s : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) := le_trans h1 h2
  exact_mod_cast hsd

#print axioms noetherNum_le_embdim

/-! ## §4. The Noether exact remainder address -/

/-- Per-Ass-prime Noether lower bound at minimal `d`: every minimal
spanning family admits integral Noether data with `s ≥ d`. Since data
always exists (§1) and every datum has `s ≤ d` (§3), this says the
normalization number is exactly `d` — equivalently (both §2
directions) the lower bound itself.

Specification (Prop address for the Noether-form remainder). -/
def NoetherGeAtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    ∀ {d : ℕ} (g : Fin d → Localization.AtPrime Q)
      (hgen : Ideal.span (Set.range g) =
        IsLocalRing.maximalIdeal (Localization.AtPrime Q))
      (_hdmin : d = (IsLocalRing.maximalIdeal
        (Localization.AtPrime Q)).spanFinrank),
      ∃ s, ∃ gN : MvPolynomial (Fin s) (NoetherResKl Q) →ₐ[NoetherResKl Q]
        (NoetherQuotKer Q d g hgen),
        Function.Injective gN ∧ gN.IsIntegral ∧ d ≤ s

/-- `HgrDimLowerMinAtAss` from the Noether residual: per-`Q` minimal sop
data (`grlift_sop_exists`) feeds the datum; `d ≤ s ≤ dim gr` (§3) and
`dim R_Q = d` (minimality) give the lower bound.

Conditional on exactly `[hGe]`. -/
theorem hgrDimLower_of_noetherGe (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hGe : NoetherGeAtAss m K J) :
    HgrDimLowerMinAtAss m K J := by
  intro Q _ hQ
  obtain ⟨d, g, hgen, hd⟩ := grlift_sop_exists Q
  obtain ⟨s, gN, hinj, hint, hds⟩ := hGe Q hQ g hgen hd
  have hR := mult_ringKrullDim_atPrime_eq_of_minimal Q d g hgen (le_of_eq hd)
  have hsT := noetherNum_le_dim_quotKer Q d g hgen s gN hinj hint
  have hTgr := mult_quotKerEquiv_dim Q d g hgen
  calc ringKrullDim (Localization.AtPrime Q)
      = (d : WithBot ℕ∞) := hR
    _ ≤ (s : WithBot ℕ∞) := by exact_mod_cast hds
    _ ≤ ringKrullDim (NoetherQuotKer Q d g hgen) := hsT
    _ = ringKrullDim (grRegular Q) := hTgr

#print axioms hgrDimLower_of_noetherGe

/-- Converse: the lower bound gives the Noether residual. Any §1 datum
works: `d = dim R_Q ≤ dim gr = dim (S ⧸ ker) ≤ s` (§2 contraction +
`mult_ringKrullDim_poly`).
-/
theorem noetherGe_of_hgrDimLower (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hLower : HgrDimLowerMinAtAss m K J) :
    NoetherGeAtAss m K J := by
  intro Q _ hQ d g hgen hdmin
  obtain ⟨s, gN, hinj, hint⟩ := noether_integral_data_of_quotKer Q d g hgen
  refine ⟨s, gN, hinj, hint, ?_⟩
  have hR := mult_ringKrullDim_atPrime_eq_of_minimal Q d g hgen (le_of_eq hdmin)
  have hlo := hLower Q hQ
  have hTgr := mult_quotKerEquiv_dim Q d g hgen
  have hcon := noetherDim_contract_le gN.toRingHom hint
  rw [mult_ringKrullDim_poly] at hcon
  have hds : (d : WithBot ℕ∞) ≤ (s : WithBot ℕ∞) := calc
    (d : WithBot ℕ∞) = ringKrullDim (Localization.AtPrime Q) := hR.symm
    _ ≤ ringKrullDim (grRegular Q) := hlo
    _ = ringKrullDim (NoetherQuotKer Q d g hgen) := hTgr.symm
    _ ≤ (s : WithBot ℕ∞) := hcon
  exact_mod_cast hds

#print axioms noetherGe_of_hgrDimLower

/-- The lower bound is exactly Noether-residual-strength at Ass primes.
-/
theorem hgrDimLower_iff_noetherGe (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HgrDimLowerMinAtAss m K J ↔ NoetherGeAtAss m K J :=
  ⟨noetherGe_of_hgrDimLower m K J, hgrDimLower_of_noetherGe m K J⟩

#print axioms hgrDimLower_iff_noetherGe

/-- On the residual, every integral Noether datum has `s = d`
(`noetherNum_le_embdim` + the residual inequality).
-/
theorem noetherNum_eq_embdim_of_ge {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] (d : ℕ)
    (g : Fin d → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (s : ℕ)
    (gN : MvPolynomial (Fin s) (NoetherResKl Q) →ₐ[NoetherResKl Q]
      (NoetherQuotKer Q d g hgen))
    (hinj : Function.Injective gN) (hint : gN.IsIntegral)
    (hds : d ≤ s) :
    s = d :=
  le_antisymm (noetherNum_le_embdim Q d g hgen s gN hinj hint) hds

#print axioms noetherNum_eq_embdim_of_ge

/-! ## §5. Residual register (doc-only)

Minimal non-circular remainder (verbatim): `NoetherGeAtAss`, i.e. per
`Q ∈ Ass(R ⧸ J)`, per minimal family (`d = spanFinrank 𝔪`), some
integral Noether datum `κ[u₁..u_s] → S ⧸ ker` has `d ≤ s`.

Why the remainder is minimal and exact (all machine-checked):

* `hgrDimLower_iff_noetherGe` (§4) shows the Noether residual is
  exactly lower-bound-strength, hence (via `GradedLowerBound` §§1–2 and
  the `WitnessKernelMain` §1 ring) exactly crux-strength: any proof of
  any crux form discharges it, and it discharges every crux form.
* `noetherNum_le_embdim` (§3) shows every datum has `s ≤ d`
  unconditionally, so the residual pins `s = d`
  (`noetherNum_eq_embdim_of_ge`) — the normalization number is exact.
* Nothing assumes `hwit`, `hmult`, `hdimEq`, `ker = ⊥`, growth, or
  polynomiality to prove the §§1–3 masters; the only undischarged
  input is the Noether inequality itself.

Routes to the residual (surveyed, none duplicated):

* Hilbert-comparison route: a finite graded injective
  `κ[u] → gr` gives `Hilb(gr) ≥ Hilb(κ[u])` pointwise, hence growth
  `≥ s - 1`. Blocked: Noether maps are not graded in general, and
  graded finite-map Hilbert theory is absent from Mathlib and
  in-tree. The §1 finite data (`noether_finite_data_of_quotKer`) is
  banked for this route (L5).
* System-of-parameters route: the minimal sop exists unconditionally
  (`grlift_sop_exists`); showing its `gr¹` classes force `s ≥ d`
  needs the L4 suitableness analysis (prime avoidance exists in
  Mathlib; suitability is the open question). No s.o.p. hypothesis
  was needed for the §4 masters.
* Direct dimension route: `s = dim (S ⧸ ker)` is §2; `s ≥ d` via
  dimension is the lower bound itself (circular, correctly registered
  as the remainder rather than attempted).

Consumers: `hgrDimLower_of_noetherGe` discharges `HgrDimLowerMinAtAss`
on `[hGe]` alone; feeding it into `hgrDimEqMin_of_lower` (GrDimEq §3)
yields `HgrDimEqMinAtAss`, hence `HmultMinAtAss` / `HdimEqMinAtAss` /
rb-1 via the §6 supply chain. `noetherDim_eq` (§2) is available to any
future finite/integral extension argument.
-/

end NoetherNormalizationBound
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
