/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.NoetherNormalizationBound
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedLowerBound
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.DimensionToMultiplicity
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.HighHomogeneousRelations
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.GradedSurjectionInjective
import Appendix_FixedPoint.BezoutChain.Geometry.UnmixednessAtLengthTwo
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic

/-!
# Direct attack on `NoetherGeAtAss`
Attacks `NoetherGeAtAss` (`NoetherNormalizationBound.lean`, §4: per Ass prime,
per minimal family, some integral Noether datum has `d ≤ s`) directly,
at minimal-`d` per-Ass-prime forms only.

verdict (machine-checked, §§1–2): the attack narrows to an exact
per-prime remainder but does not close unconditionally — and the file
pins down exactly why. Every injective integral datum has its Noether
number pinned to `s = dim (S ⧸ ker)` (§1, unconditional), so "some
datum has `d ≤ s`" is exactly the per-prime lower bound
`dim R_Q ≤ dim gr` (§2, unconditional iff). In particular no
system-of-parameters-to-datum conversion can beat `s = dim T`: any
injective datum it produces carries the pinned number, and any
non-injective (integral-only) datum yields only an upper bound
(`noetherGeDim_le_of_weakDatum`). Minimality of the family is likewise
provably insufficient: it sees only degree 1 (`Low`), while the gap is
the degree-`≥ 2` relations (`High`). The residual is therefore exactly
the shared crux (`ker = ⊥` / the `d ≥ 2` lower bound), reached here by
an independent counting route.

## What this file proves

* (§1) Datum pinning, unconditional: every injective integral datum has
  `(s : WithBot ℕ∞) = dim (S ⧸ ker)` (`noetherGeNum_eq_dim_quotKer`,
  §2-lift + §2-contraction) hence `s = dim gr`
  (`noetherGeNum_eq_dim_gr`); integral-only data give only
  `dim T ≤ e` (`noetherGeDim_le_of_weakDatum`).
* (§2) Per-prime exact remainder, unconditional iff:
  `NoetherGeAtPrime` (per-prime per-family `d ≤ s`) with both
  directions (`noetherGeAtPrime_of_lower_atPrime`,
  `lower_of_noetherGeAtPrime`), the iff
  (`noetherGeAtPrime_iff_lower_atPrime`), and Ass repackaging
  (`noetherGeAtAss_iff_forall_prime`).
* (§3) `d ≤ 1` unconditional closure: `NoetherGeAtPrime` at embdim
  `0`/`1` (`noetherGeAtPrime_embdim_zero/one`, via the closed
  §4 lower instances + the §2 forward direction).
* (§4) conditional-exact Ass-level masters (minimal-`d` forms):
  `NoetherGeAtAss` from `HkerMinAtAss` (`noetherGe_of_hkerMin`),
  from `HnoHomRelHighMinAtAss` (`noetherGe_of_noHomRelHighMin` —
  bridges the two crux addresses: High ⟹ NoetherGe), from
  `HwitMinAtAss` / `HmultMinAtAss` / `HdimEqMinAtAss` /
  `HgrDimEqMinAtAss` (one-line supply-chain compositions), and from
  per-prime `[Prime, NoIrredHigh]` (`noetherGe_of_minimal_prime_noIrred`,
  with the `d = 0` field branch closed inline).
* (§5, doc-only) Residual register: the verbatim open item, why the
  s.o.p.-conversion and minimality angles cannot close it, and the
  scoped routes.

## Scope coordination (no duplication)

* `NoetherNormalizationBound.lean`: owns `NoetherGeAtAss` (SPEC), `§1` data,
  `§2` dim lemmas, `§3` bounds, the `§4` Ass-level iff (all consumed,
  never restated). This file adds the per-prime factor + pinning.
* `GradedDimEq.lean`: owns `HgrDimLowerMinAtAss` (SPEC) and the
  `d ≤ 1` lower instances (consumed in §3).
* `GradedLowerBound.lean` §2: owns `hgrDimLower_of_hkerMin` (consumed).
* `DimensionToMultiplicity.lean` §§5–7: owns the kernel auto-close masters
  and the `HnoHomRelHighMinAtAss` SPEC (all consumed).
* `HighHomogeneousRelations.lean`: owns `Low`/`High`/`Prime`/`NoIrred` and the
  `ker = ⊥` masters (consumed; `Low`-from-minimality consumed).
* `GradedSurjectionInjective.lean`: owns `hsAssemble_ker_eq_bot_zero`
  (consumed for the `d = 0` branch).
* Sibling Lane A2 (s.o.p. wiring): not depended upon — this file
  proves its own minimal counting inline (§1) and takes crux inputs
  as explicit hypotheses in existing in-tree shapes only.

## Status

* §§1–3: unconditional.
* §4: conditional-exact on the named input in each theorem.
* Overall: partial toward `NoetherGeAtAss` (remainder = the
  per-prime `d ≥ 2` lower bound / `ker = ⊥`, §5).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace NoetherLowerAttack

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AssociatedGradedRing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjection
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.MultiplicityNonvanishing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedDimEq
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedLowerBound
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.NoetherNormalizationBound
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.DimensionToMultiplicity
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.HighHomogeneousRelations
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjectionInjective

/-! ## §1. Datum pinning: every injective datum has `s = dim T` -/

/-- Per-prime per-family Noether lower bound: some integral Noether
datum for `S ⧸ ker` at `(Q, d, g)` has `d ≤ s`. The per-prime factor
of `NoetherGeAtAss` (see `noetherGeAtAss_iff_forall_prime`).

Specification (Prop address for the per-prime Noether remainder). -/
def NoetherGeAtPrime {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] (d : ℕ)
    (g : Fin d → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q)) : Prop :=
  ∃ s, ∃ gN : MvPolynomial (Fin s) (NoetherResKl Q) →ₐ[NoetherResKl Q]
    (NoetherQuotKer Q d g hgen),
    Function.Injective gN ∧ gN.IsIntegral ∧ d ≤ s

/-- Pinning: every injective integral Noether datum for `S ⧸ ker` has
`s = dim (S ⧸ ker)` exactly (`s ≤ dim` is the §2 lift;
`dim ≤ s` is the §2 contraction + the poly formula). Hence no
conversion producing an injective datum can beat `s = dim T`: the
inequality `d ≤ s` is exactly the lower bound `d ≤ dim T`.
-/
theorem noetherGeNum_eq_dim_quotKer {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] (d : ℕ)
    (g : Fin d → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (s : ℕ)
    (gN : MvPolynomial (Fin s) (NoetherResKl Q) →ₐ[NoetherResKl Q]
      (NoetherQuotKer Q d g hgen))
    (hinj : Function.Injective gN) (hint : gN.IsIntegral) :
    (s : WithBot ℕ∞) = ringKrullDim (NoetherQuotKer Q d g hgen) := by
  have hcon := noetherDim_contract_le gN.toRingHom hint
  rw [mult_ringKrullDim_poly] at hcon
  exact le_antisymm
    (noetherNum_le_dim_quotKer Q d g hgen s gN hinj hint) hcon

#print axioms noetherGeNum_eq_dim_quotKer

/-- Pinning on `gr`: every injective integral datum has `s = dim gr`
(`quotKerEquiv` transfer of `noetherGeNum_eq_dim_quotKer`).
-/
theorem noetherGeNum_eq_dim_gr {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] (d : ℕ)
    (g : Fin d → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (s : ℕ)
    (gN : MvPolynomial (Fin s) (NoetherResKl Q) →ₐ[NoetherResKl Q]
      (NoetherQuotKer Q d g hgen))
    (hinj : Function.Injective gN) (hint : gN.IsIntegral) :
    (s : WithBot ℕ∞) = ringKrullDim (grRegular Q) := by
  rw [← mult_quotKerEquiv_dim Q d g hgen]
  exact noetherGeNum_eq_dim_quotKer Q d g hgen s gN hinj hint

#print axioms noetherGeNum_eq_dim_gr

/-- Weak (integral-only, possibly non-injective) data give only upper
bounds: an integral map `κ[X₁..X_e] → S ⧸ ker` forces
`dim (S ⧸ ker) ≤ e` (contraction needs no injectivity). So dropping
injectivity cannot help the lower bound either.
-/
theorem noetherGeDim_le_of_weakDatum {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] (d : ℕ)
    (g : Fin d → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (e : ℕ)
    (gN : MvPolynomial (Fin e) (NoetherResKl Q) →ₐ[NoetherResKl Q]
      (NoetherQuotKer Q d g hgen))
    (hint : gN.IsIntegral) :
    ringKrullDim (NoetherQuotKer Q d g hgen) ≤ (e : WithBot ℕ∞) := by
  have hcon := noetherDim_contract_le gN.toRingHom hint
  rwa [mult_ringKrullDim_poly] at hcon

#print axioms noetherGeDim_le_of_weakDatum

/-! ## §2. Per-prime exact remainder: NoetherGe ⟺ lower bound -/

/-- Per-prime NoetherGe from the per-prime lower bound (any §1 datum
works: `d = dim R_Q ≤ dim gr = dim T ≤ s`).
-/
theorem noetherGeAtPrime_of_lower_atPrime {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] (d : ℕ)
    (g : Fin d → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (hd : d = (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank)
    (hlo : ringKrullDim (Localization.AtPrime Q) ≤
      ringKrullDim (grRegular Q)) :
    NoetherGeAtPrime Q d g hgen := by
  obtain ⟨s, gN, hinj, hint⟩ := noether_integral_data_of_quotKer Q d g hgen
  refine ⟨s, gN, hinj, hint, ?_⟩
  have hR := mult_ringKrullDim_atPrime_eq_of_minimal Q d g hgen (le_of_eq hd)
  have hTgr := mult_quotKerEquiv_dim Q d g hgen
  have hcon := noetherDim_contract_le gN.toRingHom hint
  rw [mult_ringKrullDim_poly] at hcon
  have hds : (d : WithBot ℕ∞) ≤ (s : WithBot ℕ∞) := calc
    (d : WithBot ℕ∞) = ringKrullDim (Localization.AtPrime Q) := hR.symm
    _ ≤ ringKrullDim (grRegular Q) := hlo
    _ = ringKrullDim (NoetherQuotKer Q d g hgen) := hTgr.symm
    _ ≤ (s : WithBot ℕ∞) := hcon
  exact_mod_cast hds

#print axioms noetherGeAtPrime_of_lower_atPrime

/-- Per-prime lower bound from per-prime NoetherGe
(`d ≤ s ≤ dim T = dim gr` and `dim R_Q = d`).
-/
theorem lower_of_noetherGeAtPrime {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] (d : ℕ)
    (g : Fin d → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (hd : d = (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank)
    (hGe : NoetherGeAtPrime Q d g hgen) :
    ringKrullDim (Localization.AtPrime Q) ≤
      ringKrullDim (grRegular Q) := by
  obtain ⟨s, gN, hinj, hint, hds⟩ := hGe
  have hR := mult_ringKrullDim_atPrime_eq_of_minimal Q d g hgen (le_of_eq hd)
  have hsT := noetherNum_le_dim_quotKer Q d g hgen s gN hinj hint
  have hTgr := mult_quotKerEquiv_dim Q d g hgen
  calc ringKrullDim (Localization.AtPrime Q)
      = (d : WithBot ℕ∞) := hR
    _ ≤ (s : WithBot ℕ∞) := by exact_mod_cast hds
    _ ≤ ringKrullDim (NoetherQuotKer Q d g hgen) := hsT
    _ = ringKrullDim (grRegular Q) := hTgr

#print axioms lower_of_noetherGeAtPrime

/-- The per-prime Noether residual is exactly lower-bound-strength.
-/
theorem noetherGeAtPrime_iff_lower_atPrime {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] (d : ℕ)
    (g : Fin d → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (hd : d = (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank) :
    NoetherGeAtPrime Q d g hgen ↔
      ringKrullDim (Localization.AtPrime Q) ≤
        ringKrullDim (grRegular Q) :=
  ⟨lower_of_noetherGeAtPrime Q d g hgen hd,
   noetherGeAtPrime_of_lower_atPrime Q d g hgen hd⟩

#print axioms noetherGeAtPrime_iff_lower_atPrime

/-- Ass-level repackaging: `NoetherGeAtAss` is the per-prime predicate
at every Ass prime and minimal family.
-/
theorem noetherGeAtAss_iff_forall_prime (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    NoetherGeAtAss m K J ↔
      ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
        Q ∈ associatedPrimes _ (_ ⧸ J) →
        ∀ {d : ℕ} (g : Fin d → Localization.AtPrime Q)
          (hgen : Ideal.span (Set.range g) =
            IsLocalRing.maximalIdeal (Localization.AtPrime Q))
          (_hdmin : d = (IsLocalRing.maximalIdeal
            (Localization.AtPrime Q)).spanFinrank),
          NoetherGeAtPrime Q d g hgen := by
  constructor
  · intro h Q _ hQ d g hgen hdmin
    exact h Q hQ g hgen hdmin
  · intro h Q _ hQ d g hgen hdmin
    exact h Q hQ g hgen hdmin

#print axioms noetherGeAtAss_iff_forall_prime

/-! ## §3. Unconditional `d ≤ 1` closure -/

/-- `NoetherGeAtPrime` at embedding dimension `0` (closed lower
instance + the §2 forward direction).
-/
theorem noetherGeAtPrime_embdim_zero (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J))
    {d : ℕ} (g : Fin d → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (hd : d = (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank)
    (he : (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank = 0) :
    NoetherGeAtPrime Q d g hgen :=
  noetherGeAtPrime_of_lower_atPrime Q d g hgen hd
    (grDimLower_embdim_zero m K J Q hQ he)

#print axioms noetherGeAtPrime_embdim_zero

/-- `NoetherGeAtPrime` at embedding dimension `1` (closed lower
instance + the §2 forward direction).
-/
theorem noetherGeAtPrime_embdim_one (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J))
    {d : ℕ} (g : Fin d → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (hd : d = (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank)
    (he : (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank = 1) :
    NoetherGeAtPrime Q d g hgen :=
  noetherGeAtPrime_of_lower_atPrime Q d g hgen hd
    (grDimLower_embdim_one m K J Q hQ he)

#print axioms noetherGeAtPrime_embdim_one

/-! ## §4. Conditional-exact Ass-level masters -/

/-- `NoetherGeAtAss` from `HkerMinAtAss` (via GrLower §2 + Noether §4).

Conditional on exactly `[hker]`. -/
theorem noetherGe_of_hkerMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hker : UnmixednessAtLengthTwo.HkerMinAtAss m K J) :
    NoetherGeAtAss m K J :=
  noetherGe_of_hgrDimLower m K J (hgrDimLower_of_hkerMin m K J hker)

#print axioms noetherGe_of_hkerMin

/-- `NoetherGeAtAss` from `HnoHomRelHighMinAtAss`: bridges the two
Crux addresses (High ⟹ NoetherGe, via kernel auto-close).

Conditional on exactly `[hHigh]`. -/
theorem noetherGe_of_noHomRelHighMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hHigh : HnoHomRelHighMinAtAss m K J) :
    NoetherGeAtAss m K J :=
  noetherGe_of_hkerMin m K J (hkerMin_of_noHomRelHighMin m K J hHigh)

#print axioms noetherGe_of_noHomRelHighMin

/-- `NoetherGeAtAss` from `HwitMinAtAss` (via kernel auto-close).

Conditional on exactly `[hwit]`. -/
theorem noetherGe_of_hwitMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hwit : UnmixednessAtLengthTwo.HwitMinAtAss m K J) :
    NoetherGeAtAss m K J :=
  noetherGe_of_hkerMin m K J (hkerMin_of_hwitMin m K J hwit)

#print axioms noetherGe_of_hwitMin

/-- `NoetherGeAtAss` from `HmultMinAtAss` (via kernel auto-close).

Conditional on exactly `[hmult]`. -/
theorem noetherGe_of_hmultMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hmult : UnmixednessAtLengthTwo.HmultMinAtAss m K J) :
    NoetherGeAtAss m K J :=
  noetherGe_of_hkerMin m K J (hkerMin_of_hmultMin m K J hmult)

#print axioms noetherGe_of_hmultMin

/-- `NoetherGeAtAss` from `HdimEqMinAtAss` (goal-strength iff + §4).

Conditional on exactly `[hdimEq]`. -/
theorem noetherGe_of_hdimEqMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hdimEq : UnmixednessAtLengthTwo.HdimEqMinAtAss m K J) :
    NoetherGeAtAss m K J :=
  noetherGe_of_hkerMin m K J ((hdimEqMin_iff_hkerMin m K J).mp hdimEq)

#print axioms noetherGe_of_hdimEqMin

/-- `NoetherGeAtAss` from `HgrDimEqMinAtAss` (via kernel auto-close).

Conditional on exactly `[hgr]`. -/
theorem noetherGe_of_grDimEqMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hgr : HgrDimEqMinAtAss m K J) :
    NoetherGeAtAss m K J :=
  noetherGe_of_hkerMin m K J (hkerMin_of_grDimEq m K J hgr)

#print axioms noetherGe_of_grDimEqMin

/-- `NoetherGeAtAss` from per-prime `[Prime, NoIrredHigh]` at minimal
`d`: `Low` is discharged by minimality, `d = 0` by the closed field
branch, `d ≥ 1` by the HomRelHigh master — then §4 on the assembled
`HkerMinAtAss`.

Conditional on exactly `[hprime, hnoirr]`. -/
theorem noetherGe_of_minimal_prime_noIrred (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hprime : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) →
      ∀ {d : ℕ} (g : Fin d → Localization.AtPrime Q)
        (hgen : Ideal.span (Set.range g) =
          IsLocalRing.maximalIdeal (Localization.AtPrime Q))
        (_hdmin : d = (IsLocalRing.maximalIdeal
          (Localization.AtPrime Q)).spanFinrank),
        KwitKerIsPrime Q d g hgen)
    (hnoirr : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) →
      ∀ {d : ℕ} (g : Fin d → Localization.AtPrime Q)
        (hgen : Ideal.span (Set.range g) =
          IsLocalRing.maximalIdeal (Localization.AtPrime Q))
        (_hdmin : d = (IsLocalRing.maximalIdeal
          (Localization.AtPrime Q)).spanFinrank),
        KwitNoIrredHigh Q d g hgen) :
    NoetherGeAtAss m K J := by
  apply noetherGe_of_hkerMin
  intro Q _ hQ d g hgen hdmin
  by_cases hd0 : d = 0
  · subst hd0
    exact hsAssemble_ker_eq_bot_zero Q g hgen
  · have hd1 : 1 ≤ d := by omega
    exact kwitHigh_ker_eq_bot_of_minimal_prime_noIrred Q d g hgen hd1
      (le_of_eq hdmin) (hprime Q hQ g hgen hdmin)
      (hnoirr Q hQ g hgen hdmin)

#print axioms noetherGe_of_minimal_prime_noIrred

/-! ## §5. Residual register (doc-only)

Minimal non-circular remainder (verbatim): `NoetherGeAtPrime` at
minimal `d ≥ 2` per `Q ∈ Ass(R ⧸ J)`, i.e. some integral Noether datum
`κ[u₁..u_s] → S ⧸ ker` has `d ≤ s`.

Why the remainder is minimal and exact (all machine-checked):

* `noetherGeAtPrime_iff_lower_atPrime` (§2) shows the per-prime
  residual is exactly lower-bound-strength, hence (via `GradedLowerBound`
  §§1–2 and the `WitnessKernelMain` §1 ring) exactly crux-strength.
* `noetherGeNum_eq_dim_quotKer` (§1) pins `s = dim (S ⧸ ker)` for
  every injective integral datum, so the residual pins
  `d ≤ dim T` — the counting angle is exhausted, not merely stalled.
* Nothing assumes `hwit`, `hmult`, `hdimEq`, `ker = ⊥`, growth, or
  polynomiality to prove the §§1–3 masters; the only undischarged
  input is the Noether inequality itself.

Why the two suggested conversion angles cannot close it:

* s.o.p.-to-datum conversion: any conversion outputs either an
  injective datum (whose `s` is pinned to `dim T` by §1, so `d ≤ s`
  is the lower bound itself) or a weak integral-only datum (which
  yields only `dim T ≤ e` by `noetherGeDim_le_of_weakDatum` — the
  wrong direction). A system of parameters can only count dimension
  from above; the residual needs it from below.
* Minimality-of-family exploitation: minimality discharges `Low`
  (degree-1 relations vanish) but is provably blind to degree-`≥ 2`
  relations — a nonzero prime with no linear part (e.g. `(X² - Y³)`
  in two variables) satisfies `Low` with `dim T = d - 1`. The gap is
  exactly `High`, i.e. the other crux address, wired here as
  `noetherGe_of_noHomRelHighMin` (High ⟹ NoetherGe).

Routes to the residual (surveyed, none duplicated):

* Via `ker = ⊥` per Ass prime (`noetherGe_of_hkerMin`): exactly
  goal-strength (`hgrDimLower_iff_hkerMin`), correctly registered
  rather than attempted.
* Via `High` / `Prime` + `NoIrredHigh`
  (`noetherGe_of_noHomRelHighMin`,
  `noetherGe_of_minimal_prime_noIrred`): reduces NoetherGe to the
  High@Ge2 address (HighAttack iffs) — the live sibling front.
* Via the full crux ring (`Hwit`/`Hmult`/`HdimEq`/`HgrDimEq` §4
  battery): any crux form discharges NoetherGe; all are equivalent.
* The Hilbert-comparison route (finite graded `κ[u] → gr`) still
  needs graded finite-map theory, absent from Mathlib and in-tree.

Consumers: the §4 battery discharges `NoetherGeAtAss` on any single
crux-form input; feeding it into `hgrDimLower_of_noetherGe` (§4 of
`NoetherNormalizationBound`) yields `HgrDimLowerMinAtAss`, hence
`HgrDimEqMinAtAss` / `HmultMinAtAss` / `HdimEqMinAtAss` / rb-1 via the
supply chain.
-/

end NoetherLowerAttack
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
