/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Localization.FractionRing
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.AssociatedGradedRing
import Appendix_FixedPoint.BezoutChain.Regularity.Grade.GradedDimEq
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedLift
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.WitnessHighAttack
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.DimTwoEndToEnd
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.NoetherNormalizationBound
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.SystemOfParametersWiring
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.WitnessKernelDimTwo

/-!
# Gated gr-lower discharge + ungated refutation
primary (§§1–2): discharge the gated `d = 2` s.o.p.-to-gr residual
(`HsopGrLowerD2GatedAtAss`, B1 §1) through gated Noether data plus
L1-style dimension transport. The gated residual is exactly `ker = ⊥`
strength at embdim 2 (B1 §2 iff), so no unconditional close is
attempted; instead it is moved onto the two minimal gated remainders:

* (§1) the gated `d = 2` Noether datum `NoetherGeD2GatedAtAss`
  (per Ass prime at embdim 2, per minimal family, some integral
  Noether datum has `2 ≤ s`), plus the B1↔SopConsume SPEC bridge
  (the two gated SPECs differ only by binder order);
* (§2) `gatedGrLowerD2_of_noetherGeD2`: the gated residual from the
  gated Noether datum (conditional-exact), via `noetherNum_le_dim_gr`
  (`s ≤ dim gr`) — the s.o.p. numerology is fixed by minimality, the
  force comes from `2 ≤ s`; `gatedGrLowerD2_of_grDimLowerD2`: the
  gated residual from per-prime dim-lower at embdim 2 (L1-style
  transport through `dim R_Q = 2`); both converses, hence both iffs
  (the gated residual is exactly gated-Noether / gated-dimLower
  strength); downstream `HkerD2AtAss` and the 5-tuple `d = 2` joint on
  `[gated-Noether-d2]`; projections from the ungated suppliers
  (`NoetherGeAtAss`, `HgrDimLowerMinAtAss`).

secondary (§3): the ungated SPEC `HsopGrLowerD2AtAss` (HighAttack:667)
is false as stated — formal refutation with the banked witness
(any `m`, any field `K`, `J = ⊥`, `Q = ⊥`, `x = 0`):
`⊥ ∈ Ass(R ⧸ ⊥)` (colon computation), `0 ∈ 𝔪`, the quotient by
`span(range 0) = ⊥` has dimension 0 (it is the fraction field, via
`IsFractionRing.toField`), while `2 ≤ dim gr` fails (the unconditional
upper half `grDim_upper_atPrime` plus `dim AtPrime ⊥ = 0`).

## Status

* §1: SPEC + unconditional (bridge iff, projections).
* §2: discharge conditional-exact on `[NoetherGeD2GatedAtAss]` /
  `[GrDimLowerD2GatedAtAss]`; iffs unconditional; downstream
  conditional-exact on `[gated-Noether-d2]`.
* §3: unconditional (negative result: ungated SPEC refuted).
* Overall: partial (remainders = the two gated `d = 2` forms,
  which join the D2 ring through the §2 iffs).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace GatedGradedLower

/-! ## §1. Gated Noether-`d = 2` SPEC + B1↔SopConsume bridge -/

/-- Per-Ass-prime gated Noether datum at embdim exactly 2: every
minimal spanning family at an embdim-2 prime admits integral Noether
data with `2 ≤ s`. The `d = 2` slice of `NoetherGeAtAss` in gated
(embdim-carrying) form — the stated cross-lane shape: any `d = 2`
Noether close feeds it, and §2 shows it is exactly gated-gr-lower
strength.

Specification (Prop address for the gated `d = 2` Noether hypothesis). -/
def NoetherGeD2GatedAtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    ∀ (_hemb : 2 = (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank)
    (g : Fin 2 → Localization.AtPrime Q)
      (hgen : Ideal.span (Set.range g) =
        IsLocalRing.maximalIdeal (Localization.AtPrime Q)),
      ∃ s, ∃ gN : MvPolynomial (Fin s)
        (NoetherNormalizationBound.NoetherResKl Q) →ₐ[NoetherNormalizationBound.NoetherResKl Q]
        (NoetherNormalizationBound.NoetherQuotKer Q 2 g hgen),
        Function.Injective gN ∧ gN.IsIntegral ∧ 2 ≤ s

/-- The B1 gated SPEC from the SopConsume gated SPEC (rebind the
`hemb`/`x` binders).
-/
theorem gatedGrLower_b1_of_sopConsume (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hgr : SystemOfParametersWiring.SopGrLowerD2EmbAtAss m K J) :
    DimTwoEndToEnd.HsopGrLowerD2GatedAtAss m K J :=
  fun Q _ hQ x hemb hmem hdim0 => hgr Q hQ hemb x hmem hdim0

#print axioms gatedGrLower_b1_of_sopConsume

/-- The SopConsume gated SPEC from the B1 gated SPEC (rebind the
`hemb`/`x` binders).
-/
theorem gatedGrLower_sopConsume_of_b1 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hgr : DimTwoEndToEnd.HsopGrLowerD2GatedAtAss m K J) :
    SystemOfParametersWiring.SopGrLowerD2EmbAtAss m K J :=
  fun Q _ hQ hemb x hmem hdim0 => hgr Q hQ x hemb hmem hdim0

#print axioms gatedGrLower_sopConsume_of_b1

/-- The two gated SPECs agree (binder order only).
-/
theorem gatedGrLower_b1_iff_sopConsume (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    DimTwoEndToEnd.HsopGrLowerD2GatedAtAss m K J ↔
      SystemOfParametersWiring.SopGrLowerD2EmbAtAss m K J :=
  ⟨gatedGrLower_sopConsume_of_b1 m K J,
    gatedGrLower_b1_of_sopConsume m K J⟩

#print axioms gatedGrLower_b1_iff_sopConsume

/-- The gated `d = 2` Noether datum from the general Noether residual
(instantiate `d := 2`).
-/
theorem noetherGeD2Gated_of_noetherGe (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hGe : NoetherNormalizationBound.NoetherGeAtAss m K J) :
    NoetherGeD2GatedAtAss m K J := by
  intro Q _ hQ hemb g hgen
  exact hGe Q hQ g hgen hemb

#print axioms noetherGeD2Gated_of_noetherGe

/-! ## §2. Gated gr-lower discharge (primary)

The gated residual from gated Noether data (via `s ≤ dim gr`) and from
per-prime dim-lower at embdim 2 (L1-style transport through
`dim R_Q = 2`), both converses, both iffs, and the downstream
`HkerD2AtAss` / `d = 2` joint on `[gated-Noether-d2]`. -/

/-- Per-Ass-prime dim-lower at embdim exactly 2 (gated): per
`Q ∈ Ass(R ⧸ J)` at embdim 2, `dim R_Q ≤ dim gr`. The `d = 2` slice of
`HgrDimLowerMinAtAss` in gated form.

Specification (Prop address for the gated `d = 2` dim-lower hypothesis). -/
def GrDimLowerD2GatedAtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    ∀ (_hemb : 2 = (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank),
      ringKrullDim (Localization.AtPrime Q) ≤
        ringKrullDim (AssociatedGradedRing.grRegular Q)

/-- The gated `d = 2` dim-lower from the general lower bound
(restriction to embdim-2 primes).
-/
theorem grDimLowerD2Gated_of_grDimLowerMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hlower : GradedDimEq.HgrDimLowerMinAtAss m K J) :
    GrDimLowerD2GatedAtAss m K J :=
  fun Q _ hQ _ => hlower Q hQ

#print axioms grDimLowerD2Gated_of_grDimLowerMin

/-- The gated residual from gated Noether data: per `Q` at embdim 2,
minimality pins the sop length at 2, the datum gives `2 ≤ s`, and
`s ≤ dim gr` (`noetherNum_le_dim_gr`) closes the lower bound —
regardless of the s.o.p. The s.o.p. fixes the length-2 numerology;
the force is the Noether inequality.

Conditional on exactly `[hGe]`. -/
theorem gatedGrLowerD2_of_noetherGeD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hGe : NoetherGeD2GatedAtAss m K J) :
    DimTwoEndToEnd.HsopGrLowerD2GatedAtAss m K J := by
  intro Q _ hQ x hemb _ _
  obtain ⟨d, g, hgen, hd⟩ := GradedLift.grlift_sop_exists Q
  have heq : d = 2 := hd.trans hemb.symm
  subst heq
  obtain ⟨s, gN, hinj, hint, h2s⟩ := hGe Q hQ hemb g hgen
  have hs := NoetherNormalizationBound.noetherNum_le_dim_gr Q 2 g hgen s gN
    hinj hint
  have h2s' : (2 : WithBot ℕ∞) ≤ ((s : ℕ) : WithBot ℕ∞) := by
    exact_mod_cast h2s
  exact h2s'.trans hs

#print axioms gatedGrLowerD2_of_noetherGeD2

/-- The SopConsume-form gated residual from gated Noether data (via
the §1 bridge).

Conditional on exactly `[hGe]`. -/
theorem gatedGrLowerSopConsume_of_noetherGeD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hGe : NoetherGeD2GatedAtAss m K J) :
    SystemOfParametersWiring.SopGrLowerD2EmbAtAss m K J :=
  gatedGrLower_sopConsume_of_b1 m K J
    (gatedGrLowerD2_of_noetherGeD2 m K J hGe)

#print axioms gatedGrLowerSopConsume_of_noetherGeD2

/-- The gated residual from per-prime dim-lower at embdim 2: L1-style
transport — `dim R_Q = 2` (minimality) turns `dim R_Q ≤ dim gr` into
`2 ≤ dim gr`.

Conditional on exactly `[hlower]`. -/
theorem gatedGrLowerD2_of_grDimLowerD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hlower : GrDimLowerD2GatedAtAss m K J) :
    DimTwoEndToEnd.HsopGrLowerD2GatedAtAss m K J := by
  intro Q _ hQ x hemb _ _
  have hdim2 := SystemOfParametersWiring.sop_consume_dim_atPrime_eq_two Q hemb
  have hlo := hlower Q hQ hemb
  rw [hdim2] at hlo
  exact_mod_cast hlo

#print axioms gatedGrLowerD2_of_grDimLowerD2

/-- Converse: the gated residual gives the gated `d = 2` Noether datum
(via the §1 bridge + the SopConsume yields-form, whose unconditional
§2 s.o.p. feeds the residual).
-/
theorem noetherGeD2Gated_of_gatedGrLowerD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hgr : DimTwoEndToEnd.HsopGrLowerD2GatedAtAss m K J) :
    NoetherGeD2GatedAtAss m K J := by
  have hgrS := gatedGrLower_sopConsume_of_b1 m K J hgr
  intro Q _ hQ hemb g hgen
  exact SystemOfParametersWiring.sopNoether_datumD2_of_gatedGrLower m K J hgrS Q hQ
    hemb g hgen

#print axioms noetherGeD2Gated_of_gatedGrLowerD2

/-- The gated residual is exactly gated-Noether strength at embdim 2.
-/
theorem gatedGrLowerD2_iff_noetherGeD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    DimTwoEndToEnd.HsopGrLowerD2GatedAtAss m K J ↔
      NoetherGeD2GatedAtAss m K J :=
  ⟨noetherGeD2Gated_of_gatedGrLowerD2 m K J,
    gatedGrLowerD2_of_noetherGeD2 m K J⟩

#print axioms gatedGrLowerD2_iff_noetherGeD2

/-- Converse: the gated residual gives per-prime dim-lower at embdim 2
(the unconditional B1 §1 s.o.p. feeds the residual to give
`2 ≤ dim gr`, and `dim R_Q = 2`).
-/
theorem grDimLowerD2Gated_of_gatedGrLowerD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hgr : DimTwoEndToEnd.HsopGrLowerD2GatedAtAss m K J) :
    GrDimLowerD2GatedAtAss m K J := by
  intro Q _ hQ hemb
  obtain ⟨x, hmem, hdim0⟩ :=
    DimTwoEndToEnd.highD2Close_hsopD2_unconditional m K J Q hQ hemb
  have hle : 2 ≤ ringKrullDim (AssociatedGradedRing.grRegular Q) :=
    hgr Q hQ x hemb hmem hdim0
  have hdim2 := SystemOfParametersWiring.sop_consume_dim_atPrime_eq_two Q hemb
  rw [hdim2]
  exact_mod_cast hle

#print axioms grDimLowerD2Gated_of_gatedGrLowerD2

/-- The gated residual is exactly gated-dim-lower strength at embdim 2.
-/
theorem gatedGrLowerD2_iff_grDimLowerD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    DimTwoEndToEnd.HsopGrLowerD2GatedAtAss m K J ↔
      GrDimLowerD2GatedAtAss m K J :=
  ⟨grDimLowerD2Gated_of_gatedGrLowerD2 m K J,
    gatedGrLowerD2_of_grDimLowerD2 m K J⟩

#print axioms gatedGrLowerD2_iff_grDimLowerD2

/-- `HkerD2AtAss` from the gated Noether datum (via the §2 discharge +
the B1 §2 collapse).

Conditional on exactly `[hGe]`. -/
theorem hkerD2_of_noetherGeD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hGe : NoetherGeD2GatedAtAss m K J) :
    WitnessKernelDimTwo.HkerD2AtAss m K J :=
  DimTwoEndToEnd.highD2Close_hkerD2_of_sopGrLowerGated m K J
    (gatedGrLowerD2_of_noetherGeD2 m K J hGe)

#print axioms hkerD2_of_noetherGeD2

/-- One-shot `d = 2` discharge on the gated Noether datum: all five
`d = 2` forms in one tuple (via the §2 discharge + the B1 §2 joint).

Conditional on exactly `[hGe]`. -/
theorem d2joint_of_noetherGeD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hGe : NoetherGeD2GatedAtAss m K J) :
    WitnessKernelDimTwo.HwitD2AtAss m K J ∧
      WitnessKernelDimTwo.HkerD2AtAss m K J ∧
      WitnessKernelDimTwo.HdimGrD2AtAss m K J ∧
      WitnessKernelDimTwo.HhleD2AtAss m K J ∧
      WitnessHighAttack.HnoHomRelHighD2AtAss m K J :=
  DimTwoEndToEnd.highD2Close_d2joint_of_sopGrLowerGated m K J
    (gatedGrLowerD2_of_noetherGeD2 m K J hGe)

#print axioms d2joint_of_noetherGeD2

/-! ## §3. Ungated refutation (secondary)

The ungated SPEC `HsopGrLowerD2AtAss` (HighAttack:667) is false as
stated: it quantifies over length-2 families at all primes with no
embdim gate. Witness (any `m`, any field `K`): `J = ⊥`, `Q = ⊥`,
`x = 0`. Then `0 ∈ 𝔪`, `span (range 0) = ⊥` so the quotient is the
fraction field of dimension 0 (hypotheses hold), but `grRegular ⊥`
has dimension 0 (unconditional upper half), so `2 ≤ dim gr` fails. -/

/-- `⊥` is an associated prime of `R ⧸ ⊥` over a domain
(unconditional): `⊥` is prime, and it is the radical of the annihilator
of `mk 1` (the annihilator is `⊥` since `r • mk 1 = mk r`).
-/
theorem bot_mem_associatedPrimes_quotient_bot (m : ℕ) (K : Type*) [Field K] :
    (⊥ : Ideal (MvPolynomial (Fin m) K)) ∈
      associatedPrimes _ (_ ⧸ (⊥ : Ideal (MvPolynomial (Fin m) K))) := by
  rw [AssociatedPrimes.mem_iff]
  have hcolon : Submodule.colon (⊥ : Submodule (MvPolynomial (Fin m) K)
        (MvPolynomial (Fin m) K ⧸ (⊥ : Ideal (MvPolynomial (Fin m) K))))
        {Submodule.Quotient.mk (1 : MvPolynomial (Fin m) K)} = ⊥ := by
    ext r
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
    have hsmul : r • Submodule.Quotient.mk (1 : MvPolynomial (Fin m) K) =
        Ideal.Quotient.mk ⊥ r := by
      rw [← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one,
        Ideal.Quotient.mk_eq_mk]
    rw [hsmul, Ideal.Quotient.eq_zero_iff_mem]
  refine ⟨inferInstance, Submodule.Quotient.mk 1, ?_⟩
  rw [hcolon]
  exact (Ideal.IsPrime.radical inferInstance).symm

#print axioms bot_mem_associatedPrimes_quotient_bot

/-- The AtPrime-`⊥` fraction field (unconditional): localizing a domain
at the complement of `⊥` is localizing at the nonzero divisors
(`Ideal.primeCompl_bot`), hence a field (`IsFractionRing.toField`).
-/
noncomputable abbrev atPrimeBotField (m : ℕ) (K : Type*) [Field K] :
    Field (Localization.AtPrime (⊥ : Ideal (MvPolynomial (Fin m) K))) := by
  haveI : IsFractionRing (MvPolynomial (Fin m) K)
      (Localization.AtPrime (⊥ : Ideal (MvPolynomial (Fin m) K))) := by
    simpa [Ideal.primeCompl_bot] using
      Localization.isLocalization
        (M := (⊥ : Ideal (MvPolynomial (Fin m) K)).primeCompl)
  exact IsFractionRing.toField (MvPolynomial (Fin m) K)

#print axioms atPrimeBotField

/-- The witness quotient has dimension 0 (unconditional):
`span (range 0) = ⊥`, and the quotient by `⊥` is the fraction field.
-/
theorem dim_quotient_span_zero_atPrimeBot (m : ℕ) (K : Type*) [Field K] :
    ringKrullDim (Localization.AtPrime
        (⊥ : Ideal (MvPolynomial (Fin m) K)) ⧸ Ideal.span
        (Set.range (fun _ : Fin 2 => (0 : Localization.AtPrime
          (⊥ : Ideal (MvPolynomial (Fin m) K)))))) = 0 := by
  have hspan : Ideal.span (Set.range (fun _ : Fin 2 =>
      (0 : Localization.AtPrime
        (⊥ : Ideal (MvPolynomial (Fin m) K))))) = ⊥ := by
    rw [Set.range_const, Ideal.span_singleton_eq_bot.mpr rfl]
  rw [hspan]
  have hdim : ringKrullDim (Localization.AtPrime
      (⊥ : Ideal (MvPolynomial (Fin m) K))) = 0 :=
    @ringKrullDim_eq_zero_of_field _ (atPrimeBotField m K)
  calc ringKrullDim (Localization.AtPrime (⊥ : Ideal (MvPolynomial (Fin m) K)) ⧸
          (⊥ : Ideal (Localization.AtPrime (⊥ : Ideal (MvPolynomial (Fin m) K)))))
        = ringKrullDim (Localization.AtPrime
          (⊥ : Ideal (MvPolynomial (Fin m) K))) :=
        ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _)
    _ = 0 := hdim

#print axioms dim_quotient_span_zero_atPrimeBot

/-- The ungated s.o.p.-to-gr SPEC is false as stated (unconditional
refutation with witness): at `J = ⊥`, `Q = ⊥`, `x = 0` the hypotheses
hold but `2 ≤ dim gr` fails, since `grRegular ⊥` has dimension 0 by
the unconditional upper half. Every consumer must use the gated SPECs.
-/
theorem hsopGrLowerD2AtAss_false (m : ℕ) (K : Type*) [Field K] :
    ¬ WitnessHighAttack.HsopGrLowerD2AtAss m K
      (⊥ : Ideal (MvPolynomial (Fin m) K)) := by
  intro h
  have hQ := bot_mem_associatedPrimes_quotient_bot m K
  have hdim0 := dim_quotient_span_zero_atPrimeBot m K
  have hle := h (⊥ : Ideal (MvPolynomial (Fin m) K)) hQ (fun _ => 0)
    (fun _ => zero_mem _) hdim0
  have hupper := GradedDimEq.grDim_upper_atPrime
    (⊥ : Ideal (MvPolynomial (Fin m) K))
  have hdimAt : ringKrullDim (Localization.AtPrime
      (⊥ : Ideal (MvPolynomial (Fin m) K))) = 0 :=
    @ringKrullDim_eq_zero_of_field _ (atPrimeBotField m K)
  have h20 : (2 : WithBot ℕ∞) ≤ 0 :=
    hle.trans (hupper.trans (le_of_eq hdimAt))
  exact absurd h20 (by decide)

#print axioms hsopGrLowerD2AtAss_false

/-! ## §4. Residual register (doc-only)

minimal non-circular remainders (verbatim):

* `NoetherGeD2GatedAtAss` (gated `d = 2` Noether datum): per
  `Q ∈ Ass(R ⧸ J)` at embdim exactly 2, per minimal family, some
  integral Noether datum has `2 ≤ s`. Closes the gated residual
  (`gatedGrLowerD2_of_noetherGeD2`), hence `HkerD2AtAss` and the full
  `d = 2` joint (`d2joint_of_noetherGeD2`), by one `exact` each.
* `GrDimLowerD2GatedAtAss` (gated `d = 2` dim-lower): per
  `Q ∈ Ass(R ⧸ J)` at embdim exactly 2, `dim R_Q ≤ dim gr`. Closes
  the gated residual (`gatedGrLowerD2_of_grDimLowerD2`) by one `exact`.

why the remainders are minimal and exact (all machine-checked):

* The §2 iffs show the gated residual is exactly gated-Noether
  strength (`gatedGrLowerD2_iff_noetherGeD2`) and exactly
  gated-dim-lower strength (`gatedGrLowerD2_iff_grDimLowerD2`) at
  embdim 2 — hence (via the B1 §2 iff) exactly D2-ring strength.
  Neither remainder can be weakened below ring strength.
* Nothing assumes `hwit`, `hmult`, `hdimEq`, `ker = ⊥`, or any growth
  fact to prove the §2 masters; the only undischarged inputs are the
  gated remainders themselves.
* The ungated `HsopGrLowerD2AtAss` is dead (refuted in §3); the §1
  bridge shows the B1 and SopConsume gated SPECs coincide, so all
  consumers share one gated remainder.

consumers: any future gated-`d = 2` Noether (resp. dim-lower) proof
discharges the gated residual — hence every `d = 2` form — by a single
`exact`; the projections `noetherGeD2Gated_of_noetherGe` and
`grDimLowerD2Gated_of_grDimLowerMin` wire the ungated suppliers.
-/

end GatedGradedLower
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
