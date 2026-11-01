/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Finiteness.Nakayama
import Mathlib.RingTheory.Noetherian.Defs
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.AssociatedGradedRing
import Appendix_FixedPoint.BezoutChain.Regularity.Grade.GradedDimEq
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedLift
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.MultiplicityNonvanishing
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.NoetherNormalizationBound
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.NoetherLowerAttack
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GatedGradedLower
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.DimTwoEndToEnd
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.SystemOfParametersWiring
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.HSExactClosure
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.WitnessKernelDimTwo
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.CruxLowerFaceDimTwo
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.FiltrationStability
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.WitnessHighAttack

/-!
# Gated discharge lane
discharge attempt on the gated `d = 2` ring (gated-Noether /
gated-dimLower / gated-sopConsume, one ring via `GatedGrLower`
 + `HighD2Close`). All three suggested routes
were attacked; the ring does not close unconditionally (it is exactly
`ker = ⊥` strength at embdim 2, and the missing graded-dimension
theory — graded Nakayama / homogeneous minimal primes / CM-ness of
regular rings — is scoped as large work in `HSDegree` §4). What
proves is the maximal package:

* (§1) The narrowest named gated shape: per-prime `2 ≤ dim gr`
  (`GrDimGe2AtPrime`, a single inequality per prime, no `x`/datum
  binders) + Ass-level form + unconditional iffs joining the D2 ring
  (gated-dimLower, `HkerD2`, `PrimeNoIrredD2`).
* (§2) Gated-datum assembly, carefully scoped: per-prime gated-Noether
  is exactly `2 ≤ dim (S ⧸ ker)` (pinning both directions) is exactly
  `2 ≤ dim gr`; Ass-level `NoetherGeD2Gated ⟺ narrow`.
  The s.o.p. fixes the length-2 numerology (unconditional `hsopD2`
  feeds the residual); the `2 ≤ s` force is the narrow inequality —
  no assembly bypasses it (`s = dim T` for every datum).
* (§3) R-side Artinian-collapse bank for the future `dim gr ≥ 1`
  attack: Nakayama power-collapse + nilpotent-`𝔪` gives `dim R_Q = 0`
  (both unconditional). Missing for `dim gr ≥ 1`: graded Nakayama
  (`gr₊^N = 0` from Artinian) + the filtration link
  (`𝔪^N ⊆ 𝔪^{N+1}` from `gr₊^N = 0`) — scoped, not attempted.
* (§4) genuine discharge for `m ≤ 1`: `embdim Q ≤ m` (regularity +
  height + `dim R = m`), so every gated SPEC is vacuous and the full
  `d = 2` joint closes unconditionally at `m ≤ 1`.
* (§5) Downstream masters on the single narrow remainder `[narrow]`:
  `HkerD2`, the gated SPEC, the `d = 2` joint, HS-route `HwitD2`, the
  HS-chain bundle (fires `HsExactClose`), and the embdim-`≤ 2`
  lower-bound master (embdim 0/1 closed + narrow at 2).

Gate hygiene: the ungated `HsopGrLowerD2AtAss` is proved false
(`GatedGrLower`) and is never concluded; minimality gives
`d = embdim` but does not fix `d = 2`, so the embdim-2 gate cannot
shrink further (the `d`-split at §5 is maximal: `d = 0` trivial,
`d = 1` closed, `d = 2` = narrow, `d ≥ 3` = Ge3, other lanes).

## Status

* §§1–2: unconditional (SPECs + iffs, join the D2 ring).
* §3: unconditional (banked lemmas; `dim gr ≥ 1` not claimed).
* §4: unconditional (discharge for `m ≤ 1`; remainder gains `m ≥ 2`).
* §5: conditional-exact on `[narrow]`.
* Overall: partial (remainder = per-prime `2 ≤ dim gr` at
  embdim-2 Ass primes with `m ≥ 2`, iff-equivalent to the D2 ring).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace GatedDischarge

/-! ## §1. Narrow gated-inequality SPEC + ring joints -/

/-- Per-prime gated graded lower bound at embdim exactly 2: a single
inequality `2 ≤ dim gr` per prime — no `x`/datum binders. The
narrowest gated shape (the `dim R_Q` term of `GrDimLowerD2GatedAtAss`
is folded to `2` by minimality).

Specification (Prop address for the per-prime narrow hypothesis). -/
def GrDimGe2AtPrime {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] : Prop :=
  ∀ (_hemb : 2 = (IsLocalRing.maximalIdeal
    (Localization.AtPrime Q)).spanFinrank),
    2 ≤ ringKrullDim (AssociatedGradedRing.grRegular Q)

/-- Ass-level narrow gated bound: the per-prime inequality at every
Ass prime.

Specification (Prop address for the narrow gated remainder). -/
def GrDimGe2D2AtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) → GrDimGe2AtPrime Q

/-- The narrow bound from gated dim-lower: `dim R_Q = 2` (minimality)
turns `dim R_Q ≤ dim gr` into `2 ≤ dim gr` (gated-dim transport).
-/
theorem grDimGe2_of_grDimLowerD2Gated (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hlower : GatedGradedLower.GrDimLowerD2GatedAtAss m K J) :
    GrDimGe2D2AtAss m K J := by
  intro Q _ hQ hemb
  have hlo := hlower Q hQ hemb
  have hdim2 := SystemOfParametersWiring.sop_consume_dim_atPrime_eq_two Q hemb
  rw [hdim2] at hlo
  exact_mod_cast hlo

#print axioms grDimGe2_of_grDimLowerD2Gated

/-- Gated dim-lower from the narrow bound (transport back through
`dim R_Q = 2`).
-/
theorem grDimLowerD2Gated_of_grDimGe2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (h : GrDimGe2D2AtAss m K J) :
    GatedGradedLower.GrDimLowerD2GatedAtAss m K J := by
  intro Q _ hQ hemb
  have hle := h Q hQ hemb
  have hdim2 := SystemOfParametersWiring.sop_consume_dim_atPrime_eq_two Q hemb
  rw [hdim2]
  exact_mod_cast hle

#print axioms grDimLowerD2Gated_of_grDimGe2

/-- The narrow bound is exactly gated-dim-lower strength.
-/
theorem grDimGe2_iff_grDimLowerD2Gated (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    GrDimGe2D2AtAss m K J ↔
      GatedGradedLower.GrDimLowerD2GatedAtAss m K J :=
  ⟨grDimLowerD2Gated_of_grDimGe2 m K J,
    grDimGe2_of_grDimLowerD2Gated m K J⟩

#print axioms grDimGe2_iff_grDimLowerD2Gated

/-- The narrow bound joins the D2 ring: it is exactly `ker = ⊥`
strength at embdim 2.
-/
theorem grDimGe2_iff_hkerD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    GrDimGe2D2AtAss m K J ↔ WitnessKernelDimTwo.HkerD2AtAss m K J :=
  (grDimGe2_iff_grDimLowerD2Gated m K J).trans
    ((GatedGradedLower.gatedGrLowerD2_iff_grDimLowerD2 m K J).symm.trans
      (DimTwoEndToEnd.highD2Close_sopGrLowerD2Gated_iff_hkerD2 m K J))

#print axioms grDimGe2_iff_hkerD2

/-- The narrow bound is exactly prime/no-irred strength (the
narrowest D2 form).
-/
theorem grDimGe2_iff_primeNoIrredD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    GrDimGe2D2AtAss m K J ↔
      CruxLowerFaceDimTwo.HprimeNoIrredD2AtAss m K J :=
  (grDimGe2_iff_hkerD2 m K J).trans
    (CruxLowerFaceDimTwo.cruxD2_primeNoIrredD2_iff_hkerD2 m K J).symm

#print axioms grDimGe2_iff_primeNoIrredD2

/-! ## §2. Gated-datum assembly (carefully scoped)

Per-prime gated-Noether is exactly `2 ≤ dim (S ⧸ ker)` is exactly
`2 ≤ dim gr`; Ass-level gated-Noether is exactly the narrow bound.
Since `s = dim T` for every injective integral datum (pinning), no
datum assembly can bypass the narrow inequality: the s.o.p. fixes
the length-2 numerology, the inequality carries the force. -/

/-- Per-prime gated-Noether is exactly `2 ≤ dim (S ⧸ ker)`: forward by
pinning (`s = dim T`), backward from any §1 datum (whose number is
`dim T` by pinning).
-/
theorem noetherGeAtPrime_d2_iff_dimGe2_quotKer {K : Type*} [Field K]
    {m : ℕ} (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (g : Fin 2 → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q)) :
    NoetherLowerAttack.NoetherGeAtPrime Q 2 g hgen ↔
      2 ≤ ringKrullDim
        (NoetherNormalizationBound.NoetherQuotKer Q 2 g hgen) := by
  constructor
  · rintro ⟨s, gN, hinj, hint, hds⟩
    have hpin := NoetherLowerAttack.noetherGeNum_eq_dim_quotKer Q 2 g hgen
      s gN hinj hint
    have hds' : (2 : WithBot ℕ∞) ≤ (s : WithBot ℕ∞) := by
      exact_mod_cast hds
    rw [hpin] at hds'
    exact hds'
  · intro hle
    obtain ⟨s, gN, hinj, hint⟩ :=
      NoetherNormalizationBound.noether_integral_data_of_quotKer Q 2 g hgen
    have hpin := NoetherLowerAttack.noetherGeNum_eq_dim_quotKer Q 2 g hgen
      s gN hinj hint
    have hds : (2 : WithBot ℕ∞) ≤ (s : WithBot ℕ∞) := by
      rw [hpin]
      exact hle
    exact ⟨s, gN, hinj, hint, by exact_mod_cast hds⟩

#print axioms noetherGeAtPrime_d2_iff_dimGe2_quotKer

/-- `2 ≤ dim (S ⧸ ker)` is exactly `2 ≤ dim gr` (`quotKerEquiv`
transfer).
-/
theorem dimGe2_quotKer_iff_dimGe2_gr {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (g : Fin 2 → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q)) :
    2 ≤ ringKrullDim (NoetherNormalizationBound.NoetherQuotKer Q 2 g hgen) ↔
      2 ≤ ringKrullDim (AssociatedGradedRing.grRegular Q) := by
  have hTgr : ringKrullDim
        (NoetherNormalizationBound.NoetherQuotKer Q 2 g hgen) =
      ringKrullDim (AssociatedGradedRing.grRegular Q) :=
    MultiplicityNonvanishing.mult_quotKerEquiv_dim Q 2 g hgen
  rw [hTgr]

#print axioms dimGe2_quotKer_iff_dimGe2_gr

/-- Per-prime gated-Noether is exactly `2 ≤ dim gr` (datum
assembly/disassembly through the quotient side).
-/
theorem noetherGeAtPrime_d2_iff_dimGe2_gr {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (g : Fin 2 → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q)) :
    NoetherLowerAttack.NoetherGeAtPrime Q 2 g hgen ↔
      2 ≤ ringKrullDim (AssociatedGradedRing.grRegular Q) :=
  (noetherGeAtPrime_d2_iff_dimGe2_quotKer Q g hgen).trans
    (dimGe2_quotKer_iff_dimGe2_gr Q g hgen)

#print axioms noetherGeAtPrime_d2_iff_dimGe2_gr

/-- Ass-level gated-Noether is exactly the narrow bound: forward via
minimal sop data (pinning `d = 2`) into the per-prime assembly,
backward pointwise.
-/
theorem noetherGeD2Gated_iff_grDimGe2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    GatedGradedLower.NoetherGeD2GatedAtAss m K J ↔
      GrDimGe2D2AtAss m K J := by
  constructor
  · intro hGe Q _ hQ hemb
    obtain ⟨d, g, hgen, hd⟩ := GradedLift.grlift_sop_exists Q
    have heq : d = 2 := hd.trans hemb.symm
    subst heq
    obtain ⟨s, gN, hinj, hint, hds⟩ := hGe Q hQ hemb g hgen
    have hGe' : NoetherLowerAttack.NoetherGeAtPrime Q 2 g hgen :=
      ⟨s, gN, hinj, hint, hds⟩
    exact (noetherGeAtPrime_d2_iff_dimGe2_gr Q g hgen).mp hGe'
  · intro h Q _ hQ hemb g hgen
    have hle : 2 ≤ ringKrullDim (AssociatedGradedRing.grRegular Q) :=
      h Q hQ hemb
    exact (noetherGeAtPrime_d2_iff_dimGe2_gr Q g hgen).mpr hle

#print axioms noetherGeD2Gated_iff_grDimGe2

/-! ## §3. R-side Artinian-collapse bank (for the `dim gr ≥ 1` attack)

The `dim gr ≥ 1` partial attack (excluding `s = 0`, narrowing the
Noether value space from `{0, 1, 2}` to `{1, 2}`) factors through the
R-side collapse banked here: a stabilized maximal-ideal power is `⊥`
(Nakayama), and a nilpotent maximal ideal forces `dim R_Q = 0`
(unique prime). Both unconditional. What is not proved (scoped, not
attempted): graded Nakayama (`gr₊^N = 0` from Artinian `gr`) and the
filtration link (`𝔪^N ⊆ 𝔪^{N+1}` from `gr₊^N = 0`) — each needs
homogeneous-ideal machinery absent from Mathlib v4.34.0. -/

/-- Nakayama in local-ring form: a finitely generated submodule
absorbed by the maximal ideal is `⊥` (the Mathlib general form plus
the unit argument; local copy so this leaf needs no `Bridge`
import).
-/
theorem gatedDischarge_nakayama_eq_bot (R : Type*) [CommRing R]
    [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (N : Submodule R M) (hN : N.FG)
    (hle : N ≤ IsLocalRing.maximalIdeal R • N) : N = ⊥ := by
  obtain ⟨r, hr, hr'⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul
      (IsLocalRing.maximalIdeal R) N hN hle
  have hunit : IsUnit r := by
    by_contra hnu
    have hmem : r ∈ IsLocalRing.maximalIdeal R := by
      by_contra hcon
      exact hnu (IsLocalRing.notMem_maximalIdeal.mp hcon)
    have h1mem : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
      have h := sub_mem hmem hr
      simp at h
    exact (IsLocalRing.notMem_maximalIdeal.mpr isUnit_one) h1mem
  rw [Submodule.eq_bot_iff]
  intro n hn
  have h0 : r • n = 0 := hr' n hn
  obtain ⟨u, hu⟩ := hunit
  have h0' : ((u : Rˣ) : R) • n = 0 := by
    rw [hu]
    exact h0
  have h1 : (((u⁻¹ : Rˣ)) : R) * (((u : Rˣ)) : R) = 1 := u.inv_mul
  calc n = (1 : R) • n := (one_smul _ _).symm
    _ = (((u⁻¹ : Rˣ) : R) * (((u : Rˣ)) : R)) • n := by rw [h1]
    _ = (((u⁻¹ : Rˣ)) : R) • ((((u : Rˣ)) : R) • n) := mul_smul _ _ _
    _ = 0 := by rw [h0', smul_zero]

#print axioms gatedDischarge_nakayama_eq_bot

/-- A stabilized maximal-ideal power is `⊥` (Nakayama; the power is
finitely generated since `R_Q` is Noetherian).
-/
theorem pow_maximalIdeal_eq_bot_of_le_succ {K : Type*} [Field K]
    {m : ℕ} (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] (N : ℕ)
    (hle : (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) ^ N ≤
      (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) ^ (N + 1)) :
    (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) ^ N = ⊥ := by
  have hFG : ((IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)) ^ N).FG :=
    Ideal.fg_of_isNoetherianRing _
  have hsmul : (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) ^ N ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime Q) •
        ((IsLocalRing.maximalIdeal (Localization.AtPrime Q)) ^ N) := by
    rw [smul_eq_mul, ← pow_succ']
    exact hle
  exact gatedDischarge_nakayama_eq_bot _ _ hFG hsmul

#print axioms pow_maximalIdeal_eq_bot_of_le_succ

/-- A nilpotent maximal ideal forces `dim R_Q = 0`: every prime equals
`𝔪` (primes sit below `𝔪` in a local ring and above it by the prime
power-membership rule), so every prime is maximal.
-/
theorem dim_atPrime_eq_zero_of_pow_maximalIdeal_eq_bot {K : Type*}
    [Field K] {m : ℕ} (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (N : ℕ)
    (hN : (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) ^ N = ⊥) :
    ringKrullDim (Localization.AtPrime Q) = 0 := by
  cases N with
  | zero =>
    simp only [pow_zero, Ideal.one_eq_top] at hN
    have h1mem : (1 : Localization.AtPrime Q) ∈
        (⊥ : Ideal (Localization.AtPrime Q)) := by
      rw [← hN]
      exact Submodule.mem_top
    have h1 : (1 : Localization.AtPrime Q) = 0 :=
      (Submodule.mem_bot _).mp h1mem
    exact absurd h1 one_ne_zero
  | succ n =>
    have hN' : (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) ^
        (n + 1) = ⊥ := hN
    have hmax : ∀ P : Ideal (Localization.AtPrime Q),
        P.IsPrime → P.IsMaximal := by
      intro P hP
      have hle : P ≤ IsLocalRing.maximalIdeal (Localization.AtPrime Q) :=
        IsLocalRing.le_maximalIdeal hP.ne_top
      have hge : IsLocalRing.maximalIdeal (Localization.AtPrime Q) ≤ P := by
        intro x hx
        have hmem : x ^ (n + 1) ∈
            (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) ^ (n + 1) :=
          Ideal.pow_mem_pow hx (n + 1)
        rw [hN'] at hmem
        have heq : x ^ (n + 1) = 0 := (Submodule.mem_bot _).mp hmem
        have hpow : x ^ (n + 1) ∈ P := by
          rw [heq]
          exact P.zero_mem
        exact hP.mem_of_pow_mem (n + 1) hpow
      have heq : P = IsLocalRing.maximalIdeal (Localization.AtPrime Q) :=
        le_antisymm hle hge
      rw [heq]
      exact inferInstance
    have hle0 : Ring.KrullDimLE 0 (Localization.AtPrime Q) :=
      Ring.krullDimLE_zero_iff.mpr hmax
    exact ringKrullDimZero_iff_ringKrullDim_eq_zero.mp hle0

#print axioms dim_atPrime_eq_zero_of_pow_maximalIdeal_eq_bot

/-- R-side collapse assembly: a stabilized maximal-ideal power forces
`dim R_Q = 0` (Nakayama + unique prime).
-/
theorem dim_atPrime_eq_zero_of_pow_le_succ {K : Type*} [Field K]
    {m : ℕ} (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] (N : ℕ)
    (hle : (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) ^ N ≤
      (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) ^ (N + 1)) :
    ringKrullDim (Localization.AtPrime Q) = 0 :=
  dim_atPrime_eq_zero_of_pow_maximalIdeal_eq_bot Q N
    (pow_maximalIdeal_eq_bot_of_le_succ Q N hle)

#print axioms dim_atPrime_eq_zero_of_pow_le_succ

/-! ## §4. Genuine discharge for `m ≤ 1` (gate-shrinking)

`embdim Q ≤ m` (regularity identifies embdim with `dim R_Q`, which is
the height of `Q`, bounded by `dim R = m`), so at `m ≤ 1` the
embdim-2 gate is unsatisfiable and every gated SPEC holds vacuously —
hence the full `d = 2` joint closes unconditionally there. The live
remainder gains the `m ≥ 2` gate. -/

/-- `embdim Q ≤ m`: embdim is `dim R_Q` (regularity), `dim R_Q` is the
height of `Q` (localization), height is bounded by `dim R = m`.
-/
theorem embdim_atPrime_le_numVars {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] :
    (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank ≤ m := by
  have h1 := GradedDimEq.grDim_atPrime_eq_spanFinrank Q
  have h2 := IsLocalization.AtPrime.ringKrullDim_eq_height Q
    (Localization.AtPrime Q)
  have h3 := Ideal.height_le_ringKrullDim_of_isPrime (I := Q)
  have h4 := MultiplicityNonvanishing.mult_ringKrullDim_poly K m
  have hle : (((IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank : ℕ) : WithBot ℕ∞) ≤
      ((m : ℕ) : WithBot ℕ∞) := by
    calc (((IsLocalRing.maximalIdeal
            (Localization.AtPrime Q)).spanFinrank : ℕ) : WithBot ℕ∞)
        = ringKrullDim (Localization.AtPrime Q) := h1.symm
      _ = Q.height := h2
      _ ≤ ringKrullDim (MvPolynomial (Fin m) K) := h3
      _ = ((m : ℕ) : WithBot ℕ∞) := h4
  exact_mod_cast hle

#print axioms embdim_atPrime_le_numVars

/-- The narrow bound holds vacuously for `m ≤ 1` (the embdim-2 gate
is unsatisfiable).
-/
theorem grDimGe2_unconditional_of_le_one (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) (hm : m ≤ 1) :
    GrDimGe2D2AtAss m K J := by
  intro Q _ _ hemb
  have hle := embdim_atPrime_le_numVars Q
  have hcon : (2 : ℕ) ≤ 1 := by
    rw [hemb]
    exact hle.trans hm
  omega

#print axioms grDimGe2_unconditional_of_le_one

/-- The B1 gated SPEC holds vacuously for `m ≤ 1`.
-/
theorem hsopGrLowerD2Gated_unconditional_of_le_one (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K)) (hm : m ≤ 1) :
    DimTwoEndToEnd.HsopGrLowerD2GatedAtAss m K J := by
  intro Q _ _ _ hemb _ _
  have hle := embdim_atPrime_le_numVars Q
  have hcon : (2 : ℕ) ≤ 1 := by
    rw [hemb]
    exact hle.trans hm
  omega

#print axioms hsopGrLowerD2Gated_unconditional_of_le_one

/-- The SopConsume gated SPEC holds vacuously for `m ≤ 1`.
-/
theorem sopGrLowerD2Emb_unconditional_of_le_one (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K)) (hm : m ≤ 1) :
    SystemOfParametersWiring.SopGrLowerD2EmbAtAss m K J := by
  intro Q _ _ hemb _ _ _
  have hle := embdim_atPrime_le_numVars Q
  have hcon : (2 : ℕ) ≤ 1 := by
    rw [hemb]
    exact hle.trans hm
  omega

#print axioms sopGrLowerD2Emb_unconditional_of_le_one

/-- Gated Noether holds vacuously for `m ≤ 1`.
-/
theorem noetherGeD2Gated_unconditional_of_le_one (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K)) (hm : m ≤ 1) :
    GatedGradedLower.NoetherGeD2GatedAtAss m K J := by
  intro Q _ _ hemb _ _
  have hle := embdim_atPrime_le_numVars Q
  have hcon : (2 : ℕ) ≤ 1 := by
    rw [hemb]
    exact hle.trans hm
  omega

#print axioms noetherGeD2Gated_unconditional_of_le_one

/-- Gated dim-lower holds vacuously for `m ≤ 1`.
-/
theorem grDimLowerD2Gated_unconditional_of_le_one (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K)) (hm : m ≤ 1) :
    GatedGradedLower.GrDimLowerD2GatedAtAss m K J := by
  intro Q _ _ hemb
  have hle := embdim_atPrime_le_numVars Q
  have hcon : (2 : ℕ) ≤ 1 := by
    rw [hemb]
    exact hle.trans hm
  omega

#print axioms grDimLowerD2Gated_unconditional_of_le_one

/-- `HkerD2AtAss` closes unconditionally for `m ≤ 1` (vacuous gated
SPEC + the B1 §2 collapse).
-/
theorem hkerD2_unconditional_of_le_one (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) (hm : m ≤ 1) :
    WitnessKernelDimTwo.HkerD2AtAss m K J :=
  DimTwoEndToEnd.highD2Close_hkerD2_of_sopGrLowerGated m K J
    (hsopGrLowerD2Gated_unconditional_of_le_one m K J hm)

#print axioms hkerD2_unconditional_of_le_one

/-- The full `d = 2` joint closes unconditionally for `m ≤ 1`.
-/
theorem d2joint_unconditional_of_le_one (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) (hm : m ≤ 1) :
    WitnessKernelDimTwo.HwitD2AtAss m K J ∧
      WitnessKernelDimTwo.HkerD2AtAss m K J ∧
      WitnessKernelDimTwo.HdimGrD2AtAss m K J ∧
      WitnessKernelDimTwo.HhleD2AtAss m K J ∧
      WitnessHighAttack.HnoHomRelHighD2AtAss m K J :=
  DimTwoEndToEnd.highD2Close_d2joint_of_sopGrLowerGated m K J
    (hsopGrLowerD2Gated_unconditional_of_le_one m K J hm)

#print axioms d2joint_unconditional_of_le_one

/-! ## §5. Downstream masters on the narrow remainder -/

/-- `HkerD2AtAss` from the narrow remainder (via the §1 ring joint).

Conditional on exactly `[h]`. -/
theorem hkerD2_of_grDimGe2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (h : GrDimGe2D2AtAss m K J) :
    WitnessKernelDimTwo.HkerD2AtAss m K J :=
  (grDimGe2_iff_hkerD2 m K J).mp h

#print axioms hkerD2_of_grDimGe2

/-- The B1 gated SPEC from the narrow remainder (via §1 + the §2
discharge).

Conditional on exactly `[h]`. -/
theorem hsopGrLowerD2Gated_of_grDimGe2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (h : GrDimGe2D2AtAss m K J) :
    DimTwoEndToEnd.HsopGrLowerD2GatedAtAss m K J :=
  GatedGradedLower.gatedGrLowerD2_of_grDimLowerD2 m K J
    ((grDimGe2_iff_grDimLowerD2Gated m K J).mp h)

#print axioms hsopGrLowerD2Gated_of_grDimGe2

/-- One-shot `d = 2` discharge on the narrow remainder: all five
`d = 2` forms in one tuple.

Conditional on exactly `[h]`. -/
theorem d2joint_of_grDimGe2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (h : GrDimGe2D2AtAss m K J) :
    WitnessKernelDimTwo.HwitD2AtAss m K J ∧
      WitnessKernelDimTwo.HkerD2AtAss m K J ∧
      WitnessKernelDimTwo.HdimGrD2AtAss m K J ∧
      WitnessKernelDimTwo.HhleD2AtAss m K J ∧
      WitnessHighAttack.HnoHomRelHighD2AtAss m K J :=
  DimTwoEndToEnd.highD2Close_d2joint_of_sopGrLowerGated m K J
    (hsopGrLowerD2Gated_of_grDimGe2 m K J h)

#print axioms d2joint_of_grDimGe2

/-- `HwitD2AtAss` from the narrow remainder via the HS route (fires
`HsExactClose`).

Conditional on exactly `[h]`. -/
theorem hwitD2_of_grDimGe2_viaHS (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (h : GrDimGe2D2AtAss m K J) :
    WitnessKernelDimTwo.HwitD2AtAss m K J :=
  HSExactClosure.hsClose_hwitD2_of_sopGrLowerGated m K J
    (hsopGrLowerD2Gated_of_grDimGe2 m K J h)

#print axioms hwitD2_of_grDimGe2_viaHS

/-- One-shot HS-chain bundle on the narrow remainder (fires
`HsExactClose`).

Conditional on exactly `[h]`. -/
theorem hsChainD2_of_grDimGe2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (h : GrDimGe2D2AtAss m K J) :
    WitnessHighAttack.HgrExactD2AtAss m K J ∧
      WitnessHighAttack.HhsDegLowerD2AtAss m K J ∧
      WitnessKernelDimTwo.HwitD2AtAss m K J :=
  HSExactClosure.hsClose_hsChainD2_of_sopGrLowerGated m K J
    (hsopGrLowerD2Gated_of_grDimGe2 m K J h)

#print axioms hsChainD2_of_grDimGe2

/-- Per-prime lower bound at embdim `≤ 2` on the narrow remainder:
embdim 0/1 are the closed instances, embdim 2 is the narrow bound
itself. The maximal gate-split (`d ≥ 3` is Ge3, other lanes).

Conditional on exactly `[h]`. -/
theorem grDimLower_embdim_le_two_of_grDimGe2 (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (h : GrDimGe2D2AtAss m K J)
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J))
    (he2 : (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank ≤ 2) :
    ringKrullDim (Localization.AtPrime Q) ≤
      ringKrullDim (AssociatedGradedRing.grRegular Q) := by
  have htri : (IsLocalRing.maximalIdeal
        (Localization.AtPrime Q)).spanFinrank = 0 ∨
      (IsLocalRing.maximalIdeal
        (Localization.AtPrime Q)).spanFinrank = 1 ∨
      (IsLocalRing.maximalIdeal
        (Localization.AtPrime Q)).spanFinrank = 2 := by omega
  rcases htri with he0 | he1 | he2'
  · exact GradedDimEq.grDimLower_embdim_zero m K J Q hQ he0
  · exact GradedDimEq.grDimLower_embdim_one m K J Q hQ he1
  · have hemb : 2 = (IsLocalRing.maximalIdeal
        (Localization.AtPrime Q)).spanFinrank := he2'.symm
    have hle : 2 ≤ ringKrullDim (AssociatedGradedRing.grRegular Q) :=
      h Q hQ hemb
    have hdim2 := SystemOfParametersWiring.sop_consume_dim_atPrime_eq_two Q hemb
    rw [hdim2]
    exact_mod_cast hle

#print axioms grDimLower_embdim_le_two_of_grDimGe2

/-! ## §6. Residual register (doc-only)

minimal non-circular remainder (verbatim): `GrDimGe2D2AtAss` — per
`Q ∈ Ass(R ⧸ J)` at embdim exactly 2 (with `m ≥ 2`), `2 ≤ dim gr`.
A single inequality per prime; no `x`/datum binders.

why the remainder is minimal and exact (all machine-checked):

* The §1 iffs show the narrow bound is exactly gated-dim-lower
  strength, exactly `HkerD2` strength (joins the D2 ring), and
  exactly prime/no-irred strength (the narrowest
  D2 form). The §2 iffs show per-prime gated-Noether is exactly
  `2 ≤ dim (S ⧸ ker)` is exactly `2 ≤ dim gr`, and Ass-level
  gated-Noether is exactly the narrow bound. Neither the inequality
  nor any gated member can be weakened below ring strength.
* Nothing assumes `hwit`, `hmult`, `hdimEq`, `ker = ⊥`, or any growth
  fact to prove the §§1–2 joints; the only undischarged input in §5
  is the narrow remainder itself.
* The ungated `HsopGrLowerD2AtAss` is dead (refuted in `GatedGrLower`
  §3); minimality pins `d = embdim` but does not fix `d = 2`, so the
  embdim-2 gate is load-bearing and cannot shrink.
* The `m ≤ 1` slice is gone (§4: vacuous gates + unconditional joint);
  the live remainder carries `m ≥ 2`.
* The R-side half of the `dim gr ≥ 1` attack is banked (§3); the
  graded half (graded Nakayama + filtration link) is scoped future
  work needing homogeneous-ideal machinery absent from Mathlib.

consumers: any future per-prime `2 ≤ dim gr` proof at embdim 2
discharges the narrow remainder — hence every `d = 2` form (§5) — by
a single `exact`; the §5 masters fire `HsExactClose` and the B1 §2
joint on `[narrow]`.
-/

end GatedDischarge
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
