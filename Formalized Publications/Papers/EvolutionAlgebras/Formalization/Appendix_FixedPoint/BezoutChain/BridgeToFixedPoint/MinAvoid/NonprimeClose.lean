/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.FixedPointFromBezout
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoidRungs
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.AssumptionFeeds.AssReductionRungs
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.AssumptionFeeds.RungOneDiagonalDischarge
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoid.MinAvoidJoin
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.Rung.RungDiagonal
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.Rung.RungDiagonalGap
import Appendix_FixedPoint.BezoutChain.Geometry.UnmixednessAtLengthTwo
import Appendix_FixedPoint.BezoutChain.Regularity.DimensionEquality.SingleAllocator
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.PrimeAvoidance
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.RegularityBridge
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# Nonprime `minAvoid` close
Attack `MinAvoidNonprimeSpec` (S1: minimal avoidance at
nonprime stage ideals) to verdict, then re-fire every S1 §3/§4
master on the split `[prime-single (S2 shape), nonprime (owned)]`
input. Twin of S2 (prime-single); no overlap by construction.
`hdimEq`-family inputs enter only through the allocator SPEC.

## Verdict (conditional-exact, step-strength)

* §1: nonprime SPEC from `∀`-steps / `hass_all` (unconditional
  reductions); steps at nonprime stages from `[below-steps,
  hdimEq, nonprime-SPEC]` (CONDITIONAL-exact); the `∀`-level
  `nonprime-SPEC ⟺ nonprime-steps` iff mod `[below-steps,
  hdimEq]` (CONDITIONAL-exact); `n = 1` vacuity (unconditional);
  the splitter packaging onto `MinAvoidAllSpec`. Nonprime
  `minAvoid` is the nonprime steps mod `[below, hdimEq]` — the
  S1 §2 verdict restricted to nonprime stages. An unconditional
  `∀`-close is not claimed (it would be crux-strength).
* §2 (witnessed narrowing): weaker SPEC `MinAvoidNonprimeOfAssSpec`
  (Ass-gated nonprime avoidance) proved unconditionally, the
  implication (full → weak), the recombination (weak + `hass` →
  full), and the resistance witness: the gap theorem (with an
  embedded prime, some element avoids every minimal prime yet
  lies in an Ass prime) plus tightness (unmixedness is necessary
  for the reverse leg). The `[hdimEq]` pin is load-bearing.
* §3: all 13 full-SPEC S1 §3/§4 masters re-fired on
  `[hprime, hnonprime]` (`_split` suffix) + 2 nonprime-discharged
  variants (`hstepsNP` replaces `hnonprime`; the 2 already-split
  S1 masters need no re-fire and are consumed).
* §4: joint corollary — if S2 wins prime-single unconditionally
  (hypothesis in the stated shape) and S3 wins nonprime
  unconditionally (hypothesis — not proved here), then
  `minAvoid_all` and the `hass`/`hsucc` feed close except rung-1
  (in HD2) and allocator inputs.

Status: nonprime settled (step-strength,
conditional-exact) + witnessed narrowing + feed complete on
`[S2-shape, nonprime]` (+ `[S2-shape, stepsNP]` discharged forms).

## Residual register (verbatim)

closed this lane: [nonprime `⟺` steps mod `[below, hdimEq]` +
`n = 1` vacuity]; [Ass-gated weaker SPEC uncond + gap/tightness
witnesses]; [13 split re-fires + 2 discharged]; [joint corollary
shape]. Open (exact): [`MinAvoidNonprimeSpec` (step-strength —
is the nonprime steps mod `[below, hdimEq]`; verdict, not open
work)]; [S2 prime-single (sibling lane)]; [rung-1 local gates
(in HD2)]; [per-stage `d ≥ 2` allocator ].

## Import DAG

New leaf module (no importers): `BridgeToFixedPoint/MinAvoidJoin` (SPECs +
splitter + §2 verdict + §3/§4 masters), `BridgeToFixedPoint/MinAvoidRungs`
(minimal forms), `BridgeToFixedPoint/AssReductionRungs` (rung lemma +
packaging), `BridgeToFixedPoint/RungOneDiagonalDischarge` (rung-1 gates),
`BridgeToFixedPoint/RungDiagonal` (`rungI0`), `BridgeToFixedPoint/RungDiagonalGap`
(`diagWitness`), `BridgeToFixedPoint/FixedPointFromBezout` (`bridgeSystem`,
`statementIndex`), `Geometry/UnmixednessAtLengthTwo` (`HdimEqMinAtAss`),
`Regularity/SingleAllocator` (allocator),
`Regularity/PrimeAvoidance` (finite selection),
`Regularity/RegularityBridge` (`SuccessiveSMulRegular`), narrow Mathlib.
No cycle risk.

## References

Project (`Formalization/Appendix_FixedPoint/BezoutChain/`):

* `BridgeToFixedPoint/MinAvoid/MinAvoidJoin.lean/:
  397/:429/:461/:488/:517/:542/:568/:603/:638/:668/:700/:728/:
  758/:781/:807` (SPECs, splitter, §2 verdict, §3/§4 masters).
* `BridgeToFixedPoint/AssumptionFeeds/AssReductionRungs.lean` (rung lemma, packaging).
* `BridgeToFixedPoint/MinAvoidRungs.lean` (minimal forms, step iff).
* `Regularity/Avoid/PrimeAvoidance.lean` (finite selection).

Mathlib v4.34.0 (all read-only): `associatedPrimes`,
`AssociatedPrimes.mem_iff`, `isAssociatedPrime_iff`
(`AssociatedPrime/Basic.lean`); `Ideal.minimalPrimes`,
`Ideal.IsMinimalPrime` (`MinimalPrime/Basic.lean`);
`Ideal.finite_minimalPrimes_of_isNoetherianRing`
(`MinimalPrime/Noetherian.lean`); `IsSMulRegular`
(`Regular/IsSMulRegular.lean`); `Ideal.Quotient.mk_eq_mk`,
`Ideal.Quotient.eq_zero_iff_mem`; `Submodule.mem_colon_singleton`,
`Submodule.Quotient.induction_on`, `Submodule.Quotient.mk_smul`.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace NonprimeClose

/-! ## §1. Nonprime verdict: `⟺` steps mod `[below, hdimEq]` -/

/-- Nonprime SPEC from `∀`-steps (unconditional reduction): every
rung-`≥ 2` step gives per-rung `minAvoid` (S1, via the
step-`⟺`-`hass` iff + closed `minSubAss`), hence the nonprime
stages in particular.
-/
theorem minAvoidNonprime_of_steps (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (hsteps : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (MinAvoidRungs.stageIdeal n K c hn j •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
        ((bridgeSystem n K c hn) j)) :
    MinAvoidJoin.MinAvoidNonprimeSpec n K c hn :=
  fun j hj _ => MinAvoidJoin.minAvoidRung_of_step n K c hn j
    (hsteps j hj)

#print axioms minAvoidNonprime_of_steps

/-- Nonprime SPEC from `hass_all` (unconditional reduction): the
per-rung HS packaging (`Min ⊆ Ass` is the closed
`minSubAss`) applied at nonprime stages.
-/
theorem minAvoidNonprime_of_hass (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (hass : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      MinAvoidRungs.AssAvoidRung n K c hn j) :
    MinAvoidJoin.MinAvoidNonprimeSpec n K c hn :=
  fun j hj _ => AssReductionRungs.minAvoidRung_of_hassRung n K c hn j
    (hass j hj)

#print axioms minAvoidNonprime_of_hass

/-- Span-shape step at a nonprime stage from `[below-steps,
`hdimEq`, nonprime-SPEC]` (CONDITIONAL-exact): the HS rung
lemma fired with the SPEC's nonprime-`j` obligation. The exact
converse leg at nonprime stages.

Conditional on exactly `[hsteps, hdimEq, hnonprime]`. -/
theorem stepSpanNonprime_of_steps_of_hdimEq_of_nonprime (n : ℕ)
    (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1)) (hj : 2 ≤ j.val)
    (hP : ¬ (MinAvoidRungs.stageIdeal n K c hn j).IsPrime)
    (hsteps : ∀ k : Fin (statementIndex n + 1), k.val < j.val →
      IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (Ideal.span
            (Set.image (bridgeSystem n K c hn)
              {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
        ((bridgeSystem n K c hn) k))
    (hdimEq : UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex n + 2) K
      (MinAvoidRungs.stageIdeal n K c hn j))
    (hnonprime : MinAvoidJoin.MinAvoidNonprimeSpec n K c hn) :
    IsSMulRegular
      (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
        (MinAvoidRungs.stageIdeal n K c hn j •
        (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
          (MvPolynomial (Fin (statementIndex n + 2)) K))))
      ((bridgeSystem n K c hn) j) :=
  AssReductionRungs.stepSpanRung_of_steps_of_hdimEq_of_minAvoid n K c
    hn j hj hsteps hdimEq (hnonprime j hj hP)

#print axioms stepSpanNonprime_of_steps_of_hdimEq_of_nonprime

/-- `∀`-level `nonprime-SPEC ⟺ nonprime-steps` (conditional-exact
on `[below-steps, hdimEq]`): the S1 per-rung iff closed
over nonprime stages. Forward is the converse leg above;
backward is the unconditional reduction. The nonprime SPEC is
the nonprime steps mod `[below, hdimEq]` — the verdict.

Conditional on exactly `[hstepsBelow, hdimEq]`. -/
theorem minAvoidNonprimeSpec_iff_stepsNonprime_of_stepsBelow_of_hdimEq
    (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (hstepsBelow : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      ∀ k : Fin (statementIndex n + 1), k.val < j.val →
        IsSMulRegular
          (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
            (Ideal.span
              (Set.image (bridgeSystem n K c hn)
                {k' | k'.val < k.val}) •
            (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
              (MvPolynomial (Fin (statementIndex n + 2)) K))))
          ((bridgeSystem n K c hn) k))
    (hdimEq : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex n + 2) K
        (MinAvoidRungs.stageIdeal n K c hn j)) :
    MinAvoidJoin.MinAvoidNonprimeSpec n K c hn ↔
      (∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
        ¬ (MinAvoidRungs.stageIdeal n K c hn j).IsPrime →
        IsSMulRegular
          (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
            (MinAvoidRungs.stageIdeal n K c hn j •
            (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
              (MvPolynomial (Fin (statementIndex n + 2)) K))))
          ((bridgeSystem n K c hn) j)) := by
  constructor
  · intro h j hj hP
    exact (MinAvoidJoin.minAvoidRung_iff_step_of_steps_of_hdimEq
      n K c hn j hj (hstepsBelow j hj) (hdimEq j hj)).mp (h j hj hP)
  · intro h j hj hP
    exact (MinAvoidJoin.minAvoidRung_iff_step_of_steps_of_hdimEq
      n K c hn j hj (hstepsBelow j hj) (hdimEq j hj)).mpr (h j hj hP)

#print axioms minAvoidNonprimeSpec_iff_stepsNonprime_of_stepsBelow_of_hdimEq

/-- `MinAvoidNonprimeSpec` at `n = 1`, unconditional-vacuous (no
hypotheses at all): `Fin (statementIndex 1 + 1) = Fin 1` has no
index with `2 ≤ val`, so the SPEC binder is empty (same vacuity
as S1).
-/
theorem minAvoidNonprimeSpec_n1_vacuous (K : Type*) [Field K]
    (c : Fin 1 → Fin 1 → Fin 1 → K) (hn : 0 < 1) :
    MinAvoidJoin.MinAvoidNonprimeSpec 1 K c hn := by
  intro j hj _
  have h1 : statementIndex 1 + 1 = 1 := rfl
  have hlt := j.isLt
  omega

#print axioms minAvoidNonprimeSpec_n1_vacuous

/-- `MinAvoidAllSpec` from `[prime-singles, nonprime-minimal]`
(unconditional packaging): the S1 splitter iff on the
named SPECs — the exact joint shape of the S2/S3 twin lanes.
-/
theorem minAvoidAllSpec_of_primeSingle_of_nonprime (n : ℕ)
    (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (hprime : MinAvoidJoin.MinAvoidPrimeSingleSpec n K c hn)
    (hnonprime : MinAvoidJoin.MinAvoidNonprimeSpec n K c hn) :
    MinAvoidJoin.MinAvoidAllSpec n K c hn :=
  (MinAvoidJoin.minAvoidAllSpec_iff_primeSingle_nonprime n K c
    hn).mpr ⟨hprime, hnonprime⟩

#print axioms minAvoidAllSpec_of_primeSingle_of_nonprime

/-! ## §2. Witnessed narrowing: Ass-gated SPEC + gap/tightness -/

/-- The Ass-gated nonprime weaker SPEC: at nonprime stages,
Ass-avoidance implies minimal avoidance. Exactly the `minSubAss`
content of `MinAvoidNonprimeSpec`, with the `hass` content
factored out as the hypothesis.
-/
def MinAvoidNonprimeOfAssSpec (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n) : Prop :=
  ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
    ¬ (MinAvoidRungs.stageIdeal n K c hn j).IsPrime →
    MinAvoidRungs.AssAvoidRung n K c hn j →
    MinAvoidRungs.MinAvoidRung n K c hn j

#print axioms MinAvoidNonprimeOfAssSpec

/-- The weaker SPEC holds unconditionally: pointwise the HS
packaging — every minimal prime is associated (closed
`minSubAss`), so an Ass-avoider is a minimal-avoider.
-/
theorem minAvoidNonprimeOfAss_unconditional (n : ℕ) (K : Type*)
    [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n) :
    MinAvoidNonprimeOfAssSpec n K c hn :=
  fun j _ _ hass =>
    AssReductionRungs.minAvoidRung_of_hassRung n K c hn j hass

#print axioms minAvoidNonprimeOfAss_unconditional

/-- The full nonprime SPEC implies the weaker SPEC
(unconditional implication): the gated obligation is discharged
by ignoring the `hass` input.
-/
theorem minAvoidNonprime_implies_ofAss (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (h : MinAvoidJoin.MinAvoidNonprimeSpec n K c hn) :
    MinAvoidNonprimeOfAssSpec n K c hn :=
  fun j hj hP _ => h j hj hP

#print axioms minAvoidNonprime_implies_ofAss

/-- The weaker SPEC + `hass_all` recombines to the full nonprime
SPEC (unconditional reduction): the factored `hass` content is
exactly what the gate needs.
-/
theorem minAvoidNonprime_of_ofAss_of_hass (n : ℕ) (K : Type*)
    [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (hw : MinAvoidNonprimeOfAssSpec n K c hn)
    (hass : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      MinAvoidRungs.AssAvoidRung n K c hn j) :
    MinAvoidJoin.MinAvoidNonprimeSpec n K c hn :=
  fun j hj hP => hw j hj hP (hass j hj)

#print axioms minAvoidNonprime_of_ofAss_of_hass

/-- Gap theorem (unconditional resistance witness): in a general
Noetherian ring, an embedded prime `P ∈ Ass(R ⧸ J)` with
`P ∉ Min(J)` hosts an element avoiding every minimal prime —
so fixed-element minimal avoidance holds of `x` while
Ass-avoidance fails (`x ∈ P ∈ Ass`). Without `Min = Ass` (what
`hdimEq` supplies), the two notions genuinely come apart: the
`[hdimEq]` pin in the §1 converse is load-bearing. Proof: `P`
is prime and lies over `J`, so `P` is contained in no minimal
prime (else minimality forces `P = Q ∈ Min`); finite prime
avoidance selects `x ∈ P` outside all finitely many of them.
-/
theorem exists_minAvoid_not_assAvoid_of_embedded {R : Type*}
    [CommRing R] [IsNoetherianRing R] (J P : Ideal R)
    (hPass : P ∈ associatedPrimes R (R ⧸ J))
    (hPmin : P ∉ J.minimalPrimes) :
    ∃ x ∈ P, ∀ Q ∈ J.minimalPrimes, x ∉ Q := by
  have hfin : J.minimalPrimes.Finite :=
    Ideal.finite_minimalPrimes_of_isNoetherianRing R J
  have hPprime : P.IsPrime := (AssociatedPrimes.mem_iff.mp hPass).isPrime
  have hJP : J ≤ P := by
    obtain ⟨-, x, rfl⟩ :=
      isAssociatedPrime_iff.mp (AssociatedPrimes.mem_iff.mp hPass)
    intro r hr
    rw [Submodule.mem_colon_singleton]
    refine Submodule.Quotient.induction_on J x ?_
    intro a
    rw [Submodule.mem_bot, ← Submodule.Quotient.mk_smul, smul_eq_mul,
      Ideal.Quotient.mk_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right a J hr
  have hle : ∀ Q ∈ J.minimalPrimes, ¬ P ≤ Q := by
    intro Q hQ hPQ
    apply hPmin
    have hQP : Q ≤ P := hQ.2 ⟨hPprime, hJP⟩ hPQ
    have hPQeq : P = Q := le_antisymm hPQ hQP
    rw [hPQeq]
    exact hQ
  obtain ⟨x, hxP, hx⟩ :=
    PrimeAvoidance.exists_mem_notMem_of_forall_not_le_finite
      (s := J.minimalPrimes) (f := id) hfin P P
      (fun Q hQ _ _ => Ideal.IsMinimalPrime.isPrime hQ) P hle
  exact ⟨x, hxP, hx⟩

#print axioms exists_minAvoid_not_assAvoid_of_embedded

/-- Tightness (unconditional): if fixed-element minimal avoidance
always implied Ass-avoidance, every Ass prime would be minimal —
i.e. the unmixedness leg (`Ass ⊆ Min`, supplied per-rung by
`hdimEq`) is necessary for the reverse leg, not a convenience.
Contrapositive of the gap theorem above.
-/
theorem assSubMin_of_forall_minAvoid_imp_assAvoid {R : Type*}
    [CommRing R] [IsNoetherianRing R] (J : Ideal R)
    (h : ∀ x : R, (∀ Q ∈ J.minimalPrimes, x ∉ Q) →
      (∀ P ∈ associatedPrimes R (R ⧸ J), x ∉ P)) :
    ∀ P ∈ associatedPrimes R (R ⧸ J), P ∈ J.minimalPrimes := by
  intro P hP
  by_contra hPmin
  obtain ⟨x, hxP, hxmin⟩ :=
    exists_minAvoid_not_assAvoid_of_embedded J P hP hPmin
  exact (h x hxmin P hP) hxP

#print axioms assSubMin_of_forall_minAvoid_imp_assAvoid

/-- Bridge-data gap corollary (conditional-exact on
`[hembedded]`): the resistance witness at the stage-`j` ideal —
an embedded prime over it hosts an element the fixed family
cannot see, so the stage-`j` `[hdimEq]` input is load-bearing.

Conditional on exactly `[hembedded]`. -/
theorem exists_minAvoid_not_assAvoid_of_embedded_rung (n : ℕ)
    (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1))
    (P : Ideal (MvPolynomial (Fin (statementIndex n + 2)) K))
    (hPass : P ∈ associatedPrimes
      (MvPolynomial (Fin (statementIndex n + 2)) K)
      (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
        MinAvoidRungs.stageIdeal n K c hn j))
    (hPmin : P ∉ (MinAvoidRungs.stageIdeal n K c hn j).minimalPrimes) :
    ∃ x ∈ P,
      ∀ Q ∈ (MinAvoidRungs.stageIdeal n K c hn j).minimalPrimes,
        x ∉ Q :=
  exists_minAvoid_not_assAvoid_of_embedded
    (MinAvoidRungs.stageIdeal n K c hn j) P hPass hPmin

#print axioms exists_minAvoid_not_assAvoid_of_embedded_rung

/-! ## §3. S1 §3/§4 masters re-fired on split inputs -/

/-- S1 re-fired on `[hprime (S2 shape), hnonprime (owned)]`:
full `hass_all` from `[rung-1 step, per-stage allocator,
prime-singles, nonprime-minimal]` (NO `hdimEq`, NO full-`minAvoid`
hypothesis).

Conditional on exactly `[hrung1, halloc, hprime, hnonprime]`. -/
theorem hass_all_of_rung1step_of_alloc_of_minAvoidSpec_split
    (K : Type*) [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (hrung1 : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (Ideal.span
            (Set.image (bridgeSystem n K c hn)
              {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
      ((bridgeSystem n K c hn) k))
    (halloc : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex n + 2) K
        (MinAvoidRungs.stageIdeal n K c hn j) (fun d => 2 ≤ d))
    (hprime : MinAvoidJoin.MinAvoidPrimeSingleSpec n K c hn)
    (hnonprime : MinAvoidJoin.MinAvoidNonprimeSpec n K c hn) :
    ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      MinAvoidRungs.AssAvoidRung n K c hn j :=
  MinAvoidJoin.hass_all_of_rung1step_of_alloc_of_minAvoidSpec K n
    hn c hrung1 halloc
    (minAvoidAllSpec_of_primeSingle_of_nonprime n K c hn hprime
      hnonprime)

#print axioms hass_all_of_rung1step_of_alloc_of_minAvoidSpec_split

/-- S1 re-fired on `[hprime (S2 shape), hnonprime (owned)]`:
full `hass_all` from `[rung-1 avoidance, per-stage allocator,
prime-singles, nonprime-minimal]` (no step hypothesis).

Conditional on exactly `[hrung1, halloc, hprime, hnonprime]`. -/
theorem hass_all_of_rung1Avoid_of_alloc_of_minAvoidSpec_split
    (K : Type*) [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (hrung1 : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      ∀ P ∈ associatedPrimes
        (MvPolynomial (Fin (statementIndex n + 2)) K)
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (Ideal.span
            (Set.image (bridgeSystem n K c hn)
              {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K)))),
        (bridgeSystem n K c hn) k ∉ P)
    (halloc : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex n + 2) K
        (MinAvoidRungs.stageIdeal n K c hn j) (fun d => 2 ≤ d))
    (hprime : MinAvoidJoin.MinAvoidPrimeSingleSpec n K c hn)
    (hnonprime : MinAvoidJoin.MinAvoidNonprimeSpec n K c hn) :
    ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      MinAvoidRungs.AssAvoidRung n K c hn j :=
  MinAvoidJoin.hass_all_of_rung1Avoid_of_alloc_of_minAvoidSpec K n
    hn c hrung1 halloc
    (minAvoidAllSpec_of_primeSingle_of_nonprime n K c hn hprime
      hnonprime)

#print axioms hass_all_of_rung1Avoid_of_alloc_of_minAvoidSpec_split

/-- S1 re-fired on `[hprime (S2 shape), hnonprime (owned)]`:
full `hass_all` from `[local-∀, supp-∀, per-stage allocator,
prime-singles, nonprime-minimal]` (no rung-1 hypothesis).

Conditional on exactly `[local, supp, halloc, hprime,
hnonprime]`. -/
theorem hass_all_of_local_of_supp_of_alloc_of_minAvoidSpec_split
    (K : Type*) [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (hdiag : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      RungOneDiagonalDischarge.HdiagRung1 n K c hn k)
    (hsupp : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      RungOneDiagonalDischarge.HsuppRung1 n K c hn k)
    (halloc : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex n + 2) K
        (MinAvoidRungs.stageIdeal n K c hn j) (fun d => 2 ≤ d))
    (hprime : MinAvoidJoin.MinAvoidPrimeSingleSpec n K c hn)
    (hnonprime : MinAvoidJoin.MinAvoidNonprimeSpec n K c hn) :
    ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      MinAvoidRungs.AssAvoidRung n K c hn j :=
  MinAvoidJoin.hass_all_of_local_of_supp_of_alloc_of_minAvoidSpec
    K n hn c hdiag hsupp halloc
    (minAvoidAllSpec_of_primeSingle_of_nonprime n K c hn hprime
      hnonprime)

#print axioms hass_all_of_local_of_supp_of_alloc_of_minAvoidSpec_split

/-- S1 re-fired on `[hprime (S2 shape), hnonprime (owned)]`:
full `hass_all` from `[local-∀, offcenter-∀, per-stage allocator,
prime-singles, nonprime-minimal]` (NO rung-1, NO `supp`).

Conditional on exactly `[local, offcenter, halloc, hprime,
hnonprime]`. -/
theorem hass_all_of_local_of_offcenter_of_alloc_of_minAvoidSpec_split
    (K : Type*) [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (hdiag : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      RungOneDiagonalDischarge.HdiagRung1 n K c hn k)
    (hoff : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      ∃ i : Fin (statementIndex n + 1),
        i ≠ RungDiagonal.rungI0 n ∧
        shiftConsts n K c hn i i (RungDiagonal.rungI0 n) ≠ 0)
    (halloc : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex n + 2) K
        (MinAvoidRungs.stageIdeal n K c hn j) (fun d => 2 ≤ d))
    (hprime : MinAvoidJoin.MinAvoidPrimeSingleSpec n K c hn)
    (hnonprime : MinAvoidJoin.MinAvoidNonprimeSpec n K c hn) :
    ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      MinAvoidRungs.AssAvoidRung n K c hn j :=
  MinAvoidJoin.hass_all_of_local_of_offcenter_of_alloc_of_minAvoidSpec
    K n hn c hdiag hoff halloc
    (minAvoidAllSpec_of_primeSingle_of_nonprime n K c hn hprime
      hnonprime)

#print axioms hass_all_of_local_of_offcenter_of_alloc_of_minAvoidSpec_split

/-- S1 re-fired on `[hprime (S2 shape), hnonprime (owned)]`:
full `hass_all` at the all-ones-diagonal family from `[per-stage
allocator, prime-singles, nonprime-minimal]` only (no rung-1).

Conditional on exactly `[halloc, hprime, hnonprime]`. -/
theorem hass_all_cDiagOnes_of_alloc_of_minAvoid_split (K : Type*)
    [Field K]
    (n : ℕ) (hn : 0 < n)
    (halloc : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex n + 2) K
        (MinAvoidRungs.stageIdeal n K
          (RungOneDiagonalDischarge.cDiagOnes n K) hn j)
        (fun d => 2 ≤ d))
    (hprime : MinAvoidJoin.MinAvoidPrimeSingleSpec n K
      (RungOneDiagonalDischarge.cDiagOnes n K) hn)
    (hnonprime : MinAvoidJoin.MinAvoidNonprimeSpec n K
      (RungOneDiagonalDischarge.cDiagOnes n K) hn) :
    ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      MinAvoidRungs.AssAvoidRung n K
        (RungOneDiagonalDischarge.cDiagOnes n K) hn j :=
  MinAvoidJoin.hass_all_cDiagOnes_of_alloc_of_minAvoid K n hn
    halloc
    (minAvoidAllSpec_of_primeSingle_of_nonprime n K
      (RungOneDiagonalDischarge.cDiagOnes n K) hn hprime hnonprime)

#print axioms hass_all_cDiagOnes_of_alloc_of_minAvoid_split

/-- S1 re-fired on `[hprime (S2 shape), hnonprime (owned)]`:
full `hass_all` at the Gap witness from `[per-stage allocator,
prime-singles, nonprime-minimal]` only (no rung-1).

Conditional on exactly `[halloc, hprime, hnonprime]`. -/
theorem hass_all_gap_of_alloc_of_minAvoid_split (K : Type*) [Field K]
    (hn : 0 < 3)
    (halloc : ∀ j : Fin (statementIndex 3 + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex 3 + 2) K
        (MinAvoidRungs.stageIdeal 3 K
          (RungDiagonalGap.diagWitness K) hn j)
        (fun d => 2 ≤ d))
    (hprime : MinAvoidJoin.MinAvoidPrimeSingleSpec 3 K
      (RungDiagonalGap.diagWitness K) hn)
    (hnonprime : MinAvoidJoin.MinAvoidNonprimeSpec 3 K
      (RungDiagonalGap.diagWitness K) hn) :
    ∀ j : Fin (statementIndex 3 + 1), 2 ≤ j.val →
      MinAvoidRungs.AssAvoidRung 3 K
        (RungDiagonalGap.diagWitness K) hn j :=
  MinAvoidJoin.hass_all_gap_of_alloc_of_minAvoid K hn halloc
    (minAvoidAllSpec_of_primeSingle_of_nonprime 3 K
      (RungDiagonalGap.diagWitness K) hn hprime hnonprime)

#print axioms hass_all_gap_of_alloc_of_minAvoid_split

/-- S1 re-fired on `[hprime (S2 shape), hnonprime (owned)]`:
full `hass_all` from `[rung-1 step, split allocator,
prime-singles, nonprime-minimal]` (NO `hdimEq` hypothesis; the
`d = 2` / `d ≥ 3` split-allocator slices).

Conditional on exactly `[hrung1, hallocSplit, hprime,
hnonprime]`. -/
theorem hass_all_of_rung1step_of_allocSplit_of_minAvoidSpec_split
    (K : Type*) [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (hrung1 : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (Ideal.span
            (Set.image (bridgeSystem n K c hn)
              {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
      ((bridgeSystem n K c hn) k))
    (hallocSplit : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex n + 2) K
          (MinAvoidRungs.stageIdeal n K c hn j) (fun d => d = 2) ∧
        SingleAllocator.HdimEqMasterAlloc (statementIndex n + 2) K
          (MinAvoidRungs.stageIdeal n K c hn j) (fun d => 3 ≤ d))
    (hprime : MinAvoidJoin.MinAvoidPrimeSingleSpec n K c hn)
    (hnonprime : MinAvoidJoin.MinAvoidNonprimeSpec n K c hn) :
    ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      MinAvoidRungs.AssAvoidRung n K c hn j :=
  MinAvoidJoin.hass_all_of_rung1step_of_allocSplit_of_minAvoidSpec
    K n hn c hrung1 hallocSplit
    (minAvoidAllSpec_of_primeSingle_of_nonprime n K c hn hprime
      hnonprime)

#print axioms hass_all_of_rung1step_of_allocSplit_of_minAvoidSpec_split

/-- S1 re-fired on `[hprime (S2 shape), hnonprime (owned)]`:
full `hsucc` from `[rung-1 step, per-stage allocator,
prime-singles, nonprime-minimal]` (NO `hdimEq` hypothesis).

Conditional on exactly `[hrung1, halloc, hprime, hnonprime]`. -/
theorem hsucc_of_rung1step_of_alloc_of_minAvoidSpec_split
    (K : Type*) [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (hrung1 : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (Ideal.span
            (Set.image (bridgeSystem n K c hn)
              {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
      ((bridgeSystem n K c hn) k))
    (halloc : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex n + 2) K
        (MinAvoidRungs.stageIdeal n K c hn j) (fun d => 2 ≤ d))
    (hprime : MinAvoidJoin.MinAvoidPrimeSingleSpec n K c hn)
    (hnonprime : MinAvoidJoin.MinAvoidNonprimeSpec n K c hn) :
    RegularityBridge.SuccessiveSMulRegular (bridgeSystem n K c hn) :=
  MinAvoidJoin.hsucc_of_rung1step_of_alloc_of_minAvoidSpec K n
    hn c hrung1 halloc
    (minAvoidAllSpec_of_primeSingle_of_nonprime n K c hn hprime
      hnonprime)

#print axioms hsucc_of_rung1step_of_alloc_of_minAvoidSpec_split

/-- S1 re-fired on `[hprime (S2 shape), hnonprime (owned)]`:
full `hsucc` from `[rung-1 avoidance, per-stage allocator,
prime-singles, nonprime-minimal]` (no step hypothesis).

Conditional on exactly `[hrung1, halloc, hprime, hnonprime]`. -/
theorem hsucc_of_rung1Avoid_of_alloc_of_minAvoidSpec_split
    (K : Type*) [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (hrung1 : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      ∀ P ∈ associatedPrimes
        (MvPolynomial (Fin (statementIndex n + 2)) K)
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (Ideal.span
            (Set.image (bridgeSystem n K c hn)
              {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K)))),
        (bridgeSystem n K c hn) k ∉ P)
    (halloc : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex n + 2) K
        (MinAvoidRungs.stageIdeal n K c hn j) (fun d => 2 ≤ d))
    (hprime : MinAvoidJoin.MinAvoidPrimeSingleSpec n K c hn)
    (hnonprime : MinAvoidJoin.MinAvoidNonprimeSpec n K c hn) :
    RegularityBridge.SuccessiveSMulRegular (bridgeSystem n K c hn) :=
  MinAvoidJoin.hsucc_of_rung1Avoid_of_alloc_of_minAvoidSpec K n
    hn c hrung1 halloc
    (minAvoidAllSpec_of_primeSingle_of_nonprime n K c hn hprime
      hnonprime)

#print axioms hsucc_of_rung1Avoid_of_alloc_of_minAvoidSpec_split

/-- S1 re-fired on `[hprime (S2 shape), hnonprime (owned)]`:
full `hsucc` from `[local-∀, supp-∀, per-stage allocator,
prime-singles, nonprime-minimal]` (no rung-1 hypothesis).

Conditional on exactly `[local, supp, halloc, hprime,
hnonprime]`. -/
theorem hsucc_of_local_of_supp_of_alloc_of_minAvoidSpec_split
    (K : Type*) [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (hdiag : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      RungOneDiagonalDischarge.HdiagRung1 n K c hn k)
    (hsupp : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      RungOneDiagonalDischarge.HsuppRung1 n K c hn k)
    (halloc : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex n + 2) K
        (MinAvoidRungs.stageIdeal n K c hn j) (fun d => 2 ≤ d))
    (hprime : MinAvoidJoin.MinAvoidPrimeSingleSpec n K c hn)
    (hnonprime : MinAvoidJoin.MinAvoidNonprimeSpec n K c hn) :
    RegularityBridge.SuccessiveSMulRegular (bridgeSystem n K c hn) :=
  MinAvoidJoin.hsucc_of_local_of_supp_of_alloc_of_minAvoidSpec
    K n hn c hdiag hsupp halloc
    (minAvoidAllSpec_of_primeSingle_of_nonprime n K c hn hprime
      hnonprime)

#print axioms hsucc_of_local_of_supp_of_alloc_of_minAvoidSpec_split

/-- S1 re-fired on `[hprime (S2 shape), hnonprime (owned)]`:
full `hsucc` from `[local-∀, offcenter-∀, per-stage allocator,
prime-singles, nonprime-minimal]` (NO rung-1, NO `supp`).

Conditional on exactly `[local, offcenter, halloc, hprime,
hnonprime]`. -/
theorem hsucc_of_local_of_offcenter_of_alloc_of_minAvoidSpec_split
    (K : Type*) [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (hdiag : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      RungOneDiagonalDischarge.HdiagRung1 n K c hn k)
    (hoff : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      ∃ i : Fin (statementIndex n + 1),
        i ≠ RungDiagonal.rungI0 n ∧
        shiftConsts n K c hn i i (RungDiagonal.rungI0 n) ≠ 0)
    (halloc : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex n + 2) K
        (MinAvoidRungs.stageIdeal n K c hn j) (fun d => 2 ≤ d))
    (hprime : MinAvoidJoin.MinAvoidPrimeSingleSpec n K c hn)
    (hnonprime : MinAvoidJoin.MinAvoidNonprimeSpec n K c hn) :
    RegularityBridge.SuccessiveSMulRegular (bridgeSystem n K c hn) :=
  MinAvoidJoin.hsucc_of_local_of_offcenter_of_alloc_of_minAvoidSpec
    K n hn c hdiag hoff halloc
    (minAvoidAllSpec_of_primeSingle_of_nonprime n K c hn hprime
      hnonprime)

#print axioms hsucc_of_local_of_offcenter_of_alloc_of_minAvoidSpec_split

/-- S1 re-fired on `[hprime (S2 shape), hnonprime (owned)]`:
full `hsucc` at the all-ones-diagonal family from `[per-stage
allocator, prime-singles, nonprime-minimal]` only (no rung-1).

Conditional on exactly `[halloc, hprime, hnonprime]`. -/
theorem hsucc_cDiagOnes_of_alloc_of_minAvoid_split (K : Type*)
    [Field K]
    (n : ℕ) (hn : 0 < n)
    (halloc : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex n + 2) K
        (MinAvoidRungs.stageIdeal n K
          (RungOneDiagonalDischarge.cDiagOnes n K) hn j)
        (fun d => 2 ≤ d))
    (hprime : MinAvoidJoin.MinAvoidPrimeSingleSpec n K
      (RungOneDiagonalDischarge.cDiagOnes n K) hn)
    (hnonprime : MinAvoidJoin.MinAvoidNonprimeSpec n K
      (RungOneDiagonalDischarge.cDiagOnes n K) hn) :
    RegularityBridge.SuccessiveSMulRegular
      (bridgeSystem n K (RungOneDiagonalDischarge.cDiagOnes n K) hn) :=
  MinAvoidJoin.hsucc_cDiagOnes_of_alloc_of_minAvoid K n hn
    halloc
    (minAvoidAllSpec_of_primeSingle_of_nonprime n K
      (RungOneDiagonalDischarge.cDiagOnes n K) hn hprime hnonprime)

#print axioms hsucc_cDiagOnes_of_alloc_of_minAvoid_split

/-- S1 re-fired on `[hprime (S2 shape), hnonprime (owned)]`:
full `hsucc` at the Gap witness from `[per-stage allocator,
prime-singles, nonprime-minimal]` only (no rung-1).

Conditional on exactly `[halloc, hprime, hnonprime]`. -/
theorem hsucc_gap_of_alloc_of_minAvoid_split (K : Type*) [Field K]
    (hn : 0 < 3)
    (halloc : ∀ j : Fin (statementIndex 3 + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex 3 + 2) K
        (MinAvoidRungs.stageIdeal 3 K
          (RungDiagonalGap.diagWitness K) hn j)
        (fun d => 2 ≤ d))
    (hprime : MinAvoidJoin.MinAvoidPrimeSingleSpec 3 K
      (RungDiagonalGap.diagWitness K) hn)
    (hnonprime : MinAvoidJoin.MinAvoidNonprimeSpec 3 K
      (RungDiagonalGap.diagWitness K) hn) :
    RegularityBridge.SuccessiveSMulRegular
      (bridgeSystem 3 K (RungDiagonalGap.diagWitness K) hn) :=
  MinAvoidJoin.hsucc_gap_of_alloc_of_minAvoid K hn halloc
    (minAvoidAllSpec_of_primeSingle_of_nonprime 3 K
      (RungDiagonalGap.diagWitness K) hn hprime hnonprime)

#print axioms hsucc_gap_of_alloc_of_minAvoid_split

/-- Nonprime-discharged `hass_all` (consumes S1): full
`hass_all` from `[rung-1 step, per-stage allocator,
prime-singles, nonprime-steps]` — the `hnonprime` input is
discharged by the §1 reduction (steps give per-rung `minAvoid`
unconditionally), so no nonprime-SPEC hypothesis remains.

Conditional on exactly `[hrung1, halloc, hprime, hstepsNP]`. -/
theorem hass_all_of_rung1step_of_alloc_of_primeSingle_of_stepsNP
    (K : Type*) [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (hrung1 : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (Ideal.span
            (Set.image (bridgeSystem n K c hn)
              {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
      ((bridgeSystem n K c hn) k))
    (halloc : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex n + 2) K
        (MinAvoidRungs.stageIdeal n K c hn j) (fun d => 2 ≤ d))
    (hprime : MinAvoidJoin.MinAvoidPrimeSingleSpec n K c hn)
    (hstepsNP : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      ¬ (MinAvoidRungs.stageIdeal n K c hn j).IsPrime →
      IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (MinAvoidRungs.stageIdeal n K c hn j •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
        ((bridgeSystem n K c hn) j)) :
    ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      MinAvoidRungs.AssAvoidRung n K c hn j :=
  MinAvoidJoin.hass_all_of_rung1step_of_alloc_of_primeSingle_of_nonprimeMin
    K n hn c hrung1 halloc hprime
    (fun j hj hP => MinAvoidJoin.minAvoidRung_of_step n K c hn j
      (hstepsNP j hj hP))

#print axioms hass_all_of_rung1step_of_alloc_of_primeSingle_of_stepsNP

/-- Nonprime-discharged `hsucc` (consumes S1): full `hsucc`
from `[rung-1 step, per-stage allocator, prime-singles,
nonprime-steps]` — the `hnonprime` input is discharged by the §1
reduction, so no nonprime-SPEC hypothesis remains.

Conditional on exactly `[hrung1, halloc, hprime, hstepsNP]`. -/
theorem hsucc_of_rung1step_of_alloc_of_primeSingle_of_stepsNP
    (K : Type*) [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (hrung1 : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (Ideal.span
            (Set.image (bridgeSystem n K c hn)
              {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
      ((bridgeSystem n K c hn) k))
    (halloc : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex n + 2) K
        (MinAvoidRungs.stageIdeal n K c hn j) (fun d => 2 ≤ d))
    (hprime : MinAvoidJoin.MinAvoidPrimeSingleSpec n K c hn)
    (hstepsNP : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      ¬ (MinAvoidRungs.stageIdeal n K c hn j).IsPrime →
      IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (MinAvoidRungs.stageIdeal n K c hn j •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
        ((bridgeSystem n K c hn) j)) :
    RegularityBridge.SuccessiveSMulRegular (bridgeSystem n K c hn) :=
  MinAvoidJoin.hsucc_of_rung1step_of_alloc_of_primeSingle_of_nonprimeMin
    K n hn c hrung1 halloc hprime
    (fun j hj hP => MinAvoidJoin.minAvoidRung_of_step n K c hn j
      (hstepsNP j hj hP))

#print axioms hsucc_of_rung1step_of_alloc_of_primeSingle_of_stepsNP

/-! ## §4. Joint corollary (conditional on S2's stated shape) -/

-- Shared universe for the `∀`-closed twin-win shapes below: the
-- win hypotheses must instantiate at the joint theorems' `K`, so
-- both use this named universe (not independent `Type*`s).
universe uWin

/-- S2's stated unconditional-win shape: the prime-single SPEC
`∀`-closed over all bridge data. Sibling output, taken
here only as an explicit hypothesis — never assumed.
-/
def S2PrimeSingleWin : Prop :=
  ∀ (n : ℕ) (K : Type uWin) [Field K] (c : Fin n → Fin n → Fin n → K)
    (hn : 0 < n),
    MinAvoidJoin.MinAvoidPrimeSingleSpec n K c hn

#print axioms S2PrimeSingleWin

/-- S3's unconditional-win shape: the nonprime SPEC `∀`-closed
over all bridge data. Not proved in this lane (the §1 verdict is
step-strength conditional); taken only as an explicit hypothesis
in the joint corollary below.
-/
def S3NonprimeWin : Prop :=
  ∀ (n : ℕ) (K : Type uWin) [Field K] (c : Fin n → Fin n → Fin n → K)
    (hn : 0 < n),
    MinAvoidJoin.MinAvoidNonprimeSpec n K c hn

#print axioms S3NonprimeWin

/-- Joint corollary (`minAvoid`): if both twin lanes win
unconditionally (S2's stated shape + S3's shape, both as
explicit hypotheses), `MinAvoidAllSpec` closes outright via the
§1 splitter packaging — `minAvoid` is gone as a feed input.

Conditional on exactly `[S2win, S3win]`.

vacuous (kept for bookkeeping): the `hS3` antecedent is
unprovable — `S3NonprimeWin` is false:
`NonprimeAttack.not_minAvoidNonprimeSpec_zero`
(`NonprimeAttack.lean`) refutes
`MinAvoidNonprimeSpec` at zero constants for every `n ≥ 3`
(unconditional). -/
theorem joint_minAvoidAll_of_s2win_of_s3win (hS2 : S2PrimeSingleWin.{uWin})
    (hS3 : S3NonprimeWin.{uWin}) (n : ℕ) (K : Type uWin) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n) :
    MinAvoidJoin.MinAvoidAllSpec n K c hn :=
  minAvoidAllSpec_of_primeSingle_of_nonprime n K c hn (hS2 n K c hn)
    (hS3 n K c hn)

#print axioms joint_minAvoidAll_of_s2win_of_s3win

/-- Joint corollary (`hass` feed): under both twin wins, full
`hass_all` needs only `[rung-1 step, per-stage allocator]` — the
feed goes unconditional except rung-1 (in HD2) and allocator
 inputs.

Conditional on exactly `[hrung1, halloc, S2win, S3win]`.

vacuous (kept for bookkeeping): the `hS3` antecedent is
unprovable — `S3NonprimeWin` is false:
`NonprimeAttack.not_minAvoidNonprimeSpec_zero`
(`NonprimeAttack.lean`) refutes
`MinAvoidNonprimeSpec` at zero constants for every `n ≥ 3`
(unconditional). -/
theorem joint_hass_all_of_s2win_of_s3win (K : Type uWin) [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (hrung1 : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (Ideal.span
            (Set.image (bridgeSystem n K c hn)
              {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
      ((bridgeSystem n K c hn) k))
    (halloc : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex n + 2) K
        (MinAvoidRungs.stageIdeal n K c hn j) (fun d => 2 ≤ d))
    (hS2 : S2PrimeSingleWin.{uWin}) (hS3 : S3NonprimeWin.{uWin}) :
    ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      MinAvoidRungs.AssAvoidRung n K c hn j :=
  MinAvoidJoin.hass_all_of_rung1step_of_alloc_of_primeSingle_of_nonprimeMin
    K n hn c hrung1 halloc (hS2 n K c hn) (hS3 n K c hn)

#print axioms joint_hass_all_of_s2win_of_s3win

/-- Joint corollary (`hsucc` feed): under both twin wins, full
`hsucc` needs only `[rung-1 step, per-stage allocator]` — the
feed goes unconditional except rung-1 (in HD2) and allocator
 inputs.

Conditional on exactly `[hrung1, halloc, S2win, S3win]`.

vacuous (kept for bookkeeping): the `hS3` antecedent is
unprovable — `S3NonprimeWin` is false:
`NonprimeAttack.not_minAvoidNonprimeSpec_zero`
(`NonprimeAttack.lean`) refutes
`MinAvoidNonprimeSpec` at zero constants for every `n ≥ 3`
(unconditional). -/
theorem joint_hsucc_of_s2win_of_s3win (K : Type uWin) [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (hrung1 : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (Ideal.span
            (Set.image (bridgeSystem n K c hn)
              {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
      ((bridgeSystem n K c hn) k))
    (halloc : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex n + 2) K
        (MinAvoidRungs.stageIdeal n K c hn j) (fun d => 2 ≤ d))
    (hS2 : S2PrimeSingleWin.{uWin}) (hS3 : S3NonprimeWin.{uWin}) :
    RegularityBridge.SuccessiveSMulRegular (bridgeSystem n K c hn) :=
  MinAvoidJoin.hsucc_of_rung1step_of_alloc_of_primeSingle_of_nonprimeMin
    K n hn c hrung1 halloc (hS2 n K c hn) (hS3 n K c hn)

#print axioms joint_hsucc_of_s2win_of_s3win

/-! ## §5. Residual register (doc only; see module docstring)

closed this lane: [nonprime `⟺` steps mod `[below, hdimEq]` +
`n = 1` vacuity]; [Ass-gated weaker SPEC uncond + gap/tightness
witnesses]; [13 split re-fires + 2 discharged]; [joint corollary
shape]. Open (exact): [`MinAvoidNonprimeSpec` (step-strength;
verdict)]; [S2 prime-single (sibling)]; [rung-1 gates (HD2)];
[per-stage allocator ]. No new remainder.
-/

end NonprimeClose
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
