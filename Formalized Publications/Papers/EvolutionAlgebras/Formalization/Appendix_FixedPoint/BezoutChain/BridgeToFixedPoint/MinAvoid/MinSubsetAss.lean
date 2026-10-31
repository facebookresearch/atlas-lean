/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoidRungs
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.SuccClosureRungs
import Appendix_FixedPoint.BezoutChain.Geometry.UnmixednessAtLengthK
import Appendix_FixedPoint.BezoutChain.Geometry.UnmixednessAtLengthTwo
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.RegularityBridge
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# `Min ⊆ Ass` + Ass-avoidance attack at rungs `≥ 2`
Task: attack the `MinAvoidRungs` (R3) register — `minSubAss`
per rung (`Min ⊆ Ass` at stage ideals) and `assAvoid` per rung/prime —
feeding `SuccClosureRungs` discharge. Fixed-`hmin` is not re-attacked (settled:
it is the step mod `Min = Ass`) and `hunmixed → hminAvoid` is not
attempted (refuted, field/`⊥`/`0` witness).

## Verdict (minSubAss closed, assAvoid exactly narrowed)

* §1 (unconditional): per-rung/per-prime minimal forms — `MinSubAssRung`
  / `MinSubAssPrime` (the `hsub` binder decomposed) and
  `AssAvoidPrime` (the `AssAvoidRung` binder decomposed), each with an
  `rfl`-decomposition iff.
* §2 (unconditional close): `Min ⊆ Ass` holds over every Noetherian
  ring — Mathlib's `minimalPrimes_annihilator_subset_associatedPrimes`
  (minimal primes over the annihilator are associated, Stacks 0310 via
  localization) plus `Ideal.annihilator_quotient` (`Ann (R ⧸ J) = J`).
  No unmixedness input needed: unmixedness supplies the reverse
  inclusion. Per-rung (`minSubAssRung`) and `∀`-closed (`minSubAss_all`,
  the exact `hsub` shape) forms; `Min = Ass` from unmixedness
  (`minEqAss_of_hunmixed`, per-rung `minEqAssRung_of_hunmixedRung`).
  The d=0/1 splits are subsumed (the general theorem kills them).
* §3 (unconditional): `Ass (R ⧸ J) = {J}` at prime `J`
  (`associatedPrimes_quotient_prime_eq` — colon description
  `isAssociatedPrime_iff` in the domain quotient); hence `Min = Ass`
  at prime stages with no hunmixed input (`minEqAss_of_prime`),
  Ass-avoidance collapses to single avoidance
  (`assAvoidRung_iff_single_of_prime`), the field witness
  `Min = Ass` at `⊥` (`minEqAss_bot_of_field`, with banked
  `hunmixed_bot_of_field`), and step `→` per-prime avoidance
  (`assAvoidPrime_of_step`, via the banked step `⟺` Ass-avoidance).
* §4 (conditional-exact, `hsub` discharged): `hmin_all` from `[hass]`
  alone; full `hsucc` from `[hrung1, hdimEq_all, hass_all]` (rung-1
  step route) and from `[rung1Avoid, hdimEq_all, hass_all]`
  (fixed-family route, via `SuccClosureRungs` §5); per-rung `Min = Ass` and
  `hmin ⟺ assAvoid` from `[hsucc_prefix, hdimEq_j]` (via `UnmixednessAtLengthK`).

## Residual register (verbatim)

closed this lane: [`Min ⊆ Ass` at all stage ideals, unconditional
(Mathlib annihilator route) — the `hsub` binder
discharged]; [`Ass = {J}` at prime stages + `Min = Ass` + avoidance
collapse, unconditional]; [field witness `Min = Ass` at `⊥`];
[per-rung/per-prime minimal forms for `hsub` and `assAvoid`];
[`hmin` from `[hass]`; `hsucc` from `[hrung1/rung1Avoid, hdimEq_all,
hass_all]` — no `hmin`/`hsub` hypotheses]. Open (exact): [fixed-element
Ass-avoidance `hass_all` — per rung it is the step conclusion
(`MinAvoidRungs.step_span_iff_assAvoidRung`), so no independent route: a
verdict, not open work]; [rung-1 step / rung-1 avoidance]; [the
`HdimEq` crux (unchanged)].

## Import DAG

New leaf module (no importers): `BridgeToFixedPoint/MinAvoidRungs` (minimal forms,
iff, masters, field lemmas), `BridgeToFixedPoint/SuccClosureRungs`
(`prefixSlice`, `span_prefixSlice` master),
`Geometry/UnmixednessAtLengthK` (`hunmixed_ge2_of_hdimEqMin`),
`Geometry/UnmixednessAtLengthTwo` (`HdimEqMinAtAss`), `Regularity/RegularityBridge`
(`SuccessiveSMulRegular`), narrow Mathlib. No cycle risk.

## References

Project (`Formalization/Appendix_FixedPoint/BezoutChain/`):

* `BridgeToFixedPoint/MinAvoidRungs.lean` (`MinAvoidRung`/`AssAvoidRung`/
  `MinAvoidPrime`, reused shapes); (step `⟺` Ass-avoidance);
  (the R3 register discharged here);
  (`hunmixed_bot_of_field`); (the refutation respected here).
* `BridgeToFixedPoint/SuccClosureRungs.lean` (`prefixSlice`/`span_prefixSlice`);
  (`hsucc` master); (fixed-family route).
* `BridgeToFixedPoint/FixedPointFromBezout.lean`
  (`statementIndex`/`bridgeSystem`).
* `Geometry/UnmixednessAtLengthK.lean` (`hunmixed_ge2_of_hdimEqMin`);
  `Geometry/UnmixednessAtLengthTwo.lean` (`HdimEqMinAtAss`).

Mathlib v4.34.0 (all read-only):

* `Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes`
  (`RingTheory/Ideal/AssociatedPrime/Localization.lean`).
* `Ideal.annihilator_quotient`
  (`RingTheory/Ideal/Colon.lean`).
* `isAssociatedPrime_iff` (`RingTheory/Ideal/AssociatedPrime/Basic.lean`).
* `Ideal.minimalPrimes_eq_subsingleton_self`
  (`RingTheory/Ideal/MinimalPrime/Basic.lean`).
* `Ideal.IsPrime.mem_or_mem` (`RingTheory/Ideal/Prime.lean`),
  `Ideal.isPrime_iff` (same file).
* `Ideal.mul_mem_right` (`RingTheory/Ideal/Defs.lean`).
* `Submodule.Quotient.mk_smul`/`induction_on`
  (`LinearAlgebra/Quotient/Defs.lean`).
* `Ideal.Quotient.mk_eq_mk`/`eq_zero_iff_mem`
  (`RingTheory/Ideal/Quotient/Defs.lean`).
* `Module.Finite.quotient`/`self`
  (`RingTheory/Finiteness/Basic.lean`, instances).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace MinSubsetAss

/-! ## §1. Per-rung/per-prime minimal forms (unconditional) -/

/-- Per-rung `Min ⊆ Ass` predicate: every minimal prime over the
stage-`j` ideal is associated to the stage quotient — one rung of the
`MinAvoidRungs` `hsub` binder.
-/
def MinSubAssRung (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1)) : Prop :=
  ∀ Q ∈ (MinAvoidRungs.stageIdeal n K c hn j).minimalPrimes,
    Q ∈ associatedPrimes (MvPolynomial (Fin (statementIndex n + 2)) K)
      (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
        MinAvoidRungs.stageIdeal n K c hn j)

/-- Per-prime `Min ⊆ Ass` obligation: the single-`(j, Q)` minimal form —
`Q` minimal over the stage ideal implies `Q` is associated.
-/
def MinSubAssPrime (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1))
    (Q : Ideal (MvPolynomial (Fin (statementIndex n + 2)) K)) : Prop :=
  Q ∈ (MinAvoidRungs.stageIdeal n K c hn j).minimalPrimes →
    Q ∈ associatedPrimes (MvPolynomial (Fin (statementIndex n + 2)) K)
      (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
        MinAvoidRungs.stageIdeal n K c hn j)

/-- Per-prime Ass-avoidance obligation: the single-`(j, P)` minimal form
of `AssAvoidRung` — `P` associated implies the fixed next element is
outside `P`.
-/
def AssAvoidPrime (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1))
    (P : Ideal (MvPolynomial (Fin (statementIndex n + 2)) K)) : Prop :=
  P ∈ associatedPrimes (MvPolynomial (Fin (statementIndex n + 2)) K)
      (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
        MinAvoidRungs.stageIdeal n K c hn j) →
    (bridgeSystem n K c hn) j ∉ P

#print axioms MinSubAssRung
#print axioms MinSubAssPrime
#print axioms AssAvoidPrime

/-- Per-rung `Min ⊆ Ass` is the conjunction of per-prime forms
(unconditional, by `rfl`).
-/
theorem minSubAssRung_iff_forall_prime (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1)) :
    MinSubAssRung n K c hn j ↔ ∀ Q, MinSubAssPrime n K c hn j Q :=
  Iff.rfl

#print axioms minSubAssRung_iff_forall_prime

/-- Per-rung Ass-avoidance is the conjunction of per-prime forms
(unconditional, by `rfl`).
-/
theorem assAvoidRung_iff_forall_prime (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1)) :
    MinAvoidRungs.AssAvoidRung n K c hn j ↔
      ∀ P, AssAvoidPrime n K c hn j P :=
  Iff.rfl

#print axioms assAvoidRung_iff_forall_prime

/-! ## §2. `Min ⊆ Ass` closed unconditionally -/

/-- Minimal primes over `J` are associated to `R ⧸ J` (unconditional):
Mathlib's `minimalPrimes_annihilator_subset_associatedPrimes` (minimal
primes over the annihilator are associated — Stacks 0310 route via
localization; needs `Module.Finite R (R ⧸ J)`, synthesized from the
`quotient`/`self` instances) plus `Ideal.annihilator_quotient`
(`Ann (R ⧸ J) = J`). This closes the `hsub` half of the `MinAvoidRungs`
 register outright — no unmixedness input needed (the
reverse inclusion is what unmixedness supplies).
-/
theorem minSubAss_of_noetherian {R : Type*} [CommRing R]
    [IsNoetherianRing R] (J : Ideal R) :
    ∀ Q ∈ J.minimalPrimes, Q ∈ associatedPrimes R (R ⧸ J) := by
  have h :=
    Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes
      R (R ⧸ J)
  rw [Ideal.annihilator_quotient] at h
  exact h

#print axioms minSubAss_of_noetherian

/-- Per-rung `Min ⊆ Ass` at bridge data (unconditional): the §2 close at
the stage-`j` ideal (`MvPolynomial` over a field is Noetherian).
-/
theorem minSubAssRung (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1)) :
    MinSubAssRung n K c hn j :=
  minSubAss_of_noetherian _

#print axioms minSubAssRung

/-- `∀`-closed `Min ⊆ Ass` over rungs `≥ 2` (unconditional): the exact
`MinAvoidRungs` `hsub` binder, discharged with no hypotheses.
-/
theorem minSubAss_all (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n) :
    ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      ∀ Q ∈ (MinAvoidRungs.stageIdeal n K c hn j).minimalPrimes,
        Q ∈ associatedPrimes (MvPolynomial (Fin (statementIndex n + 2)) K)
          (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
            MinAvoidRungs.stageIdeal n K c hn j) :=
  fun _ _ => minSubAss_of_noetherian _

#print axioms minSubAss_all

/-- `Min = Ass` from unmixedness (unconditional reduction): the
`Ass ⊆ Min` leg (unmixedness — supplied per-rung by `HdimEq` via §4 /
`UnmixednessAtLengthK`) plus the §2 `Min ⊆ Ass` leg.
-/
theorem minEqAss_of_hunmixed {R : Type*} [CommRing R]
    [IsNoetherianRing R] (J : Ideal R)
    (hunmixed : ∀ P ∈ associatedPrimes R (R ⧸ J),
      P ∈ J.minimalPrimes) :
    J.minimalPrimes = associatedPrimes R (R ⧸ J) :=
  Set.eq_of_subset_of_subset (minSubAss_of_noetherian J) hunmixed

#print axioms minEqAss_of_hunmixed

/-- Per-rung `Min = Ass` from per-rung unmixedness (unconditional
reduction): the bridge-data form of `minEqAss_of_hunmixed`.
-/
theorem minEqAssRung_of_hunmixedRung (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1))
    (hunmixed : ∀ P ∈ associatedPrimes
        (MvPolynomial (Fin (statementIndex n + 2)) K)
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          MinAvoidRungs.stageIdeal n K c hn j),
        P ∈ (MinAvoidRungs.stageIdeal n K c hn j).minimalPrimes) :
    (MinAvoidRungs.stageIdeal n K c hn j).minimalPrimes =
      associatedPrimes (MvPolynomial (Fin (statementIndex n + 2)) K)
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          MinAvoidRungs.stageIdeal n K c hn j) :=
  minEqAss_of_hunmixed _ hunmixed

#print axioms minEqAssRung_of_hunmixedRung

/-! ## §3. `Ass (R ⧸ J) = {J}` at prime `J` + avoidance collapses -/

/-- The associated primes of `R ⧸ J` at prime `J` are exactly `{J}`
(unconditional): in the Noetherian case every associated prime is a
colon (`isAssociatedPrime_iff`); in the domain quotient `R ⧸ J` the
colon of a nonzero class is `J` (primality splits `r * a ∈ J` while
the representative stays outside `J`), the colon of `0` is `⊤`
(excluded by primality), and `J` itself is the colon of `mk 1`.
-/
theorem associatedPrimes_quotient_prime_eq {R : Type*} [CommRing R]
    [IsNoetherianRing R] (J : Ideal R) [J.IsPrime] :
    associatedPrimes R (R ⧸ J) = {J} := by
  ext P
  constructor
  · intro hP
    rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff] at hP
    obtain ⟨hprime, x, rfl⟩ := hP
    rw [Set.mem_singleton_iff]
    by_cases hx : x = 0
    · subst hx
      exfalso
      have htop : (⊥ : Submodule R (R ⧸ J)).colon {(0 : R ⧸ J)} = ⊤ := by
        ext r
        simp [Submodule.mem_colon_singleton]
      exact (Ideal.isPrime_iff.mp hprime).1 htop
    · revert hx
      refine Submodule.Quotient.induction_on J x ?_
      intro a ha
      have haJ : a ∉ J := by
        intro hmem
        apply ha
        rw [Ideal.Quotient.mk_eq_mk]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
      ext r
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot,
        ← Submodule.Quotient.mk_smul]
      change (Submodule.Quotient.mk (r * a) : R ⧸ J) = 0 ↔ r ∈ J
      rw [Ideal.Quotient.mk_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      constructor
      · intro h
        exact ((‹J.IsPrime›.mem_or_mem h).resolve_right haJ)
      · intro hr
        exact Ideal.mul_mem_right a J hr
  · have hJmem : J ∈ associatedPrimes R (R ⧸ J) := by
      rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff]
      refine ⟨‹J.IsPrime›, Submodule.Quotient.mk 1, ?_⟩
      ext r
      constructor
      · intro hr
        rw [Submodule.mem_colon_singleton, ← Submodule.Quotient.mk_smul]
        change (Submodule.Quotient.mk (r * 1) : R ⧸ J) ∈
          (⊥ : Submodule R (R ⧸ J))
        rw [mul_one, Submodule.mem_bot, Ideal.Quotient.mk_eq_mk,
          Ideal.Quotient.eq_zero_iff_mem]
        exact hr
      · intro hr
        rw [Submodule.mem_colon_singleton, ← Submodule.Quotient.mk_smul] at hr
        change (Submodule.Quotient.mk (r * 1) : R ⧸ J) ∈
          (⊥ : Submodule R (R ⧸ J)) at hr
        rw [mul_one, Submodule.mem_bot, Ideal.Quotient.mk_eq_mk,
          Ideal.Quotient.eq_zero_iff_mem] at hr
        exact hr
    intro hP
    rw [Set.mem_singleton_iff] at hP
    rw [hP]
    exact hJmem

#print axioms associatedPrimes_quotient_prime_eq

/-- `Min = Ass` at prime `J` (unconditional): both sides are `{J}` —
minimal primes by `Ideal.minimalPrimes_eq_subsingleton_self`,
associated primes by `associatedPrimes_quotient_prime_eq`. Prime stage
ideals need no hunmixed input.
-/
theorem minEqAss_of_prime {R : Type*} [CommRing R]
    [IsNoetherianRing R] (J : Ideal R) [J.IsPrime] :
    J.minimalPrimes = associatedPrimes R (R ⧸ J) := by
  rw [Ideal.minimalPrimes_eq_subsingleton_self,
    associatedPrimes_quotient_prime_eq]

#print axioms minEqAss_of_prime

/-- Ass-avoidance collapses to single avoidance at prime stages
(unconditional reduction): when the stage ideal is prime, the
per-rung Ass obligation is exactly the fixed next element outside the
stage ideal itself.
-/
theorem assAvoidRung_iff_single_of_prime (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1))
    [(MinAvoidRungs.stageIdeal n K c hn j).IsPrime] :
    MinAvoidRungs.AssAvoidRung n K c hn j ↔
      (bridgeSystem n K c hn) j ∉
        MinAvoidRungs.stageIdeal n K c hn j := by
  unfold MinAvoidRungs.AssAvoidRung
  rw [associatedPrimes_quotient_prime_eq]
  constructor
  · intro h
    exact h _ (Set.mem_singleton_iff.mpr rfl)
  · intro h P hP
    rw [Set.mem_singleton_iff] at hP
    subst hP
    exact h

#print axioms assAvoidRung_iff_single_of_prime

/-- `Min = Ass` at `⊥` over a field (unconditional field witness): the
`Ass ⊆ Min` leg is banked (`MinAvoidRungs.hunmixed_bot_of_field`), the
`Min ⊆ Ass` leg is §2 (fields are Noetherian).
-/
theorem minEqAss_bot_of_field (K : Type*) [Field K] :
    (⊥ : Ideal K).minimalPrimes =
      associatedPrimes K (K ⧸ (⊥ : Ideal K)) :=
  Set.eq_of_subset_of_subset (minSubAss_of_noetherian _)
    (MinAvoidRungs.hunmixed_bot_of_field K)

#print axioms minEqAss_bot_of_field

/-- The rung step implies per-prime Ass-avoidance (unconditional
reduction): regularity is avoidance at every Ass prime (the banked
step `⟺` Ass-avoidance, `MinAvoidRungs.step_span_iff_assAvoidRung`),
hence at each prime individually. The converse per prime is false in
general (single-prime avoidance is strictly weaker than regularity),
so fixed-element Ass-avoidance has no independent route below the
step itself.
-/
theorem assAvoidPrime_of_step (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1))
    (hstep : IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (MinAvoidRungs.stageIdeal n K c hn j •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
        ((bridgeSystem n K c hn) j)) :
    ∀ P, AssAvoidPrime n K c hn j P := by
  have hass : MinAvoidRungs.AssAvoidRung n K c hn j :=
    (MinAvoidRungs.step_span_iff_assAvoidRung n K c hn j).mp hstep
  exact (assAvoidRung_iff_forall_prime n K c hn j).mp hass

#print axioms assAvoidPrime_of_step

/-! ## §4. End-to-end: `hsub` discharged from the R3 register -/

/-- The `SuccClosureRungs` `hmin` binder from `[assAvoid]` alone (no `hsub`
hypothesis): `MinAvoidRungs` with `hsub` discharged by §2
(`minSubAss_all`).

Conditional on exactly `[hass]`. -/
theorem hmin_all_of_assAvoid_all (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (hass : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      MinAvoidRungs.AssAvoidRung n K c hn j) :
    ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      MinAvoidRungs.MinAvoidRung n K c hn j :=
  MinAvoidRungs.hmin_all_of_assAvoid_all_of_minSubAss_all n K c hn hass
    (minSubAss_all n K c hn)

#print axioms hmin_all_of_assAvoid_all

/-- Full `hsucc` at bridge data from `[rung-1 step, ∀-HdimEq,
∀-assAvoid]` (NO `hmin`, NO `hsub` hypotheses): `MinAvoidRungs`
with `hsub` discharged by §2. The residual is exactly
`[hrung1, hdimEq_all, hass_all]` — and `hass` is the step per rung
(`MinAvoidRungs.step_span_iff_assAvoidRung`), so the register now reads
`[rung-1 step, HdimEq crux, the steps themselves]`.

Conditional on exactly `[hrung1, hdimEq, hass]`. -/
theorem hsucc_bridgeSystem_of_rung1step_of_hdimEqMin_of_assAvoid
    (K : Type*) [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (hrung1 : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (Ideal.span
            (Set.image (bridgeSystem n K c hn) {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
      ((bridgeSystem n K c hn) k))
    (hdimEq : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex n + 2) K
        (Ideal.span
          (Set.image (bridgeSystem n K c hn) {k | k.val < j.val})))
    (hass : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      MinAvoidRungs.AssAvoidRung n K c hn j) :
    RegularityBridge.SuccessiveSMulRegular (bridgeSystem n K c hn) :=
  MinAvoidRungs.hsucc_bridgeSystem_of_rung1step_of_hdimEqMin_of_assAvoid_of_minSubAss
    K n hn c hrung1 hdimEq hass (minSubAss_all n K c hn)

#print axioms hsucc_bridgeSystem_of_rung1step_of_hdimEqMin_of_assAvoid

/-- Full `hsucc` at bridge data from `[rung-1 Ass-avoidance, ∀-HdimEq,
∀-assAvoid]` (NO diagonality/genericity, NO `hmin`, NO `hsub`): the
`SuccClosureRungs` §5 fixed-family route with `hmin` discharged by
`hmin_all_of_assAvoid_all`.

Conditional on exactly `[hrung1, hdimEq, hass]`. -/
theorem hsucc_bridgeSystem_of_rung1Avoid_of_hdimEqMin_of_assAvoid
    (K : Type*) [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (hrung1 : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      ∀ P ∈ associatedPrimes
        (MvPolynomial (Fin (statementIndex n + 2)) K)
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (Ideal.span
            (Set.image (bridgeSystem n K c hn) {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K)))),
        (bridgeSystem n K c hn) k ∉ P)
    (hdimEq : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex n + 2) K
        (Ideal.span
          (Set.image (bridgeSystem n K c hn) {k | k.val < j.val})))
    (hass : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      MinAvoidRungs.AssAvoidRung n K c hn j) :
    RegularityBridge.SuccessiveSMulRegular (bridgeSystem n K c hn) :=
  SuccClosureRungs.hsucc_bridgeSystem_of_rung1Avoid_of_hdimEqMin_of_minAvoid
    K n hn c hrung1 hdimEq (hmin_all_of_assAvoid_all n K c hn hass)

#print axioms hsucc_bridgeSystem_of_rung1Avoid_of_hdimEqMin_of_assAvoid

/-- Per-rung `Min = Ass` from `[prefix-hsucc, HdimEq]` (conditional-exact):
unmixedness via `UnmixednessAtLengthK.hunmixed_ge2_of_hdimEqMin` at the §1
`prefixSlice` reindexing (transport along `span_prefixSlice`, the
`SuccClosureRungs` §4 pattern) plus the §2 `Min ⊆ Ass` leg.

Conditional on exactly `[hsucc_pre, hdimEq]`. -/
theorem minEqAssRung_of_hsuccPrefix_of_hdimEq (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1)) (hj : 2 ≤ j.val)
    (hsucc_pre : RegularityBridge.SuccessiveSMulRegular
      (SuccClosureRungs.prefixSlice n K c hn j))
    (hdimEq : UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex n + 2) K
      (MinAvoidRungs.stageIdeal n K c hn j)) :
    (MinAvoidRungs.stageIdeal n K c hn j).minimalPrimes =
      associatedPrimes (MvPolynomial (Fin (statementIndex n + 2)) K)
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          MinAvoidRungs.stageIdeal n K c hn j) := by
  have hJ : MinAvoidRungs.stageIdeal n K c hn j =
      Ideal.span (Set.range (SuccClosureRungs.prefixSlice n K c hn j)) :=
    (SuccClosureRungs.span_prefixSlice n K c hn j).symm
  have hunmixed : ∀ P ∈ associatedPrimes
        (MvPolynomial (Fin (statementIndex n + 2)) K)
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          MinAvoidRungs.stageIdeal n K c hn j),
        P ∈ (MinAvoidRungs.stageIdeal n K c hn j).minimalPrimes :=
    UnmixednessAtLengthK.hunmixed_ge2_of_hdimEqMin (statementIndex n + 2) K
      (SuccClosureRungs.prefixSlice n K c hn j) hsucc_pre
      (MinAvoidRungs.stageIdeal n K c hn j) hJ hdimEq hj
  exact Set.eq_of_subset_of_subset (minSubAss_of_noetherian _) hunmixed

#print axioms minEqAssRung_of_hsuccPrefix_of_hdimEq

/-- Per-rung `hmin ⟺ assAvoid` from `[prefix-hsucc, HdimEq]`
(conditional-exact): fixed-`hmin` coincides with fixed-element
Ass-avoidance — i.e. with the step itself — once `Min = Ass` holds.
This is the exact per-rung address of fixed-`hmin`: downstream of
`[hsucc_prefix, hdimEq]`, never an independent lever.

Conditional on exactly `[hsucc_pre, hdimEq]`. -/
theorem minAvoidRung_iff_assAvoidRung_of_hsuccPrefix_of_hdimEq
    (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1)) (hj : 2 ≤ j.val)
    (hsucc_pre : RegularityBridge.SuccessiveSMulRegular
      (SuccClosureRungs.prefixSlice n K c hn j))
    (hdimEq : UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex n + 2) K
      (MinAvoidRungs.stageIdeal n K c hn j)) :
    MinAvoidRungs.MinAvoidRung n K c hn j ↔
      MinAvoidRungs.AssAvoidRung n K c hn j :=
  MinAvoidRungs.minAvoidRung_iff_assAvoidRung_of_minEqAss n K c hn j
    (minEqAssRung_of_hsuccPrefix_of_hdimEq n K c hn j hj hsucc_pre hdimEq)

#print axioms minAvoidRung_iff_assAvoidRung_of_hsuccPrefix_of_hdimEq

/-! ## §5. Residual register (doc only; see module docstring)

closed this lane: [`Min ⊆ Ass` at all stage ideals, unconditional];
[`Ass = {J}` at prime stages + `Min = Ass` + avoidance collapse];
[field witness `Min = Ass` at `⊥`]; [per-rung/per-prime minimal forms];
[`hsucc` end-to-ends with `hsub`/`hmin` discharged]. Open (exact):
[`hass_all` — is the step per rung, verdict not work]; [rung-1 step /
avoidance]; [`HdimEq` crux]. No new remainder beyond the register.
-/

end MinSubsetAss
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
