/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.FixedPointFromBezout
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.SuccClosureRungs
import Appendix_FixedPoint.BezoutChain.Dimension.RegularSequenceDimDrop
import Appendix_FixedPoint.BezoutChain.Geometry.UnmixednessAtLengthTwo
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.PrimeAvoidance
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.RegularityBridge
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# `hminAvoid` at rungs `≥ 2`: existence, exactness, refutation
Task: close or exactly-narrow `hminAvoid` at rungs `≥ 2` — the fixed next
rung element outside every minimal prime of its stage ideal (the `hmin`
binder of `SuccClosureRungs` §4/§5). Prime avoidance (existence of some avoider)
is banked (`PrimeAvoidance`); the open question is suitability: the avoider
must also serve as the rung element.

## Verdict (partial, exactly narrowed)

* §1 (unconditional): existence-form suitable avoider — some `y ∈ I`
  avoiding every minimal prime over `J` that is also regular mod `J`
  (hence serves as a rung element). New over `YSopStep` §2 (which needs
  `IsLocalRing`, selecting from `𝔪`): selection from a general ideal `I`
  in a general Noetherian ring. Does not close fixed-element `hmin`
  (existence is not fixedness).
* §2 (unconditional reductions + iffs): fixed-element exactness. The rung
  step is iff Ass-avoidance (`step_span_iff_assAvoidRung`, via Mathlib's
  `biUnion_associatedPrimes_eq_compl_regular`); Ass-avoidance is iff
  `hminAvoid` modulo `Min = Ass`
  (`minAvoidRung_iff_assAvoidRung_of_minEqAss`). Hence `hminAvoid` is
  exactly as hard as the rung step itself (mod `Min = Ass`): downstream
  of the step, not an independent lever. Per-rung (`MinAvoidRung`,
  `AssAvoidRung`) and per-prime (`MinAvoidPrime`) minimal forms, plus
  `SuccClosureRungs`-consumable discharge and end-to-end (conditional-exact on
  `[hrung1, hdimEq_all, assAvoid_all, minSubAss_all]`).
* §3 (unconditional refutation): `hminAvoid` does not follow from
  unmixedness (`hminAvoid_not_of_hunmixed`; witness: `K` a field,
  `J = ⊥`, `x = 0` — unmixedness holds vacuously-by-dichotomy while
  `0 ∈ ⊥` kills avoidance). Formalizes the `FinalDischargeHub` §9 verdict
  with a witness.

## Residual register (verbatim)

closed this lane: [existence-form suitable avoider (general `I`,
Noetherian)]; [step ⟺ Ass-avoidance (unconditional);
`hmin` ⟺ Ass-avoidance (mod `Min = Ass`); per-rung/per-prime minimal forms;
`SuccClosureRungs` discharge + end-to-end]; [`hmin`-from-unmixedness refuted
(field/`⊥`/`0` witness)]. Open (exact): [fixed-element Ass-avoidance at
rungs `≥ 2` — equivalent to the step itself, no independent route];
[`Min ⊆ Ass` at stage ideals (the reverse inclusion unmixedness does not
supply)]; [the `HdimEq` crux (unchanged)].

## Import DAG

New leaf module (no importers): `BridgeToFixedPoint/FixedPointFromBezout`,
`BridgeToFixedPoint/SuccClosureRungs`, `Dimension/RegularSequenceDimDrop`,
`Geometry/UnmixednessAtLengthTwo`,
`Regularity/PrimeAvoidance`, `Regularity/RegularityBridge`, narrow Mathlib.
No cycle risk.

## References

Project (`Formalization/Appendix_FixedPoint/BezoutChain/`):

* `BridgeToFixedPoint/SuccClosureRungs.lean` (masters; the `hmin` binder narrowed here).
* `BridgeToFixedPoint/RungStepFromUnmixedness.lean` (§1 adapters + §3
  register-shape master; absorbs the former `Hge2StepData.lean` §1 master).
* `BridgeToFixedPoint/FinalDischargeHub.lean` (§9 fixed-family verdict: unmixedness
  yields only span-level avoidance).
* `Regularity/Avoid/PrimeAvoidance.lean` (finite selection, regularity
  from avoidance, one-step feed).
* `Regularity/Koszul/YSopStep.lean` (local-ring combined selection form).
* `Dimension/RegularSequenceDimDrop.lean` (`span_smul_top`).

Mathlib v4.34.0 (all read-only):

* `biUnion_associatedPrimes_eq_compl_regular`
  (`RingTheory/Regular/IsSMulRegular.lean`).
* `Ideal.finite_minimalPrimes_of_isNoetherianRing`
  (`RingTheory/Ideal/MinimalPrime/Noetherian.lean`).
* `associatedPrimes.finite`
  (`RingTheory/Ideal/AssociatedPrime/Finiteness.lean`).
* `AssociatedPrimes.mem_iff`, `IsAssociatedPrime.isPrime`
  (`RingTheory/Ideal/AssociatedPrime/Basic.lean`).
* `Ideal.IsMinimalPrime`, `Ideal.minimalPrimes`
  (`RingTheory/Ideal/MinimalPrime/Basic.lean`).
* `Ideal.isPrime_iff`, `Ideal.mem_bot`
  (`RingTheory/Ideal/Prime.lean`, `RingTheory/Ideal/Lattice.lean`).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace MinAvoidRungs

/-! ## §1. Suitable avoiders in existence form (unconditional) -/

/-- Existence-form suitable avoider (unconditional reduction): from
per-prime non-containment of `I` over `J.minimalPrimes` and over
`Ass (R ⧸ J)`, one selection over the finite union yields `y ∈ I`
avoiding every minimal prime over `J` that is also regular mod `J` —
i.e. `y` can serve as a rung element. `YSopStep` §2 proves the
local-ring analogue (selection from `𝔪`); this is the general-ideal,
general-Noetherian-ring form. It does not close fixed-element `hmin`.
-/
theorem exists_avoider_regular_of_not_le {R : Type*} [CommRing R]
    [IsNoetherianRing R] (J I : Ideal R)
    (hmin : ∀ Q ∈ J.minimalPrimes, ¬ I ≤ Q)
    (hass : ∀ P ∈ associatedPrimes R (R ⧸ J), ¬ I ≤ P) :
    ∃ y ∈ I, (∀ Q ∈ J.minimalPrimes, y ∉ Q) ∧
      IsSMulRegular (R ⧸ J) y := by
  have hfin : (J.minimalPrimes ∪ associatedPrimes R (R ⧸ J)).Finite :=
    (Ideal.finite_minimalPrimes_of_isNoetherianRing R J).union
      (associatedPrimes.finite R (R ⧸ J))
  obtain ⟨y, hyI, hy⟩ :=
    PrimeAvoidance.exists_mem_notMem_of_forall_not_le_finite
      (s := J.minimalPrimes ∪ associatedPrimes R (R ⧸ J)) (f := id) hfin
      (⊥ : Ideal R) (⊥ : Ideal R)
      (fun Q hQ _ _ => by
        rcases hQ with hQ | hQ
        · exact Ideal.IsMinimalPrime.isPrime hQ
        · exact (AssociatedPrimes.mem_iff.mp hQ).isPrime)
      I
      (fun Q hQ => by
        rcases hQ with hQ | hQ
        · exact hmin Q hQ
        · exact hass Q hQ)
  refine ⟨y, hyI, (fun Q hQ => hy Q (Or.inl hQ)), ?_⟩
  exact PrimeAvoidance.isSMulRegular_of_forall_notMem_associatedPrimes y
    (fun P hP => hy P (Or.inr hP))

#print axioms exists_avoider_regular_of_not_le

/-- Stage-ideal suitable avoider at bridge data (unconditional
reduction): the §1 selection instantiated at the stage-`j` ideal, in
`SuccClosureRungs` span-image shape. Consumable by any future selection-route
lane; it cannot feed the fixed-family `SuccClosureRungs` masters (the selected
`y` need not be the fixed `(bridgeSystem n K c hn) j`).
-/
theorem stage_suitable_avoider (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1))
    (I : Ideal (MvPolynomial (Fin (statementIndex n + 2)) K))
    (hmin : ∀ Q ∈ (Ideal.span (Set.image (bridgeSystem n K c hn)
      {k | k.val < j.val})).minimalPrimes, ¬ I ≤ Q)
    (hass : ∀ P ∈ associatedPrimes (MvPolynomial (Fin (statementIndex n + 2)) K)
      (MvPolynomial (Fin (statementIndex n + 2)) K ⧸ Ideal.span
        (Set.image (bridgeSystem n K c hn) {k | k.val < j.val})), ¬ I ≤ P) :
    ∃ y ∈ I, (∀ Q ∈ (Ideal.span (Set.image (bridgeSystem n K c hn)
      {k | k.val < j.val})).minimalPrimes, y ∉ Q) ∧
      IsSMulRegular (MvPolynomial (Fin (statementIndex n + 2)) K ⧸ Ideal.span
        (Set.image (bridgeSystem n K c hn) {k | k.val < j.val})) y :=
  exists_avoider_regular_of_not_le _ I hmin hass

#print axioms stage_suitable_avoider

/-! ## §2. Fixed-element exactness: per-rung/per-prime minimal forms + iffs -/

/-- Regularity iff Ass-avoidance (unconditional): `x` is regular on `M`
iff it lies outside every associated prime, both directions from
Mathlib's union description `biUnion_associatedPrimes_eq_compl_regular`
(`PrimeAvoidance` banks only the reverse direction).
-/
theorem isSMulRegular_iff_forall_notMem_ass {R : Type*} [CommRing R]
    [IsNoetherianRing R] (M : Type*) [AddCommGroup M] [Module R M]
    (x : R) :
    IsSMulRegular M x ↔ ∀ P ∈ associatedPrimes R M, x ∉ P := by
  constructor
  · intro hx P hP hmem
    have hU := biUnion_associatedPrimes_eq_compl_regular R M
    have hmemU : x ∈ ⋃ P ∈ associatedPrimes R M, (P : Set R) :=
      Set.mem_iUnion₂.mpr ⟨P, hP, hmem⟩
    rw [hU] at hmemU
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hmemU
    exact (hmemU hx).elim
  · exact PrimeAvoidance.isSMulRegular_of_forall_notMem_associatedPrimes x

#print axioms isSMulRegular_iff_forall_notMem_ass

/-- Minimal avoidance from Ass-avoidance + the reverse inclusion
(unconditional reduction): if every minimal prime over `J` is associated,
a fixed Ass-avoider is a minimal-avoider. One line; the content is the
exact hypothesis (`Min ⊆ Ass`, which unmixedness does not supply).
-/
theorem hminAvoid_of_assAvoid_of_minSubAss {R : Type*} [CommRing R]
    (J : Ideal R) (x : R)
    (hsub : ∀ Q ∈ J.minimalPrimes, Q ∈ associatedPrimes R (R ⧸ J))
    (hav : ∀ P ∈ associatedPrimes R (R ⧸ J), x ∉ P) :
    ∀ Q ∈ J.minimalPrimes, x ∉ Q :=
  fun Q hQ => hav Q (hsub Q hQ)

#print axioms hminAvoid_of_assAvoid_of_minSubAss

/-- Ass-avoidance from minimal avoidance + unmixedness (unconditional
reduction): the `Hge2StepData` §1 core in register shape — every Ass
prime is minimal, hence avoided.
-/
theorem assAvoid_of_hminAvoid_of_subAss {R : Type*} [CommRing R]
    (J : Ideal R) (x : R)
    (hunmixed : ∀ P ∈ associatedPrimes R (R ⧸ J), P ∈ J.minimalPrimes)
    (hmin : ∀ Q ∈ J.minimalPrimes, x ∉ Q) :
    ∀ P ∈ associatedPrimes R (R ⧸ J), x ∉ P :=
  fun P hP => hmin P (hunmixed P hP)

#print axioms assAvoid_of_hminAvoid_of_subAss

/-- Minimal avoidance iff Ass-avoidance modulo `Min = Ass`
(unconditional): under set-equality of minimal and associated primes,
the fixed-element obligations coincide.
-/
theorem hminAvoid_iff_assAvoid_of_minEqAss {R : Type*} [CommRing R]
    (J : Ideal R) (x : R)
    (heq : J.minimalPrimes = associatedPrimes R (R ⧸ J)) :
    (∀ Q ∈ J.minimalPrimes, x ∉ Q) ↔
      (∀ P ∈ associatedPrimes R (R ⧸ J), x ∉ P) := by
  rw [heq]

#print axioms hminAvoid_iff_assAvoid_of_minEqAss

/-- The stage-`j` ideal (abbrev for statement readability; reducible so
`SuccClosureRungs`-binder defeq is transparent).
-/
noncomputable abbrev stageIdeal (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1)) :
    Ideal (MvPolynomial (Fin (statementIndex n + 2)) K) :=
  Ideal.span (Set.image (bridgeSystem n K c hn) {k | k.val < j.val})

/-- Per-rung minimal-avoidance predicate: the fixed next element outside
every minimal prime of its stage ideal — one rung of the `SuccClosureRungs`
`hmin` binder.
-/
def MinAvoidRung (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1)) : Prop :=
  ∀ P ∈ (stageIdeal n K c hn j).minimalPrimes,
    (bridgeSystem n K c hn) j ∉ P

/-- Per-rung Ass-avoidance predicate in register shape (ideal quotient):
the fixed next element outside every associated prime of the stage
quotient.
-/
def AssAvoidRung (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1)) : Prop :=
  ∀ P ∈ associatedPrimes (MvPolynomial (Fin (statementIndex n + 2)) K)
    (MvPolynomial (Fin (statementIndex n + 2)) K ⧸ stageIdeal n K c hn j),
    (bridgeSystem n K c hn) j ∉ P

/-- Per-prime minimal obligation: the single-`(j, P)` minimal form of
`hminAvoid` — `P` minimal over the stage ideal implies the fixed next
element is outside `P`.
-/
def MinAvoidPrime (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1))
    (P : Ideal (MvPolynomial (Fin (statementIndex n + 2)) K)) : Prop :=
  P ∈ (stageIdeal n K c hn j).minimalPrimes →
    (bridgeSystem n K c hn) j ∉ P

#print axioms stageIdeal
#print axioms MinAvoidRung
#print axioms AssAvoidRung
#print axioms MinAvoidPrime

/-- Per-rung form is the conjunction of per-prime forms (unconditional,
by `rfl`): the minimal per-`(j, P)` decomposition of `hminAvoid`.
-/
theorem minAvoidRung_iff_forall_prime (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1)) :
    MinAvoidRung n K c hn j ↔ ∀ P, MinAvoidPrime n K c hn j P :=
  Iff.rfl

#print axioms minAvoidRung_iff_forall_prime

/-- Per-rung minimal avoidance iff per-rung Ass-avoidance modulo
`Min = Ass` at the stage ideal (unconditional): the exact narrowing —
`hminAvoid` at rung `j` coincides with fixed-element Ass-avoidance once
both inclusions hold.
-/
theorem minAvoidRung_iff_assAvoidRung_of_minEqAss (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1))
    (heq : (stageIdeal n K c hn j).minimalPrimes =
      associatedPrimes (MvPolynomial (Fin (statementIndex n + 2)) K)
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          stageIdeal n K c hn j)) :
    MinAvoidRung n K c hn j ↔ AssAvoidRung n K c hn j :=
  hminAvoid_iff_assAvoid_of_minEqAss _ _ heq

#print axioms minAvoidRung_iff_assAvoidRung_of_minEqAss

/-- The rung step iff per-rung Ass-avoidance (unconditional): the
`• ⊤`-quotient step conclusion is equivalent to the fixed next element
avoiding every Ass prime of the stage quotient (`span_smul_top` bridge
+ the §2 iff). Hence fixed-element Ass-avoidance is exactly as hard as
the step itself — no independent route.
-/
theorem step_span_iff_assAvoidRung (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1)) :
    IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (stageIdeal n K c hn j •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
        ((bridgeSystem n K c hn) j) ↔
      AssAvoidRung n K c hn j := by
  unfold stageIdeal AssAvoidRung
  rw [RegularSequenceDimDrop.span_smul_top]
  exact isSMulRegular_iff_forall_notMem_ass _ _

#print axioms step_span_iff_assAvoidRung

/-- The `SuccClosureRungs` `hmin` binder from `[assAvoid, Min ⊆ Ass]`
(conditional-exact): per-rung discharge in `SuccClosureRungs`-consumable shape.
Note the exactness sting: by `step_span_iff_assAvoidRung`, `assAvoid`
is the step conclusion, so this rewrites `hmin` downstream of the step
rather than supplying it.

Conditional on exactly `[hass, hsub]`. -/
theorem hmin_all_of_assAvoid_all_of_minSubAss_all (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (hass : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      AssAvoidRung n K c hn j)
    (hsub : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      ∀ Q ∈ (stageIdeal n K c hn j).minimalPrimes,
        Q ∈ associatedPrimes (MvPolynomial (Fin (statementIndex n + 2)) K)
          (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
            stageIdeal n K c hn j)) :
    ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      MinAvoidRung n K c hn j :=
  fun j hj => hminAvoid_of_assAvoid_of_minSubAss _ _ (hsub j hj) (hass j hj)

#print axioms hmin_all_of_assAvoid_all_of_minSubAss_all

/-- Full `hsucc` at bridge data from `[rung-1 step, ∀-HdimEq,
∀-assAvoid, ∀-Min⊆Ass]` (NO `hmin` hypothesis): the `SuccClosureRungs` §4 master
with `hmin` discharged by the corollary above. The residual is
rewritten, not removed (`assAvoid` is the step by
`step_span_iff_assAvoidRung`).

Conditional on exactly `[hrung1, hdimEq, hass, hsub]`. -/
theorem hsucc_bridgeSystem_of_rung1step_of_hdimEqMin_of_assAvoid_of_minSubAss
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
      AssAvoidRung n K c hn j)
    (hsub : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      ∀ Q ∈ (stageIdeal n K c hn j).minimalPrimes,
        Q ∈ associatedPrimes (MvPolynomial (Fin (statementIndex n + 2)) K)
          (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
            stageIdeal n K c hn j)) :
    RegularityBridge.SuccessiveSMulRegular (bridgeSystem n K c hn) :=
  SuccClosureRungs.hsucc_bridgeSystem_of_rung1step_of_hdimEqMin_of_minAvoid K n hn c
    hrung1 hdimEq
    (hmin_all_of_assAvoid_all_of_minSubAss_all n K c hn hass hsub)

#print axioms hsucc_bridgeSystem_of_rung1step_of_hdimEqMin_of_assAvoid_of_minSubAss

/-! ## §3. `hminAvoid` does not follow from unmixedness (unconditional refutation) -/

/-- `⊥` is a minimal prime over `⊥` in a field (unconditional): `⊥` is
prime (`x * y = 0 → x = 0 ∨ y = 0`) and minimality is `bot_le`.
-/
theorem bot_mem_minimalPrimes_bot_of_field (K : Type*) [Field K] :
    (⊥ : Ideal K) ∈ (⊥ : Ideal K).minimalPrimes := by
  have hprime : (⊥ : Ideal K).IsPrime := by
    refine Ideal.isPrime_iff.mpr ⟨?_, ?_⟩
    · exact bot_ne_top
    · intro x y hxy
      rw [Ideal.mem_bot] at hxy ⊢
      exact mul_eq_zero.mp hxy
  exact ⟨⟨hprime, le_rfl⟩, fun Q _ _ => bot_le⟩

#print axioms bot_mem_minimalPrimes_bot_of_field

/-- Unmixedness at `J = ⊥` over a field (unconditional): every Ass prime
is prime, hence `= ⊥` (a nonzero member would be a unit, forcing `⊤`),
hence minimal over `⊥`.
-/
theorem hunmixed_bot_of_field (K : Type*) [Field K] :
    ∀ P ∈ associatedPrimes K (K ⧸ (⊥ : Ideal K)),
      P ∈ (⊥ : Ideal K).minimalPrimes := by
  intro P hP
  have hprime : P.IsPrime := (AssociatedPrimes.mem_iff.mp hP).isPrime
  have hPbot : P = ⊥ := by
    refine le_antisymm (fun x hx => ?_) bot_le
    rw [Ideal.mem_bot]
    by_contra hx0
    exact hprime.ne_top
      (P.eq_top_of_isUnit_mem hx (isUnit_iff_ne_zero.mpr hx0))
  rw [hPbot]
  exact bot_mem_minimalPrimes_bot_of_field K

#print axioms hunmixed_bot_of_field

/-- `hminAvoid` does not follow from unmixedness (unconditional
refutation with witness): over a field at `J = ⊥`, unmixedness holds
(`hunmixed_bot_of_field`) but the fixed element `x = 0` lies in the
minimal prime `⊥`. This formalizes the `FinalDischargeHub` §9 verdict —
unmixedness yields only span-level avoidance, never fixed-element
avoidance — so `hmin` stays an independent hypothesis in every
`SuccClosureRungs`/`Hge2StepData` master.
-/
theorem hminAvoid_not_of_hunmixed (K : Type*) [Field K] :
    ¬ ∀ x : K, (∀ P ∈ associatedPrimes K (K ⧸ (⊥ : Ideal K)),
        P ∈ (⊥ : Ideal K).minimalPrimes) →
      (∀ Q ∈ (⊥ : Ideal K).minimalPrimes, x ∉ Q) := by
  intro h
  have hU := hunmixed_bot_of_field K
  have h0 := h 0 hU
  have hmem := bot_mem_minimalPrimes_bot_of_field K
  exact h0 ⊥ hmem (zero_mem (⊥ : Ideal K))

#print axioms hminAvoid_not_of_hunmixed

end MinAvoidRungs
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
