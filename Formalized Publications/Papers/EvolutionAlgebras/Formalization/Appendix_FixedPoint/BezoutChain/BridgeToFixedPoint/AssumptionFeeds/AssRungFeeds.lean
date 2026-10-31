/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoidRungs
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.SuccClosureRungs
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoid.MinSubsetAss
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.Rung.RungDiagonal
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.Rung.RungDiagonalGeneric
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.Rung.RungRegular
import Appendix_FixedPoint.BezoutChain.Geometry.K2UnmixednessEndgame
import Appendix_FixedPoint.BezoutChain.Geometry.UnmixednessAtLengthTwo
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.DimensionToMultiplicity
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.PrimeAvoidance
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.RegularityBridge
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# `hass` / rung-1 / `hdimEq` feeds for `MinSubsetAss` §4
Task: close the `hass_all` / `rung1Avoid` / `hdimEq_all` feeds for the
`MinSubsetAss` §4 masters — assAvoidance per
rung/prime, rung-1 discharge, and the `hdimEq` crux input in exact
consumption shape. `minSubAss` is closed (`MinSubsetAss.minSubAss_all`,
reused everywhere, never reproved); crux-family inputs are taken as
explicit SPEC hypotheses.

## Verdict (feeds scoped, rung-1 dichotomy narrowed to `[hdich]`)

* §1 (unconditional reductions + iff): existence-form suitable avoiders
  from Ass non-containment alone — the `Min` leg of `MinAvoidRungs`
  `exists_avoider_regular_of_not_le` discharged by the now-closed
  `minSubAss` (`exists_avoider_regular_of_ass_only`,
  `exists_minAvoider_of_ass_only`, bridge-data forms). Fixed-element
  `hass_all` is iff the rung steps (`hass_all_iff_steps`, the ∀-closed
  form of the verdict: no independent route below the steps);
  `hmin_all` from `[hsteps]` feeds in step shape.
* §2 (rung-1 discharge): `X i ∣ X j ↔ i = j` (`x_dvd_x_iff`,
  unconditional via `degreeOf_mul_eq`); hence the `RungRegular`
  dichotomy inputs `hprime0` (`MvPolynomial.X_prime`) and `hndvd1`
  close unconditionally — the dichotomy route narrows to `[hdich]`
  alone (`rung1step_of_hdich`, `rung1Avoid_of_hdich`,
  conditional-exact). shape rung-1 step and shape rung-1
  avoidance are inter-derivable (unconditional both directions +
  iff), and both follow from `[hdiag, hgen]`
  (conditional-exact on `[hdiag, hgen]`).
* §3 (unconditional defs/iffs + conditional-exact adapters): per-rung
  / per-prime `hdimEq` minimal forms (`HdimEqRung`, `HdimEqPrime`,
  `rfl`-decomposition iffs mirroring `MinSubsetAss` §1) and the SPEC
  shim — `HdimEqAllSpec` / `HkerMinAllSpec` / `HwitMinAllSpec` /
  `HdimEqUnivAllSpec` (∀-closed stage forms) with adapters into the
  exact `hdimEq` binder from `[hkerMin]` (via
  `DimensionToMultiplicity.hdimEqMin_of_hkerMin`), `[hwitMin]`, and the
  universal `BabyABPair.HdimEqAtAss` (via `hdimEqMin_of_hdimEq`).
* §4 (conditional-exact end-to-ends): full `hsucc` from
  `[hdiag, hgen, hdimEq, hass]` (generic route), from
  `[hdich, hdimEq, hass]` (dichotomy route), the fixed-family
  route fired from the step-route rung-1 input (routes
  interchangeable on rung-1), and per-rung `Min = Ass` from
  `[steps below j, hdimEq_j]` (feeds, discharging
  `hsucc_prefix`).

## Residual register (verbatim)

closed this lane: [existence-form suitable avoiders from Ass-only
input (Min leg via closed `minSubAss`)]; [`hass_all ⟺ steps`
∀-closed verdict packaging + `hmin` from `[hsteps]`]; [`X`-primality
and `X`-non-divisibility at rung 1 (`hprime0`, `hndvd1`)];
[rung-1 step ⟺ rung-1 avoidance]; [per-rung/per-prime `hdimEq`
minimal forms + SPEC shim + crux-family adapters]. Open (exact):
[fixed-element `hass_all` — is the steps per rung (verdict, not
work)]; [rung-1: `[hdiag, hgen]` (generic families) or `[hdich]` (the
nondegeneracy disjunct — exact remainder, needs `c`-data)]; [the
`HdimEq` crux (SPEC-scoped, adapters from `hkerMin`/`hwitMin`/univ)].

## Import DAG

New leaf module (no importers): `BridgeToFixedPoint/MinAvoidRungs` (`§1` selection,
`§2` iffs, shapes), `BridgeToFixedPoint/SuccClosureRungs`
(`step_span_of_step_oflist`, `step_rung1_of_avoid`,
`hsucc_prefixSlice_of_steps`), `BridgeToFixedPoint/MinSubsetAss` (`§2`
`minSubAss`, `§4` masters), `BridgeToFixedPoint/RungDiagonal` (`IsDiagonal`),
`BridgeToFixedPoint/RungDiagonalGeneric` (`hreg_rung1_of_generic`),
`BridgeToFixedPoint/RungRegular` (`hreg_rung1_of_dichotomy`),
`Geometry/K2UnmixednessEndgame` (universal `HdimEqAtAss`),
`Geometry/UnmixednessAtLengthTwo` (minimal crux forms),
`Regularity/DimensionToMultiplicity` (`§6` supply chain),
`Regularity/PrimeAvoidance` (selection engine),
`Regularity/RegularityBridge` (`SuccessiveSMulRegular`), narrow Mathlib.
No cycle risk.

## References

Project (`Formalization/Appendix_FixedPoint/BezoutChain/`):

* `BridgeToFixedPoint/MinAvoid/MinSubsetAss.lean` (`minSubAss` closes, reused);
  shape `hsub` (discharged);
  (the §4 feed targets).
* `BridgeToFixedPoint/MinAvoidRungs.lean` (existence-form suitable avoiders,
  narrowed here to Ass-only); (regularity ⟺ Ass-avoidance);
  (step ⟺ Ass-avoidance); (R3 register).
* `BridgeToFixedPoint/SuccClosureRungs.lean` (`§3` reductions, reused);
  (masters behind the `§4` targets).
* `BridgeToFixedPoint/Rung/RungRegular.lean` (`hreg_rung1_of_dichotomy`,
  narrowed here to `[hdich]`).
* `BridgeToFixedPoint/Rung/RungDiagonalGeneric.lean` (`hreg_rung1_of_generic`).
* `Geometry/UnmixednessAtLengthTwo.lean` (`HdimEqMinAtAss`, SPEC body);
  (`HkerMinAtAss`/`HwitMinAtAss` SPEC inputs).
* `Geometry/K2UnmixednessEndgame.lean` (universal `HdimEqAtAss` SPEC input).
* `Regularity/Multiplicity/DimensionToMultiplicity.lean` (`hdimEqMin` from
  `[hwit]`/`[hker]`).

Mathlib v4.34.0 (all read-only):

* `MvPolynomial.X_prime` (`Algebra/MvPolynomial/Division.lean`).
* `MvPolynomial.X_ne_zero` (`Algebra/MvPolynomial/Basic.lean`).
* `MvPolynomial.degreeOf_X_self`, `MvPolynomial.degreeOf_X_of_ne`
  (`Algebra/MvPolynomial/Degrees.lean`).
* `MvPolynomial.degreeOf_mul_eq`
  (`Algebra/MvPolynomial/NoZeroDivisors.lean`).
* `associatedPrimes`
  (`RingTheory/Ideal/AssociatedPrime/Basic.lean`).
* `Ideal.minimalPrimes` (`RingTheory/Ideal/MinimalPrime/Basic.lean`).
* `IsSMulRegular` (`RingTheory/Regular/IsSMulRegular.lean`).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace AssRungFeeds

/-! ## §1. Existence-form Ass-avoidance with `Min ⊆ Ass` discharged -/

/-- Existence-form suitable avoider from Ass non-containment alone
(unconditional reduction): the `Min` leg of
`MinAvoidRungs.exists_avoider_regular_of_not_le` is discharged by the
now-closed `MinSubsetAss.minSubAss_of_noetherian` (every minimal prime
over `J` is associated, so Ass non-containment restricts to `Min`).
The selected `y ∈ I` avoids every minimal prime over `J` and is
regular mod `J` — hence serves as a rung element.
-/
theorem exists_avoider_regular_of_ass_only {R : Type*} [CommRing R]
    [IsNoetherianRing R] (J I : Ideal R)
    (hass : ∀ P ∈ associatedPrimes R (R ⧸ J), ¬ I ≤ P) :
    ∃ y ∈ I, (∀ Q ∈ J.minimalPrimes, y ∉ Q) ∧
      IsSMulRegular (R ⧸ J) y :=
  MinAvoidRungs.exists_avoider_regular_of_not_le J I
    (fun Q hQ => hass Q (MinSubsetAss.minSubAss_of_noetherian J Q hQ)) hass

#print axioms exists_avoider_regular_of_ass_only

/-- Existence-form minimal avoider from Ass non-containment alone
(unconditional reduction): prime-avoidance selection over `Ass`
(`PrimeAvoidance.exists_mem_notMem_associatedPrimes`) lies outside every
minimal prime via the closed `minSubAss`. The pure-avoidance half of
the suitable-avoider conclusion (no regularity claim).
-/
theorem exists_minAvoider_of_ass_only {R : Type*} [CommRing R]
    [IsNoetherianRing R] (J I : Ideal R)
    (hass : ∀ P ∈ associatedPrimes R (R ⧸ J), ¬ I ≤ P) :
    ∃ y ∈ I, ∀ Q ∈ J.minimalPrimes, y ∉ Q := by
  obtain ⟨y, hyI, hy⟩ :=
    PrimeAvoidance.exists_mem_notMem_associatedPrimes I hass
  exact ⟨y, hyI,
    fun Q hQ => hy Q (MinSubsetAss.minSubAss_of_noetherian J Q hQ)⟩

#print axioms exists_minAvoider_of_ass_only

/-- Per-rung existence-form suitable-avoider predicate: some `y ∈ I`
avoids every minimal prime of the stage-`j` ideal and is regular mod
the stage ideal — i.e. `y` can serve as a rung element. The
existence-form per-rung address of the `MinAvoidRungs` §1 question.
-/
def ExistsSuitableRung (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1))
    (I : Ideal (MvPolynomial (Fin (statementIndex n + 2)) K)) : Prop :=
  ∃ y ∈ I, (∀ Q ∈ (MinAvoidRungs.stageIdeal n K c hn j).minimalPrimes,
    y ∉ Q) ∧ IsSMulRegular
    (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
      MinAvoidRungs.stageIdeal n K c hn j) y

#print axioms ExistsSuitableRung

/-- Per-rung suitable avoider from Ass non-containment alone
(unconditional reduction): the bridge-data form of
`exists_avoider_regular_of_ass_only` at the stage-`j` ideal.
-/
theorem existsSuitableRung_of_ass_only (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1))
    (I : Ideal (MvPolynomial (Fin (statementIndex n + 2)) K))
    (hass : ∀ P ∈ associatedPrimes
        (MvPolynomial (Fin (statementIndex n + 2)) K)
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          MinAvoidRungs.stageIdeal n K c hn j),
        ¬ I ≤ P) :
    ExistsSuitableRung n K c hn j I :=
  exists_avoider_regular_of_ass_only _ I hass

#print axioms existsSuitableRung_of_ass_only

/-- Per-rung minimal avoider from Ass non-containment alone
(unconditional reduction): the bridge-data form of
`exists_minAvoider_of_ass_only` at the stage-`j` ideal.
-/
theorem stage_minAvoider_of_ass_only (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1))
    (I : Ideal (MvPolynomial (Fin (statementIndex n + 2)) K))
    (hass : ∀ P ∈ associatedPrimes
        (MvPolynomial (Fin (statementIndex n + 2)) K)
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          MinAvoidRungs.stageIdeal n K c hn j),
        ¬ I ≤ P) :
    ∃ y ∈ I, ∀ Q ∈
      (MinAvoidRungs.stageIdeal n K c hn j).minimalPrimes, y ∉ Q :=
  exists_minAvoider_of_ass_only _ I hass

#print axioms stage_minAvoider_of_ass_only

/-- Fixed-element `hass_all` iff the rung steps (unconditional): the
∀-closed form of the verdict — per rung, Ass-avoidance is the step
(`MinAvoidRungs.step_span_iff_assAvoidRung`), so the
`hass` binder is exactly the ∀-closed step binder. No independent
route below the steps themselves.
-/
theorem hass_all_iff_steps (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n) :
    (∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      MinAvoidRungs.AssAvoidRung n K c hn j) ↔
    (∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (MinAvoidRungs.stageIdeal n K c hn j •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
        ((bridgeSystem n K c hn) j)) := by
  constructor
  · intro h j hj
    exact (MinAvoidRungs.step_span_iff_assAvoidRung n K c hn j).mpr (h j hj)
  · intro h j hj
    exact (MinAvoidRungs.step_span_iff_assAvoidRung n K c hn j).mp (h j hj)

#print axioms hass_all_iff_steps

/-- The `MinSubsetAss` `hmin` binder from `[steps]` (no `hass`
hypothesis): fixed-element Ass-avoidance discharged per rung by the
step itself, then. Feeds the master in step shape.

Conditional on exactly `[hsteps]`. -/
theorem hmin_all_of_steps (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (hsteps : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (MinAvoidRungs.stageIdeal n K c hn j •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
        ((bridgeSystem n K c hn) j)) :
    ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      MinAvoidRungs.MinAvoidRung n K c hn j :=
  MinSubsetAss.hmin_all_of_assAvoid_all n K c hn (fun j hj =>
    (MinAvoidRungs.step_span_iff_assAvoidRung n K c hn j).mp (hsteps j hj))

#print axioms hmin_all_of_steps

/-! ## §2. Rung-1 discharge: `X`-divisibility closes `hprime0`/`hndvd1` -/

/-- `X i ∣ X j ↔ i = j` over a field (unconditional): forward by
`degreeOf` — `degreeOf i (X i * f) = 1 + degreeOf i f ≥ 1`
(`MvPolynomial.degreeOf_mul_eq` at nonzero factors) while
`degreeOf i (X j) = 0` for `i ≠ j`
(`MvPolynomial.degreeOf_X_of_ne`). Backward is `dvd_rfl`.
-/
theorem x_dvd_x_iff {σ : Type*} {K : Type*} [Field K] (i j : σ) :
    (MvPolynomial.X i : MvPolynomial σ K) ∣ MvPolynomial.X j ↔
      i = j := by
  constructor
  · rintro ⟨f, hf⟩
    by_contra hne
    have hXi : (MvPolynomial.X i : MvPolynomial σ K) ≠ 0 :=
      MvPolynomial.X_ne_zero i
    have hXj : (MvPolynomial.X j : MvPolynomial σ K) ≠ 0 :=
      MvPolynomial.X_ne_zero j
    have hf0 : f ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at hf
      exact hXj hf
    have hdeg := congrArg (MvPolynomial.degreeOf i) hf
    rw [MvPolynomial.degreeOf_mul_eq hXi hf0,
      MvPolynomial.degreeOf_X_self,
      MvPolynomial.degreeOf_X_of_ne hne] at hdeg
    omega
  · rintro rfl
    exact dvd_rfl

#print axioms x_dvd_x_iff

/-- Rung-1 primality input closed (unconditional): `Prime (X 0)` is
`MvPolynomial.X_prime` (in-tree precedent: `R1RegularSection`,
`DiagonalQuadBridge`).
-/
theorem rung1prime0 (n : ℕ) (K : Type*) [Field K] :
    Prime (MvPolynomial.X
      (⟨0, Nat.zero_lt_succ (statementIndex n)⟩ :
        Fin (statementIndex n + 1)) :
      MvPolynomial (Fin (statementIndex n + 1)) K) :=
  MvPolynomial.X_prime

#print axioms rung1prime0

/-- Rung-1 non-divisibility input closed (unconditional): at
`j.val = 1`, `j ≠ ⟨0, _⟩`, so `X 0 ∤ X j` by `x_dvd_x_iff`.
-/
theorem rung1nondvd1 (n : ℕ) (K : Type*) [Field K]
    (j : Fin (statementIndex n + 1)) (hj : j.val = 1) :
    ¬ (MvPolynomial.X
      (⟨0, Nat.zero_lt_succ (statementIndex n)⟩ :
        Fin (statementIndex n + 1)) :
      MvPolynomial (Fin (statementIndex n + 1)) K) ∣
      MvPolynomial.X j := by
  intro hdvd
  have heq := (x_dvd_x_iff _ _).mp hdvd
  have h1 := congrArg Fin.val heq
  rw [show (⟨0, Nat.zero_lt_succ (statementIndex n)⟩ :
    Fin (statementIndex n + 1)).val = 0 from rfl, hj] at h1
  exact zero_ne_one h1

#print axioms rung1nondvd1

/-- shape rung-1 avoidance from shape rung-1 step
(unconditional reduction): regularity is Ass-avoidance
(`MinAvoidRungs.isSMulRegular_iff_forall_notMem_ass`) at the rung-1
`• ⊤` quotient.
-/
theorem rung1Avoid_of_rung1step (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (hrung1 : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (Ideal.span
            (Set.image (bridgeSystem n K c hn)
              {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
        ((bridgeSystem n K c hn) k)) :
    ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      ∀ P ∈ associatedPrimes
        (MvPolynomial (Fin (statementIndex n + 2)) K)
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (Ideal.span
            (Set.image (bridgeSystem n K c hn)
              {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K)))),
        (bridgeSystem n K c hn) k ∉ P :=
  fun k hk =>
    (MinAvoidRungs.isSMulRegular_iff_forall_notMem_ass _ _).mp (hrung1 k hk)

#print axioms rung1Avoid_of_rung1step

/-- shape rung-1 step from shape rung-1 avoidance
(unconditional reduction): `SuccClosureRungs.step_rung1_of_avoid` at each
rung-1 index.
-/
theorem rung1step_of_rung1Avoid (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (hrung1 : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      ∀ P ∈ associatedPrimes
        (MvPolynomial (Fin (statementIndex n + 2)) K)
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (Ideal.span
            (Set.image (bridgeSystem n K c hn)
              {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K)))),
        (bridgeSystem n K c hn) k ∉ P) :
    ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (Ideal.span
            (Set.image (bridgeSystem n K c hn)
              {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
        ((bridgeSystem n K c hn) k) :=
  fun k hk => SuccClosureRungs.step_rung1_of_avoid n K c hn k (hrung1 k hk)

#print axioms rung1step_of_rung1Avoid

/-- Rung-1 step ⟺ rung-1 avoidance (unconditional): the and
rung-1 binders are inter-derivable — the two `MinSubsetAss` §4
routes are interchangeable on rung-1.
-/
theorem rung1step_iff_rung1Avoid (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n) :
    (∀ k : Fin (statementIndex n + 1), k.val = 1 →
      IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (Ideal.span
            (Set.image (bridgeSystem n K c hn)
              {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
        ((bridgeSystem n K c hn) k)) ↔
    (∀ k : Fin (statementIndex n + 1), k.val = 1 →
      ∀ P ∈ associatedPrimes
        (MvPolynomial (Fin (statementIndex n + 2)) K)
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (Ideal.span
            (Set.image (bridgeSystem n K c hn)
              {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K)))),
        (bridgeSystem n K c hn) k ∉ P) :=
  ⟨rung1Avoid_of_rung1step n K c hn, rung1step_of_rung1Avoid n K c hn⟩

#print axioms rung1step_iff_rung1Avoid

/-- shape rung-1 step from diagonality + genericity
(conditional-exact): `RungDiagonalGeneric.hreg_rung1_of_generic`
(nondegeneracy derived) transported from the `ofList` quotient to the
span-image quotient (`SuccClosureRungs.step_span_of_step_oflist`).

Conditional on exactly `[hdiag, hgen]`. -/
theorem rung1step_of_generic (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (hdiag : RungDiagonal.IsDiagonal K c)
    (hgen : RungDiagonalGeneric.CoeffGenericBridge n K c hn) :
    ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (Ideal.span
            (Set.image (bridgeSystem n K c hn)
              {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
        ((bridgeSystem n K c hn) k) := by
  intro k hk
  exact SuccClosureRungs.step_span_of_step_oflist n K c hn k
    (RungDiagonalGeneric.hreg_rung1_of_generic K n hn c k hk hdiag hgen)

#print axioms rung1step_of_generic

/-- shape rung-1 avoidance from diagonality + genericity
(conditional-exact): `rung1step_of_generic` through the §2
step-to-avoidance reduction.

Conditional on exactly `[hdiag, hgen]`. -/
theorem rung1Avoid_of_generic (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (hdiag : RungDiagonal.IsDiagonal K c)
    (hgen : RungDiagonalGeneric.CoeffGenericBridge n K c hn) :
    ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      ∀ P ∈ associatedPrimes
        (MvPolynomial (Fin (statementIndex n + 2)) K)
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (Ideal.span
            (Set.image (bridgeSystem n K c hn)
              {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K)))),
        (bridgeSystem n K c hn) k ∉ P :=
  rung1Avoid_of_rung1step n K c hn
    (rung1step_of_generic n K c hn hdiag hgen)

#print axioms rung1Avoid_of_generic

/-- shape rung-1 step from the dichotomy disjunct alone
(conditional-exact): `RungRegular.hreg_rung1_of_dichotomy` with
`hprime0`/`hndvd1` discharged by `rung1prime0`/`rung1nondvd1`,
transported to the span-image quotient. The exact remainder is
`[hdich]` — the t2a/t2b nondegeneracy disjunct, which needs `c`-data
and cannot close generally.

Conditional on exactly `[hdich]`. -/
theorem rung1step_of_hdich (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (hdich : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      (¬ (MvPolynomial.X
            (⟨0, Nat.zero_lt_succ (statementIndex n)⟩ :
              Fin (statementIndex n + 1)) :
            MvPolynomial (Fin (statementIndex n + 1)) K) ∣
            bridgeForms n K c hn
              ⟨0, Nat.zero_lt_succ (statementIndex n)⟩) ∨
        (∃ L0 : MvPolynomial (Fin (statementIndex n + 1)) K,
          bridgeForms n K c hn ⟨0, Nat.zero_lt_succ (statementIndex n)⟩ =
            MvPolynomial.X ⟨0, Nat.zero_lt_succ (statementIndex n)⟩ *
              L0 ∧
          MvPolynomial.X (⟨0, Nat.zero_lt_succ (statementIndex n)⟩ :
            Fin (statementIndex n + 1)) * bridgeForms n K c hn k -
            MvPolynomial.X k * bridgeForms n K c hn
              ⟨0, Nat.zero_lt_succ (statementIndex n)⟩ ≠ 0)) :
    ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (Ideal.span
            (Set.image (bridgeSystem n K c hn)
              {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
        ((bridgeSystem n K c hn) k) := by
  intro k hk
  exact SuccClosureRungs.step_span_of_step_oflist n K c hn k
    (RungRegular.hreg_rung1_of_dichotomy K n hn c k hk
      (rung1prime0 n K) (rung1nondvd1 n K k hk) (hdich k hk))

#print axioms rung1step_of_hdich

/-- shape rung-1 avoidance from the dichotomy disjunct alone
(conditional-exact): `rung1step_of_hdich` through the §2
step-to-avoidance reduction. Exact remainder `[hdich]`.

Conditional on exactly `[hdich]`. -/
theorem rung1Avoid_of_hdich (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (hdich : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      (¬ (MvPolynomial.X
            (⟨0, Nat.zero_lt_succ (statementIndex n)⟩ :
              Fin (statementIndex n + 1)) :
            MvPolynomial (Fin (statementIndex n + 1)) K) ∣
            bridgeForms n K c hn
              ⟨0, Nat.zero_lt_succ (statementIndex n)⟩) ∨
        (∃ L0 : MvPolynomial (Fin (statementIndex n + 1)) K,
          bridgeForms n K c hn ⟨0, Nat.zero_lt_succ (statementIndex n)⟩ =
            MvPolynomial.X ⟨0, Nat.zero_lt_succ (statementIndex n)⟩ *
              L0 ∧
          MvPolynomial.X (⟨0, Nat.zero_lt_succ (statementIndex n)⟩ :
            Fin (statementIndex n + 1)) * bridgeForms n K c hn k -
            MvPolynomial.X k * bridgeForms n K c hn
              ⟨0, Nat.zero_lt_succ (statementIndex n)⟩ ≠ 0)) :
    ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      ∀ P ∈ associatedPrimes
        (MvPolynomial (Fin (statementIndex n + 2)) K)
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (Ideal.span
            (Set.image (bridgeSystem n K c hn)
              {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K)))),
        (bridgeSystem n K c hn) k ∉ P :=
  rung1Avoid_of_rung1step n K c hn (rung1step_of_hdich n K c hn hdich)

#print axioms rung1Avoid_of_hdich

/-! ## §3. `hdimEq` minimal forms + SPEC shim with crux-family adapters -/

/-- Per-rung `HdimEq` predicate: `HdimEqMinAtAss` at the stage-`j`
ideal — one rung of the `hdimEq` binder.
-/
def HdimEqRung (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1)) : Prop :=
  UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex n + 2) K
    (MinAvoidRungs.stageIdeal n K c hn j)

#print axioms HdimEqRung

/-- Per-prime `HdimEq` obligation: the single-`(j, Q)` minimal form —
the `HdimEqMinAtAss` body at fixed associated prime `Q` (minimal
`d ≥ 2`, exact degree `d - 1`). The `_hdmin` equation fixes `d` as the
local maximal-ideal span-finrank.
-/
def HdimEqPrime (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1))
    (Q : Ideal (MvPolynomial (Fin (statementIndex n + 2)) K)) : Prop :=
  ∀ [Q.IsPrime], Q ∈ associatedPrimes _ (_ ⧸
      MinAvoidRungs.stageIdeal n K c hn j) →
    ∀ {d : ℕ}
      (_hdmin : d = (IsLocalRing.maximalIdeal
        (Localization.AtPrime Q)).spanFinrank),
    2 ≤ d →
      ∀ Qw : Polynomial ℚ, Qw.natDegree ≤ d - 1 →
        (fun n => ((SingleDropRegularity.singleDrop_grHilbert
          (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) n : ℕ) : ℚ))
          =ᶠ[Filter.atTop] NewtonDifferences.evalFun Qw →
        Qw.natDegree = d - 1

#print axioms HdimEqPrime

/-- Per-rung `HdimEq` is the conjunction of per-prime forms
(unconditional, by `rfl`): the minimal per-`(j, Q)` decomposition of
the `hdimEq` binder.
-/
theorem hdimEqRung_iff_forall_prime (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1)) :
    HdimEqRung n K c hn j ↔ ∀ Q, HdimEqPrime n K c hn j Q :=
  Iff.rfl

#print axioms hdimEqRung_iff_forall_prime

/-- The `hdimEq` binder is the conjunction of per-rung
forms (unconditional, by `rfl`).
-/
theorem hdimEq_all_iff_forall_rung (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n) :
    (∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex n + 2) K
        (Ideal.span
          (Set.image (bridgeSystem n K c hn) {k | k.val < j.val}))) ↔
    (∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      HdimEqRung n K c hn j) :=
  Iff.rfl

#print axioms hdimEq_all_iff_forall_rung

/-- SPEC: ∀-closed minimal-`HdimEq` over rungs `≥ 2` at stage ideals —
the named address of the `hdimEq` binder.

Specification (Prop address). -/
def HdimEqAllSpec (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n) : Prop :=
  ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
    UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex n + 2) K
      (MinAvoidRungs.stageIdeal n K c hn j)

/-- SPEC: ∀-closed minimal-`Hker` over rungs `≥ 2` at stage ideals —
the kernel-form crux input feeding the binder.

Specification (Prop address). -/
def HkerMinAllSpec (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n) : Prop :=
  ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
    UnmixednessAtLengthTwo.HkerMinAtAss (statementIndex n + 2) K
      (MinAvoidRungs.stageIdeal n K c hn j)

/-- SPEC: ∀-closed minimal-`Hwit` over rungs `≥ 2` at stage ideals —
the witness-form crux input feeding the binder.

Specification (Prop address). -/
def HwitMinAllSpec (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n) : Prop :=
  ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
    UnmixednessAtLengthTwo.HwitMinAtAss (statementIndex n + 2) K
      (MinAvoidRungs.stageIdeal n K c hn j)

/-- SPEC: ∀-closed universal-`HdimEq` over rungs `≥ 2` at stage ideals —
the universal-form crux input feeding the binder.

Specification (Prop address). -/
def HdimEqUnivAllSpec (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n) : Prop :=
  ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
    BabyABPair.HdimEqAtAss (statementIndex n + 2) K
      (MinAvoidRungs.stageIdeal n K c hn j)

#print axioms HdimEqAllSpec
#print axioms HkerMinAllSpec
#print axioms HwitMinAllSpec
#print axioms HdimEqUnivAllSpec

/-- The exact `hdimEq` binder from its SPEC address
(unconditional): `HdimEqAllSpec` is the binder (the stage-ideal
abbrev is reducible, so this is definitional).
-/
theorem hdimEq_all_of_spec (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (hspec : HdimEqAllSpec n K c hn) :
    ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex n + 2) K
        (Ideal.span
          (Set.image (bridgeSystem n K c hn) {k | k.val < j.val})) :=
  fun j hj => hspec j hj

#print axioms hdimEq_all_of_spec

/-- The exact `hdimEq` binder from `[hkerMin]`
(conditional-exact): per rung via
`DimensionToMultiplicity.hdimEqMin_of_hkerMin` (the `§6` supply chain).

Conditional on exactly `[hker]`. -/
theorem hdimEq_all_of_hkerMin_all (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (hker : HkerMinAllSpec n K c hn) :
    ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex n + 2) K
        (Ideal.span
          (Set.image (bridgeSystem n K c hn) {k | k.val < j.val})) := by
  intro j hj
  exact DimensionToMultiplicity.hdimEqMin_of_hkerMin _ _ _ (hker j hj)

#print axioms hdimEq_all_of_hkerMin_all

/-- The exact `hdimEq` binder from `[hwitMin]`
(conditional-exact): per rung via
`DimensionToMultiplicity.hdimEqMin_of_hwitMin` (the `§6` supply chain).

Conditional on exactly `[hwit]`. -/
theorem hdimEq_all_of_hwitMin_all (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (hwit : HwitMinAllSpec n K c hn) :
    ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex n + 2) K
        (Ideal.span
          (Set.image (bridgeSystem n K c hn) {k | k.val < j.val})) := by
  intro j hj
  exact DimensionToMultiplicity.hdimEqMin_of_hwitMin _ _ _ (hwit j hj)

#print axioms hdimEq_all_of_hwitMin_all

/-- The exact `hdimEq` binder from universal `HdimEq`
(conditional-exact): per rung via
`UnmixednessAtLengthTwo.hdimEqMin_of_hdimEq` (the universal form specializes to
the minimal form by dropping the minimality argument).

Conditional on exactly `[huniv]`. -/
theorem hdimEq_all_of_univ_all (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (huniv : HdimEqUnivAllSpec n K c hn) :
    ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex n + 2) K
        (Ideal.span
          (Set.image (bridgeSystem n K c hn) {k | k.val < j.val})) := by
  intro j hj
  exact UnmixednessAtLengthTwo.hdimEqMin_of_hdimEq _ _ _ (huniv j hj)

#print axioms hdimEq_all_of_univ_all

/-! ## §4. End-to-end feeds into the `MinSubsetAss` §4 masters -/

/-- Full `hsucc` at bridge data from `[diagonal, genericity, ∀-HdimEq,
∀-assAvoid]` (NO `hmin`, NO `hsub`): the `MinSubsetAss` master
with rung 1 discharged by `rung1step_of_generic`.

Conditional on exactly `[hdiag, hgen, hdimEq, hass]`. -/
theorem hsucc_of_generic_of_hdimEq_of_assAvoid (K : Type*) [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (hdiag : RungDiagonal.IsDiagonal K c)
    (hgen : RungDiagonalGeneric.CoeffGenericBridge n K c hn)
    (hdimEq : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex n + 2) K
        (Ideal.span
          (Set.image (bridgeSystem n K c hn) {k | k.val < j.val})))
    (hass : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      MinAvoidRungs.AssAvoidRung n K c hn j) :
    RegularityBridge.SuccessiveSMulRegular (bridgeSystem n K c hn) :=
  MinSubsetAss.hsucc_bridgeSystem_of_rung1step_of_hdimEqMin_of_assAvoid
    K n hn c (rung1step_of_generic n K c hn hdiag hgen) hdimEq hass

#print axioms hsucc_of_generic_of_hdimEq_of_assAvoid

/-- Full `hsucc` at bridge data from `[dichotomy, ∀-HdimEq,
∀-assAvoid]` (NO `hmin`, NO `hsub`, no diagonality/genericity): the
`MinSubsetAss` master with rung 1 discharged by
`rung1step_of_hdich`. The rung-1 remainder is exactly `[hdich]`.

Conditional on exactly `[hdich, hdimEq, hass]`. -/
theorem hsucc_of_hdich_of_hdimEq_of_assAvoid (K : Type*) [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (hdich : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      (¬ (MvPolynomial.X
            (⟨0, Nat.zero_lt_succ (statementIndex n)⟩ :
              Fin (statementIndex n + 1)) :
            MvPolynomial (Fin (statementIndex n + 1)) K) ∣
            bridgeForms n K c hn
              ⟨0, Nat.zero_lt_succ (statementIndex n)⟩) ∨
        (∃ L0 : MvPolynomial (Fin (statementIndex n + 1)) K,
          bridgeForms n K c hn ⟨0, Nat.zero_lt_succ (statementIndex n)⟩ =
            MvPolynomial.X ⟨0, Nat.zero_lt_succ (statementIndex n)⟩ *
              L0 ∧
          MvPolynomial.X (⟨0, Nat.zero_lt_succ (statementIndex n)⟩ :
            Fin (statementIndex n + 1)) * bridgeForms n K c hn k -
            MvPolynomial.X k * bridgeForms n K c hn
              ⟨0, Nat.zero_lt_succ (statementIndex n)⟩ ≠ 0))
    (hdimEq : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex n + 2) K
        (Ideal.span
          (Set.image (bridgeSystem n K c hn) {k | k.val < j.val})))
    (hass : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      MinAvoidRungs.AssAvoidRung n K c hn j) :
    RegularityBridge.SuccessiveSMulRegular (bridgeSystem n K c hn) :=
  MinSubsetAss.hsucc_bridgeSystem_of_rung1step_of_hdimEqMin_of_assAvoid
    K n hn c (rung1step_of_hdich n K c hn hdich) hdimEq hass

#print axioms hsucc_of_hdich_of_hdimEq_of_assAvoid

/-- Full `hsucc` at bridge data via the fixed-family route
fired from a rung-1 step (no `hmin`, no `hsub`): the master
with `rung1Avoid` discharged by `rung1Avoid_of_rung1step` — the two
`MinSubsetAss` §4 routes coincide on rung-1 input.

Conditional on exactly `[hrung1, hdimEq, hass]`. -/
theorem hsucc_rung1Avoid_route_of_rung1step (K : Type*) [Field K]
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
  MinSubsetAss.hsucc_bridgeSystem_of_rung1Avoid_of_hdimEqMin_of_assAvoid
    K n hn c (rung1Avoid_of_rung1step n K c hn hrung1) hdimEq hass

#print axioms hsucc_rung1Avoid_route_of_rung1step

/-- Per-rung `Min = Ass` from `[steps below j, HdimEq]` (no
`hsucc_prefix` hypothesis): the `MinSubsetAss` master with
prefix-`hsucc` built from earlier-rung steps
(`SuccClosureRungs.hsucc_prefixSlice_of_steps`).

Conditional on exactly `[hsteps, hdimEq]`. -/
theorem minEqAssRung_of_steps_of_hdimEq (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1)) (hj : 2 ≤ j.val)
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
      (MinAvoidRungs.stageIdeal n K c hn j)) :
    (MinAvoidRungs.stageIdeal n K c hn j).minimalPrimes =
      associatedPrimes (MvPolynomial (Fin (statementIndex n + 2)) K)
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          MinAvoidRungs.stageIdeal n K c hn j) :=
  MinSubsetAss.minEqAssRung_of_hsuccPrefix_of_hdimEq n K c hn j hj
    (SuccClosureRungs.hsucc_prefixSlice_of_steps n K c hn j hsteps) hdimEq

#print axioms minEqAssRung_of_steps_of_hdimEq

/-! ## §5. Residual register (doc only; see module docstring)

closed this lane: [existence-form suitable avoiders from Ass-only
input]; [`hass_all ⟺ steps` + `hmin` from `[hsteps]`];
[`X`-primality / `X`-non-divisibility at rung 1]; [rung-1 step ⟺
rung-1 avoidance]; [per-rung/per-prime `hdimEq` forms + SPEC shim +
adapters]. Open (exact): [`hass_all` — is the steps (verdict)];
[rung-1 `[hdiag, hgen]` or `[hdich]`]; [`HdimEq` crux (SPEC-scoped)].
No new remainder beyond the register.
-/

end AssRungFeeds
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
