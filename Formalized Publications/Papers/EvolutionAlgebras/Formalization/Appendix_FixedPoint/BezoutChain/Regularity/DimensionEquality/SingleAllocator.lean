/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.FixedPointFromBezout
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoidRungs
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.AssumptionFeeds.AssRungFeeds
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.Rung.UnmixednessRungTwo
import Appendix_FixedPoint.BezoutChain.Geometry.K2UnmixednessEndgame
import Appendix_FixedPoint.BezoutChain.Geometry.UnmixednessAtLengthTwo
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.DimEqAttackDimTwo
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.DimensionToMultiplicity
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedExactnessDischarge
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.HighDimGe3Attack
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.NewtonDifferences
import Appendix_FixedPoint.BezoutChain.Regularity.Rees.ReesClose
import Appendix_FixedPoint.BezoutChain.Regularity.Rees.ReesGe3Discharge
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.SingleDropRegularity
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.WitnessKernelDimTwo

/-!
# The single `hdimEq` allocator
Task: build the single `hdimEq` allocator — every `hdimEq`-family
input in the tree as a corollary of one master SPEC
`HdimEqMasterAlloc` (per `(family, Q, d)` with explicit gates),
the trivial dimensions closed once centrally, and every consumer
wired to the allocator with exact binder match. Pure infrastructure
+ wiring; the `d ≥ 2` crux is registered, never attacked.

## What this file proves

* (§1) The master: per-`(Q, d)` exact-degree piece `HdimEqPiece`,
  the named minimality gate `HdimEqMinGate` (`d = spanFinrank`),
  and the master SPEC `HdimEqMasterAlloc` (Ass-membership +
  minimality gate + regime gate `regGate`).
* (§2) Trivial dimensions closed unconditionally, once, centrally:
  the piece at `d = 0` / `d = 1` (pure degree-bound arithmetic —
  `deg ≤ d - 1` forces `deg = d - 1` since `d - 1 = 0`), the
  allocator slices at `d = 0` / `d = 1` / `d ≤ 1`, and the
  unconditional `ungated ⟺ d ≥ 2` collapse (the ungated allocator
  is the `d ≥ 2` allocator).
* (§3) Family corollaries (unconditional iffs): `HdimEqMinAtAss`,
  `HdimEqD2AtAss`, both `HdimEqMinGe3AtAss` twins (ReesClose
  direct, HighGe3 via the `rge3_bridge` supplier), `HdimEqAllSpec`,
  `HdimEqRung`, `HdimEqPrime`, `HdimEqD23AtAss`; plus the
  universal forms as conditional-exact one-directionals
  (`HdimEqAtAss`, `HdimEqUnivAllSpec` via `hdimEqMin_of_hdimEq`).
* (§4) The `d = 2` / `d ≥ 3` split (unconditional): the `d ≥ 2`
  allocator is the conjunction of the `d = 2` and `d ≥ 3`
  slices, hence `HdimEqMinAtAss` itself splits.
* (§5) Consumer wiring (exact binder match, conditional-exact):
  HS (`hass_all` `hdimEq` binder) and HD2 (`hsucc` `hdimEq`
  binder) from the per-stage allocator; GXQ (the `HdimEqD2AtAss`
  slice from the `d = 2` allocator slice, and the allocator
  `d = 2` slice ⟺ `HgrNonstabD2AtAss` remainder); J9
  (`HdimEqMinAtAss` and the rung-`∀` binder from the split
  allocator slices).
* (§6) Residual register (unconditional iff compositions, no
  attack): the `d ≥ 2` allocator ⟺ `HkerMinAtAss` ⟺
  `HnoHomRelHighMinAtAss` (the crux, three names); the `d = 2`
  slice ⟺ `HkerD2AtAss`; the `d ≥ 3` slice ⟺
  `HkerMinGe3AtAss`.
* (§7, doc-only) Remainder register + verdict.

## Status

unconditional: every `..._iff_...`, `..._split...`, `..._piece_d_...`,
`..._alloc_d_...`, `..._alloc_le_one`, `..._crux_iff_...`,
`..._d2_iff_hkerD2`, `..._ge3_iff_hkerGe3`.
conditional-exact on the named allocator input: every `..._of_alloc...`
wiring corollary. Conditional-exact on `[huniv]`: the two universal
one-directionals. Overall: infrastructure + wiring, partial by
design — the allocator makes `hdimEq` single, it does not close `d ≥ 2`.

## Residual register (verbatim)

closed this lane: [trivial `d = 0` / `d = 1` allocator slices +
`d ≤ 1` joint + ungated-collapse]; [every minimal-`hdimEq` family
member as an allocator corollary]; [`d = 2` / `d ≥ 3` allocator
split]; [HS + HD2 + GXQ + J9 consumption shapes as allocator
corollaries with exact binder match].
open (exact): [the `d ≥ 2` allocator = the crux — iff `HkerMinAtAss`
iff `HnoHomRelHighMinAtAss` (§6); not attacked here by design].

## Import DAG

New leaf module (no importers): `BridgeToFixedPoint/FixedPointFromBezout`
(`statementIndex`, `bridgeSystem`), `BridgeToFixedPoint/MinAvoidRungs`
(`stageIdeal`), `BridgeToFixedPoint/AssRungFeeds` (SPEC shim +
`hdimEq_all_of_spec`), `BridgeToFixedPoint/UnmixednessRungTwo` (`HdimEqD23AtAss`),
`Geometry/K2UnmixednessEndgame` (`HdimEqAtAss`), `Geometry/UnmixednessAtLengthTwo`
(`HdimEqMinAtAss`, `HkerMinAtAss`, `HwitMinAtAss`,
`hdimEqMin_of_hdimEq`), `Regularity/DimEqAttackDimTwo`
(`HgrNonstabD2AtAss` + slice iff), `Regularity/DimensionToMultiplicity`
(iff ring + `HnoHomRelHighMinAtAss` + §7 maps),
`Regularity/GradedExactnessDischarge` (`HdimEqD2AtAss` + grExact iff),
`Regularity/HighDimGe3Attack` (`HdimEqMinGe3AtAss`,
`HkerMinGe3AtAss`), `Regularity/NewtonDifferences` (`evalFun`),
`Regularity/ReesClose` (`HdimEqMinGe3AtAss` + D2-ring iff),
`Regularity/ReesGe3Discharge` (`rge3_bridge`,
`rge3_iff_hkerGe3`), `Regularity/SingleDropRegularity`
(`singleDrop_grHilbert`), `Regularity/WitnessKernelDimTwo`
(`HkerD2AtAss`), narrow Mathlib (`=ᶠ`, `associatedPrimes`).
No cycle risk (Regularity → Bridge precedent: `FinalJointAssemble`).

## References

* `Geometry/UnmixednessAtLengthTwo.lean` (`HdimEqMinAtAss`, SPEC body);
  (`hdimEqMin_of_hdimEq`).
* `Geometry/K2UnmixednessEndgame.lean` (`HdimEqAtAss`, universal form).
* `Regularity/Koszul/GradedExactnessDischarge.lean` (`HdimEqD2AtAss`);
  (slice of minimal); (slice ⟺ grExact).
* `Regularity/Rees/ReesClose.lean` (`HdimEqMinGe3AtAss`);
  (grExact ⟺ hker at D2).
* `Regularity/Multiplicity/HighDimGe3Attack.lean` (`HdimEqMinGe3AtAss` twin);
  (`HkerMinGe3AtAss`).
* `Regularity/Rees/ReesGe3Discharge.lean` (`rge3_bridge`);
  (`rge3_iff_hkerGe3`).
* `Regularity/Multiplicity/DimEqAttackDimTwo.lean` (`HgrNonstabD2AtAss`);
  (slice ⟺ nonstab).
* `Regularity/Multiplicity/DimensionToMultiplicity.lean` (`hdimEqMin_iff_hkerMin`);
  (`hwitMin_iff_hkerMin`); (`HnoHomRelHighMinAtAss`);
  (§7 maps).
* `BridgeToFixedPoint/AssumptionFeeds/AssRungFeeds.lean` (`HdimEqRung`);
  (`HdimEqPrime`); (`HdimEqAllSpec`);
  (`HdimEqUnivAllSpec`); (`hdimEq_all_of_spec`).
* `BridgeToFixedPoint/Rung/UnmixednessRungTwo.lean` (`HdimEqD23AtAss`).
* `BridgeToFixedPoint/AssumptionFeeds/AssReductionRungs.lean` (HS `hdimEq` binder).
* `BridgeToFixedPoint/AssumptionFeeds/RungOneDiagonalDischarge.lean` (HD2 `hdimEq` binder).
* `Regularity/Assembly/JointAssembly.lean`
  (`final_hdimEqMin_of_d2_ge3`); (J9 per-rung feed).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace SingleAllocator

/-! ## §1. The master: piece + gates + allocator -/

/-- Per-`(Q, d)` exact-degree piece: every degree-`≤ d - 1`
polynomial approximant of `H_gr` at `Q` has degree exactly `d - 1`.
This is the shared body of every `hdimEq`-family SPEC in the tree.
-/
def HdimEqPiece (m : ℕ) (K : Type*) [Field K]
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] (d : ℕ) : Prop :=
  ∀ Qw : Polynomial ℚ, Qw.natDegree ≤ d - 1 →
    (fun n => ((SingleDropRegularity.singleDrop_grHilbert
      (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) n : ℕ) : ℚ))
      =ᶠ[Filter.atTop] NewtonDifferences.evalFun Qw →
    Qw.natDegree = d - 1

#print axioms HdimEqPiece

/-- The minimality gate: `d` is pinned to the embedding dimension
(`spanFinrank` of the maximal ideal at `Q`). Every minimal-family
member carries this gate; the universal forms omit it.
-/
def HdimEqMinGate (m : ℕ) (K : Type*) [Field K]
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] (d : ℕ) : Prop :=
  d = (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank

#print axioms HdimEqMinGate

/-- The master allocator: per-`(Q, d)` exact-degree piece over
`Q ∈ Ass(R ⧸ J)` at minimal `d`, under an explicit regime gate
`regGate` on `d`. The two gates are: (i) the minimality gate
`HdimEqMinGate` (built in — every minimal-family member carries
it); (ii) the regime gate `regGate` (parameter — `d = 2` / `d ≥ 3`
split, trivial slices, ungated). Every `hdimEq`-family input in
the tree is a corollary of this one SPEC (§3); every consumer
reads through it (§5).

Specification (Prop address for the single allocator). -/
def HdimEqMasterAlloc (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) (regGate : ℕ → Prop) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    ∀ d, HdimEqMinGate m K Q d → regGate d → HdimEqPiece m K Q d

#print axioms HdimEqMasterAlloc

/-! ## §2. Trivial dimensions closed once, centrally -/

/-- The piece at `d = 0` (unconditional): `0 - 1 = 0`, so the
degree bound `deg ≤ 0` is the conclusion `deg = 0`. Pure
`natDegree` arithmetic — the Hilbert hypothesis is unused.
-/
theorem hdimEqMaster_piece_d_zero (m : ℕ) (K : Type*) [Field K]
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] :
    HdimEqPiece m K Q 0 := by
  unfold HdimEqPiece
  intro Qw hle _
  omega

#print axioms hdimEqMaster_piece_d_zero

/-- The piece at `d = 1` (unconditional): `1 - 1 = 0`, same
degenerate reading as `d = 0`.
-/
theorem hdimEqMaster_piece_d_one (m : ℕ) (K : Type*) [Field K]
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] :
    HdimEqPiece m K Q 1 := by
  unfold HdimEqPiece
  intro Qw hle _
  omega

#print axioms hdimEqMaster_piece_d_one

/-- The allocator slice at `d = 0` (unconditional): every minimal
instance is the closed piece above. Regime gate and family are
arbitrary — the slice holds with no hypotheses.
-/
theorem hdimEqMaster_alloc_d_zero (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HdimEqMasterAlloc m K J (fun d => d = 0) := by
  unfold HdimEqMasterAlloc
  intro Q _ _ d _ hd
  have hd0 : d = 0 := hd
  subst hd0
  exact hdimEqMaster_piece_d_zero m K Q

#print axioms hdimEqMaster_alloc_d_zero

/-- The allocator slice at `d = 1` (unconditional): same route via
the closed `d = 1` piece.
-/
theorem hdimEqMaster_alloc_d_one (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HdimEqMasterAlloc m K J (fun d => d = 1) := by
  unfold HdimEqMasterAlloc
  intro Q _ _ d _ hd
  have hd1 : d = 1 := hd
  subst hd1
  exact hdimEqMaster_piece_d_one m K Q

#print axioms hdimEqMaster_alloc_d_one

/-- The allocator slice at `d ≤ 1` (unconditional): the joint of
the two closed trivial slices.
-/
theorem hdimEqMaster_alloc_le_one (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HdimEqMasterAlloc m K J (fun d => d ≤ 1) := by
  unfold HdimEqMasterAlloc
  intro Q _ _ d _ hd
  have hd1 : d ≤ 1 := hd
  rcases (show d = 0 ∨ d = 1 by omega) with rfl | rfl
  · exact hdimEqMaster_piece_d_zero m K Q
  · exact hdimEqMaster_piece_d_one m K Q

#print axioms hdimEqMaster_alloc_le_one

/-- Ungated collapse (unconditional): the allocator with no regime
gate is the `d ≥ 2` allocator — the trivial dimensions contribute
nothing (they are closed above). From here on, every consumer may
read `regGate := fun d => 2 ≤ d` as the full allocator.
-/
theorem hdimEqMaster_ungated_iff_ge2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HdimEqMasterAlloc m K J (fun _ => True) ↔
      HdimEqMasterAlloc m K J (fun d => 2 ≤ d) := by
  unfold HdimEqMasterAlloc
  constructor
  · intro h Q _ hQ d a _
    exact h Q hQ d a trivial
  · intro h Q _ hQ d a _
    by_cases hd : 2 ≤ d
    · exact h Q hQ d a hd
    · have hle : d ≤ 1 := by omega
      exact hdimEqMaster_alloc_le_one m K J Q hQ d a hle

#print axioms hdimEqMaster_ungated_iff_ge2

/-! ## §3. Family corollaries: every member is an allocator slice -/

/-- `HdimEqMinAtAss` is the `d ≥ 2` allocator slice
(unconditional): same Ass-quantifier, same minimality gate, same
`2 ≤ d` regime, same piece body.
-/
theorem hdimEqMaster_min_iff (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    UnmixednessAtLengthTwo.HdimEqMinAtAss m K J ↔
      HdimEqMasterAlloc m K J (fun d => 2 ≤ d) := by
  unfold HdimEqMasterAlloc
  constructor
  · intro h Q _ hQ d hdmin hd2
    exact h Q hQ hdmin hd2
  · intro h
    unfold UnmixednessAtLengthTwo.HdimEqMinAtAss
    intro Q _ hQ d hdmin hd2 Qw hle hag
    exact h Q hQ d hdmin hd2 Qw hle hag

#print axioms hdimEqMaster_min_iff

/-- `HdimEqD2AtAss` is the `d = 2` allocator slice
(unconditional): the GX `d = 2` SPEC (pinned embdim, no `d`
binder) against the allocator's `d = 2` regime gate.
-/
theorem hdimEqMaster_d2_iff (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    GradedExactnessDischarge.HdimEqD2AtAss m K J ↔
      HdimEqMasterAlloc m K J (fun d => d = 2) := by
  unfold HdimEqMasterAlloc
  constructor
  · intro h Q _ hQ d a hb
    have hb2 : d = 2 := hb
    subst hb2
    exact h Q hQ a
  · intro h
    unfold GradedExactnessDischarge.HdimEqD2AtAss
    intro Q _ hQ hemb Qw hle hag
    exact h Q hQ 2 hemb rfl Qw hle hag

#print axioms hdimEqMaster_d2_iff

/-- Rees-9′ (`ReesClose.HdimEqMinGe3AtAss`) is the `d ≥ 3`
allocator slice (unconditional): same body as the minimal form
with the `3 ≤ d` regime gate.
-/
theorem hdimEqMaster_ge3_rees_iff (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    ReesClose.HdimEqMinGe3AtAss m K J ↔
      HdimEqMasterAlloc m K J (fun d => 3 ≤ d) := by
  unfold HdimEqMasterAlloc
  constructor
  · intro h Q _ hQ d hdmin hd3
    exact h Q hQ hdmin hd3
  · intro h
    unfold ReesClose.HdimEqMinGe3AtAss
    intro Q _ hQ d hdmin hd3 Qw hle hag
    exact h Q hQ d hdmin hd3 Qw hle hag

#print axioms hdimEqMaster_ge3_rees_iff

/-- The `HighGe3` twin is the `d ≥ 3` allocator slice
(unconditional): via the `rge3_bridge` supplier (never reproved)
plus the rees-9′ corollary above.
-/
theorem hdimEqMaster_ge3_high_iff (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HighDimGe3Attack.HdimEqMinGe3AtAss m K J ↔
      HdimEqMasterAlloc m K J (fun d => 3 ≤ d) :=
  (ReesGe3Discharge.rge3_bridge m K J).symm.trans
    (hdimEqMaster_ge3_rees_iff m K J)

#print axioms hdimEqMaster_ge3_high_iff

/-- `HdimEqAllSpec` is the per-stage `d ≥ 2` allocator
(unconditional): the HassRung SPEC address, pointwise the minimal
corollary at each stage ideal.
-/
theorem hdimEqMaster_allSpec_iff (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n) :
    AssRungFeeds.HdimEqAllSpec n K c hn ↔
      ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
        HdimEqMasterAlloc (statementIndex n + 2) K
          (MinAvoidRungs.stageIdeal n K c hn j) (fun d => 2 ≤ d) :=
  ⟨fun h j hj => (hdimEqMaster_min_iff _ _ _).mp (h j hj),
   fun h j hj => (hdimEqMaster_min_iff _ _ _).mpr (h j hj)⟩

#print axioms hdimEqMaster_allSpec_iff

/-- `HdimEqRung` is the per-stage `d ≥ 2` allocator slice
(unconditional): one rung of the SPEC address above.
-/
theorem hdimEqMaster_rung_iff (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1)) :
    AssRungFeeds.HdimEqRung n K c hn j ↔
      HdimEqMasterAlloc (statementIndex n + 2) K
        (MinAvoidRungs.stageIdeal n K c hn j) (fun d => 2 ≤ d) := by
  unfold AssRungFeeds.HdimEqRung
  exact hdimEqMaster_min_iff _ _ _

#print axioms hdimEqMaster_rung_iff

/-- `HdimEqPrime` is the per-`(j, Q)` allocator row
(unconditional): the single-prime body against the allocator's
per-`Q` row (Ass-membership + minimal pin + `2 ≤ d` + piece).
-/
theorem hdimEqMaster_prime_iff (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1))
    (Q : Ideal (MvPolynomial (Fin (statementIndex n + 2)) K)) :
    AssRungFeeds.HdimEqPrime n K c hn j Q ↔
      ∀ [Q.IsPrime],
        Q ∈ associatedPrimes _ (_ ⧸ MinAvoidRungs.stageIdeal n K c hn j) →
        ∀ d, HdimEqMinGate (statementIndex n + 2) K Q d →
          2 ≤ d → HdimEqPiece (statementIndex n + 2) K Q d := by
  constructor
  · intro h _ hQ d a b
    exact h hQ a b
  · intro h
    unfold AssRungFeeds.HdimEqPrime
    intro _ hQ d a b Qw hle hag
    exact h hQ d a b Qw hle hag

#print axioms hdimEqMaster_prime_iff

/-- `HdimEqD23AtAss` is the `d ∈ {2, 3}` allocator slice
(unconditional): the rung-2 narrowed remainder (verbatim minimal
binder shape, disjunctive regime gate).
-/
theorem hdimEqMaster_d23_iff (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin (statementIndex 2 + 2)) K)) :
    UnmixednessRungTwo.HdimEqD23AtAss K J ↔
      HdimEqMasterAlloc (statementIndex 2 + 2) K J
        (fun d => d = 2 ∨ d = 3) := by
  unfold HdimEqMasterAlloc
  constructor
  · intro h Q _ hQ d hdmin hd23
    exact h Q hQ hdmin hd23
  · intro h
    unfold UnmixednessRungTwo.HdimEqD23AtAss
    intro Q _ hQ d hdmin hd23 Qw hle hag
    exact h Q hQ d hdmin hd23 Qw hle hag

#print axioms hdimEqMaster_d23_iff

/-- The universal form feeds the allocator (conditional-exact on
`[huniv]`): `HdimEqAtAss` specializes to the minimal form
(`hdimEqMin_of_hdimEq` supplier), which is the `d ≥ 2` slice.

Conditional on exactly `[huniv]`. -/
theorem hdimEqMaster_univ_to_alloc (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (huniv : BabyABPair.HdimEqAtAss m K J) :
    HdimEqMasterAlloc m K J (fun d => 2 ≤ d) :=
  (hdimEqMaster_min_iff m K J).mp
    (UnmixednessAtLengthTwo.hdimEqMin_of_hdimEq m K J huniv)

#print axioms hdimEqMaster_univ_to_alloc

/-- The universal `∀`-closed form feeds the per-stage allocator
(conditional-exact on `[huniv]`): pointwise the corollary above.

Conditional on exactly `[huniv]`. -/
theorem hdimEqMaster_univAll_to_alloc (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (huniv : AssRungFeeds.HdimEqUnivAllSpec n K c hn) :
    ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      HdimEqMasterAlloc (statementIndex n + 2) K
        (MinAvoidRungs.stageIdeal n K c hn j) (fun d => 2 ≤ d) :=
  fun j hj => hdimEqMaster_univ_to_alloc _ _ _ (huniv j hj)

#print axioms hdimEqMaster_univAll_to_alloc

/-! ## §4. The `d = 2` / `d ≥ 3` split -/

/-- Allocator split (unconditional): the `d ≥ 2` allocator is the
conjunction of the `d = 2` slice and the `d ≥ 3` slice — every
`d ≥ 2` is `d = 2` or `d ≥ 3`. The joint-attack shape: D2 lanes
feed the first conjunct, Ge3 lanes the second.
-/
theorem hdimEqMaster_split_ge2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HdimEqMasterAlloc m K J (fun d => 2 ≤ d) ↔
      HdimEqMasterAlloc m K J (fun d => d = 2) ∧
        HdimEqMasterAlloc m K J (fun d => 3 ≤ d) := by
  unfold HdimEqMasterAlloc
  constructor
  · intro h
    constructor
    · intro Q _ hQ d a hb
      have h2 : d = 2 := hb
      have hge : 2 ≤ d := by omega
      exact h Q hQ d a hge
    · intro Q _ hQ d a hb
      have h3 : 3 ≤ d := hb
      have hge : 2 ≤ d := by omega
      exact h Q hQ d a hge
  · rintro ⟨h2, h3⟩ Q _ hQ d a hb
    have hge : 2 ≤ d := hb
    rcases (show d = 2 ∨ 3 ≤ d by omega) with rfl | hle3
    · exact h2 Q hQ _ a rfl
    · exact h3 Q hQ _ a hle3

#print axioms hdimEqMaster_split_ge2

/-- `HdimEqMinAtAss` splits over the allocator (unconditional):
the minimal form is the `d = 2` slice plus the `d ≥ 3` slice.
-/
theorem hdimEqMaster_min_split (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    UnmixednessAtLengthTwo.HdimEqMinAtAss m K J ↔
      HdimEqMasterAlloc m K J (fun d => d = 2) ∧
        HdimEqMasterAlloc m K J (fun d => 3 ≤ d) :=
  (hdimEqMaster_min_iff m K J).trans (hdimEqMaster_split_ge2 m K J)

#print axioms hdimEqMaster_min_split

/-! ## §5. Consumer wiring: exact binder match -/

/-- HS wiring (conditional-exact on `[halloc]`): the per-stage
`d ≥ 2` allocator proves the verbatim `hass_all` `hdimEq` binder
(`AssReductionRungs`, span-shape `∀ j ≥ 2`), via the SPEC address
(`hdimEq_all_of_spec` supplier).

Conditional on exactly `[halloc]`. -/
theorem hdimEqMaster_hs_hdimEq_of_alloc (K : Type*) [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (halloc : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      HdimEqMasterAlloc (statementIndex n + 2) K
        (MinAvoidRungs.stageIdeal n K c hn j) (fun d => 2 ≤ d)) :
    ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex n + 2) K
        (Ideal.span
          (Set.image (bridgeSystem n K c hn) {k | k.val < j.val})) :=
  AssRungFeeds.hdimEq_all_of_spec n K c hn
    ((hdimEqMaster_allSpec_iff n K c hn).mpr halloc)

#print axioms hdimEqMaster_hs_hdimEq_of_alloc

/-- HD2 wiring (conditional-exact on `[halloc]`): the same verbatim
binder feeds the HD2 `hsucc` master (`RungOneDiagonalDischarge` — its
`hdimEq` input is binder-identical to the HS one), so this is the
HS corollary under the HD2 consumption address.

Conditional on exactly `[halloc]`. -/
theorem hdimEqMaster_hd2_hdimEq_of_alloc (K : Type*) [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (halloc : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      HdimEqMasterAlloc (statementIndex n + 2) K
        (MinAvoidRungs.stageIdeal n K c hn j) (fun d => 2 ≤ d)) :
    ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex n + 2) K
        (Ideal.span
          (Set.image (bridgeSystem n K c hn) {k | k.val < j.val})) :=
  hdimEqMaster_hs_hdimEq_of_alloc K n hn c halloc

#print axioms hdimEqMaster_hd2_hdimEq_of_alloc

/-- GXQ wiring (conditional-exact on `[halloc]`): the `d = 2`
allocator slice proves the `HdimEqD2AtAss` slice — GXQ's exact
input shape (the slice GXQ closes `grExact`/`hker`/`hmult`/
`hsExact` from, and iff's with its nonstab remainder).

Conditional on exactly `[halloc]`. -/
theorem hdimEqMaster_gxq_hdimEqD2_of_alloc (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (halloc : HdimEqMasterAlloc m K J (fun d => d = 2)) :
    GradedExactnessDischarge.HdimEqD2AtAss m K J :=
  (hdimEqMaster_d2_iff m K J).mpr halloc

#print axioms hdimEqMaster_gxq_hdimEqD2_of_alloc

/-- GXQ remainder (unconditional): the allocator `d = 2` slice is
the GXQ non-stabilization remainder `HgrNonstabD2AtAss` — via the
slice corollary plus the GXQ `dimEqAttack_hdimEqD2_iff_nonstab`
supplier (never reproved).
-/
theorem hdimEqMaster_gxq_allocD2_iff_nonstab (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K)) :
    HdimEqMasterAlloc m K J (fun d => d = 2) ↔
      DimEqAttackDimTwo.HgrNonstabD2AtAss m K J :=
  (hdimEqMaster_d2_iff m K J).symm.trans
    (DimEqAttackDimTwo.dimEqAttack_hdimEqD2_iff_nonstab m K J)

#print axioms hdimEqMaster_gxq_allocD2_iff_nonstab

/-- J9 wiring, single stage (conditional-exact on `[hd2, hge3]`):
the split allocator slices prove `HdimEqMinAtAss` — the exact
conclusion shape of `final_hdimEqMin_of_d2_ge3` (which feeds it
from High-form inputs; here from allocator slices).

Conditional on exactly `[hd2, hge3]`. -/
theorem hdimEqMaster_j9_hdimEqMin_of_allocSplit (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hd2 : HdimEqMasterAlloc m K J (fun d => d = 2))
    (hge3 : HdimEqMasterAlloc m K J (fun d => 3 ≤ d)) :
    UnmixednessAtLengthTwo.HdimEqMinAtAss m K J :=
  (hdimEqMaster_min_split m K J).mpr ⟨hd2, hge3⟩

#print axioms hdimEqMaster_j9_hdimEqMin_of_allocSplit

/-- J9 wiring, rung-`∀` (conditional-exact on `[halloc]`): the
per-stage split allocator slices prove the verbatim rung-`∀`
`hdimEq` binder — the exact shape of the J9 `hsucc` per-rung feed
(`fun j hj =>... : HdimEqMinAtAss` at span ideals).

Conditional on exactly `[halloc]`. -/
theorem hdimEqMaster_j9_hdimEq_all_of_allocSplit (K : Type*)
    [Field K] (n : ℕ) (hn : 0 < n)
    (c : Fin n → Fin n → Fin n → K)
    (halloc : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      HdimEqMasterAlloc (statementIndex n + 2) K
          (MinAvoidRungs.stageIdeal n K c hn j) (fun d => d = 2) ∧
        HdimEqMasterAlloc (statementIndex n + 2) K
          (MinAvoidRungs.stageIdeal n K c hn j) (fun d => 3 ≤ d)) :
    ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex n + 2) K
        (Ideal.span
          (Set.image (bridgeSystem n K c hn) {k | k.val < j.val})) :=
  AssRungFeeds.hdimEq_all_of_spec n K c hn (fun j hj =>
    hdimEqMaster_j9_hdimEqMin_of_allocSplit _ _ _ (halloc j hj).1
      (halloc j hj).2)

#print axioms hdimEqMaster_j9_hdimEq_all_of_allocSplit

/-! ## §6. Residual register: the `d ≥ 2` allocator is the crux -/

/-- Crux address, kernel form (unconditional, no attack): the
`d ≥ 2` allocator ⟺ `HkerMinAtAss` — via the minimal corollary
plus the `hdimEqMin_iff_hkerMin` supplier.
-/
theorem hdimEqMaster_crux_iff_hkerMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HdimEqMasterAlloc m K J (fun d => 2 ≤ d) ↔
      UnmixednessAtLengthTwo.HkerMinAtAss m K J :=
  (hdimEqMaster_min_iff m K J).symm.trans
    (DimensionToMultiplicity.hdimEqMin_iff_hkerMin m K J)

#print axioms hdimEqMaster_crux_iff_hkerMin

/-- Crux address, High form (unconditional, no attack): the `d ≥ 2`
allocator ⟺ `HnoHomRelHighMinAtAss` — the four-step ring
(`hdimEqMin` ⟺ `hkerMin` ⟺ `hwitMin` ⟺ High, all suppliers). The
allocator at `d ≥ 2` is the crux under a fourth name; closing it
is out of scope for this lane by design.
-/
theorem hdimEqMaster_crux_iff_high (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HdimEqMasterAlloc m K J (fun d => 2 ≤ d) ↔
      DimensionToMultiplicity.HnoHomRelHighMinAtAss m K J :=
  (hdimEqMaster_min_iff m K J).symm.trans
    ((DimensionToMultiplicity.hdimEqMin_iff_hkerMin m K J).trans
      ((DimensionToMultiplicity.hwitMin_iff_hkerMin m K J).symm.trans
        ⟨DimensionToMultiplicity.noHomRelHighMin_of_hwitMin m K J,
          DimensionToMultiplicity.hwitMin_of_noHomRelHighMin m K J⟩))

#print axioms hdimEqMaster_crux_iff_high

/-- `d = 2` crux address (unconditional, no attack): the allocator
`d = 2` slice ⟺ `HkerD2AtAss` — slice corollary, then the GX
grExact iff (reversed), then the Rees D2-ring iff. All suppliers.
-/
theorem hdimEqMaster_d2_iff_hkerD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HdimEqMasterAlloc m K J (fun d => d = 2) ↔
      WitnessKernelDimTwo.HkerD2AtAss m K J :=
  (hdimEqMaster_d2_iff m K J).symm.trans
    ((GradedExactnessDischarge.grExactDischarge_grExactD2_iff_hdimEqD2
      m K J).symm.trans
      (ReesClose.rees_grExactD2_iff_hkerD2 m K J))

#print axioms hdimEqMaster_d2_iff_hkerD2

/-- `d ≥ 3` crux address (unconditional, no attack): the allocator
`d ≥ 3` slice ⟺ `HkerMinGe3AtAss` — rees-9′ corollary, then the
`rge3_iff_hkerGe3` supplier. All suppliers.
-/
theorem hdimEqMaster_ge3_iff_hkerGe3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HdimEqMasterAlloc m K J (fun d => 3 ≤ d) ↔
      HighDimGe3Attack.HkerMinGe3AtAss m K J :=
  (hdimEqMaster_ge3_rees_iff m K J).symm.trans
    (ReesGe3Discharge.rge3_iff_hkerGe3 m K J)

#print axioms hdimEqMaster_ge3_iff_hkerGe3

/-! ## §7. Remainder register + verdict (doc-only)

closed (this lane, all verified in-file with `#print axioms`
standard-only):
* Trivial dimensions once, centrally: piece `d = 0` / `d = 1`,
  allocator `d = 0` / `d = 1` / `d ≤ 1`, ungated-collapse
  (`True`-gate ⟺ `2 ≤ d`-gate).
* Family corollaries: `HdimEqMinAtAss`, `HdimEqD2AtAss`, both
  `HdimEqMinGe3AtAss` twins, `HdimEqAllSpec`, `HdimEqRung`,
  `HdimEqPrime`, `HdimEqD23AtAss` (all unconditional iffs);
  `HdimEqAtAss`, `HdimEqUnivAllSpec` (conditional-exact
  one-directionals on `[huniv]`).
* Split: `d ≥ 2` ⟺ (`d = 2` ∧ `d ≥ 3`), at allocator and
  `HdimEqMinAtAss` level (both unconditional iffs).
* Consumers: HS + HD2 binders, GXQ slice + nonstab remainder
  (iff), J9 single-stage + rung-`∀` (all conditional-exact on
  the named allocator inputs, exact binder match).

open (exact, by design — the allocator's job is to make `hdimEq`
single, not to close it):
* The `d ≥ 2` allocator = the crux: iff `HkerMinAtAss` iff
  `HnoHomRelHighMinAtAss` (§6, stated as interfaces).
* Slice addresses: `d = 2` iff `HkerD2AtAss`; `d ≥ 3` iff
  `HkerMinGe3AtAss` (§6, stated as interfaces).

Verdict: partial by design — pure infrastructure + wiring.
Every `hdimEq` discharge lies in one place (the
allocator's `d ≥ 2` slice) and reaches every consumer above by a
single `exact`. No cheats or nonstandard axioms
anywhere in this file.
-/

end SingleAllocator
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
