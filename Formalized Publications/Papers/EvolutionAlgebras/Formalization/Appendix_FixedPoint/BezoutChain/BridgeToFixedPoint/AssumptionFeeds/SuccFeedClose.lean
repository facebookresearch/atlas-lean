/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.FixedPointFromBezout
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoidRungs
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.SuccClosureRungs
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.AssumptionFeeds.RungOneDiagonalDischarge
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoid.MinAvoidJoin
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.Rung.RungOneJoin
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.Rung.RungDiagonal
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.Rung.RungDiagonalGap
import Appendix_FixedPoint.BezoutChain.Geometry.UnmixednessAtLengthTwo
import Appendix_FixedPoint.BezoutChain.Regularity.Assembly.JointAssembly
import Appendix_FixedPoint.BezoutChain.Regularity.DimensionEquality.SingleAllocator
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.RegularityBridge

/-!
# `hass`/`hsucc` feed close on surviving SPECs
Integrate the `hass`/`hsucc` feed end-to-end on surviving SPECs
only: the S1 (`MinAvoidJoin`) allocator masters with
rung 1 discharged by the HD2/Rung1Join feeds and `minAvoid`
narrowed to the S2/S3 SPEC pair
(`MinAvoidPrimeSingleSpec`/`MinAvoidNonprimeSpec`, S1).
No new math beyond wiring; every corollary below really closes.

## What is proved here

* §1 End-to-end `hass_all` master: general routes
  `[local-∀, supp-∀, alloc, prime, nonprime]` and
  `[local-∀, offcenter-∀, alloc, prime, nonprime]`, instance
  masters at `cDiagOnes`/Gap on `[alloc, prime, nonprime]`, the
  `d = 2`/`d ≥ 3` split-allocator variant, and the `n = 1`
  unconditional terminal.
* §2 End-to-end `hsucc` masters in `SuccClosureRungs`-§4 shape: the
  master fired with rung 1 from the HD2 feeders, `hdimEq` from
  the allocator converters, and `hmin` from the SPEC pair — same
  six input shapes as §1.
* §3 Drift twins: the general §1/§2 masters restated on the
  unfolded prime/nonprime binders. Sibling S2/S3 outputs
  are not available (checked: no S2/S3 modules in tree);
  the SPEC hypotheses are kept regardless, and these twins fire
  directly if S2/S3 land proving unfolded `∀`-forms instead of
  the stated SPEC defs. Both shapes wired.
* §4 J9 plug + audits: the §1 feed conclusion plugged into the
  J9 `final_hsucc` hass leg (binder, zero delta by
  elaboration), the pair→`hmin` audit, and the
  split-allocator→`hdimEq`-binder audit.
* §5 feed-status register (doc only): open/closed per input +
  owning strand.

Minimality convention: every master below lists exactly which
proof step consumes which hypothesis (`Consumes:`) and why no
input can be dropped (`Minimal:` — each input feeds a disjoint
leg of the cited master). The rung-1 gates, the allocator, and
the two SPECs are pairwise disjoint legs everywhere.

Status: `hass`/`hsucc` feed complete on surviving SPECs +
J9 hass leg plugged.

## Residual register (verbatim)

closed this lane: [`hass_all` on `[gates/∅, alloc(-split),
prime, nonprime]` + `n = 1` terminal]; [`hsucc` in shape
on the same inputs + `n = 1` terminal]; [drift twins on unfolded
binders]; [J9 hass-leg plug + pair/split audits].
open (exact, owned elsewhere): [per-instance rung-1 local gates
(in HD2)]; [per-stage `d ≥ 2` allocator = the crux
]; [`MinAvoidPrimeSingleSpec` (S2)];
[`MinAvoidNonprimeSpec` (S3)].

## Import DAG

New leaf module (no importers): `BridgeToFixedPoint/MinAvoidJoin` (S1
masters + SPECs + splitter iff), `BridgeToFixedPoint/RungOneDiagonalDischarge`
(rung-1 feeders + `cDiagOnes`), `BridgeToFixedPoint/RungOneJoin` (`n = 1`
terminals), `BridgeToFixedPoint/SuccClosureRungs` (master),
`Regularity/SingleAllocator` (allocator + converters),
`Regularity/JointAssembly` (J9 plug target),
`BridgeToFixedPoint/MinAvoidRungs` (register shapes), `BridgeToFixedPoint/RungDiagonal`
(`rungI0`), `BridgeToFixedPoint/RungDiagonalGap` (`diagWitness`),
`BridgeToFixedPoint/FixedPointFromBezout` (`bridgeSystem`,
`statementIndex`, `shiftConsts`), `Geometry/UnmixednessAtLengthTwo`
(`HdimEqMinAtAss` binder spelling),
`Regularity/RegularityBridge` (`SuccessiveSMulRegular`). No cycle risk.

## References

Project (`Formalization/Appendix_FixedPoint/BezoutChain/`):

* `BridgeToFixedPoint/MinAvoid/MinAvoidJoin.lean/:
  542/:568` (SPECs, splitter iff, §3 masters consumed here).
* `BridgeToFixedPoint/AssumptionFeeds/RungOneDiagonalDischarge.lean`
  (rung-1 feeders consumed here).
* `BridgeToFixedPoint/Rung/RungOneJoin.lean` (`n = 1` terminals).
* `BridgeToFixedPoint/SuccClosureRungs.lean` (`hsucc` master fired in §2).
* `Regularity/DimensionEquality/SingleAllocator.lean`
  (allocator, HS converter, split converter).
* `Regularity/Assembly/JointAssembly.lean`
  (J9 plug target + hass binder).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace SuccFeedClose

/-! ## §1. End-to-end `hass_all` on surviving SPECs -/

/-- Full `hass_all` from `[local-∀, supp-∀, per-stage allocator,
prime-singles, nonprime-minimal]` (NO rung-1, NO `hdimEq`, no
full-`minAvoid` hypothesis): the S1 master with its
`MinAvoidAllSpec` binder narrowed by the S1 splitter iff.

Consumes: `hdiag`/`hsupp` (S1 rung-1 leg via the HD2
feeder); `halloc` (S1 `hdimEq` leg via the allocator HS
converter); `hprime`/`hnonprime` (S1 `hmin` leg via the
splitter). Minimal: each input feeds a disjoint S1-master leg;
deleting any one leaves its leg unsupplied.

Conditional on exactly `[local, supp, halloc, hprime,
hnonprime]`. -/
theorem hassFeed_all_of_local_of_supp_of_alloc_of_pair
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
    ((MinAvoidJoin.minAvoidAllSpec_iff_primeSingle_nonprime n K c
      hn).mpr ⟨hprime, hnonprime⟩)

#print axioms hassFeed_all_of_local_of_supp_of_alloc_of_pair

/-- Full `hass_all` from `[local-∀, offcenter-∀, per-stage
allocator, prime-singles, nonprime-minimal]` (no rung-1, no
`supp`, no `hdimEq`, no full-`minAvoid` hypothesis): the S1
master with its `MinAvoidAllSpec` binder narrowed by the
splitter.

Consumes: `hdiag`/`hoff` (S1 rung-1 leg via the HD2
offcenter-gated feeder); `halloc` (`hdimEq` leg via the HS
converter); `hprime`/`hnonprime` (`hmin` leg via the splitter).
Minimal: disjoint legs; no input covers another's leg.

Conditional on exactly `[local, offcenter, halloc, hprime,
hnonprime]`. -/
theorem hassFeed_all_of_local_of_offcenter_of_alloc_of_pair
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
    ((MinAvoidJoin.minAvoidAllSpec_iff_primeSingle_nonprime n K c
      hn).mpr ⟨hprime, hnonprime⟩)

#print axioms hassFeed_all_of_local_of_offcenter_of_alloc_of_pair

/-- Full `hass_all` at the all-ones-diagonal family from
`[per-stage allocator, prime-singles, nonprime-minimal]` only
(no rung-1 hypotheses — discharged by the HD2 family
close inside the S1 master; no `hdimEq`, no
full-`minAvoid`): the S1 instance master narrowed by the
splitter.

Consumes: `halloc` (`hdimEq` leg via the HS converter);
`hprime`/`hnonprime` (`hmin` leg via the splitter). Minimal:
two disjoint legs; the rung-1 leg is closed, not assumed.

Conditional on exactly `[halloc, hprime, hnonprime]`. -/
theorem hassFeed_all_cDiagOnes_of_alloc_of_pair (K : Type*)
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
    ((MinAvoidJoin.minAvoidAllSpec_iff_primeSingle_nonprime n K _
      hn).mpr ⟨hprime, hnonprime⟩)

#print axioms hassFeed_all_cDiagOnes_of_alloc_of_pair

/-- Full `hass_all` at the Gap witness from `[per-stage allocator,
prime-singles, nonprime-minimal]` only (no rung-1 hypotheses —
discharged by the HD2 instance close inside the S1
master): the S1 Gap master narrowed by the splitter.

Consumes: `halloc` (`hdimEq` leg); `hprime`/`hnonprime` (`hmin`
leg via the splitter). Minimal: two disjoint legs.

Conditional on exactly `[halloc, hprime, hnonprime]`. -/
theorem hassFeed_all_gap_of_alloc_of_pair (K : Type*) [Field K]
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
    ((MinAvoidJoin.minAvoidAllSpec_iff_primeSingle_nonprime 3 K _
      hn).mpr ⟨hprime, hnonprime⟩)

#print axioms hassFeed_all_gap_of_alloc_of_pair

/-- Full `hass_all` from `[local-∀, supp-∀, split allocator,
prime-singles, nonprime-minimal]` (NO rung-1, NO `hdimEq`, no
full-`minAvoid`): the S1 split-allocator master (the D2/Ge3
joint-attack shape) with rung 1 discharged by the HD2
feeder and `minAvoid` narrowed by the splitter.

Consumes: `hdiag`/`hsupp` (rung-1 leg via the HD2 feeder);
`hallocSplit` (`hdimEq` leg via the split converter inside S1);
`hprime`/`hnonprime` (`hmin` leg via the splitter). Minimal:
three disjoint legs.

Conditional on exactly `[local, supp, hallocSplit, hprime,
hnonprime]`. -/
theorem hassFeed_all_of_local_of_supp_of_allocSplit_of_pair
    (K : Type*) [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (hdiag : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      RungOneDiagonalDischarge.HdiagRung1 n K c hn k)
    (hsupp : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      RungOneDiagonalDischarge.HsuppRung1 n K c hn k)
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
    K n hn c
    (RungOneDiagonalDischarge.rung1step_of_local_of_supp n K c hn hdiag
      hsupp)
    hallocSplit
    ((MinAvoidJoin.minAvoidAllSpec_iff_primeSingle_nonprime n K c
      hn).mpr ⟨hprime, hnonprime⟩)

#print axioms hassFeed_all_of_local_of_supp_of_allocSplit_of_pair

/-- Full `hass_all` at `n = 1`, unconditional (no hypotheses at
all): the Rung1Join vacuous terminal, cited not
duplicated — the feed's `n = 1` leg is closed.
-/
theorem hassFeed_all_n1_unconditional (K : Type*) [Field K]
    (c : Fin 1 → Fin 1 → Fin 1 → K) (hn : 0 < 1) :
    ∀ j : Fin (statementIndex 1 + 1), 2 ≤ j.val →
      MinAvoidRungs.AssAvoidRung 1 K c hn j :=
  RungOneJoin.hass_all_n1_vacuous K c hn

#print axioms hassFeed_all_n1_unconditional

/-! ## §2. End-to-end `hsucc` in `SuccClosureRungs`-§4 shape -/

/-- Full `hsucc` from `[local-∀, supp-∀, per-stage allocator,
prime-singles, nonprime-minimal]` (NO rung-1, NO `hdimEq`, no
full-`minAvoid`): the `SuccClosureRungs` master with its three
binders fed — rung 1 by the HD2 feeder, `hdimEq` by the
allocator HS converter , `hmin` by the SPEC pair across
the S1 splitter + `rfl` certificate.

Consumes: `hdiag`/`hsupp` (`hrung1` binder);
`halloc` (`hdimEq` binder); `hprime`/`hnonprime` (`hmin` binder). Minimal:
each input feeds exactly one
binder; the three binders are disjoint.

Conditional on exactly `[local, supp, halloc, hprime,
hnonprime]`. -/
theorem hsuccFeed_of_local_of_supp_of_alloc_of_pair (K : Type*)
    [Field K]
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
  SuccClosureRungs.hsucc_bridgeSystem_of_rung1step_of_hdimEqMin_of_minAvoid
    K n hn c
    (RungOneDiagonalDischarge.rung1step_of_local_of_supp n K c hn hdiag
      hsupp)
    (SingleAllocator.hdimEqMaster_hs_hdimEq_of_alloc K n hn c
      halloc)
    ((MinAvoidJoin.minAvoidAllSpec_iff_primeSingle_nonprime n K c
      hn).mpr ⟨hprime, hnonprime⟩)

#print axioms hsuccFeed_of_local_of_supp_of_alloc_of_pair

/-- Full `hsucc` from `[local-∀, offcenter-∀, per-stage allocator,
prime-singles, nonprime-minimal]` (NO rung-1, NO `supp`): the
master with rung 1 from the HD2 offcenter-gated
feeder, `hdimEq` from the HS converter, `hmin` from the pair.

Consumes: `hdiag`/`hoff` (`hrung1` binder); `halloc`
(`hdimEq` binder); `hprime`/`hnonprime` (`hmin` binder).
Minimal: one input per binder.

Conditional on exactly `[local, offcenter, halloc, hprime,
hnonprime]`. -/
theorem hsuccFeed_of_local_of_offcenter_of_alloc_of_pair
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
  SuccClosureRungs.hsucc_bridgeSystem_of_rung1step_of_hdimEqMin_of_minAvoid
    K n hn c
    (RungOneDiagonalDischarge.rung1step_of_local_of_offcenter n K c hn
      hdiag hoff)
    (SingleAllocator.hdimEqMaster_hs_hdimEq_of_alloc K n hn c
      halloc)
    ((MinAvoidJoin.minAvoidAllSpec_iff_primeSingle_nonprime n K c
      hn).mpr ⟨hprime, hnonprime⟩)

#print axioms hsuccFeed_of_local_of_offcenter_of_alloc_of_pair

/-- Full `hsucc` at the all-ones-diagonal family from `[per-stage
allocator, prime-singles, nonprime-minimal]` only (no rung-1
hypotheses — rung 1 is the HD2 family close): the
master with `hdimEq` from the HS converter and `hmin` from the
pair.

Consumes: `halloc` (`hdimEq` binder); `hprime`/`hnonprime`
(`hmin` binder). Minimal: two disjoint binders; the
rung-1 binder is closed, not assumed.

Conditional on exactly `[halloc, hprime, hnonprime]`. -/
theorem hsuccFeed_cDiagOnes_of_alloc_of_pair (K : Type*)
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
  SuccClosureRungs.hsucc_bridgeSystem_of_rung1step_of_hdimEqMin_of_minAvoid
    K n hn _
    (RungOneDiagonalDischarge.rung1step_cDiagOnes n K hn)
    (SingleAllocator.hdimEqMaster_hs_hdimEq_of_alloc K n hn _
      halloc)
    ((MinAvoidJoin.minAvoidAllSpec_iff_primeSingle_nonprime n K _
      hn).mpr ⟨hprime, hnonprime⟩)

#print axioms hsuccFeed_cDiagOnes_of_alloc_of_pair

/-- Full `hsucc` at the Gap witness from `[per-stage allocator,
prime-singles, nonprime-minimal]` only (no rung-1 hypotheses —
rung 1 is the HD2 instance close): the master with
`hdimEq` from the HS converter and `hmin` from the pair.

Consumes: `halloc` (`hdimEq` binder); `hprime`/`hnonprime`
(`hmin` binder). Minimal: two disjoint binders.

Conditional on exactly `[halloc, hprime, hnonprime]`. -/
theorem hsuccFeed_gap_of_alloc_of_pair (K : Type*) [Field K]
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
  SuccClosureRungs.hsucc_bridgeSystem_of_rung1step_of_hdimEqMin_of_minAvoid
    K 3 hn _
    (RungOneDiagonalDischarge.rung1step_gap K hn)
    (SingleAllocator.hdimEqMaster_hs_hdimEq_of_alloc K 3 hn _
      halloc)
    ((MinAvoidJoin.minAvoidAllSpec_iff_primeSingle_nonprime 3 K _
      hn).mpr ⟨hprime, hnonprime⟩)

#print axioms hsuccFeed_gap_of_alloc_of_pair

/-- Full `hsucc` from `[local-∀, supp-∀, split allocator,
prime-singles, nonprime-minimal]` (NO rung-1, NO `hdimEq`, no
full-`minAvoid`): the master with rung 1 from the HD2
feeder, `hdimEq` from the split converter ,
`hmin` from the pair. The D2/Ge3 joint-attack `hsucc` shape.

Consumes: `hdiag`/`hsupp` (`hrung1` binder); `hallocSplit`
(`hdimEq` binder); `hprime`/`hnonprime` (`hmin` binder).
Minimal: one input per binder.

Conditional on exactly `[local, supp, hallocSplit, hprime,
hnonprime]`. -/
theorem hsuccFeed_of_local_of_supp_of_allocSplit_of_pair
    (K : Type*) [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (hdiag : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      RungOneDiagonalDischarge.HdiagRung1 n K c hn k)
    (hsupp : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      RungOneDiagonalDischarge.HsuppRung1 n K c hn k)
    (hallocSplit : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex n + 2) K
          (MinAvoidRungs.stageIdeal n K c hn j) (fun d => d = 2) ∧
        SingleAllocator.HdimEqMasterAlloc (statementIndex n + 2) K
          (MinAvoidRungs.stageIdeal n K c hn j) (fun d => 3 ≤ d))
    (hprime : MinAvoidJoin.MinAvoidPrimeSingleSpec n K c hn)
    (hnonprime : MinAvoidJoin.MinAvoidNonprimeSpec n K c hn) :
    RegularityBridge.SuccessiveSMulRegular (bridgeSystem n K c hn) :=
  SuccClosureRungs.hsucc_bridgeSystem_of_rung1step_of_hdimEqMin_of_minAvoid
    K n hn c
    (RungOneDiagonalDischarge.rung1step_of_local_of_supp n K c hn hdiag
      hsupp)
    (SingleAllocator.hdimEqMaster_j9_hdimEq_all_of_allocSplit K n
      hn c hallocSplit)
    ((MinAvoidJoin.minAvoidAllSpec_iff_primeSingle_nonprime n K c
      hn).mpr ⟨hprime, hnonprime⟩)

#print axioms hsuccFeed_of_local_of_supp_of_allocSplit_of_pair

/-- Full `hsucc` at `n = 1`, unconditional (no hypotheses at
all): the Rung1Join terminal, cited not duplicated.
-/
theorem hsuccFeed_n1_unconditional (K : Type*) [Field K]
    (c : Fin 1 → Fin 1 → Fin 1 → K) (hn : 0 < 1) :
    RegularityBridge.SuccessiveSMulRegular (bridgeSystem 1 K c hn) :=
  RungOneJoin.hsucc_n1_unconditional K c hn

#print axioms hsuccFeed_n1_unconditional

/-! ## §3. Drift twins on unfolded binders

Sibling S2/S3 outputs are not available (checked:
no S2/S3 modules in tree — the stated SPEC shapes at S1
 are the only addresses). The §1/§2 masters keep
the SPEC hypotheses regardless; the twins below fire directly if
S2/S3 land proving the unfolded `∀`-forms instead. Both shapes
wired; no drift risk either way. -/

/-- Full `hass_all` from `[local-∀, supp-∀, per-stage allocator]`
plus the unfolded prime/nonprime `∀`-forms (same binders as the
S1 SPEC bodies, stated without the SPEC defs):
definitionally the §1 general master, so S2/S3 closes feed it
whatever shape they land in.

Consumes: `hdiag`/`hsupp`/`halloc` (as in §1);
`hprime`/`hnonprime` (the SPEC bodies, feeding the SPEC
hypotheses definitionally). Minimal: same disjoint legs as §1.

Conditional on exactly `[local, supp, halloc, hprime,
hnonprime]` (unfolded shapes). -/
theorem hassFeed_all_of_local_of_supp_of_alloc_of_unfoldedPair
    (K : Type*) [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (hdiag : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      RungOneDiagonalDischarge.HdiagRung1 n K c hn k)
    (hsupp : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      RungOneDiagonalDischarge.HsuppRung1 n K c hn k)
    (halloc : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex n + 2) K
        (MinAvoidRungs.stageIdeal n K c hn j) (fun d => 2 ≤ d))
    (hprime : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      (MinAvoidRungs.stageIdeal n K c hn j).IsPrime →
      (bridgeSystem n K c hn) j ∉
        MinAvoidRungs.stageIdeal n K c hn j)
    (hnonprime : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      ¬ (MinAvoidRungs.stageIdeal n K c hn j).IsPrime →
      MinAvoidRungs.MinAvoidRung n K c hn j) :
    ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      MinAvoidRungs.AssAvoidRung n K c hn j :=
  hassFeed_all_of_local_of_supp_of_alloc_of_pair K n hn c hdiag
    hsupp halloc hprime hnonprime

#print axioms hassFeed_all_of_local_of_supp_of_alloc_of_unfoldedPair

/-- Full `hsucc` from `[local-∀, supp-∀, per-stage allocator]`
plus the unfolded prime/nonprime `∀`-forms: definitionally the
§2 general master in shape.

Consumes: `hdiag`/`hsupp` (`hrung1` binder); `halloc`
(`hdimEq` binder); `hprime`/`hnonprime` (`hmin` binder via the
SPEC bodies). Minimal: one input per binder.

Conditional on exactly `[local, supp, halloc, hprime,
hnonprime]` (unfolded shapes). -/
theorem hsuccFeed_of_local_of_supp_of_alloc_of_unfoldedPair
    (K : Type*) [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (hdiag : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      RungOneDiagonalDischarge.HdiagRung1 n K c hn k)
    (hsupp : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      RungOneDiagonalDischarge.HsuppRung1 n K c hn k)
    (halloc : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex n + 2) K
        (MinAvoidRungs.stageIdeal n K c hn j) (fun d => 2 ≤ d))
    (hprime : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      (MinAvoidRungs.stageIdeal n K c hn j).IsPrime →
      (bridgeSystem n K c hn) j ∉
        MinAvoidRungs.stageIdeal n K c hn j)
    (hnonprime : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      ¬ (MinAvoidRungs.stageIdeal n K c hn j).IsPrime →
      MinAvoidRungs.MinAvoidRung n K c hn j) :
    RegularityBridge.SuccessiveSMulRegular (bridgeSystem n K c hn) :=
  hsuccFeed_of_local_of_supp_of_alloc_of_pair K n hn c hdiag hsupp
    halloc hprime hnonprime

#print axioms hsuccFeed_of_local_of_supp_of_alloc_of_unfoldedPair

/-! ## §4. J9 plug + feed audits

The §1 feed conclusion plugs the J9 hass leg
(`final_hsucc_of_hdich_of_d2_ge3_of_hass` — its
`hass` binder); elaboration of the plug is the zero-delta
verdict. The two audits name the pair and
split→`hdimEq` chains explicitly. -/

/-- Full `hsucc` via J9 with the hass leg supplied by the §1
feed: `final_hsucc_of_hdich_of_d2_ge3_of_hass` at
`hass := hassFeed`. The J9-internal legs (`hdich`, per-rung
`d2`/`ge3` → `HdimEqMin`) and the feed-internal legs
(`local`/`supp` → rung 1, `alloc` → `hdimEq`, pair → `minAvoid`)
are disjoint by construction — dual rung-1/`hdimEq` routes feed
disjoint masters, listed in full, not minimized.

Consumes: `hdich`/`hd2`/`hge3` (J9 legs); `hdiag`/`hsupp`
(feed rung-1 leg); `halloc` (feed `hdimEq` leg);
`hprime`/`hnonprime` (feed `hmin` leg).

Conditional on exactly `[hdich, d2∀, ge3∀, local, supp,
halloc, hprime, hnonprime]` (plug certificate). -/
theorem plug_j9_hsucc_of_hdich_of_d2_ge3_of_feed (K : Type*)
    [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (hdich : JointAssembly.HdichRung1 n K c hn)
    (hd2 : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      WitnessHighAttack.HnoHomRelHighD2AtAss (statementIndex n + 2) K
        (Ideal.span (Set.image (bridgeSystem n K c hn)
          {k | k.val < j.val})))
    (hge3 : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      WitnessHighAttack.HnoHomRelHighMinGe3AtAss
        (statementIndex n + 2) K
        (Ideal.span (Set.image (bridgeSystem n K c hn)
          {k | k.val < j.val})))
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
  JointAssembly.final_hsucc_of_hdich_of_d2_ge3_of_hass
    K n hn c hdich hd2 hge3
    (hassFeed_all_of_local_of_supp_of_alloc_of_pair K n hn c hdiag
      hsupp halloc hprime hnonprime)

#print axioms plug_j9_hsucc_of_hdich_of_d2_ge3_of_feed

/-- Audit: the SPEC pair feeds the `SuccClosureRungs` `hmin`
binder with zero shape delta (stated verbatim, unfolded §4
shape across the reducible stage-ideal abbrev): the S1 splitter
plus the S1/`HS :458` `rfl` chain.
-/
theorem audit_minAvoidPair_feeds_400 (n : ℕ) (K : Type*)
    [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (hprime : MinAvoidJoin.MinAvoidPrimeSingleSpec n K c hn)
    (hnonprime : MinAvoidJoin.MinAvoidNonprimeSpec n K c hn) :
    ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      ∀ P ∈ (Ideal.span (Set.image (bridgeSystem n K c hn)
        {k | k.val < j.val})).minimalPrimes,
        (bridgeSystem n K c hn) j ∉ P :=
  (MinAvoidJoin.minAvoidAllSpec_iff_primeSingle_nonprime n K c
    hn).mpr ⟨hprime, hnonprime⟩

#print axioms audit_minAvoidPair_feeds_400

/-- Audit: the per-stage split allocator feeds the HS /
`hdimEq` binder with zero shape delta (stated verbatim),
via the allocator's split converter.
-/
theorem audit_allocSplit_feeds_hdimEq_binder (K : Type*)
    [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (hallocSplit : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex n + 2) K
          (MinAvoidRungs.stageIdeal n K c hn j) (fun d => d = 2) ∧
        SingleAllocator.HdimEqMasterAlloc (statementIndex n + 2) K
          (MinAvoidRungs.stageIdeal n K c hn j) (fun d => 3 ≤ d)) :
    ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex n + 2) K
        (Ideal.span
          (Set.image (bridgeSystem n K c hn)
            {k | k.val < j.val})) :=
  SingleAllocator.hdimEqMaster_j9_hdimEq_all_of_allocSplit K n
    hn c hallocSplit

#print axioms audit_allocSplit_feeds_hdimEq_binder

/-! ## §5. Feed-status register (doc only; see module docstring)

Per-input open/closed verdicts with owning strand. S1 =
`MinAvoidJoin`; HD2 = `RungOneDiagonalDischarge`;
RUNG1 = `RungOneJoin`; hdim = `SingleAllocator`; J9 = `JointAssembly`.

* rung1 (general rung-1 step): closed-as-gated — discharged by
  the HD2 feeders (local/supp local/offcenter)
  and discharged at instances (Gap
  `cDiagOnes` `n = 1`; RUNG1
  avoidance twins + offcenter join). `∀`-unconditional
  rung-1 is impossible (HD `c = 0` refutations — never
  attempted here). Residual per-instance gates
  `[local, supp/offcenter]`: open per `c`, HD2-owned.
* hdimEq-alloc (per-stage `d ≥ 2` allocator): open = the crux —
  allocator live (hdim), HS converter + split
  converter proved; `d ≤ 1` slices closed unconditional
  (hdim); `d ≥ 2` owned by /H
  (R1/R2/R3 + H1/H2/H3 pending; never attacked here).
* minAvoid-prime-single (`MinAvoidPrimeSingleSpec`, S1):
  open — S2 owns it (stated shape; §3 twin covers unfolded-shape results).
* minAvoid-nonprime (`MinAvoidNonprimeSpec`, S1):
  open — S3 owns it (stated shape; §3 twin covers unfolded-shape results).
* minAvoid_all (`MinAvoidAllSpec`): closed-as-narrowed —
  splitter iff unconditional (S1); verdict is the step
  mod `[below-steps, hdimEq]` (S1 §2 bank/
  + `n = 1` vacuity — consumed, never
  reproved).
* hass_all / hsucc end-to-end: closed-conditional — this lane
  §1 masters on `[gates, alloc(-split), pair]` +
  `n = 1` terminal; §2 masters in shape on the same
  inputs + `n = 1` terminal.
* J9 hass leg: plugged — the §1 conclusion feeds the J9
  `hass` binder with zero delta (plug theorem §4, by
  elaboration). J9 still needs `[d2∀, ge3∀, hdich∀]` +
  algebra data (crux + rung-1 territory, not this lane).
* crux (`HdimEqMin`/`HkerMin` at `d ≥ 2`): open — /H
  (outside-ring regularity + Hilbert–Samuel banks).
-/

end SuccFeedClose
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
