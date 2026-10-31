/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Geometry.UnmixednessAtLengthTwo
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.ChiDegreeMaster
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedLift
import Appendix_FixedPoint.BezoutChain.Regularity.DimensionEquality.SingleAllocator
import Appendix_FixedPoint.BezoutChain.Regularity.DimensionEquality.MinAtAssClosure
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.HilbertSerreGrTransfer
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.HilbertSamuelDegree
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.NewtonDifferences
import Appendix_FixedPoint.BezoutChain.Regularity.Grade.DimEqualsEmbdim
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.SuperficialReduction
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.SesClosure
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.TowerClosure
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.PositiveDimTower
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoidRungs
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MkSystemBridge
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.Rung.RungDiagonalGap
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoid.MinAvoidInstances

/-!
# `HdimEqMinAtAss` closer at the rung-2 stage ideal
Closes the `hdimEq`/`halloc` column at the bad-V endgame point modulo the
exact reshaped tower residual. V1 unsound items are not resurrected (no A8, no D23,
no `∀c` claim, G1 by `statementIndex` arithmetic only).

## What this file proves

* (§0) open-1 closed, unconditional: `hchiGrowthAtAss_close` proves
  `HchiGrowthAtAss` (`ChiDegreeMaster.lean`) over general `(m, K, J)`
  by per-`Q` minimal-generator assembly (`grlift_sop_exists`), splitting
  `d = 0` (R-pin rewrite for the dim-pin + `supDimZeroBase_unconditional`
  for growth, via the `chiFunQ = supChi ⊥` bridge) vs `d ≥ 1` (direct
  `chiGrowth_of_grClose_atAss` application).
* (§1) H5 re-fired on the reshaped tower: `hchiReduceAtAss_of_reshapedTower`
  concludes `HchiReduceAtAss` from per-`Q`
  `[SupTowerPosDim, SupExactDimDrop]` via `hChiReduceAtAss_posDim_of_tower`.
* (§2) `HdimEqMinAtAss` + the `d ≥ 2` allocator slice conditional-exact on
  the reshaped tower only (H4 discharged by §0):
  `hdimEqMinAtAss_of_reshapedTower`, `alloc_ge2_of_reshapedTower`.
* (§3) Targets A/C/B at `J₂(c)` per `c ∈ RB4Cset` (exact finite set:
  `{diagWitness} ∪ realized extras`): `hdimEqMinAtAss_j2`, `alloc_ge2_j2`,
  `hdimEq_rung2_binder_j2` (G1-gated single-rung λ-term for the B1 binder
  `AssRungFeeds.lean` at n=3).

## Why the reshaped tower (not `[htower]`)

The unguarded `[htower]` (`∀ J' ≠ ⊤,...` of `hChiReduceAtAss_of_towers`)
is formally false: `supSelectColon_tower_false` (`TowerClosure`)
refutes it at `J' = 𝔪`, and `htower_forces_assEmpty` shows it can never
discharge over nonempty `Ass`. Conditioning on it would be vacuous. The
live residual is the positivity-guarded reshaped pair
`[SupTowerPosDim, SupExactDimDrop]` (true classically at `R_Q`; superficial
existence + catenary lower bound, ~300–700 lines, not attempted here).
open-2 is therefore exported as the exact reshaped residual, narrowed from
`[H4, H5]` to the per-`(c, Q)` reshaped tower.

## Status

unconditional: `hchiGrowthAtAss_close`.
conditional-exact on per-`Q` / per-`(c, Q)` `[SupTowerPosDim, SupExactDimDrop]`:
everything else. No restricted identifier is assumed anywhere; no `∀c` claim.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace MinAtAssCloser

/-! ## §0. Open-1: `HchiGrowthAtAss`, unconditionally -/

/-- Open-1 closed: the χ-growth SPEC holds unconditionally over general
`(m, K, J)`. Per `Q ∈ Ass(R ⧸ J)`, minimal-generator data comes from
`grlift_sop_exists`; `d = 0` closes via the R-pin rewrite (dim-pin) plus
the dim-zero base (growth) through the `chiFunQ = supChi ⊥` bridge, and
`d ≥ 1` is a direct `chiGrowth_of_grClose_atAss` application.
-/
theorem hchiGrowthAtAss_close (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    ChiDegreeMaster.HchiGrowthAtAss m K J := by
  intro Q _ hQ
  obtain ⟨d, g, hgen, hd⟩ := GradedLift.grlift_sop_exists Q
  by_cases hd0 : d = 0
  · subst hd0
    have hR := DimEqualsEmbdim.dimEmbAtAss_unconditional m K J Q hQ
    rw [← hd] at hR
    have hle : Ring.KrullDimLE 0
        (Localization.AtPrime Q ⧸ (⊥ : Ideal (Localization.AtPrime Q))) :=
      SesClosure.krullDimLE_quotBot_of_pin 0 hR
    have h0 := SesClosure.supDimZeroBase_unconditional
      (R := Localization.AtPrime Q) (⊥ : Ideal (Localization.AtPrime Q)) hle
    have hlink : ChiDegreeMaster.chiFunQ m K Q = fun n : ℕ =>
        ((SuperficialReduction.supChi (R := Localization.AtPrime Q) ⊥ n : ℕ) : ℚ) := by
      funext n
      change ((HilbertSamuelDegree.hsSamuel (R := Localization.AtPrime Q) n : ℕ) : ℚ) = _
      rw [← SuperficialReduction.supChi_bot]
    refine ⟨0, hR, ?_⟩
    rw [hlink]
    exact h0
  · have hd1 : 1 ≤ d := by omega
    exact HilbertSerreGrTransfer.chiGrowth_of_grClose_atAss m K J Q hQ g hgen hd hd1

#print axioms hchiGrowthAtAss_close

/-! ## §1. The reshaped residual + H5 from it -/

/-- The reshaped per-`Q` tower residual (the live open-2 form): dimension pin
plus `[SupTowerPosDim, SupExactDimDrop]` at every `Q ∈ Ass(R ⧸ J)`. This is
exactly the input of `hChiReduceAtAss_posDim_of_tower`
(`PositiveDimTower.lean`). The unguarded `[htower]`
(`∀ J' ≠ ⊤`) is not used: it is formally false
(`supSelectColon_tower_false`), so this positivity-guarded reshape is the
only viable vehicle.

Status: open residual (definition). -/
abbrev ReshapedTowerAtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    ∃ dimN : ℕ,
      ringKrullDim (Localization.AtPrime Q)
        = ((((dimN : ℕ)) : ℕ∞) : WithBot ℕ∞) ∧
      TowerClosure.SupTowerPosDim (R := Localization.AtPrime Q) ∧
        PositiveDimTower.SupExactDimDrop (R := Localization.AtPrime Q)

#print axioms ReshapedTowerAtAss

/-- H5 from the reshaped tower: the verbatim `HchiReduceAtAss` conclusion
from per-`Q` `[SupTowerPosDim, SupExactDimDrop]`, re-firing
`hChiReduceAtAss_posDim_of_tower`.

Conditional on exactly per-`Q` `[SupTowerPosDim, SupExactDimDrop]`. -/
theorem hchiReduceAtAss_of_reshapedTower (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (htower : ReshapedTowerAtAss m K J) :
    ChiDegreeMaster.HchiReduceAtAss m K J :=
  PositiveDimTower.hChiReduceAtAss_posDim_of_tower m K J htower

#print axioms hchiReduceAtAss_of_reshapedTower

/-! ## §2. `HdimEqMinAtAss` + allocator from the reshaped tower -/

/-- `HdimEqMinAtAss` over general `(m, K, J)` from the reshaped tower alone:
H4 is discharged unconditionally by §0, H5 by §1, R is unconditional in
the closer. Fires `hdimEqMinAtAss_close_of_h4H5`.

Conditional on exactly per-`Q` `[SupTowerPosDim, SupExactDimDrop]`. -/
theorem hdimEqMinAtAss_of_reshapedTower (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (htower : ReshapedTowerAtAss m K J) :
    UnmixednessAtLengthTwo.HdimEqMinAtAss m K J :=
  MinAtAssClosure.hdimEqMinAtAss_close_of_h4H5 m K J
    (hchiGrowthAtAss_close m K J)
    (hchiReduceAtAss_of_reshapedTower m K J htower)

#print axioms hdimEqMinAtAss_of_reshapedTower

/-- The `d ≥ 2` allocator slice over general `(m, K, J)` from the reshaped
tower alone (same discharge, allocator spelling via
`alloc_ge2_close_of_h4H5`).

Conditional on exactly per-`Q` `[SupTowerPosDim, SupExactDimDrop]`. -/
theorem alloc_ge2_of_reshapedTower (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (htower : ReshapedTowerAtAss m K J) :
    SingleAllocator.HdimEqMasterAlloc m K J (fun d => 2 ≤ d) :=
  MinAtAssClosure.alloc_ge2_close_of_h4H5 m K J
    (hchiGrowthAtAss_close m K J)
    (hchiReduceAtAss_of_reshapedTower m K J htower)

#print axioms alloc_ge2_of_reshapedTower

/-! ## §3. Targets A/C/B at `J₂(c)` per `c ∈ RB4Cset` -/

/-- The exact finite `c`-set (design note F8): `{diagWitness K} ∪ extras`, where
`extras` is the finite set of structure constants realized by the bad-V
lead bases (26,634 tested bases; prose-side enumeration). Stated as a set
over an explicit `Finset` parameter so no `DecidableEq` on `K`-valued
functions is needed and no `∀c` claim is made (obligations G3/F10-∀ stay open).
-/
def RB4Cset (K : Type*) [Field K]
    (extra : Finset (Fin 3 → Fin 3 → Fin 3 → K)) :
    Set (Fin 3 → Fin 3 → Fin 3 → K) :=
  insert (RungDiagonalGap.diagWitness K) ↑extra

#print axioms RB4Cset

/-- The pinned gap witness lies in every `RB4Cset` (the gap call sites pin
`c := diagWitness K`).
-/
theorem diagWitness_mem_rB4Cset (K : Type*) [Field K]
    (extra : Finset (Fin 3 → Fin 3 → Fin 3 → K)) :
    RungDiagonalGap.diagWitness K ∈ RB4Cset K extra :=
  Set.mem_insert _ _

#print axioms diagWitness_mem_rB4Cset

/-- Target A: `HdimEqMinAtAss` at `(statementIndex 3 + 2, K, J₂(c))` per
`c ∈ RB4Cset`, where `J₂(c)` is the rung-2 stage ideal at n=3 with the
exact `j₂ := gapRung2 hn` term. Fires Shape-A consumers A1–A7 at the
bad-V endgame point (A8 excluded per F1: different ideal, out of scope).

Conditional on exactly per-`(c, Q)` reshaped tower data. -/
theorem hdimEqMinAtAss_j2 (K : Type*) [Field K] (hn : 0 < 3)
    (extra : Finset (Fin 3 → Fin 3 → Fin 3 → K))
    (htower : ∀ c ∈ RB4Cset K extra,
      ReshapedTowerAtAss (statementIndex 3 + 2) K
        (MinAvoidRungs.stageIdeal 3 K c hn (MinAvoidInstances.gapRung2 hn)))
    (c : Fin 3 → Fin 3 → Fin 3 → K) (hc : c ∈ RB4Cset K extra) :
    UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex 3 + 2) K
      (MinAvoidRungs.stageIdeal 3 K c hn (MinAvoidInstances.gapRung2 hn)) :=
  hdimEqMinAtAss_of_reshapedTower _ K _ (htower c hc)

#print axioms hdimEqMinAtAss_j2

/-- Target C: the `fun d => 2 ≤ d` allocator spelling of Target A, per
`c ∈ RB4Cset` (definitionally Target A via `hdimEqMaster_min_iff`; proved
here via the §2 allocator closer).

Conditional on exactly per-`(c, Q)` reshaped tower data. -/
theorem alloc_ge2_j2 (K : Type*) [Field K] (hn : 0 < 3)
    (extra : Finset (Fin 3 → Fin 3 → Fin 3 → K))
    (htower : ∀ c ∈ RB4Cset K extra,
      ReshapedTowerAtAss (statementIndex 3 + 2) K
        (MinAvoidRungs.stageIdeal 3 K c hn (MinAvoidInstances.gapRung2 hn)))
    (c : Fin 3 → Fin 3 → Fin 3 → K) (hc : c ∈ RB4Cset K extra) :
    SingleAllocator.HdimEqMasterAlloc (statementIndex 3 + 2) K
      (MinAvoidRungs.stageIdeal 3 K c hn (MinAvoidInstances.gapRung2 hn))
      (fun d => 2 ≤ d) :=
  alloc_ge2_of_reshapedTower _ K _ (htower c hc)

#print axioms alloc_ge2_j2

/-- Target B (G1-gated): the single-rung λ-term discharging the B1 binder
(`AssRungFeeds.lean`) — and thereby B1–B6 — at n=3, per
`c ∈ RB4Cset`. `statementIndex 3 + 1 = 3` (`shift_add_one`), so
`2 ≤ j.val` forces `j.val = 2` and `j = gapRung2 hn` by `Fin.ext`;
transport to the rung-2 Target-A instance. Full `∀j` closure is not
claimed (per-site gating, R4c-v2 precedent).

Conditional on exactly per-`(c, Q)` reshaped tower data. -/
theorem hdimEq_rung2_binder_j2 (K : Type*) [Field K] (hn : 0 < 3)
    (extra : Finset (Fin 3 → Fin 3 → Fin 3 → K))
    (htower : ∀ c ∈ RB4Cset K extra,
      ReshapedTowerAtAss (statementIndex 3 + 2) K
        (MinAvoidRungs.stageIdeal 3 K c hn (MinAvoidInstances.gapRung2 hn)))
    (c : Fin 3 → Fin 3 → Fin 3 → K) (hc : c ∈ RB4Cset K extra)
    (j : Fin (statementIndex 3 + 1)) (hj : 2 ≤ j.val) :
    UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex 3 + 2) K
      (Ideal.span (Set.image (bridgeSystem 3 K c hn) {k | k.val < j.val})) := by
  have h3 : statementIndex 3 + 1 = 3 := shift_add_one 3 hn
  have hj2 : j.val = 2 := by
    have hlt : j.val < statementIndex 3 + 1 := j.isLt
    omega
  have heq : j = MinAvoidInstances.gapRung2 hn := by
    apply Fin.ext
    show j.val = (MinAvoidInstances.gapRung2 hn).val
    rw [hj2]
    rfl
  rw [heq]
  exact hdimEqMinAtAss_j2 K hn extra htower c hc

#print axioms hdimEq_rung2_binder_j2

end MinAtAssCloser
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
