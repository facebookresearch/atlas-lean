/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Regular.IsSMulRegular
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.AssociatedGradedRing
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.SuperficialReduction
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.ColonTransfer
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.PositiveDimTower
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.ColonDimDrop
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.JointAvoidance
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.QuotientKernelAvoidance
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.JointRefinement
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedQuotientComparison
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.QuotientTowerFire

/-!
# T2 Rep-fire: the T1 chain re-fired on the repaired trace (T2-repfire)

M1-as-stated (`SupT1TraceOfGrAvoidQuot`, QuotAvoid:566) is false
(TraceVV:39-74 prose: `R = k⟦u,v⟧`, `J' = (u²,uv)`, `y = v`; the
`J'`-component `z = uv` defeats the trace while graded avoidance +
positivity hold). The repaired trace below adds exactly the missing
ungraded-avoidance hypothesis — the hypothesis the §7 kernel
`SupT1OfGrAvoidQuotRep` (QuotAvoid:593) already carries.

This file re-fires the whole T1 chain on the repaired M1:

* (§1) `SupT1TraceOfGrAvoidQuotRep` (repaired M1: graded + ungraded
  avoidance imply the order-one trace) and `supT1QuotRep_of_traceRep`
  (the §7 kernel from the repaired trace + `supRegular_of_avoidAss`).
  This closes `SupT1OfGrAvoidQuotRep` modulo the repaired trace.
* (§2) `supT1Data_of_quotAvoid_repairedRep`: the §7 T2 assembly
  (`supT1Data_of_quotAvoid_repaired`, QuotAvoid:664) re-fired on the
  repaired M1. Mechanical: the assembly already derives `hungr` via
  M2 (QuotAvoid:728-730) and `hungr` is exactly the new trace
  premise, so `apply htraceRep J' y hym hpos hungr` threads it.
* (§3) `supT1Data_of_quotAvoid_repaired_narrowRep` (R0-quot/R1
  discharged), `supT1Data_phiClosedRep` (= PhiClose:73 re-fired) and
  `supT1Data_of_quot_closedRep` (= QuotTowerFire:139 re-fired):
  T2-data from the repaired M1 + per-stage `hpos`/`hdepth` only.
* (§4) `supTowerExactGated_of_quotRep` (+ `towerGatedRep` alias):
  the depth-gated tower (= QuotTowerFire:210 re-fired) from the
  repaired M1 alone.

## Status

unconditional (from the explicit repaired trace + per-stage data):
everything here. SPEC (open, exact, true classically):
`SupT1TraceOfGrAvoidQuotRep` (the repaired M1 residual; the TraceVV
lane owns its proof).

## References

Project (read-only):
* `Regularity/HomologicalDepth/QuotientKernelAvoidance.lean` (`SupT1OfGrAvoidQuotRep`
  :593, `supT1QuotRep_of_trace`:614, `supT1Data_of_quotAvoid_repaired`
  :664, `supT1Data_of_quotAvoid_repaired_narrow`:762,
  `supRegular_of_avoidAss`:338, `supAssFiniteGrQuot_of_noetherian`
  :505).
* `Regularity/HomologicalDepth/TraceRepBridge.lean` (`supT1Data_phiClosed_of_traceVV`:185).
* `Regularity/HomologicalDepth/QuotientTowerFire.lean` (`supT1Data_of_quot_closed`:139,
  `supTowerExactGated_of_quot`:210); gated def `SupTowerExactGated`:476
  in ColonTransfer (canonical address for T1 chain + T2 masters).
* `Regularity/Koszul/GradedQuotientComparison.lean` (`grQuotComp`:301,
  `grQuotComp_compat`:324, `grQuotComp_irr`:345).
* `Regularity/HomologicalDepth/JointRefinement.lean`
  (`supJointUnhgradedRefine_of_noetherian`:126).
* `Regularity/HomologicalDepth/OrderOneTrace.lean` (:39-74 M1-as-stated falsity
  prose; owns the `SupT1TraceOfGrAvoidQuotRep` proof).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace RepFire

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AssociatedGradedRing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.SuperficialReduction
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.ColonTransfer
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.PositiveDimTower
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.ColonDimDrop
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.JointAvoidance
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.QuotientKernelAvoidance
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.JointRefinement
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedQuotientComparison
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.QuotientTowerFire

/-! ## §1. The repaired trace and the repaired kernel from it -/

/-- SPEC (repaired residual M1): the Valabrega–Valla order-one trace
from quotient-side graded avoidance plus ungraded avoidance. Verbatim
the `SupT1TraceOfGrAvoidQuot` binders (QuotAvoid:566) with the
ungraded-avoidance hypothesis added — the hypothesis the M1-as-stated
counterexample (TraceVV:39-74) shows is missing, and the §7 kernel
already carries. True classically (filter-regular + regular ⟹
superficial of order one); proved by the TraceVV lane.

Status: open (exact residual; true classically). -/
def SupT1TraceOfGrAvoidQuotRep (R : Type*) [CommRing R] [IsLocalRing R] :
    Prop :=
  ∀ (J' : Ideal R) (y : R) (hym : y ∈ IsLocalRing.maximalIdeal R),
    ¬ Ring.KrullDimLE 0 (R ⧸ J') →
    (∀ P ∈ associatedPrimes R (R ⧸ J'), y ∉ P) →
    (∀ Q ∈ associatedPrimes
        (associatedGraded (R ⧸ J') (supQuotAdicIdeal J'))
        (associatedGraded (R ⧸ J') (supQuotAdicIdeal J')),
      ¬ SupIrrelevantIdeal (R ⧸ J') (supQuotAdicIdeal J') ≤ Q →
        supDegOneLift (R ⧸ J') (supQuotAdicIdeal J')
          (Ideal.Quotient.mk J' y)
          (supQuot_mk_mem_powOne J' y hym) ∉ Q) →
    ∃ c : ℕ, ∀ n : ℕ, c ≤ n → ∀ z : R,
      z ∈ IsLocalRing.maximalIdeal R ^ (n + 2) ⊔ J' →
      z ∈ Ideal.span {y} →
      ∃ a : R, a ∈ IsLocalRing.maximalIdeal R ^ (n + 1) ⊔ J' ∧ a * y = z

#print axioms SupT1TraceOfGrAvoidQuotRep

/-- The fully repaired kernel (`SupT1OfGrAvoidQuotRep`, QuotAvoid:593)
from the repaired trace: regularity is `supRegular_of_avoidAss`
(QuotAvoid:338), the trace is the repaired M1. No R0/R1 input needed —
both halves are per-`y` consequences. Verbatim `supT1QuotRep_of_trace`
(QuotAvoid:614) re-fired on the Rep trace.
-/
theorem supT1QuotRep_of_traceRep {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R]
    (htraceRep : SupT1TraceOfGrAvoidQuotRep (R := R)) :
    SupT1OfGrAvoidQuotRep (R := R) := by
  intro J' y hym hpos hungr hgr
  exact ⟨supRegular_of_avoidAss J' y hungr,
    htraceRep J' y hym hpos hungr hgr⟩

#print axioms supT1QuotRep_of_traceRep

/-! ## §2. The §7 T2 assembly re-fired on the repaired trace -/

/-- T2-data existence from R0-quot + R1 + Rep-M1 + M2: verbatim
`supT1Data_of_quotAvoid_repaired` (QuotAvoid:664) with the repaired
trace. The re-plug is mechanical: the assembly already derives `hungr`
via M2 (QuotAvoid:728-730), and `hungr` is exactly the repaired
trace's new premise.

data + depth). -/
theorem supT1Data_of_quotAvoid_repairedRep {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R]
    (hInf : Infinite (R ⧸ IsLocalRing.maximalIdeal R))
    (hfinQ : SupAssFiniteGrQuot (R := R))
    (havoid : SupJointHomAvoid (R := R))
    (htraceRep : SupT1TraceOfGrAvoidQuotRep (R := R))
    (hrefine : SupJointUnhgradedRefine (R := R))
    (J' : Ideal R)
    (hpos : ¬ Ring.KrullDimLE 0 (R ⧸ J'))
    (hdepth : IsLocalRing.maximalIdeal R
      ∉ associatedPrimes R (R ⧸ J'))
    (φ : associatedGraded R (IsLocalRing.maximalIdeal R) →+*
      associatedGraded (R ⧸ J') (supQuotAdicIdeal J'))
    (hcompat : ∀ (y : R) (h1 : y ∈ IsLocalRing.maximalIdeal R ^ 1)
      (h2 : Ideal.Quotient.mk J' y ∈ supQuotAdicIdeal J' ^ 1),
      φ (supDegOneLift R (IsLocalRing.maximalIdeal R) y h1) =
        supDegOneLift (R ⧸ J') (supQuotAdicIdeal J')
          (Ideal.Quotient.mk J' y) h2)
    (hirr : ∀ Q ∈ associatedPrimes
        (associatedGraded (R ⧸ J') (supQuotAdicIdeal J'))
        (associatedGraded (R ⧸ J') (supQuotAdicIdeal J')),
      ¬ SupIrrelevantIdeal (R ⧸ J') (supQuotAdicIdeal J') ≤ Q →
        ¬ SupIrrelevantIdeal R (IsLocalRing.maximalIdeal R)
          ≤ Ideal.comap φ Q) :
    ∃ y : R, SupSelectData J' y ∧ SupT1Data J' y := by
  have hTfin : {Q : Ideal (associatedGraded (R ⧸ J')
      (supQuotAdicIdeal J')) |
      Q ∈ associatedPrimes
        (associatedGraded (R ⧸ J') (supQuotAdicIdeal J'))
        (associatedGraded (R ⧸ J') (supQuotAdicIdeal J')) ∧
        ¬ SupIrrelevantIdeal (R ⧸ J') (supQuotAdicIdeal J') ≤ Q}.Finite :=
    (hfinQ J').subset (fun Q hQ => hQ.1)
  have hSfin : ({Q : Ideal (associatedGraded (R ⧸ J')
      (supQuotAdicIdeal J')) |
      Q ∈ associatedPrimes
        (associatedGraded (R ⧸ J') (supQuotAdicIdeal J'))
        (associatedGraded (R ⧸ J') (supQuotAdicIdeal J')) ∧
        ¬ SupIrrelevantIdeal (R ⧸ J') (supQuotAdicIdeal J') ≤ Q}.image
      fun Q => Ideal.comap φ Q).Finite :=
    supPullback_finite φ _ hTfin
  have hprime : ∀ P ∈ ({Q : Ideal (associatedGraded (R ⧸ J')
      (supQuotAdicIdeal J')) |
      Q ∈ associatedPrimes
        (associatedGraded (R ⧸ J') (supQuotAdicIdeal J'))
        (associatedGraded (R ⧸ J') (supQuotAdicIdeal J')) ∧
        ¬ SupIrrelevantIdeal (R ⧸ J') (supQuotAdicIdeal J') ≤ Q}.image
      fun Q => Ideal.comap φ Q), P.IsPrime := by
    intro P hP
    obtain ⟨Q, hQmem, rfl⟩ := hP
    exact supPullback_isPrime φ Q
      (IsAssociatedPrime.isPrime hQmem.1)
  have hirrel : ∀ P ∈ ({Q : Ideal (associatedGraded (R ⧸ J')
      (supQuotAdicIdeal J')) |
      Q ∈ associatedPrimes
        (associatedGraded (R ⧸ J') (supQuotAdicIdeal J'))
        (associatedGraded (R ⧸ J') (supQuotAdicIdeal J')) ∧
        ¬ SupIrrelevantIdeal (R ⧸ J') (supQuotAdicIdeal J') ≤ Q}.image
      fun Q => Ideal.comap φ Q),
      ¬ SupIrrelevantIdeal R (IsLocalRing.maximalIdeal R) ≤ P := by
    intro P hP
    obtain ⟨Q, hQmem, rfl⟩ := hP
    exact hirr Q hQmem.1 hQmem.2
  obtain ⟨y₁, hym₁, hsel₁, hgr₁⟩ :=
    havoid hInf J' _ hSfin hprime hirrel
  obtain ⟨y, hym, hsel, hgr, hungr⟩ :=
    hrefine J' hdepth _ hSfin hprime hirrel y₁ hym₁ hsel₁
      (fun P hP => hgr₁ P hP)
  refine ⟨y, hsel, ?_, ?_⟩
  · exact supRegular_of_avoidAss J' y hungr
  · apply htraceRep J' y hym hpos hungr
    intro Q hQmem hQirr
    have hmem : Ideal.comap φ Q ∈
        ({Q : Ideal (associatedGraded (R ⧸ J') (supQuotAdicIdeal J')) |
        Q ∈ associatedPrimes
          (associatedGraded (R ⧸ J') (supQuotAdicIdeal J'))
          (associatedGraded (R ⧸ J') (supQuotAdicIdeal J')) ∧
          ¬ SupIrrelevantIdeal (R ⧸ J') (supQuotAdicIdeal J') ≤ Q}.image
        fun Q => Ideal.comap φ Q) :=
      ⟨Q, ⟨hQmem, hQirr⟩, rfl⟩
    have hav : supDegOneLift R (IsLocalRing.maximalIdeal R) y
        (supMem_powOne _ _ hym) ∉ Ideal.comap φ Q :=
      hgr _ hmem
    have himg : φ (supDegOneLift R (IsLocalRing.maximalIdeal R) y
        (supMem_powOne _ _ hym)) ∉ Q :=
      fun hcon => hav (Ideal.mem_comap.mpr hcon)
    rw [hcompat y _ (supQuot_mk_mem_powOne J' y hym)] at himg
    exact himg

#print axioms supT1Data_of_quotAvoid_repairedRep

/-! ## §3. Narrow + closed T2-data on the repaired trace -/

/-- The §2 assembly with R0-quot (§6) and R1 (proved
`supJointHomAvoid`) discharged: T2-data from Rep-M1 + M2 + `φ` data +
depth only. Verbatim `supT1Data_of_quotAvoid_repaired_narrow`
(QuotAvoid:762) re-fired.

Conditional on exactly
`[SupT1TraceOfGrAvoidQuotRep, SupJointUnhgradedRefine]` (+ `φ` data +
depth). -/
theorem supT1Data_of_quotAvoid_repaired_narrowRep {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R]
    (hInf : Infinite (R ⧸ IsLocalRing.maximalIdeal R))
    (htraceRep : SupT1TraceOfGrAvoidQuotRep (R := R))
    (hrefine : SupJointUnhgradedRefine (R := R))
    (J' : Ideal R)
    (hpos : ¬ Ring.KrullDimLE 0 (R ⧸ J'))
    (hdepth : IsLocalRing.maximalIdeal R
      ∉ associatedPrimes R (R ⧸ J'))
    (φ : associatedGraded R (IsLocalRing.maximalIdeal R) →+*
      associatedGraded (R ⧸ J') (supQuotAdicIdeal J'))
    (hcompat : ∀ (y : R) (h1 : y ∈ IsLocalRing.maximalIdeal R ^ 1)
      (h2 : Ideal.Quotient.mk J' y ∈ supQuotAdicIdeal J' ^ 1),
      φ (supDegOneLift R (IsLocalRing.maximalIdeal R) y h1) =
        supDegOneLift (R ⧸ J') (supQuotAdicIdeal J')
          (Ideal.Quotient.mk J' y) h2)
    (hirr : ∀ Q ∈ associatedPrimes
        (associatedGraded (R ⧸ J') (supQuotAdicIdeal J'))
        (associatedGraded (R ⧸ J') (supQuotAdicIdeal J')),
      ¬ SupIrrelevantIdeal (R ⧸ J') (supQuotAdicIdeal J') ≤ Q →
        ¬ SupIrrelevantIdeal R (IsLocalRing.maximalIdeal R)
          ≤ Ideal.comap φ Q) :
    ∃ y : R, SupSelectData J' y ∧ SupT1Data J' y :=
  supT1Data_of_quotAvoid_repairedRep (R := R) hInf
    supAssFiniteGrQuot_of_noetherian supJointHomAvoid
    htraceRep hrefine J' hpos hdepth φ hcompat hirr

#print axioms supT1Data_of_quotAvoid_repaired_narrowRep

/-- T2-data from the repaired trace + per-stage hypotheses only:
`supT1Data_phiClosed` (PhiClose:73) re-fired on Rep-M1, with `φ`-data
(`grQuotComp`/`_compat`/`_irr`) and M2
(`supJointUnhgradedRefine_of_noetherian`) discharged.
-/
theorem supT1Data_phiClosedRep {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R]
    (hInf : Infinite (R ⧸ IsLocalRing.maximalIdeal R))
    (htraceRep : SupT1TraceOfGrAvoidQuotRep (R := R))
    (J' : Ideal R)
    (hpos : ¬ Ring.KrullDimLE 0 (R ⧸ J'))
    (hdepth : IsLocalRing.maximalIdeal R
      ∉ associatedPrimes R (R ⧸ J')) :
    ∃ y : R, SupSelectData J' y ∧ SupT1Data J' y :=
  supT1Data_of_quotAvoid_repaired_narrowRep (R := R) hInf htraceRep
    (supJointUnhgradedRefine_of_noetherian (R := R) hInf)
    J' hpos hdepth (grQuotComp J')
    (grQuotComp_compat J') (grQuotComp_irr J')

#print axioms supT1Data_phiClosedRep

/-- T2-data from the repaired trace + per-stage depth:
`supT1Data_of_quot_closed` (QuotTowerFire:139) re-fired on Rep-M1.
-/
theorem supT1Data_of_quot_closedRep {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R]
    (hInf : Infinite (R ⧸ IsLocalRing.maximalIdeal R))
    (htraceRep : SupT1TraceOfGrAvoidQuotRep (R := R))
    (J' : Ideal R)
    (hpos : ¬ Ring.KrullDimLE 0 (R ⧸ J'))
    (hdepth : IsLocalRing.maximalIdeal R ∉ associatedPrimes R (R ⧸ J')) :
    ∃ y : R, SupSelectData J' y ∧ SupT1Data J' y :=
  supT1Data_of_quotAvoid_repaired_narrowRep (R := R) hInf htraceRep
    (supJointUnhgradedRefine_of_noetherian hInf)
    J' hpos hdepth (grQuotComp J')
    (fun y h1 h2 => grQuotComp_compat J' y h1 h2)
    (fun Q hQmem hQirr => grQuotComp_irr J' Q hQmem hQirr)

#print axioms supT1Data_of_quot_closedRep

/-! ## §4. The depth-gated tower on the repaired trace -/

/-- The depth-gated tower (`SupTowerExactGated`, ColonTransfer:476)
from the repaired M1 alone: `supTowerExactGated_of_quot`
(QuotTowerFire:210) re-fired.

Conditional on exactly `[SupT1TraceOfGrAvoidQuotRep]`
(+ infinite residue field). -/
theorem supTowerExactGated_of_quotRep {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R]
    (hInf : Infinite (R ⧸ IsLocalRing.maximalIdeal R))
    (htraceRep : SupT1TraceOfGrAvoidQuotRep (R := R)) :
    SupTowerExactGated (R := R) := by
  intro J' d hne hd hpin hdep
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, d = k + 1 := ⟨d - 1, by omega⟩
  have hpos : ¬ Ring.KrullDimLE 0 (R ⧸ J') :=
    supPosDim_of_pin_succ k hpin
  obtain ⟨y, hsel, hT1⟩ :=
    supT1Data_of_quot_closedRep hInf htraceRep J' hpos hdep
  have hdrop : ringKrullDim (R ⧸ (J' ⊔ Ideal.span {y}))
      = ((((k : ℕ)) : ℕ∞) : WithBot ℕ∞) :=
    supExactDimDrop_of_regularMk J' y k hne hsel.1 hT1.1 hpin
  have hsub : k + 1 - 1 = k := Nat.add_sub_cancel k 1
  refine ⟨y, hsel, hT1, ?_⟩
  rw [hsub]
  exact hdrop

#print axioms supTowerExactGated_of_quotRep

/-- Alias for `supTowerExactGated_of_quotRep` under the design note's
`towerGatedRep` name.

Conditional on exactly `[SupT1TraceOfGrAvoidQuotRep]`
(+ infinite residue field). -/
theorem towerGatedRep {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R]
    (hInf : Infinite (R ⧸ IsLocalRing.maximalIdeal R))
    (htraceRep : SupT1TraceOfGrAvoidQuotRep (R := R)) :
    SupTowerExactGated (R := R) :=
  supTowerExactGated_of_quotRep hInf htraceRep

#print axioms towerGatedRep

/-! ## §5. Residual register (doc-only)

closed this lane: [the §7 kernel `SupT1OfGrAvoidQuotRep` modulo the
repaired trace], [the §7 T2 assembly re-fired on the repaired trace],
[T2-data (`supT1Data_phiClosedRep`, `supT1Data_of_quot_closedRep`)
from Rep-M1 + per-stage depth], [the depth-gated tower
(`supTowerExactGated_of_quotRep` / `towerGatedRep`) from Rep-M1].

open (exact, unchanged): [repaired M1
`SupT1TraceOfGrAvoidQuotRep` — owned by the TraceVV lane],
[per-stage `depth ≥ 1` for master-firing — CM induction along the
tower path, no CM API in tree; the ∀`J'` form is false in `dim ≥ 2`
(QuotAvoid §5 witness)].
-/

end RepFire
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
