/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.ChiDegreeMaster
import Appendix_FixedPoint.BezoutChain.Regularity.DimensionEquality.ChiReduceSubstitution
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.InfiniteResidueFields
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.RepFire
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.OrderOneTrace

/-!
# TraceVV → RepFire bridge: the repaired M1 SPEC discharged (T1-repbridge)

Prior design notes (campaign `chain.md`/`fit.md`, not in repo) record:
`OrderOneTrace.lean` `supT1Trace_of_quotAvoid_repaired` proves the
Rep SPEC, `RepFire.lean` `SupT1TraceOfGrAvoidQuotRep`
duplicates that SPEC verbatim, and zero in-tree consumers touch either
side. This file plugs the gap:

* `repTrace_of_traceVV`: the RepFire SPEC from the TraceVV proof, by
  defeq (`exact`, bodies binder-identical). This unifies the
  TraceVV duplicate with the RepFire address: there is one
  Rep SPEC (the RepFire statement) and it is now proved.
* Six re-exports of the RepFire T1 chain
  with the SPEC discharged,
  i.e. with `htraceRep := repTrace_of_traceVV`.
* The Rep master plug: `supTowerExact_of_repGated` (ungate the
  discharged tower with per-stage depth),
  `hChiReduceAtAss_of_repGated` (verbatim `HchiReduceAtAss` from
  per-`Q` residue + depth + pin, via `hChiReduceAtAss_of_exactTowers`),
  `hChiReduceAtAss_of_repDepth` (+ `_algClosed`) with residues and
  pins discharged unconditionally. No kernel anywhere on this
  route.

## Status

unconditional (given `IsNoetherianRing R` + the stated per-stage data):
the bridge and the six re-exports. The Rep SPEC
`SupT1TraceOfGrAvoidQuotRep` (RepFire, = TraceVV by
defeq) is closed by `repTrace_of_traceVV`.
conditional-exact on per-`Q` per-stage depth (+ `Infinite K` ambient):
the Rep master plug (`hChiReduceAtAss_of_repDepth`).

## References

* `Regularity/HomologicalDepth/OrderOneTrace.lean` (`SupT1TraceOfGrAvoidQuotRep`
  :662, `supT1Trace_of_quotAvoid_repaired`:689).
* `Regularity/HomologicalDepth/RepFire.lean` (`SupT1TraceOfGrAvoidQuotRep`
  :114, `supT1QuotRep_of_traceRep`:140,
  `supT1Data_of_quotAvoid_repairedRep`:160,
  `supT1Data_of_quotAvoid_repaired_narrowRep`:260,
  `supT1Data_phiClosedRep`:295, `supT1Data_of_quot_closedRep`:315,
  `supTowerExactGated_of_quotRep`:339).
* `Regularity/HomologicalDepth/ColonTransfer.lean`
  (`hChiReduceAtAss_of_exactTowers`:434).
* `Regularity/HomologicalDepth/InfiniteResidueFields.lean`
  (`atPrime_residue_infinite_atAss`:114).
* `Regularity/DimensionEquality/ChiReduceSubstitution.lean`
  (`dimPin_atAss_unconditional`:107).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace TraceRepBridge

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.ChiDegreeMaster
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AssociatedGradedRing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.ChiReduceSubstitution
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.SuperficialReduction
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.InfiniteResidueFields
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.ColonTransfer
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.PositiveDimTower
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.ColonDimDrop
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.JointAvoidance
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.QuotientKernelAvoidance
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.JointRefinement
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedQuotientComparison
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.QuotientTowerFire
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.RepFire

/-! ## The bridge: Rep SPEC proved by the TraceVV theorem -/

/-- The RepFire Rep SPEC (`SupT1TraceOfGrAvoidQuotRep`, RepFire:114)
from the TraceVV proof (`supT1Trace_of_quotAvoid_repaired`, TraceVV
:689), by defeq: the two SPEC statements (RepFire:114-129, TraceVV
:662-677) are binder-identical, so `exact` closes the goal by
unfolding both defs to the same `∀`-statement. This unifies the
TraceVV duplicate onto the RepFire address.
-/
theorem repTrace_of_traceVV {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] :
    RepFire.SupT1TraceOfGrAvoidQuotRep (R := R) :=
  OrderOneTrace.supT1Trace_of_quotAvoid_repaired

#print axioms repTrace_of_traceVV

/-! ## Re-exports: the RepFire T1 chain on the discharged SPEC -/

/-- The fully repaired kernel (`SupT1OfGrAvoidQuotRep`) from the
discharged Rep SPEC: RepFire re-fired with
`htraceRep := repTrace_of_traceVV`.
-/
theorem supT1QuotRep_of_traceVV {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] :
    SupT1OfGrAvoidQuotRep (R := R) :=
  -- Qualified: `supT1QuotRep_of_traceRep` is also declared in TraceVV (:797)
  -- with a defeq body; this re-export is exactly the RepFire one.
  RepFire.supT1QuotRep_of_traceRep repTrace_of_traceVV

#print axioms supT1QuotRep_of_traceVV

/-- T2-data existence from R0-quot + R1 + M2 + `φ` data + depth, Rep
SPEC discharged: RepFire re-fired with
`htraceRep := repTrace_of_traceVV`.

depth). -/
theorem supT1Data_of_quotAvoid_repaired_of_traceVV {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R]
    (hInf : Infinite (R ⧸ IsLocalRing.maximalIdeal R))
    (hfinQ : SupAssFiniteGrQuot (R := R))
    (havoid : SupJointHomAvoid (R := R))
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
  supT1Data_of_quotAvoid_repairedRep (R := R) hInf hfinQ havoid
    repTrace_of_traceVV hrefine J' hpos hdepth φ hcompat hirr

#print axioms supT1Data_of_quotAvoid_repaired_of_traceVV

/-- The assembly with R0-quot and R1 discharged, Rep SPEC
discharged: RepFire re-fired with
`htraceRep := repTrace_of_traceVV`.

Conditional on exactly `[SupJointUnhgradedRefine]`
(+ `φ` data + depth). -/
theorem supT1Data_of_quotAvoid_repaired_narrow_of_traceVV {R : Type*}
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hInf : Infinite (R ⧸ IsLocalRing.maximalIdeal R))
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
  supT1Data_of_quotAvoid_repaired_narrowRep (R := R) hInf
    repTrace_of_traceVV hrefine J' hpos hdepth φ hcompat hirr

#print axioms supT1Data_of_quotAvoid_repaired_narrow_of_traceVV

/-- T2-data from per-stage hypotheses only, Rep SPEC discharged:
RepFire re-fired with `htraceRep := repTrace_of_traceVV`.
-/
theorem supT1Data_phiClosed_of_traceVV {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R]
    (hInf : Infinite (R ⧸ IsLocalRing.maximalIdeal R))
    (J' : Ideal R)
    (hpos : ¬ Ring.KrullDimLE 0 (R ⧸ J'))
    (hdepth : IsLocalRing.maximalIdeal R
      ∉ associatedPrimes R (R ⧸ J')) :
    ∃ y : R, SupSelectData J' y ∧ SupT1Data J' y :=
  supT1Data_phiClosedRep (R := R) hInf repTrace_of_traceVV J' hpos hdepth

#print axioms supT1Data_phiClosed_of_traceVV

/-- T2-data from per-stage depth, Rep SPEC discharged: RepFire
re-fired with `htraceRep := repTrace_of_traceVV`.
-/
theorem supT1Data_of_quot_closed_of_traceVV {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R]
    (hInf : Infinite (R ⧸ IsLocalRing.maximalIdeal R))
    (J' : Ideal R)
    (hpos : ¬ Ring.KrullDimLE 0 (R ⧸ J'))
    (hdepth : IsLocalRing.maximalIdeal R ∉ associatedPrimes R (R ⧸ J')) :
    ∃ y : R, SupSelectData J' y ∧ SupT1Data J' y :=
  supT1Data_of_quot_closedRep (R := R) hInf repTrace_of_traceVV J' hpos hdepth

#print axioms supT1Data_of_quot_closed_of_traceVV

/-- The depth-gated tower (`SupTowerExactGated`) from the discharged
Rep SPEC alone: RepFire re-fired with
`htraceRep := repTrace_of_traceVV`.

field). -/
theorem supTowerExactGated_of_quot_of_traceVV {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R]
    (hInf : Infinite (R ⧸ IsLocalRing.maximalIdeal R)) :
    SupTowerExactGated (R := R) :=
  supTowerExactGated_of_quotRep hInf repTrace_of_traceVV

#print axioms supTowerExactGated_of_quot_of_traceVV

/-! ## The Rep master plug: `HchiReduceAtAss` from the discharged Rep tower -/

/-- Ungate: the depth-gated tower (`SupTowerExactGated`, ColonTransfer
:476) plus per-stage depth gives verbatim `SupTowerExact`
(ColonTransfer:278). Positivity comes from the exact pin
(`supPosDim_of_pin_succ`); the gated tower then fires directly. This
is the gated-master re-plumbing in its minimal form: no
kernel, no M1 hypothesis (the Rep M1 is closed by
`repTrace_of_traceVV`).
-/
theorem supTowerExact_of_repGated {R : Type*} [CommRing R] [IsLocalRing R]
    (hgated : SupTowerExactGated (R := R))
    (hdepth : ∀ J' : Ideal R, ¬ Ring.KrullDimLE 0 (R ⧸ J') →
      IsLocalRing.maximalIdeal R ∉ associatedPrimes R (R ⧸ J')) :
    SupTowerExact (R := R) := by
  intro J' d hne hd hpin
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, d = k + 1 := ⟨d - 1, by omega⟩
  have hpos : ¬ Ring.KrullDimLE 0 (R ⧸ J') :=
    supPosDim_of_pin_succ k hpin
  exact hgated J' (k + 1) hne hd hpin (hdepth J' hpos)

#print axioms supTowerExact_of_repGated

/-- T2-side plug: verbatim `HchiReduceAtAss` (ChiDegree:153) from
per-`Q` Rep inputs, firing `hChiReduceAtAss_of_exactTowers` (ColonTransfer
:434) with the discharged Rep tower
(`supTowerExactGated_of_quot_of_traceVV`) ungated by
`supTowerExact_of_repGated`. Mirror of `hChiReduceAtAss_of_quotExact`
(QuotTowerFire:242) with the M1 conjunct gone (closed by the bridge).
No catenary anywhere: the exact drop at each step goes through T1
regularity.

Conditional on exactly per-`Q` `[Infinite residue, per-stage
depth]` (+ per-`Q` dimension pin). -/
theorem hChiReduceAtAss_of_repGated (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hrep : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) →
      Infinite (Localization.AtPrime Q
          ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime Q)) ∧
        (∀ J' : Ideal (Localization.AtPrime Q),
          ¬ Ring.KrullDimLE 0 (Localization.AtPrime Q ⧸ J') →
          IsLocalRing.maximalIdeal (Localization.AtPrime Q)
            ∉ associatedPrimes (Localization.AtPrime Q)
              (Localization.AtPrime Q ⧸ J')) ∧
        ∃ dimN : ℕ, ringKrullDim (Localization.AtPrime Q)
          = ((dimN : ℕ∞) : WithBot ℕ∞)) :
    HchiReduceAtAss m K J := by
  apply hChiReduceAtAss_of_exactTowers
  intro Q _ hQ
  obtain ⟨hInf, hdepth, dimN, hpin⟩ := hrep Q hQ
  exact ⟨dimN, hpin, supTowerExact_of_repGated
    (supTowerExactGated_of_quot_of_traceVV hInf) hdepth⟩

#print axioms hChiReduceAtAss_of_repGated

/-- Verbatim `HchiReduceAtAss` on exactly `[per-Q per-stage depth]`
(given ambient `Infinite K`): fires `hChiReduceAtAss_of_repGated`
with infinite residues from `atPrime_residue_infinite_atAss`
(PerQResidue:114) and pins from `dimPin_atAss_unconditional`
(H5H6Subst:107), both unconditional. Mirror of
`hChiReduceAtAss_of_t1Kernel` (H5H6Subst:125) with the
kernel gone.

Conditional on exactly `[per-Q per-stage depth]`. -/
theorem hChiReduceAtAss_of_repDepth (m : ℕ) (K : Type*) [Field K]
    [Infinite K] (J : Ideal (MvPolynomial (Fin m) K))
    (hdepth : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) →
      ∀ J' : Ideal (Localization.AtPrime Q),
        ¬ Ring.KrullDimLE 0 (Localization.AtPrime Q ⧸ J') →
        IsLocalRing.maximalIdeal (Localization.AtPrime Q)
          ∉ associatedPrimes (Localization.AtPrime Q)
            (Localization.AtPrime Q ⧸ J')) :
    HchiReduceAtAss m K J := by
  apply hChiReduceAtAss_of_repGated
  intro Q _ hQ
  exact ⟨atPrime_residue_infinite_atAss m K J Q hQ, hdepth Q hQ,
    dimPin_atAss_unconditional m K J Q hQ⟩

#print axioms hChiReduceAtAss_of_repDepth

/-- The Rep master plug under the formalization hypothesis: `IsAlgClosed K`
supplies `Infinite K` (Mathlib instance).

Conditional on exactly `[per-Q per-stage depth]`. -/
theorem hChiReduceAtAss_of_repDepth_algClosed (m : ℕ) (K : Type*)
    [Field K] [IsAlgClosed K] (J : Ideal (MvPolynomial (Fin m) K))
    (hdepth : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) →
      ∀ J' : Ideal (Localization.AtPrime Q),
        ¬ Ring.KrullDimLE 0 (Localization.AtPrime Q ⧸ J') →
        IsLocalRing.maximalIdeal (Localization.AtPrime Q)
          ∉ associatedPrimes (Localization.AtPrime Q)
            (Localization.AtPrime Q ⧸ J')) :
    HchiReduceAtAss m K J :=
  hChiReduceAtAss_of_repDepth m K J hdepth

#print axioms hChiReduceAtAss_of_repDepth_algClosed

/-! ## Residual register (doc-only)

closed this lane: [the TraceVV→RepFire plug (chain design note):
`repTrace_of_traceVV` proves the RepFire SPEC from TraceVV
unifying the TraceVV duplicate], [the full RepFire T1
chain re-exported on the
discharged SPEC], [the Rep master plug: `supTowerExact_of_repGated` +
`hChiReduceAtAss_of_repGated` / `hChiReduceAtAss_of_repDepth` (+
`_algClosed`) land verbatim `HchiReduceAtAss` from the discharged Rep
tower + per-stage depth; no kernel].

open (exact, unchanged): [per-stage `depth ≥ 1` for master-firing —
CM induction along the tower path, no CM API in tree; the ∀`J'` form
is false in `dim ≥ 2` (QuotAvoid §5 witness)].
-/

end TraceRepBridge
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
