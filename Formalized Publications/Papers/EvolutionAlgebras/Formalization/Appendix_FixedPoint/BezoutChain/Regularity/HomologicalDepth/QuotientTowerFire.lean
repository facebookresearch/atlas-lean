/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.ChiDegreeMaster
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.SuperficialReduction
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.ColonTransfer
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.PositiveDimTower
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.ColonDimDrop
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.QuotientKernelAvoidance
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.JointRefinement
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedQuotientComparison

/-!
# Quotient-side tower fire: `SupTowerExact` from M1 + per-stage depth (T4)

T1-chain continuation: mirrors `supTowerExact_of_graded`
(ColonDimDrop:511) with the quotient-side kernels. The graded-avoidance
inputs `[SupAssFiniteGr, SupJointHomAvoid, SupT1OfGrAvoid]` are replaced by
the repaired quotient chain:

* T2-data from `supT1Data_of_quotAvoid_repaired_narrow` (QuotAvoid:762),
  with R0-quot + R1 already discharged inside;
* M2 `SupJointUnhgradedRefine` closed by
  `supJointUnhgradedRefine_of_noetherian` (JointRefine:126);
* `φ` data closed by `grQuotComp` / `grQuotComp_compat` / `grQuotComp_irr`
  (GrQuotComp:301/:324/:345), whose binder shapes match the narrow
  assembly `:677-687` verbatim;
* the exact drop from T1 regularity via the catenary-free
  `supExactDimDrop_of_regularMk` (ColonDimDrop:327), unchanged.

## What this file proves

* (§1) `supT1Data_of_quot_closed`: T2-data (`∃ y, Select ∧ T1`) from
  M1 + depth, with M2 + `φ` discharged. Unconditional from explicit
  M1 + depth.
* (§2) `supTowerExact_of_quot`: verbatim `SupTowerExact`
  (ColonTransfer:278), mirroring `supTowerExact_of_graded`
  (ColonDimDrop:511) step for step. Conditional-exact on
  `[SupT1TraceOfGrAvoidQuot, per-stage depth]`.
* (§3) `supTowerExactGated_of_quot`: the depth-gated reshape
  (`SupTowerExactGated`, canonical address ColonTransfer §3 — depth
  as a per-firing premise instead of a global hypothesis), closed
  from M1 alone. This is the reshape alternative of QuotAvoid
  :812-817; the matching gated masters
  (`sup_chi_exactDim_growth_gated`,
  `sup_tower_nonvanishing_exact_gated`,
  `hChiReduceAtAss_of_gatedTowers`) live in ColonTransfer §3.
* (§4) `hChiReduceAtAss_of_quotExact`: verbatim `HchiReduceAtAss`
  (ChiDegree:153) from per-`Q` quotient inputs, mirroring
  `hChiReduceAtAss_of_gradedExact` (ColonDimDrop:560).
* (§5) Residual register (doc-only).

## Status

unconditional (from explicit data where noted):
`supT1Data_of_quot_closed`, `supTowerExactGated_of_quot`.
conditional-exact on `[SupT1TraceOfGrAvoidQuot, per-stage depth]`:
`supTowerExact_of_quot`, `hChiReduceAtAss_of_quotExact`.
conditional-exact on `[SupT1TraceOfGrAvoidQuot]`:
`supTowerExactGated_of_quot`.

## Residual register (verbatim)

open (exact) after this lane:

* M1 `SupT1TraceOfGrAvoidQuot` (QuotAvoid:566): the order-one trace
  from quotient-side graded avoidance. True classically; price
  ~150–250 lines of initial-form calculus over `associatedGraded`
  (no such API in tree).
* Per-stage `depth ≥ 1` (`𝔪 ∉ Ass(R ⧸ J')` at each tower ideal):
  holds along the actual tower path (CM induction from `⊥` over a
  domain) but needs CM API absent from Mathlib and the project;
  alternatively re-shape `SupTowerExact` (ColonTransfer:278) to
  carry depth — the reshaped statement + gated masters live in
  ColonTransfer §3 (`SupTowerExactGated`, `SupPathDepth`, the three
  gated masters). Note the ∀`J'` depth form (hence the ∀`J'` tower)
  is false in `dim ≥ 2` (QuotAvoid §5 witness), so the masters
  cannot fire on the ungated form as stated.

## References

Project (read-only): `ColonDimDrop.lean`
(`supTowerExact_of_graded`:511, `supExactDimDrop_of_regularMk`:327,
`hChiReduceAtAss_of_gradedExact`:560),
`QuotientKernelAvoidance.lean`
(`supT1Data_of_quotAvoid_repaired_narrow`:762,
`SupT1TraceOfGrAvoidQuot`:566, §8:791-817),
`JointRefinement.lean`
(`supJointUnhgradedRefine_of_noetherian`:126),
`GradedQuotientComparison.lean` (`grQuotComp`:301, `grQuotComp_compat`:324,
`grQuotComp_irr`:345), `ColonTransfer.lean`
(`SupTowerExact`:278, `hChiReduceAtAss_of_exactTowers`:434,
`SupTowerExactGated` + gated masters §3),
`PositiveDimTower.lean` (`supPosDim_of_pin_succ`:391),
`ChiDegreeMaster.lean` (`HchiReduceAtAss`:153).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace QuotientTowerFire

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.ChiDegreeMaster
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.SuperficialReduction
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.ColonTransfer
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.PositiveDimTower
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.ColonDimDrop
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.QuotientKernelAvoidance
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.JointRefinement
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedQuotientComparison

/-! ## §1. T2-data from M1 + depth (M2 + `φ` discharged) -/

/-- T2-data existence (`∃ y, SupSelectData ∧ SupT1Data`) from the
quotient trace residual M1 plus per-`J'` depth: the narrow assembly
`supT1Data_of_quotAvoid_repaired_narrow` (R0-quot + R1 already
discharged inside) with M2 closed by
`supJointUnhgradedRefine_of_noetherian` and `φ` closed by
`grQuotComp` / `grQuotComp_compat` / `grQuotComp_irr` (verbatim
binder shapes). The depth hypothesis is load-bearing (QuotAvoid §5).
-/
theorem supT1Data_of_quot_closed {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R]
    (hInf : Infinite (R ⧸ IsLocalRing.maximalIdeal R))
    (htraceQ : SupT1TraceOfGrAvoidQuot (R := R))
    (J' : Ideal R)
    (hpos : ¬ Ring.KrullDimLE 0 (R ⧸ J'))
    (hdepth : IsLocalRing.maximalIdeal R ∉ associatedPrimes R (R ⧸ J')) :
    ∃ y : R, SupSelectData J' y ∧ SupT1Data J' y :=
  supT1Data_of_quotAvoid_repaired_narrow (R := R) hInf htraceQ
    (supJointUnhgradedRefine_of_noetherian hInf)
    J' hpos hdepth (grQuotComp J')
    (fun y h1 h2 => grQuotComp_compat J' y h1 h2)
    (fun Q hQmem hQirr => grQuotComp_irr J' Q hQmem hQirr)

#print axioms supT1Data_of_quot_closed

/-! ## §2. Verbatim `SupTowerExact` from M1 + per-stage depth -/

/-- Verbatim `SupTowerExact` (SupColonTransfer:278) from quotient
inputs: at each exact pin `d ≥ 1` write `d = k + 1`, get positivity
from the pin, get `y` with selection + T1 data from
`supT1Data_of_quot_closed` (M1 + depth at that `J'`), and get the
exact drop from T1 regularity (`supExactDimDrop_of_regularMk`,
catenary-free). Step-for-step mirror of `supTowerExact_of_graded`
(ColonDimDrop:511); this is the input the T2 master
`hChiReduceAtAss_of_exactTowers` fires on.

Conditional on exactly
`[SupT1TraceOfGrAvoidQuot, per-stage depth]` (+ infinite residue
field). The ∀`J'` depth hypothesis is false in `dim ≥ 2`
(QuotAvoid §5) — see §3 for the gated reshape and §5 for the CM
path. -/
theorem supTowerExact_of_quot {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R]
    (hInf : Infinite (R ⧸ IsLocalRing.maximalIdeal R))
    (htraceQ : SupT1TraceOfGrAvoidQuot (R := R))
    (hdepth : ∀ J' : Ideal R, ¬ Ring.KrullDimLE 0 (R ⧸ J') →
      IsLocalRing.maximalIdeal R ∉ associatedPrimes R (R ⧸ J')) :
    SupTowerExact (R := R) := by
  intro J' d hne hd hpin
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, d = k + 1 := ⟨d - 1, by omega⟩
  have hpos : ¬ Ring.KrullDimLE 0 (R ⧸ J') :=
    supPosDim_of_pin_succ k hpin
  obtain ⟨y, hsel, hT1⟩ :=
    supT1Data_of_quot_closed hInf htraceQ J' hpos (hdepth J' hpos)
  have hdrop : ringKrullDim (R ⧸ (J' ⊔ Ideal.span {y}))
      = ((((k : ℕ)) : ℕ∞) : WithBot ℕ∞) :=
    supExactDimDrop_of_regularMk J' y k hne hsel.1 hT1.1 hpin
  have hsub : k + 1 - 1 = k := Nat.add_sub_cancel k 1
  refine ⟨y, hsel, hT1, ?_⟩
  rw [hsub]
  exact hdrop

#print axioms supTowerExact_of_quot

/-! ## §3. Depth-gated reshape (M1 only)

note (unification): the canonical `SupTowerExactGated` lives in
`ColonTransfer` §3 (imported + opened above), so the T1 chain
and the T2 gated masters share one address (a second copy here would
make downstream `open`s ambiguous and break RepFire elaboration).
The firing theorem below targets the imported statement; its proof is
unchanged.
-/

/-- The depth-gated tower from M1 alone: same body as
`supTowerExact_of_quot` (§2), with the per-firing depth premise
fed directly to `supT1Data_of_quot_closed`.

Conditional on exactly `[SupT1TraceOfGrAvoidQuot]`
(+ infinite residue field). -/
theorem supTowerExactGated_of_quot {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R]
    (hInf : Infinite (R ⧸ IsLocalRing.maximalIdeal R))
    (htraceQ : SupT1TraceOfGrAvoidQuot (R := R)) :
    SupTowerExactGated (R := R) := by
  intro J' d hne hd hpin hdep
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, d = k + 1 := ⟨d - 1, by omega⟩
  have hpos : ¬ Ring.KrullDimLE 0 (R ⧸ J') :=
    supPosDim_of_pin_succ k hpin
  obtain ⟨y, hsel, hT1⟩ :=
    supT1Data_of_quot_closed hInf htraceQ J' hpos hdep
  have hdrop : ringKrullDim (R ⧸ (J' ⊔ Ideal.span {y}))
      = ((((k : ℕ)) : ℕ∞) : WithBot ℕ∞) :=
    supExactDimDrop_of_regularMk J' y k hne hsel.1 hT1.1 hpin
  have hsub : k + 1 - 1 = k := Nat.add_sub_cancel k 1
  refine ⟨y, hsel, hT1, ?_⟩
  rw [hsub]
  exact hdrop

#print axioms supTowerExactGated_of_quot

/-! ## §4. Per-`Q` master plug -/

/-- T2-side plug: verbatim `HchiReduceAtAss` (ChiDegree:153) from
per-`Q` quotient inputs, firing `hChiReduceAtAss_of_exactTowers`
with the `supTowerExact_of_quot` (§2) assembly. No catenary
anywhere: the exact drop at each step goes through T1 regularity.
Mirror of `hChiReduceAtAss_of_gradedExact` (ColonDimDrop:560).

Conditional on exactly per-`Q` `[Infinite residue,
SupT1TraceOfGrAvoidQuot, per-stage depth]` (+ per-`Q` dimension
pin). -/
theorem hChiReduceAtAss_of_quotExact (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hquot : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) →
      Infinite (Localization.AtPrime Q
          ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime Q)) ∧
        SupT1TraceOfGrAvoidQuot (R := Localization.AtPrime Q) ∧
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
  obtain ⟨hInf, htraceQ, hdepth, dimN, hpin⟩ := hquot Q hQ
  exact ⟨dimN, hpin, supTowerExact_of_quot hInf htraceQ hdepth⟩

#print axioms hChiReduceAtAss_of_quotExact

/-! ## §5. Residual register (doc-only)

open (exact) after this lane:

* M1 `SupT1TraceOfGrAvoidQuot` (QuotAvoid:566): the order-one trace
  from quotient-side graded avoidance. True classically; price
  ~150–250 lines of initial-form calculus over `associatedGraded`
  (products of initial forms, `(0 : y*)`-torsion killed by
  irrelevant powers) — no such API in tree.
* Per-stage `depth ≥ 1` for master-firing: holds along the actual
  tower path (CM induction from `⊥` over a domain) but needs CM API
  absent from Mathlib and the project; alternatively re-shape
  `SupTowerExact` (ColonTransfer:278) to carry depth — the
  reshaped statement + gated masters live in ColonTransfer §3
  (`SupTowerExactGated`, `SupPathDepth`, the three gated masters).
  Note the ∀`J'` form is false in `dim ≥ 2` (QuotAvoid §5 witness),
  so the masters cannot fire on the ungated form as stated.

closed this lane: [T2-data from M1 + depth with M2 + `φ`
discharged], [verbatim `SupTowerExact` modulo M1 + per-stage
depth], [depth-gated reshape modulo M1], [per-`Q`
`HchiReduceAtAss` plug modulo the per-`Q` list].
-/

end QuotientTowerFire
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
