/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.DimensionEquality.MinAtAssCloser
import Appendix_FixedPoint.BezoutChain.Regularity.DimensionEquality.MinAtAssClosure
import Appendix_FixedPoint.BezoutChain.Regularity.Assembly.Hres2InstanceAssembly
import Appendix_FixedPoint.BezoutChain.Regularity.CohenMacaulayLink.CMQuotientFull
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.SelectedPathDepth

/-!
# RB4-tower v2, T3: gated rework firing H5 + Close results at J₂

Re-targets the three `MinAtAssCloser` §3 results
(`hdimEqMinAtAss_j2`, `alloc_ge2_j2`, `hdimEq_rung2_binder_j2`) from the
false per-`(c, Q)` reshaped tower (`SupTowerPosDim` at `ht ≥ 2`, refuted by
the `J' = x·𝔪_Q` witness)
to the CM-conditional gated tower.

`C3aGapAll` is closed (`AssociatedPrimes.FiniteDimDischarge`) — `hC3a` binders
below are vestigial; downstream results need only `[FirstReg]`
(see discharge wrappers).

Firing vehicle (design note §(b), review §1): `hChiReduceAtAss_of_gatedDepth`
(`Hres2InstanceAssembly.lean`, pin + gated tower pre-assembled under
`[IsAlgClosed K]`), fed per-`Q` path depth from
`hdepth_stage_of_cm_residuals` (`SelectedPathDepth.lean`,
conditional-exact on `[FirstReg + C3aGapAll]`, already quantified over all
stage ideals so `j₂ := gapRung2 hn` is a plain instantiation). H4 is the
unconditional `hchiGrowthAtAss_close`; the closers are
`hdimEqMinAtAss_close_of_h4H5` / `alloc_ge2_close_of_h4H5`.

`uK`-diagonal (design note §(b)): the depth leg is `uK`-monomorphic, so this leaf
is stated at `universe uK` with `K : Type uK`. Conclusions
are the verbatim Target-A/C/B statements, now CM-conditional.

Scope: `RB4Cset`-gated only (no `∀c` claim); restricted identifiers
(`HdimEqMinAtAss`, `HdimEqMasterAlloc`) are proved here, never assumed. Never
touches the refuted `∀`-forms
(unguarded `[htower]`, route-(a), `SupTowerPosDim`, `∀J'` depth) or the
valid but inapplicable `repDepth`/`quotExact` vehicles.

Conditional on exactly `[FirstReg + C3aGapAll]` given `[IsAlgClosed K]`.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace TowerReworkFiring

universe uK

/-- H5 at `J₂(c)` per `c ∈ RB4Cset`: `HchiReduceAtAss` via the
`hChiReduceAtAss_of_gatedDepth` shortcut, whose sole per-`Q` input
(`SupPathDepthSel ⊥`) is discharged by `hdepth_stage_of_cm_residuals` at
`j₂ := gapRung2 hn`. The `RB4Cset` membership is scope-gating (no `∀c` claim); the depth leg
holds per instance regardless.

Conditional on exactly `[FirstReg + C3aGapAll]` given `[IsAlgClosed K]`. -/
theorem hchiReduceAtAss_j2_of_cm (K : Type uK) [Field K] [IsAlgClosed K]
    (hn : 0 < 3)
    (extra : Finset (Fin 3 → Fin 3 → Fin 3 → K))
    (hFR : CMQuotientFull.FirstReg.{uK, uK})
    (hC3a : CMQuotientFull.C3aGapAll.{uK})
    (c : Fin 3 → Fin 3 → Fin 3 → K)
    (_hc : c ∈ MinAtAssCloser.RB4Cset K extra) :
    ChiDegreeMaster.HchiReduceAtAss (statementIndex 3 + 2) K
      (MinAvoidRungs.stageIdeal 3 K c hn
        (MinAvoidInstances.gapRung2 hn)) := by
  apply Hres2InstanceAssembly.hChiReduceAtAss_of_gatedDepth
  intro Q _ hQ
  exact KoszulSupHdepthAssemble.hdepth_stage_of_cm_residuals K hFR hC3a 3 hn c
    (MinAvoidInstances.gapRung2 hn) Q hQ

#print axioms hchiReduceAtAss_j2_of_cm

/-- Target A re-targeted: `HdimEqMinAtAss` at `J₂(c)` per `c ∈ RB4Cset`,
firing `hdimEqMinAtAss_close_of_h4H5` with unconditional H4 and the gated
H5 above. Same verbatim conclusion as `hdimEqMinAtAss_j2`, CM-conditional.

Conditional on exactly `[FirstReg + C3aGapAll]` given `[IsAlgClosed K]`. -/
theorem hdimEqMinAtAss_j2_of_cm (K : Type uK) [Field K] [IsAlgClosed K]
    (hn : 0 < 3)
    (extra : Finset (Fin 3 → Fin 3 → Fin 3 → K))
    (hFR : CMQuotientFull.FirstReg.{uK, uK})
    (hC3a : CMQuotientFull.C3aGapAll.{uK})
    (c : Fin 3 → Fin 3 → Fin 3 → K)
    (hc : c ∈ MinAtAssCloser.RB4Cset K extra) :
    UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex 3 + 2) K
      (MinAvoidRungs.stageIdeal 3 K c hn
        (MinAvoidInstances.gapRung2 hn)) :=
  MinAtAssClosure.hdimEqMinAtAss_close_of_h4H5 _ K _
    (MinAtAssCloser.hchiGrowthAtAss_close _ K _)
    (hchiReduceAtAss_j2_of_cm K hn extra hFR hC3a c hc)

#print axioms hdimEqMinAtAss_j2_of_cm

/-- Target C re-targeted: the `fun d => 2 ≤ d` allocator spelling of
Target A, per `c ∈ RB4Cset` (via `alloc_ge2_close_of_h4H5`). Same verbatim
conclusion as `alloc_ge2_j2`, CM-conditional.

Conditional on exactly `[FirstReg + C3aGapAll]` given `[IsAlgClosed K]`. -/
theorem alloc_ge2_j2_of_cm (K : Type uK) [Field K] [IsAlgClosed K]
    (hn : 0 < 3)
    (extra : Finset (Fin 3 → Fin 3 → Fin 3 → K))
    (hFR : CMQuotientFull.FirstReg.{uK, uK})
    (hC3a : CMQuotientFull.C3aGapAll.{uK})
    (c : Fin 3 → Fin 3 → Fin 3 → K)
    (hc : c ∈ MinAtAssCloser.RB4Cset K extra) :
    SingleAllocator.HdimEqMasterAlloc (statementIndex 3 + 2) K
      (MinAvoidRungs.stageIdeal 3 K c hn
        (MinAvoidInstances.gapRung2 hn))
      (fun d => 2 ≤ d) :=
  MinAtAssClosure.alloc_ge2_close_of_h4H5 _ K _
    (MinAtAssCloser.hchiGrowthAtAss_close _ K _)
    (hchiReduceAtAss_j2_of_cm K hn extra hFR hC3a c hc)

#print axioms alloc_ge2_j2_of_cm

/-- Target B re-targeted (G1-gated): the single-rung λ-term discharging the
B1 binder at n=3, per `c ∈ RB4Cset`. Same `Fin.ext` / `j = gapRung2`
transport as `hdimEq_rung2_binder_j2`, closing on the re-targeted Target A.

Conditional on exactly `[FirstReg + C3aGapAll]` given `[IsAlgClosed K]`. -/
theorem hdimEq_rung2_binder_j2_of_cm (K : Type uK) [Field K] [IsAlgClosed K]
    (hn : 0 < 3)
    (extra : Finset (Fin 3 → Fin 3 → Fin 3 → K))
    (hFR : CMQuotientFull.FirstReg.{uK, uK})
    (hC3a : CMQuotientFull.C3aGapAll.{uK})
    (c : Fin 3 → Fin 3 → Fin 3 → K)
    (hc : c ∈ MinAtAssCloser.RB4Cset K extra)
    (j : Fin (statementIndex 3 + 1)) (hj : 2 ≤ j.val) :
    UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex 3 + 2) K
      (Ideal.span (Set.image (bridgeSystem 3 K c hn)
        {k | k.val < j.val})) := by
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
  exact hdimEqMinAtAss_j2_of_cm K hn extra hFR hC3a c hc

#print axioms hdimEq_rung2_binder_j2_of_cm

end TowerReworkFiring
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
