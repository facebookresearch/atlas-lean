/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoidRungs
import Appendix_FixedPoint.BezoutChain.Regularity.DimensionEquality.MinAtAssCloser
import Appendix_FixedPoint.BezoutChain.Regularity.DimensionEquality.SingleAllocator
import Appendix_FixedPoint.BezoutChain.Regularity.DimensionEquality.MinAtAssClosure
import Appendix_FixedPoint.BezoutChain.Regularity.DimensionEquality.K2SliceClose
import Appendix_FixedPoint.BezoutChain.Regularity.CohenMacaulayLink.CMQuotientFull
import Appendix_FixedPoint.AssociatedPrimes.FiniteDimDischarge
import Appendix_FixedPoint.BezoutChain.Regularity.CohenMacaulayLink.GradeKeepsMaximalOutOfAss
/-!
# (M-halloc): general-n `HdimEqMasterAlloc`, CM-conditional, all stages

One theorem,
`halloc_all_stages_of_cm`: the verbatim consumer `halloc` binder shape
(`∀ j`, `2 ≤ j.val` guard, `statementIndex n + 2` / `stageIdeal` / régime
`(fun d => 2 ≤ d)`, token-identical to the E10 / M2 / NonprimeClose plugs)
at general `n`, concluded from `[FirstReg + C3aGapAll] + [Infinite K]`.

`C3aGapAll` is closed (`AssociatedPrimes.FiniteDimDischarge`) — `hC3a` binders
below are vestigial; downstream results need only `[FirstReg]`
(see discharge wrappers).

Firing (verbatim T3 precedent `alloc_ge2_j2_of_cm`, H5 swapped from the
J₂-scoped producer to the general-J C1B-H5): the closer
`alloc_ge2_close_of_h4H5` with the unconditional H4
`hchiGrowthAtAss_close` and the gated H5
`hChiReduceAtAss_gated_of_cm`. Both H4 and H5 are general-J, so the
`∀ j` threading is one `intro` and every rung fires uniformly — no
`Fin.ext`, no transport, no `hc`/`extra` plumbing.

Alg-closed status: no `[IsAlgClosed K]` hypothesis — this lane needs no
alg-closed content (unlike T3, whose depth vehicle is `IsAlgClosed`-gated).
Gating is exactly `[Infinite K]` (C1B-H5's instance); consumers already
carrying `[IsAlgClosed K]` supply it by instance.

This result takes `[FirstReg + C3aGapAll]` as hypotheses. It establishes
halloc conditional-exact on `[FirstReg + C3aGapAll]` + `[Infinite K]`;
nothing is grounded, and no unconditional progress is claimed.

Conditional on exactly `[FirstReg.{u,u} + C3aGapAll.{u}]` given
`[Infinite K]`.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace MasterAllocator

universe u

/-- M-halloc: the verbatim consumer `halloc` binder at general `n`, fired
from `[FirstReg + C3aGapAll] + [Infinite K]` via the H4+H5 closer.
Takes `[FirstReg + C3aGapAll]` as hypotheses; proves halloc
conditional-exact, grounds nothing.

Conditional on exactly `[FirstReg.{u,u} + C3aGapAll.{u}]` given
`[Infinite K]`. -/
theorem halloc_all_stages_of_cm (n : ℕ) (K : Type u) [Field K] [Infinite K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (hFR : CMQuotientFull.FirstReg.{u, u})
    (hC3a : CMQuotientFull.C3aGapAll.{u}) :
    ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex n + 2) K
        (MinAvoidRungs.stageIdeal n K c hn j) (fun d => 2 ≤ d) := by
  intro j _
  exact MinAtAssClosure.alloc_ge2_close_of_h4H5 _ K _
    (MinAtAssCloser.hchiGrowthAtAss_close _ K _)
    (K2SliceClose.hChiReduceAtAss_gated_of_cm _ K _ hFR hC3a)

#print axioms halloc_all_stages_of_cm

end MasterAllocator
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

/-!
# Halloc C3a discharge: `halloc_all_stages_of_fr`


## Main result

* `halloc_all_stages_of_fr`: the M-halloc fact
  (`MasterAllocator.halloc_all_stages_of_cm`) with the `hC3a`
  hypothesis discharged via the proved
  `AssociatedPrimes.FiniteDimDischarge.c3aGapAll_of_gapBaseFin` (universe `u`),
  collapsing the hypothesis set to `[FirstReg.{u,u}]`-only. Conclusion
  restated verbatim. The wrapper-level `[Infinite K]` gate is preserved
  as-is (`Infinite-stated (preserved gate)` — head doc confirms gating is
  exactly `[Infinite K]`, TC leg not applicable).

No `[IsAlgClosed]` hypothesis is assumed or needed anywhere in this
file (`[algClosed]`-ambient applies only where consumers need it).
`hC3a` appears only as the discharged argument position, never assumed.

Import closure: proved `MasterAllocator`, `AssociatedPrimes.FiniteDimDischarge` +
mathlib only.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace KoszulHdimEqHallocMidiC3aDischarge

universe u

/-- M-halloc C3a discharge: `halloc_all_stages_of_cm` on
`[FirstReg.{u,u}]`-only given the stated `[Infinite K]` gate, `hC3a`
discharged via `c3aGapAll_of_gapBaseFin.{u}`.

Hypothesis-set collapse only; the conclusion is restated verbatim. -/
theorem halloc_all_stages_of_fr (n : ℕ) (K : Type u) [Field K] [Infinite K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (hFR : CMQuotientFull.FirstReg.{u, u}) :
    ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex n + 2) K
        (MinAvoidRungs.stageIdeal n K c hn j) (fun d => 2 ≤ d) := by
  exact MasterAllocator.halloc_all_stages_of_cm n K c hn hFR
    AssociatedPrimes.FiniteDimDischarge.c3aGapAll_of_gapBaseFin.{u}

#print axioms halloc_all_stages_of_fr

end KoszulHdimEqHallocMidiC3aDischarge
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

/-!
# halloc FirstReg firing (B2)

The `FirstReg` apex is closed
(`FirstRegAssemble.firstReg_unconditional`, unconditional
`CMQuotientFull.FirstReg`), and `C3aGapAll` was already closed
(`AssociatedPrimes.FiniteDimDischarge.c3aGapAll_of_gapBaseFin`). This leaf fires the
whole B2 halloc chain end to end:

* `hChiReduceAtAss_unconditional`: the H5 SPEC fired from the
  C1-gated producer (`hChiReduceAtAss_gated_of_cm`) with both
  hypotheses discharged.
* `alloc_ge2_close_unconditional`: the MinAssClose H4+H5 closer
  (`alloc_ge2_close_of_h4H5`) with the unconditional H4
  (`hchiGrowthAtAss_close`) and the fired H5.
* `halloc_all_stages_unconditional`: the verbatim consumer `halloc`
  binder at general `n` (via the `[FirstReg]`-only wrapper
  `halloc_all_stages_of_fr`).

Status: each conclusion is hypothesis-free given the stated
`[Infinite K]` gate (C1B-H5's instance, threaded through the gated
producer; consumers already carrying `[IsAlgClosed K]` supply it by
typeclass). This grounds the hdimEq/halloc/hdepth chain: B1's
`hdimEqMaster_*_of_alloc` now fires unconditionally (modulo
`[Infinite K]`).

-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace KoszulHdimEqHallocFirstRegFire

universe u

/-- H5 SPEC unconditional: the C1-gated H5 producer with `hFR`
discharged by `firstReg_unconditional.{u,u}` and `hC3a` by
`c3aGapAll_of_gapBaseFin.{u}`.

Hypothesis-free given `[Field K] + [Infinite K]`. -/
theorem hChiReduceAtAss_unconditional (m : ℕ) (K : Type u) [Field K] [Infinite K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    ChiDegreeMaster.HchiReduceAtAss m K J :=
  K2SliceClose.hChiReduceAtAss_gated_of_cm m K J
    FirstRegAssemble.firstReg_unconditional.{u, u}
    AssociatedPrimes.FiniteDimDischarge.c3aGapAll_of_gapBaseFin.{u}

#print axioms hChiReduceAtAss_unconditional

/-- MinAssClose H4+H5 closer fired: unconditional H4 plus the fired H5
through `alloc_ge2_close_of_h4H5`.

Hypothesis-free given `[Field K] + [Infinite K]`. -/
theorem alloc_ge2_close_unconditional (m : ℕ) (K : Type u) [Field K] [Infinite K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    SingleAllocator.HdimEqMasterAlloc m K J (fun d => 2 ≤ d) :=
  MinAtAssClosure.alloc_ge2_close_of_h4H5 m K J
    (MinAtAssCloser.hchiGrowthAtAss_close m K J)
    (hChiReduceAtAss_unconditional m K J)

#print axioms alloc_ge2_close_unconditional

/-- M-halloc fired: the verbatim consumer `halloc` binder at general
`n` with `hFR` discharged by `firstReg_unconditional.{u,u}`.

Hypothesis-free given `[Field K] + [Infinite K]`. -/
theorem halloc_all_stages_unconditional (n : ℕ) (K : Type u) [Field K] [Infinite K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n) :
    ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex n + 2) K
        (MinAvoidRungs.stageIdeal n K c hn j) (fun d => 2 ≤ d) :=
  KoszulHdimEqHallocMidiC3aDischarge.halloc_all_stages_of_fr n K c hn
    FirstRegAssemble.firstReg_unconditional.{u, u}

#print axioms halloc_all_stages_unconditional

end KoszulHdimEqHallocFirstRegFire
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
