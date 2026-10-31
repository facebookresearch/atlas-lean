/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Geometry.UnmixednessAtLengthTwo
import Appendix_FixedPoint.BezoutChain.Geometry.K2UnmixednessEndgame
import Appendix_FixedPoint.BezoutChain.Regularity.Grade.GradeUnmixedBridge
import Appendix_FixedPoint.BezoutChain.Regularity.Grade.GradeDepthFragment
import Appendix_FixedPoint.BezoutChain.Regularity.Unmixed.HeightDrop
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.RegularityBridge
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic

/-!
# Rees-route scoped probe
Survey + cost analysis of the Rees route to `DepthEqDimAt` (grade = dim at `R_P`),
plus the zero-price end-to-end wires that were still missing. Follows the
P2 regseq-probe pattern (survey + scoped GAPs); the `GAP-R1..R4`
names are already taken by `RegularSequenceProbe`, so this file uses
`GAP-REES-1..10`.

## Verdict: viable-scoped — in fact fully assembled modulo exactly the crux

Every Rees
condition below is proved, and the end-to-end chain
`hker → DepthEqDimAt → height-drop/unmixedness` is wired at pair level
(`Geometry/K2UnmixednessEndgame.lean`), Min-scoped (`Geometry/UnmixednessAtLengthTwo.lean` §§2–4),
and general-`k` (`BridgeToFixedPoint/FinalDischargeHub.lean`). The Rees route consumes the
crux (`hker`, discharged by the `d`-split on `[hmin1, hdimEq]`) — it does
not bypass it, so it adds no independent lever. Its exact residual is the
crux itself: `HdimEqMinAtAss` at `d ≥ 2` (gap-rees-9, owned by the crux
work; addresses: `NoetherGeAtAss`, High@Ge2).

## C1–C4 status (reconstructed — the tree never defines C1–C4 in one place)

* C1 = augmentation quasi-iso pair `(π, QuasiIso π)` at `residueCat`:
  proved conditional on `[hker]` — `koszulResiduePi_quasiIso`
  (`QuasiIsomorphismBridge.lean`, via `grlift_r2_exact_reduced`) +
  Shrink adapter `quasiIso_residuePiShrunk`
  (`ReesAssembly.lean`).
* C2 = Ext-comparison + Ext-subsingleton below `d`: proved conditional on
  `[hker]` — `koszulProjectiveResolutionOfSequence` (`ExtComparison`,
  on C1) + §13 master `koszulExt_subsingleton_below_ofSequence`
  (`SelfDuality.lean`, on C1 + C3 via `HomologyTransport`).
* C3 = shift-side triple `(e, hS, hS0)`: proved — `e` unconditional
  (`koszulShiftIsoSigned_commRing_ofSequence`, `SelfDuality.lean`,
  needs only `g`); `hS`/`hS0` on `[hker]` (`+ 1 ≤ d` for `hS0`)
  (`shift_hS_of_r2Reduced`, `shift_hS0_of_r2Reduced`,
  `HomologyTransport.lean`, via `grlift_r2_exact_reduced`).
* C4 = dimension equation `hdim : ↑↑d = dim R_P`: proved unconditional
  given sop data — `grlift_dim_eq_of_sop` (`GradedLift.lean`) via
  Mathlib regularity theory (`R_P` is regular: localization of a poly
  ring; `mult_dim_atPrime_eq_spanFinrank`,
  `MultiplicityNonvanishing.lean`).
* Sop data `(g, hgen, hd)` with `d = spanFinrank 𝔪`: proved
  unconditional — `grlift_sop_exists` (`GradedLift.lean`) via
  `SystemOfParameters` minimal `𝔪`-generators. Note: this is `embdim`-many
  generators of `𝔪`, not a system of parameters (see impact).
* Ext-comparison basis `b` at the ambient universe: proved unconditional —
  `extBasisULift` (`Geometry/K2UnmixednessEndgame.lean`, `Pi.basisFun` reindexed).
* Rees-tfae side conditions (`Finite` × 2, support, `I • ⊤ < ⊤`):
  discharged inside the §2 wrapper (`ReesAssembly.lean`).
* End-to-end: `depthEqDimAt_of_r2Reduced` (§6 main, on
  `[hker] + 1 ≤ d`) + `depthEqDimAt_zero_of_sop` (§7, `d = 0`
  unconditional given sop) → `depthEqDimAt_of_hker_atPrime`
  (`Geometry/K2UnmixednessEndgame.lean`, exact `[hkerQ]`) and the Min variant
  `depthEqDimAt_of_hkerMin_atPrime (`Geometry/UnmixednessAtLengthTwo.lean`).

## Impact on Rees inputs: none (all three land elsewhere)

* `hpiece` closed unconditionally: serves the HS route to `hdimEq`
  (gap-rees-9), not Rees proper — C1–C4 go through `hker`/R2, never
  through HS degree comparison.
* S.o.p. existence unconditional (`SystemOfParametersExistence`): not consumed by Rees
  — Rees needs `embdim`-many `𝔪`-generators (`grlift_sop_exists`), not
  `dim`-many parameters. Serves the crux/Noether route directly.
* `hminAvoid` narrowing, High@Ge2, NoetherLower: orthogonal (rung
  machinery) or inside gap-rees-9 (the crux addresses).

## Priced gaps (line estimates; difficulty; dependencies)

* Gap-rees-1 sop data `(g, hgen, hd)`: closed (`grlift_sop_exists`).
  0 lines.
* Gap-rees-2 basis `b`: closed (`extBasisULift`). 0 lines.
* Gap-rees-3 C1 at `residueCat`: closed on `[hker]`. 0 lines.
* Gap-rees-4 C2 Ext-subsingleton: closed on `[hker]`. 0 lines.
* Gap-rees-5 C3 shift triple: closed on `[hker]`. 0 lines.
* Gap-rees-6 C4 `hdim`: closed unconditional given sop. 0 lines.
* Gap-rees-7 end-to-end `DepthEqDimAt` on `[hker]` (full + Min scope):
  closed (`BabyABPair.depthEqDimAt_of_hker_atPrime`,
  `UnmixednessAtLengthTwo.depthEqDimAt_of_hkerMin_atPrime`). 0 lines.
* Gap-rees-8 `hker` `d`-split: closed on `[hmin1, hdimEq]`
  (`hkerAtAss_of_hmin_hdimEq`); `hmin1` closed for pairs
  (`hminOneAtAss_of_pair`); Min variant on `[hdimEqMin]` only
  (`hkerMinAtAss_of_hdimEqMin`). 0 lines Rees-side.
* Gap-rees-9 the crux (`HdimEqMinAtAss`, `d ≥ 2`): open — owned by the
  crux work (NoetherGe + HighD2 lanes). Not scoped here.
* Gap-rees-10 general-`k` geometry in Min scope: closed by this lane
  (§2, ~60 lines, easy, depends only on proved masters).

## What this file proves (all zero-price compositions of proved masters)

* (§0) Survey pins: `#check`s for the Rees-tfae API addresses.
* (§1) `rees_hkerAtAss_pair_of_hdimEq`: pair-level `HkerAtAss` on
  `[HdimEqAtAss]` only (`hmin1` via `hminOneAtAss_of_pair` — the
  composition was missing: no importers of `hminOneAtAss_of_pair`).
* (§2) Min-scope general-`k` delivery: `rees_hdepth_of_hdimEqMin`
  (`∀ Ass, DepthEqDimAt` on `[HdimEqMinAtAss]` — the Rees route's
  end-to-end output in crux scope), `rees_hunmixed_general_of_hkerMin`
  and `rees_hunmixed_general_of_hdimEqMin` (general-`k` unmixedness on
  `[HkerMinAtAss]` / `[HdimEqMinAtAss]` — the Min analogues of the
  full-`HkerAtAss` form, previously missing),
  `rees_heightDrop_general_of_hkerMin` (general-`k` height-drop on
  `[HkerMinAtAss]` — no consumer yet, completes the symmetric pair).

## Status

* §0 pins: unconditional (commands, no axioms).
* §1: conditional-exact on `[HdimEqAtAss]` (+ pair ctx).
* §2: `rees_hdepth_of_hdimEqMin`, `rees_hunmixed_general_of_hdimEqMin`:
  conditional-exact on `[HdimEqMinAtAss]`; `rees_hunmixed_general_of_hkerMin`,
  `rees_heightDrop_general_of_hkerMin`: conditional-exact on
  `[HkerMinAtAss]`.

## References

Project (read-only): `Regularity/Rees/ReesAssembly.lean` (§§1–7 Rees
scaffold), `Regularity/Koszul/SelfDuality.lean` (§13 master),
`Regularity/Koszul/HomologyTransport.lean` (C3),
`Regularity/Koszul/QuasiIsomorphismBridge.lean` (C1+C2),
`Regularity/Multiplicity/ReducedMasters.lean`
(R2 on `[hker]`), `Regularity/Koszul/GradedLift.lean` (sop data, C4),
`Regularity/Grade/GradeUnmixedBridge.lean` (chain+depth masters),
`Regularity/Grade/GradeDepthFragment.lean` (closed chain), `Geometry/K2UnmixednessEndgame.lean`
(pair Rees chain + `d`-split), `Geometry/UnmixednessAtLengthTwo.lean` §§2–4 (Min
chain), `BridgeToFixedPoint/FinalDischargeHub.lean` (general-`k` full-scope precedent).

Mathlib (`lean-toolchain` pins `v4.34.0`):
* `RingTheory/Depth/Rees.lean`
  (`ModuleCat.exists_isRegular_of_exists_subsingleton_ext`),
  (`subsingleton_ext_of_exists_isRegular`)
  (`ModuleCat.exists_isRegular_tfae`).
* `RingTheory/Ideal/AssociatedPrime/Basic.lean`
  (`AssociatedPrimes.mem_iff`).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace ReesProbe

/-! ## §0. Survey pins (Rees-tfae API addresses) -/

-- Pin: Rees backward direction `(3) → (4)` (`Rees.lean`).
#check @ModuleCat.exists_isRegular_of_exists_subsingleton_ext

-- Pin: Rees forward direction `(4) → (1)` (`Rees.lean`).
#check @ModuleCat.subsingleton_ext_of_exists_isRegular

-- Pin: the Rees tfae (`Rees.lean`).
#check @ModuleCat.exists_isRegular_tfae

-- Pin: associated-prime membership unfolds (`AssociatedPrime/Basic.lean`,
-- consumed for the `P.IsPrime` instance in §2, mirroring the former `FinalWire` route).
#check @AssociatedPrimes.mem_iff

/-! ## §1. Pair-level `HkerAtAss` on `[hdimEq]` only -/

/-- Pair-level universal `hker` on `[HdimEqAtAss]` only: the `d`-split
master `hkerAtAss_of_hmin_hdimEq` fed with the closed pair minimality
`hminOneAtAss_of_pair`. The composition was missing (no importers of
`hminOneAtAss_of_pair` outside `Geometry/K2UnmixednessEndgame.lean`).

Conditional on exactly `[HdimEqAtAss]` (+ pair ctx). -/
theorem rees_hkerAtAss_pair_of_hdimEq (m : ℕ) (K : Type*) [Field K]
    (q : Fin 2 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (hdimEq : BabyABPair.HdimEqAtAss m K J) :
    BabyABPair.HkerAtAss m K J :=
  BabyABPair.hkerAtAss_of_hmin_hdimEq m K J
    (BabyABPair.hminOneAtAss_of_pair m K q hsucc J hJ) hdimEq

/-! ## §2. Min-scope general-`k` delivery -/

/-- Universal `hdepth` on `[HdimEqMinAtAss]`: the Rees route's end-to-end
output (`∀ Q ∈ Ass, DepthEqDimAt`) in exactly the crux scope —
`hdepth_of_hkerMin` fed with the Min `d`-split
`hkerMinAtAss_of_hdimEqMin`.

Conditional on exactly `[HdimEqMinAtAss]`. -/
theorem rees_hdepth_of_hdimEqMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hdimEq : UnmixednessAtLengthTwo.HdimEqMinAtAss m K J)
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J)) :
    GradeDepthFragment.DepthEqDimAt m K Q :=
  UnmixednessAtLengthTwo.hdepth_of_hkerMin m K J
    (UnmixednessAtLengthTwo.hkerMinAtAss_of_hdimEqMin m K J hdimEq) Q hQ

/-- General-`k` unmixedness on `[HkerMinAtAss]`: the Min-scope analogue of
the full-`HkerAtAss` general-`k` form —
`unmixed_of_chain_depth` fed with the closed chain and per-prime
`hdepth_of_hkerMin`. Previously missing.

Conditional on exactly `[HkerMinAtAss]` (at `J`; general `k`). -/
theorem rees_hunmixed_general_of_hkerMin (m : ℕ) (K : Type*) [Field K]
    {k : ℕ} (q : Fin k → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (hker : UnmixednessAtLengthTwo.HkerMinAtAss m K J) :
    ∀ P ∈ associatedPrimes (MvPolynomial (Fin m) K)
      (MvPolynomial (Fin m) K ⧸ J), P ∈ J.minimalPrimes := by
  intro P hP
  have hprime : P.IsPrime := (AssociatedPrimes.mem_iff.mp hP).isPrime
  exact GradeUnmixedBridge.unmixed_of_chain_depth m K q hsucc J hJ P hP
    (GradeDepthFragment.gradeDropChain_of_successive m K q hsucc)
    (UnmixednessAtLengthTwo.hdepth_of_hkerMin m K J hker)

/-- General-`k` unmixedness on `[HdimEqMinAtAss]`: the Rees route's
end-to-end geometry delivery at general `k` in crux scope.

Conditional on exactly `[HdimEqMinAtAss]` (at `J`; general `k`). -/
theorem rees_hunmixed_general_of_hdimEqMin (m : ℕ) (K : Type*) [Field K]
    {k : ℕ} (q : Fin k → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (hdimEq : UnmixednessAtLengthTwo.HdimEqMinAtAss m K J) :
    ∀ P ∈ associatedPrimes (MvPolynomial (Fin m) K)
      (MvPolynomial (Fin m) K ⧸ J), P ∈ J.minimalPrimes :=
  rees_hunmixed_general_of_hkerMin m K q hsucc J hJ
    (UnmixednessAtLengthTwo.hkerMinAtAss_of_hdimEqMin m K J hdimEq)

/-- General-`k` height-drop on `[HkerMinAtAss]`: `heightDrop_of_chain_depth`
fed with the closed chain and per-prime `hdepth_of_hkerMin`. Note:
no consumer yet (the pair form `heightDrop_pair_of_hker` and the unmixed
form above carry the current consumers); proved to complete the symmetric
pair in Min scope.

Conditional on exactly `[HkerMinAtAss]` (at `J`; general `k`). -/
theorem rees_heightDrop_general_of_hkerMin (m : ℕ) (K : Type*) [Field K]
    {k : ℕ} (q : Fin k → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (hker : UnmixednessAtLengthTwo.HkerMinAtAss m K J) :
    HeightDrop.HeightDropResidualAt m K q hsucc J hJ :=
  GradeUnmixedBridge.heightDrop_of_chain_depth m K q hsucc J hJ
    (GradeDepthFragment.gradeDropChain_of_successive m K q hsucc)
    (UnmixednessAtLengthTwo.hdepth_of_hkerMin m K J hker)

#print axioms rees_hkerAtAss_pair_of_hdimEq
#print axioms rees_hdepth_of_hdimEqMin
#print axioms rees_hunmixed_general_of_hkerMin
#print axioms rees_hunmixed_general_of_hdimEqMin
#print axioms rees_heightDrop_general_of_hkerMin

end ReesProbe
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
