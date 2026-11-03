/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Appendix_FixedPoint.BezoutChain.Geometry.UnmixednessAtLengthTwo
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.ChiDegreeMaster
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.FiltrationStability
import Appendix_FixedPoint.BezoutChain.Regularity.DimensionEquality.SingleAllocator
import Appendix_FixedPoint.BezoutChain.Regularity.DimensionEquality.MinAtAssClosure
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.HilbertSerreGrTransfer
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.NewtonDifferences
import Appendix_FixedPoint.BezoutChain.Regularity.Grade.DimEqualsEmbdim
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.SuperficialReduction
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.SesClosure

/-!
# `HdimEqMinAtAss` assembly: per-`Q` H4/H5 conclusions into the joint closer
Assemble the per-`Q` H4/H5 conclusions into the H3 pins
(`HchiGrowthAtAss`:134, `HchiReduceAtAss`:153) and substitute into
`hdimEqMinAtAss_close_of_joint` (AssClose:192) for the verbatim
`HdimEqMinAtAss` (`UnmixednessAtLengthTwo.lean`) plus the allocator slice.

## Sibling status (verified by reading)

* H4: sibling G1 proved in source as `MinimalGeneratorExists`
  (`grMinExist_hchiGrowth_unconditional`:220), but it is not imported
  here, so its per-`Q` conclusions are taken as
  explicit hypotheses in their exact stated shapes: `MinGenAtAss`
  (§0 = `grMinExist_atAss`:137) feeds the proved
  `chiGrowth_of_grClose_atAss` (GrClose:405) at `1 ≤ d`, while the
  `d = 0` per-`Q` form is proved in-file (§1, via the proved
  `supDimZeroBase_unconditional` — an independent Artinian route, not
  G1 §3's cumsum route).
* H5: the towers conclusion `hChiReduceAtAss_of_towers` (SupSesClose
  :757) is proved, but its premise `htower` was refuted as stated by
  sibling G2 (`TowerClosure`: `supSelectColon_tower_false`:171,
  `htower_atAss_false`:271, `htower_forces_assEmpty`:297). The live
  H5 residue is G2's reshape: `SupTowerPosDim` (:330) + master rework
  (:40-53). This file takes the per-`Q` H5 conclusion shape itself as
  the explicit hypothesis, narrowed to `1 ≤ dimN` (§0) since the
  `d = 0` per-`Q` form closes in-file (§1).

## What this file proves

* (§0) `MinGenAtAss` (gap-gr-minexist per `Q`, G1 §1 shape) and
  `H5Nonvan_ge1` (per-`Q`, pinned, `1 ≤ dimN` nonvanishing). SPECs.
* (§1) Both `d = 0` per-`Q` forms, unconditional in-file:
  `chiFunQ_eq_supChi_bot` (the `χ = supChi ⊥` bridge),
  `h4Zero_of_supDimZero` (R-pin to `dimN = 0` +
  `krullDimLE_quotBot_of_pin` + `supDimZeroBase_unconditional`),
  `h5Zero_of_mingens` (R-pin to `dimN = 0` + `seqDiff_zero` + the
  dim-zero seed `sup_dimZero_seed`).
* (§2) Pin assembly: `hchiGrowthAtAss_of_mingens` (per-`Q` split on
  `d = 0` (§1) vs `1 ≤ d` (GrClose:405)) and
  `hchiReduceAtAss_of_ge1` (same split, `1 ≤ d` from §0).
* (§3) Final substitution: `hdimEqMinAtAss_assembly` +
  `alloc_ge2_assembly` on `[MinGenAtAss, H5Nonvan_ge1]` via AssClose
  :192/:147, plus `..._of_fullH5` forms so the reshape result
  (full `HchiReduceAtAss`) substitutes with no further proof.
* (§4, doc-only) Closing register with exact residuals.

## Status

unconditional: `chiFunQ_eq_supChi_bot`, `h4Zero_of_supDimZero`,
`h5Zero_of_mingens`.
conditional-exact on `[MinGenAtAss]`: `hchiGrowthAtAss_of_mingens`.
conditional-exact on `[MinGenAtAss, H5Nonvan_ge1]`:
`hchiReduceAtAss_of_ge1`, `hdimEqMinAtAss_assembly`,
`alloc_ge2_assembly`, `hdimEqMinAtAss_assembly_of_fullH5`,
`alloc_ge2_assembly_of_fullH5`.
SPEC: `MinGenAtAss`, `H5Nonvan_ge1`.

## Closing register (exact residual for `HdimEqMinAtAss`)

open (exact): [`MinGenAtAss` per `Q` ← `grMinExist_atAss` (G1:137,
present in source, substitute on rebuild); `H5Nonvan_ge1` ←
`SupTowerPosDim` per `R_Q` + master dim-zero case-split rework
(SupTowerClose:330/:40-53)]. Nothing else: the `d = 0` per-`Q` forms
are closed in §1, R is closed unconditionally (H6 §0), the
χ-master/differencing/conclusion wiring is closed inside H3+H6, and
the refuted `htower` is consumed nowhere.

## Import DAG

New leaf module (no importers): `Geometry/UnmixednessAtLengthTwo` (the
target), `Regularity/ChiDegreeMaster` (H-pins, `chiFunQ`),
`Regularity/FiltrationStability` (the `IsNoetherianRing (AtPrime)`
instance only), `Regularity/SingleAllocator` (the allocator
target), `Regularity/MinAtAssClosure` (the H6 closers),
`Regularity/HilbertSerreGrTransfer` (the:405 per-`Q` growth
master), `Regularity/NewtonDifferences` (`seqDiff`, `IsPolyGrowth`),
`Regularity/DimEqualsEmbdim` (the R pin),
`Regularity/SuperficialReduction` (`supChi`, `supChi_bot`),
`Regularity/SesClosure` (`supDimZeroBase_unconditional`,
`krullDimLE_quotBot_of_pin`, `sup_dimZero_seed`, `supBot_ne_top`).
No cycle risk (leaf).

## References

* `Regularity/Multiplicity/ChiDegreeMaster.lean` (H-pins).
* `Regularity/Multiplicity/HilbertSerreGrTransfer.lean` (per-`Q` growth).
* `Regularity/Koszul/MinimalGeneratorExists.lean` (G1, source-only here).
* `Regularity/HomologicalDepth/SesClosure.lean` (towers conclusion),
  (dim-zero seed) (dim-zero base)
  (pin-to-`KrullDimLE`) (`⊥ ≠ ⊤`).
* `Regularity/HomologicalDepth/TowerClosure.lean` (tower
  refutation) (`SupTowerPosDim` reshape).
* `Regularity/DimensionEquality/MinAtAssClosure.lean` (joint closer +
  allocator wiring).
* `Geometry/UnmixednessAtLengthTwo.lean` (`HdimEqMinAtAss`, verbatim).
* `Regularity/DimensionEquality/SingleAllocator.lean` (`HdimEqMasterAlloc`).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace MinAtAssAssembly

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.UnmixednessAtLengthTwo
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.ChiDegreeMaster
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.SingleAllocator
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.MinAtAssClosure
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.HilbertSerreGrTransfer
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.NewtonDifferences
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.DimEqualsEmbdim
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.SuperficialReduction
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.SesClosure

/-! ## §0. Explicit per-`Q` hypothesis addresses -/

/-- Gap-gr-minexist per `Q ∈ Ass(R ⧸ J)`: a minimal generator family
for `𝔪(R_Q)` — the exact `grMinExist_atAss` (G1:137) conclusion shape,
taken as an explicit hypothesis since G1 is not imported
here. Later substitution of G1's theorem closes it with no
further proof.

Specification (Prop address for the G1 per-`Q` conclusion). -/
def MinGenAtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    ∃ d : ℕ, ∃ g : Fin d → Localization.AtPrime Q,
      Ideal.span (Set.range g) =
        IsLocalRing.maximalIdeal (Localization.AtPrime Q) ∧
      d = (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank

#print axioms MinGenAtAss

/-- The narrowed H5 residual: per-`Q ∈ Ass(R ⧸ J)`, pinned, `1 ≤ dimN`
nonvanishing of `Δ^dimN χ` — the exact `HchiReduceAtAss` (:153) per-`Q`
body restricted to positive pinned dimension. The `dimN = 0` per-`Q`
form closes unconditionally in §1, so this is the full live H5
residue. The towers route to it (`hChiReduceAtAss_of_towers`, SupSesClose
:757) needs G2's reshape (`SupTowerPosDim`, SupTowerClose:330) since
`htower` as stated is refuted (`htower_forces_assEmpty`,:297).

Specification (Prop address for the narrowed H5 conclusion). -/
def H5Nonvan_ge1 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    ∀ dimN : ℕ,
      ringKrullDim (Localization.AtPrime Q) = ((dimN : ℕ∞) : WithBot ℕ∞) →
      1 ≤ dimN →
      ¬ seqDiff dimN (chiFunQ m K Q) =ᶠ[Filter.atTop] 0

#print axioms H5Nonvan_ge1

/-! ## §1. Both `d = 0` per-`Q` forms, unconditional -/

/-- The `χ = supChi ⊥` bridge: `chiFunQ` is the `ℚ`-cast relative
Hilbert–Samuel function at `⊥` (via `supChi_bot`, Superficial:455).
-/
theorem chiFunQ_eq_supChi_bot (m : ℕ) (K : Type*) [Field K]
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] :
    chiFunQ m K Q = (fun n : ℕ =>
      ((supChi (R := Localization.AtPrime Q)
        (⊥ : Ideal (Localization.AtPrime Q)) n : ℕ) : ℚ)) := by
  funext n
  simp only [chiFunQ, supChi_bot]

#print axioms chiFunQ_eq_supChi_bot

/-- The `d = 0` per-`Q` H4 form: from minimality data with `d = 0`, `χ`
has growth `≤ 0` with `dimN = 0`. Proof: the R pin
(`dimEmbAtAss_unconditional`,:210) rewritten along minimality gives
`ringKrullDim = 0` (G1's:226-227 pattern); the pin becomes
`KrullDimLE 0` over `⧸ ⊥` (`krullDimLE_quotBot_of_pin`, SupSesClose
:736); the proved dim-zero base (`supDimZeroBase_unconditional`,
:536) gives growth `≤ 0` across the §1 bridge. Independent of G1 §3's
cumsum route.
-/
theorem h4Zero_of_supDimZero (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J))
    {d : ℕ}
    (hdmin : d = (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank)
    (hd0 : d = 0) :
    ∃ dimN : ℕ,
      ringKrullDim (Localization.AtPrime Q) = ((dimN : ℕ∞) : WithBot ℕ∞) ∧
        IsPolyGrowth (chiFunQ m K Q) dimN := by
  have hR := dimEmbAtAss_unconditional m K J Q hQ
  rw [← hdmin, hd0] at hR
  refine ⟨0, hR, ?_⟩
  have hdim : Ring.KrullDimLE 0
      (Localization.AtPrime Q ⧸ (⊥ : Ideal (Localization.AtPrime Q))) :=
    krullDimLE_quotBot_of_pin 0 hR
  have hbase := supDimZeroBase_unconditional (R := Localization.AtPrime Q) ⊥ hdim
  rw [chiFunQ_eq_supChi_bot m K Q]
  exact hbase

#print axioms h4Zero_of_supDimZero

/-- The `d = 0` per-`Q` H5 form: from minimality data with `d = 0`,
the H2-SPEC body holds with `dimN = 0`. Proof: the R pin rewritten
along minimality gives `ringKrullDim = 0`; `seqDiff 0 = id`
(`seqDiff_zero`) reduces nonvanishing to `¬ χ =ᶠ 0`, which is the
proved dim-zero seed (`sup_dimZero_seed`, SupSesClose:670) across the
§1 bridge. No dimension hypothesis is needed — positivity holds at any
dimension.
-/
theorem h5Zero_of_mingens (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J))
    {d : ℕ}
    (hdmin : d = (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank)
    (hd0 : d = 0) :
    ∃ dimN : ℕ,
      ringKrullDim (Localization.AtPrime Q) = ((dimN : ℕ∞) : WithBot ℕ∞) ∧
        ¬ seqDiff dimN (chiFunQ m K Q) =ᶠ[Filter.atTop] 0 := by
  have hR := dimEmbAtAss_unconditional m K J Q hQ
  rw [← hdmin, hd0] at hR
  refine ⟨0, hR, ?_⟩
  rw [seqDiff_zero]
  have hseed := sup_dimZero_seed (R := Localization.AtPrime Q) ⊥ supBot_ne_top
  rw [chiFunQ_eq_supChi_bot m K Q]
  exact hseed

#print axioms h5Zero_of_mingens

/-! ## §2. Pin assembly -/

/-- H4 assembly: `HchiGrowthAtAss` (verbatim:134) from per-`Q` mingens
data. Per `Q`, split on the mingens dimension: at `d = 0`, §1 gives
χ-growth `≤ 0`; at `1 ≤ d`, the proved per-`Q` master
(`chiGrowth_of_grClose_atAss`, GrClose:405) fires directly.

Conditional on exactly `[MinGenAtAss]`. -/
theorem hchiGrowthAtAss_of_mingens (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hMING : MinGenAtAss m K J) :
    HchiGrowthAtAss m K J := by
  intro Q _ hQ
  obtain ⟨d, g, hgen, hdmin⟩ := hMING Q hQ
  by_cases hd0 : d = 0
  · exact h4Zero_of_supDimZero m K J Q hQ hdmin hd0
  · have hd1 : 1 ≤ d := Nat.pos_of_ne_zero hd0
    exact chiGrowth_of_grClose_atAss m K J Q hQ g hgen hdmin hd1

#print axioms hchiGrowthAtAss_of_mingens

/-- H5 assembly: `HchiReduceAtAss` (verbatim:153) from per-`Q` mingens
data plus the narrowed residual. Per `Q`, split on the mingens
dimension: at `d = 0`, §1 closes unconditionally; at `1 ≤ d`, the §0
hypothesis fires at `dimN := d` with the pin from the R corollary
(:210).

Conditional on exactly `[MinGenAtAss, H5Nonvan_ge1]`. -/
theorem hchiReduceAtAss_of_ge1 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hMING : MinGenAtAss m K J)
    (hH5 : H5Nonvan_ge1 m K J) :
    HchiReduceAtAss m K J := by
  intro Q _ hQ
  obtain ⟨d, _, _, hdmin⟩ := hMING Q hQ
  by_cases hd0 : d = 0
  · exact h5Zero_of_mingens m K J Q hQ hdmin hd0
  · have hd1 : 1 ≤ d := Nat.pos_of_ne_zero hd0
    have hR := dimEmbAtAss_unconditional m K J Q hQ
    rw [← hdmin] at hR
    exact ⟨d, hR, hH5 Q hQ d hR hd1⟩

#print axioms hchiReduceAtAss_of_ge1

/-! ## §3. Final substitution: conclusion + allocator -/

/-- The assembly close: `HdimEqMinAtAss` exactly (the verbatim
`UnmixednessAtLengthTwo.lean` def) from the two explicit residuals — H4 from
§2, H5 from §2, substituted into the joint closer
(`hdimEqMinAtAss_close_of_joint`, AssClose:192).

Conditional on exactly `[MinGenAtAss, H5Nonvan_ge1]`. -/
theorem hdimEqMinAtAss_assembly (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hMING : MinGenAtAss m K J)
    (hH5 : H5Nonvan_ge1 m K J) :
    HdimEqMinAtAss m K J :=
  hdimEqMinAtAss_close_of_joint m K J
    ⟨hchiGrowthAtAss_of_mingens m K J hMING,
      hchiReduceAtAss_of_ge1 m K J hMING hH5⟩

#print axioms hdimEqMinAtAss_assembly

/-- The same input wired to the allocator: the `d ≥ 2` slice
from the two explicit residuals (via AssClose:147). Every downstream
consumer already reads through the allocator.

Conditional on exactly `[MinGenAtAss, H5Nonvan_ge1]`. -/
theorem alloc_ge2_assembly (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hMING : MinGenAtAss m K J)
    (hH5 : H5Nonvan_ge1 m K J) :
    HdimEqMasterAlloc m K J (fun d => 2 ≤ d) :=
  alloc_ge2_close_of_h4H5 m K J
    (hchiGrowthAtAss_of_mingens m K J hMING)
    (hchiReduceAtAss_of_ge1 m K J hMING hH5)

#print axioms alloc_ge2_assembly

/-- Direct-substitution form: the reshape result (full
`HchiReduceAtAss`, verbatim:153) fires the conclusion with no further
proof — H4 from §2 on `[MinGenAtAss]`.

Conditional on exactly `[MinGenAtAss, HchiReduceAtAss]`. -/
theorem hdimEqMinAtAss_assembly_of_fullH5 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hMING : MinGenAtAss m K J)
    (hH5 : HchiReduceAtAss m K J) :
    HdimEqMinAtAss m K J :=
  hdimEqMinAtAss_close_of_joint m K J
    ⟨hchiGrowthAtAss_of_mingens m K J hMING, hH5⟩

#print axioms hdimEqMinAtAss_assembly_of_fullH5

/-- Direct-substitution allocator form: full `HchiReduceAtAss` to the
`d ≥ 2` slice with no further proof.

Conditional on exactly `[MinGenAtAss, HchiReduceAtAss]`. -/
theorem alloc_ge2_assembly_of_fullH5 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hMING : MinGenAtAss m K J)
    (hH5 : HchiReduceAtAss m K J) :
    HdimEqMasterAlloc m K J (fun d => 2 ≤ d) :=
  alloc_ge2_close_of_h4H5 m K J
    (hchiGrowthAtAss_of_mingens m K J hMING) hH5

#print axioms alloc_ge2_assembly_of_fullH5

/-! ## §4. Closing register (doc-only)

The exact remaining atoms for `HdimEqMinAtAss`, and the proof that
nothing else is needed.

remaining (two atoms):

1. `MinGenAtAss` (§0): minimal-generator data per `Q ∈ Ass(R ⧸ J)`.
   FiniteDimDischarge (not this lane): substitute `grMinExist_atAss`
   (G1, `MinimalGeneratorExists.lean` — present in source) with no further proof work.
2. `H5Nonvan_ge1` (§0): per-`Q` pinned nonvanishing of `Δ^dimN χ` at
   `1 ≤ dimN`. FiniteDimDischarge route (not this lane): G2's reshape —
   `SupTowerPosDim` per `R_Q` (SupTowerClose:330) plus the master
   dim-zero case-split rework (:40-53), after which the reworked
   tower masters conclude the full:153 pin (which implies §0 by pin
   injectivity, `chi_pin_inj`, ChiDegree:185).

nothing else is needed (closed, with pointers):

* H4 `d = 0` per-`Q` form: closed unconditionally in §1 (R pin +
  `KrullDimLE` transport + dim-zero base; no GrClose input).
* H4 `d ≥ 1` per-`Q` form: the proved GrClose:405 master, fed by
  atom 1.
* H5 `d = 0` per-`Q` form: closed unconditionally in §1 (R pin + the
  dim-zero seed; no tower input).
* R pin: closed unconditionally in H6 §0 (via RegularDimEmb:210).
* χ-degree master, differencing, conclusion + allocator firing: closed
  inside H3 §§1–3 and re-fired in H6 §§1–2.
* The towers premise `htower` as stated is not consumed anywhere: it
  is refuted (SupTowerClose:171/:271/:297). No crux-ring hypothesis
  appears in any telescope above.

Later substitution: feed G1's `grMinExist_atAss` for `hMING` and
the reshape H5 conclusion for `hH5`/`hH5-full`; the §3 theorems then
conclude with no further proof work.
-/

end MinAtAssAssembly
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
