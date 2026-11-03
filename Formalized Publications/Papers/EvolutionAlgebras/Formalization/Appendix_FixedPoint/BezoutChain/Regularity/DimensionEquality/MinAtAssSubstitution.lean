/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Geometry.UnmixednessAtLengthTwo
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.ChiDegreeMaster
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.MinimalGeneratorExists
import Appendix_FixedPoint.BezoutChain.Regularity.DimensionEquality.SingleAllocator
import Appendix_FixedPoint.BezoutChain.Regularity.DimensionEquality.MinAtAssAssembly

/-!
# `HdimEqMinAtAss` H4-discharge: mechanical G1 substitution into G3
Substitute the proved G1 conclusions
(`grMinExist_atAss`; `grMinExist_hchiGrowth_unconditional`)
for the `MinGenAtAss` hypothesis (G3) of
`hdimEqMinAtAss_assembly` (G3), so `HdimEqMinAtAss` is
conditional only on the H5 SPEC (`H5Nonvan_ge1`, G3 shape).
No new mathematics: every proof below is a one-line application.

## Shape match (verified by read this lane — no mismatch)

* `MinGenAtAss` (G3) unfolds to
  `∀ Q [Q.IsPrime], Q ∈ associatedPrimes _ (_ ⧸ J) → ∃ d g, …`
  with the existential body line-identical to the
  `grMinExist_atAss` (G1) conclusion
  (`span (range g) = 𝔪 ∧ d = spanFinrank 𝔪`). The `exact` in
  `minGenAtAss_unconditional` is the machine check: it elaborates
  iff the shapes agree definitionally.
* `grMinExist_hchiGrowth_unconditional` (G1) concludes the
  verbatim H4-SPEC `HchiGrowthAtAss` (`ChiDegreeMaster.lean`),
  the same Prop `hchiGrowthAtAss_of_mingens` (G3) concludes.

## What this file proves

* (§1) `minGenAtAss_unconditional`: `MinGenAtAss` unconditional,
  from G1.
* (§1) `hchiGrowthAtAss_unconditional_g1`: the H4 pin unconditional,
  direct G1 alias (the H4-pin discharge, recorded).
* (§1) `hchiGrowthAtAss_of_subst`: the H4 pin unconditional through
  G3 §2 applied to (§1) — cross-route check of G1.
* (§2) `hchiReduceAtAss_of_h5Nonvan`: full `HchiReduceAtAss`
  conditional only on `[H5Nonvan_ge1]`, via G3.
* (§3) `hdimEqMinAtAss_of_h5Nonvan` + `alloc_ge2_of_h5Nonvan`: the
  verbatim conclusion and the allocator slice conditional only
  on `[H5Nonvan_ge1]`, via G3.
* (§3) `hdimEqMinAtAss_of_fullH5_subst` +
  `alloc_ge2_of_fullH5_subst`: zero-proof landing pad if the
  reshape delivers the full `HchiReduceAtAss` pin, via G3.

## Status

unconditional: `minGenAtAss_unconditional`,
`hchiGrowthAtAss_unconditional_g1`, `hchiGrowthAtAss_of_subst`.
conditional-exact on `[H5Nonvan_ge1]`: `hchiReduceAtAss_of_h5Nonvan`,
`hdimEqMinAtAss_of_h5Nonvan`, `alloc_ge2_of_h5Nonvan`.
conditional-exact on `[HchiReduceAtAss]`:
`hdimEqMinAtAss_of_fullH5_subst`, `alloc_ge2_of_fullH5_subst`.

## Closing register (exact residual for `HdimEqMinAtAss`)

open (exact): [`H5Nonvan_ge1` per `Q` at `1 ≤ dimN` (G3),
or, equivalently for consumers, the full `HchiReduceAtAss` pin
]. Nothing else: H4 (`MinGenAtAss`, `HchiGrowthAtAss`) is
closed unconditionally in §1, R is closed unconditionally (H6 §0),
and the χ-master/differencing/conclusion wiring is closed inside
H3+H6 and re-fired in G3 §§1–3.

T1/T2 reshape note: no T1/T2 result is present
in-tree at this writing (verified: a repo-wide grep has zero hits, and the newest
`Regularity/` results are the G1/G2/G3 files), so the H5
address is taken as G3's `H5Nonvan_ge1` verbatim (shape).
If the reshape delivers full `HchiReduceAtAss`, the
`..._of_fullH5_subst` forms fire with no further proof; if it
delivers a narrower prop (e.g. `SupTowerPosDim` per `R_Q`,
SupTowerClose), only the implication
(reshape ⇒ `H5Nonvan_ge1`) remains, outside this file's scope.

No Mathlib-absence claim is made or estimated.

## Import DAG

New leaf module (no importers): `Geometry/UnmixednessAtLengthTwo` (the
target), `Regularity/ChiDegreeMaster` (H-pins), `Regularity/MinimalGeneratorExists`
(G1), `Regularity/SingleAllocator`
(the allocator target), `Regularity/MinAtAssAssembly`
(G3). No cycle risk (leaf).

## References

* `Regularity/Koszul/MinimalGeneratorExists.lean` (G1, proved).
* `Regularity/DimensionEquality/MinAtAssAssembly.lean`
  (G3, proved).
* `Regularity/Multiplicity/ChiDegreeMaster.lean` (H-pins).
* `Geometry/UnmixednessAtLengthTwo.lean` (`HdimEqMinAtAss`, verbatim).
* `Regularity/DimensionEquality/SingleAllocator.lean` (`HdimEqMasterAlloc`).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace MinAtAssSubstitution

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.UnmixednessAtLengthTwo
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.ChiDegreeMaster
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.MinimalGeneratorExists
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.SingleAllocator
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.MinAtAssAssembly

/-! ## §1. The H4 discharge: G1 conclusions substituted unconditionally -/

/-- Gap-gr-minexist, substituted: `MinGenAtAss` (G3)
unconditional from `grMinExist_atAss` (G1). The `exact`
elaborates iff the G3 SPEC shape is definitionally the G1
conclusion shape — it is (verified by read: line-identical
existential bodies).
-/
theorem minGenAtAss_unconditional (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    MinGenAtAss m K J := by
  intro Q _ hQ
  exact grMinExist_atAss m K J Q hQ

#print axioms minGenAtAss_unconditional

/-- The H4-pin discharge, recorded: `HchiGrowthAtAss` (verbatim
) unconditional, the direct G1 alias. This is the
conclusion downstream consumers read; §1's second route below
cross-checks it through G3 §2.
-/
theorem hchiGrowthAtAss_unconditional_g1 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HchiGrowthAtAss m K J :=
  grMinExist_hchiGrowth_unconditional m K J

#print axioms hchiGrowthAtAss_unconditional_g1

/-- H4 via G3 §2 on the substituted mingens: `HchiGrowthAtAss`
unconditional through `hchiGrowthAtAss_of_mingens` (G3)
applied to `minGenAtAss_unconditional`. Cross-route check of G1
(independent `d = 0` base: G3 §1's Artinian route vs
G1 §3's cumsum route).
-/
theorem hchiGrowthAtAss_of_subst (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HchiGrowthAtAss m K J :=
  hchiGrowthAtAss_of_mingens m K J (minGenAtAss_unconditional m K J)

#print axioms hchiGrowthAtAss_of_subst

/-! ## §2. H5 assembly on the substituted mingens -/

/-- H5 assembly on substituted mingens: full `HchiReduceAtAss`
(verbatim) conditional only on `[H5Nonvan_ge1]`, via
`hchiReduceAtAss_of_ge1` (G3) with the mingens input
discharged by §1.

Conditional on exactly `[H5Nonvan_ge1]`. -/
theorem hchiReduceAtAss_of_h5Nonvan (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hH5 : H5Nonvan_ge1 m K J) :
    HchiReduceAtAss m K J :=
  hchiReduceAtAss_of_ge1 m K J (minGenAtAss_unconditional m K J) hH5

#print axioms hchiReduceAtAss_of_h5Nonvan

/-! ## §3. Final restatement: conclusion + allocator on H5 alone -/

/-- The restated close: `HdimEqMinAtAss` exactly (the verbatim
`UnmixednessAtLengthTwo.lean` def) conditional only on `[H5Nonvan_ge1]` —
`hdimEqMinAtAss_assembly` (G3) with `hMING` discharged by
§1. The H4 pin appears nowhere in the telescope.

Conditional on exactly `[H5Nonvan_ge1]`. -/
theorem hdimEqMinAtAss_of_h5Nonvan (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hH5 : H5Nonvan_ge1 m K J) :
    HdimEqMinAtAss m K J :=
  hdimEqMinAtAss_assembly m K J (minGenAtAss_unconditional m K J) hH5

#print axioms hdimEqMinAtAss_of_h5Nonvan

/-- The restated input wired to the allocator: the `d ≥ 2`
slice conditional only on `[H5Nonvan_ge1]`, via
`alloc_ge2_assembly` (G3) with `hMING` discharged by §1.

Conditional on exactly `[H5Nonvan_ge1]`. -/
theorem alloc_ge2_of_h5Nonvan (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hH5 : H5Nonvan_ge1 m K J) :
    HdimEqMasterAlloc m K J (fun d => 2 ≤ d) :=
  alloc_ge2_assembly m K J (minGenAtAss_unconditional m K J) hH5

#print axioms alloc_ge2_of_h5Nonvan

/-- Landing pad for the reshape: if T1/T2 deliver the full
`HchiReduceAtAss` pin (verbatim), the conclusion fires with
no further proof — `hdimEqMinAtAss_assembly_of_fullH5` (G3)
with `hMING` discharged by §1.

Conditional on exactly `[HchiReduceAtAss]`. -/
theorem hdimEqMinAtAss_of_fullH5_subst (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hH5 : HchiReduceAtAss m K J) :
    HdimEqMinAtAss m K J :=
  hdimEqMinAtAss_assembly_of_fullH5 m K J
    (minGenAtAss_unconditional m K J) hH5

#print axioms hdimEqMinAtAss_of_fullH5_subst

/-- Landing-pad allocator form: full `HchiReduceAtAss` to the
`d ≥ 2` slice with no further proof, via
`alloc_ge2_assembly_of_fullH5` (G3).

Conditional on exactly `[HchiReduceAtAss]`. -/
theorem alloc_ge2_of_fullH5_subst (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hH5 : HchiReduceAtAss m K J) :
    HdimEqMasterAlloc m K J (fun d => 2 ≤ d) :=
  alloc_ge2_assembly_of_fullH5 m K J (minGenAtAss_unconditional m K J) hH5

#print axioms alloc_ge2_of_fullH5_subst

end MinAtAssSubstitution
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
