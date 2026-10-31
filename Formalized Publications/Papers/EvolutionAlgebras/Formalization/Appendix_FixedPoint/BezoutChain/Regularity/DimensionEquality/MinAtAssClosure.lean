/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Geometry.UnmixednessAtLengthTwo
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.ChiDegreeMaster
import Appendix_FixedPoint.BezoutChain.Regularity.DimensionEquality.SingleAllocator
import Appendix_FixedPoint.BezoutChain.Regularity.Grade.DimEqualsEmbdim

/-!
# `HdimEqMinAtAss` closer: H4 + H5 + R ⟹ the verbatim conclusion
The H-lane closer of the formalization: wire the H4 (GapHS discharge),
H5 (SupSes discharge), and R (regularity) pins into the H3 master
(`ChiDegreeMaster.hdimEqMinAtAss_of_chi_specs`) and conclude
`HdimEqMinAtAss` (`UnmixednessAtLengthTwo.lean`) plus the allocator slice.

## Pin ledger

* H4-SPEC = `ChiDegreeMaster.HchiGrowthAtAss` (χ eventually
  polynomial of degree `≤ dim`, dim pinned to `ringKrullDim`): the
  stated H1-conclusion shape. H4 discharges it from H1 §1+§2
  (`HilbertSerreRationality`, unconditional) + the GapHS atoms below.
  Sibling output unavailable — taken as an explicit hypothesis.
* H5-SPEC = `ChiDegreeMaster.HchiReduceAtAss` (the `dim`-th
  difference of χ does not vanish, same pin): the stated H2-conclusion
  shape. H5 discharges it from H2 §1+§2 (`SuperficialReduction`,
  unconditional) + the SupSes atoms below. Explicit hypothesis.
* R pin = `ChiDegreeMaster.HregDimAtAss` (`dim = embdim` at Ass
  primes): discharged unconditionally in-file (§0) from the proved
  `DimEqualsEmbdim.dimEmbAtAss_unconditional`. No SPEC.

## Why not unconditional (discharge check, verified by grep this lane)

The H4/H5 pins cannot be proved from proved material alone: H1 §3 needs
`GapHS1_kernelHomogeneous` (`HilbertSerreRationality.lean`, ker
homogeneous) + `GapHS2_grHilbertTransfer`
(grH agreement), and H2 §3 needs
`SupSesAssembly` + `SupDimZeroBase` (`SuperficialReduction.lean`).
Grep confirms zero in-tree proofs of any of these four (no file outside
the defining modules even mentions them), and no unconditional
`HdimEqMinAtAss` conclusion exists anywhere. Hence conditional-exact on
`[H4-SPEC, H5-SPEC]` with the wiring complete: a mechanical
substitution of the H4/H5 conclusions for `hH4`/`hH5` closes
`HdimEqMinAtAss` with no further proof work.

## Non-circularity

`HdimEqMinAtAss` is a crux-ring member, but neither hypothesis is: the
H4/H5 SPECs speak only A-side data (`ringKrullDim` of `R_Q`, `hsSamuel`
lengths), and the R pin speaks only `ringKrullDim`/`spanFinrank`. No
`gr`-statement (`ker φ`, `HdimEq`, `HgrDimLower`, …) is consumed. The
single `gr`-fact in the chain (the cumsum bridge `χ = ΣH`) is general
theory, proved unconditional inside H3. No crux-ring member is concluded
from a crux-ring hypothesis.

## Status

unconditional: `hregDimAtAss_unconditional` (R pin,).
conditional-exact on `[HchiGrowthAtAss, HchiReduceAtAss]` (the H4/H5
SPECs): `hdimEqMinAtAss_close_of_h4H5`, `alloc_ge2_close_of_h4H5`,
`hdimEqMinAtAss_close_verbatim`, `hdimEqMinAtAss_close_of_joint`.

## Closing register (exact residual for `HdimEqMinAtAss`)

open (exact): [`GapHS1_kernelHomogeneous` + `GapHS2_grHilbertTransfer`
(H4-atoms, feeding H4-SPEC) + `SupSesAssembly supChi` +
`SupDimZeroBase supChi` (H5-atoms, feeding H5-SPEC)] — see §3. Nothing
else: R is closed in §0, the χ-master (§1), differencing (§2), and
conclusion + allocator wiring (§3) are closed inside H3 and re-fired
here. In particular no `dim gr` fact (ring member) is needed anywhere.

## Import DAG

New leaf module (no importers): `Geometry/UnmixednessAtLengthTwo` (the
target), `Regularity/ChiDegreeMaster` (the H3 master + three pins),
`Regularity/SingleAllocator` (the allocator target),
`Regularity/DimEqualsEmbdim` (the R supplier). No cycle risk.

## References

* `Geometry/UnmixednessAtLengthTwo.lean` (`HdimEqMinAtAss`, verbatim binders).
* `Regularity/DimensionEquality/SingleAllocator.lean` (`HdimEqMasterAlloc`).
* `Regularity/Multiplicity/ChiDegreeMaster.lean` (H1/H2/R pins),
  (master conclusion) (allocator wiring).
* `Regularity/Grade/DimEqualsEmbdim.lean`
  (`dimEmbAtAss_unconditional`, the proved R pin).
* `Regularity/Multiplicity/HilbertSerreRationality.lean` (H4-atoms).
* `Regularity/Multiplicity/SuperficialReduction.lean` (H5-atoms).
-/

open scoped Polynomial

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace MinAtAssClosure

/-! ## §0. The R pin, unconditionally -/

/-- The R pin holds unconditionally: `dim R_Q = embdim R_Q` at every
`Q ∈ Ass(R ⧸ J)`, restating the proved
`dimEmbAtAss_unconditional` (`DimEqualsEmbdim.lean`) in the exact
`HregDimAtAss` (`ChiDegreeMaster.lean`) shape. The coercion
`ℕ → WithBot ℕ∞` matches by definitional unfolding (`exact` checks it).
-/
theorem hregDimAtAss_unconditional (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    ChiDegreeMaster.HregDimAtAss m K J := by
  intro Q _ hQ
  exact DimEqualsEmbdim.dimEmbAtAss_unconditional m K J Q hQ

#print axioms hregDimAtAss_unconditional

/-! ## §1. The closers: H4 + H5 + R(uncond) ⟹ conclusion + allocator -/

/-- The H-lane close: `HdimEqMinAtAss` exactly (the verbatim
`UnmixednessAtLengthTwo.lean` def) from the H4 + H5 SPECs, with R supplied
unconditionally from §0. Fires the H3 master
(`hdimEqMinAtAss_of_chi_specs`) with all three pins filled.

Conditional on exactly
`[HchiGrowthAtAss (H4-SPEC), HchiReduceAtAss (H5-SPEC)]`. -/
theorem hdimEqMinAtAss_close_of_h4H5 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hH4 : ChiDegreeMaster.HchiGrowthAtAss m K J)
    (hH5 : ChiDegreeMaster.HchiReduceAtAss m K J) :
    UnmixednessAtLengthTwo.HdimEqMinAtAss m K J :=
  ChiDegreeMaster.hdimEqMinAtAss_of_chi_specs m K J hH4 hH5
    (hregDimAtAss_unconditional m K J)

#print axioms hdimEqMinAtAss_close_of_h4H5

/-- The same input wired to the allocator: the `d ≥ 2` slice from
the H4 + H5 SPECs (via the H3 wiring, R filled from §0). Every
downstream consumer (HS, HD2, GXQ, J9) already reads through the
allocator, so this fires them all on H4/H5 discharge.

Conditional on exactly
`[HchiGrowthAtAss (H4-SPEC), HchiReduceAtAss (H5-SPEC)]`. -/
theorem alloc_ge2_close_of_h4H5 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hH4 : ChiDegreeMaster.HchiGrowthAtAss m K J)
    (hH5 : ChiDegreeMaster.HchiReduceAtAss m K J) :
    SingleAllocator.HdimEqMasterAlloc m K J (fun d => 2 ≤ d) :=
  ChiDegreeMaster.alloc_ge2_of_chi_specs m K J hH4 hH5
    (hregDimAtAss_unconditional m K J)

#print axioms alloc_ge2_close_of_h4H5

/-! ## §2. Verbatim-shape certificate + joint-hypothesis form -/

/-- Machine-checked verbatim certificate: the §1 conclusion restated with
the full `UnmixednessAtLengthTwo.lean` binder telescope spelled out. This
typechecks iff the stated telescope is definitionally the def,
so the successful elaboration is the verbatim proof (binder names and
implicitness match line for line).

Conditional on exactly
`[HchiGrowthAtAss (H4-SPEC), HchiReduceAtAss (H5-SPEC)]`. -/
theorem hdimEqMinAtAss_close_verbatim (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hH4 : ChiDegreeMaster.HchiGrowthAtAss m K J)
    (hH5 : ChiDegreeMaster.HchiReduceAtAss m K J) :
    ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    ∀ {d : ℕ}
      (_hdmin : d = (IsLocalRing.maximalIdeal
        (Localization.AtPrime Q)).spanFinrank),
    2 ≤ d →
      ∀ Qw : Polynomial ℚ, Qw.natDegree ≤ d - 1 →
        (fun n => ((SingleDropRegularity.singleDrop_grHilbert
          (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) n : ℕ) : ℚ))
          =ᶠ[Filter.atTop] NewtonDifferences.evalFun Qw →
        Qw.natDegree = d - 1 :=
  hdimEqMinAtAss_close_of_h4H5 m K J hH4 hH5

#print axioms hdimEqMinAtAss_close_verbatim

/-- Joint-hypothesis form: a single conjunction hypothesis for the
Mechanical substitution (substitute the H4∧H5 conjunction and
the conclusion follows with no further proof work).

Conditional on exactly
`[HchiGrowthAtAss (H4-SPEC), HchiReduceAtAss (H5-SPEC)]`. -/
theorem hdimEqMinAtAss_close_of_joint (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (h : ChiDegreeMaster.HchiGrowthAtAss m K J ∧
      ChiDegreeMaster.HchiReduceAtAss m K J) :
    UnmixednessAtLengthTwo.HdimEqMinAtAss m K J :=
  hdimEqMinAtAss_close_of_h4H5 m K J h.1 h.2

#print axioms hdimEqMinAtAss_close_of_joint

/-! ## §3. Closing register (doc-only)

The exact remaining atoms for `HdimEqMinAtAss`, and the proof that
nothing else is needed.

remaining (⊆ {H4-atoms, H5-atoms}):

1. H4-atoms (feed H4-SPEC = `HchiGrowthAtAss`):
   * `GapHS1_kernelHomogeneous` (`HilbertSerreRationality.lean`):
     `ker (polySurjResidue P d g hgen)` is homogeneous.
   * `GapHS2_grHilbertTransfer` (`HilbertSerreRationality.lean`):
     `grH n = hsQuotHilbert κ d (ker …) n` for all `n`.
   H4 route (not this lane): GapHS1+2 + H1 §1+§2 (unconditional) give
   `grH` growth `≤ d - 1` (`hsr_grRegular_rational_of_transfer`); the
   cumsum bridge (`χ = ΣH`, proved unconditional) lifts to χ growth
   `≤ d`; R (`dim = embdim`, §0) rewrites `d` to `dim`. That is
   `HchiGrowthAtAss`.
2. H5-atoms (feed H5-SPEC = `HchiReduceAtAss`):
   * `SupSesAssembly supChi` (`SuperficialReduction.lean`): the
     mul-by-`y` eventual SES equation from AR-stability + length
     finiteness (antecedents proved: `sup_arStable_of_artinRees`,
     `sup_lengthFin_supChi`).
   * `SupDimZeroBase supChi` (`SuperficialReduction.lean`): χ growth
     degree `0` over zero-dimensional quotients.
   H5 route (not this lane): the two SPECs + H2 §1+§2 (unconditional)
   drive the s.o.p. induction (`sup_chi_degree_le_dim_supChi`) and the
   exact-drop lemma (`sup_exactDrop_of_nonvanishing`) to the
   nonvanishing of the `dim`-th difference of χ. That is
   `HchiReduceAtAss`.

nothing else is needed (closed, with pointers):

* R pin: closed unconditionally in §0 (via).
* χ-degree master: closed inside H3 §1 (`chi_master_exact_dim`,
  `chi_master_exact_embdim`).
* Differencing χ-exact-`d` ⟹ `H_gr`-exact-`(d-1)`: closed inside H3 §2
  (`grPiece_of_chi_exact`, Newton + cumsum bridge only).
* Conclusion + allocator firing: closed inside H3 §3 and re-fired in
  §§1–2 (`hdimEqMinAtAss_of_chi_specs`, `alloc_ge2_of_chi_specs`).
* No `dim gr` fact (ring member) is consumed anywhere in §§0–2 or in
  H3 §§0–3; no crux-ring hypothesis appears in any telescope above.

Substitution: replace `hH4` by the H4 conclusion and `hH5` by
the H5 conclusion in §1; `hdimEqMinAtAss_close_of_h4H5` and
`alloc_ge2_close_of_h4H5` then conclude unconditionally. That ends the
HS bank and fires the ring + supply chain + J9 map to `hres2`.
-/

end MinAtAssClosure
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
