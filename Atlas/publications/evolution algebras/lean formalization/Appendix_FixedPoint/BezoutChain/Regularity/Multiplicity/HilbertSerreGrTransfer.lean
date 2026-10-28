/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.ChiDegreeMaster
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.FiltrationStability
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.AssociatedGradedRing
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.GradedSurjectionInjective
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.HilbertSamuelDegree
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.HilbertSerre
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.HilbertSerreRationality
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.LengthFramework
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.NewtonDifferences
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedSurjection
import Appendix_FixedPoint.BezoutChain.Regularity.Grade.DimEqualsEmbdim
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.SingleDropRegularity

/-!
# gr-transfer closer: GapHS1 + GapHS2 discharged, gr rationality
Track-H lane H4 (gr-transfer closer): discharge the H1 §3 register
(`HilbertSerreRationality.lean` §3) and deliver the unconditional gr-side
rationality instance. This unblocks H6's HchiGrowth pin: the per-prime
χ-growth master (§4) concludes in the exact `HchiGrowthAtAss`
(`ChiDegreeMaster.lean`) conclusion shape, conditional only on
minimal-generator data.

## Results

* (§1) GapHS1 unconditional (`gapHS1_kerHomogeneous_unconditional`):
  `ker (polySurjResidue P d g hgen)` is homogeneous — a one-step corollary
  of the proved `hsAssemble_ker_homogeneousComponent_mem` (kernel elements
  have kernel homogeneous components, via uniqueness of homogeneous
  decomposition).
* (§2) GapHS2 unconditional (`gapHS2_grHilbertTransfer_unconditional`):
  `singleDrop_grHilbert 𝔪 n = hsQuotHilbert κ d (ker polySurjResidue) n`
  for all `n`. Proof: the kernel of the surjective piece map
  `singleDrop_pieceMap` is exactly the kernel piece (`grClose_ker_pieceMap_eq`,
  via the piece spec + `of`-injectivity), so the first isomorphism theorem
  (`grClose_quotEquivPiece`, via `quotEquivOfEq` +
  `quotKerEquivOfSurjective`) identifies the quotient piece with `grPiece`,
  and `LinearEquiv.length_eq` transports `finLength`
  (`grClose_grHilbert_eq_quot`).
* (§3) Unconditional gr-side rationality: pole order `≤ d` plus growth
  `≤ d - 1` (`grClose_rational`, by feeding §1+§2 into
  `hsr_grRegular_rational_of_transfer`), pole order `≤ embdim` for minimal
  families (`grClose_poleOrder_le_embdim`), and the `d = 0` polynomial form
  (`grClose_rational_zero`).
* (§4) χ-growth per-prime master (`chiGrowth_of_grClose_atAss`),
  conditional-exact on minimal-generator data `(g, hgen, hdmin)`:
  concludes `∃ dimN, ringKrullDim = dimN ∧ IsPolyGrowth (chiFunQ m K Q)
  dimN` — the exact `HchiGrowthAtAss` body — via the §3 growth bound, the
  unconditional cumsum bridge (`χ = ΣH`), `hsCumsum_isPolyGrowth`, and the
  Track-R rewrite (`dimEmbAtAss_unconditional`).

## Register (complete — no item dropped)

The H1 §3 register contains exactly two items (verified by full read of
`HilbertSerreRationality.lean` this lane):

* Gap-hs-1 (`GapHS1_kernelHomogeneous`, Rat): closed in §1.
* Gap-hs-2 (`GapHS2_grHilbertTransfer`, Rat): closed in §2.
* Further GapHS items: none exist (repo-wide grep for `GapHS`/`GAP-HS`
  finds no `GapHS3+` definition in any `.lean` or `.md` file; the Rat
  `## Register` section lists exactly two bullets and the §3 grade line is
  conditional-exact on exactly the two-element list).

## Status

unconditional: `grClose_fieldQuot`, `gapHS1_kerHomogeneous_unconditional`,
`grClose_ker_pieceMap_eq`, `grClose_quotEquivPiece`,
`grClose_grHilbert_eq_quot`, `gapHS2_grHilbertTransfer_unconditional`,
`grClose_rational`, `grClose_poleOrder_le_embdim`, `grClose_rational_zero`.
conditional-exact on minimal-generator data `[g, hgen, hdmin]`:
`chiGrowth_of_grClose_atAss`.

## Residual register

closed this lane: [GapHS1, GapHS2, the H1 §3 register in full]; [gr-side
rationality: pole order `≤ d` / `≤ embdim`, growth `≤ d - 1`, `d = 0`
polynomial form]; [per-prime χ-growth modulo mingens data].
open (exact): [gap-gr-minexist: minimal generator family existence per
`Q ∈ Ass(R ⧸ J)` — `∃ d g hgen, d = spanFinrank 𝔪`; needs 𝔪 FG (Noetherian,
proved) + Nakayama lifting of a `𝔪/𝔪²` basis
attempted (outside the H4 design note)] — the single remaining atom between §4
and the unconditional `HchiGrowthAtAss` pin.

## References

Mathlib (`lean-toolchain` pins `v4.34.0`), all read-only:
* `LinearAlgebra/Quotient/Defs.lean`: `Submodule.quotEquivOfEq`.
* `LinearAlgebra/Isomorphisms.lean`: `LinearMap.quotKerEquivOfSurjective`.
* `RingTheory/Length.lean`: `LinearEquiv.length_eq`.
* `RingTheory/LocalRing/ResidueField/Defs.lean`: `ResidueField.field`.
* `RingTheory/PowerSeries/Basic.lean`: `PowerSeries.mk`.
* `RingTheory/KrullDimension/Basic.lean`: `ringKrullDim`.
* `RingTheory/Ideal/AssociatedPrime/Basic.lean`: `associatedPrimes`.

Project (read-only):
* `Regularity/Multiplicity/HilbertSerreRationality.lean` (`GapHS1/2` defs, the three §3
  masters, `hsrPoleOrderLE`).
* `Regularity/Multiplicity/GradedSurjectionInjective.lean`
  (`hsAssemble_ker_homogeneousComponent_mem`).
* `Regularity/Multiplicity/SingleDropRegularity.lean` (`singleDrop_pieceMap` + spec +
  surjectivity, `singleDrop_grHilbert`, `singleDrop_of_injective`).
* `Regularity/Multiplicity/HilbertSerre.lean` (`hsKerPiece`, `hsMem_kerPiece`).
* `Regularity/Multiplicity/HilbertSamuelDegree.lean` (`hsCumsum_isPolyGrowth`, the
  unconditional cumsum bridge).
* `Regularity/Multiplicity/ChiDegreeMaster.lean` (`chiFunQ`, the pin shape).
* `Regularity/Grade/DimEqualsEmbdim.lean` (`dimEmbAtAss_unconditional`).
* `Regularity/Koszul/FiltrationStability.lean` (the `IsNoetherianRing (AtPrime)`
  instance only).
-/

open scoped Polynomial

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace HilbertSerreGrTransfer

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.ChiDegreeMaster
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AssociatedGradedRing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjectionInjective
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.HilbertSamuelDegree
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.HilbertSerre
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.HilbertSerreRationality
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.LengthFramework
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.NewtonDifferences
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjection
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.DimEqualsEmbdim
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.SingleDropRegularity

/-! ## §0. Register enumeration (doc-only)

The full H1 §3 register, with disposition (see the module docstring for the
exhaustiveness evidence):

1. `GapHS1_kernelHomogeneous` (Rat): `ker (polySurjResidue P d g
   hgen)` is homogeneous → closed unconditionally in §1.
2. `GapHS2_grHilbertTransfer` (Rat): `grH n = hsQuotHilbert κ d
   (ker …) n` for all `n` → closed unconditionally in §2 with
   `grH := singleDrop_grHilbert 𝔪` (the exact sequence H3/H6 consume).
3. Further items: none exist (see module docstring). Nothing is dropped.
-/

/-! ## §1. GapHS1: the presentation kernel is homogeneous -/

/-! ### §2 design note (read before editing)

The §2 kernel equation is stated over the syntactic quotient `R ⧸ 𝔪`
throughout (homogeneous types, so `quotEquivOfEq` applies and all
typeclass search follows the global quotient-land path, consistent with
the choice baked into `polySurj`'s type). The `Field (R ⧸ 𝔪)` needed by
`hsKerPiece`/`hsQuotHilbert` is supplied explicitly (`@`-form) via the
plain def `grClose_fieldQuot` — deliberately not a global instance: a
section-level instance perturbs `Semiring (MvPolynomial …)` resolution
away from the globally-consistent choice baked into `polySurj`'s type and
breaks rewrites at reducible transparency (the equiv construction alone
uses it as a local `haveI`, where all searched instances are mutually
consistent). Only the final `gapHS2_…` step crosses to `ResidueField`
(by `exact` at default transparency).
-/

/-- Quotient-land field term: the residue field of `R_P` is a field,
restated over the syntactic quotient `R ⧸ 𝔪`. A plain abbrev, not an
instance (see the §2 design note): it is passed explicitly wherever
`hsKerPiece`/`hsQuotHilbert` need `Field (R ⧸ 𝔪)`, so it never enters
typeclass search. Definitionally `ResidueField.field`.
-/
noncomputable abbrev grClose_fieldQuot {K : Type*} [Field K] {m : ℕ}
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime] :
    Field (Localization.AtPrime P ⧸
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) :=
  IsLocalRing.ResidueField.field _

#print axioms grClose_fieldQuot

/-- Gap-hs-1, closed: the kernel of the residue-field presentation
`polySurjResidue : κ[T^d] ↠ grRegular P` is homogeneous. This is the proved
`hsAssemble_ker_homogeneousComponent_mem` (kernel elements have kernel
homogeneous components) transported along the definitional unfolding
`polySurjResidue = polySurj` / `ResidueField = R ⧸ 𝔪` by `exact`.
-/
theorem gapHS1_kerHomogeneous_unconditional {K : Type*} [Field K] {m : ℕ}
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    GapHS1_kernelHomogeneous P d g hgen := by
  intro f hf n
  exact hsAssemble_ker_homogeneousComponent_mem _ d g hgen f hf n

#print axioms gapHS1_kerHomogeneous_unconditional

/-! ## §2. GapHS2: gr lengths are quotient-Hilbert values -/

/-- The kernel of the degree-`n` piece map is exactly the degree-`n` kernel
piece of the presentation kernel: `p ∈ ker (pieceMap n)` iff
`polySurj p.val = 0` (the piece spec `singleDrop_pieceFun_spec` plus
`of`-injectivity `singleDrop_of_injective`), iff `p.val ∈ ker polySurj`
(`RingHom.mem_ker`), iff `p ∈ hsKerPiece` (`hsMem_kerPiece`).
-/
theorem grClose_ker_pieceMap_eq {K : Type*} [Field K] {m : ℕ}
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) (n : ℕ) :
    LinearMap.ker (singleDrop_pieceMap
        (IsLocalRing.maximalIdeal (Localization.AtPrime P)) d g hgen n)
      = @hsKerPiece (Localization.AtPrime P ⧸
          IsLocalRing.maximalIdeal (Localization.AtPrime P))
        (grClose_fieldQuot P) d
        (RingHom.ker (polySurj (Localization.AtPrime P)
          (IsLocalRing.maximalIdeal (Localization.AtPrime P)) d g hgen))
        n := by
  ext p
  rw [LinearMap.mem_ker]
  have hspec : (polySurj _ _ d g hgen) ↑p =
      DirectSum.of _ n ((singleDrop_pieceMap _ d g hgen n) p) :=
    singleDrop_pieceFun_spec _ d g hgen n p
  constructor
  · intro h
    have h2 : (polySurj _ _ d g hgen) ↑p = 0 := by
      rw [hspec, h]
      exact map_zero _
    exact (@hsMem_kerPiece _ (grClose_fieldQuot P) _ _ _ p).mpr
      (RingHom.mem_ker.mpr h2)
  · intro h
    have hJ := (@hsMem_kerPiece _ (grClose_fieldQuot P) _ _ _ p).mp h
    have h0 : (polySurj _ _ d g hgen) ↑p = 0 := RingHom.mem_ker.mp hJ
    apply singleDrop_of_injective _ n
    rw [← hspec, h0]
    exact (map_zero _).symm

#print axioms grClose_ker_pieceMap_eq

/-- First-isomorphism form: the homogeneous piece modulo `ker pieceMap` is
`grPiece`, by surjectivity of the piece map
(`quotKerEquivOfSurjective`, `@`-instantiated with inferred type since
stating the `⧸`-quotient over the nested residue ring directly trips
`HasQuotient` synthesis — cf. `MultiplicityNonvanishing.multDegQuotEquiv`).
The `hsKerPiece` side is bridged downstream by `rw` along §2's kernel
equation in `grClose_grHilbert_eq_quot`.
-/
noncomputable def grClose_quotEquivPiece {K : Type*} [Field K] {m : ℕ}
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) (n : ℕ) :=
  -- `quotKerEquivOfSurjective` half only: the `hsKerPiece`-side bridge is
  -- done downstream by `rw` along `grClose_ker_pieceMap_eq` (stating a
  -- `⧸`-to-`⧸` equiv via `quotEquivOfEq` trips `HasQuotient` synthesis
  -- over the nested residue ring; `rw` inherits the quotient instance).
  @LinearMap.quotKerEquivOfSurjective _ _ _ _ _ _ _ _
      (singleDrop_pieceMap
        (IsLocalRing.maximalIdeal (Localization.AtPrime P)) d g hgen n)
      (singleDrop_pieceMap_surjective
        (IsLocalRing.maximalIdeal (Localization.AtPrime P)) d g hgen n)

#print axioms grClose_quotEquivPiece

/-- Pointwise transfer: the `gr` Hilbert value is the quotient-Hilbert
value, by `LinearEquiv.length_eq` along the §2 first-isomorphism
equivalence (no finiteness hypotheses needed — length is preserved by any
linear equiv), transported across `ResidueField = R ⧸ 𝔪` by `exact`.
-/
theorem grClose_grHilbert_eq_quot {K : Type*} [Field K] {m : ℕ}
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) (n : ℕ) :
    singleDrop_grHilbert
        (IsLocalRing.maximalIdeal (Localization.AtPrime P)) n
      = @hsQuotHilbert (Localization.AtPrime P ⧸
          IsLocalRing.maximalIdeal (Localization.AtPrime P))
        (grClose_fieldQuot P) d
        (RingHom.ker (polySurj (Localization.AtPrime P)
          (IsLocalRing.maximalIdeal (Localization.AtPrime P)) d g hgen))
        n := by
  have hlen := (grClose_quotEquivPiece P d g hgen n).length_eq
  unfold hsQuotHilbert
  rw [← grClose_ker_pieceMap_eq P d g hgen n]
  exact congrArg WithTop.untop₀ hlen.symm

#print axioms grClose_grHilbert_eq_quot

/-- Gap-hs-2, closed: the gr Hilbert sequence
`grH := singleDrop_grHilbert 𝔪` (the exact sequence H3/H6 consume) agrees
coefficient-wise with `hsQuotHilbert` of the presentation kernel. This is
the §2 quotient-land transfer transported along the definitional unfoldings
`polySurjResidue = polySurj` / `ResidueField = R ⧸ 𝔪` by `exact`.
-/
theorem gapHS2_grHilbertTransfer_unconditional {K : Type*} [Field K] {m : ℕ}
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    GapHS2_grHilbertTransfer P d g hgen
      (singleDrop_grHilbert
        (IsLocalRing.maximalIdeal (Localization.AtPrime P))) := by
  intro n
  exact grClose_grHilbert_eq_quot P d g hgen n

#print axioms gapHS2_grHilbertTransfer_unconditional

/-! ## §3. Unconditional gr-side rationality -/

/-- The gr Hilbert series has pole order `≤ d` at `t = 1` and the gr Hilbert
function has growth `≤ d - 1`: the H1 §3 conditional master
(`hsr_grRegular_rational_of_transfer`) with both transfer hypotheses
discharged by §§1–2.
-/
theorem grClose_rational {K : Type*} [Field K] {m : ℕ}
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) (hd : 1 ≤ d) :
    hsrPoleOrderLE (PowerSeries.mk fun n =>
        ((singleDrop_grHilbert
          (IsLocalRing.maximalIdeal (Localization.AtPrime P)) n : ℕ) : ℚ))
        d ∧
      IsPolyGrowth (fun n => ((singleDrop_grHilbert
        (IsLocalRing.maximalIdeal (Localization.AtPrime P)) n : ℕ) : ℚ))
        (d - 1) :=
  hsr_grRegular_rational_of_transfer P d g hgen _
    (gapHS1_kerHomogeneous_unconditional P d g hgen)
    (gapHS2_grHilbertTransfer_unconditional P d g hgen) hd

#print axioms grClose_rational

/-- Pole order `≤ embdim`: for a minimal generator family (`d` rewritten to
`spanFinrank 𝔪` along `hdmin`), the gr Hilbert series has pole order at
most the embedding dimension.
-/
theorem grClose_poleOrder_le_embdim {K : Type*} [Field K] {m : ℕ}
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hdmin : d = (IsLocalRing.maximalIdeal
      (Localization.AtPrime P)).spanFinrank) (hd : 1 ≤ d) :
    hsrPoleOrderLE (PowerSeries.mk fun n =>
        ((singleDrop_grHilbert
          (IsLocalRing.maximalIdeal (Localization.AtPrime P)) n : ℕ) : ℚ))
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)).spanFinrank := by
  rw [← hdmin]
  exact (grClose_rational P d g hgen hd).1

#print axioms grClose_poleOrder_le_embdim

/-- At `d = 0` the gr Hilbert series is itself polynomial (needs only the
GapHS2-shape, via `hsr_gr_rational_zero_of_transfer`).
-/
theorem grClose_rational_zero {K : Type*} [Field K] {m : ℕ}
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) (hd0 : d = 0) :
    ∃ f : ℚ[X], PowerSeries.mk (fun n => ((singleDrop_grHilbert
        (IsLocalRing.maximalIdeal (Localization.AtPrime P)) n : ℕ) : ℚ))
      = ↑f :=
  hsr_gr_rational_zero_of_transfer _
    (gapHS2_grHilbertTransfer_unconditional P d g hgen) hd0

#print axioms grClose_rational_zero

/-! ## §4. The χ-growth master (H3-pin shape, conditional on mingens data) -/

/-- Per-prime χ-growth in the exact `HchiGrowthAtAss`
(`ChiDegreeMaster.lean`) conclusion shape: `∃ dimN, ringKrullDim =
dimN ∧ IsPolyGrowth (chiFunQ m K Q) dimN`. Proof: the §3 gr growth bound
`≤ d - 1` lifts along the unconditional cumsum bridge (`χ = ΣH`) to χ
growth `≤ d` (`hsCumsum_isPolyGrowth`); the Track-R corollary
(`dimEmbAtAss_unconditional`) plus minimality rewrites `d` to `dim`.
The only non-imported input is the minimal-generator data itself.

Conditional on exactly minimal-generator data `[g, hgen, hdmin]`. -/
theorem chiGrowth_of_grClose_atAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J))
    {d : ℕ} (g : Fin d → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (hdmin : d = (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank)
    (hd : 1 ≤ d) :
    ∃ dimN : ℕ,
      ringKrullDim (Localization.AtPrime Q) = ((dimN : ℕ∞) : WithBot ℕ∞) ∧
        IsPolyGrowth (chiFunQ m K Q) dimN := by
  have hgr := (grClose_rational Q d g hgen hd).2
  have hbridge :=
    hsBridge_hs_eq_cumsum_unconditional (R := Localization.AtPrime Q)
  have hchi : IsPolyGrowth
      (hsCumsum (fun n => ((singleDrop_grHilbert
        (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) n : ℕ) : ℚ)))
      d := by
    have h := hsCumsum_isPolyGrowth hgr
    have hde : d - 1 + 1 = d := by omega
    rwa [hde] at h
  have hR := dimEmbAtAss_unconditional m K J Q hQ
  rw [← hdmin] at hR
  refine ⟨d, hR, ?_⟩
  have hfun : (fun n => ((hsSamuel (R := Localization.AtPrime Q) n : ℕ) : ℚ))
      = chiFunQ m K Q := rfl
  rw [← hfun, hbridge]
  exact hchi

#print axioms chiGrowth_of_grClose_atAss

/-! ## §5. Residual register (doc-only)

closed this lane: [GapHS1 (`gapHS1_kerHomogeneous_unconditional`)];
[GapHS2 (`gapHS2_grHilbertTransfer_unconditional`, with
`grH := singleDrop_grHilbert 𝔪`)]; [the H1 §3 register in full — no further
GapHS item exists, §0]; [gr-side rationality: pole order `≤ d`
(`grClose_rational`), pole order `≤ embdim` (`grClose_poleOrder_le_embdim`),
growth `≤ d - 1` (`grClose_rational`), `d = 0` polynomial form
(`grClose_rational_zero`)]; [per-prime χ-growth modulo mingens data
(`chiGrowth_of_grClose_atAss`)].

open (exact): [gap-gr-minexist: minimal generator family existence per
`Q ∈ Ass(R ⧸ J)` — `∃ d g hgen, d = spanFinrank 𝔪`; needs 𝔪 FG (Noetherian,
proved) + Nakayama lifting of a `𝔪/𝔪²` basis
attempted (outside the H4 design note)] — the single remaining atom between §4
and the unconditional `HchiGrowthAtAss` pin. route: supply
gap-gr-minexist per `Q`, feed the witnesses into `chiGrowth_of_grClose_atAss`,
and substitute the resulting `HchiGrowthAtAss` for `hH4` in
`MinAtAssClosure.hdimEqMinAtAss_close_of_h4H5`.
-/

end HilbertSerreGrTransfer
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
