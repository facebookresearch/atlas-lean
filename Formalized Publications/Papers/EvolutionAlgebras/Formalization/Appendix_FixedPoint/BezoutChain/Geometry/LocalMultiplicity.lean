/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Statement.Definitions
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Module.SpanRank
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.InvariantBasisNumber
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.OreLocalization.Ring
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Local multiplicity at a locus point

This module supplies the contents of the four explicit named hypotheses
`Counting.lean` takes as its local-multiplicity inputs (`hlocal`, `hadd`,
`hpos`, `hloc`): with `S = coneQuotient n K G`, `ℓ̄` the image of `mkLin ℓ`,
and `A = chartRing n K G ℓ = (S_ℓ)₀` the degree-`0` chart,

* `coneEval` / `chartLocEval` / `chartEval`: evaluation of the chart ring at a
  chart point `v` (equations vanish at `v`, `ℓ(v) ≠ 0`), via
  `IsLocalization.lift` (canonical defs in `Statement.Definitions`, imported here).
* `chartEval_surjective`: the eval-surjectivity argument — constants land in
  the chart, so the residue field at the point is `K` (no gap).
* `chartEval_residue`: `A ⧸ ker ≃+* K`.
* `pointIdeal` / `pointIdeal_isMaximal`: the maximal ideal of `p`, as the
  kernel of evaluation at a representative (via the in-tree
  `RingHom.ker_isMaximal_of_surjective`; no gap; canonical defs in
  `Statement.Definitions`, imported here).
* `locRingAt` / `localMultiplicity`: the local ring
  `Localization (pointIdeal).primeCompl` and the local multiplicity
  (`Module.finrank K` of it; canonical defs in `Statement.Definitions`).
* `localPointMultiplicity`: the canonical point multiplicity (proved in
  `Statement.Definitions`; the preliminary global-length
  `Definitions.pointMultiplicity` is retained as a backward-compat alias —
  see the `hlocalLocal` docstring for why the preliminary form cannot satisfy
  the bridge).
* `hlocalLocal`: the `hlocal`-shape identification of the refined multiplicity
  with the representative-local length on the locus (proved).
* `hposLocal`: the `hpos`-shape positivity, from a chart point plus chart
  finiteness (proved; both inputs ChartFiltration-owned).
* `hposLocalAt` / `localPointMultiplicity_of_not_mem`: the local-ring
  positivity and the off-locus vanishing feeding migrated `mult_pos_of_mem`
  (proved).
* `hlocLocal`: the `hloc`-shape value `1` at a smooth point, from the
  regular-local input `hequiv` (proved; `_hs` is retained from
  `Counting.smooth_of_negId_linear_parts`, which is reused, not reproved).
* `regularLocal_dimZero_isField`: a regular local ring of Krull dimension `0`
  is a field (pure Mathlib assembly; closes the final link of gap G3).
* `haddLocal`: the `hadd`-shape additivity, from the Artinian decomposition
  input `hdecomp` plus finiteness (proved; inputs ChartFiltration-owned).
* `locLocusFinset` / `mem_locLocusFinset`: local mirrors of
  `Counting.locusFinset` / `Counting.mem_locusFinset` (same `Set.Finite`
  bodies), so this module no longer imports `Counting` (a downstream
  consumer, keeping this module's import closure to `Statement.Definitions`).
* `locEval` / `locEval_surjective` / `locEval_ker_isMaximal` /
  `locEval_algebraMap`: the R-hloc-3 evaluation lift to the local ring
  (residue-`K` identification in quotient-free form).
* `jacShapeAt` / `regSeqInput` / `regSeqNil` /
  `maximalIdealEqBotOfRegSeqNil`: the R-hloc-1 regular-sequence input
  (Jacobian `[-I | 0]` shape pinned; `IsRegular` output side; nil case proved).
* `hlocEquivOfMaximalBot` / `hlocBundle`: the T6 `hloc`-side consumer output
  (`≃ₐ[K]`, then multiplicity `1`, from a trivial local maximal ideal).

## Handoff mapping (which `Counting` hypothesis each theorem discharges)

* `sum_mult_eq_chart_length`'s `hlocal`
  (`∀ p ∈ locusFinset, localPointMultiplicity ℓ hc p = w p`) ⇐ `hlocalLocal`,
  with `w p := localMultiplicity` at `p.rep` (canonical
  `localPointMultiplicity` now in `Statement.Definitions`; the Counting call-site
  migration from `pointMultiplicity` is delivered alongside — gap G1).
* `sum_mult_eq_chart_length`'s `hadd`
  (`∑ p ∈ locusFinset, w p = finrank K A`) ⇐ `haddLocal` with
  `w := localPointMultiplicity`, modulo `hdecomp` (Artinian product-of-locals),
  `hfinLoc` (finiteness), `hc` (R1 nonvanishing) — all
  ChartFiltration-owned (gap G2).
* `mult_pos_of_mem`'s `hpos` (`0 < finrank K A`) ⇐ `hposLocal`, modulo a chart
  point (`v`, `hvG` from `locus_nonempty`, `hℓ` from R1) and `hfinA`;
  after migration the local form is `hposLocalAt` (modulo `hfinLoc`) with
  off-locus case `localPointMultiplicity_of_not_mem`.
* `smooth_implies_mult_one`'s `hloc` (`finrank K A = 1`) ⇐ `hlocLocal`
  (local form: `localMultiplicity = 1`), modulo `hequiv` — or ⇐ `hlocBundle`,
  which discharges `hequiv` from `hmax` (trivial local maximal ideal),
  modulo R-hloc-1 (residual ledger in gap G3). (`Counting` names cite
  the consumer side; the locus-finset facts used here are the local
  `locLocusFinset` mirrors.)

## Gaps (the deep geometric steps stay explicit hypotheses)

* G1 (bridge): proved. `Definitions.pointMultiplicity` (the global length,
  point argument unused) is retained as a backward-compat alias so
  sibling-owned `Counting`/`Statement`/`MkSystemSmoothness` keep compiling;
  identifying it with a local length at every locus point (`hlocal`) is false
  in general once the locus has more than one point. The canonical
  replacement `localPointMultiplicity` now lives in `Statement.Definitions`
  (moved down from here), and the bridge is `hlocalLocal` (proved,
  `dif_pos`). The Counting call-site migration patch is delivered alongside
  (sibling applies; not applied here).
* G2 (decomposition): `hdecomp` (the chart as the product of its local rings
  over the locus) needs the Artinian structure theorem for the chart —
  `Mathlib/RingTheory/Artinian/` (`Defs`, `Module`, `Ring`, `Algebra`,
  `Instances`) has finiteness and ACC/DCC API but no product-of-locals
  decomposition — plus the locus↔`MaxSpec` bijection. The affine case is
  in-tree (`MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton`,
  `Mathlib/RingTheory/Nullstellensatz.lean`); lifting through the section
  presentation is `Counting.locus_nonempty`'s `hlift`, owned in
  ChartFiltration (with `section_artinian` and R1).
* G3 (smooth value): `hequiv` (the local ring at a smooth point is `K`) needs
  the Jacobian criterion (full-rank Jacobian ⟹ regular local ring — in-tree
  there is only cotangent/submersive/presentation API,
  `Mathlib/RingTheory/Extension/Cotangent/Basic.lean`,
  `Mathlib/RingTheory/Extension/Presentation/{Core,Submersive}.lean`, no
  regularity-from-Jacobian), dimension-`0` of the locals, and the
  residue-field identification. `IsRegularLocalRing` itself exists
  (`Mathlib/RingTheory/RegularLocalRing/Defs.lean`); the final link
  (regular + dim-`0` ⟹ field) is now proved in-file by
  `regularLocal_dimZero_isField`. Residual ledger (R-taxonomy): R-hloc-1
  (Jacobian ⟹ regular-sequence input) is proved in interface form
  (`jacShapeAt` pins the `[-I | 0]` shape proved by
  `MkSystemSmoothness.hjac_mkSystem`,
  cited by name only,
  never imported;
  `regSeqInput` pins the `IsRegular`-plus-span output side, via the
  `Mathlib/RingTheory/Regular/RegularSequence.lean` API; `regSeqNil` and
  `maximalIdealEqBotOfRegSeqNil` prove the dimension-`0` nil case) — open
  sub-piece: producing `regSeqInput` from `jacShapeAt` (the Jacobian
  criterion proper, not in-tree); R-hloc-3 (evaluation lift of the local
  data) is proved (`locEval`, `locEval_surjective`,
  `locEval_ker_isMaximal`, `locEval_algebraMap`); `hdecomp` (G2 assembly
  input, Artinian product-of-locals) stays open, ChartFiltration-owned;
  R-hloc-2 (dimension-`0` without `hZd`) is not proved and is not attempted
  here (needs G-constraining input per the `hZd` refutation).
* No gap for eval-surjectivity (constants; `chartEval_surjective`), the
  residue field (`chartEval_residue` via
  `RingHom.quotientKerEquivOfSurjective`), or maximality
  (`RingHom.ker_isMaximal_of_surjective`, in-tree).
* Decoupling (import hygiene): this module imports only
  `Statement.Definitions` plus Mathlib (narrow, per-declaration verified in-tree);
  it does not import `Counting` (a downstream consumer via
  `ChartFiltration`/`Elimination`, cited by name), `Statement.Statement`, or
  `FixedPointFromBezout`
  (the non-import stands on DAG-hygiene grounds).
  The two `Counting` wrappers it needs are mirrored as
  `locLocusFinset` / `mem_locLocusFinset`; `Counting` theorem names appear
  only as prose citations of the consumer side. The canonical
  evaluation/local defs (`coneEval` through `localPointMultiplicity`) live in
  `Statement.Definitions` and are imported here.

## References

Mathlib v4.34.0 has no degree-of-variety or intersection-multiplicity API; the
results below are assembled from evaluation, localization, maximal-spectrum,
finrank, and length API. Per-declaration `## References` subsections cite the
exact module path and declaration name, each verified in-tree.

## Standing context (routine binders)

Named once here; per-decl docstrings below repeat GRADE verdicts and name only
substantive non-routine premises.

* `hvG : ∀ i, MvPolynomial.eval v (G i) = 0` — locus-membership equations at
  the representative `v`.
* `hℓ : MvPolynomial.eval v (mkLin n K ℓ) ≠ 0` — chart nonvanishing at `v`.
* `hc` — the ∀-point R1 chart-nonvanishing binder (definitional argument of
  `localPointMultiplicity`, not a GRADE condition).
* `hfin : (vanishingLocus n K G).Finite` — locus finiteness;
  `hfinA`/`hfinLoc : Module.Finite …` — chart/local-ring finiteness.
* `hp` — finset membership; `hdecomp` — the Artinian product-of-locals input
  of `haddLocal`.
* `hZd`/`hreg`/`hunmixed`/`hheight` appear only as cited-not-imported context.
* Instances: `[Field K]` throughout; `[Fintype …]` at the locus finset.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
open scoped BigOperators

/-! ## Residue field at a point (chart evaluation is canonical in `Statement.Definitions`) -/

/-- The residue field at the point is `K` (first isomorphism theorem for the
surjective evaluation).

## References

* `Mathlib/RingTheory/Ideal/Quotient/Operations.lean`,
  `RingHom.quotientKerEquivOfSurjective`
  (`(hf : Function.Surjective f) : R ⧸ ker f ≃+* S`). -/
noncomputable def chartEval_residue (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ : MvPolynomial.eval v (mkLin n K ℓ) ≠ 0) :
    chartRing n K G ℓ ⧸ RingHom.ker (chartEval n K G ℓ v hvG hℓ) ≃+* K :=
  RingHom.quotientKerEquivOfSurjective (chartEval_surjective n K G ℓ v hvG hℓ)

/-! ## Evaluation lift to the local ring (R-hloc-3) -/

/-- Evaluation at `v` lifted to the local ring: since `pointIdeal` is the
kernel of `chartEval`, every element of its prime complement maps to a nonzero
(hence unit) scalar, so `chartEval` extends over the localization by
`IsLocalization.lift`. This proves residual R-hloc-3 (the residue-`K` lift to
the localization in gap G3).

## References

* `Mathlib/RingTheory/Localization/Defs.lean`, `IsLocalization.lift`.
* `Mathlib/RingTheory/Ideal/Prime.lean`, `Ideal.mem_primeCompl_iff`
  (`x ∈ P.primeCompl ↔ x ∉ P`).
* `Mathlib/Algebra/Ring/Basic.lean`, `RingHom.mem_ker` (already used in
  `coneEval`, now in `Statement.Definitions`).
* `isUnit_iff_ne_zero` (core; already used in `chartLocEval`, now in
  `Statement.Definitions`). -/
noncomputable def locEval (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ : MvPolynomial.eval v (mkLin n K ℓ) ≠ 0) :
    locRingAt n K G ℓ v hvG hℓ →+* K :=
  IsLocalization.lift (M := (pointIdeal n K G ℓ v hvG hℓ).primeCompl)
    (S := locRingAt n K G ℓ v hvG hℓ)
    (g := chartEval n K G ℓ v hvG hℓ)
    (fun y => by
      have hnot : (y : chartRing n K G ℓ) ∉ pointIdeal n K G ℓ v hvG hℓ :=
        Ideal.mem_primeCompl_iff.mp y.2
      have hne : chartEval n K G ℓ v hvG hℓ y ≠ 0 :=
        fun h0 => hnot (RingHom.mem_ker.mpr h0)
      exact isUnit_iff_ne_zero.mpr hne)

/-- The lifted evaluation is surjective (chart elements map through
`algebraMap`, on which the lift computes via `lift_eq`).

## References

* `Mathlib/RingTheory/Localization/Defs.lean`, `IsLocalization.lift_eq`
  (`lift hg (algebraMap R S x) = g x`). -/
theorem locEval_surjective (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ : MvPolynomial.eval v (mkLin n K ℓ) ≠ 0) :
    Function.Surjective (locEval n K G ℓ v hvG hℓ) := by
  intro c
  obtain ⟨a, ha⟩ := chartEval_surjective n K G ℓ v hvG hℓ c
  refine ⟨algebraMap (chartRing n K G ℓ) _ a, ?_⟩
  unfold locEval
  rw [IsLocalization.lift_eq]
  exact ha

/-- The kernel of the lifted evaluation is maximal (surjective map onto the
field `K`). Together with `locEval_surjective` this is the G3(c) residue
identification at the localization (R-hloc-3): the local ring has residue
field `K`. (Remark: the quotient form `locRingAt ⧸ ker ≃+* K` via
`RingHom.quotientKerEquivOfSurjective` is mathematically immediate, but
forming `⧸` on a `Localization` hits an `OreLocalization` instance diamond
— `Ring.toSemiring` vs `OreLocalization.instSemiring` are defeq, verified by
`rfl`, yet unifying them burns all heartbeats — so the identification is
carried in quotient-free form: kernel-maximality here, and the full
`≃ₐ[K]` in `hlocEquivOfMaximalBot` below.)

## References

* `Mathlib/RingTheory/Ideal/Maps.lean`,
  `RingHom.ker_isMaximal_of_surjective`. -/
theorem locEval_ker_isMaximal (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ : MvPolynomial.eval v (mkLin n K ℓ) ≠ 0) :
    (RingHom.ker (locEval n K G ℓ v hvG hℓ)).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _
    (locEval_surjective n K G ℓ v hvG hℓ)

/-- The lifted evaluation reads off scalars: it sends `algebraMap K _ r` to
`r`. The proof pushes `algebraMap K` down the scalar tower to the chart
(`IsScalarTower.algebraMap_apply`), computes the first lift (`lift_eq`), then
pushes through the chart subalgebra coercion (definitional) and the second
lift (`lift_eq` again), ending at `coneEval_C` via `MvPolynomial.algebraMap_eq`.

## References

* `Mathlib/Algebra/Algebra/Tower.lean`, `IsScalarTower.algebraMap_apply`.
* `Mathlib/RingTheory/Localization/Defs.lean`, `IsLocalization.lift_eq`.
* `Mathlib/RingTheory/Ideal/Quotient/Operations.lean`,
  `Ideal.Quotient.mk_algebraMap`.
* `Mathlib/Algebra/MvPolynomial/Basic.lean`, `MvPolynomial.algebraMap_eq`. -/
theorem locEval_algebraMap (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ : MvPolynomial.eval v (mkLin n K ℓ) ≠ 0) (r : K) :
    locEval n K G ℓ v hvG hℓ (algebraMap K _ r) = r := by
  rw [IsScalarTower.algebraMap_apply K (chartRing n K G ℓ)
    (locRingAt n K G ℓ v hvG hℓ) r]
  unfold locEval
  rw [IsLocalization.lift_eq]
  unfold chartEval
  rw [RingHom.comp_apply]
  change chartLocEval n K G ℓ v hvG hℓ (algebraMap K _ r) = r
  rw [IsScalarTower.algebraMap_apply K (coneQuotient n K G)
    (Localization (Submonoid.powers
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ) :
        coneQuotient n K G))) r]
  unfold chartLocEval
  rw [IsLocalization.lift_eq, ← Ideal.Quotient.mk_algebraMap,
    MvPolynomial.algebraMap_eq]
  exact coneEval_C n K G v hvG r

/-! ## Local locus finset (mirror of `Counting` wrappers) -/

/-- The projective locus as a finset, from a finiteness proof. Local mirror of
`Counting.locusFinset` (same `Set.Finite.toFinset` body): stated here so this
module does not import `Counting` (a downstream consumer; cited by name, never
imported). The consumer mapping in the module docstring still cites
`Counting`'s names.

## References

* `Mathlib/Data/Set/Finite/Basic.lean`, `Set.Finite.toFinset`
  (`protected noncomputable def Finite.toFinset (h : s.Finite) : Finset α`). -/
noncomputable def locLocusFinset (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hfin : (vanishingLocus n K G).Finite) :
    Finset (Projectivization K (Fin (n + 2) → K)) :=
  hfin.toFinset

/-- Membership in `locLocusFinset` is membership in the locus (mirror of
`Counting.mem_locusFinset`).

## References

* `Mathlib/Data/Set/Finite/Basic.lean`, `Set.Finite.mem_toFinset`
  (`protected theorem mem_toFinset : a ∈ hs.toFinset ↔ a ∈ s`). -/
theorem mem_locLocusFinset (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hfin : (vanishingLocus n K G).Finite)
    (p : Projectivization K (Fin (n + 2) → K)) :
    p ∈ locLocusFinset n K G hfin ↔ p ∈ vanishingLocus n K G :=
  hfin.mem_toFinset

/-! ## The `hlocal` shape: refinement bridge -/

/-- `hlocalLocal` (discharges `Counting`'s `hlocal` after the migration from
`pointMultiplicity` to the canonical `localPointMultiplicity` — now in
`Statement.Definitions` — with `w p` the representative-local length): on the
locus, the refined multiplicity is the local length at `p.rep` (`dif_pos`;
the two sides differ only in proof terms).

Why the preliminary form cannot satisfy this (gap G1): the preliminary
`pointMultiplicity` is the global length `finrank K A` with `p` unused, so
`hlocal` would force every local length to equal the global length — false in
general once the locus has more than one point.

## References

* This module, `Appendix_FixedPoint.BezoutChain.locLocusFinset`,
  `Appendix_FixedPoint.BezoutChain.mem_locLocusFinset`
  (mirrors of `Counting.locusFinset`, `Counting.mem_locusFinset`). -/
theorem hlocalLocal (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hfin : (vanishingLocus n K G).Finite)
    (hc : ∀ (p : Projectivization K (Fin (n + 2) → K)) (_ : p ∈ vanishingLocus n K G)
      (v : Fin (n + 2) → K) (hv : v ≠ 0),
      Projectivization.mk K v hv = p → MvPolynomial.eval v (mkLin n K ℓ) ≠ 0)
    (p : Projectivization K (Fin (n + 2) → K))
    (hp : p ∈ locLocusFinset n K G hfin) :
    localPointMultiplicity n K G ℓ hc p
      = localMultiplicity n K G ℓ p.rep
        (fun i => ((mem_locLocusFinset n K G hfin p).mp hp) p.rep p.rep_nonzero
          (Projectivization.mk_rep p) i)
        (hc p ((mem_locLocusFinset n K G hfin p).mp hp) p.rep p.rep_nonzero
          (Projectivization.mk_rep p)) := by
  classical
  unfold localPointMultiplicity
  rw [dite_eq_left ((mem_locLocusFinset n K G hfin p).mp hp)]

/-- Off-locus values of the canonical multiplicity vanish (`dite_eq_right`).

## References

* `Statement.Definitions`, `Appendix_FixedPoint.BezoutChain.localPointMultiplicity` (the
  canonical def). -/
theorem localPointMultiplicity_of_not_mem (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hc : ∀ (p : Projectivization K (Fin (n + 2) → K)) (_ : p ∈ vanishingLocus n K G)
      (v : Fin (n + 2) → K) (hv : v ≠ 0),
      Projectivization.mk K v hv = p → MvPolynomial.eval v (mkLin n K ℓ) ≠ 0)
    (p : Projectivization K (Fin (n + 2) → K))
    (h : p ∉ vanishingLocus n K G) :
    localPointMultiplicity n K G ℓ hc p = 0 := by
  classical
  unfold localPointMultiplicity
  exact dite_eq_right h

/-! ## The `hpos` shape: positivity -/

/-- `hposLocal` (discharges `Counting`'s `hpos`): a chart point makes the chart
nontrivial (a surjective evaluation onto `K` cannot factor through a trivial
ring), hence of positive `K`-length. The point inputs (`v`, `hvG` from
`locus_nonempty`, `hℓ` from R1 nonvanishing) and `hfinA` (chart finiteness) are
ChartFiltration-owned.

## References

* `Mathlib/RingTheory/Length.lean`, `Module.length_pos`
  (`[Nontrivial M] : 0 < Module.length R M`), `Module.length_eq_finrank`
  (`(K M) [DivisionRing K] … [Module.Finite K M]:
  length K M = finrank K M`). -/
theorem hposLocal (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (v : Fin (n + 2) → K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ : MvPolynomial.eval v (mkLin n K ℓ) ≠ 0)
    (hfinA : Module.Finite K (chartRing n K G ℓ)) :
    0 < Module.finrank K (chartRing n K G ℓ) := by
  have hNT : Nontrivial (chartRing n K G ℓ) := by
    refine ⟨0, 1, fun h01 => ?_⟩
    have e : (chartEval n K G ℓ v hvG hℓ) 0 = (chartEval n K G ℓ v hvG hℓ) 1 :=
      congrArg _ h01
    rw [map_zero, map_one] at e
    exact one_ne_zero e.symm
  have := hNT
  have := hfinA
  have hL : 0 < Module.length K (chartRing n K G ℓ) := Module.length_pos
  rw [Module.length_eq_finrank K (chartRing n K G ℓ)] at hL
  exact_mod_cast hL

/-- `hposLocalAt` (local form of `hposLocal`, feeding migrated
`mult_pos_of_mem`): the local ring at a chart point is nontrivial (a
surjective lifted evaluation onto `K` cannot factor through a trivial ring),
hence of positive `K`-length. The local finiteness `hfinLoc` is
ChartFiltration-owned (same family input as `haddLocal`'s).

## References

* This module, `Appendix_FixedPoint.BezoutChain.locEval`,
  `Appendix_FixedPoint.BezoutChain.locEval_surjective`,
  `Appendix_FixedPoint.BezoutChain.localMultiplicity` (canonical def in `Statement.Definitions`).
* `Mathlib/RingTheory/Length.lean`, `Module.length_pos`,
  `Module.length_eq_finrank`. -/
theorem hposLocalAt (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ : MvPolynomial.eval v (mkLin n K ℓ) ≠ 0)
    (hfinLoc : Module.Finite K (locRingAt n K G ℓ v hvG hℓ)) :
    0 < localMultiplicity n K G ℓ v hvG hℓ := by
  have hNT : Nontrivial (locRingAt n K G ℓ v hvG hℓ) := by
    refine ⟨0, 1, fun h01 => ?_⟩
    have e : (locEval n K G ℓ v hvG hℓ) 0 = (locEval n K G ℓ v hvG hℓ) 1 :=
      congrArg _ h01
    rw [map_zero, map_one] at e
    exact one_ne_zero e.symm
  have := hNT
  have := hfinLoc
  have hL : 0 < Module.length K (locRingAt n K G ℓ v hvG hℓ) :=
    Module.length_pos
  rw [Module.length_eq_finrank K (locRingAt n K G ℓ v hvG hℓ)] at hL
  change 0 < Module.finrank K (locRingAt n K G ℓ v hvG hℓ)
  exact_mod_cast hL

/-! ## The `hloc` shape: value `1` at smooth points -/

/-- `hlocLocal` (discharges `Counting`'s `hloc` in local form): at a smooth
point whose local ring is `K`, the local multiplicity is `1`. `_hs` is retained
for interface stability — it is produced by
`Counting.smooth_of_negId_linear_parts` (reused, not reproved) — as are the
representative data `hv`/`_hmk` (pinning `v` above `p`, e.g. `v := p.rep`).
The regular-local input `hequiv` is the exact numerical content (gap
G3: smooth ⟹ local ring `≃ K` needs the Jacobian criterion plus dimension-`0`
plus residue-`K`, none of which is in-tree).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Statement.Definitions`,
  `Appendix_FixedPoint.BezoutChain.IsSmoothPoint`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.Counting`,
  `Appendix_FixedPoint.BezoutChain.smooth_of_negId_linear_parts`
  (producer of `hs`; reused here).
* `Mathlib/LinearAlgebra/Dimension/Finrank.lean`, `LinearEquiv.finrank_eq`,
  `Module.finrank_self`. -/
theorem hlocLocal (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (p : Projectivization K (Fin (n + 2) → K))
    (_hs : IsSmoothPoint n K G p)
    (v : Fin (n + 2) → K)
    (hv : v ≠ 0)
    (_hmk : Projectivization.mk K v hv = p)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ : MvPolynomial.eval v (mkLin n K ℓ) ≠ 0)
    (hequiv : locRingAt n K G ℓ v hvG hℓ ≃ₗ[K] K) :
    localMultiplicity n K G ℓ v hvG hℓ = 1 :=
  (LinearEquiv.finrank_eq hequiv).trans (Module.finrank_self K)

/-! ## Regular-local input: regularity plus dimension zero gives the field -/

/-- A regular local ring of Krull dimension `0` is a field: regularity forces
the `spanFinrank` of the maximal ideal to equal the dimension (`0`), hence the
maximal ideal is `⊥` (Noetherian `FG` plus the `spanFinrank`-zero
characterization), and a local ring with trivial maximal ideal is a field.
This closes the final link of gap G3 (regular + dim-`0` ⟹ the local ring
is a field, after which only the residue-`K` identification remains); the
Jacobian-criterion link (`[-I | 0]` ⟹ regular) and the dimension-`0` of the
locals stay open (residual (a)/(b) in G3). No global inputs (`hZd`,
`hunmixed`, `hheight`) are used.

## References

* `Mathlib/RingTheory/RegularLocalRing/Defs.lean`, `isRegularLocalRing_iff`
  (`IsRegularLocalRing R ↔ (maximalIdeal R).spanFinrank = ringKrullDim R`).
* `Mathlib/Algebra/Module/SpanRank.lean`,
  `Submodule.spanFinrank_eq_zero_iff_eq_bot`.
* `Mathlib/RingTheory/Noetherian/Defs.lean`,
  `Ideal.fg_of_isNoetherianRing`.
* `Mathlib/RingTheory/LocalRing/MaximalIdeal/Basic.lean`,
  `IsLocalRing.isField_iff_maximalIdeal_eq`. -/
theorem regularLocal_dimZero_isField (R : Type*) [CommRing R] [IsRegularLocalRing R]
    (hdim : ringKrullDim R = 0) : IsField R := by
  rw [IsLocalRing.isField_iff_maximalIdeal_eq,
    ← Submodule.spanFinrank_eq_zero_iff_eq_bot (Ideal.fg_of_isNoetherianRing _)]
  have hreg := (isRegularLocalRing_iff R).mp inferInstance
  rw [hdim] at hreg
  exact_mod_cast hreg

/-! ## Regular-sequence input at a smooth point (R-hloc-1) -/

/-- The exact Jacobian `[-I | 0]` shape at `v` for the system `G`: the input
side of residual R-hloc-1. This is the conclusion shape of
`MkSystemSmoothness.hjac_mkSystem`
(cited by name only —
that module is never imported here (import-closure hygiene: this module stays
on `Statement.Definitions` + Mathlib); the shape is restated to pin the interface).

## References

* `Mathlib/Algebra/MvPolynomial/PDeriv.lean`, `MvPolynomial.pderiv`. -/
def jacShapeAt (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (v : Fin (n + 2) → K) : Prop :=
  ∀ i j, MvPolynomial.eval v (MvPolynomial.pderiv j (G i))
    = -(if j = Fin.castSucc i then (1 : K) else 0)

/-- The regular-sequence input shape over the local ring: an explicit generator
list that is `IsRegular` (in the `RingTheory.Sequence` sense) and spans the
local maximal ideal. This is the output side of R-hloc-1: the Jacobian
criterion (not in-tree — no regularity-from-Jacobian API in Mathlib v4.34.0)
must supply `⟨gens, hreg, hspan⟩` from `jacShapeAt`; everything downstream of
it is proved here (`maximalIdealEqBotOfRegSeqNil`, `hlocEquivOfMaximalBot`,
`hlocBundle`).

## References

* `Mathlib/RingTheory/Regular/RegularSequence.lean`,
  `RingTheory.Sequence.IsRegular`, `Ideal.ofList`.
* `Mathlib/RingTheory/LocalRing/MaximalIdeal/Basic.lean` (already imported),
  `IsLocalRing.maximalIdeal`. -/
def regSeqInput (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ : MvPolynomial.eval v (mkLin n K ℓ) ≠ 0)
    (gens : List (locRingAt n K G ℓ v hvG hℓ)) : Prop :=
  RingTheory.Sequence.IsRegular (R := locRingAt n K G ℓ v hvG hℓ)
      (locRingAt n K G ℓ v hvG hℓ) gens ∧
    Ideal.ofList gens = IsLocalRing.maximalIdeal (locRingAt n K G ℓ v hvG hℓ)

/-- The empty list is a regular sequence on the local ring (needs only
nontriviality, available for `locRingAt`).

## References

* `Mathlib/RingTheory/Regular/RegularSequence.lean`,
  `RingTheory.Sequence.IsRegular.nil`. -/
theorem regSeqNil (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ : MvPolynomial.eval v (mkLin n K ℓ) ≠ 0) :
    RingTheory.Sequence.IsRegular (R := locRingAt n K G ℓ v hvG hℓ)
      (locRingAt n K G ℓ v hvG hℓ) [] :=
  RingTheory.Sequence.IsRegular.nil (locRingAt n K G ℓ v hvG hℓ)
    (locRingAt n K G ℓ v hvG hℓ)

/-- From a regular-sequence input with no generators, the local maximal ideal
is trivial: `ofList [] = ⊥` rewritten into the span hypothesis. At a
dimension-`0` smooth point this is the whole R-hloc-1 content (the maximal
ideal is `⊥`, so the local ring is a field); the regularity half is automatic.

## References

* `Mathlib/RingTheory/Regular/RegularSequence.lean`, `Ideal.ofList_nil`. -/
theorem maximalIdealEqBotOfRegSeqNil (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ : MvPolynomial.eval v (mkLin n K ℓ) ≠ 0)
    (gens : List (locRingAt n K G ℓ v hvG hℓ))
    (h : regSeqInput n K G ℓ v hvG hℓ gens) (hnil : gens = []) :
    IsLocalRing.maximalIdeal (locRingAt n K G ℓ v hvG hℓ) = ⊥ := by
  have hspan := h.2
  rw [hnil, Ideal.ofList_nil] at hspan
  exact hspan.symm

/-! ## Smooth-point bundle: the local `K`-algebra (T4/T6 consumer output) -/

/-- From a trivial local maximal ideal, the lifted evaluation upgrades to a
`K`-algebra isomorphism: kernel-maximality plus `IsLocalRing.eq_maximalIdeal`
force `ker = ⊥` (hence injectivity), `locEval_surjective` gives the bijection,
`RingEquiv.ofBijective` the ring isomorphism, and `locEval_algebraMap` the
scalar compatibility for `AlgEquiv.ofRingEquiv`.

## References

* `Mathlib/RingTheory/Localization/AtPrime/Basic.lean`,
  `IsLocalRing.eq_maximalIdeal` (via the `IsLocalRing` instance
  `Localization.AtPrime.isLocalRing`).
* `Mathlib/Algebra/Ring/Basic.lean`, `RingHom.injective_iff_ker_eq_bot`
  (via `RingHomClass`).
* `Mathlib/Algebra/Ring/Equiv.lean`, `RingEquiv.ofBijective`,
  `RingEquiv.ofBijective_apply`.
* `Mathlib/Algebra/Algebra/Equiv.lean`, `AlgEquiv.ofRingEquiv`. -/
noncomputable def hlocEquivOfMaximalBot (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ : MvPolynomial.eval v (mkLin n K ℓ) ≠ 0)
    (hmax : IsLocalRing.maximalIdeal (locRingAt n K G ℓ v hvG hℓ) = ⊥) :
    locRingAt n K G ℓ v hvG hℓ ≃ₐ[K] K := by
  have hker : RingHom.ker (locEval n K G ℓ v hvG hℓ) = ⊥ := by
    have h := IsLocalRing.eq_maximalIdeal
      (locEval_ker_isMaximal n K G ℓ v hvG hℓ)
    rw [hmax] at h
    exact h
  have hinj : Function.Injective (locEval n K G ℓ v hvG hℓ) :=
    (RingHom.injective_iff_ker_eq_bot _).mpr hker
  have hbij : Function.Bijective (locEval n K G ℓ v hvG hℓ) :=
    ⟨hinj, locEval_surjective n K G ℓ v hvG hℓ⟩
  refine AlgEquiv.ofRingEquiv
    (f := RingEquiv.ofBijective (locEval n K G ℓ v hvG hℓ) hbij) (fun r => ?_)
  rw [RingEquiv.ofBijective_apply]
  exact locEval_algebraMap n K G ℓ v hvG hℓ r

/-- `hlocBundle` (discharges `Counting`'s `hloc` in local form for the T6
`mkSystem` bridge): at a point whose local maximal ideal is trivial, the local
multiplicity is `1`. Same conclusion as `hlocLocal`, with its `hequiv`
discharged from `hmax` via `hlocEquivOfMaximalBot`; `hmax` itself is supplied
by R-hloc-1 (`maximalIdealEqBotOfRegSeqNil`) at dimension-`0` smooth points.
The section regularity `hreg` stays R1-owned (T4); the Artinian decomposition
`hdecomp` stays ChartFiltration-owned (G2).

## References

* `Mathlib/LinearAlgebra/Dimension/Finrank.lean`, `LinearEquiv.finrank_eq`,
  `Module.finrank_self`. -/
theorem hlocBundle (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ : MvPolynomial.eval v (mkLin n K ℓ) ≠ 0)
    (hmax : IsLocalRing.maximalIdeal (locRingAt n K G ℓ v hvG hℓ) = ⊥) :
    localMultiplicity n K G ℓ v hvG hℓ = 1 :=
  (LinearEquiv.finrank_eq
    (hlocEquivOfMaximalBot n K G ℓ v hvG hℓ hmax).toLinearEquiv).trans
    (Module.finrank_self K)

/-! ## The `hadd` shape: additivity over the locus -/

/-- Locus equations at the canonical representative (read off from
`p.2`; factored out so `locFam`'s body stays a clean application chain).

## References

* This module, `Appendix_FixedPoint.BezoutChain.mem_locLocusFinset`.
* `Mathlib/LinearAlgebra/Projectivization/Basic.lean`,
  `Projectivization.rep`, `Projectivization.rep_nonzero`,
  `Projectivization.mk_rep`. -/
theorem locMem (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hfin : (vanishingLocus n K G).Finite)
    (p : ↥(locLocusFinset n K G hfin)) :
    ∀ (v : Fin (n + 2) → K) (hv : v ≠ 0),
    Projectivization.mk K v hv = p.val → ∀ i, MvPolynomial.eval v (G i) = 0 :=
  (mem_locLocusFinset n K G hfin p.val).mp p.property

/-- The local-ring family over the locus, indexed by `↥(locusFinset …)` via
the canonical representatives (membership and chart-nonvanishing proofs read
off from `p.2`, so the summand needs no extra data). An `abbrev` (reducible)
so the `CommRing` / `Algebra K` instances flow through to `finrank`
statements. -/
noncomputable abbrev locFam (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hfin : (vanishingLocus n K G).Finite)
    (hc : ∀ (p : Projectivization K (Fin (n + 2) → K)) (_ : p ∈ vanishingLocus n K G)
      (v : Fin (n + 2) → K) (hv : v ≠ 0),
      Projectivization.mk K v hv = p → MvPolynomial.eval v (mkLin n K ℓ) ≠ 0)
    (p : ↥(locLocusFinset n K G hfin)) : Type _ :=
  locRingAt n K G ℓ p.val.rep
    (fun i => locMem n K G hfin p p.val.rep p.val.rep_nonzero
      (Projectivization.mk_rep p.val) i)
    (hc p.val ((mem_locLocusFinset n K G hfin p.val).mp p.property) p.val.rep
      p.val.rep_nonzero (Projectivization.mk_rep p.val))

/-- `haddLocal` (discharges `Counting`'s `hadd` with `w := localPointMultiplicity`):
the refined multiplicities over the locus sum to the chart length. The
substance is rank additivity over the Artinian decomposition `hdecomp`
(`finrank` of a finite product is the sum, `Module.finrank_pi_fintype`) plus
the bridge `hbr` from `localPointMultiplicity` to the family (via
`hlocalLocal`). The
inputs `hdecomp` (Artinian product-of-locals), `hfinLoc`
(finiteness), and `hc` (R1 nonvanishing) are ChartFiltration-owned (gap G2).

## References

* `Mathlib/LinearAlgebra/Dimension/Constructions.lean`,
  `Module.finrank_pi_fintype`
  (`[Fintype ι] [∀ i, Module.Free R (M i)] [∀ i, Module.Finite R (M i)]:
  finrank R (∀ i, M i) = ∑ i, finrank R (M i)`).
* `Mathlib/LinearAlgebra/Basis/VectorSpace.lean`,
  `Module.Free.of_divisionRing` (every vector space is free; resolved by TC).
* `Mathlib/LinearAlgebra/Dimension/Finrank.lean`, `LinearEquiv.finrank_eq`.
* `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`, `Finset.sum_congr`,
  `Finset.sum_attach`.
* `Mathlib/Data/Fintype/Sets.lean`, `Finset.attach_eq_univ`.
* This module, `Appendix_FixedPoint.BezoutChain.locLocusFinset`,
  `Appendix_FixedPoint.BezoutChain.mem_locLocusFinset`
  (mirrors of `Counting.locusFinset`, `Counting.mem_locusFinset`). -/
theorem haddLocal (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hfin : (vanishingLocus n K G).Finite)
    (hc : ∀ (p : Projectivization K (Fin (n + 2) → K)) (_ : p ∈ vanishingLocus n K G)
      (v : Fin (n + 2) → K) (hv : v ≠ 0),
      Projectivization.mk K v hv = p → MvPolynomial.eval v (mkLin n K ℓ) ≠ 0)
    [hfinLoc : ∀ p : ↥(locLocusFinset n K G hfin),
      Module.Finite K (locFam n K G ℓ hfin hc p)]
    (hdecomp : chartRing n K G ℓ ≃ₗ[K]
      ((p : ↥(locLocusFinset n K G hfin)) → locFam n K G ℓ hfin hc p)) :
    ∑ p ∈ locLocusFinset n K G hfin, localPointMultiplicity n K G ℓ hc p
      = Module.finrank K (chartRing n K G ℓ) := by
  classical
  have hbr : ∀ p : ↥(locLocusFinset n K G hfin),
      localPointMultiplicity n K G ℓ hc ↑p
        = Module.finrank K (locFam n K G ℓ hfin hc p) := by
    intro p
    have h1 := hlocalLocal n K G ℓ hfin hc (↑p) p.2
    rw [h1]
    rfl
  have hpi : Module.finrank K
      ((p : ↥(locLocusFinset n K G hfin)) → locFam n K G ℓ hfin hc p)
      = ∑ p : ↥(locLocusFinset n K G hfin),
        Module.finrank K (locFam n K G ℓ hfin hc p) := by
    have : ∀ p : ↥(locLocusFinset n K G hfin),
        Module.Free K (locFam n K G ℓ hfin hc p) :=
      fun p => Module.Free.of_divisionRing K (locFam n K G ℓ hfin hc p)
    exact Module.finrank_pi_fintype (R := K)
      (M := fun p : ↥(locLocusFinset n K G hfin) => locFam n K G ℓ hfin hc p)
  have hatt : (∑ p ∈ locLocusFinset n K G hfin, localPointMultiplicity n K G ℓ hc p)
      = ∑ p : ↥(locLocusFinset n K G hfin), localPointMultiplicity n K G ℓ hc ↑p := by
    rw [← Finset.sum_attach, Finset.attach_eq_univ]
  calc ∑ p ∈ locLocusFinset n K G hfin, localPointMultiplicity n K G ℓ hc p
      = ∑ p : ↥(locLocusFinset n K G hfin),
          Module.finrank K (locFam n K G ℓ hfin hc p) := by
        rw [hatt]
        exact Finset.sum_congr rfl (fun p _ => hbr p)
    _ = Module.finrank K
          ((p : ↥(locLocusFinset n K G hfin)) → locFam n K G ℓ hfin hc p) := hpi.symm
    _ = Module.finrank K (chartRing n K G ℓ) :=
      (LinearEquiv.finrank_eq hdecomp).symm

/-! ## Hpos chase: chart-point nonvanishing and chart-finiteness feeds

This section chases `Counting.mult_pos_of_mem`'s `hpos` input to its narrowest
exact form. Import-DAG status: `ChartFiltration` imports this module, so the
filtration pieces (`ChartNonvanishing`, `chart_finite_of_stable`,
`chart_pos_of_point`, `ChartLocFinite`) are taken as verbatim shapes below,
never imported (likewise `Elimination`'s `hlin` and `HilbertFunctionCount`'s
section-finiteness conclusion, both downstream of `ChartFiltration`; and
`Counting` itself, a downstream consumer cited by name, never imported).

Proved feeds:
* `hposNonvanishing_at`: the per-point `hℓ` input of `hposLocal` from the
  verbatim `HposNonvanishing` (= `ChartNonvanishing`) plus locus membership.
* `chartFinite_of_sectionEquiv`: the `hfinA` input of `hposLocal` from the
  verbatim chart–section identification `hlin` plus section finiteness.
* `hposGlobal_of_point`: global chart positivity in narrowest exact form,
  mirroring `ChartFiltration.chart_pos_of_point` with `hfinA` direct.
* `hposGlobal_of_section`: global chart positivity with `hfinA` fed through
  the proved equiv step.
* `multPos_of_mem_of_localFinite`: the consumer shape
  (`Counting.mult_pos_of_mem`'s conclusion `1 ≤ localPointMultiplicity`)
  with its `hpos` discharged by `hposLocalAt`, modulo pointwise `hfinLoc`.

Grades (closure grades per repo protocol):
* Consumer local form: conditional on exactly `[hmem, hfinLoc-at-p]`
  (`hc` is a definitional argument of `localPointMultiplicity`, not a
  condition). `hfinLoc` is the G2 Artinian-locals residual
  (`HposLocFinite` verbatim = `ChartLocFinite`): no in-tree discharge —
  finite-chart ⟹ finite-locals needs the Artinian product-of-locals
  structure theorem, absent from `Mathlib/RingTheory/Artinian/` v4.34.0.
* Global form: conditional on exactly `[hc, hp, hfinA]`, with `hfinA` fed
  here by `[hlin, section-finite]` (proved step) and section-finite fed by
  `[hreg, hZd]` (`HilbertFunctionCount.section_finite_of_artinian`, cited verbatim
  conclusion). Primary alternate `hfinA` route (filtration stability,
  `ChartFiltration.chart_finite_of_stable` from unconditional
  `chartPiece_finite` + `hstab`, cited): needs `chartPiece` vocabulary,
  hence stated in `ChartFiltration`, not here.
* Unconditional is impossible in this lane: a locus point needs `hlift`
  (projective dimension theorem, open), `hc` needs R1 avoidance
  (`ResultantLemmas.exists_regular_chartForm` modulo `hfin` + `havoid`),
  and finiteness needs `hZd`/`hreg`. Each residual above names its owner.
-/

/-- Verbatim-shape copy of `ChartFiltration.ChartNonvanishing` (the R1
nonvanishing input `hc`): the chart form misses every locus point, on every
representative. Stated here (not imported) because `ChartFiltration` imports
this module — an import would cycle.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ChartFiltration`,
  `Appendix_FixedPoint.BezoutChain.ChartNonvanishing` (verbatim source; cited, not imported). -/
def HposNonvanishing (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) : Prop :=
  ∀ (p : Projectivization K (Fin (n + 2) → K)) (_ : p ∈ vanishingLocus n K G)
    (v : Fin (n + 2) → K) (hv : v ≠ 0),
    Projectivization.mk K v hv = p → MvPolynomial.eval v (mkLin n K ℓ) ≠ 0

/-- Nonvanishing at the canonical representative: verbatim-`hc` evaluated at
`p.rep`. Proved mirror of `ChartFiltration.chartNonvanishing_at`; feeds the
`hℓ` input of `hposLocal`/`hposLocalAt`.

## References

* `Mathlib/LinearAlgebra/Projectivization/Basic.lean`,
  `Projectivization.rep`, `Projectivization.rep_nonzero`,
  `Projectivization.mk_rep`. -/
theorem hposNonvanishing_at (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hc : HposNonvanishing n K G ℓ)
    (p : Projectivization K (Fin (n + 2) → K))
    (hp : p ∈ vanishingLocus n K G) :
    MvPolynomial.eval p.rep (mkLin n K ℓ) ≠ 0 :=
  hc p hp p.rep p.rep_nonzero (Projectivization.mk_rep p)

/-- Chart finiteness (`hfinA`) from the chart–section identification plus
section finiteness: the inverse equiv exhibits the chart as a linear quotient
of the finite section. The `hlin` binder is the verbatim
`Elimination.chart_bridge` input; the instance binder is the verbatim
`HilbertFunctionCount.section_finite_of_artinian` conclusion (from `hreg` + `hZd`).

## References

* `Mathlib/LinearAlgebra/FiniteDimensional/Defs.lean`,
  `FiniteDimensional.of_surjective`.
* `Mathlib/Algebra/Module/Equiv/Defs.lean`, `LinearEquiv.surjective`. -/
theorem chartFinite_of_sectionEquiv (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hlin : (chartRing n K G ℓ) ≃ₗ[K] (sectionQuotient n K G ℓ))
    [Module.Finite K (sectionQuotient n K G ℓ)] :
    Module.Finite K (chartRing n K G ℓ) :=
  FiniteDimensional.of_surjective (V := sectionQuotient n K G ℓ)
    (V₂ := chartRing n K G ℓ) hlin.symm.toLinearMap hlin.symm.surjective

/-- Global chart positivity in narrowest exact form: a locus point plus
verbatim-`hc` plus `hfinA`. Proved mirror of
`ChartFiltration.chart_pos_of_point` with `hfinA` taken direct (its
filtration-stability discharge is cited there; its equiv discharge is proved
in `chartFinite_of_sectionEquiv` above).

Conditional on exactly `[hc, hp, hfinA]`.

## References

* This module, `Appendix_FixedPoint.BezoutChain.hposLocal`,
  `Appendix_FixedPoint.BezoutChain.hposNonvanishing_at`.
* `Mathlib/LinearAlgebra/Projectivization/Basic.lean`,
  `Projectivization.rep`, `Projectivization.rep_nonzero`,
  `Projectivization.mk_rep`. -/
theorem hposGlobal_of_point (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hc : HposNonvanishing n K G ℓ)
    (p : Projectivization K (Fin (n + 2) → K))
    (hp : p ∈ vanishingLocus n K G)
    (hfinA : Module.Finite K (chartRing n K G ℓ)) :
    0 < Module.finrank K (chartRing n K G ℓ) :=
  hposLocal n K G ℓ p.rep (hp p.rep p.rep_nonzero (Projectivization.mk_rep p))
    (hposNonvanishing_at n K G ℓ hc p hp) hfinA

/-- Global chart positivity with `hfinA` fed through the proved equiv step:
verbatim-`hc`, a locus point, verbatim-`hlin`, and section finiteness
(verbatim `HilbertFunctionCount.section_finite_of_artinian` conclusion, from `hreg` +
`hZd`).

Conditional on exactly `[hc, hp, hlin, section-finite]`.

## References

* This module, `Appendix_FixedPoint.BezoutChain.hposGlobal_of_point`,
  `Appendix_FixedPoint.BezoutChain.chartFinite_of_sectionEquiv`. -/
theorem hposGlobal_of_section (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hc : HposNonvanishing n K G ℓ)
    (p : Projectivization K (Fin (n + 2) → K))
    (hp : p ∈ vanishingLocus n K G)
    (hlin : (chartRing n K G ℓ) ≃ₗ[K] (sectionQuotient n K G ℓ))
    [Module.Finite K (sectionQuotient n K G ℓ)] :
    0 < Module.finrank K (chartRing n K G ℓ) :=
  hposGlobal_of_point n K G ℓ hc p hp
    (chartFinite_of_sectionEquiv n K G ℓ hlin)

/-- Verbatim-shape copy of `ChartFiltration.ChartLocFinite` (the `hfinLoc`
family input): every local ring over the locus is finite over `K`. Stated in
this module's own vocabulary (`locLocusFinset` / `locFam`), same
as the source. The content (Artinian locals of a finite chart) is the G2
residual proper and stays an explicit hypothesis.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ChartFiltration`,
  `Appendix_FixedPoint.BezoutChain.ChartLocFinite` (verbatim source; cited, not imported).
* This module, `Appendix_FixedPoint.BezoutChain.locLocusFinset`,
  `Appendix_FixedPoint.BezoutChain.locFam`. -/
def HposLocFinite (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hfin : (vanishingLocus n K G).Finite)
    (hc : HposNonvanishing n K G ℓ) : Prop :=
  ∀ p : ↥(locLocusFinset n K G hfin),
    Module.Finite K (locFam n K G ℓ hfin hc p)

/-- Consumer-shape local positivity: `Counting.mult_pos_of_mem`'s conclusion
(`1 ≤ localPointMultiplicity`) with its `hpos` discharged by `hposLocalAt`,
modulo pointwise local finiteness. The `dite` step mirrors the consumer's
proof (`Counting.mult_pos_of_mem`, cited not imported); `hc` keeps the exact
consumer binder shape.

Conditional on exactly `[hmem, hfinLoc-at-p]` (`hc` is a definitional
argument of `localPointMultiplicity`, not a condition).

## References

* This module, `Appendix_FixedPoint.BezoutChain.hposLocalAt`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Statement.Definitions`,
  `Appendix_FixedPoint.BezoutChain.localPointMultiplicity`,
  `Appendix_FixedPoint.BezoutChain.localMultiplicity`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.Counting`,
  `Appendix_FixedPoint.BezoutChain.mult_pos_of_mem`
  (consumer; cited by name, not imported — downstream of this module). -/
theorem multPos_of_mem_of_localFinite (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hc : ∀ (p : Projectivization K (Fin (n + 2) → K)) (_ : p ∈ vanishingLocus n K G)
      (v : Fin (n + 2) → K) (hv : v ≠ 0),
      Projectivization.mk K v hv = p → MvPolynomial.eval v (mkLin n K ℓ) ≠ 0)
    (p : Projectivization K (Fin (n + 2) → K))
    (hmem : p ∈ vanishingLocus n K G)
    (hfinLoc : Module.Finite K (locRingAt n K G ℓ p.rep
      (fun i => hmem p.rep p.rep_nonzero (Projectivization.mk_rep p) i)
      (hc p hmem p.rep p.rep_nonzero (Projectivization.mk_rep p)))) :
    1 ≤ localPointMultiplicity n K G ℓ hc p := by
  classical
  unfold localPointMultiplicity
  rw [dite_eq_left hmem]
  exact hposLocalAt n K G ℓ p.rep _ _ hfinLoc

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
/-! ## Smooth-point multiplicity one in local form (mult-assembly lane)

This section assembles smooth ⟹ mult-`1` in local form at a general smooth
point, mirroring the
`SpuriousMultiplicityOne`
pattern
(`mult1_spurious_of_hequiv` / `mult1_spurious_of_hfin_transport`, cited by
name, never imported) with `p` general instead of `distinguishedPoint`:

* `mult1_smooth_of_hequiv`: the direct reduction — `hlocalLocal` bridge plus
  the finrank computation — conditional on exactly `[hmem, hfin, hequiv]`.
* `mult1_smooth_of_transport`: the two-transport wiring — `hchart` (change of
  chart `ℓ ↦ ℓ₂` at `p.rep`) plus `hrep` (change of representative
  `p.rep ↦ w` in chart `ℓ₂`) into a base `hequiv` — conditional on exactly
  `[hmem, hfin, hequiv-at-base, hchart, hrep]`.
* `mult1_smooth_of_maximal_bot`: `hequiv` discharged in-file from `hmax`
  (trivial local maximal ideal) via `hlocBundle` — conditional on exactly
  `[hmem, hfin, hmax]`.

Conclusions are the exact `Statement.Statement.exists_another_point_of_smooth_point`
`hmult` consumer shape (`localPointMultiplicity n K G ℓ hc p = 1`, which at
`p := distinguishedPoint n K` is the `hmult` binder verbatim). `_hs` is
retained for interface stability (unused, as in `hlocLocal`/`SpuriousMultiplicityOne`);
smoothness is not re-proved.

Feed DAG check (import-vs-verbatim decision per feed; verified
by grep over `Formalization/Appendix_FixedPoint/BezoutChain/`):
* `hequiv`: source `MkSystemChart.hequiv_dist_of_residuals` is
  distinguished-chart/point-only and unimportable
  (`MkSystemChart → ChartFiltration → LocalMultiplicity` would cycle). Taken as a
  hypothesis binder (shape needs no def); in-file discharge from `hmax` via
  `hlocBundle` is `mult1_smooth_of_maximal_bot` above.
* `hchart`: source `ChartCompat.ChartCompatIso` is unimportable
  (`ChartCompat → MkSystemChart → … → LocalMultiplicity` would cycle). The residual
  is small, so it is mirrored verbatim as `HmultChartCompatIso` below with
  its consumption step proved (`hchart_of_iso_local`, via
  `LinearEquiv.finrank_eq`); the transport theorem takes the `hchart`
  equation itself as a binder.
* `hrep`: source `ChartCompat.localMultiplicity_rep_eq_zRep` is unimportable
  (same cycle) and its proof chain (`chartLocEval_smul_mk` and below) is too
  large to mirror — taken as an equation binder, not mirrored. Reported.
* `hfin`: shape `(vanishingLocus n K G).Finite` needs no def (in imported
  `Statement.Definitions`); the `mkSystem`-specific discharge
  (`MkSystemChart.locus_finite_of_bpf_affine`) is unimportable (same cycle)
  and out of scope at general `G` — taken as a binder. Reported.

Grades (closure grades per repo protocol): each theorem conditional on its
exact list above. Unconditional is impossible in this lane (needs the
Jacobian-criterion `hequiv` discharge + `hfin` + transports, all residual).
-/

/-- Verbatim-shape copy of `ChartCompat.ChartCompatIso` (the `hchart`
residual): the `K`-linear iso of the two chart-local rings at `v`. Stated
here (not imported) because `ChartCompat` transitively imports this module
(`ChartCompat → MkSystemChart → ChartFiltration → LocalMultiplicity`) — an import
would cycle.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ChartCompat`,
  `Appendix_FixedPoint.BezoutChain.ChartCompatIso`
  (verbatim source; cited, not imported). -/
def HmultChartCompatIso (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ₁ ℓ₂ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG₁ : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ₁ : MvPolynomial.eval v (mkLin n K ℓ₁) ≠ 0)
    (hvG₂ : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ₂ : MvPolynomial.eval v (mkLin n K ℓ₂) ≠ 0) : Prop :=
  Nonempty (locRingAt n K G ℓ₁ v hvG₁ hℓ₁
    ≃ₗ[K] locRingAt n K G ℓ₂ v hvG₂ hℓ₂)

/-- Proved mirror of `ChartCompat.localMultiplicity_chart_independent_of_iso`:
a `K`-linear iso of the two chart-local rings makes the local multiplicities
agree (the `hloceq` equation at `v`).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ChartCompat`,
  `Appendix_FixedPoint.BezoutChain.localMultiplicity_chart_independent_of_iso` (mirrored).
* `Mathlib/LinearAlgebra/Dimension/Finrank.lean`,
  `LinearEquiv.finrank_eq`. -/
theorem localMultiplicity_chart_independent_of_iso_local (n : ℕ) (K : Type*)
    [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ₁ ℓ₂ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG₁ : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ₁ : MvPolynomial.eval v (mkLin n K ℓ₁) ≠ 0)
    (hvG₂ : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ₂ : MvPolynomial.eval v (mkLin n K ℓ₂) ≠ 0)
    (e : locRingAt n K G ℓ₁ v hvG₁ hℓ₁
      ≃ₗ[K] locRingAt n K G ℓ₂ v hvG₂ hℓ₂) :
    localMultiplicity n K G ℓ₁ v hvG₁ hℓ₁
      = localMultiplicity n K G ℓ₂ v hvG₂ hℓ₂ :=
  LinearEquiv.finrank_eq e

/-- The `hchart` equation from the verbatim residual (proved mirror of
`ChartCompat.hloceq_of_chartCompatIso`).

## References

* This module, `Appendix_FixedPoint.BezoutChain.HmultChartCompatIso`,
  `Appendix_FixedPoint.BezoutChain.localMultiplicity_chart_independent_of_iso_local`. -/
theorem hchart_of_iso_local (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ₁ ℓ₂ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG₁ : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ₁ : MvPolynomial.eval v (mkLin n K ℓ₁) ≠ 0)
    (hvG₂ : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ₂ : MvPolynomial.eval v (mkLin n K ℓ₂) ≠ 0)
    (hiso : HmultChartCompatIso n K G ℓ₁ ℓ₂ v hvG₁ hℓ₁ hvG₂ hℓ₂) :
    localMultiplicity n K G ℓ₁ v hvG₁ hℓ₁
      = localMultiplicity n K G ℓ₂ v hvG₂ hℓ₂ := by
  obtain ⟨e⟩ := hiso
  exact localMultiplicity_chart_independent_of_iso_local n K G ℓ₁ ℓ₂ v
    hvG₁ hℓ₁ hvG₂ hℓ₂ e

/-- Direct smooth-point mult-`1` in local form (general-`p` mirror of
`SpuriousMultiplicityOne.mult1_spurious_of_hequiv`,
cited by name, never imported):
the consumer `hmult` shape from locus membership, locus finiteness, and the
local `K`-identification at `p.rep`. Proved by the `hlocalLocal` bridge plus
the finrank computation (proof-term mismatches absorbed by proof irrelevance
in `exact`, per the sibling proof).

Conditional on exactly `[hmem, hfin, hequiv]`.

## References

* This module, `Appendix_FixedPoint.BezoutChain.hlocalLocal`,
  `Appendix_FixedPoint.BezoutChain.mem_locLocusFinset`.
* `Mathlib/LinearAlgebra/Dimension/Finrank.lean`, `LinearEquiv.finrank_eq`,
  `Module.finrank_self`. -/
theorem mult1_smooth_of_hequiv (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hc : ∀ (p : Projectivization K (Fin (n + 2) → K))
      (_ : p ∈ vanishingLocus n K G)
      (v : Fin (n + 2) → K) (hv : v ≠ 0),
      Projectivization.mk K v hv = p →
        MvPolynomial.eval v (mkLin n K ℓ) ≠ 0)
    (p : Projectivization K (Fin (n + 2) → K))
    (_hs : IsSmoothPoint n K G p)
    (hmem : p ∈ vanishingLocus n K G)
    (hfin : (vanishingLocus n K G).Finite)
    (hequiv : locRingAt n K G ℓ p.rep
      (fun i => hmem _ _ (Projectivization.mk_rep p) i)
      (hc _ hmem _ _ (Projectivization.mk_rep p)) ≃ₗ[K] K) :
    localPointMultiplicity n K G ℓ hc p = 1 := by
  have hp : p ∈ locLocusFinset n K G hfin :=
    (mem_locLocusFinset n K G hfin _).mpr hmem
  have hloc := hlocalLocal n K G ℓ hfin hc p hp
  rw [hloc]
  exact (LinearEquiv.finrank_eq hequiv).trans (Module.finrank_self K)

/-- Smooth-point mult-`1` with `hequiv` discharged in-file from a trivial
local maximal ideal (via `hlocBundle`).

Conditional on exactly `[hmem, hfin, hmax]`.

## References

* This module, `Appendix_FixedPoint.BezoutChain.hlocalLocal`,
  `Appendix_FixedPoint.BezoutChain.mem_locLocusFinset`,
  `Appendix_FixedPoint.BezoutChain.hlocBundle`. -/
theorem mult1_smooth_of_maximal_bot (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hc : ∀ (p : Projectivization K (Fin (n + 2) → K))
      (_ : p ∈ vanishingLocus n K G)
      (v : Fin (n + 2) → K) (hv : v ≠ 0),
      Projectivization.mk K v hv = p →
        MvPolynomial.eval v (mkLin n K ℓ) ≠ 0)
    (p : Projectivization K (Fin (n + 2) → K))
    (_hs : IsSmoothPoint n K G p)
    (hmem : p ∈ vanishingLocus n K G)
    (hfin : (vanishingLocus n K G).Finite)
    (hmax : IsLocalRing.maximalIdeal (locRingAt n K G ℓ p.rep
      (fun i => hmem _ _ (Projectivization.mk_rep p) i)
      (hc _ hmem _ _ (Projectivization.mk_rep p))) = ⊥) :
    localPointMultiplicity n K G ℓ hc p = 1 := by
  have hp : p ∈ locLocusFinset n K G hfin :=
    (mem_locLocusFinset n K G hfin _).mpr hmem
  have hloc := hlocalLocal n K G ℓ hfin hc p hp
  rw [hloc]
  exact hlocBundle n K G ℓ _ _ _ hmax

/-- Transport-wired smooth-point mult-`1` in local form (general-`p` mirror
of
`SpuriousMultiplicityOne.mult1_spurious_of_hfin_transport`,
cited by name, never imported): the consumer `hmult` shape from locus finiteness
plus the two
transport equations into a base `hequiv` — `hchart` (chart `ℓ ↦ ℓ₂` at
`p.rep`, discharge route `hchart_of_iso_local` from `HmultChartCompatIso`)
and `hrep` (representative `p.rep ↦ w` in chart `ℓ₂`). The base-chart
nonvanishing `hℓ₂` at `p.rep` is an explicit binder (at the distinguished
point the sibling proves it in-file as `hℓdist_at_rep`; at general `p` it
is residual). Proof-term mismatches are absorbed by proof irrelevance in
`exact`, per the sibling proof.

Conditional on exactly `[hmem, hfin, hequiv-at-base, hchart, hrep]`
(`hℓ₂` is equation data, not a condition).

## References

* This module, `Appendix_FixedPoint.BezoutChain.hlocalLocal`,
  `Appendix_FixedPoint.BezoutChain.mem_locLocusFinset`.
* `Mathlib/LinearAlgebra/Dimension/Finrank.lean`, `LinearEquiv.finrank_eq`,
  `Module.finrank_self`. -/
theorem mult1_smooth_of_transport (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hc : ∀ (p : Projectivization K (Fin (n + 2) → K))
      (_ : p ∈ vanishingLocus n K G)
      (v : Fin (n + 2) → K) (hv : v ≠ 0),
      Projectivization.mk K v hv = p →
        MvPolynomial.eval v (mkLin n K ℓ) ≠ 0)
    (p : Projectivization K (Fin (n + 2) → K))
    (_hs : IsSmoothPoint n K G p)
    (hmem : p ∈ vanishingLocus n K G)
    (hfin : (vanishingLocus n K G).Finite)
    (ℓ₂ : Fin (n + 2) → K) (w : Fin (n + 2) → K)
    (hvGw : ∀ i, MvPolynomial.eval w (G i) = 0)
    (hℓw : MvPolynomial.eval w (mkLin n K ℓ₂) ≠ 0)
    (hℓ₂ : MvPolynomial.eval p.rep (mkLin n K ℓ₂) ≠ 0)
    (hequiv : locRingAt n K G ℓ₂ w hvGw hℓw ≃ₗ[K] K)
    (hchart : localMultiplicity n K G ℓ p.rep
        (fun i => hmem _ _ (Projectivization.mk_rep p) i)
        (hc _ hmem _ _ (Projectivization.mk_rep p))
      = localMultiplicity n K G ℓ₂ p.rep
        (fun i => hmem _ _ (Projectivization.mk_rep p) i) hℓ₂)
    (hrep : localMultiplicity n K G ℓ₂ p.rep
        (fun i => hmem _ _ (Projectivization.mk_rep p) i) hℓ₂
      = localMultiplicity n K G ℓ₂ w hvGw hℓw) :
    localPointMultiplicity n K G ℓ hc p = 1 := by
  have hp : p ∈ locLocusFinset n K G hfin :=
    (mem_locLocusFinset n K G hfin _).mpr hmem
  have hloc := hlocalLocal n K G ℓ hfin hc p hp
  rw [hloc]
  exact hchart.trans
    (hrep.trans ((LinearEquiv.finrank_eq hequiv).trans (Module.finrank_self K)))

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
