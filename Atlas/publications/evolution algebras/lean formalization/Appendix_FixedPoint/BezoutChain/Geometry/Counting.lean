/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Statement.Definitions
import Appendix_FixedPoint.BezoutChain.Geometry.Elimination
import Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.ResultantLemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Regular.SMul
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Set.Finite.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Order.Disjoint
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Spectrum.Maximal.Defs

/-!
# Counting points with multiplicity

This module proves the interface items
(points, multiplicities, corollary, merge helpers):

* `finite_locus`: `IsZeroDimensional` forces the projective locus finite.
* `regular_chartForm_of_zeroDim`: threads `finite_locus` back into the R1
  toolkit (`exists_regular_chartForm`'s `hfin` slot) explicitly.
* `locus_nonempty`: zero-dimensional locus is nonempty (C4 shape).
* `mult_chart_independent`: chart multiplicities agree on overlaps (Lemma C2).
* `sum_mult_eq_chart_length`: the multiplicity sum is the chart length.
* `mult_pos_of_mem`, `smooth_implies_mult_one`: positivity and the smooth
  value (needed by the §3 reconciliation).
* `smooth_of_negId_linear_parts`: Jacobian `[-I | 0]` shape gives
  `IsSmoothPoint` (needed by the §3 reconciliation).
* `infinite_locus_of_not_zeroDim`: the reconciliation case split.
* `exists_another_point_of_counting_data`: the C5 assembly — the
  counting step from the above pieces with explicit hypotheses per feed.
* Stabilization-lane consumers (`hdisj_of_dataAbove`, `hfilter_of_data`, and
  the reduced-input feeders): `hdisj` above `0` from `CfsecDisjointData` with
  `hstab`/`hvan` discharged.
* BridgeToFixedPoint/vanishing closings (`hdisjAbove_of_quadrics`, `hvan_final`,
  `chart_bridge_eq_of_final`, and the `*_final` rewires): unconditional on
  Statement's own `[hG, hreg, hZd]`.
* `cfsec_disjoint_zero`, `hfilter_of_bridge`, `section_length_eq_sum_pieces`,
  `chart_length_eq_sum_pieces`, `sum_mult_eq_sum_pieces`: the finite-length
  bridge (counting link A) — the `hdisj` base case, the `hfilter` shape for
  `length_section_eq_two_pow`, length additivity (`hlen`) on the section and
  chart sides, and the feeder through `sum_mult_eq_chart_length`.

## Added hypotheses

`localPointMultiplicity` is now the canonical local form (local `K`-length
at `p.rep`, `0` off the locus; the preliminary global-length
`pointMultiplicity` survives only as a backward-compat alias in
`Statement.Definitions`) and the chart filtration follow-ups
(`chart_filtration_exhaust`, `chart_graded_piece`) have not proved, so the
genuinely geometric contents are taken as explicit named hypotheses, each
owned by the strand that discharges it:

1. `finite_locus` takes `hcover : ∃ t : Finset _, vanishingLocus n K G ⊆ ↑t`
   (chart-cover finiteness, owned in ChartFiltration: the locus in the
   union of charts is covered by the finitely many maximal ideals of the
   Artinian section). `hZd` is retained for interface stability and is consumed
   when `hcover` is discharged (via `section_artinian`).
2. `locus_nonempty` takes the section data `ℓ` (extra argument, reported),
   `hS : Nontrivial`, `hreg` (R1-regularity), `hA : Nonempty (MaximalSpectrum …)`
   (section-nontriviality input: `S/ℓS ≠ 0 ⟹ MaxSpec ≠ ∅`, discharged by
   `CountingHandoff.section_maxSpec_nonempty` from `hG0` alone; retained for
   interface stability), and `hlift : (vanishingLocus n K G).Nonempty` (bare
   locus-nonemptiness, no uniformity over `MaxSpec`). The old ∀-shaped `hlift`
   (`∀ M : MaximalSpectrum …, locus.Nonempty`) is dropped: pulling `M` back
   can yield the origin (see `CountingHandoff` G-lift), so no discharge path
   existed. The ∃ shape is satisfiable globally via
   `ProjectiveLocus.mem_locus_of_nonzero_zero` from a nonzero common zero
   (projective dimension theorem, still open). `hZd` is retained for interface
   stability.
3. `mult_chart_independent` takes the ∀-p R1-nonvanishing `hc₁`/`hc₂`
   (required by the local form `localPointMultiplicity`; subsuming the old
   per-point overlap hypotheses of the same names) and `hloceq`
   (chart-independence of the representative-local lengths,
   ChartFiltration/LocalMultiplicity-owned). The old global-bridge inputs
   `hlin₁`/`hlin₂`/`hlen` are dropped (reported): the local lengths neither
   imply nor follow from the global section-length identity, so no proof
   route through `chart_bridge` exists. `hreg₁`/`hreg₂` are retained for
   interface stability (R1 context for `hloceq`'s discharge).
4. `sum_mult_eq_chart_length` takes the R1-nonvanishing `hc` (required by
   the local form), the locus finiteness `hfin`, an explicit
   local-multiplicity function `w` with `hlocal` (identification of the
   canonical `localPointMultiplicity` with the local lengths, discharged by
   `LocalMultiplicity.hlocalLocal` with `w p := localMultiplicity` at `p.rep` —
   cited, not imported) and `hadd` (Artinian length additivity over the
   maximal spectrum, discharged by `LocalMultiplicity.haddLocal` with
   `w := localPointMultiplicity` modulo `hdecomp` — cited, not imported).
5. `mult_pos_of_mem` takes `hmem` (locus membership, now consumed: it
   supplies the representative equations) and the local positivity `hpos:
   0 < localMultiplicity … p.rep …` (discharged by `LocalMultiplicity.hposLocalAt`
   modulo `hfinLoc` — cited, not imported).
6. `smooth_implies_mult_one` takes `hmem` (locus membership, now consumed)
   and the local value `hloc : localMultiplicity … p.rep … = 1`
   (discharged by `LocalMultiplicity.hlocLocal`/`hlocBundle` modulo the
   regular-local input — cited, not imported); `hs` is retained for
   interface stability.
7. `infinite_locus_of_not_zeroDim` takes `hcontra : Finite → IsZeroDimensional`
   (dimension–finiteness converse input, owned in ChartFiltration).
8. `smooth_of_negId_linear_parts` needs no extra hypothesis beyond the
   Jacobian `[-I | 0]` shape `hjac` (plus `hmem`, retained for interface
   stability although `IsSmoothPoint` does not bundle membership).
9. The finite-length bridge (counting link A) takes `hdisj`
   (piece-disjointness of `Cfsec` against `sectionPiece`, Counting-owned;
   only level `0` is discharged in-file, by `cfsec_disjoint_zero`),
   `hstab`/`hvan` (the Artinian stabilization bound and piece vanishing,
   Counting-owned), and `hlin` (the chart–section identification, i.e.
   `chart_bridge`'s input, ChartFiltration-owned). From these, `hlen`
   (section/chart length additivity, each for the bound `B'` supplied by the
   Artinian input rather than the input `B`) is proved
   (`section_length_eq_sum_pieces`, `chart_length_eq_sum_pieces`) and fed
   through `sum_mult_eq_chart_length` (`sum_mult_eq_sum_pieces`); the `hfilter` shape consumed by
   `length_section_eq_two_pow` is `hfilter_of_bridge`. `hadd` itself is
   discharged by `LocalMultiplicity.haddLocal` with `w := localPointMultiplicity`,
   modulo `hdecomp` (cited, not imported).
10. `exists_another_point_of_counting_data` (C5 assembly) takes one explicit
    hypothesis per feed — `hfin` (L-COVER), `hmult`
    (L-SMOOTH-VAL), `hsum` (L-LOCAL/L-ADD), `hbridge` (L-HLIN), `htotal`
    (section count), `hpos` (L-POS, subsumed by the singleton collapse but
    retained) — all now in local form, each discharged by the theorem named
    in its docstring — plus `hc` (R1 nonvanishing, required by the local form).

## `FixedPointFromBezout` non-import

`FixedPointFromBezout.lean` is not imported for its
`distinguished_smooth` linear-independence fact: its fact concerns
functions `Fin n → K → K` while the
Jacobian here is a `Matrix (Fin (n+1)) (Fin (n+2)) K` — the shapes do not match,
so no direct reuse is possible. The row-independence argument is instead proved
directly below,
following the same `Fintype.linearIndependent_iff` + `Pi.single`-evaluation
pattern.

## References

Mathlib v4.34.0 has no degree-of-variety or intersection-multiplicity API; the
results below are assembled from finiteness, maximal-spectrum, finrank, and
matrix-rank API. Per-declaration `## References` subsections cite the exact
module path and declaration name, each verified in-tree.

## Standing context (routine binders)

Named once here; per-decl docstrings below repeat GRADE verdicts and name only
substantive non-routine premises.

* `hS : Nontrivial (coneQuotient n K G)` — section nontriviality.
* `hZd : IsZeroDimensional n K G` — the cone-dimension input.
* `hreg` — R1 section regularity (`IsSMulRegular` on the cone).
* `hc` — ∀-point R1 chart nonvanishing
  (`∀ p ∈ locus, ∀ v ≠ 0, mk v = p → eval v (mkLin …) ≠ 0`).
* `hfin : (vanishingLocus n K G).Finite` — locus finiteness.
* `hG : ∀ i, (G i).IsHomogeneous 2` — the quadric-system input.
* Counting-link inputs: `hcover`, `hcontra`, `hlift`, `hA`.
* Filtration/bridge inputs: `hdisj`, `hstab`, `hvan`, `hfilter`, `hlen`, `hlin`.
* LocalMultiplicity-owned inputs: `hlocal`, `hadd`, `hpos`, `hloc`.
* C5 assembly feeds: `hfin`, `hmult`, `hsum`, `hbridge`, `htotal`, `hpos` (+`hc`).
* Instances: `[Field K]` throughout; `[IsAlgClosed K]` where the
  Nullstellensatz feeds in; `[Fintype …]` at the row-independence argument.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
open scoped BigOperators

/-! ## The locus as a finset -/

/-- The projective locus as a finset, from a finiteness proof (used by the
multiplicity sum).

## References

* `Mathlib/Data/Set/Finite/Basic.lean`, `Set.Finite.toFinset`
  (`protected noncomputable def Finite.toFinset (h : s.Finite) : Finset α`). -/
noncomputable def locusFinset (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hfin : (vanishingLocus n K G).Finite) :
    Finset (Projectivization K (Fin (n + 2) → K)) :=
  hfin.toFinset

/-- Membership in `locusFinset` is membership in the locus.

## References

* `Mathlib/Data/Set/Finite/Basic.lean`, `Set.Finite.mem_toFinset`
  (`protected theorem mem_toFinset : a ∈ hs.toFinset ↔ a ∈ s`). -/
theorem mem_locusFinset (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hfin : (vanishingLocus n K G).Finite)
    (p : Projectivization K (Fin (n + 2) → K)) :
    p ∈ locusFinset n K G hfin ↔ p ∈ vanishingLocus n K G :=
  hfin.mem_toFinset

/-! ## Finiteness from zero-dimensionality -/

/-- `finite_locus`: a zero-dimensional locus
is finite. The chart-cover input `hcover` is the ChartFiltration content
(the locus is covered by the finitely many maximal ideals of the Artinian
section); `hZd` is retained for interface stability and is consumed when
`hcover` is discharged via `section_artinian`.

## References

* `Mathlib/Data/Set/Finite/Basic.lean`, `Finset.finite_toSet`
  (`theorem finite_toSet (s : Finset α) : (s : Set α).Finite`),
  `Set.Finite.subset`
  (`theorem Finite.subset (hs : s.Finite) (ht : t ⊆ s) : t.Finite`). -/
theorem finite_locus (n : ℕ) (K : Type*) [Field K] [IsAlgClosed K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (_hZd : IsZeroDimensional n K G)
    (hcover : ∃ t : Finset (Projectivization K (Fin (n + 2) → K)),
      vanishingLocus n K G ⊆ ↑t) :
    (vanishingLocus n K G).Finite := by
  obtain ⟨t, ht⟩ := hcover
  exact (Finset.finite_toSet t).subset ht

/-- Threading `finite_locus` back into the R1 toolkit: the `hfin` hypothesis of
`exists_regular_chartForm` is discharged by `finite_locus`, so a
zero-dimensional locus (plus the chart-cover and avoidance inputs) yields the
regular chart form explicitly.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Regularity.Avoid.ResultantLemmas`,
  `Appendix_FixedPoint.BezoutChain.exists_regular_chartForm` (whose `hfin` slot `finite_locus`
  fills). -/
theorem regular_chartForm_of_zeroDim (n : ℕ) (K : Type*) [Field K] [IsAlgClosed K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hS : Nontrivial (coneQuotient n K G))
    (hZd : IsZeroDimensional n K G)
    (hcover : ∃ t : Finset (Projectivization K (Fin (n + 2) → K)),
      vanishingLocus n K G ⊆ ↑t)
    (havoid : ∀ P ∈ associatedPrimes (coneQuotient n K G) (coneQuotient n K G),
      Submodule.comap (coeffToCone n K G)
        (Submodule.restrictScalars K
          (P : Submodule (coneQuotient n K G) (coneQuotient n K G))) ≠ ⊤) :
    ∃ ℓ : Fin (n + 2) → K,
      IsSMulRegular (coneQuotient n K G)
        (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ∧
      ∀ p ∈ vanishingLocus n K G, ∀ (v : Fin (n + 2) → K) (hv : v ≠ 0),
        Projectivization.mk K v hv = p → MvPolynomial.eval v (mkLin n K ℓ) ≠ 0 :=
  exists_regular_chartForm n K G hS (finite_locus n K G hZd hcover) havoid

/-! ## Nonemptiness (C4 shape) -/

/-- `locus_nonempty` (C4): a zero-dimensional
locus is nonempty. The locus-nonemptiness itself is taken as the ∃-shaped
`hlift : (vanishingLocus n K G).Nonempty` (no uniformity over `MaxSpec`);
`hA` (the section has a maximal ideal, via
`CountingHandoff.section_maxSpec_nonempty`) is retained for interface
stability. `hS`, `hreg`, and `hZd` are likewise retained for interface
stability (provably unused in this proof: only `hA`/`hlift` are consumed,
`hA` trivially).

Why ∃ and not ∀: the old ∀-shaped `hlift`
(`∀ M : MaximalSpectrum …, locus.Nonempty`) had no sketched discharge path —
pulling `M` back along the two quotient maps to a maximal ideal of
`MvPolynomial` and applying the affine weak Nullstellensatz can yield the
origin, which is not a projective point (concrete obstruction `n = 0`,
`G₀ = X₀`, `ℓ = X₁`: see `CountingHandoff` G-lift and the `ProjectiveLocus`
obstruction note). The ∃ shape drops the doomed uniformity: it is discharged
globally (nonzero common zero ⟹ projective point, via
`ProjectiveLocus.mem_locus_of_nonzero_zero`), i.e. the projective dimension
theorem for `n + 1` homogeneous equations in `n + 2` unknowns. The C5
assembly (`Statement.Statement.exists_another_point_of_smooth_point`) consumes only
locus existence (a chart point plus the C5 count), never uniformity over `M`,
so ∃ suffices.

Pinned maximal-ideal↔`K`-point lemma (in-tree, cited for the global discharge
route of `hlift`): `MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton`
(`Mathlib/RingTheory/Nullstellensatz.lean`): over `IsAlgClosed K` with
`Finite σ`, `I.IsMaximal ↔ ∃ x : σ → K, I = vanishingIdeal K {x}`. Note there
is no ready-made maximal-ideal↔projective-`K`-point equivalence in-tree (the
Nullstellensatz API is affine, in terms of `MvPolynomial.zeroLocus` /
`vanishingIdeal`); the global nonzero-zero existence (projective dimension
theorem) is the remaining content of `hlift`,
owned in ChartFiltration.

## References

* `Mathlib/RingTheory/Spectrum/Maximal/Defs.lean`, `MaximalSpectrum`
  (`structure MaximalSpectrum (R : Type*) [CommSemiring R]` with `asIdeal`,
  `isMaximal`).
* `Mathlib/RingTheory/Nullstellensatz.lean`,
  `MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton` (discharge path). -/
theorem locus_nonempty (n : ℕ) (K : Type*) [Field K] [IsAlgClosed K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (_hZd : IsZeroDimensional n K G)
    (_hS : Nontrivial (coneQuotient n K G))
    (_hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    (hA : Nonempty (MaximalSpectrum (sectionQuotient n K G ℓ)))
    (hlift : (vanishingLocus n K G).Nonempty) :
    (vanishingLocus n K G).Nonempty := by
  obtain ⟨_M⟩ := hA
  exact hlift

/-! ## Chart-independence of multiplicity (Lemma C2 piece) -/

/-- `mult_chart_independent` (Lemma C2 piece):
multiplicities computed in two charts agree on the overlap. The ∀-p
R1-nonvanishing inputs `hc₁`/`hc₂` are required by the local form
`localPointMultiplicity` (subsuming the old per-point overlap hypotheses of
the same names); `hloceq` is chart-independence of the
representative-local lengths (ChartFiltration/LocalMultiplicity-owned).
`hreg₁`/`hreg₂` are retained for interface stability (R1 context for
`hloceq`'s discharge). The old global-bridge inputs `hlin₁`/`hlin₂` (the
`chart_bridge` filtration inputs) and `hlen` (ℓ-independence of the section
length) are dropped (reported): with the local form no proof route through
the global `chart_bridge` exists.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Statement.Definitions`,
  `Appendix_FixedPoint.BezoutChain.localPointMultiplicity`,
  `Appendix_FixedPoint.BezoutChain.localMultiplicity`. -/
theorem mult_chart_independent (n : ℕ) (K : Type*) [Field K] [IsAlgClosed K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ₁ ℓ₂ : Fin (n + 2) → K)
    (hc₁ : ∀ (p : Projectivization K (Fin (n + 2) → K))
      (_ : p ∈ vanishingLocus n K G)
      (v : Fin (n + 2) → K) (hv : v ≠ 0),
      Projectivization.mk K v hv = p → MvPolynomial.eval v (mkLin n K ℓ₁) ≠ 0)
    (hc₂ : ∀ (p : Projectivization K (Fin (n + 2) → K))
      (_ : p ∈ vanishingLocus n K G)
      (v : Fin (n + 2) → K) (hv : v ≠ 0),
      Projectivization.mk K v hv = p → MvPolynomial.eval v (mkLin n K ℓ₂) ≠ 0)
    (p : Projectivization K (Fin (n + 2) → K))
    (_hreg₁ : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ₁)))
    (_hreg₂ : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ₂)))
    (hloceq : ∀ (v : Fin (n + 2) → K)
      (hvG₁ : ∀ i, MvPolynomial.eval v (G i) = 0)
      (hℓ₁ : MvPolynomial.eval v (mkLin n K ℓ₁) ≠ 0)
      (hvG₂ : ∀ i, MvPolynomial.eval v (G i) = 0)
      (hℓ₂ : MvPolynomial.eval v (mkLin n K ℓ₂) ≠ 0),
      localMultiplicity n K G ℓ₁ v hvG₁ hℓ₁
        = localMultiplicity n K G ℓ₂ v hvG₂ hℓ₂) :
    localPointMultiplicity n K G ℓ₁ hc₁ p
      = localPointMultiplicity n K G ℓ₂ hc₂ p := by
  classical
  unfold localPointMultiplicity
  by_cases h : p ∈ vanishingLocus n K G
  · rw [dite_eq_left h, dite_eq_left h]
    exact hloceq p.rep _ _ _ _
  · rw [dite_eq_right h, dite_eq_right h]

/-! ## The multiplicity sum -/

/-- `sum_mult_eq_chart_length`: the
multiplicities over the locus sum to the chart length. The local
identification `hlocal` (discharged by `LocalMultiplicity.hlocalLocal` with
`w p := localMultiplicity` at `p.rep`) and the Artinian additivity `hadd`
(discharged by `LocalMultiplicity.haddLocal` with `w := localPointMultiplicity`
modulo `hdecomp`) are taken as explicit hypotheses (cited, not imported:
no new import edge). `hc` is the R1-nonvanishing required by the local form.

## References

* `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`,
  `Finset.sum_congr`
  (`theorem sum_congr (h₁: s₁ = s₂) (h₂: ∀ x ∈ s₂, f x = g x):
    s₁.sum f = s₂.sum g`, via `to_additive` from `prod_congr`). -/
theorem sum_mult_eq_chart_length (n : ℕ) (K : Type*) [Field K] [IsAlgClosed K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hc : ∀ (p : Projectivization K (Fin (n + 2) → K))
      (_ : p ∈ vanishingLocus n K G)
      (v : Fin (n + 2) → K) (hv : v ≠ 0),
      Projectivization.mk K v hv = p → MvPolynomial.eval v (mkLin n K ℓ) ≠ 0)
    (hfin : (vanishingLocus n K G).Finite)
    (w : Projectivization K (Fin (n + 2) → K) → ℕ)
    (hlocal : ∀ p ∈ locusFinset n K G hfin,
      localPointMultiplicity n K G ℓ hc p = w p)
    (hadd : ∑ p ∈ locusFinset n K G hfin, w p
      = Module.finrank K (chartRing n K G ℓ)) :
    ∑ p ∈ locusFinset n K G hfin, localPointMultiplicity n K G ℓ hc p
      = Module.finrank K (chartRing n K G ℓ) :=
  (Finset.sum_congr rfl (fun p hp => hlocal p hp)).trans hadd

/-! ## Finite-length bridge (counting link A) -/

/-- The `hdisj` input of `cfsec_hfilter` at level `0`: the empty join is
disjoint from every piece. This is the only level of piece-disjointness
discharged in-file; `d > 0` stays an explicit hypothesis (residual R-disj:
needs the homogeneous-cofactor geometry, cf. `DescentData`).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.Cfsec`,
  `Appendix_FixedPoint.BezoutChain.cfsec_zero`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ChartFiltration`,
  `Appendix_FixedPoint.BezoutChain.sectionPiece`.
* `Mathlib/Order/Disjoint.lean`, `disjoint_bot_left`
  (`theorem disjoint_bot_left : Disjoint ⊥ a`). -/
theorem cfsec_disjoint_zero (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) :
    Disjoint (Cfsec n K G ℓ 0) (sectionPiece n K G ℓ 0) := by
  rw [cfsec_zero]
  exact disjoint_bot_left

/-- The `hfilter` shape consumed by `length_section_eq_two_pow`, from the
Counting finite-length inputs: piece-disjointness `hdisj`, the Artinian
bound `B` with stabilization `hstab` and vanishing `hvan`. The ambient
finiteness instance `cfsec_hfilter` needs is discharged from `hreg` + `hZd`
by `section_finite_of_artinian`, so this is the exact handoff from the bridge
hypotheses to the HilbertFunctionCount assembly (with `F := Fsec …`).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.cfsec_hfilter`,
  `Appendix_FixedPoint.BezoutChain.Fsec`,
  `Appendix_FixedPoint.BezoutChain.section_finite_of_artinian` (this module's imports —
  unlike `Statement.Statement` (import would cycle, see the C5 docstring) and
  `BridgeToFixedPoint.FixedPointFromBezout` (declined per the header note), which stay
  cited-only). -/
theorem hfilter_of_bridge (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (B : ℕ)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    (hZd : IsZeroDimensional n K G)
    (hdisj : ∀ d, d ≤ B → Disjoint (Cfsec n K G ℓ d) (sectionPiece n K G ℓ d))
    (hstab : Cfsec n K G ℓ (B + 1) = ⊤)
    (hvan : ∀ d, B < d → Fsec n K G ℓ d = 0) :
    ∃ (B' : ℕ) (Cf : ℕ → Submodule K (sectionQuotient n K G ℓ)),
      Cf 0 = ⊥ ∧ Cf (B' + 1) = ⊤ ∧
      (∀ d, d ≤ B' →
        Module.finrank K ↥(Cf (d + 1)) = Module.finrank K ↥(Cf d)
          + Fsec n K G ℓ d) ∧
      ∀ d, B' < d → Fsec n K G ℓ d = 0 :=
  @cfsec_hfilter n K _ G ℓ B (section_finite_of_artinian n K G ℓ hreg hZd)
    hdisj hstab hvan

/-- Length additivity on the section (`hlen`, section side): under `hreg` +
`hZd` (via `section_finite_of_artinian`) the section length is the sum of the
filtration-piece dimensions for some bound `B'`, conditional on the bridge
inputs `hdisj` / `hstab` / `hvan` (through `hfilter_of_bridge`'s shape,
telescoped by `section_finrank_telescope`). The bound is existential —
`cfsec_hfilter` supplies it from the Artinian input — rather than the input
`B`, so no stabilization identification is needed.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.cfsec_hfilter`,
  `Appendix_FixedPoint.BezoutChain.section_finrank_telescope`,
  `Appendix_FixedPoint.BezoutChain.Fsec`,
  `Appendix_FixedPoint.BezoutChain.section_finite_of_artinian`.
* `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`, `Finset.sum`
  (the `∑ d ∈ Finset.range (B' + 1), …` notation). -/
theorem section_length_eq_sum_pieces (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (B : ℕ)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    (hZd : IsZeroDimensional n K G)
    (hdisj : ∀ d, d ≤ B → Disjoint (Cfsec n K G ℓ d) (sectionPiece n K G ℓ d))
    (hstab : Cfsec n K G ℓ (B + 1) = ⊤)
    (hvan : ∀ d, B < d → Fsec n K G ℓ d = 0) :
    ∃ B', Module.finrank K (sectionQuotient n K G ℓ)
      = ∑ d ∈ Finset.range (B' + 1), Fsec n K G ℓ d := by
  obtain ⟨B', Cf, hC0, hCtop, hCstep, _⟩ :=
    @cfsec_hfilter n K _ G ℓ B (section_finite_of_artinian n K G ℓ hreg hZd)
      hdisj hstab hvan
  exact ⟨B', section_finrank_telescope n K G ℓ (Fsec n K G ℓ) B' Cf hC0 hCtop
    hCstep⟩

/-- Length additivity on the chart (`hlen`, chart side): the chart length is
the same piece sum, via the chart–section identification `hlin`
(`chart_bridge`'s input, ChartFiltration-owned).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.Elimination`,
  `Appendix_FixedPoint.BezoutChain.chart_bridge`
  (`LinearEquiv.finrank_eq`).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.Counting`,
  `Appendix_FixedPoint.BezoutChain.section_length_eq_sum_pieces` (proved above). -/
theorem chart_length_eq_sum_pieces (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (B : ℕ)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    (hZd : IsZeroDimensional n K G)
    (hdisj : ∀ d, d ≤ B → Disjoint (Cfsec n K G ℓ d) (sectionPiece n K G ℓ d))
    (hstab : Cfsec n K G ℓ (B + 1) = ⊤)
    (hvan : ∀ d, B < d → Fsec n K G ℓ d = 0)
    (hlin : (chartRing n K G ℓ) ≃ₗ[K] (sectionQuotient n K G ℓ)) :
    ∃ B', Module.finrank K (chartRing n K G ℓ)
      = ∑ d ∈ Finset.range (B' + 1), Fsec n K G ℓ d := by
  obtain ⟨B', hB'⟩ :=
    section_length_eq_sum_pieces n K G ℓ B hreg hZd hdisj hstab hvan
  exact ⟨B', (chart_bridge n K G ℓ hreg hlin).trans hB'⟩

/-- Feeder through `sum_mult_eq_chart_length`: the multiplicity sum over the
locus equals the filtration-piece sum for some bound `B'`, conditional on
that theorem's `hlocal` + `hadd` plus the bridge inputs (`hdisj` / `hstab` /
`hvan` / `hlin`, with `hreg` + `hZd` for ambient finiteness). The `hadd`
slot itself is discharged by `LocalMultiplicity.haddLocal` with
`w := localPointMultiplicity`, modulo `hdecomp` (cited, not imported); the
`2 ^ (n + 1)` value of the right-hand side is `length_section_eq_two_pow`
applied to the `hfilter_of_bridge` shape. `hc` is the R1-nonvanishing
required by the local form.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.Counting`,
  `Appendix_FixedPoint.BezoutChain.sum_mult_eq_chart_length` (whose `hlocal`/`hadd` slots this feeds
  through), `Appendix_FixedPoint.BezoutChain.chart_length_eq_sum_pieces` (proved above).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.LocalMultiplicity`,
  `Appendix_FixedPoint.BezoutChain.haddLocal`
  (discharge route for `hadd`, cited not imported).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.length_section_eq_two_pow` (value of the piece sum, via
  `Appendix_FixedPoint.BezoutChain.hfilter_of_bridge`). -/
theorem sum_mult_eq_sum_pieces (n : ℕ) (K : Type*) [Field K] [IsAlgClosed K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (B : ℕ)
    (hc : ∀ (p : Projectivization K (Fin (n + 2) → K))
      (_ : p ∈ vanishingLocus n K G)
      (v : Fin (n + 2) → K) (hv : v ≠ 0),
      Projectivization.mk K v hv = p → MvPolynomial.eval v (mkLin n K ℓ) ≠ 0)
    (hfin : (vanishingLocus n K G).Finite)
    (w : Projectivization K (Fin (n + 2) → K) → ℕ)
    (hlocal : ∀ p ∈ locusFinset n K G hfin,
      localPointMultiplicity n K G ℓ hc p = w p)
    (hadd : ∑ p ∈ locusFinset n K G hfin, w p
      = Module.finrank K (chartRing n K G ℓ))
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    (hZd : IsZeroDimensional n K G)
    (hdisj : ∀ d, d ≤ B → Disjoint (Cfsec n K G ℓ d) (sectionPiece n K G ℓ d))
    (hstab : Cfsec n K G ℓ (B + 1) = ⊤)
    (hvan : ∀ d, B < d → Fsec n K G ℓ d = 0)
    (hlin : (chartRing n K G ℓ) ≃ₗ[K] (sectionQuotient n K G ℓ)) :
    ∃ B', ∑ p ∈ locusFinset n K G hfin, localPointMultiplicity n K G ℓ hc p
      = ∑ d ∈ Finset.range (B' + 1), Fsec n K G ℓ d := by
  obtain ⟨B', hB'⟩ :=
    chart_length_eq_sum_pieces n K G ℓ B hreg hZd hdisj hstab hvan hlin
  exact ⟨B', (sum_mult_eq_chart_length n K G ℓ hc hfin w hlocal hadd).trans hB'⟩

/-! ## Positivity and the smooth value -/

/-- `mult_pos_of_mem`: the multiplicity at a
locus point is positive. `hmem` supplies the representative equations;
`hpos` is the local positivity input (discharged by `LocalMultiplicity.hposLocalAt`
modulo `hfinLoc` — cited, not imported).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Statement.Definitions`,
  `Appendix_FixedPoint.BezoutChain.localPointMultiplicity`,
  `Appendix_FixedPoint.BezoutChain.localMultiplicity`. -/
theorem mult_pos_of_mem (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hc : ∀ (p : Projectivization K (Fin (n + 2) → K))
      (_ : p ∈ vanishingLocus n K G)
      (v : Fin (n + 2) → K) (hv : v ≠ 0),
      Projectivization.mk K v hv = p → MvPolynomial.eval v (mkLin n K ℓ) ≠ 0)
    (p : Projectivization K (Fin (n + 2) → K))
    (hmem : p ∈ vanishingLocus n K G)
    (hpos : 0 < localMultiplicity n K G ℓ p.rep
      (fun i => hmem p.rep p.rep_nonzero (Projectivization.mk_rep p) i)
      (hc p hmem p.rep p.rep_nonzero (Projectivization.mk_rep p))) :
    1 ≤ localPointMultiplicity n K G ℓ hc p := by
  classical
  unfold localPointMultiplicity
  rw [dite_eq_left hmem]
  exact hpos

/-- `smooth_implies_mult_one` (needed by the
reconciliation): a smooth locus point has multiplicity `1`. `hmem` supplies
the representative equations; the locality input `hloc` is the local value
`localMultiplicity … p.rep … = 1` (discharged by `LocalMultiplicity.hlocLocal` /
`hlocBundle` modulo the regular-local input — cited, not imported); `hs` is
retained for interface stability.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Statement.Definitions`,
  `Appendix_FixedPoint.BezoutChain.localPointMultiplicity`,
  `Appendix_FixedPoint.BezoutChain.localMultiplicity`,
  `Appendix_FixedPoint.BezoutChain.IsSmoothPoint`. -/
theorem smooth_implies_mult_one (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hc : ∀ (p : Projectivization K (Fin (n + 2) → K))
      (_ : p ∈ vanishingLocus n K G)
      (v : Fin (n + 2) → K) (hv : v ≠ 0),
      Projectivization.mk K v hv = p → MvPolynomial.eval v (mkLin n K ℓ) ≠ 0)
    (p : Projectivization K (Fin (n + 2) → K))
    (hmem : p ∈ vanishingLocus n K G)
    (_hs : IsSmoothPoint n K G p)
    (hloc : localMultiplicity n K G ℓ p.rep
      (fun i => hmem p.rep p.rep_nonzero (Projectivization.mk_rep p) i)
      (hc p hmem p.rep p.rep_nonzero (Projectivization.mk_rep p)) = 1) :
    localPointMultiplicity n K G ℓ hc p = 1 := by
  classical
  unfold localPointMultiplicity
  rw [dite_eq_left hmem]
  exact hloc

/-! ## Smoothness from the `[-I | 0]` Jacobian (reconciliation input) -/

/-- `smooth_of_negId_linear_parts` (needed by the
reconciliation): if the Jacobian of `G` at `zRep` has the `[-I | 0]` shape —
negated-identity block on the `x` (`Fin.castSucc`) columns — then the
distinguished point is smooth. The rows are (negated) distinct standard basis
vectors, hence linearly independent, so the rank is `n + 1` by
`LinearIndependent.rank_matrix`. `hmem` is retained for interface stability
(`IsSmoothPoint` does not bundle locus membership).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Statement.Definitions`,
  `Appendix_FixedPoint.BezoutChain.IsSmoothPoint`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Statement.Definitions`,
  `Appendix_FixedPoint.BezoutChain.zRep`, `Appendix_FixedPoint.BezoutChain.zRep_ne_zero`,
  `Appendix_FixedPoint.BezoutChain.distinguishedPoint`.
* `Mathlib/LinearAlgebra/Matrix/Defs.lean`, `Matrix.of`, `Matrix.of_apply`
  (`theorem of_apply (f : m → n → α) (i j) : of f i j = f i j`), `Matrix.row`
  (`def row (A : Matrix m n α) : m → n → α := A`).
* `Mathlib/LinearAlgebra/Matrix/Rank.lean`, `Matrix.rank`,
  `LinearIndependent.rank_matrix`
  (`theorem LinearIndependent.rank_matrix (h: LinearIndependent R M.row):
    M.rank = Fintype.card m`).
* `Mathlib/LinearAlgebra/LinearIndependent/Defs.lean`,
  `Fintype.linearIndependent_iff`
  (`theorem Fintype.linearIndependent_iff:
    LinearIndependent R v ↔ ∀ g: ι → R, ∑ i, g i • v i = 0 → ∀ i, g i = 0`).
* `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`, `Finset.sum_apply`,
  `Finset.sum_eq_single` (via `to_additive` from `prod_eq_single`),
  `Finset.mem_univ`.
* `Mathlib/Data/Fin/SuccPred.lean` (via `Mathlib/Data/Fin/Basic.lean`),
  `Fin.castSucc_inj` (`… ↔ …`, `simp`), `Fin.castSucc_injective`. -/
theorem smooth_of_negId_linear_parts (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (_hmem : ∀ i, MvPolynomial.eval (zRep n K) (G i) = 0)
    (hjac : ∀ (i : Fin (n + 1)) (j : Fin (n + 2)),
      MvPolynomial.eval (zRep n K) (MvPolynomial.pderiv j (G i))
        = -(if j = Fin.castSucc i then (1 : K) else 0)) :
    IsSmoothPoint n K G (distinguishedPoint n K) := by
  have hentry : ∀ (i : Fin (n + 1)) (j : Fin (n + 2)),
      (Matrix.of (fun (i : Fin (n + 1)) (j : Fin (n + 2)) =>
        MvPolynomial.eval (zRep n K) (MvPolynomial.pderiv j (G i)))).row i j
        = -(if j = Fin.castSucc i then (1 : K) else 0) :=
    fun i j => hjac i j
  have hLI : LinearIndependent K
      (Matrix.of (fun (i : Fin (n + 1)) (j : Fin (n + 2)) =>
        MvPolynomial.eval (zRep n K) (MvPolynomial.pderiv j (G i)))).row := by
    rw [Fintype.linearIndependent_iff]
    intro g hg k
    have h0 := congrFun hg (Fin.castSucc k)
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul,
      hentry] at h0
    have hsingle : (∑ i : Fin (n + 1),
          g i * (-(if Fin.castSucc k = Fin.castSucc i then (1 : K) else 0)))
        = -(g k) := by
      have hnc : ∀ i : Fin (n + 1), i ≠ k →
          ¬ (Fin.castSucc k = Fin.castSucc i) := by
        intro i hi h
        have hki : k = i := Fin.castSucc_inj.mp h
        exact hi hki.symm
      have hbase := Finset.sum_eq_single (f := fun i : Fin (n + 1) => g i *
        (-(if Fin.castSucc k = Fin.castSucc i then (1 : K) else 0))) k
        (fun i _ hi => by
          change g i * (-(if Fin.castSucc k = Fin.castSucc i then (1 : K) else 0))
            = 0
          rw [ite_eq_right (hnc i hi), neg_zero, mul_zero])
        (fun hcon => absurd (Finset.mem_univ k) hcon)
      rw [ite_eq_left rfl, mul_neg_one] at hbase
      exact hbase
    rw [hsingle] at h0
    exact neg_eq_zero.mp h0
  have hrank := LinearIndependent.rank_matrix (R := K) hLI
  rw [Fintype.card_fin] at hrank
  exact ⟨zRep n K, zRep_ne_zero n K, rfl, hrank⟩

/-! ## Infinitude without zero-dimensionality (reconciliation case split) -/

/-- `infinite_locus_of_not_zeroDim` (reconciliation
case split): a non-zero-dimensional locus is infinite. The
dimension–finiteness converse `hcontra` is owned in ChartFiltration.

## References

* `Mathlib/Basic/Finite/Defs.lean`, `Set.Infinite`
  (`protected def Infinite (s : Set α) : Prop := ¬s.Finite`). -/
theorem infinite_locus_of_not_zeroDim (n : ℕ) (K : Type*) [Field K]
    [IsAlgClosed K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (h : ¬ IsZeroDimensional n K G)
    (hcontra : (vanishingLocus n K G).Finite → IsZeroDimensional n K G) :
    (vanishingLocus n K G).Infinite :=
  fun hfin => h (hcontra hfin)

/-! ## C5 assembly: the counting step -/

/-- `exists_another_point_of_counting_data` (C5): the full
counting step — total `= 2 ^ (n+1) ≥ 2`, distinguished point
contributes exactly `1`, so a second locus point exists. The conclusion is the
binder shape of `Statement.Statement.exists_another_point_of_smooth_point`, copied
verbatim so this module never imports `Statement.Statement` (which would cycle:
`Counting → ResultantLemmas → Statement.Statement`); each missing feed is
an explicit hypothesis with its supplier:

* `hfin` ⇐ `finite_locus` (proved above) modulo L-COVER (`hcover`,
  ChartFiltration-owned; conditionally supplied by
  `ProjectiveLocus.hcover_of_chartDimZero` modulo R-dim — cited, not
  imported);
* `hmult` ⇐ `smooth_implies_mult_one` (proved above) modulo L-SMOOTH-VAL
  (`hloc`, LocalMultiplicity-owned);
* `hsum` ⇐ `sum_mult_eq_chart_length` (proved above) modulo L-LOCAL
  (`hlocal`) + L-ADD (`hadd`, ChartFiltration/LocalMultiplicity-owned);
* `hbridge` ⇐ `Elimination.chart_bridge` modulo L-HLIN (`hlin`,
  ChartFiltration-owned);
* `htotal` ⇐ `HilbertFunctionCount.length_section_eq_two_pow` (the section count,
  conditional on the R2 repair + `hfilter` — cited, not re-proved);
* `hpos` (pointwise) ⇐ `mult_pos_of_mem` (proved above) modulo L-POS
  (`hpos`, ChartFiltration-owned) — retained for
  interface stability although the proof below subsumes it (the singleton
  collapse gives the contradiction without positivity).
* `hc` is the ∀-p R1-nonvanishing required by the local form
  `localPointMultiplicity` (R1-owned, same family as
  `mult_chart_independent`'s `hc₁`/`hc₂`).

All multiplicity hypotheses are now in local form. The proof itself is pure
finset arithmetic (no geometry): if every locus point were the distinguished
point, the locus finset would be the singleton and the sum would be `1`,
contradicting `2 ≤ 2 ^ (n + 1)`.

## References

* `Mathlib/Data/Finset/Insert.lean`, `Finset.eq_singleton_iff_unique_mem`
  (`theorem eq_singleton_iff_unique_mem : s = {a} ↔ a ∈ s ∧ ∀ x ∈ s, x = a`),
  `Finset.mem_singleton` (`b ∈ {a} ↔ b = a`).
* `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`,
  `Finset.sum_singleton` (via `to_additive` from `prod_singleton`).
* `Mathlib/Algebra/Order/Monoid/Unbundled/Pow.lean`,
  `pow_le_pow_right'` (`theorem pow_le_pow_right' (ha: 1 ≤ a) (h: n ≤ m):
  a ^ n ≤ a ^ m`). -/
theorem exists_another_point_of_counting_data (n : ℕ) (K : Type*) [Field K]
    [IsAlgClosed K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hc : ∀ (p : Projectivization K (Fin (n + 2) → K))
      (_ : p ∈ vanishingLocus n K G)
      (v : Fin (n + 2) → K) (hv : v ≠ 0),
      Projectivization.mk K v hv = p → MvPolynomial.eval v (mkLin n K ℓ) ≠ 0)
    (hfin : (vanishingLocus n K G).Finite)
    (hmem : distinguishedPoint n K ∈ vanishingLocus n K G)
    (hmult : localPointMultiplicity n K G ℓ hc (distinguishedPoint n K) = 1)
    (hsum : ∑ p ∈ locusFinset n K G hfin, localPointMultiplicity n K G ℓ hc p
      = Module.finrank K (chartRing n K G ℓ))
    (hbridge : Module.finrank K (chartRing n K G ℓ) = totalDegree n K G ℓ)
    (htotal : totalDegree n K G ℓ = 2 ^ (n + 1))
    (_hpos : ∀ p ∈ locusFinset n K G hfin,
      1 ≤ localPointMultiplicity n K G ℓ hc p) :
    ∃ q : Projectivization K (Fin (n + 2) → K),
      q ∈ vanishingLocus n K G ∧ q ≠ distinguishedPoint n K := by
  have hdist : distinguishedPoint n K ∈ locusFinset n K G hfin :=
    (mem_locusFinset n K G hfin _).mpr hmem
  have h2 : 2 ≤ ∑ p ∈ locusFinset n K G hfin,
      localPointMultiplicity n K G ℓ hc p := by
    rw [hsum, hbridge, htotal]
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ (n + 1) := pow_le_pow_right' (by norm_num) (by omega)
  by_contra hcon
  push Not at hcon
  have hsub : locusFinset n K G hfin ⊆ {distinguishedPoint n K} := by
    intro p hp
    have hpmem : p ∈ vanishingLocus n K G :=
      (mem_locusFinset n K G hfin p).mp hp
    exact Finset.mem_singleton.mpr (hcon p hpmem)
  have heq : locusFinset n K G hfin = {distinguishedPoint n K} :=
    Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hdist, fun p hp => Finset.mem_singleton.mp (hsub hp)⟩
  rw [heq, Finset.sum_singleton, hmult] at h2
  exact absurd h2 (by norm_num)

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
/-! ## Stabilization-lane consumers (`hdisj` above `0`, reduced-input bridges)

This section wires the stabilization lane's `HilbertFunctionCount` closings into the
finite-length bridge:

* `cfsec_disjoint_pos_of_data`: the `d > 0` levels of `hdisj` from the
  narrowest `CfsecDisjointData` (level `0` stays `cfsec_disjoint_zero`).
  Conditional on exactly `[data at d]` (provably narrowest: the data is
  `↔`-equivalent to the goal by `cfsec_disjoint_iff_data`). No import cycle
  arises: the data and its core lemmas live in `HilbertFunctionCount` (this module's
  import), so the general case is proved there and only assembled here.
* `hdisj_of_dataAbove`: full `hdisj` from level-`0` + data above `0`.
* `hfilter_of_data`: the `hfilter` shape with stabilization discharged
  unconditionally (`cfsec_stab_section` from `hreg` + `hZd`), vanishing via
  `fsec_vanishing_of_stabAbove`, and disjointness via `hdisj_of_dataAbove`.
  Conditional on exactly `[hreg, hZd, hdata]` — the three bridge inputs
  collapse to the single disjointness-data residual plus Statement's own
  geometric hypotheses.
* `section_length_eq_sum_pieces_of_data`,
  `chart_length_eq_sum_pieces_of_data`, `sum_mult_eq_sum_pieces_of_data`:
  the length/multiplicity feeders on the same reduced inputs.

No new imports and no new edges toward `CountingHandoff`/`ProjectiveLocus`.
-/

/-- The `d > 0` levels of `hdisj` from the narrowest data (level `0` is
`cfsec_disjoint_zero`, proved above). The data is `↔`-equivalent to the goal
(`cfsec_disjoint_iff_data`), so this is provably the exact missing input.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.CfsecDisjointData`,
  `Appendix_FixedPoint.BezoutChain.cfsec_disjoint_of_data`,
  `Appendix_FixedPoint.BezoutChain.cfsec_disjoint_iff_data`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.Counting`,
  `Appendix_FixedPoint.BezoutChain.cfsec_disjoint_zero`
  (this module, the level-`0` case). -/
theorem cfsec_disjoint_pos_of_data (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (d : ℕ) (hpos : 0 < d)
    (hdata : ∀ d, 0 < d → CfsecDisjointData n K G ℓ d) :
    Disjoint (Cfsec n K G ℓ d) (sectionPiece n K G ℓ d) :=
  cfsec_disjoint_of_data n K G ℓ d (hdata d hpos)

/-- Full `hdisj` from level-`0` (`cfsec_disjoint_zero`) plus data above `0`.
Conditional on exactly `[∀ d, 0 < d → CfsecDisjointData … d]`.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.Counting`,
  `Appendix_FixedPoint.BezoutChain.cfsec_disjoint_zero`,
  `Appendix_FixedPoint.BezoutChain.cfsec_disjoint_pos_of_data` (this module). -/
theorem hdisj_of_dataAbove (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hdata : ∀ d, 0 < d → CfsecDisjointData n K G ℓ d) :
    ∀ d, Disjoint (Cfsec n K G ℓ d) (sectionPiece n K G ℓ d) := by
  intro d
  cases d with
  | zero => exact cfsec_disjoint_zero n K G ℓ
  | succ d =>
    exact cfsec_disjoint_pos_of_data n K G ℓ (d + 1)
      (Nat.zero_lt_succ d) hdata

/-- The `hfilter` shape consumed by `length_section_eq_two_pow` on reduced
inputs: stabilization is `cfsec_stab_section` (unconditional from `hreg` +
`hZd`), vanishing follows at the same bound via
`fsec_vanishing_of_stabAbove`, and disjointness is `hdisj_of_dataAbove`.
Conditional on exactly `[hreg, hZd, hdata]`.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.cfsec_stab_section`,
  `Appendix_FixedPoint.BezoutChain.fsec_vanishing_of_stabAbove`,
  `Appendix_FixedPoint.BezoutChain.section_finite_of_artinian`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.Counting`,
  `Appendix_FixedPoint.BezoutChain.hfilter_of_bridge`,
  `Appendix_FixedPoint.BezoutChain.hdisj_of_dataAbove` (this module). -/
theorem hfilter_of_data (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    (hZd : IsZeroDimensional n K G)
    (hdata : ∀ d, 0 < d → CfsecDisjointData n K G ℓ d) :
    ∃ (B' : ℕ) (Cf : ℕ → Submodule K (sectionQuotient n K G ℓ)),
      Cf 0 = ⊥ ∧ Cf (B' + 1) = ⊤ ∧
      (∀ d, d ≤ B' →
        Module.finrank K ↥(Cf (d + 1)) = Module.finrank K ↥(Cf d)
          + Fsec n K G ℓ d) ∧
      ∀ d, B' < d → Fsec n K G ℓ d = 0 := by
  obtain ⟨B, hstab⟩ := cfsec_stab_section n K G ℓ hreg hZd
  have hdisj := hdisj_of_dataAbove n K G ℓ hdata
  have hvan : ∀ d, B < d → Fsec n K G ℓ d = 0 :=
    @fsec_vanishing_of_stabAbove n K _ G ℓ B
      (section_finite_of_artinian n K G ℓ hreg hZd) hstab
      (fun d hd => hdisj d)
  exact hfilter_of_bridge n K G ℓ B hreg hZd (fun d _ => hdisj d) hstab hvan

/-- Length additivity on the section on reduced inputs (via `hfilter_of_data`
telescoped by `section_finrank_telescope`).
Conditional on exactly `[hreg, hZd, hdata]`.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.Counting`,
  `Appendix_FixedPoint.BezoutChain.hfilter_of_data`
  (this module).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.section_finrank_telescope`. -/
theorem section_length_eq_sum_pieces_of_data (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    (hZd : IsZeroDimensional n K G)
    (hdata : ∀ d, 0 < d → CfsecDisjointData n K G ℓ d) :
    ∃ B', Module.finrank K (sectionQuotient n K G ℓ)
      = ∑ d ∈ Finset.range (B' + 1), Fsec n K G ℓ d := by
  obtain ⟨B', Cf, hC0, hCtop, hCstep, _⟩ :=
    hfilter_of_data n K G ℓ hreg hZd hdata
  exact ⟨B', section_finrank_telescope n K G ℓ (Fsec n K G ℓ) B' Cf hC0 hCtop
    hCstep⟩

/-- Length additivity on the chart on reduced inputs (via the chart–section
identification `hlin`, i.e. `chart_bridge`'s input, ChartFiltration-owned).
Conditional on exactly `[hreg, hZd, hdata, hlin]`.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.Counting`,
  `Appendix_FixedPoint.BezoutChain.section_length_eq_sum_pieces_of_data` (this module).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.Elimination`,
  `Appendix_FixedPoint.BezoutChain.chart_bridge`. -/
theorem chart_length_eq_sum_pieces_of_data (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    (hZd : IsZeroDimensional n K G)
    (hdata : ∀ d, 0 < d → CfsecDisjointData n K G ℓ d)
    (hlin : (chartRing n K G ℓ) ≃ₗ[K] (sectionQuotient n K G ℓ)) :
    ∃ B', Module.finrank K (chartRing n K G ℓ)
      = ∑ d ∈ Finset.range (B' + 1), Fsec n K G ℓ d := by
  obtain ⟨B', hB'⟩ :=
    section_length_eq_sum_pieces_of_data n K G ℓ hreg hZd hdata
  exact ⟨B', (chart_bridge n K G ℓ hreg hlin).trans hB'⟩

/-- Feeder through `sum_mult_eq_chart_length` on reduced inputs: the
multiplicity sum over the locus equals the filtration-piece sum for some
bound `B'`. Conditional on exactly
`[hc, hfin, hlocal, hadd, hreg, hZd, hdata, hlin]` (the first four are the
`LocalMultiplicity`-owned slots of `sum_mult_eq_chart_length`, cited there).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.Counting`,
  `Appendix_FixedPoint.BezoutChain.sum_mult_eq_chart_length`,
  `Appendix_FixedPoint.BezoutChain.chart_length_eq_sum_pieces_of_data` (this module). -/
theorem sum_mult_eq_sum_pieces_of_data (n : ℕ) (K : Type*) [Field K]
    [IsAlgClosed K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hc : ∀ (p : Projectivization K (Fin (n + 2) → K))
      (_ : p ∈ vanishingLocus n K G)
      (v : Fin (n + 2) → K) (hv : v ≠ 0),
      Projectivization.mk K v hv = p → MvPolynomial.eval v (mkLin n K ℓ) ≠ 0)
    (hfin : (vanishingLocus n K G).Finite)
    (w : Projectivization K (Fin (n + 2) → K) → ℕ)
    (hlocal : ∀ p ∈ locusFinset n K G hfin,
      localPointMultiplicity n K G ℓ hc p = w p)
    (hadd : ∑ p ∈ locusFinset n K G hfin, w p
      = Module.finrank K (chartRing n K G ℓ))
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    (hZd : IsZeroDimensional n K G)
    (hdata : ∀ d, 0 < d → CfsecDisjointData n K G ℓ d)
    (hlin : (chartRing n K G ℓ) ≃ₗ[K] (sectionQuotient n K G ℓ)) :
    ∃ B', ∑ p ∈ locusFinset n K G hfin, localPointMultiplicity n K G ℓ hc p
      = ∑ d ∈ Finset.range (B' + 1), Fsec n K G ℓ d := by
  obtain ⟨B', hB'⟩ :=
    chart_length_eq_sum_pieces_of_data n K G ℓ hreg hZd hdata hlin
  exact ⟨B', (sum_mult_eq_chart_length n K G ℓ hc hfin w hlocal hadd).trans hB'⟩

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

/-! ## BridgeToFixedPoint/vanishing close lane (bridge lane)

equiv-vs-finrank routing (task 1 — this file's four `hlin` consumers).
Each consumer applies `chart_bridge` and transits into a length identity, so
each needs only the finrank equation: finrank rewire chosen for all four
(shorter than `Classical.choice` from `Elimination.chart_bridge_equiv_of_final`:
no choice, no chart-finiteness instance):

* `chart_length_eq_sum_pieces` + `chart_length_eq_sum_pieces_of_data`
  ⟹ `chart_length_eq_sum_pieces_final` (via `chart_bridge_eq_of_final`).
* `sum_mult_eq_sum_pieces` + `sum_mult_eq_sum_pieces_of_data`
  ⟹ `sum_mult_eq_sum_pieces_final` (via the rewired chart lemma).

The bridge equation `chart_bridge_eq_of_final` is `chart_bridge_of_final`
at the `stab_align` bound: section side from `Cfsec` (`cfsec_step_of_quadrics`
+ `hS0_of_hG`), chart side from `chartStab_of_final`. No `hlin`.

hvan-final (task 2 — this file). The lattice bridge
(`HilbertFunctionCount.cfsec_mem_lowerSum`) + `CfsecDisjointData` closure
(`HilbertFunctionCount.cfsecDisjointData_of_quadrics`) discharge `hdisjAbove-B`
(`hdisjAbove_of_quadrics`, from `hG` alone) and hence `hvan`
(`hvan_final`, via `fsec_vanishing_of_stabAbove` at the
`cfsec_stab_section` bound). All closings below are unconditional on exactly
`[hG, hreg, hZd]` (Statement's own hypotheses): `hfilter_of_final`,
`section_length_eq_sum_pieces_final`, `chartStab_of_final`,
`hfilter_cfsecSide_of_final` (the `Elimination.hfilter_of_cfsecSide`
instantiation with closed `hvan`).

No new imports; no new edges toward `CountingHandoff`/`ProjectiveLocus`.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
/-- `hdisjAbove-B` from the quadrics hypothesis alone (the `Fsec`-vanishing
input above any bound).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.hdisj_full_of_quadrics`. -/
theorem hdisjAbove_of_quadrics (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (B : ℕ)
    (hG : ∀ i, (G i).IsHomogeneous 2) :
    ∀ d, B < d → Disjoint (Cfsec n K G ℓ d) (sectionPiece n K G ℓ d) :=
  fun d _ => hdisj_full_of_quadrics n K G ℓ hG d

/-- The `Cfsec` step equation from the quadrics hypothesis (SES step with
disjointness from `hdisj_full_of_quadrics`; finrank shape, as consumed by
`chart_bridge_of_final` and `hfilter_of_cfsecSide`). Ambient section
finiteness is the `section_finite_of_artinian` instance (from `hreg` + `hZd`).

## References

* `Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean`,
  `Submodule.finrank_sup_add_finrank_inf_eq`.
* `Mathlib/Order/Disjoint.lean`, `disjoint_iff_inf_le`.
* `Mathlib/LinearAlgebra/Dimension/Finite.lean`, `finrank_bot`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.cfsec_succ`,
  `Appendix_FixedPoint.BezoutChain.hdisj_full_of_quadrics`. -/
theorem cfsec_step_of_quadrics (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (B : ℕ)
    [Module.Finite K (sectionQuotient n K G ℓ)]
    (hG : ∀ i, (G i).IsHomogeneous 2) :
    ∀ d, d ≤ B → Module.finrank K ↥(Cfsec n K G ℓ (d + 1))
      = Module.finrank K ↥(Cfsec n K G ℓ d)
        + Module.finrank K ↥(sectionPiece n K G ℓ d) := by
  intro d hd
  have hstep := Submodule.finrank_sup_add_finrank_inf_eq
    (Cfsec n K G ℓ d) (sectionPiece n K G ℓ d)
  have hinf : Cfsec n K G ℓ d ⊓ sectionPiece n K G ℓ d = ⊥ :=
    le_antisymm (disjoint_iff_inf_le.mp
      (hdisj_full_of_quadrics n K G ℓ hG d)) bot_le
  rw [hinf, finrank_bot, add_zero] at hstep
  rw [cfsec_succ]
  exact hstep

/-- `hvan`-final: stabilization + vanishing at one bound from Statement's own
hypotheses (`hstab` by `cfsec_stab_section` from `hreg` + `hZd`; `hvan` by
`fsec_vanishing_of_stabAbove` with `hdisjAbove` from `hG`).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.cfsec_stab_section`,
  `Appendix_FixedPoint.BezoutChain.fsec_vanishing_of_stabAbove`,
  `Appendix_FixedPoint.BezoutChain.section_finite_of_artinian`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.Counting`,
  `Appendix_FixedPoint.BezoutChain.hdisjAbove_of_quadrics` (this module). -/
theorem hvan_final (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    (hZd : IsZeroDimensional n K G)
    (hG : ∀ i, (G i).IsHomogeneous 2) :
    ∃ B, Cfsec n K G ℓ (B + 1) = ⊤ ∧
      ∀ d, B < d → Fsec n K G ℓ d = 0 := by
  obtain ⟨B, hstab⟩ := cfsec_stab_section n K G ℓ hreg hZd
  refine ⟨B, hstab, ?_⟩
  exact @fsec_vanishing_of_stabAbove n K _ G ℓ B
    (section_finite_of_artinian n K G ℓ hreg hZd) hstab
    (hdisjAbove_of_quadrics n K G ℓ B hG)

/-- The `hfilter` shape consumed by `length_section_eq_two_pow` from
Statement's own hypotheses: `hfilter_of_data` with the disjointness data
closed by `cfsecDisjointData_of_quadrics`.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.Counting`,
  `Appendix_FixedPoint.BezoutChain.hfilter_of_data`
  (this module).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.cfsecDisjointData_of_quadrics`. -/
theorem hfilter_of_final (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    (hZd : IsZeroDimensional n K G)
    (hG : ∀ i, (G i).IsHomogeneous 2) :
    ∃ (B' : ℕ) (Cf : ℕ → Submodule K (sectionQuotient n K G ℓ)),
      Cf 0 = ⊥ ∧ Cf (B' + 1) = ⊤ ∧
      (∀ d, d ≤ B' →
        Module.finrank K ↥(Cf (d + 1)) = Module.finrank K ↥(Cf d)
          + Fsec n K G ℓ d) ∧
      ∀ d, B' < d → Fsec n K G ℓ d = 0 :=
  hfilter_of_data n K G ℓ hreg hZd
    (fun d hd => cfsecDisjointData_of_quadrics n K G ℓ hG d hd)

/-- Length additivity on the section from Statement's own hypotheses (the
`hfilter_of_final` shape telescoped).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.Counting`,
  `Appendix_FixedPoint.BezoutChain.hfilter_of_final`
  (this module).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.section_finrank_telescope`. -/
theorem section_length_eq_sum_pieces_final (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    (hZd : IsZeroDimensional n K G)
    (hG : ∀ i, (G i).IsHomogeneous 2) :
    ∃ B', Module.finrank K (sectionQuotient n K G ℓ)
      = ∑ d ∈ Finset.range (B' + 1), Fsec n K G ℓ d := by
  obtain ⟨B', Cf, hC0, hCtop, hCstep, _⟩ :=
    hfilter_of_final n K G ℓ hreg hZd hG
  exact ⟨B', section_finrank_telescope n K G ℓ (Fsec n K G ℓ) B' Cf hC0 hCtop
    hCstep⟩

/-- Chart-side stabilization from Statement's own hypotheses: the
`Elimination.chartStab_of_hvan` instantiation with `hvan` closed by
`hvan_final` (`Fsec` unfolds to the finrank shape by `rfl`).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.Elimination`,
  `Appendix_FixedPoint.BezoutChain.chartStab_of_hvan`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.Counting`,
  `Appendix_FixedPoint.BezoutChain.hvan_final`
  (this module).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.section_finite_of_artinian`,
  `Appendix_FixedPoint.BezoutChain.Fsec`. -/
theorem chartStab_of_final (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hG : ∀ i, (G i).IsHomogeneous 2)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    (hZd : IsZeroDimensional n K G) :
    ∃ D, chartPiece n K G ℓ D = ⊤ := by
  obtain ⟨B, _, hvan⟩ := hvan_final n K G ℓ hreg hZd hG
  exact @chartStab_of_hvan n K _ G ℓ B hG hreg
    (section_finite_of_artinian n K G ℓ hreg hZd) (fun d hd => hvan d hd)

/-- The chart–section bridge equation from Statement's own hypotheses, with
no `hlin`: `chart_bridge_of_final` at the `stab_align` bound (section side
`Cfsec` via `cfsec_step_of_quadrics` + `hS0_of_hG`; chart side via
`chartStab_of_final`). The finrank target of all four `hlin` rewires.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.Elimination`,
  `Appendix_FixedPoint.BezoutChain.chart_bridge_of_final`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.stab_align`,
  `Appendix_FixedPoint.BezoutChain.cfsec_zero`, `Appendix_FixedPoint.BezoutChain.hS0_of_hG`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.Counting`,
  `Appendix_FixedPoint.BezoutChain.hvan_final`,
  `Appendix_FixedPoint.BezoutChain.chartStab_of_final`,
  `Appendix_FixedPoint.BezoutChain.cfsec_step_of_quadrics` (this module). -/
theorem chart_bridge_eq_of_final (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hG : ∀ i, (G i).IsHomogeneous 2)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    (hZd : IsZeroDimensional n K G) :
    Module.finrank K (chartRing n K G ℓ)
      = Module.finrank K (sectionQuotient n K G ℓ) := by
  obtain ⟨B, hstabS, _⟩ := hvan_final n K G ℓ hreg hZd hG
  obtain ⟨D, hstabC⟩ := chartStab_of_final n K G ℓ hG hreg hZd
  obtain ⟨B', hC', hS'⟩ := stab_align n K G ℓ B D hstabS hstabC
  exact @chart_bridge_of_final n K _ G ℓ B' hreg hG
    (section_finite_of_artinian n K G ℓ hreg hZd) hC'
    (Cfsec n K G ℓ) (cfsec_zero n K G ℓ) hS'
    (@cfsec_step_of_quadrics n K _ G ℓ B'
      (section_finite_of_artinian n K G ℓ hreg hZd) hG)
    (hS0_of_hG n K G ℓ hG)

/-- Length additivity on the chart from Statement's own hypotheses: finrank
rewire of `chart_length_eq_sum_pieces` and `chart_length_eq_sum_pieces_of_data`
(no `hlin`). Status: unconditional on exactly `[hG, hreg, hZd]`.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.Counting`,
  `Appendix_FixedPoint.BezoutChain.section_length_eq_sum_pieces_final`,
  `Appendix_FixedPoint.BezoutChain.chart_bridge_eq_of_final` (this module). -/
theorem chart_length_eq_sum_pieces_final (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hG : ∀ i, (G i).IsHomogeneous 2)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    (hZd : IsZeroDimensional n K G) :
    ∃ B', Module.finrank K (chartRing n K G ℓ)
      = ∑ d ∈ Finset.range (B' + 1), Fsec n K G ℓ d := by
  obtain ⟨B', hB'⟩ :=
    section_length_eq_sum_pieces_final n K G ℓ hreg hZd hG
  exact ⟨B', (chart_bridge_eq_of_final n K G ℓ hG hreg hZd).trans hB'⟩

/-- Feeder through `sum_mult_eq_chart_length` from Statement's own hypotheses:
finrank rewire of `sum_mult_eq_sum_pieces` and `sum_mult_eq_sum_pieces_of_data`
(no `hlin`). Status: unconditional on exactly
`[hc, hfin, hlocal, hadd, hG, hreg, hZd]` (the first four are the
`LocalMultiplicity`-owned slots of `sum_mult_eq_chart_length`, cited there).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.Counting`,
  `Appendix_FixedPoint.BezoutChain.sum_mult_eq_chart_length`,
  `Appendix_FixedPoint.BezoutChain.chart_length_eq_sum_pieces_final` (this module). -/
theorem sum_mult_eq_sum_pieces_final (n : ℕ) (K : Type*) [Field K]
    [IsAlgClosed K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hc : ∀ (p : Projectivization K (Fin (n + 2) → K))
      (_ : p ∈ vanishingLocus n K G)
      (v : Fin (n + 2) → K) (hv : v ≠ 0),
      Projectivization.mk K v hv = p → MvPolynomial.eval v (mkLin n K ℓ) ≠ 0)
    (hfin : (vanishingLocus n K G).Finite)
    (w : Projectivization K (Fin (n + 2) → K) → ℕ)
    (hlocal : ∀ p ∈ locusFinset n K G hfin,
      localPointMultiplicity n K G ℓ hc p = w p)
    (hadd : ∑ p ∈ locusFinset n K G hfin, w p
      = Module.finrank K (chartRing n K G ℓ))
    (hG : ∀ i, (G i).IsHomogeneous 2)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    (hZd : IsZeroDimensional n K G) :
    ∃ B', ∑ p ∈ locusFinset n K G hfin, localPointMultiplicity n K G ℓ hc p
      = ∑ d ∈ Finset.range (B' + 1), Fsec n K G ℓ d := by
  obtain ⟨B', hB'⟩ := chart_length_eq_sum_pieces_final n K G ℓ hG hreg hZd
  exact ⟨B', (sum_mult_eq_chart_length n K G ℓ hc hfin w hlocal hadd).trans hB'⟩

/-- The `Elimination.hfilter_of_cfsecSide` shape with `hvan` closed: `Cfsec`
instantiation (`cfsec_zero`, `cfsec_step_of_quadrics`, `hvan_final`
with `Fsec` unfolding to the finrank shape by `rfl`).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.Elimination`,
  `Appendix_FixedPoint.BezoutChain.hfilter_of_cfsecSide`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.cfsec_zero`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.Counting`,
  `Appendix_FixedPoint.BezoutChain.hvan_final`,
  `Appendix_FixedPoint.BezoutChain.cfsec_step_of_quadrics`
  (this module). -/
theorem hfilter_cfsecSide_of_final (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hG : ∀ i, (G i).IsHomogeneous 2)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    (hZd : IsZeroDimensional n K G) :
    ∃ (B' : ℕ) (Cf' : ℕ → Submodule K (sectionQuotient n K G ℓ)),
      Cf' 0 = ⊥ ∧ Cf' (B' + 1) = ⊤ ∧
      (∀ d, d ≤ B' → Module.finrank K ↥(Cf' (d + 1))
        = Module.finrank K ↥(Cf' d)
          + Module.finrank K ↥(sectionPiece n K G ℓ d)) ∧
      ∀ d, B' < d → Module.finrank K ↥(sectionPiece n K G ℓ d) = 0 := by
  obtain ⟨B, hstabS, hvanS⟩ := hvan_final n K G ℓ hreg hZd hG
  exact hfilter_of_cfsecSide n K G ℓ B (Cfsec n K G ℓ) (cfsec_zero n K G ℓ)
    hstabS (@cfsec_step_of_quadrics n K _ G ℓ B
      (section_finite_of_artinian n K G ℓ hreg hZd) hG)
    (fun d hd => hvanS d hd)

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
