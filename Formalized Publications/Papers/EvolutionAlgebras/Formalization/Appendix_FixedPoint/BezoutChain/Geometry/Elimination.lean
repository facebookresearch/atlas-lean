/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Statement.Definitions
import Appendix_FixedPoint.BezoutChain.Geometry.ChartFiltration
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Data.ENat.Monoid
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-!
# Regular section and chart bridge (route (ii′))

This module proves the interface lemmas,
plus the finrank-form bridge discharging `hlin`:

* `section_artinian`: a regular section of the cone by `ℓ` (R1-regularity taken
  as the explicit hypothesis `hreg`, as produced by
  `Appendix_FixedPoint.BezoutChain.exists_regular_chartForm`) together with `IsZeroDimensional`
  forces
  the section quotient `S ⧸ ℓS` to be Artinian. The proof is purely algebraic
  (Krull dimension drops by one along a nonzerodivisor quotient), so no
  locus-finiteness hypothesis is needed here.
* `chart_bridge`: the `K`-length of the chart side equals the `K`-length of the
  section `S ⧸ ℓS`. The SES-additivity mechanism (`ses_finrank_add` below) is
  proved; the geometric input (filtration exhausting the chart with subquotients
  `(S/ℓS)_d`) is taken as the explicit linear-equivalence hypothesis `hlin`.
* `chart_bridge_finrank`: the same equality in finrank form, with the `hlin`
  content discharged by `chart_finrank_eq_sum_pieces` (chart side) plus the
  local section-side telescope `section_telescope_of_pieces`.

## Added hypotheses

1. `section_artinian` concludes `IsArtinianRing (sectionQuotient …)`: the spec
   writes `IsArtinianRing K (sectionQuotient …)`, but `IsArtinianRing` takes a
   single argument (the ring). The `K` is a typo; the `K`-algebra structure is
   already on the quotient.
2. `section_artinian` needs no extra hypothesis beyond `hreg` + `hZd`
   (in particular not the locus-finiteness `hfin` the task permits): the
   dimension-drop argument never mentions the locus. Counting still
   discharges `hfin` from `hZd` for its own lemmas.
3. `chart_bridge` (kept for interface stability) takes one extra explicit
   hypothesis, `hlin : (chartRing n K G ℓ) ≃ₗ[K] (sectionQuotient n K G ℓ)`,
   standing in for the filtration geometry; its finrank content is now
   discharged by `chart_bridge_finrank` below (chart side via
   `chart_finrank_eq_sum_pieces` with `chartPiece_finite`,
   `descentData_of_quadrics`, `hG0_of_quadrics` proved internally, section
   side via the local telescope `section_telescope_of_pieces`). Note:
   `Definitions.chartRing` is the degree-`0` part `(S_ℓ)₀`, so the bridge
   filtration (`G_d` exhausting the chart with subquotients `(S/ℓS)_d`) lives
   in the right ring.
4. `chart_bridge` keeps the spec-mandated `hreg` hypothesis for interface
   stability although the one-line proof consumes only `hlin` (precedent:
   `Appendix_FixedPoint.BezoutChain.exists_regular_chartForm` retains its unused `hS` the same way).

## References

Mathlib v4.34.0 has no degree-of-variety or chart-restriction API, so both
results are assembled from Krull-dimension and finrank API. Per-declaration
`## References` subsections cite the exact module path and declaration name,
each verified in-tree.

## Standing context (routine binders)

Named once here; per-decl docstrings below repeat GRADE verdicts and name only
substantive non-routine premises.

* `hG : ∀ i, (G i).IsHomogeneous 2` / `hG0 : ∀ i, eval 0 (G i) = 0` —
  quadric system / vanishing at the origin.
* `hreg` — R1 section regularity (`IsSMulRegular` on the cone).
* `hZd : IsZeroDimensional n K G` — the cone-dimension input.
* `hfin`/`hfinS`/`hfinChartLocal` — `Module.Finite` forms (section pieces,
  chart side).
* `hC0 : Cf 0 = ⊥`, `hCtop : Cf (B + 1) = ⊤`,
  `hCstep : finrank (Cf (d+1)) = finrank (Cf d) + finrank (sectionPiece d)` —
  the filtration telescope data; `hS0` its degree-`0` value.
* `hdesc : ∀ d, d < B → DescentData n K G ℓ d` — per-degree descent data.
* Bridge inputs: `hdisj`, `hstab`, `hvan`, `hfilter`, `hlin`, `hlen`;
  `hcontra_of_havoid` (avoidance-fed converse).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
open scoped BigOperators

/-- A regular element of a commutative ring is a nonzerodivisor: injectivity of
`x • ·` applied to `x • a = x • 0`. (Mathlib has only the converse under a
flatness hypothesis, `Module.Flat.isSMulRegular_of_nonZeroDivisors`.)

## References

* `Mathlib/Algebra/Regular/SMul.lean`, `IsSMulRegular`
  (`def IsSMulRegular [SMul R M] (c : R) := Function.Injective ((c • ·) : M → M)`).
* `Mathlib/Algebra/GroupWithZero/NonZeroDivisors.lean`, `mem_nonZeroDivisors_iff`.
* `Mathlib/Algebra/Group/Action/Defs.lean`, `smul_eq_mul` (an `rfl`-lemma). -/
theorem smulRegular_mem_nonZeroDivisors (S : Type*) [CommRing S] (x : S)
    (hreg : IsSMulRegular S x) : x ∈ nonZeroDivisors S := by
  refine mem_nonZeroDivisors_iff.mpr ⟨fun a ha => ?_, fun a ha => ?_⟩
  · have h2 : x • a = x • (0 : S) := by
      rw [smul_eq_mul, smul_zero]
      exact ha
    exact hreg h2
  · have h2 : x • a = x • (0 : S) := by
      rw [smul_eq_mul, smul_zero, mul_comm]
      exact ha
    exact hreg h2

/-- Regular section is Artinian: with `ℓ̄`
regular on the cone (R1, hypothesis `hreg`) and the cone of Krull dimension
`≤ 1` (hypothesis `hZd`), the section `S ⧸ ℓS` has Krull dimension `0`, hence
is Artinian (it is Noetherian as an iterated quotient of `MvPolynomial`).
No locus-finiteness is used.

## References

* `Mathlib/RingTheory/KrullDimension/Basic.lean`, `Ring.krullDimLE_iff`
  (`Ring.KrullDimLE n R ↔ ringKrullDim R ≤ ↑n`), `ringKrullDim`,
  `Ring.KrullDimLE`.
* `Mathlib/RingTheory/KrullDimension/NonZeroDivisors.lean`,
  `ringKrullDim_quotient_succ_le_of_nonZeroDivisor`
  (`ringKrullDim (R ⧸ Ideal.span {r}) + 1 ≤ ringKrullDim R`).
* `Mathlib/RingTheory/HopkinsLevitzki.lean`, `isArtinianRing_iff_krullDimLE_zero`
  (needs the `[IsNoetherianRing _]` instance, via
  `Mathlib/RingTheory/Ideal/Quotient/Noetherian.lean`,
  `Ideal.Quotient.isNoetherianRing`).
* `Mathlib/Data/ENat/Monoid.lean`, `ENat.WithBot.add_le_add_one_right_iff`
  (the `+ 1`-cancellation step; same rewrite chain as
  `isFiniteLength_quotient_span_singleton` in
  `Mathlib/RingTheory/OrderOfVanishing/Basic.lean`). -/
theorem section_artinian (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    (hZd : IsZeroDimensional n K G) :
    IsArtinianRing (sectionQuotient n K G ℓ) := by
  have hmem := smulRegular_mem_nonZeroDivisors _ _ hreg
  have hdimS : ringKrullDim (coneQuotient n K G) ≤ 1 :=
    Ring.krullDimLE_iff.mp hZd
  refine (isArtinianRing_iff_krullDimLE_zero
    (R := sectionQuotient n K G ℓ)).mpr ?_
  rw [Ring.krullDimLE_iff,
    ← ENat.WithBot.add_le_add_one_right_iff, Nat.cast_zero, zero_add]
  exact (ringKrullDim_quotient_succ_le_of_nonZeroDivisor hmem).trans hdimS

/-- SES finrank additivity: the single short-exact-sequence step the chart
filtration proof iterates. If `G_d` exhausts the chart with
`G_d / G_{d-1} ≅ (S/ℓS)_d` (using `ℓ`-torsionfreeness from R1 regularity),
summing this step over `d` gives
`finrank K chart = ∑ finrank K (S/ℓS)_d = finrank K section`.

## References

* `Mathlib/LinearAlgebra/Dimension/RankNullity.lean`,
  `Submodule.finrank_quotient_add_finrank`
  (`finrank R (M ⧸ N) + finrank R N = finrank R M`, needs `[Module.Finite R M]`). -/
theorem ses_finrank_add (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    (s : Submodule K V) [Module.Finite K V] :
    Module.finrank K (V ⧸ s) + Module.finrank K s = Module.finrank K V :=
  Submodule.finrank_quotient_add_finrank s

/-- Chart bridge: the chart side has the
same `K`-length as the regular section. The filtration geometry (exhaustion by
`G_d = S_d / ℓ^d` plus the torsionfree identifications `G_d / G_{d-1}`) is taken
as the explicit hypothesis `hlin`; see the module docstring for why the
unconditional form is false for the full localization `chartRing`. The
`hreg` hypothesis is retained for interface stability.

## References

* `Mathlib/LinearAlgebra/Dimension/Finrank.lean`, `LinearEquiv.finrank_eq`. -/
theorem chart_bridge (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (_hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    (hlin : (chartRing n K G ℓ) ≃ₗ[K] (sectionQuotient n K G ℓ)) :
    Module.finrank K (chartRing n K G ℓ)
      = Module.finrank K (sectionQuotient n K G ℓ) :=
  LinearEquiv.finrank_eq hlin

/-- Section-side telescope from piece steps (mirror of
`chart_finrank_telescope`, for the `chart_bridge_finrank` assembly): a degree
filtration `Cf` of the section with `Cf 0 = ⊥`, `Cf (B + 1) = ⊤`, and steps
adding `finrank sectionPiece d` sums to the section length. Downstream
instantiates `Cf := Cfsec` via `cfsec_hfilter` (with `F := Fsec`, matching
`finrank sectionPiece d` by `rfl`).

## References

* `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`,
  `Finset.sum_range_succ`.
* `Mathlib/Algebra/Module/Submodule/Lattice.lean`, `Submodule.topEquiv`.
* `Mathlib/LinearAlgebra/Dimension/Finrank.lean`, `LinearEquiv.finrank_eq`. -/
theorem section_telescope_of_pieces (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (B : ℕ)
    (Cf : ℕ → Submodule K (sectionQuotient n K G ℓ))
    (hC0 : Cf 0 = ⊥) (hCtop : Cf (B + 1) = ⊤)
    (hCstep : ∀ d, d ≤ B → Module.finrank K ↥(Cf (d + 1))
      = Module.finrank K ↥(Cf d)
        + Module.finrank K ↥(sectionPiece n K G ℓ d)) :
    Module.finrank K (sectionQuotient n K G ℓ)
      = ∑ d ∈ Finset.range (B + 1),
        Module.finrank K ↥(sectionPiece n K G ℓ d) := by
  have hsum : ∀ m : ℕ, m ≤ B + 1 → Module.finrank K ↥(Cf m)
      = ∑ d ∈ Finset.range m,
        Module.finrank K ↥(sectionPiece n K G ℓ d) := by
    intro m
    induction m with
    | zero => intro _; rw [hC0]; simp
    | succ m IH =>
      intro hm
      have hmB : m ≤ B := by omega
      have hm' : m ≤ B + 1 := by omega
      rw [hCstep m hmB, IH hm', Finset.sum_range_succ]
  have h := hsum (B + 1) le_rfl
  rw [hCtop] at h
  rwa [LinearEquiv.finrank_eq Submodule.topEquiv] at h

/-- Chart bridge in finrank form (restates `chart_bridge`'s `hlin` content
without the `LinearEquiv`): the chart length equals the section length. The
chart side is `chart_finrank_eq_sum_pieces` (with `chartPiece_finite`,
`descentData_of_quadrics`, `hG0_of_quadrics` discharged internally from
`hG`/`hreg`, and `G_0 = 1` by `chartPiece_zero_finrank`); the section side
is the local telescope `section_telescope_of_pieces` peeled by `hS0`.
Remaining inputs and their discharge routes: `hfinS` (by
`sectionPiece_finite_of` from `hreg` + `hZd`), `hstab` (by
`chartPiece_stabilizes_of_finite` from chart finiteness, via
`chart_finite_of_sectionPiece_vanishing` from `hvan`), and the
section-filtration inputs `Cf`/`hC0`/`hCtop`/`hCstep`/`hS0` (by
`cfsec_hfilter` + `fsec_zero_eq_one`). The old `chart_bridge` (`hlin` form)
is kept for interface stability.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ChartFiltration`,
  `Appendix_FixedPoint.BezoutChain.chart_finrank_eq_sum_pieces`,
  `Appendix_FixedPoint.BezoutChain.chartPiece_finite`,
  `Appendix_FixedPoint.BezoutChain.chartPiece_zero_finrank`,
  `Appendix_FixedPoint.BezoutChain.descentData_of_quadrics`,
  `Appendix_FixedPoint.BezoutChain.hG0_of_quadrics` (imported above).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.Elimination`,
  `Appendix_FixedPoint.BezoutChain.section_telescope_of_pieces` (this module).
* `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`,
  `Finset.sum_range_succ'`. -/
theorem chart_bridge_finrank (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (B : ℕ)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    (hG : ∀ i, (G i).IsHomogeneous 2)
    (hfinS : ∀ d, Module.Finite K ↥(sectionPiece n K G ℓ d))
    (hstab : chartPiece n K G ℓ B = ⊤)
    (Cf : ℕ → Submodule K (sectionQuotient n K G ℓ))
    (hC0 : Cf 0 = ⊥) (hCtop : Cf (B + 1) = ⊤)
    (hCstep : ∀ d, d ≤ B → Module.finrank K ↥(Cf (d + 1))
      = Module.finrank K ↥(Cf d)
        + Module.finrank K ↥(sectionPiece n K G ℓ d))
    (hS0 : Module.finrank K ↥(sectionPiece n K G ℓ 0) = 1) :
    Module.finrank K (chartRing n K G ℓ)
      = Module.finrank K (sectionQuotient n K G ℓ) := by
  have hfin : ∀ d, Module.Finite K ↥(chartPiece n K G ℓ d) :=
    fun d => chartPiece_finite n K G ℓ d
  have hG0 : ∀ i, MvPolynomial.eval (0 : Fin (n + 2) → K) (G i) = 0 :=
    hG0_of_quadrics n K G hG
  have hdesc : ∀ d, d < B → DescentData n K G ℓ d :=
    fun d _ => descentData_of_quadrics n K G ℓ hG hreg d
  have hchart :=
    chart_finrank_eq_sum_pieces n K G ℓ B hfin hfinS hstab hreg hdesc
  rw [chartPiece_zero_finrank n K G ℓ hG0 hreg] at hchart
  have hsec := section_telescope_of_pieces n K G ℓ B Cf hC0 hCtop hCstep
  rw [Finset.sum_range_succ', hS0] at hsec
  rw [hchart, hsec, add_comm]

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

/-! ## hfilter assembly from proved pieces (hfilter-assembly lane)

This section assembles the `hfilter` input of `HilbertFunctionCount.length_section_eq_two_pow`
(cited by name — `HilbertFunctionCount` imports this module, so no import edge is possible)
maximally from proved pieces, in `Elimination` vocabulary (no `Fsec`/`Cfsec`,
which live in the unimportable `HilbertFunctionCount`; no `Counting` import, which would
also cycle). The `F` in the pinned `hfilter` shape is the `Fsec` unfolding
`fun d => Module.finrank K ↥(sectionPiece n K G ℓ d)` by `rfl`.

Discharged in-file (this lane):
* `DescentData` ← `descentData_of_quadrics` (from `hG` + `hreg`).
* `hfin` ← `chartPiece_finite` (unconditional); `hfinS` ←
  `sectionPiece_finite_of_finite` (from the ambient-finiteness instance).
* `hG0` ← `hG0_of_quadrics` (from `hG`).
* Chart-side stabilization, existential form ← `chartStab_of_hvan` (from `hvan`
  via `chart_finite_of_sectionPiece_vanishing` + `chartPiece_stabilizes_of_finite`).
* Section telescope ← `section_telescope_of_pieces`; SES additivity ←
  `ses_finrank_add`; section Artinian ← `section_artinian` (from `hreg` + `hZd`).

conditional-exact remainder (narrowest list; each an explicit hypothesis below):
1. `hdisj-d>0`: `Disjoint (Cfsec d) (sectionPiece d)` for `0 < d ≤ B` (residual
   R-disj; level `0` is `Counting.cfsec_disjoint_zero`, cited by name).
2. `hstab` (section side): `Cfsec (B + 1) = ⊤` (Artinian stabilization bound).
3. `hvan`: `finrank (sectionPiece d) = 0` for `B < d` (piece vanishing).
4. Ambient finiteness `[Module.Finite K sectionQuotient]` (via
   `HilbertFunctionCount.section_finite_of_artinian` from `hreg` + `hZd`, cited by name;
   `hZd` itself via `ConeDimOne.hcontra_of_havoid` from locus finiteness +
   `hdim` + `havoid`, cited by name).
5. `hS0`: `finrank (sectionPiece 0) = 1` (via `HilbertFunctionCount.fsec_zero_eq_one` from
   `hG0` + `section_nontrivial_of_evalZero`, cited by name).
6. `hstab` (chart side, bridge only): `chartPiece B = ⊤` at the section bound
   (the existential form is `chartStab_of_hvan`; bound alignment stays open).

Status: `hfilter`: conditional on exactly `[hdisj-d>0, hstab, hvan]` modulo the
`Cfsec`-side instantiation (`HilbertFunctionCount.cfsec_hfilter`, cited by name) and the
ambient bridges above.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
/-- Chart-side stabilization, existential form, from section-piece vanishing:
`hvan` (finrank shape at `B`) plus quadrics (`hG`) plus R1-regularity (`hreg`)
plus ambient section finiteness makes the chart finite
(`chart_finite_of_sectionPiece_vanishing`, with `DescentData` discharged
internally by `descentData_of_quadrics`), hence the filtration stabilizes
(`chartPiece_stabilizes_of_finite`, with `hfin` discharged internally by
`chartPiece_finite`). The stabilizing bound `D` is unrelated to `B`
(bound alignment for the bridge stays open; see `chart_bridge_of_final`).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ChartFiltration`,
  `Appendix_FixedPoint.BezoutChain.chart_finite_of_sectionPiece_vanishing`,
  `Appendix_FixedPoint.BezoutChain.chartPiece_stabilizes_of_finite` (imported above). -/
theorem chartStab_of_hvan (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (B : ℕ)
    (hG : ∀ i, (G i).IsHomogeneous 2)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    [Module.Finite K (sectionQuotient n K G ℓ)]
    (hvan : ∀ d, B < d → Module.finrank K ↥(sectionPiece n K G ℓ d) = 0) :
    ∃ D, chartPiece n K G ℓ D = ⊤ := by
  have : Module.Finite K (chartRing n K G ℓ) :=
    chart_finite_of_sectionPiece_vanishing n K G ℓ B hG hreg hvan
  exact chartPiece_stabilizes_of_finite n K G ℓ

/-- The `hfilter` shape consumed by `HilbertFunctionCount.length_section_eq_two_pow`
(binder shape copied verbatim, with `F` the `Fsec` unfolding), from the
`Cfsec`-side inputs in verbatim shape: downstream instantiates `Cf := Cfsec`
via `HilbertFunctionCount.cfsec_hfilter` (cited by name), whose `hdisj` is level-`0`-done
by `Counting.cfsec_disjoint_zero` (cited by name) with `d > 0` residual, and
whose `hstab`/`hvan` are the Artinian bound residuals. The ambient finiteness
that `cfsec_hfilter` needs is `HilbertFunctionCount.section_finite_of_artinian` (from
`hreg` + `hZd`, cited by name); `hZd` itself is `ConeDimOne.hcontra_of_havoid`
(cited by name). This is the `Elimination`-vocabulary analogue of
`Counting.hfilter_of_bridge` (cited by name — that module imports this one).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.cfsec_hfilter`,
  `Appendix_FixedPoint.BezoutChain.Fsec`,
  `Appendix_FixedPoint.BezoutChain.length_section_eq_two_pow` (cited by name).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.Counting`,
  `Appendix_FixedPoint.BezoutChain.hfilter_of_bridge`,
  `Appendix_FixedPoint.BezoutChain.cfsec_disjoint_zero` (cited by name).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ConeDimOne`,
  `Appendix_FixedPoint.BezoutChain.hcontra_of_havoid`
  (cited by name). -/
theorem hfilter_of_cfsecSide (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (B : ℕ)
    (Cf : ℕ → Submodule K (sectionQuotient n K G ℓ))
    (hC0 : Cf 0 = ⊥) (hCtop : Cf (B + 1) = ⊤)
    (hCstep : ∀ d, d ≤ B → Module.finrank K ↥(Cf (d + 1))
      = Module.finrank K ↥(Cf d)
        + Module.finrank K ↥(sectionPiece n K G ℓ d))
    (hvan : ∀ d, B < d → Module.finrank K ↥(sectionPiece n K G ℓ d) = 0) :
    ∃ (B' : ℕ) (Cf' : ℕ → Submodule K (sectionQuotient n K G ℓ)),
      Cf' 0 = ⊥ ∧ Cf' (B' + 1) = ⊤ ∧
      (∀ d, d ≤ B' → Module.finrank K ↥(Cf' (d + 1))
        = Module.finrank K ↥(Cf' d)
          + Module.finrank K ↥(sectionPiece n K G ℓ d)) ∧
      ∀ d, B' < d → Module.finrank K ↥(sectionPiece n K G ℓ d) = 0 :=
  ⟨B, Cf, hC0, hCtop, hCstep, hvan⟩

/-- Combined bridge (`chart_bridge_finrank` with `hfinS` discharged): the chart
length equals the section length from `hreg` + `hG` + ambient section finiteness
(via `HilbertFunctionCount.section_finite_of_artinian` from `hreg` + `hZd`, cited by name)
+ chart-side `hstab` at `B` + the `Cfsec`-side inputs + `hS0` (via
`HilbertFunctionCount.fsec_zero_eq_one`, cited by name). `hfinS` is
`sectionPiece_finite_of_finite` from the ambient instance; `hdesc`/`hG0` are
discharged inside `chart_bridge_finrank` as before.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.Elimination`,
  `Appendix_FixedPoint.BezoutChain.chart_bridge_finrank` (this module).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ChartFiltration`,
  `Appendix_FixedPoint.BezoutChain.sectionPiece_finite_of_finite` (imported above).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.section_finite_of_artinian`,
  `Appendix_FixedPoint.BezoutChain.fsec_zero_eq_one`
  (cited by name). -/
theorem chart_bridge_of_final (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (B : ℕ)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    (hG : ∀ i, (G i).IsHomogeneous 2)
    [Module.Finite K (sectionQuotient n K G ℓ)]
    (hstab : chartPiece n K G ℓ B = ⊤)
    (Cf : ℕ → Submodule K (sectionQuotient n K G ℓ))
    (hC0 : Cf 0 = ⊥) (hCtop : Cf (B + 1) = ⊤)
    (hCstep : ∀ d, d ≤ B → Module.finrank K ↥(Cf (d + 1))
      = Module.finrank K ↥(Cf d)
        + Module.finrank K ↥(sectionPiece n K G ℓ d))
    (hS0 : Module.finrank K ↥(sectionPiece n K G ℓ 0) = 1) :
    Module.finrank K (chartRing n K G ℓ)
      = Module.finrank K (sectionQuotient n K G ℓ) :=
  chart_bridge_finrank n K G ℓ B hreg hG
    (fun d => sectionPiece_finite_of_finite n K G ℓ d)
    hstab Cf hC0 hCtop hCstep hS0

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

/-! ## Cfsec-disjointness geometric core (cfdisjoint lane)

This section discharges the homogeneous-geometry content of
`HilbertFunctionCount.CfsecDisjointData` above `0` (cited by name — `HilbertFunctionCount` imports
this module, so no import edge is possible): a degree-`d` section class lying
in the lower span vanishes, for `0 < d`, from Statement's `hG` alone
(quadrics homogeneous of degree `2`; no `hreg` needed — gradedness holds
without regularity).

* `homogeneousComponent_lowSum_eq_zero`: the degree-`d` component of a sum of
  homogeneous polynomials of degrees `< d` vanishes (via
  `homogeneousComponent_of_mem` + `if d = e` discrimination).
* `sectionPiece_of_lowSum_eq_zero`: if the section class of a homogeneous
  degree-`d` lift `p` (`0 < d`) equals the sum of lower-degree section classes,
  it is zero. Proof: write `Q` for the low sum; then `mk p - mk Q ∈ span {ℓ̄}`,
  so `mk (p - Q) = t * ℓ̄`; lift `t` to `qq`, so `R := p - Q - qq * ℓ ∈ span G`;
  take `homogeneousComponent d` (stays in `span G` by
  `homogeneousComponent_mem_span_of_isHomogeneous`): the `Q` part vanishes by
  the helper, the `qq * ℓ` part is `(homogeneousComponent (d-1) qq) * ℓ` by
  `homogeneousComponent_mul_of_isHomogeneous_right` with `ℓ` homogeneous of
  degree `1`, leaving `p - _ * ℓ ∈ span G`, i.e. `mk p ∈ span {ℓ̄}`.
  This is the DescentData-family geometry (the same two homogeneous-component
  lemmas underlying `descentData_of_quadrics`), applied without the regularity
  cancellation `descentData_of_quadrics` needs.
* `sectionPiece_disjoint_lowerSum_of_quadrics`: the `y`-version mirroring
  `CfsecDisjointData`'s shape (`y ∈ sectionPiece d` + explicit lower-sum
  representation `⟹ y = 0`).

conditional-exact remainder (single mechanical bridge, no geometry):
`HilbertFunctionCount` proves `y ∈ Cfsec d → ∃ q..., y = ∑...` by induction on `d`
(`cfsec_succ` is `rfl`, `Submodule.mem_sup`, `Finset.sum_range_succ`), then
applies `sectionPiece_disjoint_lowerSum_of_quadrics` to close
`CfsecDisjointData` above `0`. Level `0` stays `Counting.cfsec_disjoint_zero`
(cited by name).

Status: geometric core unconditional on exactly `[hG]` (Statement's own
hypothesis); formal `HilbertFunctionCount.CfsecDisjointData`-above-`0` conditional-exact
`[Cfsec→sum lattice bridge]` (this module cannot state `Cfsec`, import cycle).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
open scoped BigOperators

/-- The degree-`d` homogeneous component of a sum of homogeneous polynomials
of degrees `< d` vanishes.

## References

* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.homogeneousComponent_of_mem`,
  `MvPolynomial.mem_homogeneousSubmodule`.
* `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`,
  `Finset.sum_eq_zero`, `Finset.mem_range`. -/
theorem homogeneousComponent_lowSum_eq_zero (n : ℕ) (K : Type*) [Field K]
    (q : ℕ → MvPolynomial (Fin (n + 2)) K)
    (d : ℕ) (hq : ∀ e, e < d → (q e).IsHomogeneous e) :
    MvPolynomial.homogeneousComponent d (∑ e ∈ Finset.range d, q e) = 0 := by
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro e he
  have hel : e < d := Finset.mem_range.mp he
  have hmem : q e ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 2)) K e :=
    (MvPolynomial.mem_homogeneousSubmodule e (q e)).mpr (hq e hel)
  have h := MvPolynomial.homogeneousComponent_of_mem (m := d) (n := e) hmem
  rw [h]
  have hne : ¬ (d = e) := ne_of_gt hel
  rw [ite_eq_right hne]

/-- A degree-`d` section class (`0 < d`) that equals a lower-degree sum
vanishes, from quadrics-homogeneity `hG` alone (DescentData-family geometry;
no `hreg` needed).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ChartFiltration`,
  `Appendix_FixedPoint.BezoutChain.homogeneousComponent_mem_span_of_isHomogeneous`,
  `Appendix_FixedPoint.BezoutChain.homogeneousComponent_mul_of_isHomogeneous_right`,
  `Appendix_FixedPoint.BezoutChain.mkLin_isHomogeneous` (imported above).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.Elimination`,
  `Appendix_FixedPoint.BezoutChain.homogeneousComponent_lowSum_eq_zero` (this module).
* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.homogeneousComponent_eq_self`,
  `MvPolynomial.homogeneousComponent_of_mem`,
  `MvPolynomial.mem_homogeneousSubmodule`.
* `Mathlib/RingTheory/Ideal/Quotient/Defs.lean`,
  `Ideal.Quotient.eq_zero_iff_mem`, `Ideal.Quotient.mk_surjective`.
* `Mathlib/RingTheory/Ideal/Span.lean`, `Ideal.mem_span_singleton'`. -/
theorem sectionPiece_of_lowSum_eq_zero (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hG : ∀ i, (G i).IsHomogeneous 2)
    (d : ℕ) (hpos : 0 < d)
    (p : MvPolynomial (Fin (n + 2)) K) (hp : p.IsHomogeneous d)
    (q : ℕ → MvPolynomial (Fin (n + 2)) K) (hq : ∀ e, e < d → (q e).IsHomogeneous e)
    (heq : Ideal.Quotient.mk (Ideal.span
        ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
          Set (coneQuotient n K G)))
        (Ideal.Quotient.mk (Ideal.span (Set.range G)) p)
      = ∑ e ∈ Finset.range d, Ideal.Quotient.mk (Ideal.span
        ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
          Set (coneQuotient n K G)))
        (Ideal.Quotient.mk (Ideal.span (Set.range G)) (q e))) :
    Ideal.Quotient.mk (Ideal.span
        ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
          Set (coneQuotient n K G)))
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) p) = 0 := by
  set mkG := Ideal.Quotient.mk (Ideal.span (Set.range G))
    with hmkG
  set mkS := Ideal.Quotient.mk (Ideal.span
    ({mkG (mkLin n K ℓ)} : Set (coneQuotient n K G)))
    with hmkS
  set Q : MvPolynomial (Fin (n + 2)) K := ∑ e ∈ Finset.range d, q e with hQ
  have heqS : mkS (mkG p) = mkS (mkG Q) := by
    have hsum : mkS (mkG Q) = ∑ e ∈ Finset.range d, mkS (mkG (q e)) := by
      rw [hQ, map_sum, map_sum]
    rw [hsum]
    exact heq
  have hmemS : mkG p - mkG Q ∈ Ideal.span ({mkG (mkLin n K ℓ)} : Set (coneQuotient n K G)) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    rw [map_sub]
    exact sub_eq_zero.mpr heqS
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hmemS
  obtain ⟨qq, hqq⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span (Set.range G)) t
  have hRmem : p - Q - qq * mkLin n K ℓ ∈ Ideal.span (Set.range G) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have e1 : mkG (p - Q - qq * mkLin n K ℓ) = mkG p - mkG Q - t * mkG (mkLin n K ℓ) := by
      rw [map_sub, map_sub, map_mul, hqq]
    rw [e1]
    rw [← ht, sub_self]
  have hcomp := homogeneousComponent_mem_span_of_isHomogeneous G hG
    (p - Q - qq * mkLin n K ℓ) hRmem d
  have hp_self : MvPolynomial.homogeneousComponent d p = p :=
    MvPolynomial.homogeneousComponent_eq_self hp
  have hQ_zero : MvPolynomial.homogeneousComponent d Q = 0 :=
    homogeneousComponent_lowSum_eq_zero n K q d hq
  have hmul : MvPolynomial.homogeneousComponent d (qq * mkLin n K ℓ)
      = MvPolynomial.homogeneousComponent (d - 1) qq * mkLin n K ℓ := by
    have hd : d = (d - 1) + 1 := by omega
    conv_lhs => rw [hd]
    exact homogeneousComponent_mul_of_isHomogeneous_right qq (mkLin n K ℓ) (d - 1) 1
      (mkLin_isHomogeneous n K ℓ)
  have hRcomp : MvPolynomial.homogeneousComponent d (p - Q - qq * mkLin n K ℓ)
      = p - MvPolynomial.homogeneousComponent (d - 1) qq * mkLin n K ℓ := by
    rw [map_sub, map_sub, hp_self, hQ_zero, hmul, sub_zero]
  rw [hRcomp] at hcomp
  have hmk0 : mkG p - mkG (MvPolynomial.homogeneousComponent (d - 1) qq)
      * mkG (mkLin n K ℓ) = 0 := by
    have h0 := Ideal.Quotient.eq_zero_iff_mem.mpr hcomp
    rwa [map_sub, map_mul] at h0
  have hmem2 : mkG p ∈ Ideal.span ({mkG (mkLin n K ℓ)} : Set (coneQuotient n K G)) := by
    rw [Ideal.mem_span_singleton']
    refine ⟨mkG (MvPolynomial.homogeneousComponent (d - 1) qq), ?_⟩
    exact (sub_eq_zero.mp hmk0).symm
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem2

/-- `CfsecDisjointData` shape with `Cfsec` membership replaced by an explicit
lower-sum representation: a degree-`d` section class (`0 < d`) admitting a
lower-degree sum representation vanishes (`y = 0`), from quadrics-homogeneity
`hG` alone. The `HilbertFunctionCount`-side `Cfsec → sum` lattice bridge (mechanical, no
geometry) closes the gap to formal `CfsecDisjointData`; see the section
docstring above.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ChartFiltration`,
  `Appendix_FixedPoint.BezoutChain.sectionPiece`
  (imported above; membership unfolding).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.Elimination`,
  `Appendix_FixedPoint.BezoutChain.sectionPiece_of_lowSum_eq_zero` (this module).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.CfsecDisjointData`,
  `Appendix_FixedPoint.BezoutChain.Cfsec` (cited by name).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.Counting`,
  `Appendix_FixedPoint.BezoutChain.cfsec_disjoint_zero`
  (cited by name, level-`0` case). -/
theorem sectionPiece_disjoint_lowerSum_of_quadrics (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hG : ∀ i, (G i).IsHomogeneous 2)
    (d : ℕ) (hpos : 0 < d)
    (y : sectionQuotient n K G ℓ)
    (hy1 : y ∈ sectionPiece n K G ℓ d)
    (q : ℕ → MvPolynomial (Fin (n + 2)) K) (hq : ∀ e, e < d → (q e).IsHomogeneous e)
    (hy2 : y = ∑ e ∈ Finset.range d, Ideal.Quotient.mk (Ideal.span
        ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
          Set (coneQuotient n K G)))
        (Ideal.Quotient.mk (Ideal.span (Set.range G)) (q e))) : y = 0 := by
  obtain ⟨p, hp, hp_eq⟩ := hy1
  have heq : Ideal.Quotient.mk (Ideal.span
        ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
          Set (coneQuotient n K G)))
        (Ideal.Quotient.mk (Ideal.span (Set.range G)) p)
      = ∑ e ∈ Finset.range d, Ideal.Quotient.mk (Ideal.span
        ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
          Set (coneQuotient n K G)))
        (Ideal.Quotient.mk (Ideal.span (Set.range G)) (q e)) := hp_eq.trans hy2
  have hzero := sectionPiece_of_lowSum_eq_zero n K G ℓ hG d hpos p hp q hq heq
  rw [hp_eq] at hzero
  exact hzero

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

/-! ## BridgeToFixedPoint/vanishing close lane (bridge lane)

equiv-vs-finrank decision (task 1 — per-`hlin`-consumer routing). Every `hlin`
consumer in the owned files needs only the finrank equation
`finrank chart = finrank section`, never the `LinearEquiv` itself:

* `Counting.chart_length_eq_sum_pieces`, `Counting.sum_mult_eq_sum_pieces`,
  `Counting.chart_length_eq_sum_pieces_of_data`,
  `Counting.sum_mult_eq_sum_pieces_of_data`: each applies `chart_bridge`
  then transits into a length identity — rewired to the finrank form
  (`Counting.chart_bridge_eq_of_final`, that file) rather than the equiv.
* `Statement.exists_another_point_of_smooth_point` (`hbridge` slot) and
  `BridgeToFixedPoint.CountAssembly.hbridge_of_hlin` (cited by name): same equation —
  closed by `Statement.hbridge_of_final` (that file, finrank route).
* `LocalMultiplicity.chartFinite_of_sectionEquiv`, `LocalMultiplicity.hfinChartLocal`
  (cited by name — read-only file): the only consumers needing an actual
  `LinearEquiv` (as a surjection source for finiteness transfer) — supplied
  by `chart_bridge_equiv_of_final` below.

Choice summary: finrank rewire for all equation consumers (shorter: no
`Classical.choice`, no chart-finiteness instance needed); equiv proved once
below as the discharge-all for the two genuine-equiv consumers. No natural
map `chartRing → sectionQuotient` is claimed (`chartRing = (S_ℓ)₀` vs
`sectionQuotient = S/ℓS`); the equiv is non-canonical, from equal finranks.

hvan routing (task 2 — this file). `chartStab_of_hvan` and
`hfilter_of_cfsecSide` consume `hvan`, whose closure
(`HilbertFunctionCount.fsec_vanishing_of_stabAbove` from `cfsec_stab_section` +
`hdisj_full_of_quadrics`, both cited by name) lives in the unimportable
`HilbertFunctionCount` (import cycle). So this file forwards `hvan`; the discharge is
proved at the instantiation sites: `Counting.hvan_final` /
`Counting.chartStab_of_final` /
`Counting.hfilter_cfsecSide_of_final` and
`Statement.hbridge_of_final` (each cited by name), all unconditional on
exactly `[hG, hreg, hZd]`. GRADE (this file): equiv unconditional on the
`chart_bridge_of_final` inputs + chart finiteness; `hvan` conditional with
exact downstream discharge (proved this lane).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
/-- The `chart_bridge` identification (`hlin`) from a finrank equation: two
finite `K`-spaces of equal finrank are `K`-linearly equivalent
(non-canonical — `Classical.choice` inside `ofFinrankEq`). The discharge-all
for the two genuine-equiv consumers (`LocalMultiplicity.chartFinite_of_sectionEquiv`,
`LocalMultiplicity.hfinChartLocal`, cited by name).

## References

* `Mathlib/LinearAlgebra/Dimension/Free.lean`, `LinearEquiv.ofFinrankEq`
  (`[Module.Free]`/`[StrongRankCondition]` over the field `K` by instance). -/
noncomputable def chart_bridge_equiv_of_eq (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    [Module.Finite K (chartRing n K G ℓ)]
    [Module.Finite K (sectionQuotient n K G ℓ)]
    (heq : Module.finrank K (chartRing n K G ℓ)
      = Module.finrank K (sectionQuotient n K G ℓ)) :
    (chartRing n K G ℓ) ≃ₗ[K] (sectionQuotient n K G ℓ) :=
  LinearEquiv.ofFinrankEq _ _ heq

/-- The `chart_bridge` identification from the proved finrank inputs: same
inputs as `chart_bridge_of_final` plus chart finiteness (via
`chart_finite_of_sectionPiece_vanishing` from `hvan`, cited above — closed
downstream by `Counting.hvan_final`, cited by name).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.Elimination`,
  `Appendix_FixedPoint.BezoutChain.chart_bridge_of_final`,
  `Appendix_FixedPoint.BezoutChain.chart_bridge_equiv_of_eq`
  (this module). -/
noncomputable def chart_bridge_equiv_of_final (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (B : ℕ)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    (hG : ∀ i, (G i).IsHomogeneous 2)
    [Module.Finite K (sectionQuotient n K G ℓ)]
    [Module.Finite K (chartRing n K G ℓ)]
    (hstab : chartPiece n K G ℓ B = ⊤)
    (Cf : ℕ → Submodule K (sectionQuotient n K G ℓ))
    (hC0 : Cf 0 = ⊥) (hCtop : Cf (B + 1) = ⊤)
    (hCstep : ∀ d, d ≤ B → Module.finrank K ↥(Cf (d + 1))
      = Module.finrank K ↥(Cf d)
        + Module.finrank K ↥(sectionPiece n K G ℓ d))
    (hS0 : Module.finrank K ↥(sectionPiece n K G ℓ 0) = 1) :
    (chartRing n K G ℓ) ≃ₗ[K] (sectionQuotient n K G ℓ) :=
  chart_bridge_equiv_of_eq n K G ℓ
    (chart_bridge_of_final n K G ℓ B hreg hG hstab Cf hC0 hCtop hCstep hS0)

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

/-! ## Ffun-filtration transport (Ffun-filtration lane)

L-FILT reduction (this lane). The `FinalResiduals` `hfilter` slot
(`BridgeToFixedPoint/FinalDischargeHub.lean`, cited by name) and the `bezout_quadrics`
`hfilter` hypothesis (`BridgeToFixedPoint/FixedPointFromBezout.lean`, cited by name)
quantify `Cf` over `Submodule K (sectionQuotient …)` — the same type as the
closed `Fsec` filtration — and differ from it only in the `F` argument
(`Ffun` vs `Fsec`). Hence no new `Cf`-construction for the
`stagePiece`/`secIdeal` pieces is needed: the same `B`/`Cf` works, and the
whole `Ffun`-filtration reduces to the two transport lemmas below plus the
exact residual list underneath. This dissolves the "filtration geometry"
reading of L-FILT into linear algebra (one pointwise finrank equation).

* `hfilter_F_of_cfsecSide`: the verbatim consumer `hfilter` shape for a
  general `F : ℕ → ℕ`, from the `Cfsec`-side raw inputs in
  `sectionPiece`-finrank form (the `hfilter_of_cfsecSide` input style) plus
  the pointwise bridge `hF : ∀ d, F d = finrank (sectionPiece d)`.
* `hfilter_F_of_fsecSide`: same conclusion from the assembled
  `sectionPiece`-form `∃` (i.e. `Statement.hfilter_fsec_of_final`'s
  conclusion, cited by name, up to the `Fsec` definitional unfolding
  `Fsec … d = finrank (sectionPiece d)` by `rfl`) plus `hF`.

Instantiation (import-capable site, e.g. `FinalDischargeHub`): `F := Ffun …`
with `hF` the pointwise `Ffun` equation (residual (1) below) and the
`sectionPiece`-side input from `Statement.hfilter_fsec_of_final`
(residual (2) below, already closed).

conditional-exact residuals (nothing else assumed):
1. `hF-at-Ffun`: `∀ d, Ffun … d = finrank (sectionPiece … d)` — the
   double-quotient (`(R ⧸ span G) ⧸ span {ℓ̄}`) vs joined-ideal
   (`span G ⊔ span {ℓ}`) presentation bridge, by the third isomorphism
   theorem + homogeneous division (the `stepCokerEquiv` machinery,
   `MkSystemSESData`, cited by name). Provable only at an
   import-capable site (this module cannot name `Ffun`: `MkSystemSESData`
   imports `HilbertFunctionCount` imports this module — an import would cycle).
2. `sectionPiece`-side input — closed: `Statement.hfilter_fsec_of_final`
   (cited by name), unconditional on exactly `[hreg, hZd, hG]`.

Status: `Ffun`-filtration transport unconditional in-file (both lemmas
proved); end-to-end `hfilter` slot conditional-exact
`[hF-at-Ffun, hreg, hZd, hG]`.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
/-- The verbatim consumer `hfilter` shape for a general `F`, from the
`Cfsec`-side raw inputs in `sectionPiece`-finrank form plus the pointwise
bridge `hF`. The `Ffun` instantiation (`F := Ffun …`, cited by name) closes
the `FinalResiduals` `hfilter` slot once residual `hF-at-Ffun` proves.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ChartFiltration`,
  `Appendix_FixedPoint.BezoutChain.sectionPiece` (imported above; the `hF` right-hand side).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.FinalDischargeHub`,
  `Appendix_FixedPoint.BezoutChain.FinalDischargeHub.FinalResiduals` (cited by name: binder shape).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.FixedPointFromBezout`,
  `Appendix_FixedPoint.BezoutChain.bezout_quadrics` (cited by name: `hfilter` hypothesis shape).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Regularity.Avoid.MkSystemSESData`,
  `Appendix_FixedPoint.BezoutChain.MkSystemSESData.Ffun` (cited by name: the `F` instantiation). -/
theorem hfilter_F_of_cfsecSide (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (F : ℕ → ℕ)
    (hF : ∀ d, F d = Module.finrank K ↥(sectionPiece n K G ℓ d))
    (B : ℕ)
    (Cf : ℕ → Submodule K (sectionQuotient n K G ℓ))
    (hC0 : Cf 0 = ⊥) (hCtop : Cf (B + 1) = ⊤)
    (hCstep : ∀ d, d ≤ B → Module.finrank K ↥(Cf (d + 1))
      = Module.finrank K ↥(Cf d)
        + Module.finrank K ↥(sectionPiece n K G ℓ d))
    (hvan : ∀ d, B < d → Module.finrank K ↥(sectionPiece n K G ℓ d) = 0) :
    ∃ (B' : ℕ) (Cf' : ℕ → Submodule K (sectionQuotient n K G ℓ)),
      Cf' 0 = ⊥ ∧ Cf' (B' + 1) = ⊤ ∧
      (∀ d, d ≤ B' → Module.finrank K ↥(Cf' (d + 1))
        = Module.finrank K ↥(Cf' d) + F d) ∧
      ∀ d, B' < d → F d = 0 := by
  refine ⟨B, Cf, hC0, hCtop, ?_, ?_⟩
  · intro d hd
    rw [hCstep d hd, hF d]
  · intro d hd
    rw [hF d]
    exact hvan d hd

/-- The verbatim consumer `hfilter` shape for a general `F`, from the
assembled `sectionPiece`-form `∃` (i.e. `hfilter_fsec_of_final`'s
conclusion up to the `Fsec` `rfl`-unfolding) plus the pointwise bridge `hF`.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.Elimination`,
  `Appendix_FixedPoint.BezoutChain.hfilter_F_of_cfsecSide` (this module).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Statement.Statement`,
  `Appendix_FixedPoint.BezoutChain.hfilter_fsec_of_final` (cited by name: the `hsec` supplier,
  unconditional on `[hreg, hZd, hG]`).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.Fsec`
  (cited by name: `Fsec … d` unfolds to the `hsec` summand by `rfl`). -/
theorem hfilter_F_of_fsecSide (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (F : ℕ → ℕ)
    (hF : ∀ d, F d = Module.finrank K ↥(sectionPiece n K G ℓ d))
    (hsec : ∃ (B : ℕ) (Cf : ℕ → Submodule K (sectionQuotient n K G ℓ)),
      Cf 0 = ⊥ ∧ Cf (B + 1) = ⊤ ∧
      (∀ d, d ≤ B → Module.finrank K ↥(Cf (d + 1))
        = Module.finrank K ↥(Cf d)
          + Module.finrank K ↥(sectionPiece n K G ℓ d)) ∧
      ∀ d, B < d → Module.finrank K ↥(sectionPiece n K G ℓ d) = 0) :
    ∃ (B' : ℕ) (Cf' : ℕ → Submodule K (sectionQuotient n K G ℓ)),
      Cf' 0 = ⊥ ∧ Cf' (B' + 1) = ⊤ ∧
      (∀ d, d ≤ B' → Module.finrank K ↥(Cf' (d + 1))
        = Module.finrank K ↥(Cf' d) + F d) ∧
      ∀ d, B' < d → F d = 0 := by
  obtain ⟨B, Cf, hC0, hCtop, hCstep, hvan⟩ := hsec
  exact hfilter_F_of_cfsecSide n K G ℓ F hF B Cf hC0 hCtop hCstep hvan

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
