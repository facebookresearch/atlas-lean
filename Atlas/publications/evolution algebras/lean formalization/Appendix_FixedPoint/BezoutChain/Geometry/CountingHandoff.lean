/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Statement.Definitions
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Spectrum.Maximal.Defs

/-!
# Counting handoff: discharging `Counting.lean`'s ChartFiltration-owned hypotheses

This module discharges the explicit named hypotheses of
`EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.Counting` that belong to
ChartFiltration,
i.e. everything conditional except the LocalMultiplicity-owned
`hlocal`/`hadd`/`hpos`/`hloc` (supplied by
`EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.LocalMultiplicity`,
not redone here) and the inputs already consumed or retained by their
Counting-statement owners (`hS`, `hreg`), which stay put; `hZd` is assembled
conditionally from the `hcover` + `hcontra` shapes (gap G-hZd).

## Handoff mapping (which `Counting` hypothesis each theorem discharges)

* `finite_locus`'s `hcover`
  (`∃ t : Finset (Projectivization K (Fin (n + 2) → K)), vanishingLocus ⊆ ↑t`)
  ⇐ not discharged; gap G-cover below.
* `locus_nonempty`'s `hA`
  (`Nonempty (MaximalSpectrum (sectionQuotient n K G ℓ))`)
  ⇐ `section_maxSpec_nonempty` (proved here, from `hG0` alone), via the
  section-nontriviality step `section_nontrivial` and the general Zorn step
  `maxSpec_nonempty_of_nontrivial`.
* `locus_nonempty`'s `hlift`
  (old ∀ shape `∀ _M: MaximalSpectrum (sectionQuotient n K G ℓ),
    (vanishingLocus n K G).Nonempty`, superseded by the bare-∃ slot
  `hlift : (vanishingLocus n K G).Nonempty` — see
  `Geometry/Counting.lean`'s `locus_nonempty`, whose docstring records why
  the ∀ uniformity was dropped)
  ⇐ not discharged; gap G-lift below.
* `infinite_locus_of_not_zeroDim`'s `hcontra`
  (`(vanishingLocus n K G).Finite → IsZeroDimensional n K G`)
  ⇐ retained as the explicit Link-B hypothesis of the `hZd` assembly
  (`hZd_of_hcover_and_hcontra`); supplied conditionally, never proved
  unconditionally — gap G-hZd below.
* `finite_locus`'s `hZd` (`IsZeroDimensional n K G`)
  ⇐ `hZd_of_hcover_and_hcontra` (proved here, from the `hcover` + `hcontra`
  shapes) — although `finite_locus` itself never consumes `_hZd`, the same
  conclusion feeds the genuine `hZd` consumers (`bezout_quadratic`,
  `section_artinian`, `regular_chartForm_of_zeroDim`); see gap G-hZd.

## Notes on the `hA` discharge (reported deviations)

1. No Artinian input is used. The task hint suggests
   "Artinian + nontrivial via `section_artinian`", but maximal ideals exist by
   Zorn in any nontrivial commutative ring (`Ideal.exists_maximal`), so
   `section_artinian` (and hence `hreg`/`hZd`) is unnecessary for `hA`.
   The only input is `hG0` (equations vanish at `0`, immediate from
   homogeneity; same hypothesis shape as `ChartFiltration.evalAtZero`).
2. No `IsAlgClosed` hypothesis is needed either (Krull's theorem is not about
   algebraically closed fields); only `[Field K]` is kept, as required by the
   `coneQuotient`/`sectionQuotient` constructions.
3. The augmentation lift `augZero` below restates the
   `ChartFiltration.evalAtZero` pattern locally (same `Ideal.Quotient.lift`
   shape, `hG0` in place of nothing else) so that this handoff adds no new
   module dependencies — the same precedent as
   `LocalMultiplicity.coneEval`, which restates the pattern with `hvG` in place of
   `hG0` rather than importing `ChartFiltration`.

## Gaps (the deep geometric steps are documented, not taken)

* G-cover (`hcover`): `hcover` is equivalent to finiteness of the locus
  (`Set.Finite` ↔ `∃ t : Finset _, s ⊆ ↑t` via `Set.Finite.exists_finset_coe` /
  `Finset.finite_toSet` + `Set.Finite.subset`, all in
  `Mathlib/Data/Set/Finite/Basic.lean`). The covering step itself is trivial
  chart membership: every projective point has a nonzero coordinate, so the
  finitely many standard charts (indexed by `Fin (n + 2)`) cover projective
  space. The missing piece is per-chart finiteness: each chart piece of the
  locus is the affine zero locus of the dehomogenized system, and bounding it
  needs (i) MvPolynomial dehomogenization API — there is none in Mathlib
  v4.34.0 (the only `Homogenization.lean`,
  `Mathlib/LinearAlgebra/AffineSpace/Homogenization.lean`, is about
  homogenization of affine spaces, unrelated); (ii) the bridge "a positive
  dimensional finitely generated `K`-algebra over an infinite algebraically
  closed field has infinitely many `K`-points" (contrapositive gives chart
  finiteness from `IsZeroDimensional`) — no such API, although a proof
  starts from Noether normalization, which does exist
  (`Mathlib/RingTheory/NoetherNormalization.lean`,
  `exists_finite_inj_algHom_of_fg`, `exists_integral_inj_algHom_of_quotient`).
  Note a single section chart `D₊(ℓ)` does not cover projective space (it
  misses `V(ℓ)`), so the Artinian-section route alone cannot yield `hcover`
  without the multi-chart argument above.
* G-lift (`hlift`): the conclusion does not mention `M`, so `hlift` is
  `(MaxSpec inhabited) → (locus nonempty)`. It cannot be proved by sending `M`
  to "its" projective point: pulling `M` back along the two quotient maps to a
  maximal ideal `m` of `MvPolynomial` and applying the affine weak
  Nullstellensatz (`MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton`,
  `Mathlib/RingTheory/Nullstellensatz.lean`) can yield the origin `x = 0`,
  which is not a projective point. Concrete obstruction: `n = 0`,
  `G₀ = X₀`, `ℓ = X₁` gives section `≅ K` whose unique maximal ideal pulls
  back to `⟨X₀, X₁⟩ = vanishingIdeal {(0, 0)}`, while the locus `{[0 : 1]}`
  is nonempty — from this `M` alone no projective point is definable. Hence
  any proof must establish locus-nonemptiness globally, i.e. the projective
  dimension theorem (`n + 1` homogeneous equations in `n + 2` unknowns over an
  algebraically closed field have a nontrivial common zero). There is no
  projective-Nullstellensatz / projective-dimension API in Mathlib v4.34.0;
  the in-tree height API (`Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean`)
  bounds prime heights but does not connect them to `vanishingLocus`.
* G-contra (`hcontra`): finiteness of the projective locus must force
  `Ring.KrullDimLE 1` of the cone. Mathematically this is the affine-cone
  picture (the cone over a finite point set is a finite union of lines through
  the origin, hence `≤ 1`-dimensional), but there is no API connecting
  `vanishingLocus`/`MvPolynomial.zeroLocus` finiteness to `Ring.KrullDimLE`
  (or to prime coheights) in Mathlib v4.34.0. The height bounds in
  `Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean`
  (e.g. `Ideal.height_span_le_ncard_of_span_ne_top`) go the wrong way
  (generators bound height from above only via minimal primes, and the
  projective-affine prime correspondence is itself part of this gap).
  For how `hcontra` now enters the `hZd`
  assembly conditionally, see G-hZd below.
* G-hZd (`hZd`): conditional assembly `hZd_of_hcover_and_hcontra` (plus the
  `mkSystem` instantiation `hZd_mkSystem_of_hcover_and_hcontra`): Link A
  `locus_finite_of_hcover` is proved here from the `hcover` shape with no
  `hZd` input; Link B is the explicit `hcontra`-shape hypothesis. Exact
  minimal hypothesis list: (H1) the `hcover` shape
  (`∃ t : Finset _, vanishingLocus n K G ⊆ ↑t`), supplied closed-modulo the
  explicit `ChartDimZero` by `ProjectiveLocus.hcover_of_chartDimZero`
  (residual R-dim: `IsZeroDimensional ⟹ ChartDimZero` — see `ProjectiveLocus`
  Obstruction (b)); (H2) the `hcontra` shape
  (`Finite → IsZeroDimensional`), supplied conditionally by
  `ProjectiveLocus.hcontra_of_krullDimLE_zero` modulo cone-`KrullDimLE 0`
  (a height-arithmetic feed: valid as a conditional supply, non-genuine as
  geometry — see the M-verdict below) or else residual R-cone. The
  `ProjectiveLocus` import is declined (that module imports this file, so the
  import would cycle); both supplies are wired by verbatim-shape hypotheses,
  each cited by declaration name. Section finiteness enters hZd-free:
  `section_krullDimLE_zero_of_artinian` /
  `section_artinian_of_krullDimLE_zero` (Artinian section ↔ `KrullDimLE 0`
  section, proved here) pin its exact formal content; it dead-ends before
  `hZd` (no in-tree cone-section upper bound), in contrast with
  `Elimination.section_artinian`, which consumes `hZd`.
  M-verdict (pure height arithmetic cannot yield `hZd`): the in-tree height
  API bounds heights from above via minimal primes and quotient dimensions
  from below (`Ideal.height_span_le_card_of_span_ne_top`,
  `ringKrullDim_quotient_succ_le_of_nonZeroDivisor`) — every bound points
  away from the needed `≤ 1` upper bound. `G = 0` (empty system: cone =
  whole polynomial ring of dimension `n + 2 > 1`, locus = all of projective
  space) refutes every unconditional or pure-height-arithmetic route.
  Sharpening: over a finite field `G = 0` even satisfies (H1) (the
  whole-space locus is a finite set) while violating `hZd` — so (H2) is
  essential and cannot be dropped; and (H2) is itself false unconditionally
  for the same example (finite locus, dimension `n + 2`), so it stays an
  explicit hypothesis. Residuals: R-dim (chart-dimension drop
  `IsZeroDimensional ⟹ ChartDimZero`; grep evidence: `dehomog` (any case)
  has zero hits in `.lake/packages/mathlib/Mathlib/`); R-cone (finite locus
  ⟹ cone `KrullDimLE 1`, the cone-over-finite-set picture; grep evidence:
  `MvPolynomial.zeroLocus` occurs in exactly two Mathlib files
  (`Mathlib/RingTheory/Nullstellensatz.lean`,
  `Mathlib/ModelTheory/Algebra/Ring/Definability.lean`) with zero lines
  co-mentioning `Finite`/`Krull`/`DimLE`, and every `zeroLocus` hit under
  `Mathlib/RingTheory/KrullDimension/` is `PrimeSpectrum.zeroLocus` (the
  prime-ideal locus, unrelated to `K`-point finiteness); `vanishingLocus`
  itself is custom, so zero in-tree hits by construction).

## References

Mathlib v4.34.0 has no degree-of-variety or projective-locus API; the proved
results below are assembled from quotient, span, evaluation, and maximal-ideal
API. Per-declaration `## References` subsections cite the exact module path
and declaration name, each verified in-tree.

## Standing context (routine binders)

Named once here; per-decl docstrings below repeat GRADE verdicts and name only
substantive non-routine premises.

* `hG0 : ∀ i, MvPolynomial.eval 0 (G i) = 0` — equations vanish at the origin
  (the sole input of the `hA` discharge, via `augZero`).
* `hG : ∀ i, (G i).IsHomogeneous 2` — the quadric-system input.
* `hcover : ∃ t : Finset _, vanishingLocus n K G ⊆ ↑t` — finset-cover shape.
* `hcontra : (vanishingLocus n K G).Finite → IsZeroDimensional n K G` —
  the Link-B hypothesis of the `hZd` assembly.
* `hS`/`hZd`/`hreg`/`hc`/`hA`/`hlift` appear only as Counting-owned context
  (cited by name, never re-bound here).
* Instance: `[Field K]` throughout (no `IsAlgClosed` input is needed).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
/-! ## The `hA` discharge: the section has a maximal ideal -/

/-- Evaluation at `0` descends to the cone when every equation vanishes at `0`
(same `Ideal.Quotient.lift` pattern as `ChartFiltration.evalAtZero`, restated
here so this handoff adds no new module dependencies; cf. the
`LocalMultiplicity.coneEval` precedent).

## References

* `Mathlib/RingTheory/Ideal/Quotient/Defs.lean`, `Ideal.Quotient.lift`.
* `Mathlib/RingTheory/Ideal/Span.lean`, `Ideal.span_le`.
* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.eval` (ring hom). -/
private noncomputable def augZero (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hG0 : ∀ i, MvPolynomial.eval (0 : Fin (n + 2) → K) (G i) = 0) :
    coneQuotient n K G →+* K :=
  Ideal.Quotient.lift _ (MvPolynomial.eval 0) (fun a ha => by
    have hsub : Ideal.span (Set.range G)
        ≤ RingHom.ker (MvPolynomial.eval (0 : Fin (n + 2) → K) :
          MvPolynomial _ _ →+* K) := by
      rw [Ideal.span_le]
      intro x hx
      obtain ⟨i, rfl⟩ := hx
      exact RingHom.mem_ker.mpr (hG0 i)
    exact RingHom.mem_ker.mp (hsub ha))

/-- The augmentation sends the section linear form to `0` (it is a linear form
evaluated at `0`).

## References

* `Mathlib/RingTheory/Ideal/Quotient/Defs.lean`, `Ideal.Quotient.lift_mk`
  (`rfl`-lemma, used via definitional unfolding in `show`).
* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.eval_C`,
  `MvPolynomial.eval_X`. -/
private theorem augZero_mkLin (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hG0 : ∀ i, MvPolynomial.eval (0 : Fin (n + 2) → K) (G i) = 0) :
    augZero n K G hG0
        (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) = 0 := by
  change MvPolynomial.eval (0 : Fin (n + 2) → K) (mkLin n K ℓ) = 0
  unfold mkLin
  simp

/-- The regular section is nontrivial: `ℓ̄` is a non-unit (it dies under the
augmentation), so cutting by it cannot kill the whole cone. Only `hG0` is
needed — not `hS`, `hreg`, or `hZd`.

## References

* `Mathlib/RingTheory/Ideal/Quotient/Defs.lean`,
  `Ideal.Quotient.eq_zero_iff_mem`
  (`mk I a = 0 ↔ a ∈ I`).
* `Mathlib/RingTheory/Ideal/Span.lean`, `Ideal.mem_span_singleton'`
  (`x ∈ span {y} ↔ ∃ a, a * y = x`). -/
theorem section_nontrivial (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hG0 : ∀ i, MvPolynomial.eval (0 : Fin (n + 2) → K) (G i) = 0) :
    Nontrivial (sectionQuotient n K G ℓ) := by
  refine ⟨1, 0, ?_⟩
  intro h10
  have h0 : Ideal.Quotient.mk (Ideal.span
      ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
        Set (coneQuotient n K G))) (1 : coneQuotient n K G) = 0 := by
    rw [map_one]
    exact h10
  have hmem : (1 : coneQuotient n K G) ∈ Ideal.span
      ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
        Set (coneQuotient n K G)) :=
    (Ideal.Quotient.eq_zero_iff_mem).mp h0
  obtain ⟨s, hs⟩ := (Ideal.mem_span_singleton').mp hmem
  have hℓ0 := augZero_mkLin n K G ℓ hG0
  have h1 := congrArg (augZero n K G hG0) hs
  rw [map_mul, hℓ0, mul_zero, map_one] at h1
  exact one_ne_zero h1.symm

/-- Zorn step: any nontrivial commutative (semi)ring has a maximal ideal
(Krull's theorem), hence inhabited maximal spectrum.

## References

* `Mathlib/RingTheory/Ideal/Maximal.lean`, `Ideal.exists_maximal`
  (`∃ M : Ideal α, M.IsMaximal`, needs only `[Semiring α] [Nontrivial α]`).
* `Mathlib/RingTheory/Spectrum/Maximal/Defs.lean`, `MaximalSpectrum`
  (`structure MaximalSpectrum (R : Type*) [CommSemiring R]` with `asIdeal`,
  `isMaximal`). -/
theorem maxSpec_nonempty_of_nontrivial (R : Type*) [CommSemiring R]
    [Nontrivial R] : Nonempty (MaximalSpectrum R) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal R
  exact ⟨⟨M, hM⟩⟩

/-- `locus_nonempty`'s `hA` (the section-nontriviality input): the section has
a maximal ideal as soon as the equations vanish at `0`. Assembled from
`section_nontrivial` and `maxSpec_nonempty_of_nontrivial`.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.Counting`,
  `Appendix_FixedPoint.BezoutChain.locus_nonempty` (whose `hA`
  slot this fills). -/
theorem section_maxSpec_nonempty (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hG0 : ∀ i, MvPolynomial.eval (0 : Fin (n + 2) → K) (G i) = 0) :
    Nonempty (MaximalSpectrum (sectionQuotient n K G ℓ)) := by
  have hNT := section_nontrivial n K G ℓ hG0
  exact maxSpec_nonempty_of_nontrivial _

/-! ## The `hZd` assembly: `hcover` + `hcontra` give cone `KrullDimLE 1` -/

/-- Locus finiteness from a finset cover (Link A of the `hZd` assembly):
`finite_locus`'s `hcover` slot yields `(vanishingLocus n K G).Finite` with no
`hZd` input — `Counting.finite_locus` takes `_hZd` but never consumes it.
Restated here (same `Finset.finite_toSet` + `Set.Finite.subset` pattern) so
this handoff keeps its narrow import closure (restating the pattern rather
than widening imports); cf. the `augZero` precedent.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.Counting`,
  `Appendix_FixedPoint.BezoutChain.finite_locus` (pattern
  restated, not imported).
* `Mathlib/Data/Set/Finite/Basic.lean`, `Finset.finite_toSet`
  (`theorem finite_toSet (s : Finset α) : (s : Set α).Finite`),
  `Set.Finite.subset`
  (`theorem Finite.subset (hs : s.Finite) (ht : t ⊆ s) : t.Finite`). -/
theorem locus_finite_of_hcover (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hcover : ∃ t : Finset (Projectivization K (Fin (n + 2) → K)),
      vanishingLocus n K G ⊆ ↑t) :
    (vanishingLocus n K G).Finite := by
  obtain ⟨t, ht⟩ := hcover
  exact (Finset.finite_toSet t).subset ht

/-- `hZd` assembly (conditional, exact hypothesis list — see gap G-hZd):
the `hcover` shape plus the `hcontra` shape yield `IsZeroDimensional n K G`
(the cone-`KrullDimLE 1` consumer slot, used verbatim — not the stronger
cone-`KrullDimLE 0`, not section data). Link A is `locus_finite_of_hcover`
(proved above); Link B is the explicit `hcontra` hypothesis (binder shape
copied verbatim from `Counting.infinite_locus_of_not_zeroDim`). The
`ProjectiveLocus` supplies (`hcover_of_chartDimZero` modulo `ChartDimZero`;
`hcontra_of_krullDimLE_zero` modulo cone-`KrullDimLE 0`) are wired by these
verbatim shapes — that module imports this file, so it is cited, not imported
(the import would cycle).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.Counting`,
  `Appendix_FixedPoint.BezoutChain.infinite_locus_of_not_zeroDim` (whose `hcontra` slot Link B
  copies).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ProjectiveLocus`,
  `Appendix_FixedPoint.BezoutChain.hcover_of_chartDimZero`,
  `Appendix_FixedPoint.BezoutChain.hcontra_of_krullDimLE_zero`
  (conditional suppliers, cited not imported).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.CountingHandoff`,
  `Appendix_FixedPoint.BezoutChain.locus_finite_of_hcover` (Link A, proved above). -/
theorem hZd_of_hcover_and_hcontra (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hcover : ∃ t : Finset (Projectivization K (Fin (n + 2) → K)),
      vanishingLocus n K G ⊆ ↑t)
    (hcontra : (vanishingLocus n K G).Finite → IsZeroDimensional n K G) :
    IsZeroDimensional n K G :=
  hcontra (locus_finite_of_hcover n K G hcover)

/-- `hZd` at `mkSystem` shape: the assembly above instantiated at the canonical
system `G := mkSystem n K F` (the exact object the fixed-point consumer
instantiates). No homogeneity input is needed for the assembly itself — `hF`
is consumed upstream when the `hcover` shape is discharged via
`hcover_mkSystem_of_zeroDim`; here both shapes are explicit hypotheses.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Statement.Definitions`,
  `Appendix_FixedPoint.BezoutChain.mkSystem`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ProjectiveLocus`,
  `Appendix_FixedPoint.BezoutChain.hcover_mkSystem_of_zeroDim` (shape mirror of this bundle).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.CountingHandoff`,
  `Appendix_FixedPoint.BezoutChain.hZd_of_hcover_and_hcontra` (proved above). -/
theorem hZd_mkSystem_of_hcover_and_hcontra (n : ℕ) (K : Type*) [Field K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hcover : ∃ t : Finset (Projectivization K (Fin (n + 2) → K)),
      vanishingLocus n K (mkSystem n K F) ⊆ ↑t)
    (hcontra : (vanishingLocus n K (mkSystem n K F)).Finite →
      IsZeroDimensional n K (mkSystem n K F)) :
    IsZeroDimensional n K (mkSystem n K F) :=
  hZd_of_hcover_and_hcontra n K _ hcover hcontra

/-- Section finiteness is section dimension zero (hZd-free): an Artinian
section has `KrullDimLE 0`. This pins the exact hZd-free formal content of the
"section finiteness" input — it dead-ends before `hZd` (no in-tree
cone-section upper bound; see gap G-hZd), in contrast with
`Elimination.section_artinian`, which goes the other way and consumes `hZd`.

## References

* `Mathlib/RingTheory/HopkinsLevitzki.lean`,
  `isArtinianRing_iff_krullDimLE_zero` (needs the `[IsNoetherianRing _]`
  instance, via `Mathlib/RingTheory/Ideal/Quotient/Noetherian.lean`,
  `Ideal.Quotient.isNoetherianRing`).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.Elimination`,
  `Appendix_FixedPoint.BezoutChain.section_artinian`
  (the converse-direction result, which consumes `hZd`). -/
theorem section_krullDimLE_zero_of_artinian (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hArt : IsArtinianRing (sectionQuotient n K G ℓ)) :
    Ring.KrullDimLE 0 (sectionQuotient n K G ℓ) :=
  (isArtinianRing_iff_krullDimLE_zero (R := sectionQuotient n K G ℓ)).mp hArt

/-- Section dimension zero is section finiteness (hZd-free converse): a
zero-dimensional section is Artinian (Noetherian as an iterated quotient of
`MvPolynomial`). Together with `section_krullDimLE_zero_of_artinian` this is
the hZd-free equivalence `Artinian section ↔ KrullDimLE 0 section` — the form
in which section finiteness enters the `hZd` chain (documented context for the
future genuine `hcontra` proof, not a proof of `hZd`; see G-hZd).

## References

* `Mathlib/RingTheory/HopkinsLevitzki.lean`,
  `isArtinianRing_iff_krullDimLE_zero` (same `iff` as above).
* `Mathlib/RingTheory/Ideal/Quotient/Noetherian.lean`,
  `Ideal.Quotient.isNoetherianRing` (the instance this needs). -/
theorem section_artinian_of_krullDimLE_zero (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hdim : Ring.KrullDimLE 0 (sectionQuotient n K G ℓ)) :
    IsArtinianRing (sectionQuotient n K G ℓ) :=
  (isArtinianRing_iff_krullDimLE_zero (R := sectionQuotient n K G ℓ)).mpr hdim

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
