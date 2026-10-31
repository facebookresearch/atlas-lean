/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Statement.Statement
import Appendix_FixedPoint.BezoutChain.Geometry.CountingHandoff
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Set.Image
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Spectrum.Maximal.Defs
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Data.Fin.SuccPred

/-!
# Projective-locus toolkit (Group 1 — Counting's three general-G gaps)

This module targets the three open hypotheses of
`EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Counting` documented in
`EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.CountingHandoff`'s gap G-cover / G-lift /
G-contra:

* `finite_locus`'s `hcover`
  (`∃ t : Finset (Projectivization K (Fin (n + 2) → K)), vanishingLocus ⊆ ↑t`);
* `locus_nonempty`'s `hlift` (old ∀ shape
  (`∀ _M: MaximalSpectrum (sectionQuotient n K G ℓ),
    (vanishingLocus n K G).Nonempty`), now superseded by the bare-∃ slot
  `hlift : (vanishingLocus n K G).Nonempty` in `Geometry/Counting.lean`'s
  `locus_nonempty`; `hlift_of_nonzero_zero` below still proves the old ∀
  shape, hence supplies the new ∃ shape at the `hA` witness);
* `infinite_locus_of_not_zeroDim`'s `hcontra`
  (`(vanishingLocus n K G).Finite → IsZeroDimensional n K G`).

Status: (b) is conditional-single-residual (global `hcover` from per-chart
affine covers, proved below as `hcover_of_chartDimZero` with the `mkSystem`
bundle `hcover_mkSystem_of_zeroDim`, conditional on the single explicit
hypothesis `ChartDimZero` — chart-dimension drop from `IsZeroDimensional`;
residual R-dim in `## Obstruction (b)`). The affine bridge
(`zeroLocus_finite_of_krullDimLE_zero`) and the all-chart dehomogenization
plus transfer (`dehomogAt*`, `chart_cover_of_affine_cover_at`) are closed.
(a) and (c) land proved true steps plus precise
`## Obstruction` notes; the remaining geometric content (projective dimension
theorem; cone-over-finite-set dimension bound) has no in-tree API and is
documented, not taken. (d) wires the proved links into the end-to-end
`hZd_of_chartDimZero_and_hcontra` chain (residuals R-dim/R-cone unchanged).

## References

Mathlib v4.34.0 has no projective-Nullstellensatz / projective-dimension /
degree-of-variety API; the results below are assembled from quotient,
evaluation, finiteness, height, and maximal-spectrum API. Per-declaration
`## References` subsections cite the exact module path and declaration name,
each verified in-tree by `grep -rn` in `.lake/packages/mathlib`.

## Standing context (routine binders)

Named once here; per-decl docstrings below repeat GRADE verdicts and name only
substantive non-routine premises.

* `hF`/`hG : ∀ i, (G i).IsHomogeneous 2` (resp. `(d i)`) — homogeneous input
  family; `hG0 : ∀ i, eval 0 (G i) = 0` — vanishing at the origin.
* `hc : v c ≠ 0` — chart-coordinate nonvanishing;
  `hGv : ∀ i, eval v (G i) = 0` — affine equations at `v`.
* Counting-link inputs: `hcharts`, `hcover`, `hcontra`, `hlift`.
* `hdrop : ChartDimZero n K G` — the single residual hypothesis (R-dim);
  `hdim : Ring.KrullDimLE 0 …` — affine-dimension input;
  `hex` — nonzero-common-zero existence.
* Instances: `[Field K]` throughout; `[IsAlgClosed K]` where the
  Nullstellensatz feeds in.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
open scoped BigOperators

/-! ## (a) hlift-target: projective dimension theorem -/

/-- Homogeneous scaling law (new; no in-tree version exists): evaluating a
homogeneous degree-`m` polynomial at a scaled point pulls out `a ^ m`.
Proved by induction over the monomial support (`as_sum`), using
`eval_monomial` on each monomial and the weight condition on the support.

## References

* `Mathlib/Algebra/MvPolynomial/Basic.lean`, `MvPolynomial.as_sum`
  (`theorem as_sum (p) : p = ∑ v ∈ p.support, monomial v (p.coeff v)`).
* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.eval_monomial`
  (`theorem eval_monomial:
    eval f (monomial s a) = a * s.prod fun n e => f n ^ e`).
* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.IsHomogeneous`
  (`def IsHomogeneous (φ) (n) := IsWeightedHomogeneous 1 φ n`).
* `Mathlib/RingTheory/MvPolynomial/WeightedHomogeneous.lean`,
  `MvPolynomial.IsWeightedHomogeneous`
  (`def IsWeightedHomogeneous (w) (φ) (m):=
    ∀ ⦃d⦄, φ.coeff d ≠ 0 → weight w d = m`).
* `Mathlib/Data/Finsupp/Weight.lean`, `Finsupp.weight_apply`
  (`theorem weight_apply (f) : weight w f = Finsupp.sum f (fun i c => c • w i)`).
* `Mathlib/Data/Finsupp/Defs.lean`, `Finsupp.mem_support_iff`
  (`theorem mem_support_iff : a ∈ f.support ↔ f a ≠ 0`).
* `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`,
  `Finset.prod_pow_eq_pow_sum`, `Finset.prod_mul_distrib`, `Finset.mul_sum`,
  `map_sum`. -/
theorem eval_smul_of_isHomogeneous {σ : Type*} {K : Type*} [CommSemiring K]
    {φ : MvPolynomial σ K} {m : ℕ}
    (hφ : φ.IsHomogeneous m) (a : K) (v : σ → K) :
    MvPolynomial.eval (a • v) φ = a ^ m * MvPolynomial.eval v φ := by
  rw [φ.as_sum]
  simp only [map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  have hsup : φ.coeff e ≠ 0 := Finsupp.mem_support_iff.mp he
  have hwt : Finsupp.weight (1 : σ → ℕ) e = m := hφ hsup
  rw [Finsupp.weight_apply] at hwt
  have hsum : e.sum (fun _ c => c) = m := by
    simpa using hwt
  simp only [MvPolynomial.eval_monomial]
  have hterm : e.prod (fun n en => ((a • v) n) ^ en)
      = a ^ m * e.prod (fun n en => (v n) ^ en) := by
    have h1 : ∀ n en, ((a • v) n) ^ en = a ^ en * (v n) ^ en := fun n en => by
      rw [Pi.smul_apply, smul_eq_mul, mul_pow]
    simp_rw [h1]
    unfold Finsupp.prod
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    have hnat : e.support.sum (fun n => e n) = m := by
      have h2 := hsum
      unfold Finsupp.sum at h2
      simpa using h2
    rw [hnat]
  rw [hterm, mul_left_comm]

/-- Eval-at-`0` bridge (F-HG0 leaf): a homogeneous system vanishes at `0`,
discharging the section-nontriviality input `hG0` of
`CountingHandoff.section_nontrivial` / `section_maxSpec_nonempty` from the
canonical system data `hG` (`Statement/Statement.lean`:
`∀ i, (G i).IsHomogeneous 2`). The consumer shape
`∀ i, MvPolynomial.eval 0 (G i) = 0` is matched verbatim; no adjustment was
needed. Proof: `eval_smul_of_isHomogeneous` at `a = 0` gives
`eval 0 = 0 ^ 2 * eval 0 = 0`.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ProjectiveLocus`,
  `Appendix_FixedPoint.BezoutChain.eval_smul_of_isHomogeneous` (proved above; the `a = 0` instance).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Statement.Statement`,
  `Appendix_FixedPoint.BezoutChain.mkSystem_homogeneous`
  (canonical supplier shape `∀ i, (G i).IsHomogeneous 2`).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.CountingHandoff`,
  `Appendix_FixedPoint.BezoutChain.section_nontrivial`
  (consumer shape `∀ i, MvPolynomial.eval 0 (G i) = 0`).
* `Mathlib/Algebra/GroupWithZero/Basic.lean`, `zero_pow`
  (`@[simp] lemma zero_pow : n ≠ 0 → (0 : M₀) ^ n = 0`). -/
theorem hG0_of_homogeneous_two (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hG : ∀ i, (G i).IsHomogeneous 2) :
    ∀ i, MvPolynomial.eval (0 : Fin (n + 2) → K) (G i) = 0 := by
  intro i
  have h := eval_smul_of_isHomogeneous (hG i) (0 : K) (0 : Fin (n + 2) → K)
  have h00 : (0 : K) • (0 : Fin (n + 2) → K) = 0 := by
    funext j
    simp
  rw [h00] at h
  simpa using h

/-- `hG0` at `mkSystem` shape (F-HG0 leaf, canonical instance): the system
`G := mkSystem n K F` vanishes at `0` whenever the input forms are homogeneous
quadratic. Chains `mkSystem_homogeneous` with `hG0_of_homogeneous_two`; feeds
`CountingHandoff.section_nontrivial` / `section_maxSpec_nonempty` at the exact
object the fixed-point consumer instantiates.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Statement.Statement`,
  `Appendix_FixedPoint.BezoutChain.mkSystem_homogeneous`
  (canonical supplier shape `∀ i, (G i).IsHomogeneous 2`).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ProjectiveLocus`,
  `Appendix_FixedPoint.BezoutChain.hG0_of_homogeneous_two` (proved above). -/
theorem hG0_of_mkSystem (n : ℕ) (K : Type*) [Field K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2) :
    ∀ i, MvPolynomial.eval (0 : Fin (n + 2) → K) ((mkSystem n K F) i) = 0 :=
  hG0_of_homogeneous_two n K _ (mkSystem_homogeneous n K F hF)

/-- `hA` at `mkSystem` shape: the section of the canonical system
`G := mkSystem n K F` has a maximal ideal as soon as the input forms are
homogeneous quadratic. Chains the mkSystem `hG0` (`hG0_of_mkSystem`) through
`CountingHandoff.section_nontrivial` and
`CountingHandoff.maxSpec_nonempty_of_nontrivial`. This is the exact object
the fixed-point consumer instantiates in `Counting.locus_nonempty`'s `hA`
slot.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ProjectiveLocus`,
  `Appendix_FixedPoint.BezoutChain.hG0_of_mkSystem` (mkSystem `hG0` from `hF`, proved above).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.CountingHandoff`,
  `Appendix_FixedPoint.BezoutChain.section_nontrivial`,
  `Appendix_FixedPoint.BezoutChain.maxSpec_nonempty_of_nontrivial`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Counting`,
  `Appendix_FixedPoint.BezoutChain.locus_nonempty` (whose `hA`
  slot this fills at mkSystem shape). -/
theorem section_maxSpec_nonempty_mkSystem (n : ℕ) (K : Type*) [Field K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (ℓ : Fin (n + 2) → K)
    (hF : ∀ i, (F i).IsHomogeneous 2) :
    Nonempty (MaximalSpectrum (sectionQuotient n K (mkSystem n K F) ℓ)) := by
  have hNT := section_nontrivial n K (mkSystem n K F) ℓ
    (hG0_of_mkSystem n K F hF)
  exact maxSpec_nonempty_of_nontrivial _

/-- Global Krull-height bound (the dimension half of the projective dimension
theorem): the ideal cut out by the `n + 1` equations has height at most
`n + 1`. The generator set is presented as a `Finset` image so the
Finset-card height bound applies directly.

## References

* `Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean`,
  `Ideal.height_span_le_card_of_span_ne_top`
  (`lemma height_span_le_card_of_span_ne_top {s: Finset R}
    (ht: Ideal.span (s: Set R) ≠ ⊤): (Ideal.span (s: Set R)).height ≤ s.card`).
* `Mathlib/Data/Finset/Card.lean`, `Finset.card_image_le`
  (`theorem card_image_le : #(s.image f) ≤ #s`).
* `Mathlib/Data/Fintype/Card.lean`, `Fintype.card_fin`
  (`theorem Fintype.card_fin (n) : Fintype.card (Fin n) = n`).
* `Mathlib/Data/Finset/Image.lean`, `Finset.coe_image`
  (`theorem coe_image : ↑(s.image f) = f '' ↑s`).
* `Mathlib/Data/Set/Image.lean`, `Set.image_univ`
  (`theorem image_univ : f '' univ = range f`). -/
theorem span_height_le (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hne : Ideal.span (Set.range G) ≠ ⊤) :
    (Ideal.span (Set.range G)).height ≤ n + 1 := by
  classical
  have hcoe : ((Finset.image G Finset.univ : Finset _) : Set _) = Set.range G := by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  have hcard : (Finset.image G Finset.univ).card ≤ n + 1 :=
    (Finset.card_image_le).trans_eq (by rw [Finset.card_univ, Fintype.card_fin])
  rw [← hcoe]
  refine (Ideal.height_span_le_card_of_span_ne_top (by rwa [hcoe])).trans ?_
  exact_mod_cast hcard

/-- Affine-to-projective bridge (global, no `M` used): a nonzero common zero
of a homogeneous system determines a projective point of the locus.
Scale-invariance is exactly `eval_smul_of_isHomogeneous`; the representative
change is `Projectivization.mk_eq_mk_iff'`.

Adaptations vs `Counting.locus_nonempty`'s `hlift`: two explicit inputs are
added — the degree function `d` with homogeneity `hG` (needed for
scale-invariance, absent from `hlift`'s shape) and the global nonzero-zero
existence `hex` (the projective-dimension content itself, left open in
`## Obstruction (a)`). No `IsAlgClosed` is needed for the bridge itself.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Statement`,
  `Appendix_FixedPoint.BezoutChain.vanishingLocus`.
* `Mathlib/LinearAlgebra/Projectivization/Basic.lean`,
  `Projectivization.mk`, `Projectivization.mk_eq_mk_iff'`
  (`theorem mk_eq_mk_iff' (v w) (hv) (hw):
    mk K v hv = mk K w hw ↔ ∃ a: K, a • w = v`). -/
theorem mem_locus_of_nonzero_zero (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (d : Fin (n + 1) → ℕ)
    (hG : ∀ i, (G i).IsHomogeneous (d i))
    (hex : ∃ v : Fin (n + 2) → K, v ≠ 0 ∧
      ∀ i, MvPolynomial.eval v (G i) = 0) :
    (vanishingLocus n K G).Nonempty := by
  obtain ⟨v, hv, hGv⟩ := hex
  refine ⟨Projectivization.mk K v hv, ?_⟩
  intro w hw hmk
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' K v w hv hw).mp hmk.symm
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ha
    exact hv ha.symm
  have hw' : w = a⁻¹ • v := by
    rw [← ha, ← mul_smul, inv_mul_cancel₀ ha0, one_smul]
  intro i
  rw [hw', eval_smul_of_isHomogeneous (hG i) _ _, hGv i, mul_zero]

/-- `hlift` from a global nonzero zero: this proves the old ∀-shaped slot
`∀ _M : MaximalSpectrum (sectionQuotient n K G ℓ), locus.Nonempty` (the shape
formerly quoted by `CountingHandoff` and `Counting.locus_nonempty`); the proof
ignores `M` (as it must — see the G-lift counterexample in `CountingHandoff`)
and applies the global bridge above.

Kept as a stronger supplier of the new bare-∃ slot
`hlift : (vanishingLocus n K G).Nonempty` of `Counting.locus_nonempty`
(`Geometry/Counting.lean`): instantiating this theorem at the `hA` witness
(`CountingHandoff.section_maxSpec_nonempty`, now fed from `hG` via
`hG0_of_homogeneous_two` above) discharges the ∃. It is not the slot itself.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Counting`,
  `Appendix_FixedPoint.BezoutChain.locus_nonempty` (whose old
  `hlift` ∀-slot this targeted; the current slot is the bare ∃, supplied by
  instantiating this theorem at the `hA` witness).
* `Mathlib/RingTheory/Spectrum/Maximal/Defs.lean`, `MaximalSpectrum`. -/
theorem hlift_of_nonzero_zero (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (d : Fin (n + 1) → ℕ)
    (hG : ∀ i, (G i).IsHomogeneous (d i))
    (hex : ∃ v : Fin (n + 2) → K, v ≠ 0 ∧
      ∀ i, MvPolynomial.eval v (G i) = 0)
    : ∀ _M : MaximalSpectrum (sectionQuotient n K G ℓ),
      (vanishingLocus n K G).Nonempty :=
  fun _ => mem_locus_of_nonzero_zero n K G d hG hex

/-! ## (a′) `z = 0` section at `mkSystem` shape (hz-block promotion) -/

/- ## Obstruction (a) — partial: existence of the nonzero common zero.

Proved above: the height bound (`span_height_le`: height of `span G ≤ n+1`)
and the bridge (nonzero affine zero ⟹ projective point ⟹ `hlift`).
What resists: producing `hex` for `n+1` homogeneous equations in `n+2`
unknowns over `IsAlgClosed K` — the projective dimension theorem. The
intended global route, with in-tree names verified by grep:

1. `span G ≠ ⊤` from homogeneity of positive degree (evaluation at `0`
   kills every equation; same `Ideal.Quotient.lift` pattern as
   `CountingHandoff.augZero`).
2. `ringKrullDim (MvPolynomial (Fin (n+2)) K) = n + 2` via
   `MvPolynomial.ringKrullDim_of_isNoetherianRing`
   (`Mathlib/RingTheory/KrullDimension/Polynomial.lean`) plus the field case.
3. Hence a minimal prime over `span G` (height `≤ n+1 < n+2`) is non-maximal;
   localize at it, take a maximal ideal above (`Ideal.exists_maximal`, cf.
   `CountingHandoff.maxSpec_nonempty_of_nontrivial`), and apply the affine
   weak Nullstellensatz
   `MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton`
   (`Mathlib/RingTheory/Nullstellensatz.lean`,
   `I.IsMaximal ↔ ∃ x, I = vanishingIdeal K {x}`) to get an affine point,
   nonzero because the prime is non-maximal.
4. Land it in the locus via `mem_locus_of_nonzero_zero` above.

Missing in-tree: the projective-affine prime correspondence linking prime
height to `vanishingLocus` (the height API in
`Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean` does not connect to
`vanishingLocus`; cf. `CountingHandoff` G-lift). From `M` alone no point is
definable: e.g. `n = 0`, `G₀ = X₀`, `ℓ = X₁` gives section `≅ K` whose
maximal ideal pulls back to `⟨X₀, X₁⟩ = vanishingIdeal {(0,0)}` while the
locus `{[0:1]}` is nonempty. -/

/-! ## (b) hcover-target: per-chart finiteness implies global finiteness -/

/-- The `i`-th standard affine chart `D₊(Xᵢ)` as a set of projective points:
those admitting a representative with nonzero `i`-th coordinate.

## References

* `Mathlib/LinearAlgebra/Projectivization/Basic.lean`, `Projectivization.mk`. -/
def chartSet (n : ℕ) (K : Type*) [Field K] (i : Fin (n + 2)) :
    Set (Projectivization K (Fin (n + 2) → K)) :=
  {p | ∃ v hv, Projectivization.mk K v hv = p ∧ v i ≠ 0}

/-- The standard charts cover projective space: every point has a nonzero
coordinate. Uses the canonical nonzero representative
(`Projectivization.rep`, `rep_nonzero`, `mk_rep`); no quotient induction is
needed since `Projectivization` is a quotient of the nonzero subtype.

## References

* `Mathlib/LinearAlgebra/Projectivization/Basic.lean`,
  `Projectivization.rep`, `Projectivization.rep_nonzero`
  (`theorem rep_nonzero (v) : v.rep ≠ 0`), `Projectivization.mk_rep`
  (`@[simp] theorem mk_rep (v) : mk K v.rep v.rep_nonzero = v`). -/
theorem rep_mem_chart (n : ℕ) (K : Type*) [Field K]
    (p : Projectivization K (Fin (n + 2) → K)) :
    ∃ i, p ∈ chartSet n K i := by
  have hne : Projectivization.rep p ≠ 0 := Projectivization.rep_nonzero p
  have hcoord : ∃ i, Projectivization.rep p i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hne (by funext i; simpa using hcon i)
  obtain ⟨i, hi⟩ := hcoord
  exact ⟨i, Projectivization.rep p, Projectivization.rep_nonzero p,
    Projectivization.mk_rep p, hi⟩

/-- Closed: per-chart finiteness yields `finite_locus`'s `hcover` (binder
shape copied verbatim from `Counting.finite_locus`). Given a finset cover of
each chart piece, the finite union over the `Fin (n+2)` charts covers the
locus. What remains outside this file is chart-piece finiteness from
`IsZeroDimensional` — see `## Obstruction (b)`.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Counting`,
  `Appendix_FixedPoint.BezoutChain.finite_locus` (whose `hcover`
  slot this discharges).
* `Mathlib/Data/Finset/Union.lean`, `Finset.mem_biUnion`
  (`lemma mem_biUnion : b ∈ s.biUnion t ↔ ∃ a ∈ s, b ∈ t a`). -/
theorem hcover_of_chart_covers (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hcharts : ∀ i : Fin (n + 2),
      ∃ t : Finset (Projectivization K (Fin (n + 2) → K)),
        chartSet n K i ∩ vanishingLocus n K G ⊆ ↑t) :
    ∃ t : Finset (Projectivization K (Fin (n + 2) → K)),
      vanishingLocus n K G ⊆ ↑t := by
  classical
  choose f hf using hcharts
  refine ⟨Finset.univ.biUnion f, fun p hp => ?_⟩
  obtain ⟨i, v, hv, rfl, hi⟩ := rep_mem_chart n K p
  rw [Finset.mem_coe, Finset.mem_biUnion]
  exact ⟨i, Finset.mem_univ i, hf i ⟨⟨v, hv, rfl, hi⟩, hp⟩⟩

/-! ## (b′) Dehomogenization at the `z`-chart (minimal fragment for G-cover)

The `hcover` residual needs each chart piece as the affine zero locus of a
dehomogenized system with degree control. This section proves the minimal
fragment at the `z`-chart (`j = Fin.last (n + 1)`, i.e. `D₊(X_last)`):

* `dehomogCoord` / `dehomogHom` / `dehomog`: dehomogenization `φ ↦ φ(x, 1)`
  as `eval₂Hom C g` (send `X_last ↦ 1`, keep the `x`-variables);
* `eval_dehomog`: evaluation commutes
  (`eval x (dehomog φ) = eval (snoc x 1) φ`);
* `totalDegree_dehomog_le` / `totalDegree_dehomog_of_isHomogeneous`: degree
  does not increase (in particular quadratics stay `≤ 2`);
* `snoc_of_dehomog_zero` / `dehomog_eval_of_mem_chart_last`: the `z`-chart
  piece of the locus is the affine zero locus of the dehomogenized system
  (the forward direction needs homogeneity for `z`-normalization via
  `eval_smul_of_isHomogeneous`).

Residual (discharged in `(b-aff)`/`(b-gen)` modulo R-dim — see
`## Obstruction (b)`): the bridge half ("`KrullDimLE 0` quotient ⟹ finite
zero locus") is `zeroLocus_finite_of_krullDimLE_zero` (no `IsAlgClosed`
needed for this direction); the chart-repeat half is the `dehomogAt*`
fragment plus `chart_cover_of_affine_cover_at` in `(b-gen)`. What remains is
only the chart-dimension drop `ChartDimZero`. -/

/-- The `z = 1` coordinate substitution: `X_last ↦ 1`, `X_(castSucc j) ↦ X_j`.

## References

* `Mathlib/Algebra/MvPolynomial/Basic.lean`, `MvPolynomial.C`, `MvPolynomial.X`.
* `Mathlib/Data/Fin/SuccPred.lean`, `Fin.castPred`
  (`def castPred (i : Fin (n + 1)) (h : i ≠ last n) : Fin n`),
  `Fin.castSucc_ne_last` (`theorem castSucc_ne_last (i) : i.castSucc ≠.last n`). -/
noncomputable def dehomogCoord (n : ℕ) (K : Type*) [Field K] :
    Fin (n + 2) → MvPolynomial (Fin (n + 1)) K :=
  fun j => if h : j = Fin.last (n + 1) then 1
    else MvPolynomial.X (Fin.castPred j h)

/-- The substitution sends `X_last` to `1`.

## References

* `Mathlib/Data/Fin/SuccPred.lean`, `Fin.last`. -/
@[simp]
theorem dehomogCoord_last (n : ℕ) (K : Type*) [Field K] :
    dehomogCoord n K (Fin.last (n + 1)) = 1 := by
  unfold dehomogCoord
  simp

/-- The substitution fixes the `x`-variables.

## References

* `Mathlib/Data/Fin/SuccPred.lean`, `Fin.castPred_castSucc`
  (`@[simp] theorem castPred_castSucc : castPred (castSucc i) h' = i`),
  `Fin.castSucc_ne_last`. -/
theorem dehomogCoord_castSucc (n : ℕ) (K : Type*) [Field K] (i : Fin (n + 1)) :
    dehomogCoord n K (Fin.castSucc i) = MvPolynomial.X i := by
  have h : Fin.castSucc i ≠ Fin.last (n + 1) := Fin.castSucc_ne_last i
  unfold dehomogCoord
  rw [dite_eq_right h, Fin.castPred_castSucc]

/-- Dehomogenization as a ring hom: evaluate at `z = 1`.

## References

* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.eval₂Hom`
  (`def eval₂Hom (f : R →+* S₁) (g : σ → S₁) : MvPolynomial σ R →+* S₁`). -/
noncomputable def dehomogHom (n : ℕ) (K : Type*) [Field K] :
    MvPolynomial (Fin (n + 2)) K →+* MvPolynomial (Fin (n + 1)) K :=
  MvPolynomial.eval₂Hom MvPolynomial.C (dehomogCoord n K)

/-- Dehomogenization of a polynomial at the `z`-chart: `φ ↦ φ(x, 1)`.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ProjectiveLocus`,
  `Appendix_FixedPoint.BezoutChain.dehomogHom`
  (proved above). -/
noncomputable def dehomog (n : ℕ) (K : Type*) [Field K]
    (φ : MvPolynomial (Fin (n + 2)) K) : MvPolynomial (Fin (n + 1)) K :=
  dehomogHom n K φ

/-- Dehomogenization fixes constants.

## References

* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.eval₂Hom_C`
  (`@[simp] theorem eval₂Hom_C (f) (g) (r) : eval₂Hom f g (C r) = f r`),
  `MvPolynomial.eval_C`. -/
@[simp]
theorem dehomog_C (n : ℕ) (K : Type*) [Field K] (a : K) :
    dehomog n K (MvPolynomial.C a) = MvPolynomial.C a := by
  unfold dehomog dehomogHom
  simp

/-- Dehomogenization sends each variable to its substitution value.

## References

* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.eval₂Hom_X'`
  (`@[simp] theorem eval₂Hom_X' (f) (g) (i) : eval₂Hom f g (X i) = g i`). -/
@[simp]
theorem dehomog_X (n : ℕ) (K : Type*) [Field K] (j : Fin (n + 2)) :
    dehomog n K (MvPolynomial.X j) = dehomogCoord n K j := by
  unfold dehomog dehomogHom
  simp

/-- Evaluation commutes with dehomogenization: evaluating the dehomogenized
polynomial at `x` is evaluating the original at `(x, 1)`. This is the
computation the G-cover chart leaf stands on.

## References

* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.eval₂Hom`
  (`def eval₂Hom`), `MvPolynomial.map_eval₂Hom`
  (`theorem map_eval₂Hom (f) (g) (φ) (p):
    φ (eval₂Hom f g p) = eval₂Hom (φ.comp f) (fun i => φ (g i)) p`),
  `MvPolynomial.eval` (`def eval (f): MvPolynomial σ R →+* R:=
    eval₂Hom (RingHom.id _) f`), `MvPolynomial.eval_C`, `MvPolynomial.eval_X`.
* `Mathlib/Data/Fin/Tuple/Basic.lean`, `Fin.snoc_castSucc`
  (`@[simp] theorem snoc_castSucc : snoc p x i.castSucc = p i`),
  `Fin.snoc_last` (`@[simp] theorem snoc_last : snoc p x (last n) = x`).
* `Mathlib/Data/Fin/SuccPred.lean`, `Fin.eq_castSucc_of_ne_last`
  (`theorem eq_castSucc_of_ne_last (h : x ≠ last _) : ∃ y, castSucc y = x`).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ProjectiveLocus`,
  `Appendix_FixedPoint.BezoutChain.dehomogCoord_last`,
  `Appendix_FixedPoint.BezoutChain.dehomogCoord_castSucc` (proved above). -/
theorem eval_dehomog (n : ℕ) (K : Type*) [Field K]
    (φ : MvPolynomial (Fin (n + 2)) K) (x : Fin (n + 1) → K) :
    MvPolynomial.eval x (dehomog n K φ)
      = MvPolynomial.eval (Fin.snoc (α := fun _ => K) x 1) φ := by
  have hC : (MvPolynomial.eval x).comp MvPolynomial.C = RingHom.id K := by
    ext a
    simp only [RingHom.comp_apply, MvPolynomial.eval_C, RingHom.id_apply]
  have hg : (fun j => MvPolynomial.eval x (dehomogCoord n K j))
      = Fin.snoc (α := fun _ => K) x 1 := by
    funext j
    by_cases hj : j = Fin.last (n + 1)
    · subst hj
      rw [dehomogCoord_last, map_one, Fin.snoc_last]
    · obtain ⟨k, rfl⟩ := Fin.eq_castSucc_of_ne_last hj
      rw [dehomogCoord_castSucc, MvPolynomial.eval_X, Fin.snoc_castSucc]
  calc MvPolynomial.eval x (dehomog n K φ)
      = MvPolynomial.eval₂Hom (RingHom.id K) (Fin.snoc (α := fun _ => K) x 1) φ := by
        unfold dehomog dehomogHom
        rw [MvPolynomial.map_eval₂Hom, hC, hg]
    _ = MvPolynomial.eval (Fin.snoc (α := fun _ => K) x 1) φ := rfl

/-- Each substitution value has total degree at most `1` (`X_j` or `1`).

## References

* `Mathlib/Algebra/MvPolynomial/Degrees.lean`, `MvPolynomial.totalDegree_X`
  (`@[simp] theorem totalDegree_X (s) : (X s).totalDegree = 1`),
  `MvPolynomial.totalDegree_one`
  (`@[simp] theorem totalDegree_one : (1).totalDegree = 0`).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ProjectiveLocus`,
  `Appendix_FixedPoint.BezoutChain.dehomogCoord_last` (proved above). -/
theorem totalDegree_dehomogCoord_le (n : ℕ) (K : Type*) [Field K]
    (j : Fin (n + 2)) : (dehomogCoord n K j).totalDegree ≤ 1 := by
  by_cases hj : j = Fin.last (n + 1)
  · subst hj
    rw [dehomogCoord_last]
    simp
  · have hX : dehomogCoord n K j
        = MvPolynomial.X (Fin.castPred j hj) := by
      unfold dehomogCoord
      rw [dite_eq_right hj]
    rw [hX, MvPolynomial.totalDegree_X]

/-- Degree does not increase under dehomogenization. Proof: expand `φ` as a
sum of monomials (`as_sum`), push `eval₂Hom` through (`eval₂Hom_monomial`),
and bound each image monomial by its source weight via `totalDegree_pow` /
`totalDegree_finsetProd` / `totalDegree_finsetSum_le` (this route avoids the
cancellation trap of a naive `totalDegree_add` induction).

## References

* `Mathlib/Algebra/MvPolynomial/Basic.lean`, `MvPolynomial.as_sum`
  (`theorem as_sum (p) : p = ∑ v ∈ p.support, monomial v (p.coeff v)`).
* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.eval₂Hom_monomial`
  (`theorem eval₂Hom_monomial (f) (g) (d) (r):
    eval₂Hom f g (monomial d r) = f r * d.prod fun i k => g i ^ k`).
* `Mathlib/Algebra/MvPolynomial/Degrees.lean`,
  `MvPolynomial.totalDegree_finsetSum_le`
  (`lemma totalDegree_finsetSum_le (hf: ∀ i ∈ s, (f i).totalDegree ≤ d):
    (s.sum f).totalDegree ≤ d`),
  `MvPolynomial.totalDegree_mul`, `MvPolynomial.totalDegree_pow`,
  `MvPolynomial.totalDegree_C`, `MvPolynomial.totalDegree_finsetProd`
  (`theorem totalDegree_finsetProd (s) (f):
    (s.prod f).totalDegree ≤ ∑ i ∈ s, (f i).totalDegree`),
  `MvPolynomial.le_totalDegree`
  (`theorem le_totalDegree (h: s ∈ p.support):
    (s.sum fun _ e => e) ≤ totalDegree p`).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ProjectiveLocus`,
  `Appendix_FixedPoint.BezoutChain.dehomogHom`, `Appendix_FixedPoint.BezoutChain.dehomog`,
  `Appendix_FixedPoint.BezoutChain.totalDegree_dehomogCoord_le` (proved above). -/
theorem totalDegree_dehomog_le (n : ℕ) (K : Type*) [Field K]
    (φ : MvPolynomial (Fin (n + 2)) K) :
    (dehomog n K φ).totalDegree ≤ φ.totalDegree := by
  have hprod : ∀ s : Fin (n + 2) →₀ ℕ,
      (s.prod fun i k => dehomogCoord n K i ^ k).totalDegree
        ≤ s.sum fun _ e => e := by
    intro s
    calc (s.prod fun i k => dehomogCoord n K i ^ k).totalDegree
        = (s.support.prod fun i => dehomogCoord n K i ^ s i).totalDegree := rfl
      _ ≤ Finset.sum s.support
            (fun i => (dehomogCoord n K i ^ s i).totalDegree) :=
          MvPolynomial.totalDegree_finsetProd _ _
      _ ≤ Finset.sum s.support (fun i => s i) := by
          apply Finset.sum_le_sum
          intro i _
          calc (dehomogCoord n K i ^ s i).totalDegree
              ≤ s i * (dehomogCoord n K i).totalDegree :=
                MvPolynomial.totalDegree_pow _ _
            _ ≤ s i * 1 :=
                Nat.mul_le_mul le_rfl (totalDegree_dehomogCoord_le n K i)
            _ = s i := Nat.mul_one _
      _ = s.sum fun _ e => e := rfl
  have hexpand : MvPolynomial.eval₂Hom MvPolynomial.C (dehomogCoord n K) φ
      = Finset.sum φ.support (fun s => MvPolynomial.eval₂Hom MvPolynomial.C
          (dehomogCoord n K) (MvPolynomial.monomial s (φ.coeff s))) := by
    conv_lhs => rw [φ.as_sum]
    rw [map_sum]
  have hde : dehomog n K φ
      = Finset.sum φ.support (fun s => MvPolynomial.eval₂Hom MvPolynomial.C
          (dehomogCoord n K) (MvPolynomial.monomial s (φ.coeff s))) := hexpand
  rw [hde]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro s hs
  rw [MvPolynomial.eval₂Hom_monomial]
  calc (MvPolynomial.C (φ.coeff s)
          * s.prod fun i k => dehomogCoord n K i ^ k).totalDegree
      ≤ (MvPolynomial.C (φ.coeff s)).totalDegree
          + (s.prod fun i k => dehomogCoord n K i ^ k).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
    _ = (s.prod fun i k => dehomogCoord n K i ^ k).totalDegree := by
        rw [MvPolynomial.totalDegree_C, Nat.zero_add]
    _ ≤ s.sum fun _ e => e := hprod s
    _ ≤ φ.totalDegree := MvPolynomial.le_totalDegree hs

/-- Degree control at homogeneous shape: dehomogenizing a degree-`d`
homogeneous polynomial yields total degree at most `d` (in particular
quadratics stay `≤ 2`, the exact input the G-cover chart leaf needs at
`mkSystem` shape).

## References

* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.IsHomogeneous`
  (`def IsHomogeneous (φ) (n) := IsWeightedHomogeneous 1 φ n`).
* `Mathlib/RingTheory/MvPolynomial/WeightedHomogeneous.lean`,
  `MvPolynomial.IsWeightedHomogeneous`
  (`def IsWeightedHomogeneous (w) (φ) (m):=
    ∀ ⦃d⦄, φ.coeff d ≠ 0 → weight w d = m`).
* `Mathlib/Data/Finsupp/Weight.lean`, `Finsupp.weight_apply`
  (`theorem weight_apply (f) : weight w f = Finsupp.sum f (fun i c => c • w i)`).
* `Mathlib/Data/Finsupp/Defs.lean`, `Finsupp.mem_support_iff`
  (`theorem mem_support_iff : a ∈ f.support ↔ f a ≠ 0`).
* `Mathlib/Algebra/MvPolynomial/Degrees.lean`, `MvPolynomial.totalDegree`
  (`def totalDegree (p) : ℕ := p.support.sup fun s => s.sum fun _ e => e`).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ProjectiveLocus`,
  `Appendix_FixedPoint.BezoutChain.totalDegree_dehomog_le` (proved above). -/
theorem totalDegree_dehomog_of_isHomogeneous (n : ℕ) (K : Type*) [Field K]
    {φ : MvPolynomial (Fin (n + 2)) K} {d : ℕ}
    (hφ : φ.IsHomogeneous d) :
    (dehomog n K φ).totalDegree ≤ d := by
  refine (totalDegree_dehomog_le n K φ).trans ?_
  change φ.support.sup (fun s => s.sum fun _ e => e) ≤ d
  apply Finset.sup_le
  intro s hs
  have hsup : φ.coeff s ≠ 0 := Finsupp.mem_support_iff.mp hs
  have hwt : Finsupp.weight (1 : Fin (n + 2) → ℕ) s = d := hφ hsup
  rw [Finsupp.weight_apply] at hwt
  have hsum : s.sum (fun _ e => e) = d := by simpa using hwt
  exact le_of_eq hsum

/-- Affine zeros lift to normalized common zeros: a common zero `x` of the
dehomogenized system gives `(x, 1)`, nonzero with `z = 1`, still a common
zero of `G`. No homogeneity needed (one representative only).

## References

* `Mathlib/Data/Fin/Tuple/Basic.lean`, `Fin.snoc_last`
  (`@[simp] theorem snoc_last : snoc p x (last n) = x`).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ProjectiveLocus`,
  `Appendix_FixedPoint.BezoutChain.eval_dehomog`
  (proved above). -/
theorem snoc_of_dehomog_zero (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (x : Fin (n + 1) → K)
    (hx : ∀ i, MvPolynomial.eval x (dehomog n K (G i)) = 0) :
    (Fin.snoc (α := fun _ => K) x 1 ≠ 0) ∧
      ∀ i, MvPolynomial.eval (Fin.snoc (α := fun _ => K) x 1) (G i) = 0 := by
  refine ⟨?_, fun i => ?_⟩
  · intro h
    have h1 := congrFun h (Fin.last (n + 1))
    simp [Fin.snoc_last] at h1
  · have h := hx i
    rw [eval_dehomog] at h
    exact h

/-- Chart points descend to affine zeros: a common zero `v` with `z ≠ 0`
`z`-normalizes to an affine common zero of the dehomogenized system. Uses
homogeneity (`eval_smul_of_isHomogeneous` at `a = v_last⁻¹`) to clear the
`z`-coordinate, then `eval_dehomog`.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ProjectiveLocus`,
  `Appendix_FixedPoint.BezoutChain.eval_smul_of_isHomogeneous`,
  `Appendix_FixedPoint.BezoutChain.eval_dehomog` (proved above).
* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.eval`
  (ring hom), `MvPolynomial.eval_X`.
* `Mathlib/Data/Fin/Tuple/Basic.lean`, `Fin.snoc_castSucc`, `Fin.snoc_last`.
* `Mathlib/Data/Fin/SuccPred.lean`, `Fin.eq_castSucc_of_ne_last`. -/
theorem dehomog_eval_of_mem_chart_last (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (d : Fin (n + 1) → ℕ)
    (hG : ∀ i, (G i).IsHomogeneous (d i))
    (v : Fin (n + 2) → K)
    (hlast : v (Fin.last (n + 1)) ≠ 0)
    (hGv : ∀ i, MvPolynomial.eval v (G i) = 0) :
    ∀ i, MvPolynomial.eval
      (fun j => (v (Fin.last (n + 1)))⁻¹ * v (Fin.castSucc j))
      (dehomog n K (G i)) = 0 := by
  have hws : Fin.snoc (α := fun _ => K)
        (fun j => (v (Fin.last (n + 1)))⁻¹ * v (Fin.castSucc j)) 1
      = (v (Fin.last (n + 1)))⁻¹ • v := by
    funext j
    by_cases hj : j = Fin.last (n + 1)
    · subst hj
      rw [Fin.snoc_last, Pi.smul_apply, smul_eq_mul, inv_mul_cancel₀ hlast]
    · obtain ⟨k, rfl⟩ := Fin.eq_castSucc_of_ne_last hj
      rw [Fin.snoc_castSucc, Pi.smul_apply, smul_eq_mul]
  intro i
  rw [eval_dehomog, hws, eval_smul_of_isHomogeneous (hG i), hGv i, mul_zero]

/-! ## (b″) `z`-chart transfer and the maximal conditional `hcover`

`hcover_of_chart_covers` reduces global `hcover` to per-chart covers. This
section discharges the `z`-chart (`j = Fin.last (n + 1)`) piece from an affine
cover of the dehomogenized system, then assembles the strongest provable
global statement: `hcover` from the `z`-chart affine cover plus covers of the
remaining charts, with the `mkSystem` bundle additionally discharging the
`locus_nonempty` `hA` slot via `section_maxSpec_nonempty_mkSystem`. The two
residuals (affine finiteness from `IsZeroDimensional`; the mechanical repeat
at the remaining charts) are listed exactly in `## Obstruction (b)` below. -/

/-- The `z = 1` section point is always nonzero (its last coordinate is `1`).

## References

* `Mathlib/Data/Fin/Tuple/Basic.lean`, `Fin.snoc_last`
  (`@[simp] theorem snoc_last : snoc p x (last n) = x`). -/
theorem snoc_one_ne_zero (n : ℕ) (K : Type*) [Field K]
    (x : Fin (n + 1) → K) :
    Fin.snoc (α := fun _ => K) x (1 : K) ≠ 0 := by
  intro h
  have h1 := congrFun h (Fin.last (n + 1))
  simp [Fin.snoc_last] at h1

/-- `z`-chart transfer (closed): the `D₊(X_last)` piece of the locus is covered
by the `mk`-image of any finset covering the affine zero locus of the
dehomogenized system. Backward (chart point ⟹ affine zero) is
`dehomog_eval_of_mem_chart_last` on the `z`-normalized representative
`x = v_last⁻¹ • vₓ`; forward (that representative re-marks the same projective
point) is `z`-normalization scale-invariance via
`Projectivization.mk_eq_mk_iff'`.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ProjectiveLocus`,
  `Appendix_FixedPoint.BezoutChain.dehomog_eval_of_mem_chart_last`,
  `Appendix_FixedPoint.BezoutChain.snoc_one_ne_zero`
  (proved above).
* `Mathlib/LinearAlgebra/Projectivization/Basic.lean`,
  `Projectivization.mk`, `Projectivization.mk_eq_mk_iff'`
  (`theorem mk_eq_mk_iff' (v w) (hv) (hw):
    mk K v hv = mk K w hw ↔ ∃ a: K, a • w = v`).
* `Mathlib/Data/Finset/Image.lean`, `Finset.mem_image`
  (`theorem mem_image : b ∈ s.image f ↔ ∃ a ∈ s, f a = b`).
* `Mathlib/Data/Fin/Tuple/Basic.lean`, `Fin.snoc_castSucc`, `Fin.snoc_last`.
* `Mathlib/Data/Fin/SuccPred.lean`, `Fin.eq_castSucc_of_ne_last`. -/
theorem chart_last_cover_of_affine_cover (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (d : Fin (n + 1) → ℕ)
    (hG : ∀ i, (G i).IsHomogeneous (d i))
    (S : Finset (Fin (n + 1) → K))
    (haff : ∀ x, (∀ i, MvPolynomial.eval x (dehomog n K (G i)) = 0) → x ∈ S) :
    ∃ t : Finset (Projectivization K (Fin (n + 2) → K)),
      chartSet n K (Fin.last (n + 1)) ∩ vanishingLocus n K G ⊆ ↑t := by
  classical
  refine ⟨S.image (fun x => Projectivization.mk K
    (Fin.snoc (α := fun _ => K) x 1) (snoc_one_ne_zero n K x)), fun p hp => ?_⟩
  obtain ⟨⟨v, hv, hmk, hlast⟩, hloc⟩ := hp
  have hGv : ∀ i, MvPolynomial.eval v (G i) = 0 := fun i => hloc v hv hmk i
  have hxmem : ∀ i, MvPolynomial.eval
      (fun j => (v (Fin.last (n + 1)))⁻¹ * v (Fin.castSucc j))
      (dehomog n K (G i)) = 0 :=
    dehomog_eval_of_mem_chart_last n K G d hG v hlast hGv
  have hws : Fin.snoc (α := fun _ => K)
        (fun j => (v (Fin.last (n + 1)))⁻¹ * v (Fin.castSucc j)) 1
      = (v (Fin.last (n + 1)))⁻¹ • v := by
    funext j
    by_cases hj : j = Fin.last (n + 1)
    · subst hj
      rw [Fin.snoc_last, Pi.smul_apply, smul_eq_mul, inv_mul_cancel₀ hlast]
    · obtain ⟨k, rfl⟩ := Fin.eq_castSucc_of_ne_last hj
      rw [Fin.snoc_castSucc, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mem_coe, Finset.mem_image]
  refine ⟨_, haff _ hxmem, ?_⟩
  have hscale : Projectivization.mk K
        (Fin.snoc (α := fun _ => K)
          (fun j => (v (Fin.last (n + 1)))⁻¹ * v (Fin.castSucc j)) 1)
        (snoc_one_ne_zero n K _) =
        Projectivization.mk K v hv :=
    (Projectivization.mk_eq_mk_iff' K _ v _ hv).mpr
      ⟨(v (Fin.last (n + 1)))⁻¹, hws.symm⟩
  exact hscale.trans hmk

/-- Maximal conditional `hcover` (closed modulo the exact residual list in
`## Obstruction (b)`): global `hcover` from an affine cover of the
dehomogenized system at the `z`-chart plus covers of the remaining charts.
Wires `hcover_of_chart_covers` (which itself uses `rep_mem_chart`) with the
`z`-chart transfer above; homogeneity `hG` is needed only at the `z`-chart.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ProjectiveLocus`,
  `Appendix_FixedPoint.BezoutChain.hcover_of_chart_covers`,
  `Appendix_FixedPoint.BezoutChain.chart_last_cover_of_affine_cover`
  (proved above), `Appendix_FixedPoint.BezoutChain.rep_mem_chart` (used inside
  `hcover_of_chart_covers`).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Counting`,
  `Appendix_FixedPoint.BezoutChain.finite_locus` (whose `hcover`
  slot the conclusion discharges). -/
theorem hcover_of_affine_last_and_other_charts (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (d : Fin (n + 1) → ℕ)
    (hG : ∀ i, (G i).IsHomogeneous (d i))
    (S : Finset (Fin (n + 1) → K))
    (haff : ∀ x, (∀ i, MvPolynomial.eval x (dehomog n K (G i)) = 0) → x ∈ S)
    (hother : ∀ i : Fin (n + 2), i ≠ Fin.last (n + 1) →
      ∃ t : Finset (Projectivization K (Fin (n + 2) → K)),
        chartSet n K i ∩ vanishingLocus n K G ⊆ ↑t) :
    ∃ t : Finset (Projectivization K (Fin (n + 2) → K)),
      vanishingLocus n K G ⊆ ↑t := by
  apply hcover_of_chart_covers
  intro i
  by_cases hi : i = Fin.last (n + 1)
  · subst hi
    exact chart_last_cover_of_affine_cover n K G d hG S haff
  · exact hother i hi

/-- `mkSystem` bundle (closed modulo the exact residual list in
`## Obstruction (b)`): at the canonical system `G := mkSystem n K F` with
homogeneous quadratic inputs, the caller supplies only `hF`, the `z`-chart
affine cover, and the remaining-chart covers, and receives `finite_locus`'s
`hcover` slot together with `locus_nonempty`'s `hA` slot (via
`section_maxSpec_nonempty_mkSystem`, which needs no further input).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Statement.Statement`,
  `Appendix_FixedPoint.BezoutChain.mkSystem_homogeneous`
  (canonical supplier shape `∀ i, (G i).IsHomogeneous 2`).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ProjectiveLocus`,
  `Appendix_FixedPoint.BezoutChain.hcover_of_affine_last_and_other_charts`,
  `Appendix_FixedPoint.BezoutChain.section_maxSpec_nonempty_mkSystem` (proved above).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Counting`,
  `Appendix_FixedPoint.BezoutChain.finite_locus`,
  `Appendix_FixedPoint.BezoutChain.locus_nonempty` (whose `hcover` / `hA` slots this discharges). -/
theorem hcover_mkSystem_of_affine_and_charts (n : ℕ) (K : Type*) [Field K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2)
    (ℓ : Fin (n + 2) → K)
    (S : Finset (Fin (n + 1) → K))
    (haff : ∀ x, (∀ i, MvPolynomial.eval x
      (dehomog n K ((mkSystem n K F) i)) = 0) → x ∈ S)
    (hother : ∀ i : Fin (n + 2), i ≠ Fin.last (n + 1) →
      ∃ t : Finset (Projectivization K (Fin (n + 2) → K)),
        chartSet n K i ∩ vanishingLocus n K (mkSystem n K F) ⊆ ↑t) :
    (∃ t : Finset (Projectivization K (Fin (n + 2) → K)),
      vanishingLocus n K (mkSystem n K F) ⊆ ↑t)
      ∧ Nonempty (MaximalSpectrum (sectionQuotient n K (mkSystem n K F) ℓ)) := by
  refine ⟨?_, section_maxSpec_nonempty_mkSystem n K F ℓ hF⟩
  exact hcover_of_affine_last_and_other_charts n K _ (fun _ => 2)
    (mkSystem_homogeneous n K F hF) S haff hother

/-! ## (b-aff) Affine finiteness from chart-dimension zero (R-aff closed)

The affine residual proves here as a proved bridge: a zero-dimensional affine
quotient has finite zero locus, hence every affine system with
`KrullDimLE 0` quotient admits a finset cover. The route is Noetherian +
dimension-zero ⟹ Artinian, whose finitely many maximal ideals bound the
`K`-points via the Nullstellensatz Galois connection (each point maps to the
maximal image of its vanishing ideal; distinct points give distinct ideals).
Notably no `IsAlgClosed` is needed for this direction — only maximality of
point kernels, which holds over any field.

What remains open is the chart-dimension drop (`IsZeroDimensional` of the cone
⟹ `KrullDimLE 0` of each chart quotient), recorded as the single explicit
hypothesis `ChartDimZero` in `(b-asm)`; see `## Obstruction (b)`. -/

/-- Points give distinct vanishing ideals: the singleton-ideal map is injective.
Evaluating `Xᵢ − C (xᵢ)` (which vanishes at `x`) at `y` forces `yᵢ = xᵢ`.

## References

* `Mathlib/RingTheory/Nullstellensatz.lean`,
  `MvPolynomial.mem_vanishingIdeal_singleton_iff`
  (`theorem mem_vanishingIdeal_singleton_iff (x) (p):
    p ∈ vanishingIdeal k {x} ↔ aeval x p = 0`),
  `MvPolynomial.vanishingIdeal`.
* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.aeval_X`,
  `MvPolynomial.aeval_C`. -/
theorem vanishingIdeal_singleton_injective
    {m : ℕ} {K : Type*} [Field K] :
    Function.Injective (fun x : Fin m → K =>
      MvPolynomial.vanishingIdeal K ({x} : Set (Fin m → K))) := by
  intro x y h
  have h' : MvPolynomial.vanishingIdeal K ({x} : Set (Fin m → K))
      = MvPolynomial.vanishingIdeal K ({y} : Set (Fin m → K)) := h
  funext i
  have hmem : MvPolynomial.X i - MvPolynomial.C (x i)
      ∈ MvPolynomial.vanishingIdeal K ({x} : Set (Fin m → K)) := by
    rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
    simp
  rw [h'] at hmem
  rw [MvPolynomial.mem_vanishingIdeal_singleton_iff] at hmem
  simp only [MvPolynomial.aeval_eq_eval, map_sub, MvPolynomial.eval_X,
    MvPolynomial.eval_C] at hmem
  exact (sub_eq_zero.mp hmem).symm

/-- The image of a point's vanishing ideal in an affine quotient (by an ideal
it contains) is maximal: a surjective image of a maximal ideal is maximal or
top, and top is ruled out by pulling back (`comap_map` collapses to the
original ideal since the kernel is contained in it).

## References

* `Mathlib/RingTheory/Ideal/Maps.lean`,
  `Ideal.map_eq_top_or_isMaximal_of_surjective`
  (`theorem map_eq_top_or_isMaximal_of_surjective (f) (hf) (H):
    map f I = ⊤ ∨ IsMaximal (map f I)`),
  `Ideal.comap_map_of_surjective`
  (`theorem comap_map_of_surjective (f) (hf) (I):
    comap f (map f I) = I ⊔ comap f ⊥`),
  `RingHom.ker_eq_comap_bot`
  (`theorem ker_eq_comap_bot (f) : ker f = Ideal.comap f ⊥`).
* `Mathlib/RingTheory/Ideal/Quotient/Defs.lean`, `Ideal.Quotient.mk`,
  `Ideal.Quotient.mk_surjective`.
* `Mathlib/RingTheory/Ideal/Quotient/Operations.lean`, `Ideal.mk_ker`
  (`theorem mk_ker : ker (Quotient.mk I) = I`).
* `Mathlib/RingTheory/Nullstellensatz.lean`,
  `MvPolynomial.vanishingIdeal` (maximality of point ideals is the
  in-tree instance from `aeval` surjectivity). -/
theorem map_vanishingIdeal_isMaximal
    {m : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin m) K))
    (x : Fin m → K)
    (hle : I ≤ MvPolynomial.vanishingIdeal K ({x} : Set (Fin m → K))) :
    (Ideal.map (Ideal.Quotient.mk I)
      (MvPolynomial.vanishingIdeal K ({x} : Set (Fin m → K)))).IsMaximal := by
  have hmax : (MvPolynomial.vanishingIdeal K ({x} : Set (Fin m → K))).IsMaximal :=
    inferInstance
  rcases Ideal.map_eq_top_or_isMaximal_of_surjective
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective hmax with htop | hmax'
  · exfalso
    have hcomap : Ideal.comap (Ideal.Quotient.mk I)
        (Ideal.map (Ideal.Quotient.mk I)
          (MvPolynomial.vanishingIdeal K ({x} : Set (Fin m → K))))
        = MvPolynomial.vanishingIdeal K ({x} : Set (Fin m → K)) := by
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
      have hker : Ideal.comap (Ideal.Quotient.mk I) ⊥ = I := by
        rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
      rw [hker, sup_eq_left.mpr hle]
    rw [htop] at hcomap
    simp only [Ideal.comap_top] at hcomap
    have hne := hmax.ne_top
    rw [← hcomap] at hne
    exact hne rfl
  · exact hmax'

/-- Pullback undoes the pushforward on point ideals containing the kernel:
for a point `x` of the zero locus, pulling back the pushed-forward
`vanishingIdeal {x}` recovers it, because the quotient kernel `I` is absorbed
(`⊔`-neutral) inside it. This is the injectivity half of the point-to-maximal
ideal map in `zeroLocus_finite_of_krullDimLE_zero`.

## References

* `Mathlib/RingTheory/Ideal/Maps.lean`, `Ideal.comap_map_of_surjective`,
  `RingHom.ker_eq_comap_bot` (cited above).
* `Mathlib/RingTheory/Ideal/Quotient/Operations.lean`, `Ideal.mk_ker`
  (cited above). -/
theorem comap_map_vanishingIdeal
    {m : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin m) K))
    (x : Fin m → K)
    (hle : I ≤ MvPolynomial.vanishingIdeal K ({x} : Set (Fin m → K))) :
    Ideal.comap (Ideal.Quotient.mk I)
      (Ideal.map (Ideal.Quotient.mk I)
        (MvPolynomial.vanishingIdeal K ({x} : Set (Fin m → K))))
      = MvPolynomial.vanishingIdeal K ({x} : Set (Fin m → K)) := by
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
  have hker : Ideal.comap (Ideal.Quotient.mk I) ⊥ = I := by
    rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  rw [hker, sup_eq_left.mpr hle]

/-- Affine bridge (closed): the zero locus of an ideal with zero-dimensional
quotient is finite. The quotient is Artinian (Noetherian + `KrullDimLE 0`),
hence has finitely many maximal ideals; points inject into them by pushing
their vanishing ideals forward (`map_vanishingIdeal_isMaximal`) and pulling
back (`comap_map_vanishingIdeal`, `vanishingIdeal_singleton_injective`).

## References

* `Mathlib/RingTheory/HopkinsLevitzki.lean`,
  `IsNoetherianRing.isArtinianRing_of_krullDimLE_zero`
  (`theorem isArtinianRing_of_krullDimLE_zero [IsNoetherianRing R]
    [Ring.KrullDimLE 0 R]: IsArtinianRing R`).
* `Mathlib/RingTheory/Artinian/Module.lean`,
  `IsArtinianRing.setOfPred_isMaximal_finite`
  (`lemma setOfPred_isMaximal_finite (R) : {I : Ideal R | I.IsMaximal}.Finite`).
* `Mathlib/Data/Set/Finite/Basic.lean`, `Set.Finite.of_injOn`
  (`theorem Finite.of_injOn (hm: MapsTo f s t) (hi: InjOn f s)
    (ht: t.Finite): s.Finite`).
* `Mathlib/Data/Set/Function.lean`, `Function.Injective.injOn`.
* `Mathlib/RingTheory/Nullstellensatz.lean`,
  `MvPolynomial.zeroLocus`, `MvPolynomial.vanishingIdeal`,
  `MvPolynomial.le_zeroLocus_iff_le_vanishingIdeal`.
* `Mathlib/Data/Set/Insert.lean`, `Set.singleton_subset_iff`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ProjectiveLocus`,
  `Appendix_FixedPoint.BezoutChain.vanishingIdeal_singleton_injective`,
  `Appendix_FixedPoint.BezoutChain.map_vanishingIdeal_isMaximal`,
  `Appendix_FixedPoint.BezoutChain.comap_map_vanishingIdeal` (proved above). -/
theorem zeroLocus_finite_of_krullDimLE_zero
    {m : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin m) K))
    (hdim : Ring.KrullDimLE 0 (MvPolynomial (Fin m) K ⧸ I)) :
    (MvPolynomial.zeroLocus K I).Finite := by
  have hArt : IsArtinianRing (MvPolynomial (Fin m) K ⧸ I) :=
    @IsNoetherianRing.isArtinianRing_of_krullDimLE_zero _ _ _ hdim
  have hfinMax :=
    @IsArtinianRing.setOfPred_isMaximal_finite _ _ hArt
  refine Set.Finite.of_injOn (f := fun x : Fin m → K =>
      Ideal.map (Ideal.Quotient.mk I)
        (MvPolynomial.vanishingIdeal K ({x} : Set (Fin m → K))))
    (t := {J : Ideal (MvPolynomial (Fin m) K ⧸ I) | J.IsMaximal}) ?_ ?_ hfinMax
  · intro x hx
    change (Ideal.map (Ideal.Quotient.mk I)
      (MvPolynomial.vanishingIdeal K ({x} : Set (Fin m → K)))).IsMaximal
    have hle : I ≤ MvPolynomial.vanishingIdeal K ({x} : Set (Fin m → K)) :=
      (MvPolynomial.le_zeroLocus_iff_le_vanishingIdeal).mp
        (Set.singleton_subset_iff.mpr hx)
    exact map_vanishingIdeal_isMaximal I x hle
  · intro x hx y hy hxy
    have hxle : I ≤ MvPolynomial.vanishingIdeal K ({x} : Set (Fin m → K)) :=
      (MvPolynomial.le_zeroLocus_iff_le_vanishingIdeal).mp
        (Set.singleton_subset_iff.mpr hx)
    have hyle : I ≤ MvPolynomial.vanishingIdeal K ({y} : Set (Fin m → K)) :=
      (MvPolynomial.le_zeroLocus_iff_le_vanishingIdeal).mp
        (Set.singleton_subset_iff.mpr hy)
    have hxy' : Ideal.map (Ideal.Quotient.mk I)
          (MvPolynomial.vanishingIdeal K ({x} : Set (Fin m → K)))
        = Ideal.map (Ideal.Quotient.mk I)
          (MvPolynomial.vanishingIdeal K ({y} : Set (Fin m → K))) := hxy
    have hJ : MvPolynomial.vanishingIdeal K ({x} : Set (Fin m → K))
        = MvPolynomial.vanishingIdeal K ({y} : Set (Fin m → K)) := by
      have h1 := comap_map_vanishingIdeal I x hxle
      have h2 := comap_map_vanishingIdeal I y hyle
      have hc := congrArg (Ideal.comap (Ideal.Quotient.mk I)) hxy'
      rw [h1, h2] at hc
      exact hc
    exact vanishingIdeal_singleton_injective hJ

/-- Affine cover from chart-dimension zero (general family shape): the
`eval`-zero set of `F` is the `aeval`-`zeroLocus` of its span
(`MvPolynomial.aeval_eq_eval` is `rfl`), hence finite by the bridge above,
hence covered by a finset.

## References

* `Mathlib/RingTheory/Nullstellensatz.lean`, `MvPolynomial.zeroLocus_span`
  (`theorem zeroLocus_span (S):
    zeroLocus K (Ideal.span S) = {x | ∀ p ∈ S, aeval x p = 0}`).
* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.aeval_eq_eval`
  (`lemma aeval_eq_eval : (aeval f : MvPolynomial σ S₁ → S₁) = eval f`).
* `Mathlib/Data/Set/Finite/Basic.lean`, `Set.Finite.exists_finset_coe`
  (`theorem Finite.exists_finset_coe (h: s.Finite):
    ∃ s': Finset α, ↑s' = s`).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ProjectiveLocus`,
  `Appendix_FixedPoint.BezoutChain.zeroLocus_finite_of_krullDimLE_zero` (proved above). -/
theorem affine_cover_of_krullDimLE_zero_general
    {m : ℕ} {K : Type*} [Field K]
    (F : Fin m → MvPolynomial (Fin m) K)
    (hdim : Ring.KrullDimLE 0
      (MvPolynomial (Fin m) K ⧸ Ideal.span (Set.range F))) :
    ∃ S : Finset (Fin m → K),
      ∀ x, (∀ i, MvPolynomial.eval x (F i) = 0) → x ∈ S := by
  have hfin := zeroLocus_finite_of_krullDimLE_zero _ hdim
  obtain ⟨S, hS⟩ := hfin.exists_finset_coe
  refine ⟨S, fun x hx => ?_⟩
  have hxmem : x ∈ MvPolynomial.zeroLocus K (Ideal.span (Set.range F)) := by
    rw [MvPolynomial.zeroLocus_span]
    intro p hp
    obtain ⟨i, rfl⟩ := hp
    exact hx i
  rw [← hS] at hxmem
  exact Finset.mem_coe.mp hxmem

/-- R-aff at the `z`-chart: the dehomogenized system's affine zero locus is
covered by a finset as soon as its affine quotient is zero-dimensional. This
discharges the `haff` input of `hcover_of_affine_last_and_other_charts` and
`hcover_mkSystem_of_affine_and_charts` modulo the chart-dimension hypothesis.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ProjectiveLocus`,
  `Appendix_FixedPoint.BezoutChain.affine_cover_of_krullDimLE_zero_general` (proved above),
  `Appendix_FixedPoint.BezoutChain.dehomog` (the `z`-chart dehomogenization). -/
theorem affine_cover_of_krullDimLE_zero (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hdim : Ring.KrullDimLE 0 (MvPolynomial (Fin (n + 1)) K ⧸
      Ideal.span (Set.range (fun i => dehomog n K (G i))))) :
    ∃ S : Finset (Fin (n + 1) → K),
      ∀ x, (∀ i, MvPolynomial.eval x (dehomog n K (G i)) = 0) → x ∈ S :=
  affine_cover_of_krullDimLE_zero_general _ hdim

/-! ## (b-gen) Dehomogenization and transfer at an arbitrary chart (R-charts closed)

This section repeats the `(b′)` dehomogenization fragment and the `(b″)`
transfer at an arbitrary chart `c : Fin (n + 2)`, discharging `hother`. The
only change versus the `z`-chart versions is the deletion coordinate:
`Fin.succAbove c` in place of `Fin.castSucc` (with `Fin.insertNth c 1` in
place of `Fin.snoc · 1`), and the deletion index `chartDel` (chosen via
`Fin.exists_succAbove_eq`) in place of `Fin.castPred`. No Mathlib block:
everything used is already in-tree and imported. -/

/-- Deletion index at `c`: for `j ≠ c`, the `Fin (n + 1)` index sent to `j`
by `c.succAbove`.

## References

* `Mathlib/Data/Fin/SuccPred.lean`, `Fin.exists_succAbove_eq`
  (`lemma exists_succAbove_eq {x y: Fin (n + 1)} (h: x ≠ y):
    ∃ z, y.succAbove z = x`). -/
noncomputable def chartDel (n : ℕ) (c j : Fin (n + 2)) (h : j ≠ c) : Fin (n + 1) :=
  Classical.choose (Fin.exists_succAbove_eq h)

/-- The deletion index hits `j`.

## References

* `Mathlib/Data/Fin/SuccPred.lean`, `Fin.exists_succAbove_eq` (cited above). -/
theorem chartDel_spec (n : ℕ) (c j : Fin (n + 2)) (h : j ≠ c) :
    c.succAbove (chartDel n c j h) = j :=
  Classical.choose_spec (Fin.exists_succAbove_eq h)

/-- The chart-`c` coordinate substitution: `X_c ↦ 1`, `X_j ↦ X_(del j)` for
`j ≠ c`. Generalizes `dehomogCoord` (which is the `c = Fin.last _` case with
`Fin.castPred` as the deletion).

## References

* `Mathlib/Algebra/MvPolynomial/Basic.lean`, `MvPolynomial.C`, `MvPolynomial.X`.
* `Mathlib/Data/Fin/SuccPred.lean`, `Fin.succAbove_ne`
  (`lemma succAbove_ne (p : Fin (n + 1)) (i : Fin n) : p.succAbove i ≠ p`).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ProjectiveLocus`,
  `Appendix_FixedPoint.BezoutChain.chartDel`
  (proved above). -/
noncomputable def dehomogAtCoord (n : ℕ) (K : Type*) [Field K] (c : Fin (n + 2)) :
    Fin (n + 2) → MvPolynomial (Fin (n + 1)) K :=
  fun j => if h : j = c then 1 else MvPolynomial.X (chartDel n c j h)

/-- The substitution sends `X_c` to `1`: the definitional unfolding at the
deleted coordinate (the chart-`c` analogue of `dehomogCoord_last`).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ProjectiveLocus`,
  `Appendix_FixedPoint.BezoutChain.dehomogCoord_last`
  (the `z`-chart instance of the same unfolding). -/
@[simp]
theorem dehomogAtCoord_self (n : ℕ) (K : Type*) [Field K] (c : Fin (n + 2)) :
    dehomogAtCoord n K c c = 1 := by
  unfold dehomogAtCoord
  simp

/-- The substitution fixes the remaining variables.

## References

* `Mathlib/Data/Fin/SuccPred.lean`, `Fin.succAbove_ne` (cited above),
  `Fin.succAbove_right_injective`
  (`lemma succAbove_right_injective : Injective p.succAbove`).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ProjectiveLocus`,
  `Appendix_FixedPoint.BezoutChain.chartDel_spec`
  (proved above). -/
theorem dehomogAtCoord_succAbove (n : ℕ) (K : Type*) [Field K] (c : Fin (n + 2))
    (k : Fin (n + 1)) :
    dehomogAtCoord n K c (c.succAbove k) = MvPolynomial.X k := by
  have h : c.succAbove k ≠ c := Fin.succAbove_ne _ _
  unfold dehomogAtCoord
  rw [dite_eq_right h]
  congr 1
  exact Fin.succAbove_right_injective (chartDel_spec n c (c.succAbove k) h)

/-- Dehomogenization at `c` as a ring hom: evaluate at `X_c = 1`.
Generalizes `dehomogHom` (the `c = Fin.last _` case).

## References

* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.eval₂Hom`
  (`def eval₂Hom (f : R →+* S₁) (g : σ → S₁) : MvPolynomial σ R →+* S₁`). -/
noncomputable def dehomogAtHom (n : ℕ) (K : Type*) [Field K] (c : Fin (n + 2)) :
    MvPolynomial (Fin (n + 2)) K →+* MvPolynomial (Fin (n + 1)) K :=
  MvPolynomial.eval₂Hom MvPolynomial.C (dehomogAtCoord n K c)

/-- Dehomogenization of a polynomial at chart `c`: `φ ↦ φ(x, 1)` with the
`1` inserted at coordinate `c`. Generalizes `dehomog`.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ProjectiveLocus`,
  `Appendix_FixedPoint.BezoutChain.dehomogAtHom`
  (proved above). -/
noncomputable def dehomogAt (n : ℕ) (K : Type*) [Field K] (c : Fin (n + 2))
    (φ : MvPolynomial (Fin (n + 2)) K) : MvPolynomial (Fin (n + 1)) K :=
  dehomogAtHom n K c φ

/-- Dehomogenization at `c` fixes constants.

## References

* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.eval₂Hom_C`
  (`@[simp] theorem eval₂Hom_C (f) (g) (r) : eval₂Hom f g (C r) = f r`),
  `MvPolynomial.eval_C`. -/
@[simp]
theorem dehomogAt_C (n : ℕ) (K : Type*) [Field K] (c : Fin (n + 2)) (a : K) :
    dehomogAt n K c (MvPolynomial.C a) = MvPolynomial.C a := by
  unfold dehomogAt dehomogAtHom
  simp

/-- Dehomogenization at `c` sends each variable to its substitution value.

## References

* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.eval₂Hom_X'`
  (`@[simp] theorem eval₂Hom_X' (f) (g) (i) : eval₂Hom f g (X i) = g i`). -/
@[simp]
theorem dehomogAt_X (n : ℕ) (K : Type*) [Field K] (c : Fin (n + 2))
    (j : Fin (n + 2)) :
    dehomogAt n K c (MvPolynomial.X j) = dehomogAtCoord n K c j := by
  unfold dehomogAt dehomogAtHom
  simp

/-- Evaluation commutes with dehomogenization at `c`: evaluating the
dehomogenized polynomial at `x` is evaluating the original at
`insertNth c 1 x`. Generalizes `eval_dehomog`.

## References

* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.eval₂Hom`,
  `MvPolynomial.map_eval₂Hom`, `MvPolynomial.eval`.
* `Mathlib/Data/Fin/Tuple/Basic.lean`, `Fin.insertNth_apply_same`
  (`@[simp] theorem insertNth_apply_same (i) (x) (p):
    insertNth i x p i = x`),
  `Fin.insertNth_apply_succAbove`
  (`@[simp] theorem insertNth_apply_succAbove (i) (x) (p) (j):
    insertNth i x p (i.succAbove j) = p j`).
* `Mathlib/Data/Fin/SuccPred.lean`, `Fin.exists_succAbove_eq` (cited above).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ProjectiveLocus`,
  `Appendix_FixedPoint.BezoutChain.dehomogAtCoord_self`,
  `Appendix_FixedPoint.BezoutChain.dehomogAtCoord_succAbove`
  (proved above). -/
theorem eval_dehomogAt (n : ℕ) (K : Type*) [Field K] (c : Fin (n + 2))
    (φ : MvPolynomial (Fin (n + 2)) K) (x : Fin (n + 1) → K) :
    MvPolynomial.eval x (dehomogAt n K c φ)
      = MvPolynomial.eval (Fin.insertNth (α := fun _ => K) c 1 x) φ := by
  have hC : (MvPolynomial.eval x).comp MvPolynomial.C = RingHom.id K := by
    ext a
    simp only [RingHom.comp_apply, MvPolynomial.eval_C, RingHom.id_apply]
  have hg : (fun j => MvPolynomial.eval x (dehomogAtCoord n K c j))
      = Fin.insertNth (α := fun _ => K) c 1 x := by
    funext j
    by_cases hj : j = c
    · subst hj
      rw [dehomogAtCoord_self, map_one, Fin.insertNth_apply_same]
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
      rw [dehomogAtCoord_succAbove, MvPolynomial.eval_X,
        Fin.insertNth_apply_succAbove]
  calc MvPolynomial.eval x (dehomogAt n K c φ)
      = MvPolynomial.eval₂Hom (RingHom.id K)
          (Fin.insertNth (α := fun _ => K) c 1 x) φ := by
        unfold dehomogAt dehomogAtHom
        rw [MvPolynomial.map_eval₂Hom, hC, hg]
    _ = MvPolynomial.eval (Fin.insertNth (α := fun _ => K) c 1 x) φ := rfl

/-- The `c = 1` section point is always nonzero (its `c`-th coordinate is
`1`). Generalizes `snoc_one_ne_zero`.

## References

* `Mathlib/Data/Fin/Tuple/Basic.lean`, `Fin.insertNth_apply_same`. -/
theorem insertNth_one_ne_zero (n : ℕ) (K : Type*) [Field K] (c : Fin (n + 2))
    (x : Fin (n + 1) → K) :
    Fin.insertNth (α := fun _ => K) c (1 : K) x ≠ 0 := by
  intro h
  have h1 := congrFun h c
  simp [Fin.insertNth_apply_same] at h1

/-- Chart points descend to affine zeros at chart `c`. Generalizes
`dehomog_eval_of_mem_chart_last`.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ProjectiveLocus`,
  `Appendix_FixedPoint.BezoutChain.eval_smul_of_isHomogeneous`,
  `Appendix_FixedPoint.BezoutChain.eval_dehomogAt` (proved above).
* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.eval`.
* `Mathlib/Data/Fin/Tuple/Basic.lean`, `Fin.insertNth_apply_same`,
  `Fin.insertNth_apply_succAbove`.
* `Mathlib/Data/Fin/SuccPred.lean`, `Fin.exists_succAbove_eq`. -/
theorem dehomogAt_eval_of_mem_chart (n : ℕ) (K : Type*) [Field K]
    (c : Fin (n + 2))
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (d : Fin (n + 1) → ℕ)
    (hG : ∀ i, (G i).IsHomogeneous (d i))
    (v : Fin (n + 2) → K)
    (hc : v c ≠ 0)
    (hGv : ∀ i, MvPolynomial.eval v (G i) = 0) :
    ∀ i, MvPolynomial.eval
      (fun j => (v c)⁻¹ * v (c.succAbove j))
      (dehomogAt n K c (G i)) = 0 := by
  have hws : Fin.insertNth (α := fun _ => K) c 1
        (fun j => (v c)⁻¹ * v (c.succAbove j))
      = (v c)⁻¹ • v := by
    funext j
    by_cases hj : j = c
    · subst hj
      rw [Fin.insertNth_apply_same, Pi.smul_apply, smul_eq_mul,
        inv_mul_cancel₀ hc]
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
      rw [Fin.insertNth_apply_succAbove, Pi.smul_apply, smul_eq_mul]
  intro i
  rw [eval_dehomogAt, hws, eval_smul_of_isHomogeneous (hG i), hGv i, mul_zero]

/-- Chart transfer at `c` (closed): the `D₊(X_c)` piece of the locus is covered
by the `mk`-image of any finset covering the affine zero locus of the
chart-`c` dehomogenized system. Generalizes
`chart_last_cover_of_affine_cover`.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ProjectiveLocus`,
  `Appendix_FixedPoint.BezoutChain.dehomogAt_eval_of_mem_chart`,
  `Appendix_FixedPoint.BezoutChain.insertNth_one_ne_zero`
  (proved above).
* `Mathlib/LinearAlgebra/Projectivization/Basic.lean`,
  `Projectivization.mk`, `Projectivization.mk_eq_mk_iff'`.
* `Mathlib/Data/Finset/Image.lean`, `Finset.mem_image`.
* `Mathlib/Data/Fin/Tuple/Basic.lean`, `Fin.insertNth_apply_same`,
  `Fin.insertNth_apply_succAbove`.
* `Mathlib/Data/Fin/SuccPred.lean`, `Fin.exists_succAbove_eq`. -/
theorem chart_cover_of_affine_cover_at (n : ℕ) (K : Type*) [Field K]
    (c : Fin (n + 2))
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (d : Fin (n + 1) → ℕ)
    (hG : ∀ i, (G i).IsHomogeneous (d i))
    (S : Finset (Fin (n + 1) → K))
    (haff : ∀ x, (∀ i, MvPolynomial.eval x (dehomogAt n K c (G i)) = 0)
      → x ∈ S) :
    ∃ t : Finset (Projectivization K (Fin (n + 2) → K)),
      chartSet n K c ∩ vanishingLocus n K G ⊆ ↑t := by
  classical
  refine ⟨S.image (fun x => Projectivization.mk K
    (Fin.insertNth (α := fun _ => K) c 1 x)
    (insertNth_one_ne_zero n K c x)), fun p hp => ?_⟩
  obtain ⟨⟨v, hv, hmk, hc⟩, hloc⟩ := hp
  have hGv : ∀ i, MvPolynomial.eval v (G i) = 0 := fun i => hloc v hv hmk i
  have hxmem : ∀ i, MvPolynomial.eval
      (fun j => (v c)⁻¹ * v (c.succAbove j))
      (dehomogAt n K c (G i)) = 0 :=
    dehomogAt_eval_of_mem_chart n K c G d hG v hc hGv
  have hws : Fin.insertNth (α := fun _ => K) c 1
        (fun j => (v c)⁻¹ * v (c.succAbove j))
      = (v c)⁻¹ • v := by
    funext j
    by_cases hj : j = c
    · subst hj
      rw [Fin.insertNth_apply_same, Pi.smul_apply, smul_eq_mul,
        inv_mul_cancel₀ hc]
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
      rw [Fin.insertNth_apply_succAbove, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mem_coe, Finset.mem_image]
  refine ⟨_, haff _ hxmem, ?_⟩
  have hscale : Projectivization.mk K
        (Fin.insertNth (α := fun _ => K) c 1
          (fun j => (v c)⁻¹ * v (c.succAbove j)))
        (insertNth_one_ne_zero n K c _) =
        Projectivization.mk K v hv :=
    (Projectivization.mk_eq_mk_iff' K _ v _ hv).mpr
      ⟨(v c)⁻¹, hws.symm⟩
  exact hscale.trans hmk

/-- R-aff at chart `c`: the chart-`c` affine zero locus is covered by a finset
as soon as its affine quotient is zero-dimensional.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ProjectiveLocus`,
  `Appendix_FixedPoint.BezoutChain.affine_cover_of_krullDimLE_zero_general` (proved in `(b-aff)`),
  `Appendix_FixedPoint.BezoutChain.dehomogAt` (proved above). -/
theorem affine_cover_at_of_krullDimLE_zero (n : ℕ) (K : Type*) [Field K]
    (c : Fin (n + 2))
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hdim : Ring.KrullDimLE 0 (MvPolynomial (Fin (n + 1)) K ⧸
      Ideal.span (Set.range (fun i => dehomogAt n K c (G i))))) :
    ∃ S : Finset (Fin (n + 1) → K),
      ∀ x, (∀ i, MvPolynomial.eval x (dehomogAt n K c (G i)) = 0) → x ∈ S :=
  affine_cover_of_krullDimLE_zero_general _ hdim

/-! ## (b-asm) Assembly from the single residual hypothesis (R-dim)

`ChartDimZero` is the single weakest explicit hypothesis: zero-dimensionality
of every chart's affine quotient. From it, per-chart affine covers
(`affine_cover_at_of_krullDimLE_zero`) feed the general transfer
(`chart_cover_of_affine_cover_at`) at every chart, and the union step
(`hcover_of_chart_covers`) yields `finite_locus`'s `hcover`; the `mkSystem`
bundle additionally discharges `locus_nonempty`'s `hA` slot. The remaining
implication `IsZeroDimensional ⟹ ChartDimZero` is the exact residual R-dim in
`## Obstruction (b)`. -/

/-- Explicit residual hypothesis R-dim (single): every chart's affine quotient
is zero-dimensional. This is the chart-dimension consequence that
`IsZeroDimensional` of the projective cone should imply; the implication
itself is the only remaining gap (see `## Obstruction (b)`).

## References

* `Mathlib/RingTheory/KrullDimension/Basic.lean`, `Ring.KrullDimLE`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Statement.Definitions`,
  `Appendix_FixedPoint.BezoutChain.IsZeroDimensional`
  (`Ring.KrullDimLE 1` of the cone; the hypothesis this should imply).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ProjectiveLocus`,
  `Appendix_FixedPoint.BezoutChain.dehomogAt`
  (proved in `(b-gen)`). -/
def ChartDimZero (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K) : Prop :=
  ∀ c : Fin (n + 2), Ring.KrullDimLE 0
    (MvPolynomial (Fin (n + 1)) K ⧸
      Ideal.span (Set.range (fun i => dehomogAt n K c (G i))))

/-- Global `hcover` from the single residual hypothesis (closed modulo R-dim):
per-chart affine covers from `ChartDimZero` feed the general transfer at every
chart. Homogeneity `hG` is needed at each chart for `c`-normalization.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ProjectiveLocus`,
  `Appendix_FixedPoint.BezoutChain.hcover_of_chart_covers`,
  `Appendix_FixedPoint.BezoutChain.chart_cover_of_affine_cover_at`,
  `Appendix_FixedPoint.BezoutChain.affine_cover_at_of_krullDimLE_zero` (proved above).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Counting`,
  `Appendix_FixedPoint.BezoutChain.finite_locus` (whose `hcover`
  slot the conclusion discharges). -/
theorem hcover_of_chartDimZero (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (d : Fin (n + 1) → ℕ)
    (hG : ∀ i, (G i).IsHomogeneous (d i))
    (hdrop : ChartDimZero n K G) :
    ∃ t : Finset (Projectivization K (Fin (n + 2) → K)),
      vanishingLocus n K G ⊆ ↑t := by
  apply hcover_of_chart_covers
  intro c
  obtain ⟨S, hS⟩ := affine_cover_at_of_krullDimLE_zero n K c G (hdrop c)
  exact chart_cover_of_affine_cover_at n K c G d hG S hS

/-- `mkSystem` bundle from the single residual hypothesis (closed modulo
R-dim): at the canonical system with homogeneous quadratic inputs, the caller
supplies only `hF` and `ChartDimZero`, and receives `finite_locus`'s `hcover`
slot together with `locus_nonempty`'s `hA` slot (via
`section_maxSpec_nonempty_mkSystem`, which needs no further input).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Statement.Statement`,
  `Appendix_FixedPoint.BezoutChain.mkSystem_homogeneous`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ProjectiveLocus`,
  `Appendix_FixedPoint.BezoutChain.hcover_of_chartDimZero`,
  `Appendix_FixedPoint.BezoutChain.section_maxSpec_nonempty_mkSystem` (proved above).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Counting`,
  `Appendix_FixedPoint.BezoutChain.finite_locus`,
  `Appendix_FixedPoint.BezoutChain.locus_nonempty` (whose `hcover` / `hA` slots this discharges). -/
theorem hcover_mkSystem_of_zeroDim (n : ℕ) (K : Type*) [Field K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2)
    (ℓ : Fin (n + 2) → K)
    (hdrop : ChartDimZero n K (mkSystem n K F)) :
    (∃ t : Finset (Projectivization K (Fin (n + 2) → K)),
      vanishingLocus n K (mkSystem n K F) ⊆ ↑t)
      ∧ Nonempty (MaximalSpectrum (sectionQuotient n K (mkSystem n K F) ℓ)) := by
  refine ⟨?_, section_maxSpec_nonempty_mkSystem n K F ℓ hF⟩
  exact hcover_of_chartDimZero n K _ (fun _ => 2)
    (mkSystem_homogeneous n K F hF) hdrop

/- ## Obstruction (b) — conditional on the single residual R-dim.

Proved above:
* the multi-chart union step (`hcover_of_chart_covers`), using all
  `Fin (n+2)` standard charts (a single section chart `D₊(ℓ)` does not
  suffice — it misses `V(ℓ)` — so the Artinian-section route alone cannot
  yield `hcover`; the multi-chart argument is essential);
* the `z`-chart transfer (`chart_last_cover_of_affine_cover` in `(b″)`)
  and its generalization to every chart (`chart_cover_of_affine_cover_at`
  in `(b-gen)`, via the choice-based deletion coordinate
  `dehomogAtCoord`/`dehomogAt` repeating the full `(b′)` fragment:
  `eval_dehomogAt`, degree bounds, lift/descend);
* the affine bridge (`zeroLocus_finite_of_krullDimLE_zero` in `(b-aff)`):
  a `KrullDimLE 0` affine quotient has finite `zeroLocus` — Noetherian plus
  dimension-zero ⟹ Artinian
  (`IsNoetherianRing.isArtinianRing_of_krullDimLE_zero`), finitely many
  maximal ideals (`IsArtinianRing.setOfPred_isMaximal_finite`), points inject
  into them through the Nullstellensatz Galois connection (no `IsAlgClosed`
  needed for this direction) — hence per-chart affine covers
  (`affine_cover_of_krullDimLE_zero`, `affine_cover_at_of_krullDimLE_zero`);
* the assembly from the single hypothesis (`hcover_of_chartDimZero` and the
  `mkSystem` bundle `hcover_mkSystem_of_zeroDim`, which additionally
  discharges the `locus_nonempty` `hA` slot via
  `section_maxSpec_nonempty_mkSystem`). The earlier conditional assembly
  (`hcover_of_affine_last_and_other_charts`,
  `hcover_mkSystem_of_affine_and_charts`) is subsumed; its `haff` input is
  now discharged by `affine_cover_of_krullDimLE_zero` modulo the
  chart-dimension hypothesis.

Residual (single — `hcover` is closed iff it proves):
* R-dim (genuinely absent Mathlib API): the chart-dimension drop —
  `IsZeroDimensional n K G` (`KrullDimLE 1` of the cone) implies
  `ChartDimZero n K G` (`KrullDimLE 0` of every chart's affine quotient
  `MvPolynomial (Fin (n+1)) K ⧸ span (range (dehomogAt c G))`). Grep evidence
  in v4.34.0: `dehomog` (any case) has zero hits in `.lake/packages/mathlib`
  (the only `Homogenization.lean`,
  `Mathlib/LinearAlgebra/AffineSpace/Homogenization.lean`, concerns
  homogenization of affine spaces, unrelated), so no in-tree lemma can even
  state the drop; the height bounds in
  `Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean` go the wrong way
  (generators bound height from above only via minimal primes). The future
  proof starts from Noether normalization, which does exist:
  `exists_finite_inj_algHom_of_fg`
  (`Mathlib/RingTheory/NoetherNormalization.lean`), toward the contrapositive
  "a positive-dimensional finitely generated `K`-algebra over an infinite
  algebraically closed field has infinitely many `K`-points". Neither
  `IsAlgClosed K` nor `Infinite K` is needed for anything proved above; both
  belong to the future R-dim proof. -/

/-! ## (c) hcontra-target: finite locus forces a one-dimensional cone -/

/-- A zero-dimensional affine cone is projectively zero-dimensional: the
`0 → 1` lift is the in-tree Krull-dimension monotonicity lemma.

## References

* `Mathlib/RingTheory/KrullDimension/Basic.lean`, `Ring.KrullDimLE`
  (`abbrev Ring.KrullDimLE (n) (R) : Prop`).
* `Mathlib/Order/KrullDimension.lean`, `Order.KrullDimLE.mono`
  (`lemma KrullDimLE.mono (e : n ≤ m) (α) : KrullDimLE m α`).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Definitions`,
  `Appendix_FixedPoint.BezoutChain.IsZeroDimensional`
  (`Ring.KrullDimLE 1 (coneQuotient n K G)`). -/
theorem isZeroDimensional_of_krullDimLE_zero (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (h0 : Ring.KrullDimLE 0 (coneQuotient n K G)) :
    IsZeroDimensional n K G :=
  @Order.KrullDimLE.mono 0 1 zero_le_one _ _ h0

/-- `hcontra` under an affine zero-dimensionality hypothesis (binder shape
`Finite → IsZeroDimensional` copied verbatim from
`Counting.infinite_locus_of_not_zeroDim`).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Counting`,
  `Appendix_FixedPoint.BezoutChain.infinite_locus_of_not_zeroDim`
  (whose `hcontra` slot this targets). -/
theorem hcontra_of_krullDimLE_zero (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (h0 : Ring.KrullDimLE 0 (coneQuotient n K G)) :
    (vanishingLocus n K G).Finite → IsZeroDimensional n K G :=
  fun _ => isZeroDimensional_of_krullDimLE_zero n K G h0

/- ## Obstruction (c) — partial: from locus finiteness to cone dimension.

Proved above: the last step (affine `KrullDimLE 0` ⟹ `IsZeroDimensional`,
hence `hcontra`). What resists: deriving any cone dimension bound from
finiteness of the projective locus — the affine-cone-over-finite-set picture
(the cone over finitely many projective points is a finite union of lines
through the origin, hence `≤ 1`-dimensional). There is no API connecting
`vanishingLocus` / `MvPolynomial.zeroLocus` finiteness to `Ring.KrullDimLE`
(or to prime coheights) in Mathlib v4.34.0, and the height bounds in
`Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean` (e.g.
`Ideal.height_span_le_ncard_of_span_ne_top`) go the wrong way: generators
bound height from above only via minimal primes, while the needed
projective-affine prime correspondence is itself missing (cf.
`CountingHandoff` G-contra). -/

/-! ## (d) `hZd` chain assembly: `ChartDimZero` + `hcontra` give the cone bound

This closes the `hcover → hZd` chain end-to-end modulo the two documented
residuals: Link A (`hcover` from `ChartDimZero`, proved above as
`hcover_of_chartDimZero`) feeds `CountingHandoff.hZd_of_hcover_and_hcontra`
(Link A + explicit `hcontra`), which this module may use directly since it
already imports `CountingHandoff` (no new import edge in either direction).
Residual R-dim (`IsZeroDimensional ⟹ ChartDimZero`, `## Obstruction (b)`)
and residual R-cone (genuine `hcontra`, `## Obstruction (c)`) are unchanged
and genuinely open — this theorem only wires the proved links. -/

/-- `hZd` from the chart-dimension drop plus the dimension–finiteness converse:
`ChartDimZero` supplies Link A (`hcover`) and the explicit `hcontra`-shape
hypothesis (binder copied verbatim from
`Counting.infinite_locus_of_not_zeroDim`) supplies Link B. Residuals R-dim
and R-cone stay open (see `## Obstruction (b)` / `(c)`).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ProjectiveLocus`,
  `Appendix_FixedPoint.BezoutChain.hcover_of_chartDimZero` (Link A, proved above).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.CountingHandoff`,
  `Appendix_FixedPoint.BezoutChain.hZd_of_hcover_and_hcontra` (Link A + Link B assembly).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Counting`,
  `Appendix_FixedPoint.BezoutChain.infinite_locus_of_not_zeroDim` (whose `hcontra` slot Link B
  copies). -/
theorem hZd_of_chartDimZero_and_hcontra (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (d : Fin (n + 1) → ℕ)
    (hG : ∀ i, (G i).IsHomogeneous (d i))
    (hdrop : ChartDimZero n K G)
    (hcontra : (vanishingLocus n K G).Finite → IsZeroDimensional n K G) :
    IsZeroDimensional n K G :=
  hZd_of_hcover_and_hcontra n K G
    (hcover_of_chartDimZero n K G d hG hdrop) hcontra

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
