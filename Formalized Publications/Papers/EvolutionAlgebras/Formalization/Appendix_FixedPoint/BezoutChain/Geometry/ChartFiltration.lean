/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Statement.Definitions
import Appendix_FixedPoint.BezoutChain.Geometry.LocalMultiplicity
import Appendix_FixedPoint.BezoutChain.Dimension.ArtinianDecomposition
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Action.Units
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Regular.SMul
import Mathlib.GroupTheory.MonoidLocalization.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Spectrum.Maximal.Defs
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Nullstellensatz

/-!
# Chart filtration (route (ii′))

This module builds the filtration geometry that Elimination's
`chart_bridge` stands on: with `S = coneQuotient n K G`,
`ℓ̄` the image of `mkLin ℓ`, and `A = (S_ℓ)₀ = chartRing n K G ℓ` the degree-`0`
part,

* `chartPiece d` (`G_d`): the `K`-submodule of fractions `s / ℓ̄ ^ d` whose
  numerator admits a homogeneous degree-`d` lift. Exact-denominator
  presentation (rather than `≤ d`): sums keep the common denominator `ℓ̄ ^ d`
  (`Localization.add_mk_self`), so each `G_d` is genuinely a submodule; the
  choice of submodules (rather than a bare predicate) is documented here, as
  the task permits either formulation.
* `sectionPiece d` (`(S/ℓS)_d`): the `K`-submodule of
  `sectionQuotient n K G ℓ` of classes admitting a homogeneous degree-`d` lift.
* `chart_filtration_exhaust`: `⋃ d, G_d = univ` — every chart element carries
  its balanced degree, read off from `Definitions.chartRing` itself.
* `chart_step_finrank`: `finrank K G_{d+1} = finrank K G_d + finrank K (S/ℓS)_{d+1}`
  (the finrank form of the graded piece, which is all downstream uses need),
  via rank-nullity on the grade map (`LinearMap.finrank_range_add_finrank_ker`)
  with the range (`gradeMap_range_eq_top`) and kernel (`gradeMap_ker_eq`, from
  `hreg` (`ℓ`-torsionfreeness) plus the explicit homogeneous-descent hypothesis
  `DescentData`) computations. Quotient types
  are avoided throughout since `HasQuotient` synthesis diverges on these
  types.
* `chart_finrank_telescope` / `chart_finrank_eq_sum_pieces`: summation
  interface — from exhaustion-stabilization plus the step equation,
  `finrank K A = finrank K G_0 + ∑ d ∈ range D, finrank K (S/ℓS)_{d+1}`.
* `chartPiece_zero_equiv` / `chartPiece_zero_finrank`: `G_0 ≃ₗ[K] K`
  (evaluation at `0`, using `hG0`), so the sum starts at `1`.

## Handoff to Counting

`Counting.sum_mult_eq_chart_length` (`∑ p ∈ locusFinset, mult p = finrank K A`)
consumes `chart_finrank_eq_sum_pieces` (which turns `finrank K A` into
`finrank K G_0 + ∑` section-piece dimensions) together with
`chartPiece_zero_finrank` (`finrank K G_0 = 1`). The remaining section-side
identity `1 + ∑_d dim (S/ℓS)_{d+1} = finrank K (S/ℓS)` (high-degree vanishing
plus the section-side telescope) belongs to the Counting/HilbertFunctionCount strands,
which own the Artinian input (`section_artinian`) and the Hilbert-function
recurrence.

## Residual outputs (this module's Counting inputs)

* `ChartNonvanishing` (`hc`): the R1 nonvanishing shape feeding
  `LocalMultiplicity.localPointMultiplicity` / `LocalMultiplicity.haddLocal` (and, at `p.rep`
  via `chartNonvanishing_at`, `LocalMultiplicity.hposLocal`'s `hℓ`).
* `chart_finite_of_stable` (`hfinA`, proved): filtration stabilization plus
  piece-finiteness makes the chart finite over `K`, feeding
  `LocalMultiplicity.hposLocal`; `chart_pos_of_point` is the composed positivity
  (`Counting.mult_pos_of_mem`'s `hpos` route).
* `ChartLocFinite` (`hfinLoc`) and `ChartDecomp` (`hdecomp`): the G2 Artinian
  inputs feeding `LocalMultiplicity.haddLocal` (`Counting.sum_mult_eq_chart_length`'s
  `hadd` route), stated in `LocalMultiplicity`'s vocabulary
  (`locLocusFinset` / `locFam`, imported below; no cycle since `LocalMultiplicity`
  imports only `Statement.Definitions`).

## Added hypotheses

1. `hreg : IsSMulRegular S (mk ℓ)` — as in `Elimination.chart_bridge`, stated
   with the explicit quotient image (as produced by
   `Appendix_FixedPoint.BezoutChain.exists_regular_chartForm`), since `IsSMulRegular` needs an
   element
   of `S`, not a polynomial.
2. `DescentData n K G ℓ d` (new, named): if `mk p = t * ℓ̄` with `p`
   homogeneous of degree `d + 1`, then `t` admits a homogeneous degree-`d`
   lift. This is the homogeneous-cofactor step of the kernel computation; it
   is the standard consequence of "`span (range G)` is a homogeneous ideal"
   (homogeneous components of an ideal element stay in the ideal) and is left
   as an explicit hypothesis rather than reproved.
3. `hstab : chartPiece D = ⊤` (new, named): stabilization of the filtration.
   Follows from exhaustion + finite-dimensionality + monotonicity once the
   Counting supplies those; taken as a hypothesis here.
4. `hfin : ∀ d, Module.Finite K ↥(chartPiece d)` (new, named): finiteness of
   each piece, needed for rank-nullity at every telescope step.
5. `hfinS : ∀ d, Module.Finite K ↥(sectionPiece d)` (new, named): finiteness of
   each section piece, needed for the same rank-nullity step.
6. `hG0 : ∀ i, eval 0 (G i) = 0` (new, named): the equations vanish at `0`
   (immediate from homogeneity, cf. `ResultantLemmas`' `heval0`), needed so
   evaluation at `0` descends to the cone and `G_0 ≃ K`.

## Discharged inputs
* `DescentData` ← `descentData_of_quadrics` (from Statement's `hG` + `hreg`).
* `hfin` ← `chartPiece_finite` (unconditional).
* `hfinS` ← `sectionPiece_finite_of_finite` (from ambient section finiteness,
  discharged downstream by `section_finite_of_artinian` from `hreg` + `hZd`).
* `hG0` ← `hG0_of_quadrics` (from Statement's `hG`).
* `hstab` ← `chartPiece_stabilizes_of_finite` (from chart finiteness, via
  `chart_finite_of_sectionPiece_vanishing` from the `hvan` finrank shape).
* `chart_bridge`'s `hlin` content ← `chart_bridge_finrank` (`Elimination`).

## Appended closures (G2 / MaxSpec / prime-patch)

The sections after `Chart residuals for Counting` close the
`hfinA` / `hbij` / `hstab` / MaxSpec-correspondence inputs in consumer
shapes; each section header states its exact residual list:

* G2 closure: `chartHfinA_of_stable`, `chartLocFinite_of_finite`,
  `ChartMaxSpecInj` / `ChartMaxSpecSurj`, `chart_hadd_of_stable`.
* ChartMaxSpec closure: the residue step (`chartAlgHom_of_maximal`) plus
  the narrow transfer conditions (`ChartEvalSeparation` /
  `ChartPointTransfer` with `chartMaxSpecInj_of_separation` /
  `chartMaxSpecSurj_of_transfer`).
* Stabilization from the section side (`chartStab_of_sectionVanishing`),
  `FinalResiduals` ∀-shape adapters, injectivity closure
  (`chartMaxSpecInj_forall`, unconditional), the `chartOfHomog` API, and
  surjectivity closure (`chartMaxSpecSurj_forall`, from `[hG]`).
* Minimal-prime avoidance: `ConeMinAvoidWitness` (every
  minimal prime of the cone sits below a maximal ideal missing `ℓ̄`)
  implies `SecFormAvoidsMinimal` (`minAvoid_of_maxSpecWitness`,
  `secFormAvoidsMinimal_of_witness`).
* Prime patch: the literal witness is false as stated —
  refuted at `n = 0`, `F = (X₀²)` by the non-prime `Q = span{z̄}`
  (`coneMinAvoidWitness_false_n0`). The patched
  `ConeMinAvoidWitnessPrime` adds the `Q.IsPrime` hypothesis (exactly
  what downstream consumes: `R1RegularSection` applies avoidance only at
  associated, hence prime, ideals), with prime-indexed twins
  `minAvoid_of_maxSpecWitness_prime` /
  `secFormAvoidsMinimal_of_witness_prime`.
* FiniteDimDischarge (`MinAvoidDischarge`): the patched witness is
  discharged end-to-end from `[IsAlgClosed K, hF, hcut]` via the
  strong-Nullstellensatz component witness
  (`component_mem_vz_eq_originMap`) and the axis-prime witness
  (`axisPrimeCone_below_origin`), giving `secFormAvoidsMinimal_prime`,
  `coneMinAvoidWitness_prime`, and `coneMinAvoidWitnessPrime_discharge`.

## Standing context (routine binders, not residuals)

Per-declaration GRADE lines track only non-standing residuals. The following
recur verbatim across declarations and are documented once here: `hvG` /
`hvGw` (pointwise vanishing of `G` at a point representative), `hG` / `hF`
(quadratic homogeneity of the input system), `hfin` (locus finiteness),
`hc` (chart nonvanishing), and instance binders (`[Field K]`,
`[IsAlgClosed K]` where taken).

## References

Mathlib v4.34.0 has no graded-ring / Hilbert-function API, so the filtration
is built from localization, homogeneous-polynomial, and finrank API. Exact
module paths and declaration names (each verified in-tree) are cited per
declaration below.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
open scoped BigOperators

/-! ## Filtration pieces -/

/-- The image `ℓ̄` of the chart linear form in the cone quotient `S`.
Private helper; public statements use the explicit quotient image (matching
`Elimination.chart_bridge`'s `hreg`, as produced by
`Appendix_FixedPoint.BezoutChain.exists_regular_chartForm`).

## References

* `Mathlib/RingTheory/Ideal/Quotient/Defs.lean`, `Ideal.Quotient.mk`. -/
private noncomputable abbrev ℓbar (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) : coneQuotient n K G :=
  Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)

/-- The denominator `ℓ̄ ^ d` as an element of the localized submonoid, with the
canonical powers-membership proof — stated exactly as in
`Definitions.chartRing` so membership witnesses transfer definitionally.

## References

* `Mathlib/Algebra/Group/Submonoid/Membership.lean`,
  `Submonoid.mem_powers_iff`
  (`x ∈ powers z ↔ ∃ n, z ^ n = x`; `Submonoid.powers` from
  `Mathlib/Algebra/Group/Submonoid/Membership.lean`). -/
private noncomputable abbrev denom (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (d : ℕ) :
    Submonoid.powers (ℓbar n K G ℓ) :=
  ⟨(ℓbar n K G ℓ) ^ d, (Submonoid.mem_powers_iff _ _).mpr ⟨d, rfl⟩⟩

/-- The `d`-th filtration piece `G_d`: fractions `s / ℓ̄ ^ d` whose numerator
admits a homogeneous degree-`d` lift, as a `K`-submodule of the chart ring.
Exact-denominator formulation: `add_mem'` keeps the common denominator
`ℓ̄ ^ d`, `smul_mem'` uses a constant (`degree-0`) lift for the scalar.

## References

* `Mathlib/RingTheory/Localization/Defs.lean`, `Localization.add_mk_self`
  (`mk a b + mk c b = mk (a + c) b`), `Localization.mk_zero`,
  `Localization.smul_mk` (`c • mk a b = mk (c • a) b`, needs
  `[SMul K S] [IsScalarTower K S S]` from the `K`-algebra structure).
* `Mathlib/Algebra/Algebra/Defs.lean`, `Algebra.smul_def`
  (`r • x = algebraMap R A r * x`).
* `Mathlib/RingTheory/Ideal/Quotient/Operations.lean`,
  `Ideal.Quotient.mk_algebraMap`.
* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.isHomogeneous_C` (explicit-`σ` first argument, as in
  `Definitions.chartRing`), `MvPolynomial.isHomogeneous_zero`,
  `MvPolynomial.IsHomogeneous.add/mul`.
* `Mathlib/Algebra/MvPolynomial/Basic.lean`, `MvPolynomial.algebraMap_eq`. -/
noncomputable def chartPiece (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (d : ℕ) : Submodule K (chartRing n K G ℓ) where
  carrier := {x | ∃ p : MvPolynomial (Fin (n + 2)) K, p.IsHomogeneous d ∧
    (x : chartRing n K G ℓ).val =
      Localization.mk (Ideal.Quotient.mk (Ideal.span (Set.range G)) p)
        (denom n K G ℓ d)}
  add_mem' := by
    intro x y hx hy
    obtain ⟨p, hp, epx⟩ := hx
    obtain ⟨q, hq, eqy⟩ := hy
    refine ⟨p + q, hp.add hq, ?_⟩
    have ecalc : (x : chartRing n K G ℓ).val + (y : chartRing n K G ℓ).val
        = Localization.mk
          (Ideal.Quotient.mk (Ideal.span (Set.range G)) (p + q))
          (denom n K G ℓ d) := by
      rw [epx, eqy, Localization.add_mk_self, ← map_add]
    exact ecalc
  zero_mem' := by
    refine ⟨0, MvPolynomial.isHomogeneous_zero _ _ d, ?_⟩
    change (0 : Localization (Submonoid.powers (ℓbar n K G ℓ))) =
      Localization.mk (Ideal.Quotient.mk (Ideal.span (Set.range G)) 0)
        (denom n K G ℓ d)
    rw [map_zero, Localization.mk_zero]
  smul_mem' := by
    intro c x hx
    obtain ⟨p, hp, epx⟩ := hx
    have hmap : Ideal.Quotient.mk (Ideal.span (Set.range G)) (MvPolynomial.C c)
        = algebraMap K (coneQuotient n K G) c := by
      have hC : (MvPolynomial.C c : MvPolynomial (Fin (n + 2)) K)
          = algebraMap K (MvPolynomial (Fin (n + 2)) K) c := by
        rw [MvPolynomial.algebraMap_eq]
      rw [hC]
      exact Ideal.Quotient.mk_algebraMap K _ _
    have hhom : (MvPolynomial.C c * p).IsHomogeneous d := by
      have h := (MvPolynomial.isHomogeneous_C _ c).mul hp
      rwa [zero_add] at h
    refine ⟨MvPolynomial.C c * p, hhom, ?_⟩
    have ecalc : c • (x : chartRing n K G ℓ).val
        = Localization.mk
          (Ideal.Quotient.mk (Ideal.span (Set.range G)) (MvPolynomial.C c * p))
          (denom n K G ℓ d) := by
      have esmul : c • Localization.mk
          (Ideal.Quotient.mk (Ideal.span (Set.range G)) p) (denom n K G ℓ d)
          = Localization.mk
            (c • Ideal.Quotient.mk (Ideal.span (Set.range G)) p)
            (denom n K G ℓ d) :=
        Localization.smul_mk (R := K) _ _ _
      have esmul2 : c • Ideal.Quotient.mk (Ideal.span (Set.range G)) p
          = algebraMap K (coneQuotient n K G) c
            * Ideal.Quotient.mk (Ideal.span (Set.range G)) p :=
        Algebra.smul_def (A := coneQuotient n K G) c _
      rw [epx, esmul, esmul2, ← hmap, ← map_mul]
    exact ecalc

/-- The degree-`d` part `(S/ℓS)_d` of the section: classes admitting a
homogeneous degree-`d` lift, as a `K`-submodule of the section quotient.

## References

* `Mathlib/RingTheory/Ideal/Quotient/Defs.lean`, `Ideal.Quotient.mk`.
* `Mathlib/Algebra/Algebra/Defs.lean`, `Algebra.smul_def`.
* `Mathlib/RingTheory/Ideal/Quotient/Operations.lean`,
  `Ideal.Quotient.mk_algebraMap`.
* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.isHomogeneous_C`, `MvPolynomial.isHomogeneous_zero`,
  `MvPolynomial.IsHomogeneous.add/mul`. -/
noncomputable def sectionPiece (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (d : ℕ) : Submodule K (sectionQuotient n K G ℓ) where
  carrier := {y | ∃ p : MvPolynomial (Fin (n + 2)) K, p.IsHomogeneous d ∧
    Ideal.Quotient.mk (Ideal.span
        ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
          Set (coneQuotient n K G)))
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) p) = y}
  add_mem' := by
    intro x y hx hy
    obtain ⟨p, hp, epx⟩ := hx
    obtain ⟨q, hq, eqy⟩ := hy
    refine ⟨p + q, hp.add hq, ?_⟩
    rw [map_add, map_add, ← epx, ← eqy]
  zero_mem' := by
    refine ⟨0, MvPolynomial.isHomogeneous_zero _ _ d, ?_⟩
    rw [map_zero, map_zero]
  smul_mem' := by
    intro c x hx
    obtain ⟨p, hp, epx⟩ := hx
    have hmap : Ideal.Quotient.mk (Ideal.span (Set.range G)) (MvPolynomial.C c)
        = algebraMap K (coneQuotient n K G) c := by
      have hC : (MvPolynomial.C c : MvPolynomial (Fin (n + 2)) K)
          = algebraMap K (MvPolynomial (Fin (n + 2)) K) c := by
        rw [MvPolynomial.algebraMap_eq]
      rw [hC]
      exact Ideal.Quotient.mk_algebraMap K _ _
    have hmapS : algebraMap K (coneQuotient n K G) c
        = Ideal.Quotient.mk (Ideal.span (Set.range G)) (MvPolynomial.C c) :=
      hmap.symm
    have hhom : (MvPolynomial.C c * p).IsHomogeneous d := by
      have h := (MvPolynomial.isHomogeneous_C _ c).mul hp
      rwa [zero_add] at h
    refine ⟨MvPolynomial.C c * p, hhom, ?_⟩
    have esmul : c • Ideal.Quotient.mk (Ideal.span
          ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
            Set (coneQuotient n K G)))
          (Ideal.Quotient.mk (Ideal.span (Set.range G)) p)
        = algebraMap K (sectionQuotient n K G ℓ) c
          * Ideal.Quotient.mk (Ideal.span
            ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
              Set (coneQuotient n K G)))
            (Ideal.Quotient.mk (Ideal.span (Set.range G)) p) :=
      Algebra.smul_def (A := sectionQuotient n K G ℓ) c _
    rw [← epx, esmul, ← Ideal.Quotient.mk_algebraMap K _ _, hmapS,
      ← map_mul, ← map_mul]

/-- The chart linear form is homogeneous of degree `1` (same proof as the
`add_mem'` step of `Definitions.chartRing`).

## References

* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.IsHomogeneous.sum`, `MvPolynomial.isHomogeneous_C_mul_X`. -/
theorem mkLin_isHomogeneous (n : ℕ) (K : Type*) [Field K]
    (ℓ : Fin (n + 2) → K) : (mkLin n K ℓ).IsHomogeneous 1 := by
  unfold mkLin
  exact MvPolynomial.IsHomogeneous.sum _ _ _ fun j _ =>
    MvPolynomial.isHomogeneous_C_mul_X _ _

/-! ## Lifts and fraction identities -/

/-- Every element of `G_m` admits a homogeneous degree-`m` lift over `ℓ̄ ^ m`
(unfolding the submodule membership).

## References

* `Mathlib/Algebra/Module/Submodule/Lattice.lean` (membership in a
  `Submodule` with set-builder carrier). -/
theorem chartPiece_mem_obtain (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (x : chartRing n K G ℓ) (m : ℕ)
    (hx : x ∈ chartPiece n K G ℓ m) :
    ∃ p : MvPolynomial (Fin (n + 2)) K, p.IsHomogeneous m ∧
      x.val = Localization.mk (Ideal.Quotient.mk (Ideal.span (Set.range G)) p)
        (denom n K G ℓ m) :=
  hx

/-- Constructor for filtration membership from an explicit homogeneous lift
(assembles the existential once, so kernel computations need not re-unfold
`chartPiece` at every use site).

## References

* `Mathlib/Algebra/Module/Submodule/Lattice.lean` (membership in a
  `Submodule` with set-builder carrier). -/
theorem mem_chartPiece_of_lift (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (x : chartRing n K G ℓ) (d : ℕ)
    (q : MvPolynomial (Fin (n + 2)) K) (hq : q.IsHomogeneous d)
    (e : x.val = Localization.mk (Ideal.Quotient.mk (Ideal.span (Set.range G)) q)
      (denom n K G ℓ d)) : x ∈ chartPiece n K G ℓ d :=
  ⟨q, hq, e⟩

/-- Multiplying numerator and denominator by `ℓ̄` does not change the fraction
(the `G_d ≤ G_{d+1}` step).

## References

* `Mathlib/GroupTheory/MonoidLocalization/Basic.lean`,
  `Localization.mk_eq_mk_iff`
  (`mk a b = mk c d ↔ r S ⟨a, b⟩ ⟨c, d⟩`), `Localization.r_of_eq`
  (the `c = 1` case of `Localization.r_iff_exists`). -/
theorem mk_mul_ℓbar (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (p : MvPolynomial (Fin (n + 2)) K) (d : ℕ) :
    Localization.mk (Ideal.Quotient.mk (Ideal.span (Set.range G)) p)
        (denom n K G ℓ d)
      = Localization.mk
        (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ * p))
        (denom n K G ℓ (d + 1)) := by
  have hnum : Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ * p)
      = Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)
        * Ideal.Quotient.mk (Ideal.span (Set.range G)) p :=
    map_mul _ _ _
  refine Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq ?_)
  change (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ (d + 1)
      * Ideal.Quotient.mk (Ideal.span (Set.range G)) p
    = (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ d
      * Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ * p)
  rw [hnum, pow_succ']
  ring

/-- Denominator cancellation: equal fractions with `ℓ̄`-power denominators have
equal numerators, using R1-regularity (`hreg`) — `ℓ`-torsionfreeness, with
powers of the regular element regular by `IsSMulRegular.pow`.

## References

* `Mathlib/GroupTheory/MonoidLocalization/Basic.lean`,
  `Localization.mk_eq_mk_iff`, `Localization.r_iff_exists`.
* `Mathlib/Algebra/Group/Submonoid/Membership.lean`,
  `Submonoid.mem_powers_iff`.
* `Mathlib/Algebra/Regular/SMul.lean`, `IsSMulRegular.pow`.
* `Mathlib/Algebra/Group/Action/Defs.lean`, `smul_eq_mul`. -/
theorem mk_cancel_of_mk_eq (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    (a a' : coneQuotient n K G) (d : ℕ)
    (h : Localization.mk a (denom n K G ℓ d)
      = Localization.mk a' (denom n K G ℓ d)) :
    a = a' := by
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists] at h
  obtain ⟨c, hc⟩ := h
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp c.2
  have hc' : (ℓbar n K G ℓ) ^ k * ((ℓbar n K G ℓ) ^ d * a)
      = (ℓbar n K G ℓ) ^ k * ((ℓbar n K G ℓ) ^ d * a') := by
    rw [hk]
    exact hc
  have hregpow := IsSMulRegular.pow (k + d)
    (show IsSMulRegular (coneQuotient n K G) (ℓbar n K G ℓ) from hreg)
  have hgoal : (ℓbar n K G ℓ) ^ (k + d) • a
      = (ℓbar n K G ℓ) ^ (k + d) • a' := by
    rw [smul_eq_mul, smul_eq_mul, pow_add]
    linear_combination hc'
  exact hregpow hgoal

/-- The section class of a lift is independent of the chosen lift
(well-definedness of the grade map).

## References

* `Mathlib/GroupTheory/MonoidLocalization/Basic.lean`
  (via `mk_cancel_of_mk_eq` above). -/
theorem gradeMap_welldef (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    (m : ℕ) (x : chartRing n K G ℓ) (p q : MvPolynomial (Fin (n + 2)) K)
    (_hp : p.IsHomogeneous m) (_hq : q.IsHomogeneous m)
    (ep : x.val = Localization.mk (Ideal.Quotient.mk (Ideal.span (Set.range G)) p)
      (denom n K G ℓ m))
    (eq : x.val = Localization.mk (Ideal.Quotient.mk (Ideal.span (Set.range G)) q)
      (denom n K G ℓ m)) :
    Ideal.Quotient.mk (Ideal.span
        ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
          Set (coneQuotient n K G)))
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) p)
      = Ideal.Quotient.mk (Ideal.span
        ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
          Set (coneQuotient n K G)))
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) q) := by
  apply congrArg (Ideal.Quotient.mk _)
  exact mk_cancel_of_mk_eq n K G ℓ hreg _ _ _ (ep.symm.trans eq)

/-- Chosen homogeneous lift of a filtration element (classical choice).

## References

* `Classical.choose` / `Classical.choose_spec` (core; one of the three
  permitted axioms). -/
noncomputable def chartLift (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (m : ℕ) (w : ↥(chartPiece n K G ℓ m)) :
    MvPolynomial (Fin (n + 2)) K :=
  Classical.choose (chartPiece_mem_obtain n K G ℓ (↑w) m w.2)

/-- The chosen lift is homogeneous of degree `m`. -/
theorem chartLift_hom (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (m : ℕ) (w : ↥(chartPiece n K G ℓ m)) :
    (chartLift n K G ℓ m w).IsHomogeneous m :=
  (Classical.choose_spec (chartPiece_mem_obtain n K G ℓ (↑w) m w.2)).1

/-- The chosen lift represents `w` over `ℓ̄ ^ m`. -/
theorem chartLift_eq (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (m : ℕ) (w : ↥(chartPiece n K G ℓ m)) :
    (↑w : chartRing n K G ℓ).val
      = Localization.mk
        (Ideal.Quotient.mk (Ideal.span (Set.range G)) (chartLift n K G ℓ m w))
        (denom n K G ℓ m) :=
  (Classical.choose_spec (chartPiece_mem_obtain n K G ℓ (↑w) m w.2)).2

/-! ## The grade map -/

/-- The grade map `G_{d+1} → (S/ℓS)_{d+1}`: send a fraction to the section
class of (any) homogeneous lift. Linearity is checked on chosen lifts via
`gradeMap_welldef`.

## References

* `Mathlib/RingTheory/Localization/Defs.lean`, `Localization.add_mk_self`;
  `Mathlib/GroupTheory/MonoidLocalization/Basic.lean`,
  `Localization.smul_mk`.
* `Mathlib/Algebra/Algebra/Defs.lean`, `Algebra.smul_def`.
* `Mathlib/RingTheory/Ideal/Quotient/Operations.lean`,
  `Ideal.Quotient.mk_algebraMap`. -/
noncomputable def gradeMap (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (d : ℕ)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ))) :
    ↥(chartPiece n K G ℓ (d + 1)) →ₗ[K] ↥(sectionPiece n K G ℓ (d + 1)) where
  toFun x := ⟨Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (chartLift n K G ℓ (d + 1) x)),
    chartLift n K G ℓ (d + 1) x, chartLift_hom n K G ℓ (d + 1) x, rfl⟩
  map_add' x y := by
    have hadd : ((↑(x + y) : ↥(chartPiece n K G ℓ (d + 1))) : chartRing n K G ℓ).val
        = Localization.mk (Ideal.Quotient.mk (Ideal.span (Set.range G))
            (chartLift n K G ℓ (d + 1) x + chartLift n K G ℓ (d + 1) y))
          (denom n K G ℓ (d + 1)) := by
      have ecalc : (↑x : chartRing n K G ℓ).val + (↑y : chartRing n K G ℓ).val
          = Localization.mk (Ideal.Quotient.mk (Ideal.span (Set.range G))
              (chartLift n K G ℓ (d + 1) x + chartLift n K G ℓ (d + 1) y))
            (denom n K G ℓ (d + 1)) := by
        rw [chartLift_eq n K G ℓ (d + 1) x, chartLift_eq n K G ℓ (d + 1) y,
          Localization.add_mk_self, ← map_add]
      exact ecalc
    apply Subtype.ext
    change Ideal.Quotient.mk (Ideal.span
        ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
          Set (coneQuotient n K G)))
        (Ideal.Quotient.mk (Ideal.span (Set.range G))
          (chartLift n K G ℓ (d + 1) (x + y)))
      = Ideal.Quotient.mk (Ideal.span
        ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
          Set (coneQuotient n K G)))
        (Ideal.Quotient.mk (Ideal.span (Set.range G))
          (chartLift n K G ℓ (d + 1) x))
        + Ideal.Quotient.mk (Ideal.span
        ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
          Set (coneQuotient n K G)))
        (Ideal.Quotient.mk (Ideal.span (Set.range G))
          (chartLift n K G ℓ (d + 1) y))
    have hwd := gradeMap_welldef n K G ℓ hreg (d + 1) _
      (chartLift n K G ℓ (d + 1) (x + y))
      (chartLift n K G ℓ (d + 1) x + chartLift n K G ℓ (d + 1) y)
      (chartLift_hom n K G ℓ (d + 1) (x + y))
      ((chartLift_hom n K G ℓ (d + 1) x).add (chartLift_hom n K G ℓ (d + 1) y))
      (chartLift_eq n K G ℓ (d + 1) (x + y)) hadd
    rw [hwd, map_add, map_add]
  map_smul' c x := by
    have hmap : Ideal.Quotient.mk (Ideal.span (Set.range G)) (MvPolynomial.C c)
        = algebraMap K (coneQuotient n K G) c := by
      have hC : (MvPolynomial.C c : MvPolynomial (Fin (n + 2)) K)
          = algebraMap K (MvPolynomial (Fin (n + 2)) K) c := by
        rw [MvPolynomial.algebraMap_eq]
      rw [hC]
      exact Ideal.Quotient.mk_algebraMap K _ _
    have hmapS : algebraMap K (coneQuotient n K G) c
        = Ideal.Quotient.mk (Ideal.span (Set.range G)) (MvPolynomial.C c) :=
      hmap.symm
    have hsec : algebraMap K (sectionQuotient n K G ℓ) c
        = Ideal.Quotient.mk (Ideal.span
          ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
            Set (coneQuotient n K G)))
          (algebraMap K (coneQuotient n K G) c) :=
      (Ideal.Quotient.mk_algebraMap K _ _).symm
    have hhom' : (MvPolynomial.C c * chartLift n K G ℓ (d + 1) x).IsHomogeneous
        (d + 1) := by
      have h := (MvPolynomial.isHomogeneous_C _ c).mul
        (chartLift_hom n K G ℓ (d + 1) x)
      rwa [zero_add] at h
    have hsmul : ((↑(c • x) : ↥(chartPiece n K G ℓ (d + 1))) : chartRing n K G ℓ).val
        = Localization.mk (Ideal.Quotient.mk (Ideal.span (Set.range G))
            (MvPolynomial.C c * chartLift n K G ℓ (d + 1) x))
          (denom n K G ℓ (d + 1)) := by
      have ecalc : c • (↑x : chartRing n K G ℓ).val
          = Localization.mk (Ideal.Quotient.mk (Ideal.span (Set.range G))
              (MvPolynomial.C c * chartLift n K G ℓ (d + 1) x))
            (denom n K G ℓ (d + 1)) := by
        have esmul : c • Localization.mk
            (Ideal.Quotient.mk (Ideal.span (Set.range G))
              (chartLift n K G ℓ (d + 1) x)) (denom n K G ℓ (d + 1))
            = Localization.mk
              (c • Ideal.Quotient.mk (Ideal.span (Set.range G))
                (chartLift n K G ℓ (d + 1) x)) (denom n K G ℓ (d + 1)) :=
          Localization.smul_mk (R := K) _ _ _
        have esmul2 : c • Ideal.Quotient.mk (Ideal.span (Set.range G))
              (chartLift n K G ℓ (d + 1) x)
            = algebraMap K (coneQuotient n K G) c
              * Ideal.Quotient.mk (Ideal.span (Set.range G))
                (chartLift n K G ℓ (d + 1) x) :=
          Algebra.smul_def (A := coneQuotient n K G) c _
        rw [chartLift_eq n K G ℓ (d + 1) x, esmul, esmul2, hmapS, ← map_mul]
      exact ecalc
    apply Subtype.ext
    change Ideal.Quotient.mk (Ideal.span
        ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
          Set (coneQuotient n K G)))
        (Ideal.Quotient.mk (Ideal.span (Set.range G))
          (chartLift n K G ℓ (d + 1) (c • x)))
      = (RingHom.id K) c • Ideal.Quotient.mk (Ideal.span
        ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
          Set (coneQuotient n K G)))
        (Ideal.Quotient.mk (Ideal.span (Set.range G))
          (chartLift n K G ℓ (d + 1) x))
    have hwd := gradeMap_welldef n K G ℓ hreg (d + 1) _
      (chartLift n K G ℓ (d + 1) (c • x))
      (MvPolynomial.C c * chartLift n K G ℓ (d + 1) x)
      (chartLift_hom n K G ℓ (d + 1) (c • x)) hhom'
      (chartLift_eq n K G ℓ (d + 1) (c • x)) hsmul
    have esec : c • Ideal.Quotient.mk (Ideal.span
        ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
          Set (coneQuotient n K G)))
        (Ideal.Quotient.mk (Ideal.span (Set.range G))
          (chartLift n K G ℓ (d + 1) x))
        = algebraMap K (sectionQuotient n K G ℓ) c
          * Ideal.Quotient.mk (Ideal.span
            ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
              Set (coneQuotient n K G)))
            (Ideal.Quotient.mk (Ideal.span (Set.range G))
              (chartLift n K G ℓ (d + 1) x)) :=
      Algebra.smul_def (A := sectionQuotient n K G ℓ) c _
    rw [hwd, RingHom.id_apply, esec, hsec, hmapS, ← map_mul, ← map_mul]

/-- The grade map sends any homogeneous lift to its section class
(public computation rule for `gradeMap`, whose chosen lift is internal).

## References

* `Mathlib/Algebra/Module/Submodule/Lattice.lean` (`Subtype.ext` is core). -/
theorem gradeMap_val_eq (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (d : ℕ)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    (w : ↥(chartPiece n K G ℓ (d + 1))) (p : MvPolynomial (Fin (n + 2)) K)
    (hp : p.IsHomogeneous (d + 1))
    (ep : (↑w : chartRing n K G ℓ).val
      = Localization.mk (Ideal.Quotient.mk (Ideal.span (Set.range G)) p)
        (denom n K G ℓ (d + 1))) :
        (gradeMap n K G ℓ d hreg w).val
      = Ideal.Quotient.mk (Ideal.span
        ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
          Set (coneQuotient n K G)))
        (Ideal.Quotient.mk (Ideal.span (Set.range G)) p) := by
  change Ideal.Quotient.mk (Ideal.span
      ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
        Set (coneQuotient n K G)))
      (Ideal.Quotient.mk (Ideal.span (Set.range G))
        (chartLift n K G ℓ (d + 1) w)) = _
  exact gradeMap_welldef n K G ℓ hreg (d + 1) _ (chartLift n K G ℓ (d + 1) w) p
    (chartLift_hom n K G ℓ (d + 1) w) hp (chartLift_eq n K G ℓ (d + 1) w) ep

/-! ## Exhaustion and monotonicity -/

/-- Filtration exhaustion (chart bridge): the pieces
`G_d` cover the chart — every degree-`0` fraction carries its balanced degree,
read off from `Definitions.chartRing` itself.

## References

* Core `Set.eq_univ_iff_forall`, `Set.mem_iUnion` (no Mathlib API needed
  beyond the `chartRing` carrier). -/
theorem chart_filtration_exhaust (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) :
    ⋃ d, (chartPiece n K G ℓ d : Set (chartRing n K G ℓ)) = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro x
  obtain ⟨d, s, ⟨p, hp, hps⟩, eℓ⟩ := x.2
  refine Set.mem_iUnion.mpr ⟨d, p, hp, ?_⟩
  rw [hps]
  exact eℓ

/-- One-step monotonicity `G_d ≤ G_{d+1}` (multiply top and bottom by `ℓ̄`;
the lift degree shifts by `1`). -/
theorem chartPiece_le_succ (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (d : ℕ) :
    chartPiece n K G ℓ d ≤ chartPiece n K G ℓ (d + 1) := by
  intro x hx
  obtain ⟨p, hp, epx⟩ := hx
  have hpq : (mkLin n K ℓ * p).IsHomogeneous (d + 1) :=
    add_comm 1 d ▸ (mkLin_isHomogeneous n K ℓ).mul hp
  exact ⟨mkLin n K ℓ * p, hpq, epx.trans (mk_mul_ℓbar n K G ℓ p d)⟩

/-- The filtration is monotone.

## References

* `Mathlib/Order/Monotone/Basic.lean`, `monotone_nat_of_le_succ`. -/
theorem chartPiece_mono (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) : Monotone (chartPiece n K G ℓ) :=
  monotone_nat_of_le_succ (chartPiece_le_succ n K G ℓ)

/-! ## Piece finiteness -/

/-- The degree-`d` homogeneous polynomials surject onto the filtration piece
`G_d`: send `p` to the fraction `mk p / ℓ̄ ^ d`. Linearity is the
`chartPiece` submodule computation (`add_mk_self` for sums, `smul_mk` plus
the constant-lift algebra computation for scalars).

## References

* `Mathlib/RingTheory/Localization/Defs.lean`, `Localization.add_mk_self`;
  `Mathlib/GroupTheory/MonoidLocalization/Basic.lean`,
  `Localization.smul_mk`.
* `Mathlib/RingTheory/Ideal/Quotient/Operations.lean`,
  `Ideal.Quotient.mk_algebraMap`.
* `Mathlib/Algebra/Algebra/Defs.lean`, `Algebra.smul_def`.
* `Mathlib/Algebra/MvPolynomial/Basic.lean`, `MvPolynomial.algebraMap_eq`,
  `MvPolynomial.smul_eq_C_mul`.
* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.mem_homogeneousSubmodule`. -/
noncomputable def chartPieceMk (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (d : ℕ) :
    ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 2)) K d)
      →ₗ[K] ↥(chartPiece n K G ℓ d) where
  toFun u := ⟨⟨Localization.mk (Ideal.Quotient.mk (Ideal.span (Set.range G)) u.val)
      (denom n K G ℓ d),
      d, Ideal.Quotient.mk (Ideal.span (Set.range G)) u.val,
      ⟨u.val, (MvPolynomial.mem_homogeneousSubmodule d u.val).mp u.2, rfl⟩, rfl⟩,
    u.val, (MvPolynomial.mem_homogeneousSubmodule d u.val).mp u.2, rfl⟩
  map_add' u v := by
    have ecalc : Localization.mk (Ideal.Quotient.mk (Ideal.span (Set.range G))
          (u.val + v.val)) (denom n K G ℓ d)
        = Localization.mk (Ideal.Quotient.mk (Ideal.span (Set.range G)) u.val)
          (denom n K G ℓ d)
        + Localization.mk (Ideal.Quotient.mk (Ideal.span (Set.range G)) v.val)
          (denom n K G ℓ d) := by
      rw [map_add, ← Localization.add_mk_self]
    have hval : ((u + v :
        ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 2)) K d)).val)
        = u.val + v.val := rfl
    apply Subtype.ext
    apply Subtype.ext
    change Localization.mk (Ideal.Quotient.mk (Ideal.span (Set.range G))
        (u + v).val) (denom n K G ℓ d)
      = Localization.mk (Ideal.Quotient.mk (Ideal.span (Set.range G)) u.val)
        (denom n K G ℓ d)
      + Localization.mk (Ideal.Quotient.mk (Ideal.span (Set.range G)) v.val)
        (denom n K G ℓ d)
    rw [hval]
    exact ecalc
  map_smul' c u := by
    have hmap : Ideal.Quotient.mk (Ideal.span (Set.range G)) (MvPolynomial.C c)
        = algebraMap K (coneQuotient n K G) c := by
      have hC : (MvPolynomial.C c : MvPolynomial (Fin (n + 2)) K)
          = algebraMap K (MvPolynomial (Fin (n + 2)) K) c := by
        rw [MvPolynomial.algebraMap_eq]
      rw [hC]
      exact Ideal.Quotient.mk_algebraMap K _ _
    have hval : ((c • u :
        ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 2)) K d)).val)
        = c • u.val := rfl
    apply Subtype.ext
    apply Subtype.ext
    change Localization.mk (Ideal.Quotient.mk (Ideal.span (Set.range G))
        (c • u).val) (denom n K G ℓ d)
      = c • Localization.mk (Ideal.Quotient.mk (Ideal.span (Set.range G)) u.val)
        (denom n K G ℓ d)
    rw [hval, MvPolynomial.smul_eq_C_mul u.val c, map_mul, hmap,
      ← Algebra.smul_def, Localization.smul_mk]

/-- `chartPieceMk` is surjective: every filtration element carries a
homogeneous lift (`chartLift`), which is the required preimage.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ChartFiltration`,
  `Appendix_FixedPoint.BezoutChain.chartLift`,
  `Appendix_FixedPoint.BezoutChain.chartLift_hom`,
  `Appendix_FixedPoint.BezoutChain.chartLift_eq` (this module).
* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.mem_homogeneousSubmodule`. -/
theorem chartPieceMk_surjective (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (d : ℕ) :
    Function.Surjective (chartPieceMk n K G ℓ d) := by
  intro w
  refine ⟨⟨chartLift n K G ℓ d w, ?_⟩, ?_⟩
  · exact (MvPolynomial.mem_homogeneousSubmodule d _).mpr
      (chartLift_hom n K G ℓ d w)
  · apply Subtype.ext
    apply Subtype.ext
    change Localization.mk (Ideal.Quotient.mk (Ideal.span (Set.range G))
        (chartLift n K G ℓ d w)) (denom n K G ℓ d) = w.val.val
    exact (chartLift_eq n K G ℓ d w).symm

/-- Each chart piece is finite over `K` (discharges the `hfin` hypothesis
unconditionally): it is a linear quotient of the finite-dimensional space of
homogeneous degree-`d` polynomials (`MvPolynomial.homogeneousSubmodule_fg`).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ChartFiltration`,
  `Appendix_FixedPoint.BezoutChain.chartPieceMk`,
  `Appendix_FixedPoint.BezoutChain.chartPieceMk_surjective` (this module).
* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.homogeneousSubmodule_fg`.
* `Mathlib/RingTheory/Finiteness/Basic.lean`, `Module.Finite.of_fg`.
* `Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean`,
  `FiniteDimensional.of_surjective`. -/
theorem chartPiece_finite (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (d : ℕ) :
    Module.Finite K ↥(chartPiece n K G ℓ d) := by
  have : Module.Finite K
      ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 2)) K d) :=
    Module.Finite.of_fg
      (MvPolynomial.homogeneousSubmodule_fg (Fin (n + 2)) K d)
  exact FiniteDimensional.of_surjective
    (V := ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 2)) K d))
    (V₂ := ↥(chartPiece n K G ℓ d))
    (chartPieceMk n K G ℓ d) (chartPieceMk_surjective n K G ℓ d)

/-- Each section piece is finite over a finite section (the `hfinS`
hypothesis from ambient finiteness; downstream discharges the instance by
`section_finite_of_artinian` from `hreg` + `hZd`): a submodule of a finite
module over a field is finite, by instance resolution.

## References

* `Mathlib/RingTheory/Finiteness/Basic.lean`, `Module.Finite` (the class
  closed here by instance resolution). -/
theorem sectionPiece_finite_of_finite (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    [Module.Finite K (sectionQuotient n K G ℓ)] (d : ℕ) :
    Module.Finite K ↥(sectionPiece n K G ℓ d) := inferInstance

/-! ## Graded pieces -/

/-- Homogeneous descent along `ℓ̄` (explicit extra hypothesis, reported in the
module docstring): if `mk p = t * ℓ̄` with `p` homogeneous of degree `d + 1`,
the cofactor `t` admits a homogeneous degree-`d` lift. This is the
homogeneous-cofactor step of the grade-map kernel computation. -/
def DescentData (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (d : ℕ) : Prop :=
  ∀ (p : MvPolynomial (Fin (n + 2)) K) (t : coneQuotient n K G),
    p.IsHomogeneous (d + 1) →
    Ideal.Quotient.mk (Ideal.span (Set.range G)) p
      = t * Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ) →
    ∃ q : MvPolynomial (Fin (n + 2)) K, q.IsHomogeneous d ∧
      Ideal.Quotient.mk (Ideal.span (Set.range G)) q = t

/-- Homogeneous components commute with multiplication against a homogeneous
right factor: the degree-`(m + n)` component of `f * g` with `g` homogeneous
of degree `n` is the degree-`m` component of `f` times `g`. The proof is
coefficient-wise (`MvPolynomial.ext`): on the antidiagonal the surviving
terms have `x.2.degree = n` (else `g.coeff x.2 = 0`), so
`d.degree = m + n ↔ x.1.degree = m` by degree additivity.

## References

* `Mathlib/Algebra/MvPolynomial/Basic.lean`, `MvPolynomial.ext`,
  `MvPolynomial.coeff_mul`.
* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.coeff_homogeneousComponent`,
  `MvPolynomial.IsHomogeneous.coeff_eq_zero`.
* `Finset.mem_antidiagonal` (the `Finset.HasAntidiagonal` membership lemma).
* `Mathlib/Data/Finsupp/Weight.lean`, `Finsupp.degree` (an `AddMonoidHom`,
  via `map_add`). -/
theorem homogeneousComponent_mul_of_isHomogeneous_right
    {σ : Type*} {R : Type*} [CommSemiring R]
    (f g : MvPolynomial σ R) (m n : ℕ) (hg : g.IsHomogeneous n) :
    MvPolynomial.homogeneousComponent (m + n) (f * g)
      = MvPolynomial.homogeneousComponent m f * g := by
  classical
  apply MvPolynomial.ext
  intro d
  rw [MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_mul,
    MvPolynomial.coeff_mul]
  by_cases hd : d.degree = m + n
  · rw [ite_eq_left hd]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [MvPolynomial.coeff_homogeneousComponent]
    have hxmem : x.1 + x.2 = d := Finset.mem_antidiagonal.mp hx
    have hdegsum : x.1.degree + x.2.degree = d.degree := by
      rw [← hxmem, map_add]
    by_cases h2 : x.2.degree = n
    · have hdeg1 : x.1.degree = m := by omega
      rw [ite_eq_left hdeg1]
    · have hg2 : g.coeff x.2 = 0 := hg.coeff_eq_zero h2
      simp [hg2]
  · rw [ite_eq_right hd]
    symm
    apply Finset.sum_eq_zero
    intro x hx
    rw [MvPolynomial.coeff_homogeneousComponent]
    have hxmem : x.1 + x.2 = d := Finset.mem_antidiagonal.mp hx
    have hdegsum : x.1.degree + x.2.degree = d.degree := by
      rw [← hxmem, map_add]
    by_cases h2 : x.2.degree = n
    · have hdeg1 : x.1.degree ≠ m := by omega
      rw [ite_eq_right hdeg1, zero_mul]
    · have hg2 : g.coeff x.2 = 0 := hg.coeff_eq_zero h2
      simp [hg2]

/-- Low-degree homogeneous components of a multiple of a homogeneous
polynomial vanish: every monomial of `f * g` with `g` homogeneous of degree
`n` has degree `≥ n`. Coefficient-wise via `MvPolynomial.ext`: on the
antidiagonal, `x.2.degree ≤ d.degree = t < n` forces `g.coeff x.2 = 0`.

## References

* `Mathlib/Algebra/MvPolynomial/Basic.lean`, `MvPolynomial.ext`,
  `MvPolynomial.coeff_mul`, `MvPolynomial.coeffAddMonoidHom` (via `map_zero`).
* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.coeff_homogeneousComponent`,
  `MvPolynomial.IsHomogeneous.coeff_eq_zero`.
* `Finset.mem_antidiagonal` (the `Finset.HasAntidiagonal` membership lemma).
* `Mathlib/Data/Finsupp/Weight.lean`, `Finsupp.degree` (an `AddMonoidHom`,
  via `map_add`). -/
theorem homogeneousComponent_mul_eq_zero_of_lt
    {σ : Type*} {R : Type*} [CommSemiring R]
    (f g : MvPolynomial σ R) (t n : ℕ) (hg : g.IsHomogeneous n)
    (hlt : t < n) :
    MvPolynomial.homogeneousComponent t (f * g) = 0 := by
  classical
  apply MvPolynomial.ext
  intro d
  have h0 : (0 : MvPolynomial σ R).coeff d = 0 :=
    map_zero (MvPolynomial.coeffAddMonoidHom d)
  rw [h0, MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_mul]
  by_cases hd : d.degree = t
  · rw [ite_eq_left hd]
    apply Finset.sum_eq_zero
    intro x hx
    have hxmem : x.1 + x.2 = d := Finset.mem_antidiagonal.mp hx
    have hdegsum : x.1.degree + x.2.degree = d.degree := by
      rw [← hxmem, map_add]
    have h2 : x.2.degree ≠ n := by omega
    have hg2 : g.coeff x.2 = 0 := hg.coeff_eq_zero h2
    rw [hg2, mul_zero]
  · rw [ite_eq_right hd]

/-- Homogeneous components stay in a homogeneous-generated span: if every
generator `G i` is homogeneous (of degree `2`), so is every homogeneous
component of every element of `Ideal.span (Set.range G)`. From the finite-sum
presentation the claim reduces to the product lemmas above (the top case by
`homogeneousComponent_mul_of_isHomogeneous_right`, degrees `< 2` by
`homogeneousComponent_mul_eq_zero_of_lt`).

## References

* `Mathlib/RingTheory/Ideal/Operations.lean`,
  `Ideal.mem_span_range_iff_exists_fun`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ChartFiltration`,
  `Appendix_FixedPoint.BezoutChain.homogeneousComponent_mul_of_isHomogeneous_right`,
  `Appendix_FixedPoint.BezoutChain.homogeneousComponent_mul_eq_zero_of_lt` (this module). -/
theorem homogeneousComponent_mem_span_of_isHomogeneous
    {σ : Type*} {R : Type*} [CommSemiring R]
    {ι : Type*} [Finite ι] (G : ι → MvPolynomial σ R)
    (hG : ∀ i, (G i).IsHomogeneous 2)
    (f : MvPolynomial σ R) (hf : f ∈ Ideal.span (Set.range G)) (t : ℕ) :
    MvPolynomial.homogeneousComponent t f ∈ Ideal.span (Set.range G) := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hf
  rw [← hc, map_sum]
  refine sum_mem (fun i _ => ?_)
  by_cases ht : t < 2
  · have hz : MvPolynomial.homogeneousComponent t (c i * G i) = 0 :=
      homogeneousComponent_mul_eq_zero_of_lt (c i) (G i) t 2 (hG i) ht
    rw [hz]
    exact Submodule.zero_mem _
  · have ht : 2 ≤ t := le_of_not_gt ht
    obtain ⟨m, rfl⟩ : ∃ m, t = m + 2 := ⟨t - 2, by omega⟩
    rw [homogeneousComponent_mul_of_isHomogeneous_right (c i) (G i) m 2 (hG i)]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

/-- `DescentData` from quadrics + R1-regularity (discharges the explicit
homogeneous-cofactor hypothesis): if `mk p = t * ℓ̄` with `p` homogeneous of
degree `d + 1`, take any lift `q` of `t`; then `p - q * ℓ` lies in the
equation span, so its degree-`(d + 1)` homogeneous component does too
(`homogeneousComponent_mem_span_of_isHomogeneous`), i.e.
`p - (homogeneousComponent d q) * ℓ ∈ span` (using
`homogeneousComponent_mul_of_isHomogeneous_right` with `ℓ` homogeneous of
degree `1`); cancelling `ℓ̄` by `hreg` gives `t = mk (homogeneousComponent d q)`.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ChartFiltration`,
  `Appendix_FixedPoint.BezoutChain.homogeneousComponent_mem_span_of_isHomogeneous`,
  `Appendix_FixedPoint.BezoutChain.homogeneousComponent_mul_of_isHomogeneous_right`,
  `Appendix_FixedPoint.BezoutChain.mkLin_isHomogeneous` (this module).
* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.homogeneousComponent_eq_self`,
  `MvPolynomial.homogeneousComponent_isHomogeneous`.
* `Mathlib/RingTheory/Ideal/Quotient/Defs.lean`,
  `Ideal.Quotient.mk_surjective`, `Ideal.Quotient.eq_zero_iff_mem`.
* `Mathlib/Algebra/Regular/SMul.lean`, `IsSMulRegular` (cancellation).
* `Mathlib/Algebra/Group/Action/Defs.lean`, `smul_eq_mul`. -/
theorem descentData_of_quadrics (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hG : ∀ i, (G i).IsHomogeneous 2)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    (d : ℕ) : DescentData n K G ℓ d := by
  intro p t hp heq
  obtain ⟨q, hq⟩ := Ideal.Quotient.mk_surjective t
  have hmem : p - q * mkLin n K ℓ ∈ Ideal.span (Set.range G) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have e : Ideal.Quotient.mk (Ideal.span (Set.range G)) p
        = Ideal.Quotient.mk (Ideal.span (Set.range G)) (q * mkLin n K ℓ) := by
      rw [heq, ← hq, map_mul]
    rw [map_sub, e, sub_self]
  have hcomp := homogeneousComponent_mem_span_of_isHomogeneous G hG
    (p - q * mkLin n K ℓ) hmem (d + 1)
  rw [map_sub, MvPolynomial.homogeneousComponent_eq_self hp] at hcomp
  have hmul : MvPolynomial.homogeneousComponent (d + 1) (q * mkLin n K ℓ)
      = MvPolynomial.homogeneousComponent d q * mkLin n K ℓ :=
    homogeneousComponent_mul_of_isHomogeneous_right q (mkLin n K ℓ) d 1
      (mkLin_isHomogeneous n K ℓ)
  rw [hmul] at hcomp
  have hmk0 : Ideal.Quotient.mk (Ideal.span (Set.range G)) p
      - Ideal.Quotient.mk (Ideal.span (Set.range G))
        (MvPolynomial.homogeneousComponent d q)
      * Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ) = 0 := by
    have h0 := Ideal.Quotient.eq_zero_iff_mem.mpr hcomp
    rwa [map_sub, map_mul] at h0
  have hcancel : t * Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)
      = Ideal.Quotient.mk (Ideal.span (Set.range G))
        (MvPolynomial.homogeneousComponent d q)
        * Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ) := by
    rw [← heq]
    exact sub_eq_zero.mp hmk0
  have hsmul : Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ) • t
      = Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ) •
        Ideal.Quotient.mk (Ideal.span (Set.range G))
          (MvPolynomial.homogeneousComponent d q) := by
    rw [smul_eq_mul, smul_eq_mul]
    linear_combination hcancel
  have hteq : t = Ideal.Quotient.mk (Ideal.span (Set.range G))
      (MvPolynomial.homogeneousComponent d q) := hreg hsmul
  exact ⟨MvPolynomial.homogeneousComponent d q,
    MvPolynomial.homogeneousComponent_isHomogeneous d q, hteq.symm⟩

/-- The grade map is surjective onto the section piece (every homogeneous lift
occurs).

## References

* `Mathlib/Algebra/Module/Submodule/Lattice.lean`, `Submodule.eq_top_iff'`,
  `Submodule.mem_top`; `LinearMap.mem_range` (core Mathlib linear-map API). -/
theorem gradeMap_range_eq_top (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (d : ℕ)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ))) :
    LinearMap.range (gradeMap n K G ℓ d hreg) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro z
  obtain ⟨q, hq, eqz⟩ := z.2
  rw [LinearMap.mem_range]
  refine ⟨⟨⟨Localization.mk (Ideal.Quotient.mk (Ideal.span (Set.range G)) q)
    (denom n K G ℓ (d + 1)), by
    exact ⟨d + 1, Ideal.Quotient.mk (Ideal.span (Set.range G)) q,
      ⟨q, hq, rfl⟩, rfl⟩⟩, q, hq, rfl⟩, ?_⟩
  have hwd : (gradeMap n K G ℓ d hreg ⟨⟨Localization.mk
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) q) (denom n K G ℓ (d + 1)),
      by exact ⟨d + 1, Ideal.Quotient.mk (Ideal.span (Set.range G)) q,
        ⟨q, hq, rfl⟩, rfl⟩⟩, q, hq, rfl⟩).val
      = Ideal.Quotient.mk (Ideal.span
        ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
          Set (coneQuotient n K G)))
        (Ideal.Quotient.mk (Ideal.span (Set.range G)) q) := by
    apply gradeMap_val_eq n K G ℓ d hreg _ q hq
    rfl
  apply Subtype.ext
  rw [hwd]
  exact eqz

/-- The easy kernel inclusion: `G_d` maps to `0` in the section
(`ℓ̄` times anything dies in `S/ℓS`).

## References

* `Mathlib/RingTheory/Ideal/Quotient/Defs.lean`,
  `Ideal.Quotient.eq_zero_iff_mem`.
* `Mathlib/RingTheory/Ideal/Span.lean`, `Ideal.mem_span_singleton'`.
* `Mathlib/Algebra/Module/Submodule/Map.lean`, `Submodule.mem_comap`. -/
theorem gradeMap_comap_le_ker (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (d : ℕ)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ))) :
    (chartPiece n K G ℓ d).comap (chartPiece n K G ℓ (d + 1)).subtype
      ≤ LinearMap.ker (gradeMap n K G ℓ d hreg) := by
  intro y hy
  have hy' := chartPiece_mem_obtain _ _ _ _
    ((chartPiece n K G ℓ (d + 1)).subtype y) d (Submodule.mem_comap.mp hy)
  obtain ⟨q, hq, eqy⟩ := hy'
  have hpq : (mkLin n K ℓ * q).IsHomogeneous (d + 1) :=
    add_comm 1 d ▸ (mkLin_isHomogeneous n K ℓ).mul hq
  have e1 := gradeMap_val_eq n K G ℓ d hreg y (mkLin n K ℓ * q) hpq
    (eqy.trans (mk_mul_ℓbar n K G ℓ q d))
  have hnum : Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ * q)
      = Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)
        * Ideal.Quotient.mk (Ideal.span (Set.range G)) q :=
    map_mul _ _ _
  rw [hnum] at e1
  have hmem : Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)
        * Ideal.Quotient.mk (Ideal.span (Set.range G)) q
      ∈ Ideal.span
        ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
          Set (coneQuotient n K G)) :=
    Ideal.mem_span_singleton'.mpr ⟨_, mul_comm _ _⟩
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hmem] at e1
  rw [LinearMap.mem_ker]
  exact Subtype.ext e1

/-- Cofactor equation for the kernel descent (split out as its own lemma so
each command stays within the heartbeat budget): from `mk p = t * ℓ̄` and
`mk q = t`, the lift `p` equals `ℓ̄ * q` in the cone.

## References

* `Mathlib/Algebra/Group/Hom/Defs.lean` (`map_mul` is core). -/
theorem descent_cofactor_eq (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (p : MvPolynomial (Fin (n + 2)) K) (t : coneQuotient n K G)
    (ht : t * Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)
      = Ideal.Quotient.mk (Ideal.span (Set.range G)) p)
    (q : MvPolynomial (Fin (n + 2)) K)
    (eq : Ideal.Quotient.mk (Ideal.span (Set.range G)) q = t) :
    Ideal.Quotient.mk (Ideal.span (Set.range G)) p
      = Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ * q) :=
  calc Ideal.Quotient.mk (Ideal.span (Set.range G)) p
      = t * Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ) :=
        ht.symm
    _ = Ideal.Quotient.mk (Ideal.span (Set.range G)) q
        * Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ) := by
        rw [eq]
    _ = Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ * q) := by
        rw [map_mul, mul_comm]

set_option maxHeartbeats 1000000 in
-- Raised budget: the kernel-inclusion proof rewrites through nested quotient/localization goals.
/-- The hard kernel inclusion `ker gradeMap ≤ G_d` (split out as its own
lemma so each command stays within the heartbeat budget): a lift mapping to
`0` in the section is divisible by `ℓ̄`, and the cofactor descends a degree
via `DescentData`.

## References

* `Mathlib/RingTheory/Ideal/Quotient/Defs.lean`,
  `Ideal.Quotient.eq_zero_iff_mem`.
* `Mathlib/RingTheory/Ideal/Span.lean`, `Ideal.mem_span_singleton'`.
* `Mathlib/Algebra/Module/Submodule/Map.lean`, `Submodule.mem_comap`. -/
theorem gradeMap_ker_le_comap (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (d : ℕ)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    (hdesc : DescentData n K G ℓ d) :
    LinearMap.ker (gradeMap n K G ℓ d hreg)
      ≤ (chartPiece n K G ℓ d).comap (chartPiece n K G ℓ (d + 1)).subtype := by
  intro y hy
  have hy0 : gradeMap n K G ℓ d hreg y = 0 := LinearMap.mem_ker.mp hy
  have h0 : (gradeMap n K G ℓ d hreg y).val = 0 := congrArg Subtype.val hy0
  obtain ⟨p, hp, ep⟩ := chartPiece_mem_obtain _ _ _ _ _ (d + 1) y.2
  have hclass : Ideal.Quotient.mk (Ideal.span
      ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
        Set (coneQuotient n K G)))
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) p) = 0 :=
    (gradeMap_val_eq n K G ℓ d hreg y p hp ep).symm.trans h0
  rw [Ideal.Quotient.eq_zero_iff_mem] at hclass
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hclass
  obtain ⟨q, hq, eq⟩ := hdesc p t hp ht.symm
  have e2 : Ideal.Quotient.mk (Ideal.span (Set.range G)) p
      = Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ * q) :=
    descent_cofactor_eq n K G ℓ p t ht q eq
  have efinal : (↑y : chartRing n K G ℓ).val
      = Localization.mk (Ideal.Quotient.mk (Ideal.span (Set.range G)) q)
        (denom n K G ℓ d) := by
    rw [ep, e2, ← mk_mul_ℓbar n K G ℓ q d]
  rw [Submodule.mem_comap]
  exact mem_chartPiece_of_lift n K G ℓ _ _ q hq efinal

set_option maxHeartbeats 1000000 in
-- Raised budget: typechecking the kernel computation against the comap statement is slow.
/-- The kernel of the grade map is exactly `G_d` (both inclusions). -/
theorem gradeMap_ker_eq (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (d : ℕ)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    (hdesc : DescentData n K G ℓ d) :
    LinearMap.ker (gradeMap n K G ℓ d hreg)
      = (chartPiece n K G ℓ d).comap (chartPiece n K G ℓ (d + 1)).subtype :=
  le_antisymm (gradeMap_ker_le_comap n K G ℓ d hreg hdesc)
    (gradeMap_comap_le_ker n K G ℓ d hreg)

set_option maxHeartbeats 1000000 in
-- Raised budget: finrank unification over the grade-map range type is slow.
/-- Finrank of the grade-map range: surjectivity (`gradeMap_range_eq_top`) plus
`finrank_top`. Split out so each command stays within the heartbeat budget.

## References

* `Mathlib/LinearAlgebra/Dimension/Finrank.lean`, `finrank_top`. -/
theorem gradeMap_range_finrank (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (d : ℕ)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ))) :
    Module.finrank K ↥(LinearMap.range (gradeMap n K G ℓ d hreg))
      = Module.finrank K ↥(sectionPiece n K G ℓ (d + 1)) := by
  rw [gradeMap_range_eq_top n K G ℓ d hreg, finrank_top]

set_option maxHeartbeats 1000000 in
-- Raised budget: finrank unification over the kernel/comap equivalence is slow.
/-- Finrank of the grade-map kernel: the kernel computation
(`gradeMap_ker_eq`, from `hreg` plus `DescentData`), identified with the
previous piece via `Submodule.comapSubtypeEquivOfLe`. Split out so each
command stays within the heartbeat budget.

## References

* `Mathlib/LinearAlgebra/Dimension/Finrank.lean`, `LinearEquiv.finrank_eq`.
* `Mathlib/Algebra/Module/Submodule/Map.lean`,
  `Submodule.comapSubtypeEquivOfLe`. -/
theorem gradeMap_ker_finrank (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (d : ℕ)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    (hdesc : DescentData n K G ℓ d) :
    Module.finrank K ↥(LinearMap.ker (gradeMap n K G ℓ d hreg))
      = Module.finrank K ↥(chartPiece n K G ℓ d) := by
  have hmono : chartPiece n K G ℓ d ≤ chartPiece n K G ℓ (d + 1) :=
    chartPiece_mono n K G ℓ (Nat.le_succ d)
  rw [gradeMap_ker_eq n K G ℓ d hreg hdesc]
  exact LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hmono)

set_option maxHeartbeats 2000000 in
-- Raised budget: the rank-nullity assembly over large graded-piece types is slow.
/-- Step finrank equation (chart bridge): each filtration
step adds exactly the section-piece dimension,
`finrank K G_{d+1} = finrank K G_d + finrank K (S/ℓS)_{d+1}`. This is the
finrank form of the graded piece (which is all downstream uses need). The
proof is rank-nullity on the grade map
(`LinearMap.finrank_range_add_finrank_ker`), with the range
(`gradeMap_range_finrank`) and kernel (`gradeMap_ker_finrank`, from `hreg`
(`ℓ`-torsionfreeness) plus the explicit homogeneous-descent hypothesis
`DescentData`) computations. Quotient types are avoided
throughout because `HasQuotient` synthesis diverges for submodules over
`chartRing`.

## References

* `Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean`,
  `LinearMap.finrank_range_add_finrank_ker`. -/
theorem chart_step_finrank (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (d : ℕ)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    (hdesc : DescentData n K G ℓ d)
    [Module.Finite K ↥(chartPiece n K G ℓ (d + 1))]
    [Module.Finite K ↥(chartPiece n K G ℓ d)]
    [Module.Finite K ↥(sectionPiece n K G ℓ (d + 1))] :
    Module.finrank K ↥(chartPiece n K G ℓ (d + 1))
      = Module.finrank K ↥(chartPiece n K G ℓ d)
        + Module.finrank K ↥(sectionPiece n K G ℓ (d + 1)) := by
  -- `K/V/V₂` pinned explicitly so no metavariable-driven TC search runs
  -- through the heavy terms; `f` then unifies as a term. Applying the lemma
  -- directly would force its `DivisionRing`-path scalar instances onto the
  -- `Field`-built `gradeMap`.
  have hRN : Module.finrank K ↥(LinearMap.range (gradeMap n K G ℓ d hreg))
      + Module.finrank K ↥(LinearMap.ker (gradeMap n K G ℓ d hreg))
      = Module.finrank K ↥(chartPiece n K G ℓ (d + 1)) :=
    LinearMap.finrank_range_add_finrank_ker (K := K)
      (V := ↥(chartPiece n K G ℓ (d + 1)))
      (V₂ := ↥(sectionPiece n K G ℓ (d + 1))) _
  rw [gradeMap_range_finrank n K G ℓ d hreg,
    gradeMap_ker_finrank n K G ℓ d hreg hdesc] at hRN
  omega

/-! ## Summation interface -/

/-- Telescope: `finrank G_D` is `finrank G_0` plus the sum of the section-piece
dimensions — one `chart_step_finrank` per degree (rank-nullity on the grade
map, no submodule quotients).

## References

* `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean` (via
  `Finset.sum_range_succ`). -/
theorem chart_finrank_telescope (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (D : ℕ)
    (hfin : ∀ d, Module.Finite K ↥(chartPiece n K G ℓ d))
    (hfinS : ∀ d, Module.Finite K ↥(sectionPiece n K G ℓ d))
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    (hdesc : ∀ d, d < D → DescentData n K G ℓ d) :
    Module.finrank K ↥(chartPiece n K G ℓ D)
      = Module.finrank K ↥(chartPiece n K G ℓ 0)
        + ∑ d ∈ Finset.range D, Module.finrank K ↥(sectionPiece n K G ℓ (d + 1)) := by
  revert hdesc
  induction D with
  | zero => intro; simp
  | succ D ih =>
    intro hdesc
    have := hfin (D + 1)
    have := hfin D
    have := hfinS (D + 1)
    have ih' := ih (fun d hd => hdesc d (lt_of_lt_of_le hd (Nat.le_succ D)))
    have hstep :=
      chart_step_finrank n K G ℓ D hreg (hdesc D (Nat.lt_succ_self D))
    rw [Finset.sum_range_succ]
    omega

/-- Summation handoff (chart bridge): at stabilization
`G_D = A`, the chart length is `finrank G_0` plus the sum of the section-piece
dimensions. This is the exact shape `Counting.sum_mult_eq_chart_length`
consumes (with `chartPiece_zero_finrank` discharging the `G_0` term).

## References

* `Mathlib/Algebra/Module/Submodule/Lattice.lean`, `Submodule.topEquiv`.
* `Mathlib/LinearAlgebra/Dimension/Finrank.lean`, `LinearEquiv.finrank_eq`. -/
theorem chart_finrank_eq_sum_pieces (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (D : ℕ)
    (hfin : ∀ d, Module.Finite K ↥(chartPiece n K G ℓ d))
    (hfinS : ∀ d, Module.Finite K ↥(sectionPiece n K G ℓ d))
    (hstab : chartPiece n K G ℓ D = ⊤)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    (hdesc : ∀ d, d < D → DescentData n K G ℓ d) :
    Module.finrank K (chartRing n K G ℓ)
      = Module.finrank K ↥(chartPiece n K G ℓ 0)
        + ∑ d ∈ Finset.range D,
          Module.finrank K ↥(sectionPiece n K G ℓ (d + 1)) := by
  have := hfin D
  have htop : ↥(chartPiece n K G ℓ D) ≃ₗ[K] chartRing n K G ℓ := by
    rw [hstab]
    exact Submodule.topEquiv
  have fsurj : Function.Surjective (htop.toLinearMap) := htop.surjective
  have hfinA : Module.Finite K (chartRing n K G ℓ) :=
    FiniteDimensional.of_surjective (V := ↥(chartPiece n K G ℓ D))
      (V₂ := chartRing n K G ℓ) htop.toLinearMap fsurj
  have := hfinA
  rw [← LinearEquiv.finrank_eq htop,
    chart_finrank_telescope n K G ℓ D hfin hfinS hreg hdesc]

/-! ## Stabilization -/

/-- Filtration stabilization (`hstab`) from chart finiteness: the piece
finranks form a monotone `ℕ`-sequence bounded by `finrank K A`, hence
stabilize (a non-stabilizing sequence would exceed any bound); exhaustion
plus equal-finrank identification (`Submodule.eq_of_le_of_finrank_eq`) then
forces the stabilizing piece to be `⊤`. Piece finiteness is
`chartPiece_finite` (unconditional), so chart finiteness is the only input.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ChartFiltration`,
  `Appendix_FixedPoint.BezoutChain.chartPiece_mono`,
  `Appendix_FixedPoint.BezoutChain.chart_filtration_exhaust`,
  `Appendix_FixedPoint.BezoutChain.chartPiece_finite` (this module).
* `Mathlib/LinearAlgebra/Dimension/Constructions.lean`,
  `Submodule.finrank_le`.
* `Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`,
  `Submodule.eq_of_le_of_finrank_eq`.
* `Mathlib/Algebra/Module/Submodule/Map.lean`,
  `Submodule.comapSubtypeEquivOfLe`.
* `Mathlib/LinearAlgebra/Dimension/Finrank.lean`, `LinearEquiv.finrank_eq`.
* `Mathlib/Order/Monotone/Basic.lean`, `monotone_nat_of_le_succ`. -/
theorem chartPiece_stabilizes_of_finite (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    [Module.Finite K (chartRing n K G ℓ)] :
    ∃ D, chartPiece n K G ℓ D = ⊤ := by
  have : ∀ d, Module.Finite K ↥(chartPiece n K G ℓ d) :=
    fun d => chartPiece_finite n K G ℓ d
  have hmono : Monotone (fun d => Module.finrank K ↥(chartPiece n K G ℓ d)) := by
    apply monotone_nat_of_le_succ
    intro d
    change Module.finrank K ↥(chartPiece n K G ℓ d)
      ≤ Module.finrank K ↥(chartPiece n K G ℓ (d + 1))
    have hle : chartPiece n K G ℓ d ≤ chartPiece n K G ℓ (d + 1) :=
      chartPiece_mono n K G ℓ (Nat.le_succ d)
    rw [← LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hle)]
    exact Submodule.finrank_le _
  have hbound : ∀ d, Module.finrank K ↥(chartPiece n K G ℓ d)
      ≤ Module.finrank K (chartRing n K G ℓ) := by
    intro d
    exact Submodule.finrank_le (chartPiece n K G ℓ d)
  have hstab : ∃ D, ∀ e, D ≤ e →
      Module.finrank K ↥(chartPiece n K G ℓ e)
        = Module.finrank K ↥(chartPiece n K G ℓ D) := by
    by_contra hcon
    have hgt : ∀ D, ∃ e, D < e ∧
        Module.finrank K ↥(chartPiece n K G ℓ D)
          < Module.finrank K ↥(chartPiece n K G ℓ e) := by
      intro D
      by_contra hD
      apply hcon
      refine ⟨D, fun e hDe => ?_⟩
      by_contra hne
      apply hD
      refine ⟨e, ?_, ?_⟩
      · rcases eq_or_lt_of_le hDe with rfl | h
        · exact absurd rfl hne
        · exact h
      · exact lt_of_le_of_ne (hmono hDe) (fun h => hne h.symm)
    choose nxt hnxt using hgt
    have hiter : ∀ k, ∃ e,
        Module.finrank K ↥(chartPiece n K G ℓ 0) + k
          ≤ Module.finrank K ↥(chartPiece n K G ℓ e) := by
      intro k
      induction k with
      | zero => exact ⟨0, le_rfl⟩
      | succ k ih =>
        obtain ⟨e, he⟩ := ih
        exact ⟨nxt e, by have h2 := (hnxt e).2; omega⟩
    obtain ⟨e, he⟩ := hiter (Module.finrank K (chartRing n K G ℓ) + 1)
    have hle := hbound e
    omega
  obtain ⟨D, hD⟩ := hstab
  refine ⟨D, le_antisymm le_top ?_⟩
  intro x _
  have hex : x ∈ ⋃ d, (chartPiece n K G ℓ d : Set (chartRing n K G ℓ)) := by
    rw [chart_filtration_exhaust n K G ℓ]
    exact Set.mem_univ x
  obtain ⟨d, hd⟩ := Set.mem_iUnion.mp hex
  have hDd : D ≤ max D d := Nat.le_max_left D d
  have hdd : d ≤ max D d := Nat.le_max_right D d
  have hle : chartPiece n K G ℓ D ≤ chartPiece n K G ℓ (max D d) :=
    chartPiece_mono n K G ℓ hDd
  have heq : chartPiece n K G ℓ D = chartPiece n K G ℓ (max D d) :=
    Submodule.eq_of_le_of_finrank_eq hle (hD (max D d) hDd).symm
  rw [heq]
  exact chartPiece_mono n K G ℓ hdd hd

/-- The low-degree homogeneous pieces map jointly to the chart: sum the
`chartPieceMk` images over `d ∈ Fin (B + 1)`. This is the finite source
whose surjectivity (via degree reduction,
`chart_finite_of_sectionPiece_vanishing`) makes the chart finite.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ChartFiltration`,
  `Appendix_FixedPoint.BezoutChain.chartPieceMk`
  (this module).
* `Mathlib/LinearAlgebra/Pi.lean`, `LinearMap.proj`. -/
noncomputable def chartSumMk (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (B : ℕ) :
    (Π d : Fin (B + 1),
        ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 2)) K d.val))
      →ₗ[K] chartRing n K G ℓ :=
  ∑ d : Fin (B + 1), ((chartPiece n K G ℓ d.val).subtype ∘ₗ
    chartPieceMk n K G ℓ d.val ∘ₗ LinearMap.proj d)

/-- Computation rule for `chartSumMk` (unfold the sum of linear maps).

## References

* `Mathlib/Algebra/Module/Submodule/LinearMap.lean`, `LinearMap.sum_apply`.
* `Mathlib/Algebra/Module/LinearMap/Defs.lean`, `LinearMap.comp_apply`.
* `Mathlib/LinearAlgebra/Pi.lean`, `LinearMap.proj_apply`. -/
theorem chartSumMk_apply (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (B : ℕ)
    (u : Π d : Fin (B + 1),
      ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 2)) K d.val)) :
    chartSumMk n K G ℓ B u
      = ∑ d : Fin (B + 1), (chartPiece n K G ℓ d.val).subtype
        (chartPieceMk n K G ℓ d.val (u d)) := by
  simp only [chartSumMk, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply]

set_option maxHeartbeats 1000000 in
-- Raised budget: the chart-finiteness reduction over the sum of pieces is slow.
/-- Chart finiteness from section-piece vanishing: if every section piece
above `B` has finrank `0` (the `hvan` shape, matching `Fsec` by `rfl` for
the downstream instantiation), every chart element reduces to degree `≤ B`
(one step: the section class of a high-degree lift vanishes, so the lift is
`ℓ`-divisible with the cofactor descending a degree by
`descentData_of_quadrics`), hence the chart is a linear quotient of the
finite product of low-degree homogeneous pieces (`chartSumMk`). The ambient
section-finiteness instance is discharged downstream by
`section_finite_of_artinian` (from `hreg` + `hZd`).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ChartFiltration`,
  `Appendix_FixedPoint.BezoutChain.chartSumMk`, `Appendix_FixedPoint.BezoutChain.chartSumMk_apply`,
  `Appendix_FixedPoint.BezoutChain.chartPieceMk_surjective`,
  `Appendix_FixedPoint.BezoutChain.descentData_of_quadrics`,
  `Appendix_FixedPoint.BezoutChain.descent_cofactor_eq`,
  `Appendix_FixedPoint.BezoutChain.mk_mul_ℓbar`,
  `Appendix_FixedPoint.BezoutChain.mem_chartPiece_of_lift`,
  `Appendix_FixedPoint.BezoutChain.chart_filtration_exhaust` (this module).
* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.homogeneousSubmodule_fg`.
* `Mathlib/RingTheory/Finiteness/Basic.lean`, `Module.Finite.of_fg`,
  `Module.Finite.pi`.
* `Mathlib/LinearAlgebra/Dimension/Finite.lean`,
  `Module.finrank_eq_zero_iff`.
* `Mathlib/Algebra/GroupWithZero/Action/Units.lean`, `inv_smul_smul₀`.
* `Mathlib/RingTheory/Ideal/Quotient/Defs.lean`,
  `Ideal.Quotient.eq_zero_iff_mem`.
* `Mathlib/RingTheory/Ideal/Span.lean`, `Ideal.mem_span_singleton'`.
* `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`,
  `Finset.sum_eq_single`.
* `Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean`,
  `FiniteDimensional.of_surjective`. -/
theorem chart_finite_of_sectionPiece_vanishing (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (B : ℕ)
    (hG : ∀ i, (G i).IsHomogeneous 2)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    [Module.Finite K (sectionQuotient n K G ℓ)]
    (hvan : ∀ d, B < d → Module.finrank K ↥(sectionPiece n K G ℓ d) = 0) :
    Module.Finite K (chartRing n K G ℓ) := by
  have : ∀ d, Module.Finite K ↥(sectionPiece n K G ℓ d) :=
    fun d => sectionPiece_finite_of_finite n K G ℓ d
  have : ∀ d : Fin (B + 1), Module.Finite K
      ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 2)) K d.val) :=
    fun d => Module.Finite.of_fg
      (MvPolynomial.homogeneousSubmodule_fg (Fin (n + 2)) K d.val)
  have hdesc : ∀ d, DescentData n K G ℓ d :=
    fun d => descentData_of_quadrics n K G ℓ hG hreg d
  have hred : ∀ (fuel d : ℕ), d ≤ B + fuel → ∀ x : chartRing n K G ℓ,
      x ∈ chartPiece n K G ℓ d →
      ∃ d', d' ≤ B ∧ x ∈ chartPiece n K G ℓ d' := by
    intro fuel
    induction fuel with
    | zero =>
      intro d hd x hx
      exact ⟨d, by omega, hx⟩
    | succ fuel ih =>
      intro d hd x hx
      by_cases hdB : d ≤ B
      · exact ⟨d, hdB, hx⟩
      · have hdB' : B < d := Nat.lt_of_not_ge hdB
        have hd1 : 1 ≤ d := by omega
        have hdsub : d - 1 + 1 = d := by omega
        obtain ⟨p, hp, ep⟩ := hx
        have hclass : Ideal.Quotient.mk (Ideal.span
              ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
                Set (coneQuotient n K G)))
            (Ideal.Quotient.mk (Ideal.span (Set.range G)) p) = 0 := by
          have hmem : Ideal.Quotient.mk (Ideal.span
                ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
                  Set (coneQuotient n K G)))
              (Ideal.Quotient.mk (Ideal.span (Set.range G)) p)
              ∈ sectionPiece n K G ℓ d := ⟨p, hp, rfl⟩
          obtain ⟨a, ha, hax⟩ := Module.finrank_eq_zero_iff.mp (hvan d hdB')
            ⟨_, hmem⟩
          have hax' : a • Ideal.Quotient.mk (Ideal.span
                ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
                  Set (coneQuotient n K G)))
              (Ideal.Quotient.mk (Ideal.span (Set.range G)) p) = 0 :=
            congrArg Subtype.val hax
          have e := congrArg (a⁻¹ • ·) hax'
          rw [inv_smul_smul₀ ha, smul_zero] at e
          exact e
        rw [Ideal.Quotient.eq_zero_iff_mem] at hclass
        obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hclass
        have hp' : p.IsHomogeneous (d - 1 + 1) := hdsub ▸ hp
        obtain ⟨q, hq, hqeq⟩ := hdesc (d - 1) p t hp' ht.symm
        have e2 : Ideal.Quotient.mk (Ideal.span (Set.range G)) p
            = Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ * q) :=
          descent_cofactor_eq n K G ℓ p t ht q hqeq
        have efinal : x.val
            = Localization.mk (Ideal.Quotient.mk (Ideal.span (Set.range G)) q)
              (denom n K G ℓ (d - 1)) := by
          rw [ep, e2]
          have hmul := mk_mul_ℓbar n K G ℓ q (d - 1)
          rw [hdsub] at hmul
          exact hmul.symm
        have hxd : x ∈ chartPiece n K G ℓ (d - 1) :=
          mem_chartPiece_of_lift n K G ℓ x (d - 1) q hq efinal
        exact ih (d - 1) (by omega) x hxd
  have hsurj : Function.Surjective (chartSumMk n K G ℓ B) := by
    intro x
    have hex : x ∈ ⋃ d, (chartPiece n K G ℓ d : Set (chartRing n K G ℓ)) := by
      rw [chart_filtration_exhaust n K G ℓ]
      exact Set.mem_univ x
    obtain ⟨d, hd⟩ := Set.mem_iUnion.mp hex
    obtain ⟨d', hd'B, hx'⟩ := hred d d (Nat.le_add_left d B) x hd
    obtain ⟨w, hw⟩ := chartPieceMk_surjective n K G ℓ d' ⟨x, hx'⟩
    have ha : d' < B + 1 := by omega
    refine ⟨(Function.update (0 : Π d : Fin (B + 1),
      ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 2)) K d.val)) ⟨d', ha⟩ w :
      Π d : Fin (B + 1),
        ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 2)) K d.val)), ?_⟩
    rw [chartSumMk_apply]
    rw [Finset.sum_eq_single (⟨d', ha⟩ : Fin (B + 1))]
    · have hsame : Function.update (0 : Π d : Fin (B + 1),
            ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 2)) K d.val))
            ⟨d', ha⟩ w ⟨d', ha⟩ = w :=
          Function.update_self _ _ _
      rw [hsame, hw]
      rfl
    · intro j _ hja
      have h0 : Function.update (0 : Π d : Fin (B + 1),
            ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 2)) K d.val))
            ⟨d', ha⟩ w j = 0 := Function.update_of_ne hja _ _
      rw [h0, map_zero]
      rfl
    · intro ha'
      exact absurd (Finset.mem_univ _) ha'
  exact FiniteDimensional.of_surjective
    (V := Π d : Fin (B + 1),
      ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 2)) K d.val))
    (V₂ := chartRing n K G ℓ) (chartSumMk n K G ℓ B) hsurj

/-! ## The degree-zero piece -/

/-- The equations vanish at `0` when they are quadrics (discharges the `hG0`
hypothesis from Statement's own `hG`): evaluation at `0` is the constant
coefficient (`MvPolynomial.eval_zero`), which is the `0`-monomial coefficient
(`MvPolynomial.constantCoeff_eq`), and that coefficient vanishes in positive
homogeneous degree (`MvPolynomial.IsHomogeneous.coeff_eq_zero`).

## References

* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.eval_zero`.
* `Mathlib/Algebra/MvPolynomial/Basic.lean`, `MvPolynomial.constantCoeff_eq`.
* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.IsHomogeneous.coeff_eq_zero`. -/
theorem hG0_of_quadrics (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hG : ∀ i, (G i).IsHomogeneous 2) :
    ∀ i, MvPolynomial.eval (0 : Fin (n + 2) → K) (G i) = 0 := by
  intro i
  have h1 : MvPolynomial.eval (0 : Fin (n + 2) → K) (G i)
      = MvPolynomial.constantCoeff (G i) :=
    congrFun (congrArg DFunLike.coe MvPolynomial.eval_zero) (G i)
  rw [h1, MvPolynomial.constantCoeff_eq]
  exact MvPolynomial.IsHomogeneous.coeff_eq_zero (hG i) (by
    have hdeg : (0 : Fin (n + 2) →₀ ℕ).degree = 0 := by simp [Finsupp.degree]
    omega)

/-- Evaluation at `0` descends to the cone when every equation vanishes at `0`
(immediate from homogeneity; cf. `ResultantLemmas`' `heval0`).

## References

* `Mathlib/RingTheory/Ideal/Quotient/Defs.lean`, `Ideal.Quotient.lift`,
  `Ideal.Quotient.lift_mk` (an `rfl`-lemma).
* `Mathlib/RingTheory/Ideal/Span.lean`, `Ideal.span_le`.
* `Mathlib/Algebra/MvPolynomial/Eval.lean` (`MvPolynomial.eval` ring hom). -/
noncomputable def evalAtZero (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hG0 : ∀ i, MvPolynomial.eval (0 : Fin (n + 2) → K) (G i) = 0) :
    coneQuotient n K G →+* K :=
  Ideal.Quotient.lift _ (MvPolynomial.eval 0) (fun a ha => by
    have hsub : Ideal.span (Set.range G)
        ≤ RingHom.ker (MvPolynomial.eval (0 : Fin (n + 2) → K) : MvPolynomial _ _ →+* K) := by
      rw [Ideal.span_le]
      intro x hx
      obtain ⟨i, rfl⟩ := hx
      exact RingHom.mem_ker.mpr (hG0 i)
    exact RingHom.mem_ker.mp (hsub ha))

/-- Evaluation at `0` reads off the constant coefficient (used by `zeroMap`
linearity, surjectivity, and injectivity, so it is factored out once).

## References

* `Mathlib/RingTheory/Ideal/Quotient/Defs.lean`, `Ideal.Quotient.lift_mk`
  (used via definitional unfolding in `show`).
* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.eval_C`. -/
theorem evalAtZero_mk_C (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hG0 : ∀ i, MvPolynomial.eval (0 : Fin (n + 2) → K) (G i) = 0) (c : K) :
    evalAtZero n K G hG0
        (Ideal.Quotient.mk (Ideal.span (Set.range G)) (MvPolynomial.C c)) = c := by
  change MvPolynomial.eval (0 : Fin (n + 2) → K) (MvPolynomial.C c) = c
  rw [MvPolynomial.eval_C]

/-- The degree-`0` piece maps to `K` by evaluating a (constant) lift at `0`;
well-definedness is denominator cancellation (`mk_cancel_of_mk_eq`).

## References

* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.eval_C`. -/
noncomputable def zeroMap (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hG0 : ∀ i, MvPolynomial.eval (0 : Fin (n + 2) → K) (G i) = 0)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ))) :
    ↥(chartPiece n K G ℓ 0) →ₗ[K] K where
  toFun x := evalAtZero n K G hG0
    (Ideal.Quotient.mk (Ideal.span (Set.range G)) (chartLift n K G ℓ 0 x))
  map_add' x y := by
    have hadd : ((↑(x + y) : ↥(chartPiece n K G ℓ 0)) : chartRing n K G ℓ).val
        = Localization.mk (Ideal.Quotient.mk (Ideal.span (Set.range G))
            (chartLift n K G ℓ 0 x + chartLift n K G ℓ 0 y))
          (denom n K G ℓ 0) := by
      have ecalc : (↑x : chartRing n K G ℓ).val + (↑y : chartRing n K G ℓ).val
          = Localization.mk (Ideal.Quotient.mk (Ideal.span (Set.range G))
              (chartLift n K G ℓ 0 x + chartLift n K G ℓ 0 y))
            (denom n K G ℓ 0) := by
        rw [chartLift_eq n K G ℓ 0 x, chartLift_eq n K G ℓ 0 y,
          Localization.add_mk_self, ← map_add]
      exact ecalc
    have hcancel := mk_cancel_of_mk_eq n K G ℓ hreg _ _ 0
      ((chartLift_eq n K G ℓ 0 (x + y)).symm.trans hadd)
    change evalAtZero n K G hG0 (Ideal.Quotient.mk (Ideal.span (Set.range G))
        (chartLift n K G ℓ 0 (x + y)))
      = evalAtZero n K G hG0 (Ideal.Quotient.mk (Ideal.span (Set.range G))
        (chartLift n K G ℓ 0 x))
        + evalAtZero n K G hG0 (Ideal.Quotient.mk (Ideal.span (Set.range G))
        (chartLift n K G ℓ 0 y))
    rw [hcancel, map_add, map_add]
  map_smul' c x := by
    have hhom' : (MvPolynomial.C c * chartLift n K G ℓ 0 x).IsHomogeneous 0 :=
      (MvPolynomial.isHomogeneous_C _ c).mul (chartLift_hom n K G ℓ 0 x)
    have hsmul : ((↑(c • x) : ↥(chartPiece n K G ℓ 0)) : chartRing n K G ℓ).val
        = Localization.mk (Ideal.Quotient.mk (Ideal.span (Set.range G))
            (MvPolynomial.C c * chartLift n K G ℓ 0 x))
          (denom n K G ℓ 0) := by
      have ecalc : c • (↑x : chartRing n K G ℓ).val
          = Localization.mk (Ideal.Quotient.mk (Ideal.span (Set.range G))
              (MvPolynomial.C c * chartLift n K G ℓ 0 x))
            (denom n K G ℓ 0) := by
        have esmul : c • Localization.mk
            (Ideal.Quotient.mk (Ideal.span (Set.range G))
              (chartLift n K G ℓ 0 x)) (denom n K G ℓ 0)
            = Localization.mk
              (c • Ideal.Quotient.mk (Ideal.span (Set.range G))
                (chartLift n K G ℓ 0 x)) (denom n K G ℓ 0) :=
          Localization.smul_mk (R := K) _ _ _
        have esmul2 : c • Ideal.Quotient.mk (Ideal.span (Set.range G))
              (chartLift n K G ℓ 0 x)
            = algebraMap K (coneQuotient n K G) c
              * Ideal.Quotient.mk (Ideal.span (Set.range G))
                (chartLift n K G ℓ 0 x) :=
          Algebra.smul_def (A := coneQuotient n K G) c _
        have hmap : Ideal.Quotient.mk (Ideal.span (Set.range G))
            (MvPolynomial.C c) = algebraMap K (coneQuotient n K G) c := by
          have hC : (MvPolynomial.C c : MvPolynomial (Fin (n + 2)) K)
              = algebraMap K (MvPolynomial (Fin (n + 2)) K) c := by
            rw [MvPolynomial.algebraMap_eq]
          rw [hC]
          exact Ideal.Quotient.mk_algebraMap K _ _
        rw [chartLift_eq n K G ℓ 0 x, esmul, esmul2, ← hmap, ← map_mul]
      exact ecalc
    have hcancel := mk_cancel_of_mk_eq n K G ℓ hreg _ _ 0
      ((chartLift_eq n K G ℓ 0 (c • x)).symm.trans hsmul)
    have eC : evalAtZero n K G hG0
        (Ideal.Quotient.mk (Ideal.span (Set.range G)) (MvPolynomial.C c)) = c :=
      evalAtZero_mk_C n K G hG0 c
    change evalAtZero n K G hG0 (Ideal.Quotient.mk (Ideal.span (Set.range G))
        (chartLift n K G ℓ 0 (c • x)))
      = (RingHom.id K) c • evalAtZero n K G hG0
        (Ideal.Quotient.mk (Ideal.span (Set.range G))
        (chartLift n K G ℓ 0 x))
    rw [hcancel, map_mul, map_mul, eC, smul_eq_mul, RingHom.id_apply]

/-- The constant chart element (the `zeroMap` surjectivity witness, factored
out so the large membership term is elaborated once).

## References

* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.isHomogeneous_C`. -/
noncomputable def constChartWit (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (c : K) : ↥(chartPiece n K G ℓ 0) :=
  ⟨⟨Localization.mk
    (Ideal.Quotient.mk (Ideal.span (Set.range G)) (MvPolynomial.C c))
    (denom n K G ℓ 0),
    0, Ideal.Quotient.mk (Ideal.span (Set.range G)) (MvPolynomial.C c),
    ⟨MvPolynomial.C c, MvPolynomial.isHomogeneous_C _ c, rfl⟩, rfl⟩,
    MvPolynomial.C c, MvPolynomial.isHomogeneous_C _ c, rfl⟩

/-- The constant chart element carries the constant lift over `ℓ̄ ^ 0`. -/
theorem constChartWit_val (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (c : K) :
    (constChartWit n K G ℓ c : chartRing n K G ℓ).val
      = Localization.mk
        (Ideal.Quotient.mk (Ideal.span (Set.range G)) (MvPolynomial.C c))
        (denom n K G ℓ 0) := rfl

/-- `zeroMap` is injective: a degree-`0` fraction evaluating to `0` at `0` has
vanishing constant coefficient, hence is `0`.

## References

* `Mathlib/Algebra/MvPolynomial/Degrees.lean`,
  `MvPolynomial.totalDegree_eq_zero_iff_eq_C`.
* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.totalDegree_zero_iff_isHomogeneous`.
* `Mathlib/Algebra/MvPolynomial/Basic.lean`, `MvPolynomial.C_0`.
* `Mathlib/Algebra/Module/Submodule/Lattice.lean`,
  `Submodule.eq_bot_iff` (protected), `Submodule.mem_bot`. -/
theorem zeroMap_ker_eq_bot (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hG0 : ∀ i, MvPolynomial.eval (0 : Fin (n + 2) → K) (G i) = 0)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ))) :
    LinearMap.ker (zeroMap n K G ℓ hG0 hreg) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro w hw
  rw [LinearMap.mem_ker] at hw
  have hp : (chartLift n K G ℓ 0 w).IsHomogeneous 0 :=
    chartLift_hom n K G ℓ 0 w
  have htd : (chartLift n K G ℓ 0 w).totalDegree = 0 :=
    Iff.mpr (MvPolynomial.totalDegree_zero_iff_isHomogeneous _) hp
  have hC : chartLift n K G ℓ 0 w
      = MvPolynomial.C ((chartLift n K G ℓ 0 w).coeff 0) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp htd
  have hw2 : evalAtZero n K G hG0 (Ideal.Quotient.mk (Ideal.span (Set.range G))
      (chartLift n K G ℓ 0 w)) = 0 := hw
  have hc : (chartLift n K G ℓ 0 w).coeff 0 = 0 := by
    have e : evalAtZero n K G hG0 (Ideal.Quotient.mk (Ideal.span (Set.range G))
        (chartLift n K G ℓ 0 w))
        = (chartLift n K G ℓ 0 w).coeff 0 := by
      conv_lhs => rw [hC]
      exact evalAtZero_mk_C n K G hG0 _
    rw [e] at hw2
    exact hw2
  have hp0 : chartLift n K G ℓ 0 w = 0 := by
    rw [hC, hc, MvPolynomial.C_0]
  have hval : (↑w : chartRing n K G ℓ).val = 0 := by
    rw [chartLift_eq n K G ℓ 0 w, hp0, map_zero, Localization.mk_zero]
  have hchart : (↑w : chartRing n K G ℓ) = 0 := Subtype.ext hval
  exact Subtype.ext hchart

/-- `zeroMap` is surjective: every constant is the evaluation of the constant
chart element. -/
theorem zeroMap_surjective (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hG0 : ∀ i, MvPolynomial.eval (0 : Fin (n + 2) → K) (G i) = 0)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ))) :
    Function.Surjective (zeroMap n K G ℓ hG0 hreg) := by
  intro c
  refine ⟨constChartWit n K G ℓ c, ?_⟩
  have hcancel : Ideal.Quotient.mk (Ideal.span (Set.range G))
        (chartLift n K G ℓ 0 (constChartWit n K G ℓ c))
      = Ideal.Quotient.mk (Ideal.span (Set.range G)) (MvPolynomial.C c) :=
    mk_cancel_of_mk_eq n K G ℓ hreg _ _ 0
      ((chartLift_eq n K G ℓ 0 _).symm.trans (constChartWit_val n K G ℓ c))
  have hcomp := congrArg (evalAtZero n K G hG0) hcancel
  rw [evalAtZero_mk_C] at hcomp
  exact hcomp

set_option maxHeartbeats 2000000 in
-- Raised budget: injectivity via the kernel lemma unifies large localization types.
/-- `zeroMap` is injective (via `zeroMap_ker_eq_bot`). -/
theorem zeroMap_injective (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hG0 : ∀ i, MvPolynomial.eval (0 : Fin (n + 2) → K) (G i) = 0)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ))) :
    Function.Injective (zeroMap n K G ℓ hG0 hreg) := by
  intro w1 w2 h
  have e : zeroMap n K G ℓ hG0 hreg (w1 - w2)
      = zeroMap n K G ℓ hG0 hreg w1 - zeroMap n K G ℓ hG0 hreg w2 :=
    map_sub (zeroMap n K G ℓ hG0 hreg) w1 w2
  rw [h, sub_self] at e
  have hmem : w1 - w2 ∈ LinearMap.ker (zeroMap n K G ℓ hG0 hreg) :=
    LinearMap.mem_ker.mpr e
  have h0 : w1 - w2 = 0 :=
    (Submodule.eq_bot_iff _).mp (zeroMap_ker_eq_bot n K G ℓ hG0 hreg) _ hmem
  exact sub_eq_zero.mp h0

/-- `G_0 ≃ₗ[K] K`: a degree-`0` fraction is a constant, and evaluation at `0`
is an isomorphism (kernel: a homogeneous degree-`0` polynomial is `C` of its
constant coefficient, which the evaluation reads off).

## References

* `Mathlib/Algebra/MvPolynomial/Degrees.lean`,
  `MvPolynomial.totalDegree_eq_zero_iff_eq_C`.
* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.totalDegree_zero_iff_isHomogeneous`.
* `Mathlib/Algebra/MvPolynomial/Basic.lean`, `MvPolynomial.C_0`.
* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.eval_C`.
* `Mathlib/Algebra/Module/Submodule/Equiv.lean`,
  `LinearEquiv.ofBijective`.
* `Mathlib/Algebra/Module/Submodule/Lattice.lean`,
  `Submodule.eq_bot_iff` (protected), `Submodule.mem_bot`. -/
noncomputable def chartPiece_zero_equiv (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hG0 : ∀ i, MvPolynomial.eval (0 : Fin (n + 2) → K) (G i) = 0)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ))) :
    ↥(chartPiece n K G ℓ 0) ≃ₗ[K] K :=
  LinearEquiv.ofBijective (zeroMap n K G ℓ hG0 hreg)
    ⟨zeroMap_injective n K G ℓ hG0 hreg, zeroMap_surjective n K G ℓ hG0 hreg⟩

/-- The `G_0` term of the handoff sum is `1` (discharged in Counting
alongside `chart_finrank_eq_sum_pieces`).

## References

* `Mathlib/LinearAlgebra/Dimension/Finrank.lean`, `LinearEquiv.finrank_eq`.
* `Mathlib/LinearAlgebra/Dimension/StrongRankCondition.lean`,
  `Module.finrank_self`. -/
theorem chartPiece_zero_finrank (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hG0 : ∀ i, MvPolynomial.eval (0 : Fin (n + 2) → K) (G i) = 0)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ))) :
    Module.finrank K ↥(chartPiece n K G ℓ 0) = 1 :=
  (LinearEquiv.finrank_eq (chartPiece_zero_equiv n K G ℓ hG0 hreg)).trans
    (Module.finrank_self K)

/-! ## Chart residuals for Counting -/

/-- R1 nonvanishing input (`hc`): the chart form misses every locus point.
This is the exact `hc` binder shape `LocalMultiplicity.haddLocal` (and
`LocalMultiplicity.localPointMultiplicity`) take — same statement, named here since
its discharge (R1 avoidance) is ChartFiltration-owned.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Definitions`,
  `Appendix_FixedPoint.BezoutChain.vanishingLocus`,
  `Appendix_FixedPoint.BezoutChain.mkLin`.
* `Mathlib/LinearAlgebra/Projectivization/Basic.lean`, `Projectivization.mk`.
* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.eval`. -/
def ChartNonvanishing (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) : Prop :=
  ∀ (p : Projectivization K (Fin (n + 2) → K)) (_ : p ∈ vanishingLocus n K G)
    (v : Fin (n + 2) → K) (hv : v ≠ 0),
    Projectivization.mk K v hv = p → MvPolynomial.eval v (mkLin n K ℓ) ≠ 0

/-- Nonvanishing at the canonical representative: `hc` evaluated at `p.rep`
(the single-point `hℓ` input `LocalMultiplicity.hposLocal` needs).

## References

* `Mathlib/LinearAlgebra/Projectivization/Basic.lean`,
  `Projectivization.rep`, `Projectivization.rep_nonzero`,
  `Projectivization.mk_rep`. -/
theorem chartNonvanishing_at (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hc : ChartNonvanishing n K G ℓ)
    (p : Projectivization K (Fin (n + 2) → K))
    (hp : p ∈ vanishingLocus n K G) :
    MvPolynomial.eval p.rep (mkLin n K ℓ) ≠ 0 :=
  hc p hp p.rep p.rep_nonzero (Projectivization.mk_rep p)

/-- Chart finiteness (`hfinA`): stabilization plus piece-finiteness makes the
chart finite over `K` (the `hfinA` input `LocalMultiplicity.hposLocal` needs). This is
the finiteness half of `chart_finrank_eq_sum_pieces`, factored out so the
Counting can consume it without the rank identity.

## References

* `Mathlib/Algebra/Module/Submodule/Lattice.lean`, `Submodule.topEquiv`.
* `Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean`,
  `FiniteDimensional.of_surjective` (same assembly as in
  `chart_finrank_eq_sum_pieces`). -/
theorem chart_finite_of_stable (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (D : ℕ)
    (hfin : ∀ d, Module.Finite K ↥(chartPiece n K G ℓ d))
    (hstab : chartPiece n K G ℓ D = ⊤) :
    Module.Finite K (chartRing n K G ℓ) := by
  have := hfin D
  have htop : ↥(chartPiece n K G ℓ D) ≃ₗ[K] chartRing n K G ℓ := by
    rw [hstab]
    exact Submodule.topEquiv
  exact FiniteDimensional.of_surjective (V := ↥(chartPiece n K G ℓ D))
    (V₂ := chartRing n K G ℓ) htop.toLinearMap htop.surjective

/-- Chart positivity via a locus point: from filtration stability plus `hc`, a
locus point makes the chart nontrivial of positive length. This is
`LocalMultiplicity.hposLocal` fed with ChartFiltration-owned inputs throughout
(`v := p.rep`, `hvG` from locus membership, `hℓ` from `hc` via
`chartNonvanishing_at`, `hfinA` from `chart_finite_of_stable`) — the
`Counting.mult_pos_of_mem` `hpos` route.

## References

* This module, `Appendix_FixedPoint.BezoutChain.chart_finite_of_stable`,
  `Appendix_FixedPoint.BezoutChain.chartNonvanishing_at`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.LocalMultiplicity`,
  `Appendix_FixedPoint.BezoutChain.hposLocal`. -/
theorem chart_pos_of_point (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (D : ℕ)
    (hfin : ∀ d, Module.Finite K ↥(chartPiece n K G ℓ d))
    (hstab : chartPiece n K G ℓ D = ⊤)
    (hc : ChartNonvanishing n K G ℓ)
    (p : Projectivization K (Fin (n + 2) → K))
    (hp : p ∈ vanishingLocus n K G) :
    0 < Module.finrank K (chartRing n K G ℓ) :=
  hposLocal n K G ℓ p.rep (hp p.rep p.rep_nonzero (Projectivization.mk_rep p))
    (chartNonvanishing_at n K G ℓ hc p hp)
    (chart_finite_of_stable n K G ℓ D hfin hstab)

/-- Local finiteness input (`hfinLoc`): every local ring over the locus is
finite over `K`. This is the exact `[hfinLoc]` instance-binder shape
`LocalMultiplicity.haddLocal` takes, stated in `LocalMultiplicity`'s vocabulary
(`locLocusFinset` / `locFam`, imported at the top of this module; no cycle
since `LocalMultiplicity` imports only `Statement.Definitions`). The content (Artinian
locals of a finite chart) is the G2 residual proper and stays an explicit
hypothesis.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.LocalMultiplicity`,
  `Appendix_FixedPoint.BezoutChain.locLocusFinset`,
  `Appendix_FixedPoint.BezoutChain.locFam`. -/
def ChartLocFinite (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hfin : (vanishingLocus n K G).Finite)
    (hc : ChartNonvanishing n K G ℓ) : Prop :=
  ∀ p : ↥(locLocusFinset n K G hfin),
    Module.Finite K (locFam n K G ℓ hfin hc p)

/-- Artinian product-of-locals input (`hdecomp`): the chart is the product of
its local rings over the locus. This is the exact `hdecomp` binder shape
`LocalMultiplicity.haddLocal` takes (same import/vocabulary note as `ChartLocFinite`).
It needs the Artinian structure theorem for the chart —
`Mathlib/RingTheory/Artinian/` has finiteness and ACC/DCC API but no
product-of-locals decomposition (cf. `LocalMultiplicity` G2) — plus the
locus↔`MaxSpec` bijection, so it stays an explicit hypothesis: the one
remaining Bézout residual owned here.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.LocalMultiplicity`,
  `Appendix_FixedPoint.BezoutChain.locLocusFinset`,
  `Appendix_FixedPoint.BezoutChain.locFam`.
* `Mathlib/RingTheory/Artinian/` (no product-of-locals API in v4.34.0;
  hence residual). -/
def ChartDecomp (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hfin : (vanishingLocus n K G).Finite)
    (hc : ChartNonvanishing n K G ℓ) : Type _ :=
  chartRing n K G ℓ ≃ₗ[K]
    ((p : ↥(locLocusFinset n K G hfin)) → locFam n K G ℓ hfin hc p)

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
open scoped BigOperators

/-! ## G2 closure: `hfinA`, `hfinLoc`, `hbij`, `hloc` in consumer shapes

This section closes the four ChartFiltration-owned residuals in the exact
shapes the consumers take (`LocalMultiplicity.hposLocal` / `hposLocalAt` /
`multPos_of_mem_of_localFinite` / `haddLocal`, `ArtinianDecomposition.chartDecomp_of`,
`Counting.sum_mult_eq_chart_length` / `mult_pos_of_mem` via those):

* `chartHfinA_of_stable` (`hfinA`): `chart_finite_of_stable` with its
  piece-finiteness input discharged unconditionally by `chartPiece_finite`.
  Conditional on exactly `[hstab]`.
* `chartLocFinite_of_finite` + `chartHfinLoc_at` (`hfinLoc`): finite chart ⟹
  finite locals, via `ArtinianDecomposition.chartLocFinite_of_chartFinite` (§5: the
  `K`-algebra localization map is surjective for the Artinian chart).
  Conditional on exactly `[hfinA]` (fed by `chartHfinA_of_stable`).
* `locusToMaxSpec` (unconditional forward map) + `ChartMaxSpecInj` /
  `ChartMaxSpecSurj` (narrowest exact conditions) + `chartHbij_of_bijective`
  (`hbij`): the locus↔`MaxSpec` bijection in the exact `chartDecomp_of`
  binder shape. Conditional on exactly
  `[ChartMaxSpecInj, ChartMaxSpecSurj]`. The affine feed is the in-tree
  Nullstellensatz (`MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton`,
  `Mathlib/RingTheory/Nullstellensatz.lean`, needs `[IsAlgClosed K]`);
  the open step is the transfer through the section presentation
  (cone → chart localization → degree-`0` part + projectivization).
* `chartHbij_coherence` + `chartLocCongr` + `chartHloc_of_bijective` (`hloc`):
  the AtPrime-to-`locFam` fiber equivs in the exact `chartDecomp_of` binder
  shape, from `pointIdeal` coherence (equal ideals have equal prime
  complements; equal submonoids give equivalent localizations).
  Conditional on exactly `[ChartMaxSpecInj, ChartMaxSpecSurj]` (via
  coherence — no new hypotheses beyond `hbij`'s list).
* `chartDecomp_closed` / `chart_hadd_of_decomp` / `chart_hadd_closed` /
  `chart_hadd_of_stable`: end-to-end G2 assembly — the `hadd` sum equation
  from stabilization plus the two geometric conditions.
  Conditional on exactly `[hstab, ChartMaxSpecInj, ChartMaxSpecSurj]`.
* `chart_multPos_of_mem` / `chart_pos_of_stable`: the `hpos` routes
  (local and global) with all ChartFiltration-side inputs discharged.

Import note: the `ChartFiltration → ArtinianDecomposition` edge is acyclic
(`ArtinianDecomposition` imports only `LocalMultiplicity` plus Mathlib, never this module),
as that module's header anticipates.
-/

/-- Chart finiteness (`hfinA`) from stabilization alone:
`chart_finite_of_stable` with its piece-finiteness input discharged
unconditionally by `chartPiece_finite`. This is the exact `hfinA` binder
`LocalMultiplicity.hposLocal` takes (and the input feeding `chartDecomp_of` /
`chartLocFinite_of_finite` below).

Conditional on exactly `[hstab]` (section-side stabilization is out of
reach here — `chartPiece_stabilizes_of_finite` would need chart finiteness
itself — so `hstab` stays an explicit hypothesis).

## References

* This module, `Appendix_FixedPoint.BezoutChain.chart_finite_of_stable`,
  `Appendix_FixedPoint.BezoutChain.chartPiece_finite`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.LocalMultiplicity`,
  `Appendix_FixedPoint.BezoutChain.hposLocal`
  (consumer). -/
theorem chartHfinA_of_stable (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (D : ℕ)
    (hstab : chartPiece n K G ℓ D = ⊤) :
    Module.Finite K (chartRing n K G ℓ) :=
  chart_finite_of_stable n K G ℓ D (fun d => chartPiece_finite n K G ℓ d) hstab

/-- Local finiteness (`hfinLoc`) from chart finiteness: every local ring over
the locus is finite over `K`. This discharges `ChartLocFinite` — i.e.
`LocalMultiplicity.haddLocal`'s `[hfinLoc]` instance binder — from `hfinA`.

Conditional on exactly `[hfinA]` (fed by `chartHfinA_of_stable`).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Dimension.ArtinianDecomposition`,
  `Appendix_FixedPoint.BezoutChain.chartLocFinite_of_chartFinite` (the §5 feed).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.LocalMultiplicity`,
  `Appendix_FixedPoint.BezoutChain.haddLocal`
  (consumer). -/
theorem chartLocFinite_of_finite (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hfin : (vanishingLocus n K G).Finite)
    (hc : ChartNonvanishing n K G ℓ)
    (hfinA : Module.Finite K (chartRing n K G ℓ)) :
    ChartLocFinite n K G ℓ hfin hc :=
  fun p => chartLocFinite_of_chartFinite n K G ℓ hfin hc hfinA p

/-- Pointwise local finiteness at the canonical representative: the exact
single-point `hfinLoc` input `LocalMultiplicity.hposLocalAt` /
`LocalMultiplicity.multPos_of_mem_of_localFinite` take. From
`ArtinianDecomposition.chartLocFinite_of_chartFinite` at `⟨p, hp⟩` (proof terms
differ from `locFam`'s only up to proof irrelevance).

Conditional on exactly `[hfin, hmem, hfinA]` (`hc` is a definitional
argument of the multiplicity, not a condition).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Dimension.ArtinianDecomposition`,
  `Appendix_FixedPoint.BezoutChain.chartLocFinite_of_chartFinite`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.LocalMultiplicity`,
  `Appendix_FixedPoint.BezoutChain.hposLocalAt`,
  `Appendix_FixedPoint.BezoutChain.multPos_of_mem_of_localFinite` (consumers).
* `Mathlib/Data/Set/Finite/Basic.lean`, `Set.Finite.mem_toFinset`. -/
theorem chartHfinLoc_at (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hfin : (vanishingLocus n K G).Finite)
    (hc : ChartNonvanishing n K G ℓ)
    (hfinA : Module.Finite K (chartRing n K G ℓ))
    (p : Projectivization K (Fin (n + 2) → K))
    (hmem : p ∈ vanishingLocus n K G)
    (hvG : ∀ i, MvPolynomial.eval p.rep (G i) = 0)
    (hℓ : MvPolynomial.eval p.rep (mkLin n K ℓ) ≠ 0) :
    Module.Finite K (locRingAt n K G ℓ p.rep hvG hℓ) :=
  chartLocFinite_of_chartFinite n K G ℓ hfin hc hfinA
    ⟨p, hfin.mem_toFinset.mpr hmem⟩

/-- Consumer-shape local positivity: `Counting.mult_pos_of_mem`'s conclusion
(`1 ≤ localPointMultiplicity`) with all ChartFiltration-side inputs
discharged — `hpos` via `hposLocalAt`, pointwise `hfinLoc` via
`chartHfinLoc_at`.

Conditional on exactly `[hfin, hmem, hfinA]` (`hc` is a definitional
argument of `localPointMultiplicity`, not a condition).

## References

* This module, `Appendix_FixedPoint.BezoutChain.chartHfinLoc_at`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.LocalMultiplicity`,
  `Appendix_FixedPoint.BezoutChain.multPos_of_mem_of_localFinite`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.Counting`,
  `Appendix_FixedPoint.BezoutChain.mult_pos_of_mem`
  (consumer; cited, not imported — import would cycle via
  `Elimination`/`HilbertFunctionCount`). -/
theorem chart_multPos_of_mem (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hfin : (vanishingLocus n K G).Finite)
    (hc : ChartNonvanishing n K G ℓ)
    (p : Projectivization K (Fin (n + 2) → K))
    (hmem : p ∈ vanishingLocus n K G)
    (hfinA : Module.Finite K (chartRing n K G ℓ)) :
    1 ≤ localPointMultiplicity n K G ℓ hc p :=
  multPos_of_mem_of_localFinite n K G ℓ hc p hmem
    (chartHfinLoc_at n K G ℓ hfin hc hfinA p hmem _ _)

/-- The `hadd` sum equation from the decomposition plus chart finiteness:
`LocalMultiplicity.haddLocal` with its `[hfinLoc]` instance fed by
`chartLocFinite_of_finite` and its `hdecomp` binder taken as `ChartDecomp`.

## References

* This module, `Appendix_FixedPoint.BezoutChain.chartLocFinite_of_finite`,
  `Appendix_FixedPoint.BezoutChain.ChartDecomp`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.LocalMultiplicity`,
  `Appendix_FixedPoint.BezoutChain.haddLocal`. -/
theorem chart_hadd_of_decomp (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hfin : (vanishingLocus n K G).Finite)
    (hc : ChartNonvanishing n K G ℓ)
    (hfinA : Module.Finite K (chartRing n K G ℓ))
    (hdecomp : ChartDecomp n K G ℓ hfin hc) :
    ∑ p ∈ locLocusFinset n K G hfin, localPointMultiplicity n K G ℓ hc p
      = Module.finrank K (chartRing n K G ℓ) :=
  @haddLocal n K _ G ℓ hfin hc
    (chartLocFinite_of_finite n K G ℓ hfin hc hfinA) hdecomp

/-- The locus-to-`MaxSpec` forward map (unconditional): send a locus point to
the maximal ideal of chart evaluation at its canonical representative
(`pointIdeal_isMaximal`). The two narrowest exact conditions promoting this
to the `hbij` bijection are `ChartMaxSpecInj` / `ChartMaxSpecSurj` below.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Definitions`,
  `Appendix_FixedPoint.BezoutChain.pointIdeal`,
  `Appendix_FixedPoint.BezoutChain.pointIdeal_isMaximal`.
* `Mathlib/RingTheory/Spectrum/Maximal/Defs.lean`, `MaximalSpectrum`. -/
noncomputable def locusToMaxSpec (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hfin : (vanishingLocus n K G).Finite)
    (hc : ChartNonvanishing n K G ℓ)
    (p : ↥(locLocusFinset n K G hfin)) : MaximalSpectrum (chartRing n K G ℓ) :=
  ⟨pointIdeal n K G ℓ p.val.rep
      (fun i => locMem n K G hfin p p.val.rep p.val.rep_nonzero
        (Projectivization.mk_rep p.val) i)
      (hc p.val ((mem_locLocusFinset n K G hfin p.val).mp p.property) p.val.rep
        p.val.rep_nonzero (Projectivization.mk_rep p.val)),
    pointIdeal_isMaximal n K G ℓ p.val.rep _ _⟩

/-- Narrowest exact condition (surjectivity half of `hbij`): every maximal
ideal of the chart is chart evaluation at some locus point. The affine feed
is the in-tree Nullstellensatz
(`MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton`, needs
`[IsAlgClosed K]`); the open step is the transfer through the section
presentation (cone → chart localization → degree-`0` part, plus
projectivization), so this stays explicit.

GRADE (with `ChartMaxSpecInj`): `hbij` is conditional on exactly
`[ChartMaxSpecInj, ChartMaxSpecSurj]`.

## References

* `Mathlib/RingTheory/Nullstellensatz.lean`,
  `MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton` (affine feed). -/
def ChartMaxSpecSurj (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hfin : (vanishingLocus n K G).Finite)
    (hc : ChartNonvanishing n K G ℓ) : Prop :=
  Function.Surjective (locusToMaxSpec n K G ℓ hfin hc)

/-- Narrowest exact condition (injectivity half of `hbij`): distinct locus
points give distinct chart-evaluation ideals. Same Nullstellensatz feed and
same open section-presentation transfer as `ChartMaxSpecSurj`.

GRADE (with `ChartMaxSpecSurj`): `hbij` is conditional on exactly
`[ChartMaxSpecInj, ChartMaxSpecSurj]`.

## References

* `Mathlib/RingTheory/Nullstellensatz.lean`,
  `MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton` (affine feed). -/
def ChartMaxSpecInj (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hfin : (vanishingLocus n K G).Finite)
    (hc : ChartNonvanishing n K G ℓ) : Prop :=
  Function.Injective (locusToMaxSpec n K G ℓ hfin hc)

/-- The `hbij` locus↔`MaxSpec` bijection in the exact `chartDecomp_of` binder
shape, from the two-item conditional list.

Conditional on exactly `[ChartMaxSpecInj, ChartMaxSpecSurj]`.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Dimension.ArtinianDecomposition`,
  `Appendix_FixedPoint.BezoutChain.chartDecomp_of`
  (consumer of this binder shape).
* `Equiv.ofBijective` (core). -/
noncomputable def chartHbij_of_bijective (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hfin : (vanishingLocus n K G).Finite)
    (hc : ChartNonvanishing n K G ℓ)
    (hinj : ChartMaxSpecInj n K G ℓ hfin hc)
    (hsurj : ChartMaxSpecSurj n K G ℓ hfin hc) :
    MaximalSpectrum (chartRing n K G ℓ) ≃ ↥(locLocusFinset n K G hfin) :=
  (Equiv.ofBijective (locusToMaxSpec n K G ℓ hfin hc) ⟨hinj, hsurj⟩).symm

/-- `pointIdeal` coherence of `hbij` (from the bijection data alone): the
maximal ideal `m` is the evaluation ideal at the representative of the locus
point `hbij` assigns to it. The locus-equation proofs are bound (any proofs
do, by proof irrelevance); feeds `chartHloc_of_bijective`.

## References

* `Equiv.apply_symm_apply` (core). -/
theorem chartHbij_coherence (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hfin : (vanishingLocus n K G).Finite)
    (hc : ChartNonvanishing n K G ℓ)
    (hinj : ChartMaxSpecInj n K G ℓ hfin hc)
    (hsurj : ChartMaxSpecSurj n K G ℓ hfin hc)
    (m : MaximalSpectrum (chartRing n K G ℓ))
    (hvG : ∀ i, MvPolynomial.eval
      ((chartHbij_of_bijective n K G ℓ hfin hc hinj hsurj) m).val.rep (G i) = 0)
    (hℓ : MvPolynomial.eval
      ((chartHbij_of_bijective n K G ℓ hfin hc hinj hsurj) m).val.rep
      (mkLin n K ℓ) ≠ 0) :
    m.asIdeal = pointIdeal n K G ℓ
      ((chartHbij_of_bijective n K G ℓ hfin hc hinj hsurj) m).val.rep hvG hℓ := by
  have h := Equiv.apply_symm_apply
    (Equiv.ofBijective (locusToMaxSpec n K G ℓ hfin hc) ⟨hinj, hsurj⟩) m
  have h2 := congrArg MaximalSpectrum.asIdeal h
  exact h2.symm

/-- Localization congruence from submonoid equality (transport for `hloc`):
equal submonoids give `K`-linearly equivalent localizations. Stated for the
chart so the `K`-module instances resolve from context.

## References

* `Mathlib/Algebra/Module/Equiv/Defs.lean`, `LinearEquiv.refl`. -/
noncomputable def chartLocCongr (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (M N : Submonoid (chartRing n K G ℓ)) (h : M = N) :
    Localization M ≃ₗ[K] Localization N := by
  subst h
  exact LinearEquiv.refl K _

/-- The `hloc` fiber identification in the exact `chartDecomp_of` binder
shape: localization at `m` is `K`-linearly the local ring at the locus point
`hbij` assigns. From `pointIdeal` coherence (`chartHbij_coherence`): equal
ideals have equal prime complements (`Ideal.mem_primeCompl_iff` + `ext`),
and equal submonoids give equivalent localizations (`chartLocCongr`).

Conditional on exactly `[ChartMaxSpecInj, ChartMaxSpecSurj]` (via
coherence — no new hypotheses beyond `hbij`'s list).

## References

* This module, `Appendix_FixedPoint.BezoutChain.chartHbij_coherence`,
  `Appendix_FixedPoint.BezoutChain.chartLocCongr`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Dimension.ArtinianDecomposition`,
  `Appendix_FixedPoint.BezoutChain.chartDecomp_of`
  (consumer of this binder shape).
* `Mathlib/RingTheory/Ideal/Prime.lean`, `Ideal.mem_primeCompl_iff`.
* `Mathlib/RingTheory/Localization/AtPrime/Basic.lean`,
  `Localization.AtPrime` (reducible abbrev — defeq to `Localization`). -/
noncomputable def chartHloc_of_bijective (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hfin : (vanishingLocus n K G).Finite)
    (hc : ChartNonvanishing n K G ℓ)
    (hinj : ChartMaxSpecInj n K G ℓ hfin hc)
    (hsurj : ChartMaxSpecSurj n K G ℓ hfin hc)
    (m : MaximalSpectrum (chartRing n K G ℓ)) :
    Localization.AtPrime m.asIdeal ≃ₗ[K]
      locFam n K G ℓ hfin hc
        ((chartHbij_of_bijective n K G ℓ hfin hc hinj hsurj) m) := by
  set p : ↥(locLocusFinset n K G hfin) :=
    (chartHbij_of_bijective n K G ℓ hfin hc hinj hsurj) m with hp
  have hmem : p.val ∈ vanishingLocus n K G :=
    (mem_locLocusFinset n K G hfin p.val).mp p.property
  have hvG : ∀ i, MvPolynomial.eval p.val.rep (G i) = 0 :=
    fun i => hmem p.val.rep p.val.rep_nonzero
      (Projectivization.mk_rep p.val) i
  have hℓ : MvPolynomial.eval p.val.rep (mkLin n K ℓ) ≠ 0 :=
    hc p.val hmem p.val.rep p.val.rep_nonzero (Projectivization.mk_rep p.val)
  have hcoh := chartHbij_coherence n K G ℓ hfin hc hinj hsurj m hvG hℓ
  have hM : m.asIdeal.primeCompl =
      (pointIdeal n K G ℓ p.val.rep hvG hℓ).primeCompl := by
    ext x
    simp only [Ideal.mem_primeCompl_iff]
    rw [hcoh]
  exact chartLocCongr n K G ℓ _ _ hM

/-- The exact `ChartDecomp` shape (`LocalMultiplicity.haddLocal`'s `hdecomp` binder)
from `hfinA` plus the two-item geometric list: the `ArtinianDecomposition`
structure equiv (`chartDecomp_of`) fed with `chartHbij_of_bijective` and
`chartHloc_of_bijective`.

Conditional on exactly `[hfinA, ChartMaxSpecInj, ChartMaxSpecSurj]`.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Dimension.ArtinianDecomposition`,
  `Appendix_FixedPoint.BezoutChain.chartDecomp_of`.
* This module, `Appendix_FixedPoint.BezoutChain.chartHbij_of_bijective`,
  `Appendix_FixedPoint.BezoutChain.chartHloc_of_bijective`. -/
noncomputable def chartDecomp_closed (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hfin : (vanishingLocus n K G).Finite)
    (hc : ChartNonvanishing n K G ℓ)
    (hfinA : Module.Finite K (chartRing n K G ℓ))
    (hinj : ChartMaxSpecInj n K G ℓ hfin hc)
    (hsurj : ChartMaxSpecSurj n K G ℓ hfin hc) :
    ChartDecomp n K G ℓ hfin hc :=
  chartDecomp_of n K G ℓ hfin hc hfinA
    (chartHbij_of_bijective n K G ℓ hfin hc hinj hsurj)
    (chartHloc_of_bijective n K G ℓ hfin hc hinj hsurj)

/-- The `hadd` sum equation from chart finiteness plus the two-item geometric
list (`chart_hadd_of_decomp` fed with `chartDecomp_closed`).

Conditional on exactly `[hfinA, ChartMaxSpecInj, ChartMaxSpecSurj]`.

## References

* This module, `Appendix_FixedPoint.BezoutChain.chart_hadd_of_decomp`,
  `Appendix_FixedPoint.BezoutChain.chartDecomp_closed`. -/
theorem chart_hadd_closed (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hfin : (vanishingLocus n K G).Finite)
    (hc : ChartNonvanishing n K G ℓ)
    (hfinA : Module.Finite K (chartRing n K G ℓ))
    (hinj : ChartMaxSpecInj n K G ℓ hfin hc)
    (hsurj : ChartMaxSpecSurj n K G ℓ hfin hc) :
    ∑ p ∈ locLocusFinset n K G hfin, localPointMultiplicity n K G ℓ hc p
      = Module.finrank K (chartRing n K G ℓ) :=
  chart_hadd_of_decomp n K G ℓ hfin hc hfinA
    (chartDecomp_closed n K G ℓ hfin hc hfinA hinj hsurj)

/-- End-to-end G2 assembly from stabilization: the `hadd` sum equation from
filtration stabilization plus the two geometric conditions (`hfinA` via
`chartHfinA_of_stable`).

Conditional on exactly `[hstab, ChartMaxSpecInj, ChartMaxSpecSurj]`.

## References

* This module, `Appendix_FixedPoint.BezoutChain.chart_hadd_closed`,
  `Appendix_FixedPoint.BezoutChain.chartHfinA_of_stable`. -/
theorem chart_hadd_of_stable (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hfin : (vanishingLocus n K G).Finite)
    (hc : ChartNonvanishing n K G ℓ) (D : ℕ)
    (hstab : chartPiece n K G ℓ D = ⊤)
    (hinj : ChartMaxSpecInj n K G ℓ hfin hc)
    (hsurj : ChartMaxSpecSurj n K G ℓ hfin hc) :
    ∑ p ∈ locLocusFinset n K G hfin, localPointMultiplicity n K G ℓ hc p
      = Module.finrank K (chartRing n K G ℓ) :=
  chart_hadd_closed n K G ℓ hfin hc
    (chartHfinA_of_stable n K G ℓ D hstab) hinj hsurj

/-- Chart positivity via a locus point, from stabilization alone:
`chart_pos_of_point` with its piece-finiteness input discharged
unconditionally by `chartPiece_finite` (the global `hpos` route with all
ChartFiltration-side inputs closed except stabilization).

Conditional on exactly `[hstab, hc, hp]`.

## References

* This module, `Appendix_FixedPoint.BezoutChain.chart_pos_of_point`,
  `Appendix_FixedPoint.BezoutChain.chartPiece_finite`. -/
theorem chart_pos_of_stable (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (D : ℕ)
    (hstab : chartPiece n K G ℓ D = ⊤)
    (hc : ChartNonvanishing n K G ℓ)
    (p : Projectivization K (Fin (n + 2) → K))
    (hp : p ∈ vanishingLocus n K G) :
    0 < Module.finrank K (chartRing n K G ℓ) :=
  chart_pos_of_point n K G ℓ D (fun d => chartPiece_finite n K G ℓ d)
    hstab hc p hp

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
open scoped BigOperators

/-! ## ChartMaxSpec closure: Nullstellensatz residue + exact transfer conditions

This section discharges the two G2 geometric conditions (`ChartMaxSpecInj` /
`ChartMaxSpecSurj`) down to their narrowest exact residuals, via the in-tree
Nullstellensatz engine over an algebraically closed field:

* Residue step (`chartAlgHom_of_maximal`, proved): over `[IsAlgClosed K]`,
  every maximal ideal `m` of a finite chart is the kernel of a `K`-point
  `φ : chartRing n K G ℓ →ₐ[K] K`. The engine is `IsAlgClosed.lift` applied
  to the residue field `chartRing ⧸ m.asIdeal` (a field by
  `Ideal.Quotient.field`, finite over `K` by
  `ArtinianDecomposition.moduleFinite_quotient_of_finite`, hence algebraic by
  `Algebra.IsAlgebraic.of_finite`) — the same engine proving
  `MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton`.
  Conditional on exactly `[IsAlgClosed K, hfinA]`.
* Affine feed (`affinePoint_of_maximal`, proved): every maximal ideal of the
  ambient polynomial ring containing the equation span is evaluation at an
  affine cone point — a direct corollary of
  `MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton`. This is the
  affine half of any future section-presentation transfer proof.
  Conditional on exactly `[IsAlgClosed K]`.
* `ChartEvalSeparation` (new, narrow): chart evaluations at distinct locus
  points differ as functions. `chartMaxSpecInj_of_separation` (proved)
  promotes this to `ChartMaxSpecInj` via the purely algebraic
  `chartEval_eq_of_ker_eq` (equal kernels + scalar compatibility ⟹ equal
  maps, from `chartEval_algebraMap`).
  Conditional on exactly `[ChartEvalSeparation]`.
* `ChartPointTransfer` (new, narrow): every abstract `K`-point
  `φ : chartRing n K G ℓ →ₐ[K] K` has kernel `pointIdeal` at some locus
  point's representative — i.e. every abstract point is geometric. This is
  the section-presentation transfer proper (chart `K`-point ↦ cone point
  avoiding `ℓ` ↦ projective locus point), which needs dehomogenization API
  absent from Mathlib v4.34.0. `chartMaxSpecSurj_of_transfer` (proved)
  promotes it to `ChartMaxSpecSurj` via the residue step.
  Conditional on exactly `[IsAlgClosed K, hfinA, ChartPointTransfer]`.

End-to-end effect: `chart_hadd_of_stable`'s list
`[hstab, ChartMaxSpecInj, ChartMaxSpecSurj]` refines to
`[hstab, ChartEvalSeparation, IsAlgClosed K, hfinA, ChartPointTransfer]`
with `hfinA` fed by `chartHfinA_of_stable`; the stabilization input
`hstab` is closed from the section side in the next section.
-/

/-- Chart evaluation respects scalars (feeds the kernel-comparison lemma).


## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Definitions`,
  `Appendix_FixedPoint.BezoutChain.chartEval`,
  `Appendix_FixedPoint.BezoutChain.chartLocEval`, `Appendix_FixedPoint.BezoutChain.coneEval_C`.
* `Mathlib/RingTheory/Localization/Defs.lean`, `IsLocalization.lift_eq`.
* `Mathlib/Algebra/Algebra/Tower.lean`, `IsScalarTower.algebraMap_apply`.
* `Mathlib/RingTheory/Ideal/Quotient/Operations.lean`,
  `Ideal.Quotient.mk_algebraMap`.
* `Mathlib/Algebra/MvPolynomial/Basic.lean`, `MvPolynomial.algebraMap_eq`. -/
theorem chartEval_algebraMap (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ : MvPolynomial.eval v (mkLin n K ℓ) ≠ 0) (r : K) :
    chartEval n K G ℓ v hvG hℓ (algebraMap K _ r) = r := by
  unfold chartEval
  rw [RingHom.comp_apply]
  change chartLocEval n K G ℓ v hvG hℓ (algebraMap K _ r) = r
  rw [IsScalarTower.algebraMap_apply K (coneQuotient n K G) _ r]
  unfold chartLocEval
  rw [IsLocalization.lift_eq, ← Ideal.Quotient.mk_algebraMap,
    MvPolynomial.algebraMap_eq]
  exact coneEval_C n K G v hvG r

/-- Two scalar-compatible maps to a field with equal kernels agree: for
`c := f x`, the element `x - algebraMap c` lies in both kernels, forcing
`g x = c`. Quotient-free (no `HasQuotient` synthesis over the chart).
-/
theorem chartEval_eq_of_ker_eq (K A : Type*) [Field K] [CommRing A]
    [Algebra K A] (f g : A →+* K)
    (hf : ∀ r : K, f (algebraMap K A r) = r)
    (hg : ∀ r : K, g (algebraMap K A r) = r)
    (hker : RingHom.ker f = RingHom.ker g) (x : A) : f x = g x := by
  have h0 : f (x - algebraMap K A (f x)) = 0 := by rw [map_sub, hf, sub_self]
  have hmem : x - algebraMap K A (f x) ∈ RingHom.ker g := by
    rw [← hker]
    exact RingHom.mem_ker.mpr h0
  have h1 : g (x - algebraMap K A (f x)) = 0 := RingHom.mem_ker.mp hmem
  rw [map_sub, hg, sub_eq_zero] at h1
  exact h1.symm

/-- A ring map out of a field has trivial kernel (the kernel is `⊥` or `⊤`
by `Ideal.eq_bot_or_top`, and `⊤` would kill `1`).


## References

* `Mathlib/RingTheory/Ideal/Lattice.lean`, `Ideal.eq_bot_or_top`. -/
theorem ker_eq_bot_of_field (Q K : Type*) [Field Q] [Field K]
    (e : Q →+* K) : RingHom.ker e = ⊥ := by
  rcases Ideal.eq_bot_or_top (RingHom.ker e) with h | h
  · exact h
  · exfalso
    have h1mem : (1 : Q) ∈ RingHom.ker e := by
      rw [h]
      exact Submodule.mem_top
    rw [RingHom.mem_ker, map_one] at h1mem
    exact one_ne_zero h1mem

/-- Kernel of the residue-field point: for `e : chart ⧸ m →ₐ[K] K` with
trivial kernel, `ker (e ∘ mkₐ) = m` (elementwise via `mkₐ_eq_mk`).


## References

* `Mathlib/RingTheory/Ideal/Quotient/Operations.lean`,
  `Ideal.Quotient.mkₐ_eq_mk`.
* `Mathlib/RingTheory/Ideal/Quotient/Defs.lean`,
  `Ideal.Quotient.eq_zero_iff_mem`.
* `Mathlib/Algebra/Module/Submodule/Lattice.lean`, `Submodule.mem_bot`. -/
theorem chartKer_comp_mk (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (m : MaximalSpectrum (chartRing n K G ℓ))
    (e : (chartRing n K G ℓ ⧸ m.asIdeal) →ₐ[K] K)
    (he : RingHom.ker e.toRingHom = ⊥) :
    RingHom.ker (e.comp (Ideal.Quotient.mkₐ K m.asIdeal)).toRingHom
      = m.asIdeal := by
  ext x
  simp only [RingHom.mem_ker]
  rw [show (e.comp (Ideal.Quotient.mkₐ K m.asIdeal)).toRingHom x
      = e ((Ideal.Quotient.mkₐ K m.asIdeal) x) from rfl]
  have hmk : (Ideal.Quotient.mkₐ K m.asIdeal) x
      = Ideal.Quotient.mk m.asIdeal x :=
    congrFun (Ideal.Quotient.mkₐ_eq_mk K m.asIdeal) x
  rw [hmk]
  constructor
  · intro h0
    have hmem : Ideal.Quotient.mk m.asIdeal x ∈ RingHom.ker e.toRingHom :=
      RingHom.mem_ker.mpr h0
    rw [he] at hmem
    have hx0 : Ideal.Quotient.mk m.asIdeal x = 0 :=
      (Submodule.mem_bot _).mp hmem
    exact (Ideal.Quotient.eq_zero_iff_mem).mp hx0
  · intro hx
    have hx0 : Ideal.Quotient.mk m.asIdeal x = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).mpr hx
    rw [hx0, map_zero]

/-- Residue step: over an algebraically closed field, every maximal ideal
of a finite chart is the kernel of a (surjective) `K`-point. The residue
field is a field (`Ideal.Quotient.field`), finite over `K`
(`ArtinianDecomposition.moduleFinite_quotient_of_finite`), hence algebraic
(`Algebra.IsAlgebraic.of_finite`), so `IsAlgClosed.lift` embeds it into
`K`; composing with `mkₐ` gives the point, surjective since `K`-algebra
maps hit all scalars.

Conditional on exactly `[IsAlgClosed K, hfinA]`.

## References

* This module, `Appendix_FixedPoint.BezoutChain.chartKer_comp_mk`,
  `Appendix_FixedPoint.BezoutChain.ker_eq_bot_of_field`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Dimension.ArtinianDecomposition`,
  `Appendix_FixedPoint.BezoutChain.moduleFinite_quotient_of_finite`.
* `Mathlib/FieldTheory/IsAlgClosed/Basic.lean`, `IsAlgClosed.lift`.
* `Mathlib/RingTheory/Algebraic/Integral.lean`,
  `Algebra.IsAlgebraic.of_finite`.
* `Mathlib/RingTheory/Ideal/Quotient/Basic.lean`,
  `Ideal.Quotient.field`. -/
theorem chartAlgHom_of_maximal (n : ℕ) (K : Type*) [Field K] [IsAlgClosed K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    [Module.Finite K (chartRing n K G ℓ)]
    (m : MaximalSpectrum (chartRing n K G ℓ)) :
    ∃ φ : chartRing n K G ℓ →ₐ[K] K,
      Function.Surjective φ ∧ RingHom.ker φ.toRingHom = m.asIdeal := by
  have hmax := m.isMaximal
  let hF : Field (chartRing n K G ℓ ⧸ m.asIdeal) :=
    Ideal.Quotient.field m.asIdeal
  have hfinQ : Module.Finite K (chartRing n K G ℓ ⧸ m.asIdeal) :=
    moduleFinite_quotient_of_finite K (chartRing n K G ℓ) m.asIdeal
  refine ⟨(IsAlgClosed.lift : (chartRing n K G ℓ ⧸ m.asIdeal) →ₐ[K] K).comp
    (Ideal.Quotient.mkₐ K m.asIdeal), ?_, ?_⟩
  · intro c
    refine ⟨algebraMap K _ c, ?_⟩
    rw [AlgHom.comp_apply, AlgHom.commutes, AlgHom.commutes]
    rfl
  · exact chartKer_comp_mk n K G ℓ m IsAlgClosed.lift
      (ker_eq_bot_of_field _ _ IsAlgClosed.lift.toRingHom)

/-- Affine feed: every maximal ideal of the ambient polynomial ring
containing the equation span is evaluation at an affine cone point —
directly from `MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton`
(`aeval` is `eval` by `MvPolynomial.aeval_eq_eval`, an `rfl`-lemma).

Conditional on exactly `[IsAlgClosed K]`.

## References

* `Mathlib/RingTheory/Nullstellensatz.lean`,
  `MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton`,
  `MvPolynomial.mem_vanishingIdeal_singleton_iff`.
* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.aeval_eq_eval`. -/
theorem affinePoint_of_maximal (n : ℕ) (K : Type*) [Field K] [IsAlgClosed K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (I : Ideal (MvPolynomial (Fin (n + 2)) K)) (hI : I.IsMaximal)
    (hG : Ideal.span (Set.range G) ≤ I) :
    ∃ v : Fin (n + 2) → K, (∀ i, MvPolynomial.eval v (G i) = 0) ∧
      ∀ p, p ∈ I ↔ MvPolynomial.eval v p = 0 := by
  obtain ⟨x, hx⟩ := MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.mp hI
  refine ⟨x, fun i => ?_, fun p => ?_⟩
  · have hmem : G i ∈ I := hG (Ideal.subset_span ⟨i, rfl⟩)
    rw [hx, MvPolynomial.mem_vanishingIdeal_singleton_iff] at hmem
    exact hmem
  · rw [hx, MvPolynomial.mem_vanishingIdeal_singleton_iff]
    exact Iff.rfl

/-- Narrowest exact condition (injectivity half of `hbij`, refined):
chart evaluations at distinct locus points differ as functions. The
membership/nonvanishing proofs are the exact `locusToMaxSpec` terms, so
`chartMaxSpecInj_of_separation` applies definitionally.

GRADE (with `ChartPointTransfer`): `hbij` is conditional on exactly
`[ChartEvalSeparation, IsAlgClosed K, hfinA, ChartPointTransfer]`. -/
def ChartEvalSeparation (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hfin : (vanishingLocus n K G).Finite)
    (hc : ChartNonvanishing n K G ℓ) : Prop :=
  ∀ p q : ↥(locLocusFinset n K G hfin),
    (∀ x : chartRing n K G ℓ,
      chartEval n K G ℓ p.val.rep
        (fun i => locMem n K G hfin p p.val.rep p.val.rep_nonzero
          (Projectivization.mk_rep p.val) i)
        (hc p.val ((mem_locLocusFinset n K G hfin p.val).mp p.property)
          p.val.rep p.val.rep_nonzero (Projectivization.mk_rep p.val)) x
      = chartEval n K G ℓ q.val.rep
        (fun i => locMem n K G hfin q q.val.rep q.val.rep_nonzero
          (Projectivization.mk_rep q.val) i)
        (hc q.val ((mem_locLocusFinset n K G hfin q.val).mp q.property)
          q.val.rep q.val.rep_nonzero (Projectivization.mk_rep q.val)) x)
    → p = q

/-- `ChartMaxSpecInj` from evaluation separation: equal evaluation ideals
give equal kernels, hence equal evaluation maps
(`chartEval_eq_of_ker_eq` with `chartEval_algebraMap`), hence equal
points by separation.

Conditional on exactly `[ChartEvalSeparation]`.

## References

* This module, `Appendix_FixedPoint.BezoutChain.ChartEvalSeparation`,
  `Appendix_FixedPoint.BezoutChain.chartEval_eq_of_ker_eq`,
  `Appendix_FixedPoint.BezoutChain.chartEval_algebraMap`,
  `Appendix_FixedPoint.BezoutChain.ChartMaxSpecInj`. -/
theorem chartMaxSpecInj_of_separation (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hfin : (vanishingLocus n K G).Finite)
    (hc : ChartNonvanishing n K G ℓ)
    (hsep : ChartEvalSeparation n K G ℓ hfin hc) :
    ChartMaxSpecInj n K G ℓ hfin hc := by
  change Function.Injective (locusToMaxSpec n K G ℓ hfin hc)
  intro p q h
  apply hsep
  intro x
  have hker : RingHom.ker (chartEval n K G ℓ p.val.rep _ _) =
      RingHom.ker (chartEval n K G ℓ q.val.rep _ _) :=
    congrArg MaximalSpectrum.asIdeal h
  exact chartEval_eq_of_ker_eq K (chartRing n K G ℓ) _ _
    (chartEval_algebraMap n K G ℓ p.val.rep _ _)
    (chartEval_algebraMap n K G ℓ q.val.rep _ _) hker x

/-- Narrowest exact condition (surjectivity half of `hbij`, refined):
every abstract `K`-point `φ : chartRing n K G ℓ →ₐ[K] K` has kernel
`pointIdeal` at some locus point's representative — i.e. every abstract
point is geometric. This is the section-presentation transfer proper
(chart `K`-point ↦ cone point avoiding `ℓ` ↦ projective locus point);
the affine half is `affinePoint_of_maximal`, the projectivization half
needs dehomogenization API absent from Mathlib v4.34.0. The
membership/nonvanishing proofs are the exact `locusToMaxSpec` terms.

GRADE (with `ChartEvalSeparation`): `hbij` is conditional on exactly
`[ChartEvalSeparation, IsAlgClosed K, hfinA, ChartPointTransfer]`. -/
def ChartPointTransfer (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hfin : (vanishingLocus n K G).Finite)
    (hc : ChartNonvanishing n K G ℓ) : Prop :=
  ∀ φ : chartRing n K G ℓ →ₐ[K] K, ∃ p : ↥(locLocusFinset n K G hfin),
    RingHom.ker φ.toRingHom = pointIdeal n K G ℓ p.val.rep
      (fun i => locMem n K G hfin p p.val.rep p.val.rep_nonzero
        (Projectivization.mk_rep p.val) i)
      (hc p.val ((mem_locLocusFinset n K G hfin p.val).mp p.property)
        p.val.rep p.val.rep_nonzero (Projectivization.mk_rep p.val))

/-- `ChartMaxSpecSurj` from the transfer condition: the residue step
(`chartAlgHom_of_maximal`) turns `m` into a `K`-point `φ`, and
`ChartPointTransfer` identifies `ker φ` with a locus evaluation ideal.

Conditional on exactly `[IsAlgClosed K, hfinA, ChartPointTransfer]`.

## References

* This module, `Appendix_FixedPoint.BezoutChain.ChartPointTransfer`,
  `Appendix_FixedPoint.BezoutChain.chartAlgHom_of_maximal`,
  `Appendix_FixedPoint.BezoutChain.ChartMaxSpecSurj`.
* `Mathlib/RingTheory/Spectrum/Maximal/Defs.lean`,
  `MaximalSpectrum.ext`. -/
theorem chartMaxSpecSurj_of_transfer (n : ℕ) (K : Type*) [Field K]
    [IsAlgClosed K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hfin : (vanishingLocus n K G).Finite)
    (hc : ChartNonvanishing n K G ℓ)
    (hfinA : Module.Finite K (chartRing n K G ℓ))
    (htransfer : ChartPointTransfer n K G ℓ hfin hc) :
    ChartMaxSpecSurj n K G ℓ hfin hc := by
  change Function.Surjective (locusToMaxSpec n K G ℓ hfin hc)
  intro m
  have hfinA' : Module.Finite K (chartRing n K G ℓ) := hfinA
  obtain ⟨φ, -, hker⟩ := chartAlgHom_of_maximal n K G ℓ m
  obtain ⟨p, hp⟩ := htransfer φ
  refine ⟨p, ?_⟩
  apply MaximalSpectrum.ext
  exact hp.symm.trans hker

/-! ## Stabilization from the section side

`hstab` (`∃ D, chartPiece D = ⊤`) from section-piece vanishing:
`chart_finite_of_sectionPiece_vanishing` makes the chart finite, and
`chartPiece_stabilizes_of_finite` turns chart finiteness into
stabilization. The section-finiteness instance is discharged downstream
by `HilbertFunctionCount.section_finite_of_artinian` (from `hreg` + `hZd`; cited,
not imported — that module imports this one). The high-degree vanishing
shape `hvan` (a Hilbert-function input) stays explicit.
-/

/-- Chart finiteness (`hfinA`) from the section side: the exact
`chart_finite_of_sectionPiece_vanishing` handoff, named for the
conditional list.

Conditional on exactly `[hG, hreg, section-finite, hvan]`.

## References

* This module, `Appendix_FixedPoint.BezoutChain.chart_finite_of_sectionPiece_vanishing`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.section_finite_of_artinian` (discharges `section-finite` from
  `hreg` + `hZd`; cited, not imported). -/
theorem chartHfinA_of_sectionVanishing (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (B : ℕ)
    (hG : ∀ i, (G i).IsHomogeneous 2)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    [Module.Finite K (sectionQuotient n K G ℓ)]
    (hvan : ∀ d, B < d → Module.finrank K ↥(sectionPiece n K G ℓ d) = 0) :
    Module.Finite K (chartRing n K G ℓ) :=
  chart_finite_of_sectionPiece_vanishing n K G ℓ B hG hreg hvan

/-- Filtration stabilization (`hstab`) from the section side: section-piece
vanishing makes the chart finite, and a finite chart's monotone filtration
stabilizes.

Conditional on exactly `[hG, hreg, section-finite, hvan]`.

## References

* This module, `Appendix_FixedPoint.BezoutChain.chartHfinA_of_sectionVanishing`,
  `Appendix_FixedPoint.BezoutChain.chartPiece_stabilizes_of_finite`. -/
theorem chartStab_of_sectionVanishing (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (B : ℕ)
    (hG : ∀ i, (G i).IsHomogeneous 2)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    [Module.Finite K (sectionQuotient n K G ℓ)]
    (hvan : ∀ d, B < d → Module.finrank K ↥(sectionPiece n K G ℓ d) = 0) :
    ∃ D, chartPiece n K G ℓ D = ⊤ := by
  have hfinA : Module.Finite K (chartRing n K G ℓ) :=
    chartHfinA_of_sectionVanishing n K G ℓ B hG hreg hvan
  exact chartPiece_stabilizes_of_finite n K G ℓ

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
open scoped BigOperators

/-! ## MaxSpec correspondence in `FinalResiduals` ∀-shapes: adapters

This section packages the cf-close outputs (`chartMaxSpecInj_of_separation`,
`chartMaxSpecSurj_of_transfer`) in the exact `∀`-binder shapes the
`FinalDischargeHub.FinalResiduals` bundle consumes as its `hinj`/`hsurj`
components: `∀ hfin hc, ChartMaxSpecInj … hfin hc` and the `Surj` twin. At
bridge data (`N := statementIndex n`, `G := bridgeSystem n K c hn`,
`ℓ := R1RegularSection.secForm (statementIndex n) K`) these conclusions are
syntactically the `FinalResiduals` fields.

Conditional on exactly `[∀ hfin hc, ChartEvalSeparation …]` (`hinj`)
and `[IsAlgClosed K, hfinA, ∀ hfin hc, ChartPointTransfer …]` (`hsurj`). The
genuine closures below discharge these further (`hinj` unconditionally in
the next section; `hsurj` from quadrics `hG` in the section after).
-/

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
open scoped BigOperators

/-! ## Injectivity closure: evaluation separation (unconditional)

This section proves `ChartEvalSeparation` genuinely, closing the `hinj`
half of `hbij` with no residual hypotheses. The separating family is the
coordinate functions `X_j / ℓ` (`chartCoord`): chart evaluation at `v`
reads off the ratio `v_j / ℓ(v)` (`chartEval_chartCoord`, via the
`IsLocalization.lift` spec equation), so evaluations agreeing on all chart
elements force proportional representatives, hence equal projective points
(`Projectivization.mk_eq_mk_iff'`).

`FinalResiduals.hinj` ∀-shape with no hypotheses beyond the binders).
-/

/-- Coordinate functions `X_j / ℓ` in the chart (degree-`1` lift `X j` over
`ℓ̄ ^ 1`).


## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Statement.Definitions`,
  `Appendix_FixedPoint.BezoutChain.chartRing` (same
  anonymous-constructor pattern as `chartEval_surjective`'s degree-`0`
  witness).
* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.isHomogeneous_X`.
* `Mathlib/Algebra/Group/Submonoid/Membership.lean`,
  `Submonoid.mem_powers_iff`. -/
noncomputable def chartCoord (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (j : Fin (n + 2)) : chartRing n K G ℓ :=
  ⟨Localization.mk (Ideal.Quotient.mk (Ideal.span (Set.range G)) (MvPolynomial.X j))
    ⟨(Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ 1,
      (Submonoid.mem_powers_iff _ _).mpr ⟨1, rfl⟩⟩,
    1, Ideal.Quotient.mk (Ideal.span (Set.range G)) (MvPolynomial.X j),
    ⟨MvPolynomial.X j, MvPolynomial.isHomogeneous_X K j, rfl⟩, rfl⟩

/-- Chart evaluation at `v` reads off the coordinate ratio `v_j / ℓ(v)`
(the `IsLocalization.lift` spec equation
`coneEval s = coneEval ℓ^1 * V` solved by division).


## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Statement.Definitions`,
  `Appendix_FixedPoint.BezoutChain.chartEval`,
  `Appendix_FixedPoint.BezoutChain.chartLocEval`, `Appendix_FixedPoint.BezoutChain.coneEval`.
* `Mathlib/RingTheory/Localization/Defs.lean`,
  `Localization.mk_eq_mk'_apply`, `IsLocalization.lift_mk'_spec`.
* `Mathlib/RingTheory/Ideal/Quotient/Defs.lean`, `Ideal.Quotient.lift_mk`
  (used via definitional unfolding in `change`/`rfl`, per the `coneEval_C`
  precedent).
* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.eval_X`.
* `Mathlib/Algebra/GroupWithZero/Units/Basic.lean`, `div_mul_cancel₀`. -/
theorem chartEval_chartCoord (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ : MvPolynomial.eval v (mkLin n K ℓ) ≠ 0)
    (j : Fin (n + 2)) :
    chartEval n K G ℓ v hvG hℓ (chartCoord n K G ℓ j)
      = v j / MvPolynomial.eval v (mkLin n K ℓ) := by
  unfold chartEval chartCoord
  rw [RingHom.comp_apply]
  change chartLocEval n K G ℓ v hvG hℓ (Localization.mk
    (Ideal.Quotient.mk (Ideal.span (Set.range G)) (MvPolynomial.X j))
    ⟨(Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ 1, _⟩)
    = v j / MvPolynomial.eval v (mkLin n K ℓ)
  unfold chartLocEval
  rw [Localization.mk_eq_mk'_apply, IsLocalization.lift_mk'_spec]
  change coneEval n K G v hvG
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (MvPolynomial.X j))
    = coneEval n K G v hvG
      ((Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ 1)
      * (v j / MvPolynomial.eval v (mkLin n K ℓ))
  have eX : coneEval n K G v hvG
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (MvPolynomial.X j)) = v j := by
    change MvPolynomial.eval v (MvPolynomial.X j) = v j
    rw [MvPolynomial.eval_X]
  have eL : coneEval n K G v hvG
      ((Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ 1)
      = MvPolynomial.eval v (mkLin n K ℓ) := by
    rw [pow_one]
    rfl
  rw [eX, eL]
  rw [mul_comm (MvPolynomial.eval v (mkLin n K ℓ)) _]
  exact (div_mul_cancel₀ _ hℓ).symm

/-- Evaluation separation, proved: chart evaluations agreeing on all chart
elements (in particular on the coordinate functions, where they read off
`v_j / ℓ(v)`) force proportional representatives, hence equal projective
points.


## References

* This module, `Appendix_FixedPoint.BezoutChain.chartCoord`,
  `Appendix_FixedPoint.BezoutChain.chartEval_chartCoord`,
  `Appendix_FixedPoint.BezoutChain.ChartEvalSeparation`.
* `Mathlib/LinearAlgebra/Projectivization/Basic.lean`,
  `Projectivization.mk_eq_mk_iff'`, `Projectivization.mk_rep`. -/
theorem chartEvalSeparation_proved (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hfin : (vanishingLocus n K G).Finite)
    (hc : ChartNonvanishing n K G ℓ) :
    ChartEvalSeparation n K G ℓ hfin hc := by
  intro p q hagree
  have hLp : MvPolynomial.eval p.val.rep (mkLin n K ℓ) ≠ 0 :=
    hc p.val ((mem_locLocusFinset n K G hfin p.val).mp p.property)
      p.val.rep p.val.rep_nonzero (Projectivization.mk_rep p.val)
  have hLq : MvPolynomial.eval q.val.rep (mkLin n K ℓ) ≠ 0 :=
    hc q.val ((mem_locLocusFinset n K G hfin q.val).mp q.property)
      q.val.rep q.val.rep_nonzero (Projectivization.mk_rep q.val)
  have hcoord : ∀ j : Fin (n + 2),
      p.val.rep j / MvPolynomial.eval p.val.rep (mkLin n K ℓ)
        = q.val.rep j / MvPolynomial.eval q.val.rep (mkLin n K ℓ) := by
    intro j
    have h := hagree (chartCoord n K G ℓ j)
    rw [chartEval_chartCoord, chartEval_chartCoord] at h
    exact h
  have hkey : ∀ x y z : K, x * (y / z) = (x / z) * y := by
    intro x y z
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  have hvw : p.val.rep
      = (MvPolynomial.eval p.val.rep (mkLin n K ℓ)
        / MvPolynomial.eval q.val.rep (mkLin n K ℓ)) • q.val.rep := by
    funext j
    rw [Pi.smul_apply, smul_eq_mul]
    have h2 : p.val.rep j = MvPolynomial.eval p.val.rep (mkLin n K ℓ)
        * (q.val.rep j / MvPolynomial.eval q.val.rep (mkLin n K ℓ)) := by
      rw [← hcoord j]
      rw [mul_comm]
      exact (div_mul_cancel₀ _ hLp).symm
    rw [h2, hkey]
  have hmk : Projectivization.mk K p.val.rep p.val.rep_nonzero
      = Projectivization.mk K q.val.rep q.val.rep_nonzero :=
    (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr ⟨_, hvw.symm⟩
  have hpq : p.val = q.val := by
    have e1 := Projectivization.mk_rep p.val
    have e2 := Projectivization.mk_rep q.val
    rw [← e1, ← e2]
    exact hmk
  exact Subtype.ext hpq

/-- `hinj` ∀-form, closed: the exact `FinalResiduals.hinj` shape with no
residual hypotheses.


## References

* This module, `Appendix_FixedPoint.BezoutChain.chartMaxSpecInj_of_separation`,
  `Appendix_FixedPoint.BezoutChain.chartEvalSeparation_proved`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.FinalDischargeHub`,
  `Appendix_FixedPoint.BezoutChain.FinalResiduals`
  (consumer of this binder shape; cited, not imported). -/
theorem chartMaxSpecInj_forall (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) :
    ∀ (hfin : (vanishingLocus n K G).Finite)
      (hc : ChartNonvanishing n K G ℓ),
      ChartMaxSpecInj n K G ℓ hfin hc := by
  intro hfin hc
  exact chartMaxSpecInj_of_separation n K G ℓ hfin hc
    (chartEvalSeparation_proved n K G ℓ hfin hc)

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
open scoped BigOperators

/-! ## Scale lemmas (mirrored from `ChartCompat`)

Verbatim mirrors of `ChartCompat.eval_smul_compat`,
`ChartCompat.chartLocEval_smul_mk`, `ChartCompat.chartEval_smul`, and
`ChartCompat.pointIdeal_smul` (homogeneous-eval scaling and
scale-invariance of chart evaluation / point ideals). Mirrored rather than
imported: `ChartCompat` imports `MkSystemChart`, which imports this module,
so a `ChartFiltration → ChartCompat` edge would cycle. The only adaptation
is using this module's own `mkLin_isHomogeneous` for the degree-`1` fact.
-/

/-- Homogeneous evaluation scales: `eval (a • v) φ = a ^ d * eval v φ`.
Mirror of `ChartCompat.eval_smul_compat` (see section docstring).

## References

* `Mathlib/Algebra/MvPolynomial/Basic.lean`, `MvPolynomial.as_sum`.
* `Mathlib/Data/Finsupp/Weight.lean`, `Finsupp.weight_apply`.
* `Mathlib/Data/Finsupp/Defs.lean`, `Finsupp.mem_support_iff`.
* `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`,
  `Finset.prod_pow_eq_pow_sum`, `Finset.prod_mul_distrib`, `Finset.mul_sum`,
  `map_sum`. -/
theorem eval_smul_compat_cf {σ : Type*} {K : Type*} [Field K]
    {φ : MvPolynomial σ K} {d : ℕ} (hφ : φ.IsHomogeneous d) (a : K)
    (v : σ → K) :
    MvPolynomial.eval (a • v) φ = a ^ d * MvPolynomial.eval v φ := by
  rw [φ.as_sum]
  simp only [map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  have hsup : φ.coeff e ≠ 0 := Finsupp.mem_support_iff.mp he
  have hwt : Finsupp.weight (1 : σ → ℕ) e = d := hφ hsup
  rw [Finsupp.weight_apply] at hwt
  have hsum : e.sum (fun _ c => c) = d := by
    simpa using hwt
  simp only [MvPolynomial.eval_monomial]
  have hterm : e.prod (fun n en => ((a • v) n) ^ en)
      = a ^ d * e.prod (fun n en => (v n) ^ en) := by
    have h1 : ∀ n en, ((a • v) n) ^ en = a ^ en * (v n) ^ en := fun n en => by
      rw [Pi.smul_apply, smul_eq_mul, mul_pow]
    simp_rw [h1]
    unfold Finsupp.prod
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    have hnat : e.support.sum (fun n => e n) = d := by
      have h2 := hsum
      unfold Finsupp.sum at h2
      simpa using h2
    rw [hnat]
  rw [hterm, mul_left_comm]

/-- Scale-invariance of `chartLocEval` on a presented fraction. Mirror of
`ChartCompat.chartLocEval_smul_mk` (see section docstring).

## References

* `Statement.Definitions`, `Appendix_FixedPoint.BezoutChain.chartLocEval`,
  `Appendix_FixedPoint.BezoutChain.coneEval`,
  `Appendix_FixedPoint.BezoutChain.mkLin`.
* This module, `Appendix_FixedPoint.BezoutChain.eval_smul_compat_cf`,
  `Appendix_FixedPoint.BezoutChain.mkLin_isHomogeneous`.
* `Mathlib/RingTheory/Localization/Defs.lean`,
  `Localization.mk_eq_mk'_apply`, `IsLocalization.lift_mk'_spec`.
* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.IsHomogeneous.pow`.
* `Mathlib/RingTheory/Ideal/Quotient/Defs.lean`, `Ideal.Quotient.lift_mk`
  (used via definitional unfolding in `rfl`, per the `coneEval_C` precedent).
* `Mathlib/Algebra/Group/Hom/Defs.lean`, `map_pow`. -/
theorem chartLocEval_smul_mk_cf (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (v : Fin (n + 2) → K) (a : K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ : MvPolynomial.eval v (mkLin n K ℓ) ≠ 0)
    (hvGw : ∀ i, MvPolynomial.eval (a • v) (G i) = 0)
    (hℓw : MvPolynomial.eval (a • v) (mkLin n K ℓ) ≠ 0)
    (d : ℕ) (s : coneQuotient n K G) (p : MvPolynomial (Fin (n + 2)) K)
    (hphom : p.IsHomogeneous d)
    (hpeq : Ideal.Quotient.mk (Ideal.span (Set.range G)) p = s)
    (y : Submonoid.powers (Ideal.Quotient.mk (Ideal.span (Set.range G))
      (mkLin n K ℓ)))
    (hy : (y : coneQuotient n K G)
      = (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ d) :
    chartLocEval n K G ℓ (a • v) hvGw hℓw (Localization.mk s y)
      = chartLocEval n K G ℓ v hvG hℓ (Localization.mk s y) := by
  set V := chartLocEval n K G ℓ v hvG hℓ (Localization.mk s y) with hVdef
  unfold chartLocEval
  rw [Localization.mk_eq_mk'_apply, IsLocalization.lift_mk'_spec]
  have hV : coneEval n K G v hvG s
      = coneEval n K G v hvG (y : coneQuotient n K G) * V := by
    rw [hVdef]
    unfold chartLocEval
    rw [Localization.mk_eq_mk'_apply]
    exact (IsLocalization.lift_mk'_spec _ _ _ _).mp rfl
  have hws : coneEval n K G (a • v) hvGw s
      = a ^ d * coneEval n K G v hvG s := by
    have cw : coneEval n K G (a • v) hvGw s
        = MvPolynomial.eval (a • v) p := by
      rw [← hpeq]
      rfl
    have cv : coneEval n K G v hvG s = MvPolynomial.eval v p := by
      rw [← hpeq]
      rfl
    rw [cw, cv, eval_smul_compat_cf hphom a v]
  have hpowmk : (Ideal.Quotient.mk (Ideal.span (Set.range G))
        (mkLin n K ℓ)) ^ d
      = Ideal.Quotient.mk (Ideal.span (Set.range G)) ((mkLin n K ℓ) ^ d) := by
    rw [map_pow]
  have hhom : ((mkLin n K ℓ) ^ d).IsHomogeneous d := by
    have h1 := (mkLin_isHomogeneous n K ℓ).pow d
    rwa [one_mul] at h1
  have hwℓ : coneEval n K G (a • v) hvGw (y : coneQuotient n K G)
      = a ^ d * coneEval n K G v hvG (y : coneQuotient n K G) := by
    rw [hy]
    have cw : coneEval n K G (a • v) hvGw
          ((Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ d)
        = MvPolynomial.eval (a • v) ((mkLin n K ℓ) ^ d) := by
      rw [hpowmk]
      rfl
    have cv : coneEval n K G v hvG
          ((Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ d)
        = MvPolynomial.eval v ((mkLin n K ℓ) ^ d) := by
      rw [hpowmk]
      rfl
    rw [cw, cv, eval_smul_compat_cf hhom a v]
  rw [hws, hwℓ, hV]
  ring

/-- Scale-invariance of `chartEval` as ring homs. Mirror of
`ChartCompat.chartEval_smul` (see section docstring).

## References

* `Statement.Definitions`, `Appendix_FixedPoint.BezoutChain.chartEval`,
  `Appendix_FixedPoint.BezoutChain.chartRing`.
* This module, `Appendix_FixedPoint.BezoutChain.chartLocEval_smul_mk_cf`.
* `Mathlib/Algebra/Ring/Hom/Defs.lean`, `RingHom.ext`,
  `RingHom.comp_apply`. -/
theorem chartEval_smul_cf (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (v : Fin (n + 2) → K) (a : K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ : MvPolynomial.eval v (mkLin n K ℓ) ≠ 0)
    (hvGw : ∀ i, MvPolynomial.eval (a • v) (G i) = 0)
    (hℓw : MvPolynomial.eval (a • v) (mkLin n K ℓ) ≠ 0) :
    chartEval n K G ℓ (a • v) hvGw hℓw
      = chartEval n K G ℓ v hvG hℓ := by
  apply RingHom.ext
  intro x
  obtain ⟨val, d, s, ⟨p, hphom, hpeq⟩, e⟩ := x
  unfold chartEval
  rw [RingHom.comp_apply, RingHom.comp_apply]
  change chartLocEval n K G ℓ (a • v) hvGw hℓw val
    = chartLocEval n K G ℓ v hvG hℓ val
  rw [e]
  exact chartLocEval_smul_mk_cf n K G ℓ v a hvG hℓ hvGw hℓw d s p hphom hpeq
    _ rfl

/-- Scale-invariance of the point ideal. Mirror of
`ChartCompat.pointIdeal_smul` (see section docstring).

## References

* `Statement.Definitions`, `Appendix_FixedPoint.BezoutChain.pointIdeal`.
* This module, `Appendix_FixedPoint.BezoutChain.chartEval_smul_cf`. -/
theorem pointIdeal_smul_cf (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (v : Fin (n + 2) → K) (a : K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ : MvPolynomial.eval v (mkLin n K ℓ) ≠ 0)
    (hvGw : ∀ i, MvPolynomial.eval (a • v) (G i) = 0)
    (hℓw : MvPolynomial.eval (a • v) (mkLin n K ℓ) ≠ 0) :
    pointIdeal n K G ℓ (a • v) hvGw hℓw
      = pointIdeal n K G ℓ v hvG hℓ := by
  unfold pointIdeal
  rw [chartEval_smul_cf n K G ℓ v a hvG hℓ hvGw hℓw]

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
open scoped BigOperators

/-! ## Chart elements from homogeneous lifts (`chartOfHomog` API)

This section builds the bridge between homogeneous polynomials and chart
elements: `chartOfHomog d p h` is the class of `p / ℓ^d`, with the ring
operations (`chartOfHomog_add/mul/C`), the `chartEval` computation
(`chartEval_chartOfHomog`: evaluation reads off `eval v p / ℓ(v)^d`), and
the key generation fact `phi_chartOfHomog`: every abstract `K`-point `φ`
evaluates `chartOfHomog d p h` as `eval a p` at the coordinate point
`a j := φ (chartCoord j)` (via the monomial decomposition `as_sum` +
`monomial_eq` and the finiteness bridge `Finsupp.prod_fintype`). Together
with `chartCoord_sum_lin` (`∑ ℓ_j • u_j = 1`, so the coordinate point has
`ℓ(a) = 1`), this feeds the genuine `ChartPointTransfer` proof.
-/

/-- The chart element `p / ℓ^d` for `p` homogeneous of degree `d`.


## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Statement.Definitions`,
  `Appendix_FixedPoint.BezoutChain.chartRing` (same
  anonymous-constructor pattern as `chartEval_surjective`).
* `Mathlib/Algebra/Group/Submonoid/Membership.lean`,
  `Submonoid.mem_powers_iff`. -/
noncomputable def chartOfHomog (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (d : ℕ) (p : MvPolynomial (Fin (n + 2)) K)
    (_h : p.IsHomogeneous d) : chartRing n K G ℓ :=
  ⟨Localization.mk (Ideal.Quotient.mk (Ideal.span (Set.range G)) p)
    ⟨(Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ d,
      (Submonoid.mem_powers_iff _ _).mpr ⟨d, rfl⟩⟩,
    d, Ideal.Quotient.mk (Ideal.span (Set.range G)) p,
    ⟨p, _h, rfl⟩, rfl⟩

/-- `chartOfHomog` is additive in the lift (common denominator).


## References

* This module, `Appendix_FixedPoint.BezoutChain.chartOfHomog`.
* `Mathlib/RingTheory/Localization/Defs.lean`, `Localization.add_mk_self`. -/
theorem chartOfHomog_add (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (d : ℕ)
    (p q : MvPolynomial (Fin (n + 2)) K)
    (h₁ : p.IsHomogeneous d) (h₂ : q.IsHomogeneous d)
    (h : (p + q).IsHomogeneous d) :
    chartOfHomog n K G ℓ d (p + q) h
      = chartOfHomog n K G ℓ d p h₁ + chartOfHomog n K G ℓ d q h₂ := by
  apply Subtype.ext
  change Localization.mk (Ideal.Quotient.mk (Ideal.span (Set.range G)) (p + q)) _
    = Localization.mk (Ideal.Quotient.mk (Ideal.span (Set.range G)) p) _
      + Localization.mk (Ideal.Quotient.mk (Ideal.span (Set.range G)) q) _
  rw [Localization.add_mk_self, ← map_add]

/-- `chartOfHomog` is multiplicative in the lift (degrees add).


## References

* This module, `Appendix_FixedPoint.BezoutChain.chartOfHomog`.
* `Mathlib/GroupTheory/MonoidLocalization/Basic.lean`, `Localization.mk_mul`. -/
theorem chartOfHomog_mul (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (d₁ d₂ : ℕ)
    (p q : MvPolynomial (Fin (n + 2)) K)
    (h₁ : p.IsHomogeneous d₁) (h₂ : q.IsHomogeneous d₂)
    (h : (p * q).IsHomogeneous (d₁ + d₂)) :
    chartOfHomog n K G ℓ (d₁ + d₂) (p * q) h
      = chartOfHomog n K G ℓ d₁ p h₁ * chartOfHomog n K G ℓ d₂ q h₂ := by
  apply Subtype.ext
  change Localization.mk (Ideal.Quotient.mk (Ideal.span (Set.range G)) (p * q)) _
    = Localization.mk (Ideal.Quotient.mk (Ideal.span (Set.range G)) p) _
      * Localization.mk (Ideal.Quotient.mk (Ideal.span (Set.range G)) q) _
  rw [Localization.mk_mul, ← map_mul]
  congr 1
  exact Subtype.ext (pow_add _ _ _)

/-- `chartOfHomog` on constants is the scalar map.


## References

* This module, `Appendix_FixedPoint.BezoutChain.chartOfHomog`.
* `Mathlib/RingTheory/Localization/Defs.lean`, `Localization.mk_algebraMap`.
* `Mathlib/Algebra/Algebra/Subalgebra/Basic.lean`,
  `Subalgebra.coe_algebraMap`.
* `Mathlib/RingTheory/Ideal/Quotient/Operations.lean`,
  `Ideal.Quotient.mk_algebraMap`.
* `Mathlib/Algebra/MvPolynomial/Basic.lean`, `MvPolynomial.algebraMap_eq`. -/
theorem chartOfHomog_C (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (c : K)
    (h : (MvPolynomial.C c : MvPolynomial (Fin (n + 2)) K).IsHomogeneous 0) :
    chartOfHomog n K G ℓ 0 (MvPolynomial.C c) h
      = algebraMap K (chartRing n K G ℓ) c := by
  apply Subtype.ext
  change Localization.mk (Ideal.Quotient.mk (Ideal.span (Set.range G)) (MvPolynomial.C c)) _
    = (algebraMap K (chartRing n K G ℓ) c).val
  have hC : (MvPolynomial.C c : MvPolynomial (Fin (n + 2)) K)
      = algebraMap K (MvPolynomial (Fin (n + 2)) K) c := by
    rw [MvPolynomial.algebraMap_eq]
  have hmap : Ideal.Quotient.mk (Ideal.span (Set.range G)) (MvPolynomial.C c)
      = algebraMap K (coneQuotient n K G) c := by
    rw [hC]
    exact Ideal.Quotient.mk_algebraMap K _ _
  rw [hmap, Subalgebra.coe_algebraMap]
  exact Localization.mk_algebraMap c

/-- Chart evaluation on `chartOfHomog`: reads off `eval v p / ℓ(v)^d`.


## References

* This module, `Appendix_FixedPoint.BezoutChain.chartOfHomog` (same `IsLocalization.lift` pattern as
  `Appendix_FixedPoint.BezoutChain.chartEval_chartCoord`).
* `Mathlib/RingTheory/Localization/Defs.lean`,
  `Localization.mk_eq_mk'_apply`, `IsLocalization.lift_mk'_spec`.
* `Mathlib/Algebra/GroupWithZero/Units/Basic.lean`, `div_mul_cancel₀`. -/
theorem chartEval_chartOfHomog (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ : MvPolynomial.eval v (mkLin n K ℓ) ≠ 0)
    (d : ℕ) (p : MvPolynomial (Fin (n + 2)) K) (h : p.IsHomogeneous d) :
    chartEval n K G ℓ v hvG hℓ (chartOfHomog n K G ℓ d p h)
      = MvPolynomial.eval v p / (MvPolynomial.eval v (mkLin n K ℓ)) ^ d := by
  unfold chartEval chartOfHomog
  rw [RingHom.comp_apply]
  change chartLocEval n K G ℓ v hvG hℓ (Localization.mk
    (Ideal.Quotient.mk (Ideal.span (Set.range G)) p)
    ⟨(Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ d, _⟩)
    = MvPolynomial.eval v p / (MvPolynomial.eval v (mkLin n K ℓ)) ^ d
  unfold chartLocEval
  rw [Localization.mk_eq_mk'_apply, IsLocalization.lift_mk'_spec]
  change coneEval n K G v hvG (Ideal.Quotient.mk (Ideal.span (Set.range G)) p)
    = coneEval n K G v hvG
      ((Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ d)
      * (MvPolynomial.eval v p / (MvPolynomial.eval v (mkLin n K ℓ)) ^ d)
  have eP : coneEval n K G v hvG
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) p)
      = MvPolynomial.eval v p := rfl
  have eL0 : coneEval n K G v hvG
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ))
      = MvPolynomial.eval v (mkLin n K ℓ) := rfl
  have eL : coneEval n K G v hvG
      ((Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ d)
      = (MvPolynomial.eval v (mkLin n K ℓ)) ^ d := by
    rw [map_pow, eL0]
  rw [eP, eL]
  have hL : (MvPolynomial.eval v (mkLin n K ℓ)) ^ d ≠ 0 := pow_ne_zero d hℓ
  rw [mul_comm ((MvPolynomial.eval v (mkLin n K ℓ)) ^ d) _]
  exact (div_mul_cancel₀ _ hL).symm

/-- Finite sums of fractions with a common denominator.


## References

* `Mathlib/RingTheory/Localization/Defs.lean`, `Localization.add_mk_self`.
* `Mathlib/GroupTheory/MonoidLocalization/Basic.lean`,
  `Localization.mk_zero`. -/
theorem locMk_sum {ι : Type*} {R : Type*} [CommRing R] {M : Submonoid R}
    (s : Finset ι) (f : ι → R) (y : M) :
    (∑ j ∈ s, Localization.mk (f j) y) = Localization.mk (∑ j ∈ s, f j) y := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact (Localization.mk_zero _).symm
  | insert _a _s' ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, Localization.add_mk_self]

/-- The coordinate functions sum to `1` against `ℓ`
(`∑ ℓ_j • (X_j / ℓ) = mkLin / ℓ = 1`).


## References

* This module, `Appendix_FixedPoint.BezoutChain.chartCoord`,
  `Appendix_FixedPoint.BezoutChain.locMk_sum`.
* `Mathlib/GroupTheory/MonoidLocalization/Basic.lean`,
  `Localization.smul_mk`, `Localization.mk_self`.
* `Mathlib/Algebra/Algebra/Subalgebra/Basic.lean`, `Subalgebra.coe_smul`.
* `Mathlib/Algebra/Algebra/Defs.lean`, `Algebra.smul_def`.
* `Mathlib/RingTheory/Ideal/Quotient/Operations.lean`,
  `Ideal.Quotient.mk_algebraMap`.
* `Mathlib/Algebra/MvPolynomial/Basic.lean`, `MvPolynomial.algebraMap_eq`. -/
theorem chartCoord_sum_lin (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) :
    (∑ j : Fin (n + 2), ℓ j • chartCoord n K G ℓ j) = 1 := by
  have hterm : ∀ j : Fin (n + 2),
      ((ℓ j • chartCoord n K G ℓ j : chartRing n K G ℓ).val
        = Localization.mk (Ideal.Quotient.mk (Ideal.span (Set.range G))
            (MvPolynomial.C (ℓ j) * MvPolynomial.X j))
          ⟨(Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ 1,
            (Submonoid.mem_powers_iff _ _).mpr ⟨1, rfl⟩⟩) := by
    intro j
    have hval : (chartCoord n K G ℓ j).val
        = Localization.mk (Ideal.Quotient.mk (Ideal.span (Set.range G)) (MvPolynomial.X j))
          ⟨(Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ 1,
            (Submonoid.mem_powers_iff _ _).mpr ⟨1, rfl⟩⟩ := rfl
    have hsmul : ((ℓ j • chartCoord n K G ℓ j : chartRing n K G ℓ).val)
        = ℓ j • (chartCoord n K G ℓ j).val :=
      Subalgebra.coe_smul _ _ _
    rw [hsmul, hval, Localization.smul_mk]
    congr 1
    have hC : (MvPolynomial.C (ℓ j) : MvPolynomial (Fin (n + 2)) K)
        = algebraMap K (MvPolynomial (Fin (n + 2)) K) (ℓ j) := by
      rw [MvPolynomial.algebraMap_eq]
    have hmap : Ideal.Quotient.mk (Ideal.span (Set.range G)) (MvPolynomial.C (ℓ j))
        = algebraMap K (coneQuotient n K G) (ℓ j) := by
      rw [hC]
      exact Ideal.Quotient.mk_algebraMap K _ _
    have esmul : ℓ j • Ideal.Quotient.mk (Ideal.span (Set.range G)) (MvPolynomial.X j)
        = algebraMap K (coneQuotient n K G) (ℓ j)
          * Ideal.Quotient.mk (Ideal.span (Set.range G)) (MvPolynomial.X j) :=
      Algebra.smul_def (A := coneQuotient n K G) (ℓ j) _
    rw [esmul, ← hmap, ← map_mul]
  have hdist : ((∑ j : Fin (n + 2), ℓ j • chartCoord n K G ℓ j : chartRing n K G ℓ).val)
      = ∑ j : Fin (n + 2), ((ℓ j • chartCoord n K G ℓ j : chartRing n K G ℓ).val) :=
    map_sum (Subalgebra.val _).toRingHom _ _
  have hmk : (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ))
      = ∑ j : Fin (n + 2), Ideal.Quotient.mk (Ideal.span (Set.range G))
        (MvPolynomial.C (ℓ j) * MvPolynomial.X j) := by
    unfold mkLin
    rw [map_sum]
  apply Subtype.ext
  rw [hdist]
  simp only [hterm]
  rw [locMk_sum]
  rw [← hmk]
  have hstep : Localization.mk (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ))
        ⟨(Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ 1,
          (Submonoid.mem_powers_iff _ _).mpr ⟨1, rfl⟩⟩
      = Localization.mk ((Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ 1)
        ⟨(Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ 1,
          (Submonoid.mem_powers_iff _ _).mpr ⟨1, rfl⟩⟩ := by
    congr 1
    exact (pow_one _).symm
  rw [hstep, Subalgebra.coe_one]
  exact Localization.mk_self (M := coneQuotient n K G)
    ⟨(Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ 1,
      (Submonoid.mem_powers_iff _ _).mpr ⟨1, rfl⟩⟩

/-- A product of variable powers is homogeneous of the summed degree.


## References

* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.isHomogeneous_X`, `MvPolynomial.isHomogeneous_one`,
  `MvPolynomial.IsHomogeneous.pow/mul`. -/
theorem isHomog_X_pow_prod (n : ℕ) (K : Type*) [Field K]
    (s : Finset (Fin (n + 2))) (e : Fin (n + 2) → ℕ) :
    ((∏ j ∈ s, (MvPolynomial.X j : MvPolynomial (Fin (n + 2)) K) ^ (e j))).IsHomogeneous
      (∑ j ∈ s, e j) := by
  induction s using Finset.induction with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty]
    exact MvPolynomial.isHomogeneous_one _ _
  | insert a s' ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hXa : ((MvPolynomial.X a : MvPolynomial (Fin (n + 2)) K) ^ (e a)).IsHomogeneous
        (e a) := by
      have h0 := (MvPolynomial.isHomogeneous_X K a).pow (e a)
      rwa [one_mul] at h0
    exact hXa.mul ih

/-- `chartOfHomog` on variable powers is the coordinate power.


## References

* This module, `Appendix_FixedPoint.BezoutChain.chartOfHomog`,
  `Appendix_FixedPoint.BezoutChain.chartOfHomog_mul`,
  `Appendix_FixedPoint.BezoutChain.chartCoord`.
* `Mathlib/GroupTheory/MonoidLocalization/Basic.lean`,
  `Localization.mk_self`. -/
theorem chartOfHomog_X_pow (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (j : Fin (n + 2)) (m : ℕ) :
    ∀ h : ((MvPolynomial.X j : MvPolynomial (Fin (n + 2)) K) ^ m).IsHomogeneous m,
    chartOfHomog n K G ℓ m ((MvPolynomial.X j) ^ m) h
      = (chartCoord n K G ℓ j) ^ m := by
  induction m with
  | zero =>
    rw [pow_zero, pow_zero]
    intro h
    apply Subtype.ext
    change Localization.mk _ _ = _
    rw [map_one, Subalgebra.coe_one]
    exact Localization.mk_self (M := coneQuotient n K G)
      ⟨(Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ 0,
        (Submonoid.mem_powers_iff _ _).mpr ⟨0, rfl⟩⟩
  | succ m ih =>
    intro h
    revert h
    rw [pow_succ, pow_succ]
    intro h
    have hXm : ((MvPolynomial.X j : MvPolynomial (Fin (n + 2)) K) ^ m).IsHomogeneous m := by
      have h0 := (MvPolynomial.isHomogeneous_X K j).pow m
      rwa [one_mul] at h0
    have hX1 : (MvPolynomial.X j : MvPolynomial (Fin (n + 2)) K).IsHomogeneous 1 :=
      MvPolynomial.isHomogeneous_X K j
    have hcoord : chartCoord n K G ℓ j
        = chartOfHomog n K G ℓ 1 (MvPolynomial.X j) hX1 := rfl
    rw [chartOfHomog_mul _ _ _ _ _ _ _ _ hXm hX1, ih, ← hcoord]

/-- `chartOfHomog` on a product of variable powers is the product of
coordinate powers.


## References

* This module, `Appendix_FixedPoint.BezoutChain.chartOfHomog`,
  `Appendix_FixedPoint.BezoutChain.chartOfHomog_mul`,
  `Appendix_FixedPoint.BezoutChain.chartOfHomog_X_pow`,
  `Appendix_FixedPoint.BezoutChain.chartOfHomog_C`,
  `Appendix_FixedPoint.BezoutChain.isHomog_X_pow_prod`.
* `Mathlib/Algebra/MvPolynomial/Basic.lean`, `MvPolynomial.C_1`. -/
theorem chartOfHomog_X_pow_prod (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (s : Finset (Fin (n + 2))) (e : Fin (n + 2) → ℕ) :
    ∀ hpr : ((∏ j ∈ s, (MvPolynomial.X j : MvPolynomial (Fin (n + 2)) K) ^ (e j))).IsHomogeneous
      (∑ j ∈ s, e j),
    chartOfHomog n K G ℓ (∑ j ∈ s, e j)
        (∏ j ∈ s, (MvPolynomial.X j : MvPolynomial (Fin (n + 2)) K) ^ (e j)) hpr
      = ∏ j ∈ s, (chartCoord n K G ℓ j) ^ (e j) := by
  induction s using Finset.induction with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty, Finset.prod_empty, ← MvPolynomial.C_1]
    intro hpr
    rw [chartOfHomog_C, map_one]
  | insert a s' ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]
    intro hpr
    have hXa : ((MvPolynomial.X a : MvPolynomial (Fin (n + 2)) K) ^ (e a)).IsHomogeneous
        (e a) := by
      have h0 := (MvPolynomial.isHomogeneous_X K a).pow (e a)
      rwa [one_mul] at h0
    have hs' : ((∏ j ∈ s', (MvPolynomial.X j : MvPolynomial (Fin (n + 2)) K) ^ (e j))).IsHomogeneous
        (∑ j ∈ s', e j) :=
      isHomog_X_pow_prod n K s' e
    rw [chartOfHomog_mul _ _ _ _ _ _ _ _ hXa hs', chartOfHomog_X_pow, ih hs']

/-- `chartOfHomog` distributes over finite sums of same-degree lifts.


## References

* This module, `Appendix_FixedPoint.BezoutChain.chartOfHomog`,
  `Appendix_FixedPoint.BezoutChain.chartOfHomog_add`.
* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.IsHomogeneous.sum`.
* `Mathlib/GroupTheory/MonoidLocalization/Basic.lean`,
  `Localization.mk_zero`. -/
theorem chartOfHomog_sum (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (ι : Type*) (s : Finset ι)
    (f : ι → MvPolynomial (Fin (n + 2)) K)
    (d : ℕ) (h : ∀ e, (f e).IsHomogeneous d) :
    ∀ hs : (∑ e ∈ s, f e).IsHomogeneous d,
    chartOfHomog n K G ℓ d (∑ e ∈ s, f e) hs
      = ∑ e ∈ s, chartOfHomog n K G ℓ d (f e) (h e) := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    intro hs
    apply Subtype.ext
    change Localization.mk _ _ = _
    rw [map_zero, Localization.mk_zero]
    exact (Subalgebra.coe_zero _).symm
  | insert a s' ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    intro hs
    have hs' : (∑ e ∈ s', f e).IsHomogeneous d :=
      MvPolynomial.IsHomogeneous.sum _ _ _ (fun e _ => h e)
    rw [chartOfHomog_add _ _ _ _ _ _ _ (h a) hs', ih hs']

/-- A monomial is the constant times the product of variable powers over
`univ` (via `Finsupp.prod_fintype`).


## References

* `Mathlib/Algebra/MvPolynomial/Basic.lean`, `MvPolynomial.monomial_eq`.
* `Mathlib/Algebra/BigOperators/Finsupp/Basic.lean`,
  `Finsupp.prod_fintype`. -/
theorem monomial_eq_prod_univ (n : ℕ) (K : Type*) [Field K]
    (e : Fin (n + 2) →₀ ℕ) (c : K) :
    MvPolynomial.monomial e c
      = MvPolynomial.C c * ∏ j : Fin (n + 2), (MvPolynomial.X j) ^ (e j) := by
  rw [MvPolynomial.monomial_eq]
  congr 1
  exact Finsupp.prod_fintype _ _ (fun i => pow_zero _)

/-- `chartOfHomog` on a monomial is the scalar times the product of
coordinate powers.


## References

* This module, `Appendix_FixedPoint.BezoutChain.chartOfHomog`,
  `Appendix_FixedPoint.BezoutChain.chartOfHomog_mul`,
  `Appendix_FixedPoint.BezoutChain.chartOfHomog_C`,
  `Appendix_FixedPoint.BezoutChain.chartOfHomog_X_pow_prod`,
  `Appendix_FixedPoint.BezoutChain.isHomog_X_pow_prod`,
  `Appendix_FixedPoint.BezoutChain.monomial_eq_prod_univ`.
* `Mathlib/Data/Finsupp/Weight.lean`, `Finsupp.degree_eq_sum`. -/
theorem chartOfHomog_monomial (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (e : Fin (n + 2) →₀ ℕ) (c : K) (d : ℕ) (hd : e.degree = d)
    (h : (MvPolynomial.monomial e c).IsHomogeneous d) :
    chartOfHomog n K G ℓ d (MvPolynomial.monomial e c) h
      = algebraMap K (chartRing n K G ℓ) c
        * ∏ j : Fin (n + 2), (chartCoord n K G ℓ j) ^ (e j) := by
  subst hd
  have hdeg : (∑ j : Fin (n + 2), e j) = e.degree :=
    (Finsupp.degree_eq_sum e).symm
  have hprod : ((∏ j : Fin (n + 2),
      (MvPolynomial.X j : MvPolynomial (Fin (n + 2)) K) ^ (e j))).IsHomogeneous
      e.degree := by
    have h0 := isHomog_X_pow_prod n K Finset.univ (fun j => e j)
    rwa [hdeg] at h0
  have hC0 : (MvPolynomial.C c : MvPolynomial (Fin (n + 2)) K).IsHomogeneous 0 :=
    MvPolynomial.isHomogeneous_C _ c
  have hmon := monomial_eq_prod_univ n K e c
  revert h
  rw [← zero_add e.degree, hmon]
  intro h
  rw [chartOfHomog_mul _ _ _ _ _ _ _ _ hC0 hprod, chartOfHomog_C]
  congr 1
  revert hprod
  rw [← hdeg]
  intro hprod
  exact chartOfHomog_X_pow_prod n K G ℓ Finset.univ (fun j => e j) hprod

/-- Every abstract `K`-point evaluates `chartOfHomog` as evaluation at the
coordinate point `a j := φ (chartCoord j)` (monomial decomposition).


## References

* This module, `Appendix_FixedPoint.BezoutChain.chartOfHomog`,
  `Appendix_FixedPoint.BezoutChain.chartOfHomog_sum`,
  `Appendix_FixedPoint.BezoutChain.chartOfHomog_monomial`,
  `Appendix_FixedPoint.BezoutChain.monomial_eq_prod_univ`.
* `Mathlib/Algebra/MvPolynomial/Basic.lean`, `MvPolynomial.as_sum`.
* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.eval_C`,
  `MvPolynomial.eval_X`.
* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.isHomogeneous_monomial`,
  `MvPolynomial.isHomogeneous_zero`.
* `Mathlib/Data/Finsupp/Defs.lean`, `Finsupp.mem_support_iff`.
* `Mathlib/Data/Finsupp/Weight.lean`, `Finsupp.degree_eq_weight_one`.
* `Mathlib/Algebra/Algebra/Defs.lean`, `Algebra.algebraMap_self_apply`. -/
theorem phi_chartOfHomog (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (φ : chartRing n K G ℓ →ₐ[K] K) (a : Fin (n + 2) → K)
    (ha : ∀ j, φ (chartCoord n K G ℓ j) = a j)
    (d : ℕ) (p : MvPolynomial (Fin (n + 2)) K) (h : p.IsHomogeneous d) :
    φ (chartOfHomog n K G ℓ d p h) = MvPolynomial.eval a p := by
  have hmono : ∀ e : Fin (n + 2) →₀ ℕ,
      (MvPolynomial.monomial e (p.coeff e)).IsHomogeneous d := by
    intro e
    by_cases he : e ∈ p.support
    · have hsup : p.coeff e ≠ 0 := Finsupp.mem_support_iff.mp he
      have hwt : Finsupp.weight (fun _ ↦ (1 : ℕ)) e = d := h hsup
      have hde : e.degree = d := by
        rw [Finsupp.degree_eq_weight_one]
        exact hwt
      exact MvPolynomial.isHomogeneous_monomial (p.coeff e) hde
    · have h0 : p.coeff e = 0 := by
        by_contra hne
        exact he (Finsupp.mem_support_iff.mpr hne)
      rw [MvPolynomial.monomial_eq_zero.mpr h0]
      exact MvPolynomial.isHomogeneous_zero _ _ d
  have hsum : ((∑ e ∈ p.support, MvPolynomial.monomial e (p.coeff e))).IsHomogeneous d := by
    rw [← p.as_sum]
    exact h
  have heq : chartOfHomog n K G ℓ d p h
      = chartOfHomog n K G ℓ d
        (∑ e ∈ p.support, MvPolynomial.monomial e (p.coeff e)) hsum := by
    apply Subtype.ext
    change Localization.mk (Ideal.Quotient.mk (Ideal.span (Set.range G)) p) _
      = Localization.mk (Ideal.Quotient.mk (Ideal.span (Set.range G))
        (∑ e ∈ p.support, MvPolynomial.monomial e (p.coeff e))) _
    congr 1
    congr 1
    exact p.as_sum
  rw [heq, chartOfHomog_sum _ _ _ _ _ _ _ _ hmono, map_sum]
  conv_rhs => rw [p.as_sum]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro e he
  have hde : e.degree = d := by
    have hsup : p.coeff e ≠ 0 := Finsupp.mem_support_iff.mp he
    have hwt : Finsupp.weight (fun _ ↦ (1 : ℕ)) e = d := h hsup
    rw [Finsupp.degree_eq_weight_one]
    exact hwt
  rw [chartOfHomog_monomial _ _ _ _ _ _ _ hde, map_mul, map_prod,
    monomial_eq_prod_univ, map_mul, map_prod]
  congr 1
  · have hcomm := AlgHom.commutes φ (p.coeff e)
    rw [MvPolynomial.eval_C]
    rw [hcomm]
    exact Algebra.algebraMap_self_apply _
  · apply Finset.prod_congr rfl
    intro j _
    rw [map_pow, ha j, map_pow, MvPolynomial.eval_X]

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
open scoped BigOperators

/-! ## Surjectivity closure: point transfer from quadrics

This section proves `ChartPointTransfer` genuinely for quadrics systems,
closing the `hsurj` half of `hbij` down to `[IsAlgClosed K, hfinA, hG]`.
Given an abstract `K`-point `φ`, the coordinate point
`a j := φ (chartCoord j)` has `ℓ(a) = 1` (`eval_coordPoint_mkLin`, via
`chartCoord_sum_lin`), vanishes on every equation
(`coordPoint_eval_eq_zero_of_quadrics`, via `phi_chartOfHomog` and
`mk (G i) = 0`), hence defines a projective locus point
(`coordPoint_mem_locus`, via `eval_smul_compat_cf` for scale-invariance of
the equations); its kernel is the evaluation ideal
(`ker_eq_pointIdeal_of_phi`), transferred to the canonical representative
by scale-invariance (`pointIdeal_smul_cf`).

Conditional on exactly `[IsAlgClosed K, hfinA, hG]`
(`chartMaxSpecSurj_forall` below is the exact `FinalResiduals.hsurj` ∀-shape
with these hypotheses; `hG` is genuinely necessary — without homogeneity
the chart does not see the equations in degree `0`).
-/

/-- The coordinate point has `ℓ(a) = 1` (push `chartCoord_sum_lin` through
`φ`).


## References

* This module, `Appendix_FixedPoint.BezoutChain.chartCoord`,
  `Appendix_FixedPoint.BezoutChain.chartCoord_sum_lin`.
* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.eval_C`,
  `MvPolynomial.eval_X`.
* `Mathlib/Algebra/Algebra/Defs.lean`, `Algebra.smul_def`,
  `Algebra.algebraMap_self_apply`. -/
theorem eval_coordPoint_mkLin (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (φ : chartRing n K G ℓ →ₐ[K] K) (a : Fin (n + 2) → K)
    (ha : ∀ j, φ (chartCoord n K G ℓ j) = a j) :
    MvPolynomial.eval a (mkLin n K ℓ) = 1 := by
  have h1 : MvPolynomial.eval a (mkLin n K ℓ)
      = ∑ j : Fin (n + 2), ℓ j * a j := by
    unfold mkLin
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  rw [h1]
  have h2 : (∑ j : Fin (n + 2), ℓ j * a j)
      = φ (∑ j : Fin (n + 2), ℓ j • chartCoord n K G ℓ j) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hsm : φ (ℓ j • chartCoord n K G ℓ j) = ℓ j * a j := by
      have hsd : ℓ j • chartCoord n K G ℓ j
          = algebraMap K (chartRing n K G ℓ) (ℓ j) * chartCoord n K G ℓ j :=
        Algebra.smul_def (A := chartRing n K G ℓ) (ℓ j) _
      rw [hsd, map_mul, AlgHom.commutes, Algebra.algebraMap_self_apply, ha j]
    exact hsm.symm
  rw [h2, chartCoord_sum_lin, map_one]

/-- The coordinate point vanishes on every quadric equation (the equation
is `0` in the chart, and `φ` reads off evaluation).

Conditional on exactly `[hG]`.

## References

* This module, `Appendix_FixedPoint.BezoutChain.chartOfHomog`,
  `Appendix_FixedPoint.BezoutChain.phi_chartOfHomog`.
* `Mathlib/RingTheory/Ideal/Quotient/Defs.lean`,
  `Ideal.Quotient.eq_zero_iff_mem`.
* `Mathlib/RingTheory/Ideal/Span.lean`, `Ideal.subset_span`.
* `Mathlib/GroupTheory/MonoidLocalization/Basic.lean`,
  `Localization.mk_zero`.
* `Mathlib/Algebra/Algebra/Subalgebra/Basic.lean`,
  `Subalgebra.coe_zero`. -/
theorem coordPoint_eval_eq_zero_of_quadrics (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hG : ∀ i, (G i).IsHomogeneous 2)
    (φ : chartRing n K G ℓ →ₐ[K] K) (a : Fin (n + 2) → K)
    (ha : ∀ j, φ (chartCoord n K G ℓ j) = a j)
    (i : Fin (n + 1)) :
    MvPolynomial.eval a (G i) = 0 := by
  have hXi : chartOfHomog n K G ℓ 2 (G i) (hG i) = 0 := by
    apply Subtype.ext
    change Localization.mk (Ideal.Quotient.mk (Ideal.span (Set.range G)) (G i)) _
      = _
    have hmem : Ideal.Quotient.mk (Ideal.span (Set.range G)) (G i) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span ⟨i, rfl⟩
    rw [hmem, Subalgebra.coe_zero]
    exact Localization.mk_zero _
  have hφ := phi_chartOfHomog n K G ℓ φ a ha 2 (G i) (hG i)
  rw [hXi, map_zero] at hφ
  exact hφ.symm

/-- The coordinate point is nonzero (it has `ℓ(a) = 1`).


## References

* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.eval_C`,
  `MvPolynomial.eval_X`. -/
theorem coordPoint_ne_zero (n : ℕ) (K : Type*) [Field K]
    (ℓ : Fin (n + 2) → K) (a : Fin (n + 2) → K)
    (hL : MvPolynomial.eval a (mkLin n K ℓ) = 1) :
    a ≠ 0 := by
  intro h0
  rw [h0] at hL
  have h00 : MvPolynomial.eval (0 : Fin (n + 2) → K) (mkLin n K ℓ) = 0 := by
    unfold mkLin
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro j _
    rw [map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, Pi.zero_apply, mul_zero]
  rw [h00] at hL
  exact one_ne_zero hL.symm

/-- The coordinate point defines a projective locus point (equations are
scale-invariant by homogeneity).

Conditional on exactly `[hG]`.

## References

* This module, `Appendix_FixedPoint.BezoutChain.eval_smul_compat_cf`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Statement.Definitions`,
  `Appendix_FixedPoint.BezoutChain.vanishingLocus`.
* `Mathlib/LinearAlgebra/Projectivization/Basic.lean`,
  `Projectivization.mk_eq_mk_iff'`. -/
theorem coordPoint_mem_locus (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hG : ∀ i, (G i).IsHomogeneous 2)
    (a : Fin (n + 2) → K) (ha0 : a ≠ 0)
    (hvG : ∀ i, MvPolynomial.eval a (G i) = 0) :
    Projectivization.mk K a ha0 ∈ vanishingLocus n K G := by
  intro v hv hmk i
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' K v a hv ha0).mp hmk
  have hsm := eval_smul_compat_cf (hG i) c a
  rw [← hc, hsm, hvG i, mul_zero]

/-- The kernel of `φ` is the evaluation ideal at the coordinate point
(`φ` and `chartEval a` agree on every presented fraction).


## References

* This module, `Appendix_FixedPoint.BezoutChain.chartOfHomog`,
  `Appendix_FixedPoint.BezoutChain.phi_chartOfHomog`,
  `Appendix_FixedPoint.BezoutChain.chartEval_chartOfHomog`,
  `Appendix_FixedPoint.BezoutChain.eval_coordPoint_mkLin`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Statement.Definitions`,
  `Appendix_FixedPoint.BezoutChain.pointIdeal`,
  `Appendix_FixedPoint.BezoutChain.chartEval`. -/
theorem ker_eq_pointIdeal_of_phi (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (φ : chartRing n K G ℓ →ₐ[K] K) (a : Fin (n + 2) → K)
    (ha : ∀ j, φ (chartCoord n K G ℓ j) = a j)
    (hvG : ∀ i, MvPolynomial.eval a (G i) = 0)
    (hℓ : MvPolynomial.eval a (mkLin n K ℓ) ≠ 0) :
    RingHom.ker φ.toRingHom = pointIdeal n K G ℓ a hvG hℓ := by
  unfold pointIdeal
  have hagree : ∀ x : chartRing n K G ℓ,
      φ x = chartEval n K G ℓ a hvG hℓ x := by
    intro x
    obtain ⟨val, d, s, ⟨p, hphom, hpeq⟩, e⟩ := x
    have hx : (⟨val, d, s, ⟨p, hphom, hpeq⟩, e⟩ : chartRing n K G ℓ)
        = chartOfHomog n K G ℓ d p hphom := by
      apply Subtype.ext
      change val = Localization.mk
        (Ideal.Quotient.mk (Ideal.span (Set.range G)) p) _
      rw [e, hpeq]
    rw [hx, phi_chartOfHomog n K G ℓ φ a ha d p hphom, chartEval_chartOfHomog]
    have hL1 : MvPolynomial.eval a (mkLin n K ℓ) = 1 :=
      eval_coordPoint_mkLin n K G ℓ φ a ha
    rw [hL1, one_pow, div_one]
  ext x
  simp only [RingHom.mem_ker]
  change φ x = 0 ↔ chartEval n K G ℓ a hvG hℓ x = 0
  rw [hagree x]

/-- Point transfer for quadrics: every abstract `K`-point is geometric.

Conditional on exactly `[hG]`.

## References

* This module, `Appendix_FixedPoint.BezoutChain.eval_coordPoint_mkLin`,
  `Appendix_FixedPoint.BezoutChain.coordPoint_eval_eq_zero_of_quadrics`,
  `Appendix_FixedPoint.BezoutChain.coordPoint_ne_zero`,
  `Appendix_FixedPoint.BezoutChain.coordPoint_mem_locus`,
  `Appendix_FixedPoint.BezoutChain.ker_eq_pointIdeal_of_phi`,
  `Appendix_FixedPoint.BezoutChain.pointIdeal_smul_cf`,
  `Appendix_FixedPoint.BezoutChain.eval_smul_compat_cf`,
  `Appendix_FixedPoint.BezoutChain.mkLin_isHomogeneous`,
  `Appendix_FixedPoint.BezoutChain.ChartPointTransfer`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.LocalMultiplicity`,
  `Appendix_FixedPoint.BezoutChain.locLocusFinset`.
* `Mathlib/LinearAlgebra/Projectivization/Basic.lean`,
  `Projectivization.mk_eq_mk_iff'`, `Projectivization.mk_rep`.
* `Mathlib/Data/Set/Finite/Basic.lean`, `Set.Finite.mem_toFinset`. -/
theorem chartPointTransfer_of_quadrics (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hfin : (vanishingLocus n K G).Finite)
    (hc : ChartNonvanishing n K G ℓ)
    (hG : ∀ i, (G i).IsHomogeneous 2) :
    ChartPointTransfer n K G ℓ hfin hc := by
  intro φ
  set a : Fin (n + 2) → K := fun j => φ (chartCoord n K G ℓ j) with hadef
  have ha : ∀ j, φ (chartCoord n K G ℓ j) = a j := fun j => rfl
  have hL1 : MvPolynomial.eval a (mkLin n K ℓ) = 1 :=
    eval_coordPoint_mkLin n K G ℓ φ a ha
  have hℓ : MvPolynomial.eval a (mkLin n K ℓ) ≠ 0 := by
    rw [hL1]
    exact one_ne_zero
  have hvG : ∀ i, MvPolynomial.eval a (G i) = 0 :=
    fun i => coordPoint_eval_eq_zero_of_quadrics n K G ℓ hG φ a ha i
  have ha0 : a ≠ 0 := coordPoint_ne_zero n K ℓ a hL1
  have hmem : Projectivization.mk K a ha0 ∈ vanishingLocus n K G :=
    coordPoint_mem_locus n K G hG a ha0 hvG
  have hmemF : Projectivization.mk K a ha0 ∈ locLocusFinset n K G hfin :=
    hfin.mem_toFinset.mpr hmem
  have hrep_eq : Projectivization.mk K (Projectivization.mk K a ha0).rep
      (Projectivization.mk K a ha0).rep_nonzero
      = Projectivization.mk K a ha0 :=
    Projectivization.mk_rep _
  obtain ⟨c, hcrep⟩ := (Projectivization.mk_eq_mk_iff' K _ _ _ _).mp hrep_eq
  have hc0 : c ≠ 0 := by
    intro h0
    have hrep0 : (Projectivization.mk K a ha0).rep = 0 := by
      rw [← hcrep, h0, zero_smul]
    exact (Projectivization.mk K a ha0).rep_nonzero hrep0
  have hvGw : ∀ i, MvPolynomial.eval (c • a) (G i) = 0 := by
    intro i
    rw [eval_smul_compat_cf (hG i) c a, hvG i, mul_zero]
  have hℓw : MvPolynomial.eval (c • a) (mkLin n K ℓ) ≠ 0 := by
    have h1 := eval_smul_compat_cf (mkLin_isHomogeneous n K ℓ) c a
    rw [h1, hL1, pow_one, mul_one]
    exact hc0
  have hker : RingHom.ker φ.toRingHom
      = pointIdeal n K G ℓ a hvG hℓ :=
    ker_eq_pointIdeal_of_phi n K G ℓ φ a ha hvG hℓ
  have hsm : pointIdeal n K G ℓ a hvG hℓ
      = pointIdeal n K G ℓ (c • a) hvGw hℓw :=
    (pointIdeal_smul_cf n K G ℓ a c hvG hℓ hvGw hℓw).symm
  refine ⟨⟨Projectivization.mk K a ha0, hmemF⟩, ?_⟩
  rw [hker, hsm]
  clear hsm
  revert hvGw hℓw
  rw [hcrep]
  intro hvGw' hℓw'
  rfl

/-- `hsurj` ∀-form, closed: the exact `FinalResiduals.hsurj` shape from
`[IsAlgClosed K, hfinA, hG]`.

Conditional on exactly `[IsAlgClosed K, hfinA, hG]`.

## References

* This module, `Appendix_FixedPoint.BezoutChain.chartMaxSpecSurj_of_transfer`,
  `Appendix_FixedPoint.BezoutChain.chartPointTransfer_of_quadrics`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.FinalDischargeHub`,
  `Appendix_FixedPoint.BezoutChain.FinalResiduals`
  (consumer of this binder shape; cited, not imported). -/
theorem chartMaxSpecSurj_forall (n : ℕ) (K : Type*) [Field K] [IsAlgClosed K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hfinA : Module.Finite K (chartRing n K G ℓ))
    (hG : ∀ i, (G i).IsHomogeneous 2) :
    ∀ (hfin : (vanishingLocus n K G).Finite)
      (hc : ChartNonvanishing n K G ℓ),
      ChartMaxSpecSurj n K G ℓ hfin hc := by
  intro hfin hc
  exact chartMaxSpecSurj_of_transfer n K G ℓ hfin hc hfinA
    (chartPointTransfer_of_quadrics n K G ℓ hfin hc hG)

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
open scoped BigOperators

/-! ## Minimal-prime avoidance for the section form (minimal-avoidance lane)

This section proves the `R1RegularSection.SecFormAvoidsMinimal` residual — "`z̄`
avoids each minimal prime of the cone" — conditionally on its narrowest exact
MaxSpec witness (`ConeMinAvoidWitness`): every minimal prime of the cone sits
below a maximal ideal missing `ℓ̄`. The implication
(`minAvoid_of_maxSpecWitness`, general `G`/`ℓ` form; the `mkSystem`/secForm-`ℓ`
instance `secFormAvoidsMinimal_of_witness` is stated as a definitional twin of
`R1RegularSection.SecFormAvoidsMinimal`, which this file cannot import — `R1RegularSection`
imports this file — so the consumer applies it by unfolding
`R1RegularSection.secForm`) is three lines: `z̄ ∈ Q ≤ m` contradicts `z̄ ∉ m`.

Why the cone-side `MaxSpec` (rather than the chart-side `locusToMaxSpec`
bijection above): the chart only sees primes missing `ℓ̄`, while the residual
is exactly about controlling the primes that may contain it. The cone-side
maximal ideals are the Nullstellensatz-correspondence side (affine cone
points): discharging `ConeMinAvoidWitness` is the Nullstellensatz argument
below (`coneMinAvoidWitnessPrime_discharge`)
(strong Nullstellensatz: a minimal prime contained in `V(z)` has vanishing
locus in `{origin}` under `cutsOutOrigin`, forcing it to be the origin's
maximal ideal, against the `z`-axis line below it).

Sharpness: no unconditional proof exists — at `F = 0`, `(z)` is a minimal
prime of `k[x,z]/(zx)` containing `z̄` (paper proof: the quotient by `(z)` is
`k[x]`, so it is prime; a prime `Q` with `(zx) ⊆ Q ⊆ (z)` and `z ∉ Q` would
contain every `xᵢ` by primality, but `x₀ ∉ (z)`). That refutation is
formalized downstream (`R1RegularSection.secForm_not_minAvoid_zero`), and
`R1RegularSection.havoid_secForm_necess_ne_zero` already forces `∃ i, F i ≠ 0`.

Conditional on exactly `[ConeMinAvoidWitness n K (mkSystem n K F)
secForm-ℓ]`. Consumer: `R1RegularSection.havoid_secForm_of_noEmbedded_of_minAvoid`
(combine with `ConeNoEmbedded` for `havoid`).
-/

/-- Narrowest exact residual for minimal-prime avoidance: every minimal prime
of the cone `S = coneQuotient n K G` sits below a maximal ideal (a cone-side
`MaxSpec` point, the Nullstellensatz-correspondence side) missing `ℓ̄`. The
Krull half (a maximal above exists) is unconditional
(`exists_maximal_above_prime_cone`); the residual content is choosing it off
the hyperplane.

## References

* `Mathlib/RingTheory/Spectrum/Maximal/Defs.lean`, `MaximalSpectrum`,
  `MaximalSpectrum.asIdeal`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Statement.Definitions`,
  `Appendix_FixedPoint.BezoutChain.coneQuotient`,
  `Appendix_FixedPoint.BezoutChain.mkLin`.

Sharpness : this literal form is false — refuted at `n = 0`,
`F = (X₀²)` by the non-prime `Q = span{z̄}`
(`coneMinAvoidWitness_false_n0`, which must keep referring to this literal
def). Downstream must use the patched `ConeMinAvoidWitnessPrime` below
(which adds the `Q.IsPrime` hypothesis). -/
def ConeMinAvoidWitness (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) : Prop :=
  ∀ Q : Ideal (coneQuotient n K G),
    (∀ Q' : Ideal (coneQuotient n K G), Q'.IsPrime → Q' ≤ Q → Q ≤ Q') →
    ∃ m : MaximalSpectrum (coneQuotient n K G),
      Q ≤ m.asIdeal ∧
        Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)
          ∉ m.asIdeal

/-- Krull step (unconditional): every prime of the cone sits below a maximal
ideal. Isolates the residual content of `ConeMinAvoidWitness` (the maximal
can be chosen missing `ℓ̄`).


## References

* `Mathlib/RingTheory/Ideal/Maximal.lean`, `Ideal.exists_le_maximal`
  (available via the public import of `Spectrum.Maximal.Defs`, already
  imported above — no new import).
* `Mathlib/RingTheory/Ideal/Prime.lean`, `Ideal.IsPrime.ne_top`. -/
theorem exists_maximal_above_prime_cone (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (Q : Ideal (coneQuotient n K G)) (hQ : Q.IsPrime) :
    ∃ m : MaximalSpectrum (coneQuotient n K G), Q ≤ m.asIdeal := by
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal Q hQ.ne_top
  exact ⟨⟨M, hM⟩, hle⟩

/-- Minimal-prime avoidance from the MaxSpec witness (general `G`/`ℓ` form):
if every minimal prime sits below a maximal ideal missing `ℓ̄`, then `ℓ̄`
avoids every minimal prime (`z̄ ∈ Q ≤ m` contradicts `z̄ ∉ m`).

Conditional on exactly `[ConeMinAvoidWitness n K G ℓ]`. -/
theorem minAvoid_of_maxSpecWitness (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hwit : ConeMinAvoidWitness n K G ℓ) :
    ∀ Q : Ideal (coneQuotient n K G),
      (∀ Q' : Ideal (coneQuotient n K G), Q'.IsPrime → Q' ≤ Q → Q ≤ Q') →
      Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ) ∉ Q := by
  intro Q hmin
  obtain ⟨m, hle, hmiss⟩ := hwit Q hmin
  exact fun hmem => hmiss (hle hmem)

/-- The `SecFormAvoidsMinimal` residual, discharged: the exact definitional
twin of `R1RegularSection.SecFormAvoidsMinimal` (same minimality predicate shape;
`Pi.single (Fin.last _) 1` is `R1RegularSection.secForm` by definition), from the
cone-side MaxSpec witness. Consumer `R1RegularSection` (which imports this file)
applies this by unfolding `secForm`, then feeds
`havoid_secForm_of_noEmbedded_of_minAvoid` together with `ConeNoEmbedded`.

Conditional on exactly `[ConeMinAvoidWitness n K (mkSystem n K F)
secForm-ℓ]`.

## References

* This module, `Appendix_FixedPoint.BezoutChain.minAvoid_of_maxSpecWitness`,
  `Appendix_FixedPoint.BezoutChain.ConeMinAvoidWitness`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Statement.Definitions`,
  `Appendix_FixedPoint.BezoutChain.mkSystem`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.R1RegularSection`,
  `Appendix_FixedPoint.BezoutChain.R1RegularSection.secForm`,
  `Appendix_FixedPoint.BezoutChain.R1RegularSection.SecFormAvoidsMinimal` (consumer twin; cited, not
  imported — reverse import would cycle). -/
theorem secFormAvoidsMinimal_of_witness (n : ℕ) (K : Type*) [Field K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hwit : ConeMinAvoidWitness n K (mkSystem n K F)
      (Pi.single (Fin.last (n + 1)) 1)) :
    ∀ Q : Ideal (coneQuotient n K (mkSystem n K F)),
      (∀ Q' : Ideal (coneQuotient n K (mkSystem n K F)),
        Q'.IsPrime → Q' ≤ Q → Q ≤ Q') →
      Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))
        (mkLin n K (Pi.single (Fin.last (n + 1)) 1)) ∉ Q :=
  minAvoid_of_maxSpecWitness n K (mkSystem n K F) _ hwit

/-- Patched MaxSpec witness: the literal `ConeMinAvoidWitness` is false as
stated (refuted at `n = 0`, `F = (X₀²)` by the non-prime `Q = span{z̄}` —
see `coneMinAvoidWitness_false_n0`, which keeps referring to the literal
def). The patch requires `Q.IsPrime`: every prime minimal `Q` sits below a
maximal ideal missing `ℓ̄`. This is exactly what downstream consumes
(`R1RegularSection` applies avoidance only at associated, hence prime, ideals),
and it is discharged end-to-end in-file by
`coneMinAvoidWitnessPrime_discharge` (via `coneMinAvoidWitness_prime`).

Status: discharged unconditionally (from `[IsAlgClosed K, hF, hcut]`) for
`mkSystem`/secForm-`ℓ` by `coneMinAvoidWitnessPrime_discharge`.

## References

* This module, `Appendix_FixedPoint.BezoutChain.ConeMinAvoidWitness` (literal, refuted),
  `Appendix_FixedPoint.BezoutChain.coneMinAvoidWitness_false_n0`,
  `Appendix_FixedPoint.BezoutChain.coneMinAvoidWitness_prime`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Statement.Definitions`,
  `Appendix_FixedPoint.BezoutChain.coneQuotient`,
  `Appendix_FixedPoint.BezoutChain.mkLin`. -/
def ConeMinAvoidWitnessPrime (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) : Prop :=
  ∀ Q : Ideal (coneQuotient n K G),
    Q.IsPrime →
    (∀ Q' : Ideal (coneQuotient n K G), Q'.IsPrime → Q' ≤ Q → Q ≤ Q') →
    ∃ m : MaximalSpectrum (coneQuotient n K G),
      Q ≤ m.asIdeal ∧
        Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)
          ∉ m.asIdeal

/-- Minimal-prime avoidance from the patched MaxSpec witness (general
`G`/`ℓ` form): prime-indexed twin of `minAvoid_of_maxSpecWitness`.

Conditional on exactly `[ConeMinAvoidWitnessPrime n K G ℓ]`. -/
theorem minAvoid_of_maxSpecWitness_prime (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hwit : ConeMinAvoidWitnessPrime n K G ℓ) :
    ∀ Q : Ideal (coneQuotient n K G),
      Q.IsPrime →
      (∀ Q' : Ideal (coneQuotient n K G), Q'.IsPrime → Q' ≤ Q → Q ≤ Q') →
      Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ) ∉ Q := by
  intro Q hQ hmin
  obtain ⟨m, hle, hmiss⟩ := hwit Q hQ hmin
  exact fun hmem => hmiss (hle hmem)

/-- The prime-indexed `SecFormAvoidsMinimal` residual, discharged: twin of
`secFormAvoidsMinimal_of_witness` under the `Q.IsPrime` patch. Consumer
`R1RegularSection` (which imports this file) applies this by unfolding `secForm`.

Conditional on exactly `[ConeMinAvoidWitnessPrime n K (mkSystem n K F)
secForm-ℓ]`; discharged by `coneMinAvoidWitnessPrime_discharge`.

## References

* This module, `Appendix_FixedPoint.BezoutChain.minAvoid_of_maxSpecWitness_prime`,
  `Appendix_FixedPoint.BezoutChain.ConeMinAvoidWitnessPrime`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Statement.Definitions`,
  `Appendix_FixedPoint.BezoutChain.mkSystem`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.R1RegularSection`,
  `Appendix_FixedPoint.BezoutChain.R1RegularSection.secForm`
  (consumer twin; cited, not imported — reverse import would cycle). -/
theorem secFormAvoidsMinimal_of_witness_prime (n : ℕ) (K : Type*) [Field K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hwit : ConeMinAvoidWitnessPrime n K (mkSystem n K F)
      (Pi.single (Fin.last (n + 1)) 1)) :
    ∀ Q : Ideal (coneQuotient n K (mkSystem n K F)),
      Q.IsPrime →
      (∀ Q' : Ideal (coneQuotient n K (mkSystem n K F)),
        Q'.IsPrime → Q' ≤ Q → Q ≤ Q') →
      Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))
        (mkLin n K (Pi.single (Fin.last (n + 1)) 1)) ∉ Q :=
  minAvoid_of_maxSpecWitness_prime n K (mkSystem n K F) _ hwit

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
/-! ## ConeMinAvoid discharge: strong-NS component witness + axis-prime witness

This section discharges the mathematical content of the conditional
`ConeMinAvoidWitness` residual — in prime-indexed form — via the two missing
witnesses from the section sketch:

* **Witness 1 (strong-NS component-in-`V(z)`):** a prime `Q` of the `mkSystem`
  cone with `z̄ ∈ Q` equals the origin maximal ideal
  (`component_mem_vz_eq_originMap`, via `component_mem_vz_locus_subset_origin`
  + strong Nullstellensatz). Needs `[IsAlgClosed K]`, `hF`, `cutsOutOrigin_cf`.
* **Witness 2 (z-axis axis-prime):** the axis ideal `(x̄)` is prime and sits
  strictly below the origin maximal on the cone
  (`axisPrimeCone_below_origin`, via the `ker φ` computation
  `axisIdeal_eq_ker`). Needs `hF`.

Together they give minimal-prime avoidance for prime ideals
(`secFormAvoidsMinimal_prime`) and the prime-indexed MaxSpec witness
(`coneMinAvoidWitness_prime`): every prime minimal `Q` sits below a maximal
ideal missing `z̄` (point-picking via strong Nullstellensatz + `coneEval`).
This prime-indexed form is exactly what downstream consumes:
`R1RegularSection.havoid_secForm_of_noEmbedded_of_minAvoid` applies the avoidance
predicate only at associated (hence prime) ideals.

Sharpness / blocker for the literal defs: the stated `ConeMinAvoidWitness`
and `R1RegularSection.SecFormAvoidsMinimal` quantify over all `Q` (the minimality
predicate does not require `Q` prime), and are false as stated — refuted at
`n = 0`, `F = (X₀²)` by `Q = span{z̄}` (`coneMinAvoidWitness_false_n0`):
`z̄ ∈ Q` while no prime lies strictly below `Q` (a prime below would contain
`X₀` or `X₀ - X₁`, both of which miss `span{z, G₀}` by a linear-part
computation). The `Q.IsPrime` patch has proved in-file as
`ConeMinAvoidWitnessPrime` (with prime-indexed consumers
`minAvoid_of_maxSpecWitness_prime` / `secFormAvoidsMinimal_of_witness_prime`);
the prime-indexed theorems here discharge it end-to-end
(`coneMinAvoidWitnessPrime_discharge`).

`R1RegularSection` facts are mirrored as `-cf` twins (that file imports this one,
so the reverse import would cycle).

`[IsAlgClosed K, hF, hcut]`); the literal `ConeMinAvoidWitness` is refuted.

## References

* `Mathlib/RingTheory/Nullstellensatz.lean`,
  `MvPolynomial.IsPrime.vanishingIdeal_zeroLocus`, `zeroLocus`,
  `vanishingIdeal`.
* `Mathlib/RingTheory/Ideal/Maps.lean`, `Ideal.comap_isPrime`,
  `Ideal.map_comap_of_surjective`, `RingHom.ker_isPrime`,
  `RingHom.ker_isMaximal_of_surjective`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Statement.Definitions`,
  `Appendix_FixedPoint.BezoutChain.coneEval`,
  `Appendix_FixedPoint.BezoutChain.coneEval_C`, `Appendix_FixedPoint.BezoutChain.mkSystem`,
  `Appendix_FixedPoint.BezoutChain.mkLin`.
-/

section MinAvoidDischarge

variable (n : ℕ) (K : Type*) [Field K]

/-- `mkLin` of the `z`-form is the `z` variable (mirror of
`R1RegularSection.mkLin_secForm`; this file cannot import `R1RegularSection` — reverse
import would cycle). -/
theorem mkLin_zForm_cf :
    mkLin n K (Pi.single (Fin.last (n + 1)) 1)
      = MvPolynomial.X (Fin.last (n + 1)) := by
  unfold mkLin
  rw [Finset.sum_eq_single (Fin.last (n + 1))
    (fun j _ hlj => by rw [Pi.single_eq_of_ne hlj]; simp)
    (fun hcon => absurd (Finset.mem_univ _) hcon)]
  simp [Pi.single_eq_same]

/-- Evaluation of the `z`-form reads off the `z` coordinate (mirror of
`R1RegularSection.eval_mkLin_secForm`). -/
theorem eval_mkLin_zForm_cf (v : Fin (n + 2) → K) :
    MvPolynomial.eval v (mkLin n K (Pi.single (Fin.last (n + 1)) 1))
      = v (Fin.last (n + 1)) := by
  rw [mkLin_zForm_cf, MvPolynomial.eval_X]

/-- `mkSystem` evaluation splits as `Fᵢ(x) − z·xᵢ` (mirror of
`R1RegularSection.eval_mkSystem_split`). -/
theorem eval_mkSystem_split_cf
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (i : Fin (n + 1)) (v : Fin (n + 2) → K) :
    MvPolynomial.eval v (mkSystem n K F i)
      = MvPolynomial.eval (fun j => v (Fin.castSucc j)) (F i)
        - v (Fin.last (n + 1)) * v (Fin.castSucc i) := by
  unfold mkSystem
  rw [map_sub, MvPolynomial.eval_rename, map_mul,
    MvPolynomial.eval_X, MvPolynomial.eval_X]
  rfl

/-- Twin of `R1RegularSection.cutsOutOrigin` (that file cannot be imported here):
the input forms cut out the origin. -/
def cutsOutOrigin_cf (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K) : Prop :=
  ∀ x : Fin (n + 1) → K, x ≠ 0 → ∃ i, MvPolynomial.eval x (F i) ≠ 0

/-- Witness 1, locus half (strong-NS component-in-`V(z)`): a cone prime
containing `z̄` has vanishing locus inside `{origin}`. Given `v` in the
locus, `G` and `z` vanish at `v`, so `x = v ∘ castSucc` is a common zero of
`F`, hence `0` by `hcut`; with `z = 0` this forces `v = 0`. -/
theorem component_mem_vz_locus_subset_origin
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hcut : cutsOutOrigin_cf n K F)
    (Q : Ideal (coneQuotient n K (mkSystem n K F)))
    (hz : Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))
      (mkLin n K (Pi.single (Fin.last (n + 1)) 1)) ∈ Q) :
    MvPolynomial.zeroLocus K
        (Ideal.comap (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))) Q)
      ⊆ {0} := by
  intro v hv
  rw [MvPolynomial.mem_zeroLocus_iff] at hv
  have hGv : ∀ i, MvPolynomial.eval v (mkSystem n K F i) = 0 := by
    intro i
    have hmem : mkSystem n K F i
        ∈ Ideal.comap (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))) Q := by
      change Ideal.Quotient.mk _ _ ∈ Q
      have h0 : Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))
          (mkSystem n K F i) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
      rw [h0]
      exact Submodule.zero_mem _
    exact hv _ hmem
  have hzv : MvPolynomial.eval v (mkLin n K (Pi.single (Fin.last (n + 1)) 1)) = 0 :=
    hv _ hz
  rw [eval_mkLin_zForm_cf] at hzv
  have hx0 : ∀ i, MvPolynomial.eval (fun j => v (Fin.castSucc j)) (F i) = 0 := by
    intro i
    have hGi := hGv i
    rw [eval_mkSystem_split_cf, hzv, zero_mul, sub_zero] at hGi
    exact hGi
  have hxeq : (fun j => v (Fin.castSucc j)) = 0 := by
    by_contra hne
    obtain ⟨i, hi⟩ := hcut _ hne
    exact hi (hx0 i)
  have hv0 : v = 0 := by
    funext j
    by_cases hjl : j = Fin.last (n + 1)
    · subst hjl
      exact hzv
    · have hlt : j.val < n + 1 := by
        have h1 := j.2
        have h2 : j.val ≠ n + 1 := fun he => hjl (Fin.ext he)
        omega
      have hcast : Fin.castSucc ⟨j.val, hlt⟩ = j := Fin.ext rfl
      have h0j : v (Fin.castSucc ⟨j.val, hlt⟩) = (0 : Fin (n + 1) → K) ⟨j.val, hlt⟩ :=
        congrFun hxeq ⟨j.val, hlt⟩
      rw [hcast] at h0j
      simpa using h0j
  exact Set.mem_singleton_iff.mpr hv0

/-- Witness 1, identification half: the preimage prime equals the origin's
vanishing ideal, by strong Nullstellensatz (`P = V(Z)`, `Z ⊆ {0}`,
`0 ∈ Z` since `Z = ∅` would force `P = ⊤`). -/
theorem component_mem_vz_eq_originVanishing [IsAlgClosed K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hcut : cutsOutOrigin_cf n K F)
    (Q : Ideal (coneQuotient n K (mkSystem n K F)))
    (hQ : Q.IsPrime)
    (hz : Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))
      (mkLin n K (Pi.single (Fin.last (n + 1)) 1)) ∈ Q) :
    Ideal.comap (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))) Q
      = MvPolynomial.vanishingIdeal K ({0} : Set (Fin (n + 2) → K)) := by
  have hP : (Ideal.comap (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))) Q).IsPrime :=
    Ideal.comap_isPrime (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))) (H := hQ)
  have hNS : MvPolynomial.vanishingIdeal K (MvPolynomial.zeroLocus K
      (Ideal.comap (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))) Q))
      = Ideal.comap (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))) Q :=
    MvPolynomial.IsPrime.vanishingIdeal_zeroLocus _ (h := hP)
  have hsub := component_mem_vz_locus_subset_origin n K F hcut Q hz
  have hne : MvPolynomial.zeroLocus K
      (Ideal.comap (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))) Q) ≠ ∅ := by
    intro hempty
    rw [hempty, MvPolynomial.vanishingIdeal_empty] at hNS
    exact hP.ne_top hNS.symm
  obtain ⟨v, hv⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have hv0 : v = 0 := Set.mem_singleton_iff.mp (hsub hv)
  subst hv0
  have hZ : MvPolynomial.zeroLocus K
      (Ideal.comap (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))) Q) = {0} :=
    le_antisymm hsub (by intro x hx; rw [Set.mem_singleton_iff.mp hx]; exact hv)
  rw [← hNS, hZ]

/-- Witness 1, descended: a cone prime containing `z̄` is the origin maximal
ideal (`map mk` of the origin's vanishing ideal). -/
theorem component_mem_vz_eq_originMap [IsAlgClosed K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hcut : cutsOutOrigin_cf n K F)
    (Q : Ideal (coneQuotient n K (mkSystem n K F)))
    (hQ : Q.IsPrime)
    (hz : Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))
      (mkLin n K (Pi.single (Fin.last (n + 1)) 1)) ∈ Q) :
    Q = Ideal.map (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F))))
      (MvPolynomial.vanishingIdeal K ({0} : Set (Fin (n + 2) → K))) := by
  have hW1b := component_mem_vz_eq_originVanishing n K F hcut Q hQ hz
  have hsurj : Function.Surjective
      (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))) :=
    Ideal.Quotient.mk_surjective
  have hmc := Ideal.map_comap_of_surjective _ hsurj Q
  rw [hW1b] at hmc
  exact hmc.symm

/-- The axis ideal: the span of the `x`-variables in the ambient polynomial
ring. Its quotient is the `z`-axis coordinate ring, hence it is prime
(`axisIdeal_isPrime`); it contains the `mkSystem` equations given `hF`
(`span_mkSystem_le_axis`). -/
noncomputable abbrev axisIdeal : Ideal (MvPolynomial (Fin (n + 2)) K) :=
  Ideal.span (Set.range (fun j : Fin (n + 1) => MvPolynomial.X (Fin.castSucc j)))

/-- The axis quotient map: kill the `x`-variables, keep `z` as `X 0`. Its
kernel is the axis ideal (`axisIdeal_eq_ker`). -/
noncomputable def axisQuotMap :
    MvPolynomial (Fin (n + 2)) K →+* MvPolynomial (Fin 1) K :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun j => if j = Fin.last (n + 1) then MvPolynomial.X (0 : Fin 1) else 0)

/-- Section of the axis quotient map: `X 0 ↦ X_last`. Used to show
`ker φ = axisIdeal` by induction (`p - lift (φ p)` always lies in the
axis ideal). -/
noncomputable def axisSectionLift :
    MvPolynomial (Fin 1) K →+* MvPolynomial (Fin (n + 2)) K :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun _ => MvPolynomial.X (Fin.last (n + 1)))

/-- Homogeneous quadrics lie in the span of the variables: every monomial
has a variable factor (its exponent is nonzero since the constant
coefficient vanishes). -/
theorem homog_mem_span_range_X {σ : Type*}
    (p : MvPolynomial σ K) (hp : p.IsHomogeneous 2) :
    p ∈ Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ K)) := by
  rw [MvPolynomial.as_sum p]
  exact Submodule.sum_mem _ (fun e he => by
    have hne : AddMonoidAlgebra.coeff p e ≠ 0 := MvPolynomial.mem_support_iff.mp he
    have e_ne : e ≠ 0 := by
      intro h0
      subst h0
      exact hne (hp.coeff_eq_zero (by
        have hdeg : (0 : σ →₀ ℕ).degree = 0 := by simp [Finsupp.degree]
        omega))
    obtain ⟨j, hj⟩ := Finsupp.support_nonempty_iff.mpr e_ne
    have hej : e j ≠ 0 := Finsupp.mem_support_iff.mp hj
    have h1le : 1 ≤ e j := by omega
    have hle : Finsupp.single j 1 ≤ e := Finsupp.single_le_iff.mpr h1le
    have hdecomp : e = Finsupp.single j 1 + (e - Finsupp.single j 1) := by
      ext k
      by_cases hkj : k = j
      · subst hkj
        rw [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]
        omega
      · rw [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_of_ne hkj]
        omega
    have hmon : MvPolynomial.monomial e (AddMonoidAlgebra.coeff p e)
        = MvPolynomial.X j
          * MvPolynomial.monomial (e - Finsupp.single j 1) (AddMonoidAlgebra.coeff p e) := by
      have h2 := MvPolynomial.monomial_single_add (n := j) (e := 1)
        (s := e - Finsupp.single j 1) (a := AddMonoidAlgebra.coeff p e)
      rw [← hdecomp] at h2
      rw [pow_one] at h2
      exact h2
    rw [hmon]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨j, rfl⟩))

/-- Witness 2, containment half: the `mkSystem` equations lie in the axis
ideal given `hF` (`Fᵢ(x)` by the homogeneous lemma above, `z·xᵢ`
directly). -/
theorem span_mkSystem_le_axis
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2) :
    Ideal.span (Set.range (mkSystem n K F)) ≤ axisIdeal n K := by
  rw [Ideal.span_le]
  intro y hy
  obtain ⟨i, rfl⟩ := hy
  have hFmem : MvPolynomial.rename Fin.castSucc (F i) ∈ axisIdeal n K := by
    have hFi := homog_mem_span_range_X K (F i) (hF i)
    have hmap := Ideal.mem_map_of_mem (MvPolynomial.rename Fin.castSucc) hFi
    rw [Ideal.map_span] at hmap
    have hsub : MvPolynomial.rename Fin.castSucc ''
        Set.range (MvPolynomial.X : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
        ⊆ axisIdeal n K := by
      intro z hz
      obtain ⟨w, hw, rfl⟩ := hz
      obtain ⟨j, rfl⟩ := hw
      rw [MvPolynomial.rename_X]
      exact Ideal.subset_span ⟨j, rfl⟩
    exact (Ideal.span_le.mpr hsub) hmap
  have hmem2 : MvPolynomial.X (Fin.last (n + 1)) * MvPolynomial.X (Fin.castSucc i)
      ∈ axisIdeal n K := by
    have hmem : MvPolynomial.X (Fin.castSucc i) ∈ axisIdeal n K :=
      Ideal.subset_span ⟨i, rfl⟩
    exact Ideal.mul_mem_left _ _ hmem
  have hsplit : mkSystem n K F i
      = MvPolynomial.rename Fin.castSucc (F i)
        - MvPolynomial.X (Fin.last (n + 1)) * MvPolynomial.X (Fin.castSucc i) := rfl
  rw [hsplit]
  exact sub_mem hFmem hmem2

/-- Witness 2, kernel computation: the axis ideal is `ker φ`. The reverse
inclusion is by `MvPolynomial.induction_on`: `p - lift (φ p)` always proves
in the axis ideal (the `mul_X` step splits off `(Xⱼ - lift (φ Xⱼ))`, which
is `0` at `z` and `Xⱼ` on the `x`-variables). -/
theorem axisIdeal_eq_ker :
    axisIdeal n K = RingHom.ker (axisQuotMap n K) := by
  apply le_antisymm
  · rw [Ideal.span_le]
    intro y hy
    obtain ⟨j, rfl⟩ := hy
    change MvPolynomial.X (Fin.castSucc j) ∈ RingHom.ker (axisQuotMap n K)
    rw [RingHom.mem_ker]
    simp only [axisQuotMap, MvPolynomial.eval₂Hom_X']
    rw [ite_eq_right (ne_of_lt (Fin.castSucc_lt_last j))]
  · intro g hg
    have key : ∀ p : MvPolynomial (Fin (n + 2)) K,
        p - axisSectionLift n K (axisQuotMap n K p) ∈ axisIdeal n K := by
      intro p
      refine MvPolynomial.induction_on
        (motive := fun p => p - axisSectionLift n K (axisQuotMap n K p) ∈ axisIdeal n K)
        p ?hC ?hadd ?hmulX
      · intro a
        have h1 : axisQuotMap n K (MvPolynomial.C a) = MvPolynomial.C a := by
          simp [axisQuotMap, MvPolynomial.eval₂Hom_C]
        have h2 : axisSectionLift n K (MvPolynomial.C a) = MvPolynomial.C a := by
          simp [axisSectionLift, MvPolynomial.eval₂Hom_C]
        rw [h1, h2, sub_self]
        exact Submodule.zero_mem _
      · intro p q hp hq
        have hexpand : (p + q) - axisSectionLift n K (axisQuotMap n K (p + q))
            = (p - axisSectionLift n K (axisQuotMap n K p))
              + (q - axisSectionLift n K (axisQuotMap n K q)) := by
          rw [map_add, map_add]
          ring
        rw [hexpand]
        exact add_mem hp hq
      · intro p j hp
        have hexpand : (p * MvPolynomial.X j)
              - axisSectionLift n K (axisQuotMap n K (p * MvPolynomial.X j))
            = (p - axisSectionLift n K (axisQuotMap n K p)) * MvPolynomial.X j
              + axisSectionLift n K (axisQuotMap n K p)
                * (MvPolynomial.X j
                  - axisSectionLift n K (axisQuotMap n K (MvPolynomial.X j))) := by
          rw [map_mul, map_mul]
          ring
        rw [hexpand]
        apply add_mem _ _
        · exact Ideal.mul_mem_right _ _ hp
        · apply Ideal.mul_mem_left
          by_cases hjl : j = Fin.last (n + 1)
          · subst hjl
            have h1 : axisQuotMap n K (MvPolynomial.X (Fin.last (n + 1)))
                = MvPolynomial.X (0 : Fin 1) := by
              simp [axisQuotMap, MvPolynomial.eval₂Hom_X']
            have h2 : axisSectionLift n K (MvPolynomial.X (0 : Fin 1))
                = MvPolynomial.X (Fin.last (n + 1)) := by
              simp [axisSectionLift, MvPolynomial.eval₂Hom_X']
            rw [h1, h2, sub_self]
            exact Submodule.zero_mem _
          · have h1 : axisQuotMap n K (MvPolynomial.X j) = 0 := by
              simp only [axisQuotMap, MvPolynomial.eval₂Hom_X']
              rw [ite_eq_right hjl]
            rw [h1, map_zero, sub_zero]
            have hlt : j.val < n + 1 := by
              have h1j := j.2
              have h2j : j.val ≠ n + 1 := fun he => hjl (Fin.ext he)
              omega
            have hcast : Fin.castSucc ⟨j.val, hlt⟩ = j := Fin.ext rfl
            rw [← hcast]
            exact Ideal.subset_span ⟨⟨j.val, hlt⟩, rfl⟩
    have h0 := key g
    rw [RingHom.mem_ker.mp hg, map_zero, sub_zero] at h0
    exact h0

/-- Witness 2, primality: the axis ideal is prime (kernel into a domain). -/
theorem axisIdeal_isPrime : (axisIdeal n K).IsPrime := by
  rw [axisIdeal_eq_ker]
  exact RingHom.ker_isPrime _

/-- The axis ideal vanishes at the origin. -/
theorem axisIdeal_le_originVanishing :
    axisIdeal n K
      ≤ MvPolynomial.vanishingIdeal K ({0} : Set (Fin (n + 2) → K)) := by
  rw [Ideal.span_le]
  intro y hy
  obtain ⟨j, rfl⟩ := hy
  change MvPolynomial.X (Fin.castSucc j)
    ∈ MvPolynomial.vanishingIdeal K ({0} : Set (Fin (n + 2) → K))
  rw [MvPolynomial.mem_vanishingIdeal_iff]
  intro x hx
  rw [Set.mem_singleton_iff.mp hx]
  simp [MvPolynomial.aeval_X]

/-- `z` vanishes at the origin. -/
theorem z_mem_originVanishing :
    MvPolynomial.X (Fin.last (n + 1))
      ∈ MvPolynomial.vanishingIdeal K ({0} : Set (Fin (n + 2) → K)) := by
  rw [MvPolynomial.mem_vanishingIdeal_iff]
  intro x hx
  rw [Set.mem_singleton_iff.mp hx]
  simp [MvPolynomial.aeval_X]

/-- Witness 2, on the cone: the axis prime sits below the origin maximal,
with `z̄` the separating element (`z̄` is in the maximal but not in the
axis prime). -/
theorem axisPrimeCone_below_origin
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2) :
    ∃ A : Ideal (coneQuotient n K (mkSystem n K F)), A.IsPrime
      ∧ A ≤ Ideal.map (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F))))
          (MvPolynomial.vanishingIdeal K ({0} : Set (Fin (n + 2) → K)))
      ∧ Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))
          (mkLin n K (Pi.single (Fin.last (n + 1)) 1)) ∈ Ideal.map
          (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F))))
          (MvPolynomial.vanishingIdeal K ({0} : Set (Fin (n + 2) → K)))
      ∧ Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))
          (mkLin n K (Pi.single (Fin.last (n + 1)) 1)) ∉ A := by
  have hle : Ideal.span (Set.range (mkSystem n K F))
      ≤ RingHom.ker (axisQuotMap n K) := by
    rw [← axisIdeal_eq_ker]
    exact span_mkSystem_le_axis n K F hF
  set φ' : coneQuotient n K (mkSystem n K F) →+* MvPolynomial (Fin 1) K :=
    Ideal.Quotient.lift (Ideal.span (Set.range (mkSystem n K F))) (axisQuotMap n K)
      (fun a ha => RingHom.mem_ker.mp (hle ha)) with hφ'def
  refine ⟨RingHom.ker φ', RingHom.ker_isPrime _, ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective q
    have hg0 : φ' (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F))) g) = 0 :=
      RingHom.mem_ker.mp hq
    rw [hφ'def, Ideal.Quotient.lift_mk] at hg0
    have hgker : g ∈ RingHom.ker (axisQuotMap n K) := RingHom.mem_ker.mpr hg0
    have hgax : g ∈ axisIdeal n K := by
      rw [axisIdeal_eq_ker]
      exact hgker
    have hgV : g ∈ MvPolynomial.vanishingIdeal K ({0} : Set (Fin (n + 2) → K)) :=
      axisIdeal_le_originVanishing n K hgax
    exact Ideal.mem_map_of_mem _ hgV
  · have hzV := z_mem_originVanishing n K
    have hmk : mkLin n K (Pi.single (Fin.last (n + 1)) 1)
        = MvPolynomial.X (Fin.last (n + 1)) :=
      mkLin_zForm_cf n K
    rw [hmk]
    exact Ideal.mem_map_of_mem _ hzV
  · intro hcon
    have h0 := RingHom.mem_ker.mp hcon
    rw [hφ'def, Ideal.Quotient.lift_mk] at h0
    have hmk : mkLin n K (Pi.single (Fin.last (n + 1)) 1)
        = MvPolynomial.X (Fin.last (n + 1)) :=
      mkLin_zForm_cf n K
    rw [hmk] at h0
    have h1 : axisQuotMap n K (MvPolynomial.X (Fin.last (n + 1)))
        = MvPolynomial.X (0 : Fin 1) := by
      simp [axisQuotMap, MvPolynomial.eval₂Hom_X']
    rw [h1] at h0
    exact MvPolynomial.X_ne_zero _ h0

/-- Prime-indexed minimal avoidance: a prime minimal `Q` misses `z̄`. If
`z̄ ∈ Q`, Witness 1 forces `Q` to be the origin maximal, against the axis
prime strictly below it (Witness 2) by minimality. -/
theorem secFormAvoidsMinimal_prime [IsAlgClosed K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2)
    (hcut : cutsOutOrigin_cf n K F)
    (Q : Ideal (coneQuotient n K (mkSystem n K F)))
    (hQ : Q.IsPrime)
    (hmin : ∀ Q' : Ideal (coneQuotient n K (mkSystem n K F)),
      Q'.IsPrime → Q' ≤ Q → Q ≤ Q') :
    Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))
      (mkLin n K (Pi.single (Fin.last (n + 1)) 1)) ∉ Q := by
  intro hz
  have hQeq := component_mem_vz_eq_originMap n K F hcut Q hQ hz
  obtain ⟨A, hApr, hle, hzM, hznA⟩ := axisPrimeCone_below_origin n K F hF
  have hAQ : A ≤ Q := by
    rw [hQeq]
    exact hle
  have hQA := hmin A hApr hAQ
  have hzQ : Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))
      (mkLin n K (Pi.single (Fin.last (n + 1)) 1)) ∈ Q := by
    rw [hQeq]
    exact hzM
  exact hznA (hQA hzQ)

/-- Prime-indexed MaxSpec witness: a prime minimal `Q` sits below a maximal
ideal missing `z̄`. Since `z̄ ∉ Q` (above), `z` misses the preimage prime
`P = V(Z)`, so some `v ∈ Z` has `z(v) ≠ 0`; the `coneEval`-kernel at `v`
is the required maximal. -/
theorem coneMinAvoidWitness_prime [IsAlgClosed K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2)
    (hcut : cutsOutOrigin_cf n K F)
    (Q : Ideal (coneQuotient n K (mkSystem n K F)))
    (hQ : Q.IsPrime)
    (hmin : ∀ Q' : Ideal (coneQuotient n K (mkSystem n K F)),
      Q'.IsPrime → Q' ≤ Q → Q ≤ Q') :
    ∃ m : MaximalSpectrum (coneQuotient n K (mkSystem n K F)),
      Q ≤ m.asIdeal ∧
        Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))
          (mkLin n K (Pi.single (Fin.last (n + 1)) 1)) ∉ m.asIdeal := by
  have haz := secFormAvoidsMinimal_prime n K F hF hcut Q hQ hmin
  have hP : (Ideal.comap (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))) Q).IsPrime :=
    Ideal.comap_isPrime (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))) (H := hQ)
  have hNS : MvPolynomial.vanishingIdeal K (MvPolynomial.zeroLocus K
      (Ideal.comap (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))) Q))
      = Ideal.comap (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))) Q :=
    MvPolynomial.IsPrime.vanishingIdeal_zeroLocus _ (h := hP)
  have hzP : mkLin n K (Pi.single (Fin.last (n + 1)) 1)
      ∉ Ideal.comap (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))) Q := haz
  have hex : ∃ v ∈ MvPolynomial.zeroLocus K
      (Ideal.comap (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))) Q),
      MvPolynomial.aeval v (mkLin n K (Pi.single (Fin.last (n + 1)) 1)) ≠ 0 := by
    by_contra hcon
    have hforall : ∀ v ∈ MvPolynomial.zeroLocus K
        (Ideal.comap (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))) Q),
        MvPolynomial.aeval v (mkLin n K (Pi.single (Fin.last (n + 1)) 1)) = 0 := by
      intro v hv
      by_contra hne
      exact hcon ⟨v, hv, hne⟩
    have hzV : mkLin n K (Pi.single (Fin.last (n + 1)) 1)
        ∈ MvPolynomial.vanishingIdeal K (MvPolynomial.zeroLocus K
          (Ideal.comap (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))) Q)) :=
      MvPolynomial.mem_vanishingIdeal_iff.mpr hforall
    rw [hNS] at hzV
    exact hzP hzV
  obtain ⟨v, hvZ, hvz⟩ := hex
  rw [MvPolynomial.mem_zeroLocus_iff] at hvZ
  have hvG : ∀ i, MvPolynomial.eval v (mkSystem n K F i) = 0 := by
    intro i
    have hmem : mkSystem n K F i
        ∈ Ideal.comap (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))) Q := by
      change Ideal.Quotient.mk _ _ ∈ Q
      have h0 : Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))
          (mkSystem n K F i) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
      rw [h0]
      exact Submodule.zero_mem _
    exact hvZ _ hmem
  have hvz' : MvPolynomial.eval v (mkLin n K (Pi.single (Fin.last (n + 1)) 1)) ≠ 0 := hvz
  have hsurj : Function.Surjective (coneEval n K (mkSystem n K F) v hvG) := by
    intro c
    exact ⟨Ideal.Quotient.mk _ (MvPolynomial.C c), coneEval_C n K (mkSystem n K F) v hvG c⟩
  refine ⟨⟨RingHom.ker (coneEval n K (mkSystem n K F) v hvG),
    RingHom.ker_isMaximal_of_surjective _ hsurj⟩, ?_, ?_⟩
  · intro q hq
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective q
    change Ideal.Quotient.mk _ g ∈ RingHom.ker (coneEval n K (mkSystem n K F) v hvG)
    rw [RingHom.mem_ker]
    change MvPolynomial.eval v g = 0
    have hgP : g ∈ Ideal.comap (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))) Q := hq
    exact hvZ g hgP
  · intro hcon
    have hcon' : Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))
        (mkLin n K (Pi.single (Fin.last (n + 1)) 1))
        ∈ RingHom.ker (coneEval n K (mkSystem n K F) v hvG) := hcon
    have h0 := RingHom.mem_ker.mp hcon'
    have h0' : MvPolynomial.eval v (mkLin n K (Pi.single (Fin.last (n + 1)) 1)) = 0 := h0
    exact hvz' h0'

/-- End-to-end discharge of the patched witness: the prime-indexed MaxSpec
witness (`coneMinAvoidWitness_prime`) is exactly `ConeMinAvoidWitnessPrime`
for `mkSystem`/secForm-`ℓ`. Together with
`secFormAvoidsMinimal_of_witness_prime`, avoidance is discharged with no
residual left.
-/
theorem coneMinAvoidWitnessPrime_discharge [IsAlgClosed K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2)
    (hcut : cutsOutOrigin_cf n K F) :
    ConeMinAvoidWitnessPrime n K (mkSystem n K F)
      (Pi.single (Fin.last (n + 1)) 1) :=
  fun Q hQ hmin => coneMinAvoidWitness_prime n K F hF hcut Q hQ hmin

/-- No `X₀`-linear part in `X₁`: any antidiagonal piece below `e₀` kills it
(`single 1 1 ≰ e₀` since `(single 1 1) 1 = 1 > 0 = e₀ 1`). -/
theorem coeff_x1_of_add_eq_single (a b : Fin (0 + 2) →₀ ℕ)
    (hab : a + b = Finsupp.single (0 : Fin (0 + 2)) 1) :
    AddMonoidAlgebra.coeff (MvPolynomial.X (1 : Fin (0 + 2)) :
      MvPolynomial (Fin (0 + 2)) K) b = 0 := by
  rw [MvPolynomial.coeff_X]
  apply ite_eq_right
  intro hcon
  have h01 : (0 : Fin (0 + 2)) ≠ 1 := by decide
  have hb1 : b 1 = 0 := by
    have h : (a + b) 1 = (Finsupp.single (0 : Fin (0 + 2)) 1) 1 :=
      congrArg (fun f : Fin (0 + 2) →₀ ℕ => f 1) hab
    rw [Finsupp.add_apply, Finsupp.single_eq_of_ne' h01] at h
    omega
  have hcon1 : (Finsupp.single (1 : Fin (0 + 2)) 1) 1 = b 1 :=
    congrArg (fun f : Fin (0 + 2) →₀ ℕ => f 1) hcon
  rw [Finsupp.single_eq_same] at hcon1
  omega

/-- No `X₀`-linear part in `X₀² - X₁X₀` either (`X₀²` needs `single 0 2 ≰
e₀`; `X₁X₀` dies by the previous lemma on the `X₁` factor). -/
theorem coeff_quad_of_add_eq_single (a b : Fin (0 + 2) →₀ ℕ)
    (hab : a + b = Finsupp.single (0 : Fin (0 + 2)) 1) :
    AddMonoidAlgebra.coeff (MvPolynomial.X (0 : Fin (0 + 2)) ^ 2
        - MvPolynomial.X (1 : Fin (0 + 2)) * MvPolynomial.X (0 : Fin (0 + 2)) :
        MvPolynomial (Fin (0 + 2)) K) b = 0 := by
  have hsub : AddMonoidAlgebra.coeff (MvPolynomial.X (0 : Fin (0 + 2)) ^ 2
        - MvPolynomial.X (1 : Fin (0 + 2)) * MvPolynomial.X (0 : Fin (0 + 2)) :
        MvPolynomial (Fin (0 + 2)) K) b
      = AddMonoidAlgebra.coeff (MvPolynomial.X (0 : Fin (0 + 2)) ^ 2 :
        MvPolynomial (Fin (0 + 2)) K) b
        - AddMonoidAlgebra.coeff (MvPolynomial.X (1 : Fin (0 + 2))
          * MvPolynomial.X (0 : Fin (0 + 2)) : MvPolynomial (Fin (0 + 2)) K) b := by
    simp
  rw [hsub]
  have hpow : AddMonoidAlgebra.coeff (MvPolynomial.X (0 : Fin (0 + 2)) ^ 2 :
      MvPolynomial (Fin (0 + 2)) K) b = 0 := by
    rw [MvPolynomial.coeff_X_pow]
    apply ite_eq_right
    intro hcon
    have hb0 : b 0 ≤ 1 := by
      have h : (a + b) 0 = (Finsupp.single (0 : Fin (0 + 2)) 1) 0 :=
        congrArg (fun f : Fin (0 + 2) →₀ ℕ => f 0) hab
      rw [Finsupp.add_apply, Finsupp.single_eq_same] at h
      omega
    have hcon0 : (Finsupp.single (0 : Fin (0 + 2)) 2) 0 = b 0 :=
      congrArg (fun f : Fin (0 + 2) →₀ ℕ => f 0) hcon
    rw [Finsupp.single_eq_same] at hcon0
    omega
  have hmul : AddMonoidAlgebra.coeff (MvPolynomial.X (1 : Fin (0 + 2))
      * MvPolynomial.X (0 : Fin (0 + 2)) : MvPolynomial (Fin (0 + 2)) K) b = 0 := by
    rw [MvPolynomial.coeff_mul]
    apply Finset.sum_eq_zero
    intro x hx
    obtain ⟨a', b'⟩ := x
    rw [Finset.mem_antidiagonal] at hx
    have hx' : a' + b' = b := hx
    change AddMonoidAlgebra.coeff (MvPolynomial.X (1 : Fin (0 + 2)) :
        MvPolynomial (Fin (0 + 2)) K) a'
        * AddMonoidAlgebra.coeff (MvPolynomial.X (0 : Fin (0 + 2)) :
        MvPolynomial (Fin (0 + 2)) K) b' = 0
    have hadd : (a + b') + a' = Finsupp.single (0 : Fin (0 + 2)) 1 := by
      have h1 : (a + b') + a' = a + (a' + b') := by
        rw [add_assoc, add_comm b' a']
      rw [h1, hx', hab]
    rw [coeff_x1_of_add_eq_single K _ _ hadd, zero_mul]
  rw [hpow, hmul, sub_zero]

/-- The `e₀`-coefficient of any `X₁`-multiple vanishes. -/
theorem coeff_mul_x1_eq_zero (c : MvPolynomial (Fin (0 + 2)) K) :
    AddMonoidAlgebra.coeff (c * MvPolynomial.X (1 : Fin (0 + 2)))
      (Finsupp.single (0 : Fin (0 + 2)) 1) = 0 := by
  rw [MvPolynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro x hx
  obtain ⟨a', b'⟩ := x
  rw [Finset.mem_antidiagonal] at hx
  have hx' : a' + b' = Finsupp.single (0 : Fin (0 + 2)) 1 := hx
  change AddMonoidAlgebra.coeff c a' * AddMonoidAlgebra.coeff
      (MvPolynomial.X (1 : Fin (0 + 2)) : MvPolynomial (Fin (0 + 2)) K) b' = 0
  rw [coeff_x1_of_add_eq_single K _ _ hx', mul_zero]

/-- The `e₀`-coefficient of any `(X₀² - X₁X₀)`-multiple vanishes. -/
theorem coeff_mul_quad_eq_zero (e : MvPolynomial (Fin (0 + 2)) K) :
    AddMonoidAlgebra.coeff (e * (MvPolynomial.X (0 : Fin (0 + 2)) ^ 2
        - MvPolynomial.X (1 : Fin (0 + 2)) * MvPolynomial.X (0 : Fin (0 + 2))))
      (Finsupp.single (0 : Fin (0 + 2)) 1) = 0 := by
  rw [MvPolynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro x hx
  obtain ⟨a', b'⟩ := x
  rw [Finset.mem_antidiagonal] at hx
  have hx' : a' + b' = Finsupp.single (0 : Fin (0 + 2)) 1 := hx
  change AddMonoidAlgebra.coeff e a' * AddMonoidAlgebra.coeff
      (MvPolynomial.X (0 : Fin (0 + 2)) ^ 2
        - MvPolynomial.X (1 : Fin (0 + 2)) * MvPolynomial.X (0 : Fin (0 + 2)) :
        MvPolynomial (Fin (0 + 2)) K) b' = 0
  rw [coeff_quad_of_add_eq_single K _ _ hx', mul_zero]

/-- The `e₀`-coefficient of a combination `c·X₁ - e·(X₀² - X₁X₀)` vanishes. -/
theorem coeff_comb_eq_zero (c e : MvPolynomial (Fin (0 + 2)) K) :
    AddMonoidAlgebra.coeff (c * MvPolynomial.X (1 : Fin (0 + 2))
        - e * (MvPolynomial.X (0 : Fin (0 + 2)) ^ 2
        - MvPolynomial.X (1 : Fin (0 + 2)) * MvPolynomial.X (0 : Fin (0 + 2))))
      (Finsupp.single (0 : Fin (0 + 2)) 1) = 0 := by
  have hsplit : AddMonoidAlgebra.coeff (c * MvPolynomial.X (1 : Fin (0 + 2))
        - e * (MvPolynomial.X (0 : Fin (0 + 2)) ^ 2
        - MvPolynomial.X (1 : Fin (0 + 2)) * MvPolynomial.X (0 : Fin (0 + 2))))
      (Finsupp.single (0 : Fin (0 + 2)) 1)
      = AddMonoidAlgebra.coeff (c * MvPolynomial.X (1 : Fin (0 + 2)))
        (Finsupp.single (0 : Fin (0 + 2)) 1)
        - AddMonoidAlgebra.coeff (e * (MvPolynomial.X (0 : Fin (0 + 2)) ^ 2
        - MvPolynomial.X (1 : Fin (0 + 2)) * MvPolynomial.X (0 : Fin (0 + 2))))
        (Finsupp.single (0 : Fin (0 + 2)) 1) := by
    simp
  rw [hsplit, coeff_mul_x1_eq_zero, coeff_mul_quad_eq_zero, sub_zero]

/-- No prime lies below `span{z̄}` at `n = 0`, `F = (X₀²)`: a prime below
would contain a factor of `G₀ = X₀(X₀ - X₁)`, but `X₀` and `X₀ - X₁` both
miss the preimage `span{z, G₀}` (their `e₀`-coefficients are nonzero while
every element of the preimage has `e₀`-coefficient zero). -/
theorem noPrime_below_span_zbar_n0
    (F : Fin (0 + 1) → MvPolynomial (Fin (0 + 1)) K)
    (hF : ∀ i, F i = MvPolynomial.X (0 : Fin (0 + 1)) ^ 2)
    (Q' : Ideal (coneQuotient 0 K (mkSystem 0 K F)))
    (hQ' : Q'.IsPrime)
    (hle : Q' ≤ Ideal.span ({(Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem 0 K F)))
      (mkLin 0 K (Pi.single (Fin.last (0 + 1)) 1)))} : Set _)) :
    False := by
  have hsub : Subsingleton (Fin (0 + 1)) :=
    ⟨fun i j => Fin.ext (by have hi := i.2; have hj := j.2; omega)⟩
  have hlast : Fin.last (0 + 1) = (1 : Fin (0 + 2)) := by decide
  have hcast0 : Fin.castSucc (0 : Fin (0 + 1)) = (0 : Fin (0 + 2)) := by decide
  have hG0 : ∀ i : Fin (0 + 1), mkSystem 0 K F i
      = MvPolynomial.X (0 : Fin (0 + 2)) ^ 2
        - MvPolynomial.X (1 : Fin (0 + 2)) * MvPolynomial.X (0 : Fin (0 + 2)) := by
    intro i
    have hi0 : i = 0 := @Subsingleton.elim _ hsub i 0
    subst hi0
    have hFi := hF 0
    change MvPolynomial.rename Fin.castSucc (F 0)
        - MvPolynomial.X (Fin.last (0 + 1))
          * MvPolynomial.X (Fin.castSucc (0 : Fin (0 + 1)))
        = MvPolynomial.X (0 : Fin (0 + 2)) ^ 2
          - MvPolynomial.X (1 : Fin (0 + 2)) * MvPolynomial.X (0 : Fin (0 + 2))
    rw [hFi, map_pow, MvPolynomial.rename_X, hcast0, hlast]
  have hrange : Set.range (mkSystem 0 K F) = {mkSystem 0 K F 0} := by
    ext y
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      have hi0 : i = 0 := @Subsingleton.elim _ hsub i 0
      rw [hi0]
    · intro h
      rw [h]
      exact ⟨0, rfl⟩
  have hzpoly : mkLin 0 K (Pi.single (Fin.last (0 + 1)) 1)
      = MvPolynomial.X (1 : Fin (0 + 2)) := by
    rw [mkLin_zForm_cf 0 K, hlast]
  have hfactor : MvPolynomial.X (0 : Fin (0 + 2))
        * (MvPolynomial.X (0 : Fin (0 + 2)) - MvPolynomial.X (1 : Fin (0 + 2)))
      = mkSystem 0 K F 0 := by
    rw [hG0 0]
    ring
  have hGmem : ∀ i : Fin (0 + 1), mkSystem 0 K F i
      ∈ Ideal.comap (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem 0 K F)))) Q' := by
    intro i
    change Ideal.Quotient.mk _ _ ∈ Q'
    have h0 : Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem 0 K F)))
        (mkSystem 0 K F i) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
    rw [h0]
    exact Submodule.zero_mem _
  have hPc : (Ideal.comap (Ideal.Quotient.mk
      (Ideal.span (Set.range (mkSystem 0 K F)))) Q').IsPrime :=
    Ideal.comap_isPrime (Ideal.Quotient.mk
      (Ideal.span (Set.range (mkSystem 0 K F)))) (H := hQ')
  have hfactor_mem : MvPolynomial.X (0 : Fin (0 + 2))
        * (MvPolynomial.X (0 : Fin (0 + 2)) - MvPolynomial.X (1 : Fin (0 + 2)))
      ∈ Ideal.comap (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem 0 K F)))) Q' := by
    rw [hfactor]
    exact hGmem 0
  rcases (hPc.mul_mem_iff_mem_or_mem).mp hfactor_mem with hX0 | hX01
  · have hmemQ : Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem 0 K F)))
        (MvPolynomial.X (0 : Fin (0 + 2))) ∈ Q' := hX0
    have hmemS := hle hmemQ
    rw [Ideal.mem_span_singleton'] at hmemS
    obtain ⟨c, hc⟩ := hmemS
    obtain ⟨cpoly, rfl⟩ := Ideal.Quotient.mk_surjective c
    have hc0 : Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem 0 K F)))
        (cpoly * mkLin 0 K (Pi.single (Fin.last (0 + 1)) 1)
          - MvPolynomial.X (0 : Fin (0 + 2))) = 0 := by
      rw [map_sub]
      rw [← map_mul] at hc
      rw [hc, sub_self]
    have hceq := Ideal.Quotient.eq_zero_iff_mem.mp hc0
    rw [hrange, Ideal.mem_span_singleton'] at hceq
    obtain ⟨e, he⟩ := hceq
    have heq : MvPolynomial.X (0 : Fin (0 + 2))
        = cpoly * MvPolynomial.X (1 : Fin (0 + 2))
          - e * (MvPolynomial.X (0 : Fin (0 + 2)) ^ 2
          - MvPolynomial.X (1 : Fin (0 + 2)) * MvPolynomial.X (0 : Fin (0 + 2))) := by
      rw [hzpoly, hG0 0] at he
      linear_combination he
    have hcc := congrArg (fun p : MvPolynomial (Fin (0 + 2)) K =>
      AddMonoidAlgebra.coeff p (Finsupp.single (0 : Fin (0 + 2)) 1)) heq
    rw [MvPolynomial.coeff_X_same, coeff_comb_eq_zero] at hcc
    exact one_ne_zero hcc
  · have hmemQ : Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem 0 K F)))
        (MvPolynomial.X (0 : Fin (0 + 2)) - MvPolynomial.X (1 : Fin (0 + 2))) ∈ Q' := hX01
    have hmemS := hle hmemQ
    rw [Ideal.mem_span_singleton'] at hmemS
    obtain ⟨c, hc⟩ := hmemS
    obtain ⟨cpoly, rfl⟩ := Ideal.Quotient.mk_surjective c
    have hc0 : Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem 0 K F)))
        (cpoly * mkLin 0 K (Pi.single (Fin.last (0 + 1)) 1)
          - (MvPolynomial.X (0 : Fin (0 + 2)) - MvPolynomial.X (1 : Fin (0 + 2)))) = 0 := by
      rw [map_sub]
      rw [← map_mul] at hc
      rw [hc, sub_self]
    have hceq := Ideal.Quotient.eq_zero_iff_mem.mp hc0
    rw [hrange, Ideal.mem_span_singleton'] at hceq
    obtain ⟨e, he⟩ := hceq
    have heq : MvPolynomial.X (0 : Fin (0 + 2)) - MvPolynomial.X (1 : Fin (0 + 2))
        = cpoly * MvPolynomial.X (1 : Fin (0 + 2))
          - e * (MvPolynomial.X (0 : Fin (0 + 2)) ^ 2
          - MvPolynomial.X (1 : Fin (0 + 2)) * MvPolynomial.X (0 : Fin (0 + 2))) := by
      rw [hzpoly, hG0 0] at he
      linear_combination he
    have hcc := congrArg (fun p : MvPolynomial (Fin (0 + 2)) K =>
      AddMonoidAlgebra.coeff p (Finsupp.single (0 : Fin (0 + 2)) 1)) heq
    have hsplitL : AddMonoidAlgebra.coeff ((MvPolynomial.X (0 : Fin (0 + 2)) :
          MvPolynomial (Fin (0 + 2)) K) - (MvPolynomial.X (1 : Fin (0 + 2)) :
          MvPolynomial (Fin (0 + 2)) K)) (Finsupp.single (0 : Fin (0 + 2)) 1) = 1 := by
      have hs : AddMonoidAlgebra.coeff ((MvPolynomial.X (0 : Fin (0 + 2)) :
            MvPolynomial (Fin (0 + 2)) K) - (MvPolynomial.X (1 : Fin (0 + 2)) :
            MvPolynomial (Fin (0 + 2)) K)) (Finsupp.single (0 : Fin (0 + 2)) 1)
          = AddMonoidAlgebra.coeff (MvPolynomial.X (0 : Fin (0 + 2)) :
            MvPolynomial (Fin (0 + 2)) K) (Finsupp.single (0 : Fin (0 + 2)) 1)
            - AddMonoidAlgebra.coeff (MvPolynomial.X (1 : Fin (0 + 2)) :
            MvPolynomial (Fin (0 + 2)) K) (Finsupp.single (0 : Fin (0 + 2)) 1) := by
        simp
      rw [hs, MvPolynomial.coeff_X_same, coeff_x1_of_add_eq_single K 0 _ (zero_add _), sub_zero]
    rw [hsplitL, coeff_comb_eq_zero] at hcc
    exact one_ne_zero hcc

/-- The literal `ConeMinAvoidWitness` is false: refuted at `n = 0`,
`F = (X₀²)` by `Q = span{z̄}` (which contains `z̄` yet has no prime
strictly below it). The minimality predicate needs a `Q.IsPrime` patch. -/
theorem coneMinAvoidWitness_false_n0 :
    ¬ ConeMinAvoidWitness 0 K
      (mkSystem 0 K (fun _ : Fin (0 + 1) => MvPolynomial.X (0 : Fin (0 + 1)) ^ 2))
      (Pi.single (Fin.last (0 + 1)) 1) := by
  intro hcon
  have hmin : ∀ Q' : Ideal (coneQuotient 0 K
      (mkSystem 0 K (fun _ : Fin (0 + 1) => MvPolynomial.X (0 : Fin (0 + 1)) ^ 2))),
      Q'.IsPrime
        → Q' ≤ Ideal.span ({(Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem 0 K
          (fun _ : Fin (0 + 1) => MvPolynomial.X (0 : Fin (0 + 1)) ^ 2))))
          (mkLin 0 K (Pi.single (Fin.last (0 + 1)) 1)))} : Set _)
        → Ideal.span ({(Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem 0 K
          (fun _ : Fin (0 + 1) => MvPolynomial.X (0 : Fin (0 + 1)) ^ 2))))
          (mkLin 0 K (Pi.single (Fin.last (0 + 1)) 1)))} : Set _) ≤ Q' := by
    intro Q' hQ' hle
    exact False.elim (noPrime_below_span_zbar_n0 K
      (fun _ : Fin (0 + 1) => MvPolynomial.X (0 : Fin (0 + 1)) ^ 2)
      (fun _ => rfl) Q' hQ' hle)
  obtain ⟨m, hle, hmiss⟩ := hcon _ hmin
  exact hmiss (hle (Ideal.subset_span (Set.mem_singleton_iff.mpr rfl)))

end MinAvoidDischarge

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
