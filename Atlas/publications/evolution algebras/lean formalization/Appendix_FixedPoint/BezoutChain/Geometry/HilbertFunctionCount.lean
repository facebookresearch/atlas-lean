/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Statement.Definitions
import Appendix_FixedPoint.BezoutChain.Geometry.ChartFiltration
import Appendix_FixedPoint.BezoutChain.Geometry.Elimination
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Order.WithBot
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Jacobson.Artinian
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Bézout induction: Hilbert function of a complete intersection and the count

This module proves the two interface items (route (ii′)):

* `hilbertSeries_poly`: the `K`-dimension of the homogeneous degree-`d` piece
  in `N` variables is `Nat.choose (d + N - 1) (N - 1)` (stars and bars).
* `length_section_eq_two_pow`: the regular-section length is `2 ^ (n + 1)`.
  The main theorem is stated over `totalDegree` (unfolding it finishes
  `bezout_quadratic`; `Statement.lean` is not edited here), with the graded
  SES recurrences and the filtration summation taken as explicit named
  hypotheses (see below).

Later sections discharge the assembly inputs: the `H`/`F` witnesses (`Hwit`,
`Fsec`, `Hgeom`), the section SES (`coneMul`/`secProj`/`secCokernelEquiv`),
the geometric filtration (`Cfsec` + `cfsec_hfilter`), the full section-count
application (`fsec_totalDegree_eq_two_pow`, `bezout_quadratic_of_shapes`),
section stabilization/vanishing (`cfsec_stab_section`,
`fsec_vanishing_of_stabAbove`, `CfsecDisjointData`), and the lattice bridge
closing disjointness from `hG` (`hdisj_full_of_quadrics`).

## Design: numerical Hilbert functions

The per-quadric SES `0 → S(−2) →[×q] S → S/qS → 0`
does not double total lengths (intermediate quotients are not Artinian); the
true induction is on Hilbert *functions*. With `N = n + 2` variables and
`K = n + 1` quadrics, write `H k d` for the `K`-dimension of the degree-`d`
piece after quotienting by the first `k` quadrics, and `F d` for the section
pieces. Regularity of each quadric gives `H (k+1) d + H k (d−2) = H k d`
(`graded_piece_ses`, proved from `ses_finrank_add`); regularity of the linear
section gives `F d + H K (d−1) = H K d`. From `H 0 d = choose` one gets the
closed form `(1+t)^k / (1−t)^{N−k}` (`Gclosed`), hence the section values are
`F d = Nat.choose (n+1) d`, summing to `2 ^ (n+1)` (`Nat.sum_range_choose`).

## Added hypotheses and deviations (reported)

1. `hilbertSeries_poly` takes `0 < N`: stars and bars degenerates at `N = 0`
   (for `N = 0 < d` the piece is `0` but truncated subtraction gives
   `Nat.choose (d - 1) 0 = 1`). Stars and bars itself is reused in-tree
   (`Sym.card_sym_eq_choose`), not proved from scratch.
2. `length_section_eq_two_pow` takes the numerical inputs `H`, `F` with
   `hH0` (base, discharged by `hilbertSeries_poly`), `hSES` (per-quadric
   graded SES recurrence, discharged from a regular sequence via
   `graded_piece_ses`), `hSEC` (linear-section recurrence, discharged from
   R1-regularity the same way), and `hfilter` (degree-filtration summation
   with an explicit Artinian bound `B`, discharged by the Elimination /
   Counting filtration geometry). The geometric context (`hG`, `hZd`, R1
   regularity, `IsAlgClosed`) enters only through the discharge of these
   inputs, so — unlike the spec sketch — the assembly takes no further
   hypotheses.
3. `exists_regular_quadrics` (`Regularity.Avoid.ResultantLemmas`, R2) is not consumed
   here but needs no repair: it concludes `RingTheory.Sequence.IsRegular` for the
   combinations `F k = ∑ j, M k j • G j` in the polynomial ring
   `MvPolynomial (Fin (n + 2)) K` itself (weak regularity on the successive
   quotients `R ⧸ (F₀, …, F_{k-1})`), plus span equality
   `Ideal.span (Set.range F) = Ideal.span (Set.range G)` from `IsUnit M`
   (not quotient images in `coneQuotient`). The remaining bridge to `hSES` is
   graded regularity ⇒ the numerical recurrence via `graded_piece_ses`
   (proved above from `Elimination.ses_finrank_add`): at each stage `k` and degree
   `d`, multiplication by the regular quadric gives the injective `K`-linear map
   `f` between graded pieces (degree shift `2`) with cokernel identified with the
   next-quotient piece `R`, yielding `H (k+1) d + H k (d-2) = H k d`.
4. `section_artinian` (`Elimination.lean`) is not called: its Artinian
   conclusion justifies the existence of `hfilter`'s bound `B` (the degree
   filtration stabilizes), but no finite-length API is consumed in the
   assembly itself. The operative reuse from `Elimination.lean` is
   `ses_finrank_add` (in `graded_piece_ses`). `chart_bridge` / `chartRing`
   are not used (parallel repair in progress).
5. Input inventory (R2-at-mkSystem, hHt, hlow now
   proved conditionally — this item is itself a result). Per assembly
   piece, provable now vs still-blocked with the exact missing input:
   * `hH0`: provable now → already proved (`hwit_geometric_base`,
     `hwit_discharge` above; pure combinatorics via `gclosed_zero`).
   * `hlow`-shape consumed by `exists_regular_quadrics_mkSystem`
     (`Regularity/Avoid/ResultantLemmas.lean`) and `avoid_of_hunmixed_ge2`
     (`Regularity/Avoid/AvoidanceApply.lean`): provable now → proved here as
     `hlow_input_of_uncond`, from `hlow_uncond`
     (`Dimension/HeightLowerBound.lean`, taken as an explicit hypothesis —
     cited, not imported) with containment/`hZd` retained for interface
     stability.
   * `hSES` (R2 output ⇒ per-quadric recurrence): still-blocked. Exact missing
     input: the graded-quotient cokernel identification
     `e : (Q ⧸ LinearMap.range (×Fₖ)) ≃ₗ[K] R` with `R` the next-quotient
     graded piece — unstatable without a graded-quotient API (Mathlib
     v4.34.0 has `homogeneousSubmodule` only for the polynomial ring;
     documented in this section — downstream consumers such as
     `Regularity/Avoid/MkSystemSESData.lean` import this file, not the
     reverse). Factored out conditionally:
     `heq_gclosed_of_shapes` (any `H` with the `hH0`/`hSES` shapes equals
     `Gclosed` below `n + 1`) and `fsec_hSEC_closed` (the `hSEC` input shape
     against the closed form, conditional on the identification `hHeq`).
     Regularity half is available
     (conditionally): cone-side `exists_regular_quadrics` needs `hZd` plus
     `havoid`, discharged via `avoid_of_hunmixed_ge2` from `hZd` + `hlow`
     (wired above) + `hunmixed_ge2` (open research beyond t2a/t2b data).
   * `hSEC` (R1 regularity ⇒ section recurrence): proved conditionally as
     `hgeom_sec_recurrence` (from `hreg` + per-degree `DescentData` +
     `h0`, all explicit; `h0` discharged by `hgeom_sec_zero_eq` from section
     and cone nontriviality). The remaining section-step input is the
     per-degree `DescentData` (homogeneous-cofactor) half, owned with
     Elimination.
   * `hfilter` (`Cf`/`B` construction from `sectionPiece`): proved
     conditionally as `Cfsec` + `cfsec_hfilter` (from the explicit
     piece-disjointness `hdisj` and the Artinian bound `hstab`/`hvan`;
     ambient finiteness is the proved bridge
     `section_finite_of_artinian`). The remaining inputs are `hdisj`,
     `hstab`, `hvan` (Counting finite-length bridge) and the `hZd`
     bridges.
   * `Fsec … 0 = 1`: proved conditionally as `fsec_zero_eq_one` (weakest
     hypothesis: section nontriviality, discharged from `hG0` by
     `section_nontrivial_of_evalZero`).
   * Full application of `length_section_eq_two_pow` to `totalDegree`:
     proved conditionally as `fsec_totalDegree_eq_two_pow` (witnesses
     `Hwit`/`Fsec` + `fsec_hSEC_closed` + `cfsec_hfilter`) and
     `bezout_quadratic_of_shapes` (Statement's own `hG`/`hreg`/`hZd` via
     `evalZero_of_homogTwo` + `section_finite_of_artinian` +
     `hgeom_sec_zero_eq`); residual inputs exactly
     `hdesc`/`hHeq`/`hdisj`/`hstab`/`hvan` (+`B`). The `hSES` numerical
     assembly is `hSES_step_of_pieceSES` + `hSES_of_steps`
     (per-`(k,d)` graded-SES-data ⇒ `hSES` shape); its step-`0`
     geometric instance from R2 output is `hSES_step_of_pieceSES` at `k = 0`,
     steps `k ≥ 1` still need the graded-quotient API.

## References

Mathlib v4.34.0 has no degree-of-variety or Hilbert-series API; the count is
assembled from monomial-basis, finset-cardinality (`Sym` stars and bars),
`Nat.choose`, and finrank API. Per-declaration `## References` subsections
cite the exact module path and declaration name, each verified in-tree.

## Standing context (routine binders)

Named once here; per-decl docstrings below repeat GRADE verdicts and name only
substantive non-routine premises.

* `hG : ∀ i, (G i).IsHomogeneous 2` / `hG0 : ∀ i, eval 0 (G i) = 0` —
  quadric system / vanishing at the origin.
* `hreg` — R1 section regularity; `hZd : IsZeroDimensional n K G`.
* Numerical data: `H : ℕ → ℕ → ℕ`, `F : ℕ → ℕ` with `hH0` (stars-and-bars
  base), `hSES` (per-quadric graded recurrence), `hSEC` (section recurrence),
  `hfilter` (degree-filtration summation at bound `B`); `hHeq` identifies the
  geometric instance.
* `Cf`-filtration data: `hC0`/`hCtop`/`hCstep`, `hdesc : DescentData`,
  `hdisj`/`hstab`/`hvan`, `hlin`/`hlen`.
* `Module.Finite` (section/graded-piece finiteness); `[IsAlgClosed K]` where
  the Nullstellensatz feeds in; `[Field K]` throughout.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
open scoped BigOperators

/-! ## Hilbert series of polynomial rings (stars and bars) -/

/-- Stars and bars for monomial exponents: functions `Fin N →₀ ℕ` of degree
`d` are counted by `Nat.choose (N + d - 1) d`.

The bridge is `Finset.univ.finsuppAntidiag d`: membership is
`∑`-equals-`d` plus support containment (`Finset.mem_finsuppAntidiag`),
which for `s = Finset.univ` is exactly `Finsupp.degree_eq_sum`.
The finset card is `Finset.card_finsuppAntidiag_nat_eq_choose`, and it is
transported to the subtype via `Fintype.card_ofFinset`.

## References

* `Mathlib/Algebra/Order/Antidiag/Finsupp.lean`, `Finset.finsuppAntidiag`,
  `Finset.mem_finsuppAntidiag`.
* `Mathlib/Algebra/Order/Antidiag/FinsuppEquiv.lean`,
  `Finset.card_finsuppAntidiag_nat_eq_choose`.
* `Mathlib/Data/Sym/Card.lean`, `Sym.card_sym_eq_choose` (the in-tree
  stars-and-bars theorem consumed by the previous item).
* `Mathlib/Data/Finsupp/Weight.lean`, `Finsupp.degree_eq_sum`.
* `Mathlib/Data/Fintype/Card.lean`, `Fintype.card_ofFinset`. -/
theorem mem_degreeExponents (N d : ℕ) (e : Fin N →₀ ℕ) :
    e ∈ Finset.univ.finsuppAntidiag d
      ↔ e ∈ ({e : Fin N →₀ ℕ | e.degree = d} : Set (Fin N →₀ ℕ)) := by
  rw [Finset.mem_finsuppAntidiag, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, -⟩
    have h2 := Finsupp.degree_eq_sum e
    have hsum : Finset.univ.sum ⇑e = ∑ i, e i := rfl
    omega
  · intro h
    have h2 := Finsupp.degree_eq_sum e
    have hsum : Finset.univ.sum ⇑e = ∑ i, e i := rfl
    exact ⟨by omega, Finset.subset_univ _⟩

/-- The exponent subtype is a fintype (via the antidiagonal finset). -/
noncomputable instance {N d : ℕ} :
    Fintype ↥({e : Fin N →₀ ℕ | e.degree = d} : Set (Fin N →₀ ℕ)) :=
  Fintype.ofFinset _ (fun x => mem_degreeExponents N d x)

/-- Stars and bars, subtype form: there are `(N + d - 1).choose d` finitely
supported functions `Fin N →₀ ℕ` of degree `d`. The subtype card is
transported from the antidiagonal finset (`Fintype.card_ofFinset`) and closed
by `Finset.card_finsuppAntidiag_nat_eq_choose`.

## References

* `Mathlib/Algebra/Order/Antidiag/FinsuppEquiv.lean`,
  `Finset.card_finsuppAntidiag_nat_eq_choose`.
* `Mathlib/Data/Fintype/Card.lean`, `Fintype.card_ofFinset`.
* `Mathlib/Data/Fintype/Fin.lean`, `Fintype.card_fin`. -/
theorem card_degreeExponents (N d : ℕ) :
    Fintype.card ↥({e : Fin N →₀ ℕ | e.degree = d} : Set (Fin N →₀ ℕ))
      = (N + d - 1).choose d := by
  have h1 : Fintype.card ↥({e : Fin N →₀ ℕ | e.degree = d} : Set (Fin N →₀ ℕ))
      = (Finset.univ.finsuppAntidiag d).card :=
    Fintype.card_ofFinset _ _
  rw [h1, Finset.card_finsuppAntidiag_nat_eq_choose, Finset.card_univ,
    Fintype.card_fin]

/-- `hilbertSeries_poly`: the `K`-dimension
of the homogeneous degree-`d` piece in `N` variables is
`Nat.choose (d + N - 1) (N - 1)`.

The piece is the span of the degree-`d` monomials
(`MvPolynomial.homogeneousSubmodule_eq_finsupp_supported` plus
`AddMonoidAlgebra.supported_eq_span_single`, with the image rewritten as a
range over the exponent subtype via `Set.image_eq_range` and
`MvPolynomial.single_eq_monomial`); those monomials are linearly independent
(`MvPolynomial.basisMonomials`), so `finrank_span_eq_card` plus
`card_degreeExponents` and `Nat.choose_symm` close the goal. The positivity
`0 < N` is needed: at `N = 0 < d` the piece vanishes while the truncated
formula gives `1`.

## References

* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.homogeneousSubmodule`,
  `MvPolynomial.homogeneousSubmodule_eq_finsupp_supported`.
* `Mathlib/Algebra/MonoidAlgebra/Module.lean`,
  `AddMonoidAlgebra.supported_eq_span_single`.
* `Mathlib/Algebra/MvPolynomial/Basic.lean`,
  `MvPolynomial.single_eq_monomial`.
* `Mathlib/RingTheory/MvPolynomial/Basic.lean`,
  `MvPolynomial.basisMonomials`, `MvPolynomial.coe_basisMonomials`.
* `Mathlib/LinearAlgebra/Dimension/Constructions.lean`,
  `finrank_span_eq_card`.
* `Mathlib/LinearAlgebra/LinearIndependent/Defs.lean`,
  `LinearIndependent.comp`.
* `Mathlib/Data/Set/Image.lean`, `Set.image_eq_range`.
* `Mathlib/Data/Nat/Choose/Basic.lean`, `Nat.choose_symm`. -/
theorem hilbertSeries_poly (K : Type*) [Field K] (N d : ℕ) (hN : 0 < N) :
    Module.finrank K (MvPolynomial.homogeneousSubmodule (Fin N) K d)
      = Nat.choose (d + N - 1) (N - 1) := by
  have h1N : 1 ≤ N := hN
  have hspan : MvPolynomial.homogeneousSubmodule (Fin N) K d
      = Submodule.span K (Set.range
        (fun e : ↥({e : Fin N →₀ ℕ | e.degree = d} : Set (Fin N →₀ ℕ)) =>
          MvPolynomial.monomial e.1 (1 : K))) := by
    rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported,
      AddMonoidAlgebra.supported_eq_span_single, Set.image_eq_range]
    simp only [MvPolynomial.single_eq_monomial]
  have hLI : LinearIndependent K
      (fun e : ↥({e : Fin N →₀ ℕ | e.degree = d} : Set (Fin N →₀ ℕ)) =>
        MvPolynomial.monomial e.1 (1 : K)) := by
    have h := (MvPolynomial.basisMonomials (Fin N) K).linearIndependent.comp
      (fun e : ↥({e : Fin N →₀ ℕ | e.degree = d} : Set (Fin N →₀ ℕ)) =>
        (e.1 : Fin N →₀ ℕ))
      (fun a b hab => Subtype.ext hab)
    simpa only [Function.comp_def, MvPolynomial.coe_basisMonomials] using h
  rw [hspan, finrank_span_eq_card hLI, card_degreeExponents]
  have hNe : N + d - 1 = d + N - 1 := by omega
  have hle : N - 1 ≤ d + N - 1 := by omega
  have hsub : d + N - 1 - (N - 1) = d := by omega
  have hsym := Nat.choose_symm (n := d + N - 1) (k := N - 1) hle
  rw [hsub] at hsym
  rw [hNe]
  exact hsym

/-! ## The graded SES mechanism (`×(1+t)` step) -/

/-- SES finrank recurrence with a degree shift (the
`0 → S(−2) →[×q] S → S/qS → 0` step): an injective `K`-linear map `f`
(multiplication by a regular quadric between graded pieces, shifting degree
by `2`) into `Q` with cokernel identified with `R` gives
`finrank Q = finrank P + finrank R`.

The geometry instantiates `P, Q` with consecutive graded pieces, `f` with
`×q̄` (injective by regularity of the quadric), and `R` with the graded piece
of the next quotient; `ses_finrank_add` supplies the additivity and
`LinearMap.finrank_range_add_finrank_ker` identifies the range.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.Elimination`,
  `Appendix_FixedPoint.BezoutChain.ses_finrank_add`
  (itself `Submodule.finrank_quotient_add_finrank`,
  `Mathlib/LinearAlgebra/Dimension/RankNullity.lean`).
* `Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean`,
  `LinearMap.finrank_range_add_finrank_ker`.
* `Mathlib/Algebra/Module/Submodule/Ker.lean`, `LinearMap.ker_eq_bot'`.
* `Mathlib/LinearAlgebra/Dimension/Finite.lean`, `finrank_bot`.
* `Mathlib/LinearAlgebra/Dimension/Finrank.lean`, `LinearEquiv.finrank_eq`. -/
theorem graded_piece_ses (K : Type*) [Field K]
    (P Q R : Type*) [AddCommGroup P] [AddCommGroup Q] [AddCommGroup R]
    [Module K P] [Module K Q] [Module K R]
    [Module.Finite K P] [Module.Finite K Q]
    (f : P →ₗ[K] Q) (e : (Q ⧸ LinearMap.range f) ≃ₗ[K] R)
    (hinj : Function.Injective f) :
    Module.finrank K Q = Module.finrank K P + Module.finrank K R := by
  have h1 := ses_finrank_add K Q (LinearMap.range f)
  have hker : LinearMap.ker f = ⊥ :=
    LinearMap.ker_eq_bot'.mpr (fun m hm => hinj (by rw [hm, map_zero]))
  have h2 := LinearMap.finrank_range_add_finrank_ker f
  rw [hker, finrank_bot, add_zero] at h2
  rw [LinearEquiv.finrank_eq e] at h1
  omega

/-! ## Closed form of the Hilbert function -/

/-- Closed form for the stage-`k` Hilbert function: the coefficients of
`(1 + t)^k / (1 - t)^{n+1-k}`, i.e. `∑ i, choose k i * choose (d-i+M) M`
with `M = n + 1 - k`. The `i`-sum ranges over `Finset.range (d + 1)` with no
truncation issues: `Nat.choose k i` vanishes for `i > k`, and `i ≤ d` holds
on the range. -/
def Gclosed (n k d : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (d + 1),
    Nat.choose k i * Nat.choose (d - i + (n + 1 - k)) (n + 1 - k)

/-- Base case: the closed form at stage `0` is the stars-and-bars value
(`hilbertSeries_poly` with `N = n + 2`).

## References

* `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`,
  `Finset.sum_eq_single`.
* `Mathlib/Data/Nat/Choose/Basic.lean`, `Nat.choose_eq_zero_of_lt`,
  `Nat.choose_self`. -/
theorem gclosed_zero (n d : ℕ) :
    Gclosed n 0 d = Nat.choose (d + (n + 2) - 1) ((n + 2) - 1) := by
  have h0 : ∀ i ∈ Finset.range (d + 1), i ≠ 0 →
      Nat.choose 0 i * Nat.choose (d - i + (n + 1 - 0)) (n + 1 - 0) = 0 := by
    intro i _ hi
    have hpos : 0 < i := Nat.pos_of_ne_zero hi
    rw [Nat.choose_eq_zero_of_lt hpos, zero_mul]
  simp only [Gclosed]
  rw [Finset.sum_eq_single 0 h0 (fun hcon =>
    absurd (Finset.mem_range.mpr (Nat.zero_lt_succ d)) hcon)]
  simp only [Nat.sub_zero]
  rw [Nat.choose_self 0, one_mul]
  have eA : d + (n + 1) = d + (n + 2) - 1 := by omega
  have eB : n + 1 = (n + 2) - 1 := by omega
  rw [eA, eB]

/-- SES step for the closed form: quotienting by one more quadric subtracts
the twice-shifted function. Summation ranges are peeled with
`Finset.sum_range_succ'` (front, where `Nat.choose_succ_succ'` applies
genuinely) and `Finset.sum_range_succ` (back); the bulk identifies via
double Pascal and the two boundary values by direct computation.

## References

* `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`,
  `Finset.sum_range_succ`, `Finset.sum_range_succ'`,
  `Finset.sum_range_one`, `Finset.sum_add_distrib`, `Finset.sum_congr`.
* `Mathlib/Data/Nat/Choose/Basic.lean`, `Nat.choose_succ_succ'`,
  `Nat.choose_succ_self_right`, `Nat.choose_self`,
  `Nat.choose_zero_right`, `Nat.choose_one_right`. -/
theorem gclosed_step (n k d : ℕ) (hk : k < n + 1) :
    Gclosed n (k + 1) d + (if 2 ≤ d then Gclosed n k (d - 2) else 0)
      = Gclosed n k d := by
  have hk1 : k + 1 ≤ n + 1 := hk
  have hMM : n + 1 - (k + 1) + 1 = n + 1 - k := by omega
  split_ifs with hd
  · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hd
    rw [show (2 : ℕ) + e - 2 = e from by omega]
    simp only [Gclosed]
    -- A + C = B with A, B over `range (2+e+1)`, C over `range (e+1)`.
    have hApeel : (∑ i ∈ Finset.range (2 + e + 1),
          Nat.choose (k + 1) i * Nat.choose (2 + e - i + (n + 1 - (k + 1))) (n + 1 - (k + 1)))
        = (∑ i ∈ Finset.range (2 + e),
            Nat.choose (k + 1) (i + 1)
              * Nat.choose (2 + e - (i + 1) + (n + 1 - (k + 1))) (n + 1 - (k + 1)))
        + Nat.choose (k + 1) 0 * Nat.choose (2 + e - 0 + (n + 1 - (k + 1))) (n + 1 - (k + 1)) :=
      Finset.sum_range_succ' _ (2 + e)
    have hS1peel : (∑ i ∈ Finset.range (2 + e + 1),
          Nat.choose k i * Nat.choose (2 + e - i + (n + 1 - (k + 1))) (n + 1 - (k + 1)))
        = (∑ i ∈ Finset.range (2 + e),
            Nat.choose k (i + 1)
              * Nat.choose (2 + e - (i + 1) + (n + 1 - (k + 1))) (n + 1 - (k + 1)))
        + Nat.choose k 0 * Nat.choose (2 + e - 0 + (n + 1 - (k + 1))) (n + 1 - (k + 1)) :=
      Finset.sum_range_succ' _ (2 + e)
    have hV : (∑ i ∈ Finset.range (2 + e),
          Nat.choose (k + 1) (i + 1)
            * Nat.choose (2 + e - (i + 1) + (n + 1 - (k + 1))) (n + 1 - (k + 1)))
        = (∑ i ∈ Finset.range (2 + e),
            Nat.choose k i * Nat.choose (2 + e - (i + 1) + (n + 1 - (k + 1))) (n + 1 - (k + 1)))
        + (∑ i ∈ Finset.range (2 + e),
            Nat.choose k (i + 1)
              * Nat.choose (2 + e - (i + 1) + (n + 1 - (k + 1))) (n + 1 - (k + 1))) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [Nat.choose_succ_succ', add_mul]
    have hR1S2 : (∑ i ∈ Finset.range (2 + e),
          Nat.choose k i * Nat.choose (2 + e - (i + 1) + (n + 1 - (k + 1))) (n + 1 - (k + 1)))
        = (∑ j ∈ Finset.range (2 + e),
          Nat.choose k j * Nat.choose (2 + e - 1 - j + (n + 1 - (k + 1))) (n + 1 - (k + 1))) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i < 2 + e := Finset.mem_range.mp hi
      have eA : 2 + e - (i + 1) + (n + 1 - (k + 1)) = 2 + e - 1 - i + (n + 1 - (k + 1)) := by
        omega
      rw [eA]
    have hA0 : Nat.choose (k + 1) 0 * Nat.choose (2 + e - 0 + (n + 1 - (k + 1))) (n + 1 - (k + 1))
        = Nat.choose k 0 * Nat.choose (2 + e - 0 + (n + 1 - (k + 1))) (n + 1 - (k + 1)) := by
      rw [Nat.choose_zero_right, Nat.choose_zero_right]
    have h2e : (2 : ℕ) + e = e + 1 + 1 := by omega
    have hS2peel : (∑ j ∈ Finset.range (2 + e),
          Nat.choose k j * Nat.choose (2 + e - 1 - j + (n + 1 - (k + 1))) (n + 1 - (k + 1)))
        = (∑ j ∈ Finset.range (e + 1),
            Nat.choose k j * Nat.choose (2 + e - 1 - j + (n + 1 - (k + 1))) (n + 1 - (k + 1)))
        + Nat.choose k (e + 1)
          * Nat.choose (2 + e - 1 - (e + 1) + (n + 1 - (k + 1))) (n + 1 - (k + 1)) := by
      rw [h2e]
      exact Finset.sum_range_succ _ _
    have hbulk : (∑ j ∈ Finset.range (e + 1),
          Nat.choose k j * Nat.choose (2 + e - 1 - j + (n + 1 - (k + 1))) (n + 1 - (k + 1)))
        + (∑ i ∈ Finset.range (e + 1),
          Nat.choose k i * Nat.choose (e - i + (n + 1 - k)) (n + 1 - k))
        = (∑ j ∈ Finset.range (e + 1),
          Nat.choose k j * Nat.choose (2 + e - j + (n + 1 - (k + 1))) ((n + 1 - (k + 1)) + 1)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : j < e + 1 := Finset.mem_range.mp hj
      have q1 : 2 + e - 1 - j + (n + 1 - (k + 1)) = (e + 1 - j + (n + 1 - (k + 1))) := by
        omega
      have q2 : e - j + (n + 1 - k) = (e + 1 - j + (n + 1 - (k + 1))) := by omega
      have q3 : (e + 1 - j + (n + 1 - (k + 1))) + 1 = 2 + e - j + (n + 1 - (k + 1)) := by
        omega
      rw [q1, q2, ← hMM, ← mul_add, ← Nat.choose_succ_succ', q3]
    have hlast : Nat.choose k (e + 1)
        * Nat.choose (2 + e - 1 - (e + 1) + (n + 1 - (k + 1))) (n + 1 - (k + 1))
        = Nat.choose k (e + 1) := by
      have q4 : 2 + e - 1 - (e + 1) + (n + 1 - (k + 1)) = n + 1 - (k + 1) := by omega
      rw [q4, Nat.choose_self, mul_one]
    have hS1p1 : (∑ i ∈ Finset.range (2 + e + 1),
          Nat.choose k i * Nat.choose (2 + e - i + (n + 1 - (k + 1))) (n + 1 - (k + 1)))
        = (∑ i ∈ Finset.range (2 + e),
            Nat.choose k i * Nat.choose (2 + e - i + (n + 1 - (k + 1))) (n + 1 - (k + 1)))
        + Nat.choose k (2 + e)
          * Nat.choose (2 + e - (2 + e) + (n + 1 - (k + 1))) (n + 1 - (k + 1)) :=
      Finset.sum_range_succ _ (2 + e)
    have hS1p2 : (∑ i ∈ Finset.range (2 + e),
          Nat.choose k i * Nat.choose (2 + e - i + (n + 1 - (k + 1))) (n + 1 - (k + 1)))
        = (∑ i ∈ Finset.range (e + 1),
            Nat.choose k i * Nat.choose (2 + e - i + (n + 1 - (k + 1))) (n + 1 - (k + 1)))
        + Nat.choose k (e + 1)
          * Nat.choose (2 + e - (e + 1) + (n + 1 - (k + 1))) (n + 1 - (k + 1)) := by
      rw [h2e]
      exact Finset.sum_range_succ _ _
    have hBp1 : (∑ i ∈ Finset.range (2 + e + 1),
          Nat.choose k i * Nat.choose (2 + e - i + (n + 1 - k)) (n + 1 - k))
        = (∑ i ∈ Finset.range (2 + e),
            Nat.choose k i * Nat.choose (2 + e - i + (n + 1 - k)) (n + 1 - k))
        + Nat.choose k (2 + e) * Nat.choose (2 + e - (2 + e) + (n + 1 - k)) (n + 1 - k) :=
      Finset.sum_range_succ _ (2 + e)
    have hBp2 : (∑ i ∈ Finset.range (2 + e),
          Nat.choose k i * Nat.choose (2 + e - i + (n + 1 - k)) (n + 1 - k))
        = (∑ i ∈ Finset.range (e + 1),
            Nat.choose k i * Nat.choose (2 + e - i + (n + 1 - k)) (n + 1 - k))
        + Nat.choose k (e + 1) * Nat.choose (2 + e - (e + 1) + (n + 1 - k)) (n + 1 - k) := by
      rw [h2e]
      exact Finset.sum_range_succ _ _
    have hbulk2 : (∑ i ∈ Finset.range (e + 1),
          Nat.choose k i * Nat.choose (2 + e - i + (n + 1 - (k + 1))) (n + 1 - (k + 1)))
        + (∑ j ∈ Finset.range (e + 1),
          Nat.choose k j * Nat.choose (2 + e - j + (n + 1 - (k + 1))) ((n + 1 - (k + 1)) + 1))
        = (∑ i ∈ Finset.range (e + 1),
          Nat.choose k i * Nat.choose (2 + e - i + (n + 1 - k)) (n + 1 - k)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      have q5 : (2 + e - j + (n + 1 - (k + 1))) + 1 = 2 + e - j + (n + 1 - k) := by omega
      rw [← mul_add, ← Nat.choose_succ_succ', q5, hMM]
    have hbdry : Nat.choose k (e + 1)
        * Nat.choose (2 + e - (e + 1) + (n + 1 - (k + 1))) (n + 1 - (k + 1))
        + Nat.choose k (2 + e) * Nat.choose (2 + e - (2 + e) + (n + 1 - (k + 1))) (n + 1 - (k + 1))
        + Nat.choose k (e + 1)
        = Nat.choose k (e + 1) * Nat.choose (2 + e - (e + 1) + (n + 1 - k)) (n + 1 - k)
        + Nat.choose k (2 + e) * Nat.choose (2 + e - (2 + e) + (n + 1 - k)) (n + 1 - k) := by
      have t1 : 2 + e - (e + 1) + (n + 1 - (k + 1)) = (n + 1 - (k + 1)) + 1 := by omega
      have t2 : 2 + e - (2 + e) + (n + 1 - (k + 1)) = n + 1 - (k + 1) := by omega
      have t3 : 2 + e - (e + 1) + (n + 1 - k) = (n + 1 - k) + 1 := by omega
      have t4 : 2 + e - (2 + e) + (n + 1 - k) = n + 1 - k := by omega
      rw [t1, t2, t3, t4, Nat.choose_succ_self_right, Nat.choose_self,
        Nat.choose_succ_self_right, Nat.choose_self,
        show n + 1 - k = (n + 1 - (k + 1)) + 1 from by omega]
      simp only [mul_add, mul_one]
      ac_rfl
    omega
  · have hd' : d = 0 ∨ d = 1 := by omega
    rw [add_zero]
    rcases hd' with rfl | rfl
    · simp only [Gclosed, Nat.zero_add, Finset.sum_range_one,
        Nat.choose_zero_right, Nat.sub_zero, Nat.choose_self, mul_one]
    · simp only [Gclosed, Finset.sum_range_succ, Finset.sum_range_zero]
      have e1 : 1 - 0 + (n + 1 - (k + 1)) = (n + 1 - (k + 1)) + 1 := by omega
      have e2 : 1 - 1 + (n + 1 - (k + 1)) = n + 1 - (k + 1) := by omega
      have e3 : 1 - 0 + (n + 1 - k) = (n + 1 - k) + 1 := by omega
      have e4 : 1 - 1 + (n + 1 - k) = n + 1 - k := by omega
      rw [e1, e2, e3, e4]
      simp only [Nat.choose_succ_self_right, Nat.choose_self,
        Nat.choose_zero_right, Nat.choose_one_right, mul_one, one_mul]
      omega

/-! ## The count: section length is `2 ^ (n + 1)` -/

/-- `length_section_eq_two_pow`: for
`n + 1` quadrics in `n + 2` variables over a field, the regular-section
length `totalDegree n K G ℓ` is `2 ^ (n + 1)`.

The numerical inputs are explicit: `H`/`hH0`/`hSES` is the Hilbert function
of the successive quadric quotients (base from `hilbertSeries_poly`, step
from a regular sequence via `graded_piece_ses`); `F`/`hSEC` is the section
Hilbert function (step from R1-regularity via `graded_piece_ses`);
`hfilter` is the degree-filtration summation with Artinian bound `B`
(the filtration geometry of `Elimination`/`Counting`). Unfolding
`totalDegree` in `bezout_quadratic` (`Statement.lean`) reduces that goal to
an application of this theorem (no edit of `Statement.lean` here).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Statement.Definitions`,
  `Appendix_FixedPoint.BezoutChain.totalDegree`,
  `Appendix_FixedPoint.BezoutChain.sectionQuotient`.
* `Mathlib/Data/Nat/Choose/Sum.lean`, `Nat.sum_range_choose`.
* `Mathlib/Algebra/Module/Submodule/Lattice.lean`, `Submodule.topEquiv`.
* `Mathlib/LinearAlgebra/Dimension/Finrank.lean`, `LinearEquiv.finrank_eq`. -/
theorem length_section_eq_two_pow (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (H : ℕ → ℕ → ℕ) (F : ℕ → ℕ)
    (hH0 : ∀ d, H 0 d = Nat.choose (d + (n + 2) - 1) ((n + 2) - 1))
    (hSES : ∀ k, k < n + 1 → ∀ d,
      H (k + 1) d + (if 2 ≤ d then H k (d - 2) else 0) = H k d)
    (hSEC : ∀ d,
      F d + (if 1 ≤ d then H (n + 1) (d - 1) else 0) = H (n + 1) d)
    (hfilter : ∃ (B : ℕ) (Cf : ℕ → Submodule K (sectionQuotient n K G ℓ)),
      Cf 0 = ⊥ ∧ Cf (B + 1) = ⊤ ∧
      (∀ d, d ≤ B →
        Module.finrank K ↥(Cf (d + 1)) = Module.finrank K ↥(Cf d) + F d) ∧
      ∀ d, B < d → F d = 0) :
    totalDegree n K G ℓ = 2 ^ (n + 1) := by
  have Hunif : ∀ k, k ≤ n + 1 → ∀ d, H k d = Gclosed n k d := by
    intro k
    induction k with
    | zero => intro _ d; rw [hH0 d, gclosed_zero n d]
    | succ k IH =>
      intro hk d
      have hk' : k < n + 1 := by omega
      have hk'' : k ≤ n + 1 := by omega
      have h1 := hSES k hk' d
      have h2 := gclosed_step n k d hk'
      rw [IH hk'' d, IH hk'' (d - 2)] at h1
      exact Nat.add_right_cancel (h1.trans h2.symm)
  have hGsec : ∀ e, Gclosed n (n + 1) e
      = ∑ i ∈ Finset.range (e + 1), Nat.choose (n + 1) i := by
    intro e
    have hMK : n + 1 - (n + 1) = 0 := by omega
    simp only [Gclosed, hMK, Nat.choose_zero_right, mul_one]
  have HF : ∀ d, F d = Nat.choose (n + 1) d := by
    intro d
    have hsec := hSEC d
    by_cases hd : 1 ≤ d
    · obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 :=
        Nat.exists_eq_succ_of_ne_zero (by omega)
      simp only [hd, ite_true] at hsec
      have he : e + 1 - 1 = e := by omega
      rw [he, Hunif (n + 1) le_rfl (e + 1), Hunif (n + 1) le_rfl e,
        hGsec (e + 1), hGsec e] at hsec
      have hpeel := Finset.sum_range_succ (fun i => Nat.choose (n + 1) i) (e + 1)
      rw [hpeel] at hsec
      omega
    · have hd0 : d = 0 := by omega
      subst hd0
      simp only [hd, ite_false] at hsec
      rw [Hunif (n + 1) le_rfl 0, hGsec 0, show (0 : ℕ) + 1 = 1 from rfl,
        Finset.sum_range_one] at hsec
      omega
  obtain ⟨B, Cf, hC0, hCtop, hCstep, hvan⟩ := hfilter
  have hsum : ∀ m : ℕ, m ≤ B + 1 →
      Module.finrank K ↥(Cf m) = ∑ d ∈ Finset.range m, F d := by
    intro m
    induction m with
    | zero => intro _; rw [hC0]; simp
    | succ m IH =>
      intro hm
      have hmB : m ≤ B := by omega
      have hm' : m ≤ B + 1 := by omega
      rw [hCstep m hmB, IH hm', Finset.sum_range_succ]
  have htop : Module.finrank K (sectionQuotient n K G ℓ)
      = ∑ d ∈ Finset.range (B + 1), F d := by
    have h := hsum (B + 1) le_rfl
    rw [hCtop] at h
    rwa [LinearEquiv.finrank_eq Submodule.topEquiv] at h
  have hKle : n + 1 ≤ B := by
    by_contra hlt
    have hlt' : B < n + 1 := by omega
    have h0 := hvan (n + 1) hlt'
    rw [HF] at h0
    rw [Nat.choose_self] at h0
    exact one_ne_zero h0
  unfold totalDegree
  rw [htop,
    show (∑ d ∈ Finset.range (B + 1), F d)
      = ∑ d ∈ Finset.range (B + 1), Nat.choose (n + 1) d from
      Finset.sum_congr rfl (fun d _ => HF d)]
  have hsplit : B + 1 = (n + 1 + 1) + (B + 1 - (n + 1 + 1)) := by omega
  rw [hsplit, Finset.sum_range_add]
  have htail : ∑ i ∈ Finset.range (B + 1 - (n + 1 + 1)),
      Nat.choose (n + 1) (n + 1 + 1 + i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    apply Nat.choose_eq_zero_of_lt
    omega
  rw [htail, add_zero]
  exact Nat.sum_range_choose (n + 1)

/-! ## Section witnesses `H`/`F` and the section-side telescope -/

/-- The Hilbert-function witness for `length_section_eq_two_pow`: the closed
form `Gclosed n` as a stage-indexed function. At stage `0` this is the
stars-and-bars value (`hwit_hH0`, via `gclosed_zero`), identified with the
polynomial-ring Hilbert function by `hilbertSeries_poly`
(`hwit_geometric_base`); the per-quadric SES recurrence is `gclosed_step`
(`hwit_hSES`).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.Gclosed`
  (this module). -/
def Hwit (n : ℕ) : ℕ → ℕ → ℕ := fun k d => Gclosed n k d

/-- `Hwit` satisfies the `hH0` input shape of `length_section_eq_two_pow`.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.gclosed_zero`
  (this module). -/
theorem hwit_hH0 (n : ℕ) (d : ℕ) :
    Hwit n 0 d = Nat.choose (d + (n + 2) - 1) ((n + 2) - 1) :=
  gclosed_zero n d

/-- `Hwit` satisfies the `hSES` input shape of `length_section_eq_two_pow`.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.gclosed_step`
  (this module). -/
theorem hwit_hSES (n : ℕ) (k d : ℕ) (hk : k < n + 1) :
    Hwit n (k + 1) d + (if 2 ≤ d then Hwit n k (d - 2) else 0)
      = Hwit n k d :=
  gclosed_step n k d hk

/-- Geometric base case: the actual degree-`d` Hilbert function of the
polynomial ring in `n + 2` variables equals the witness `Hwit n 0 d`
(`hilbertSeries_poly` for the geometry, `hwit_hH0` for the witness side).
Together with `hwit_hSES` this discharges the `H`-inputs of
`length_section_eq_two_pow` for `H := Hwit n`.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.hilbertSeries_poly`,
  `Appendix_FixedPoint.BezoutChain.hwit_hH0` (this module). -/
theorem hwit_geometric_base (n : ℕ) (K : Type*) [Field K] (d : ℕ) :
    Module.finrank K (MvPolynomial.homogeneousSubmodule (Fin (n + 2)) K d)
      = Hwit n 0 d := by
  rw [hwit_hH0 n d]
  exact hilbertSeries_poly K (n + 2) d (by omega)

/-- Witness package for the `H`-inputs of `length_section_eq_two_pow`:
`Hwit n` satisfies exactly the `hH0` and `hSES` shapes. The remaining inputs
for a full application, `hSEC` and `hfilter`, are section geometry
(residual gaps, reported, owned with the Elimination/Counting strands).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.hwit_hH0`,
  `Appendix_FixedPoint.BezoutChain.hwit_hSES` (this module). -/
theorem hwit_discharge (n : ℕ) :
    (∀ d, Hwit n 0 d = Nat.choose (d + (n + 2) - 1) ((n + 2) - 1)) ∧
      (∀ k, k < n + 1 → ∀ d,
        Hwit n (k + 1) d + (if 2 ≤ d then Hwit n k (d - 2) else 0)
          = Hwit n k d) :=
  ⟨hwit_hH0 n, fun k hk d => hwit_hSES n k d hk⟩

/-- The `hlow` consumption shape of `exists_regular_quadrics_mkSystem`
(`EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Regularity.Avoid.ResultantLemmas`) and
`avoid_of_hunmixed_ge2`
(`EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Regularity.Avoid.AvoidanceApply`),
discharged from the unconditional bound `hlow_uncond`
(`EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Dimension.HeightLowerBound`, taken as the
explicit
hypothesis `hlowU` — cited, not imported, per narrow-import discipline).
Zero-dimensionality and the containment hypothesis are retained for interface
stability (the consumers' assemblies need `hZd` elsewhere); the height content
is fully unconditional. The remaining R2 inputs are `hZd` (bridges, with the
Counting/Dimension strands) and `hunmixed_ge2` (open research beyond t2a/t2b).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Dimension.HeightLowerBound`,
  `Appendix_FixedPoint.BezoutChain.hlow_uncond`
  (source of `hlowU`).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Regularity.Avoid.ResultantLemmas`,
  `Appendix_FixedPoint.BezoutChain.exists_regular_quadrics_mkSystem` (consumer `hlow` shape).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Regularity.Avoid.AvoidanceApply`,
  `Appendix_FixedPoint.BezoutChain.avoid_of_hunmixed_ge2` (consumer `hlow` shape). -/
theorem hlow_input_of_uncond (n : ℕ) (K : Type*) [Field K] [IsAlgClosed K]
    (S : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (_hZd : IsZeroDimensional n K S)
    (hlowU : ∀ (P : Ideal (MvPolynomial (Fin (n + 2)) K)) [P.IsPrime],
      ((((n + 2 : ℕ))) : WithBot ℕ∞) ≤
        (P.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial (Fin (n + 2)) K ⧸ P))
    (P : Ideal (MvPolynomial (Fin (n + 2)) K)) [P.IsPrime]
    (_hle : Ideal.span (Set.range S) ≤ P) :
    ((((n + 2 : ℕ))) : WithBot ℕ∞) ≤
      (P.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial (Fin (n + 2)) K ⧸ P) :=
  hlowU P

/-- The section-piece witness for `length_section_eq_two_pow`:
filtration-piece dimensions of the section, reusing Filtration's
`sectionPiece` submodules. The section recurrence `hSEC` for this witness is
`hgeom_sec_recurrence` (from `hreg` + `DescentData` + `h0`, all explicit) and
the value `Fsec … 0 = 1` is `fsec_zero_eq_one` (weakest hypothesis:
section nontriviality, discharged from `hG0`).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ChartFiltration`,
  `Appendix_FixedPoint.BezoutChain.sectionPiece`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.hgeom_sec_recurrence`,
  `Appendix_FixedPoint.BezoutChain.fsec_zero_eq_one` (this module).
* `Mathlib/LinearAlgebra/Dimension/Finrank.lean`, `Module.finrank`. -/
noncomputable def Fsec (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) : ℕ → ℕ :=
  fun d => Module.finrank K ↥(sectionPiece n K G ℓ d)

/-- Per-piece finiteness for the section filtration dimensions: over a field,
a submodule of a finite module is finite. The ambient finiteness is the proved
bridge `section_finite_of_artinian` (see `sectionPiece_finite_of`).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.section_finite_of_artinian`,
  `Appendix_FixedPoint.BezoutChain.sectionPiece_finite_of`
  (this module).
* `Mathlib/LinearAlgebra/Dimension/Finrank.lean`, `Module.Finite` (the class
  closed here by instance resolution). -/
theorem sectionPiece_finite (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    [Module.Finite K (sectionQuotient n K G ℓ)] (d : ℕ) :
    Module.Finite K ↥(sectionPiece n K G ℓ d) := inferInstance

/-- Section-side telescope (mirror of the chart-side
`chart_finrank_telescope`): a degree filtration `Cf` of the section with
`Cf 0 = ⊥`, `Cf (B + 1) = ⊤`, and successive steps `F d` sums to the section
length. This is the exact summation interface `hfilter` feeds to
`length_section_eq_two_pow` (whose `hsum`/`htop` steps are factored out here);
the geometric construction of `Cf` from `sectionPiece` is `Cfsec` with the
`hfilter` discharge `cfsec_hfilter` (conditional on the explicit
piece-disjointness `hdisj` and the Artinian bound `hstab`/`hvan`).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.Cfsec`,
  `Appendix_FixedPoint.BezoutChain.cfsec_hfilter` (this module).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ChartFiltration`,
  `Appendix_FixedPoint.BezoutChain.chart_finrank_telescope` (the mirrored chart-side statement).
* `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`,
  `Finset.sum_range_succ`.
* `Mathlib/Algebra/Module/Submodule/Lattice.lean`, `Submodule.topEquiv`.
* `Mathlib/LinearAlgebra/Dimension/Finrank.lean`, `LinearEquiv.finrank_eq`. -/
theorem section_finrank_telescope (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (F : ℕ → ℕ) (B : ℕ)
    (Cf : ℕ → Submodule K (sectionQuotient n K G ℓ))
    (hC0 : Cf 0 = ⊥) (hCtop : Cf (B + 1) = ⊤)
    (hCstep : ∀ d, d ≤ B →
      Module.finrank K ↥(Cf (d + 1)) = Module.finrank K ↥(Cf d) + F d) :
    Module.finrank K (sectionQuotient n K G ℓ)
      = ∑ d ∈ Finset.range (B + 1), F d := by
  have hsum : ∀ m : ℕ, m ≤ B + 1 →
      Module.finrank K ↥(Cf m) = ∑ d ∈ Finset.range m, F d := by
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

/-! ## Section-quotient instances (first-order TC interface) -/

/-- The section quotient is a semiring, stated as a first-order instance on
the `sectionQuotient` abbrev: general quotient instances
(`Ideal.Quotient.semiring` and friends) require the unifier to see through
the nested-quotient abbrev to the `?A ⧸ ?I` shape, which is fragile
(order/cache-dependent) at use sites such as `algebraMap`; this instance
matches first-order so no unfolding is ever needed. The construction itself
is the standard quotient instance (found by `inferInstance` against the
explicit type, which drives TC by the expected type).

## References

* `Mathlib/RingTheory/Ideal/Quotient/Defs.lean`, `Ideal.Quotient.semiring`
  (the construction consumed here). -/
noncomputable instance secSemiring (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) : Semiring (sectionQuotient n K G ℓ) :=
  inferInstance

/-- The section quotient is a `K`-algebra, stated as a first-order instance
for the same reason as `secSemiring` (see there): use sites such as
`algebraMap K (sectionQuotient …)` and `Algebra.smul_def` otherwise hit the
fragile nested-quotient unification. The construction is the standard
iterated-quotient algebra instance.

## References

* `Mathlib/RingTheory/Ideal/Quotient/Operations.lean`
  (the iterated-quotient `Algebra` instance consumed here). -/
noncomputable instance secAlgebra (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) : Algebra K (sectionQuotient n K G ℓ) :=
  inferInstance

/-! ## Ambient finiteness bridge (section-count application, item 1) -/

/-- Each graded piece of the polynomial ring is finite-dimensional over `K`:
`homogeneousSubmodule` is finitely generated (`homogeneousSubmodule_fg`,
using `Finite (Fin (n + 2))`), hence finite (`Module.Finite.of_fg`).

## References

* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.homogeneousSubmodule_fg`.
* `Mathlib/RingTheory/Finiteness/Basic.lean`, `Module.Finite.of_fg`
  (alias of `Module.Finite.iff_fg`). -/
theorem homogeneousPiece_finite (n : ℕ) (K : Type*) [Field K] (d : ℕ) :
    Module.Finite K ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 2)) K d) :=
  Module.Finite.of_fg
    (MvPolynomial.homogeneousSubmodule_fg (Fin (n + 2)) K d)

/-- Ambient finiteness bridge (section-count application piece): under
R1-regularity (`hreg`, Statement's own hypothesis) and zero-dimensionality
(`hZd`), the section quotient is finite over `K`.

The proof is `section_artinian` (Elimination: Artinian from `hreg` + `hZd`)
followed by the Jacobson–Artinian bridge `Module.finite_of_isArtinianRing`
(a finite-type algebra over the Jacobson ring `K` that is Artinian as a ring
is finite): `K` is Jacobson as a field (Artinian via
`DivisionRing.instIsArtinianRing`, Artinian ⇒ Jacobson), and finite-type
flows through both quotients (`Algebra.FiniteType.quotient`).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.Elimination`,
  `Appendix_FixedPoint.BezoutChain.section_artinian`.
* `Mathlib/RingTheory/Jacobson/Artinian.lean`,
  `Module.finite_of_isArtinianRing`.
* `Mathlib/RingTheory/FiniteType.lean`, `Algebra.FiniteType.quotient`
  (both quotient steps) and the MvPolynomial finite-type instance.
* `Mathlib/RingTheory/Artinian/Module.lean`,
  `DivisionRing.instIsArtinianRing` (fields are Artinian).
* `Mathlib/RingTheory/Jacobson/Ring.lean`, the Artinian ⇒ Jacobson
  instance. -/
theorem section_finite_of_artinian (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    (hZd : IsZeroDimensional n K G) :
    Module.Finite K (sectionQuotient n K G ℓ) :=
  @Module.finite_of_isArtinianRing K (sectionQuotient n K G ℓ) _ _ _ _ _
    (section_artinian n K G ℓ hreg hZd)

/-- Per-piece finiteness from the geometric hypotheses (corollary of the
bridge): `sectionPiece_finite` with its ambient-finiteness instance
hypothesis discharged by `section_finite_of_artinian`.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.section_finite_of_artinian`,
  `Appendix_FixedPoint.BezoutChain.sectionPiece_finite`
  (this module). -/
theorem sectionPiece_finite_of (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    (hZd : IsZeroDimensional n K G) (d : ℕ) :
    Module.Finite K ↥(sectionPiece n K G ℓ d) :=
  @sectionPiece_finite n K _ G ℓ (section_finite_of_artinian n K G ℓ hreg hZd) d

/-! ## Section constants: `Fsec … 0 = 1` (section-count application, item 2) -/

/-- The chart linear form evaluates to `0` at the origin (each term
`ℓ j * X j` vanishes at `0`).

## References

* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.eval_C`,
  `MvPolynomial.eval_X` (plus core `map_sum`, `map_mul`, `Pi.zero_apply`,
  `mul_zero`). -/
theorem mkLin_eval_zero (n : ℕ) (K : Type*) [Field K] (ℓ : Fin (n + 2) → K) :
    MvPolynomial.eval (0 : Fin (n + 2) → K) (mkLin n K ℓ) = 0 := by
  simp only [mkLin, map_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, Pi.zero_apply, mul_zero]

/-- The cone is nontrivial when every equation vanishes at `0`: evaluation at
`0` (`evalAtZero`, from Filtration) separates `0` from `1`.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ChartFiltration`,
  `Appendix_FixedPoint.BezoutChain.evalAtZero`. -/
theorem cone_nontrivial_of_evalZero (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hG0 : ∀ i, MvPolynomial.eval (0 : Fin (n + 2) → K) (G i) = 0) :
    Nontrivial (coneQuotient n K G) := by
  have h01 : (0 : coneQuotient n K G) ≠ 1 := by
    intro h
    have h2 := congrArg (evalAtZero n K G hG0) h
    simp only [map_zero, map_one] at h2
    exact zero_ne_one h2
  exact ⟨0, 1, h01⟩

/-- Evaluation at `0` descends to the section: the extra generator `ℓ̄`
itself evaluates to `0` (`mkLin_eval_zero`), so the section quotient admits
the algebra retraction directly extending `evalAtZero`.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ChartFiltration`,
  `Appendix_FixedPoint.BezoutChain.evalAtZero`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.mkLin_eval_zero`
  (this module).
* `Mathlib/RingTheory/Ideal/Quotient/Defs.lean`, `Ideal.Quotient.lift`.
* `Mathlib/RingTheory/Ideal/Span.lean`, `Ideal.span_le`.
* `Mathlib/Algebra/Ring/Basic.lean`, `RingHom.mem_ker`. -/
noncomputable def evalAtZeroSec (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hG0 : ∀ i, MvPolynomial.eval (0 : Fin (n + 2) → K) (G i) = 0) :
    sectionQuotient n K G ℓ →+* K :=
  Ideal.Quotient.lift _ (evalAtZero n K G hG0) (fun a ha => by
    have hsub : ∀ x ∈ ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
        Set (coneQuotient n K G)),
        (evalAtZero n K G hG0) x = 0 := by
      intro x hx
      obtain rfl := Set.mem_singleton_iff.mp hx
      have he : (evalAtZero n K G hG0)
          (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ))
          = MvPolynomial.eval (0 : Fin (n + 2) → K) (mkLin n K ℓ) := rfl
      rw [he, mkLin_eval_zero]
    have hle : Ideal.span ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
        Set (coneQuotient n K G)) ≤ RingHom.ker (evalAtZero n K G hG0) := by
      rw [Ideal.span_le]
      intro x hx
      exact RingHom.mem_ker.mpr (hsub x hx)
    exact RingHom.mem_ker.mp (hle ha))

/-- The section is nontrivial when every equation vanishes at `0`
(the retraction `evalAtZeroSec` separates `0` from `1`).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.evalAtZeroSec`
  (this module). -/
theorem section_nontrivial_of_evalZero (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hG0 : ∀ i, MvPolynomial.eval (0 : Fin (n + 2) → K) (G i) = 0) :
    Nontrivial (sectionQuotient n K G ℓ) := by
  have h01 : (0 : sectionQuotient n K G ℓ) ≠ 1 := by
    intro h
    have h2 := congrArg (evalAtZeroSec n K G ℓ hG0) h
    simp only [map_zero, map_one] at h2
    exact zero_ne_one h2
  exact ⟨0, 1, h01⟩

/-- The section class of a constant lift is the algebra scalar: both
quotient maps send `C c` to `algebraMap c` (Filtration's
`hmap`/`hmapS` computation).

## References

* `Mathlib/Algebra/MvPolynomial/Basic.lean`, `MvPolynomial.algebraMap_eq`.
* `Mathlib/RingTheory/Ideal/Quotient/Operations.lean`,
  `Ideal.Quotient.mk_algebraMap`. -/
theorem secMkC_eq_algebraMap (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (c : K) :
    Ideal.Quotient.mk (Ideal.span
        ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
          Set (coneQuotient n K G)))
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (MvPolynomial.C c))
      = algebraMap K (sectionQuotient n K G ℓ) c := by
  have hC : (MvPolynomial.C c : MvPolynomial (Fin (n + 2)) K)
      = algebraMap K (MvPolynomial (Fin (n + 2)) K) c := by
    rw [MvPolynomial.algebraMap_eq]
  have hcone : Ideal.Quotient.mk (Ideal.span (Set.range G)) (MvPolynomial.C c)
      = algebraMap K (coneQuotient n K G) c := by
    rw [hC]
    rfl
  rw [hcone]
  rfl

/-- The constant section classes: `c ↦ [C c]` inside `sectionPiece 0`.
Linearity is `map_add`/`map_mul` on representatives plus `secMkC_eq_algebraMap`
for the scalar case (Filtration's `gradeMap` pattern).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ChartFiltration`,
  `Appendix_FixedPoint.BezoutChain.sectionPiece`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.secMkC_eq_algebraMap`
  (this module).
* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.isHomogeneous_C`.
* `Mathlib/Algebra/Algebra/Defs.lean`, `Algebra.smul_def`. -/
noncomputable def secConst (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) : K →ₗ[K] ↥(sectionPiece n K G ℓ 0) where
  toFun c := ⟨Ideal.Quotient.mk (Ideal.span
      ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
        Set (coneQuotient n K G)))
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (MvPolynomial.C c)),
    MvPolynomial.C c, MvPolynomial.isHomogeneous_C _ c, rfl⟩
  map_add' c₁ c₂ := by
    apply Subtype.ext
    change Ideal.Quotient.mk (Ideal.span
        ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
          Set (coneQuotient n K G)))
        (Ideal.Quotient.mk (Ideal.span (Set.range G))
          (MvPolynomial.C (c₁ + c₂)))
      = Ideal.Quotient.mk (Ideal.span
        ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
          Set (coneQuotient n K G)))
        (Ideal.Quotient.mk (Ideal.span (Set.range G)) (MvPolynomial.C c₁)) +
        Ideal.Quotient.mk (Ideal.span
        ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
          Set (coneQuotient n K G)))
        (Ideal.Quotient.mk (Ideal.span (Set.range G)) (MvPolynomial.C c₂))
    simp only [map_add MvPolynomial.C, map_add]
  map_smul' r x := by
    apply Subtype.ext
    change Ideal.Quotient.mk (Ideal.span
        ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
          Set (coneQuotient n K G)))
        (Ideal.Quotient.mk (Ideal.span (Set.range G)) (MvPolynomial.C (r • x)))
      = r • Ideal.Quotient.mk (Ideal.span
        ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
          Set (coneQuotient n K G)))
        (Ideal.Quotient.mk (Ideal.span (Set.range G)) (MvPolynomial.C x))
    simp only [smul_eq_mul, map_mul MvPolynomial.C, map_mul,
      Algebra.smul_def (R := K) (A := sectionQuotient n K G ℓ),
      secMkC_eq_algebraMap]

/-- The value of `secConst` on representatives (definitional unfolding,
factored out so kernel/surjectivity proofs need not unfold `secConst`). -/
theorem secConst_val (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (c : K) :
    (secConst n K G ℓ c).val = Ideal.Quotient.mk (Ideal.span
      ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
        Set (coneQuotient n K G)))
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (MvPolynomial.C c)) := rfl

/-- `secConst` is injective over a nontrivial section: a constant class that
vanishes forces its scalar to vanish, since nonzero scalars map to units
(`algebraMap c * algebraMap c⁻¹ = 1`) while `0` is not a unit.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.secConst_val`,
  `Appendix_FixedPoint.BezoutChain.secMkC_eq_algebraMap` (this module).
* `Mathlib/LinearAlgebra/Dimension/Finrank.lean` (`LinearMap.ker_eq_bot`,
  `LinearMap.ker_eq_bot'` kernel criteria).
* Core `mul_inv_cancel₀`, `zero_ne_one`. -/
theorem secConst_injective (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) [Nontrivial (sectionQuotient n K G ℓ)] :
    Function.Injective (secConst n K G ℓ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c hc
  by_contra hcne
  have hval : algebraMap K (sectionQuotient n K G ℓ) c = 0 := by
    have h2 := congrArg Subtype.val hc
    rw [secConst_val, secMkC_eq_algebraMap] at h2
    exact h2
  have hmul : algebraMap K (sectionQuotient n K G ℓ) c
      * algebraMap K (sectionQuotient n K G ℓ) c⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hcne, map_one]
  rw [hval, zero_mul] at hmul
  exact zero_ne_one hmul

/-- `secConst` is surjective: every degree-`0` lift is the constant polynomial
on its constant coefficient (`totalDegree_eq_zero_iff_eq_C`).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.secConst_val`
  (this module).
* `Mathlib/Algebra/MvPolynomial/Degrees.lean`,
  `MvPolynomial.totalDegree_eq_zero_iff_eq_C`.
* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.totalDegree_zero_iff_isHomogeneous`. -/
theorem secConst_surjective (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) :
    Function.Surjective (secConst n K G ℓ) := by
  intro y
  obtain ⟨p, hp, hpy⟩ := y.2
  have htd : p.totalDegree = 0 :=
    (MvPolynomial.totalDegree_zero_iff_isHomogeneous _).mpr hp
  have hC : p = MvPolynomial.C (p.coeff 0) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp htd
  refine ⟨p.coeff 0, ?_⟩
  apply Subtype.ext
  rw [secConst_val, ← hC]
  exact hpy

/-- Section at level `0` is `1` (section-count application piece): the
degree-`0` section piece is `K` itself (`secConst` is bijective over a
nontrivial section), hence one-dimensional. The nontriviality is the weakest
explicit hypothesis — discharged from `hG0` by `section_nontrivial_of_evalZero`.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.secConst`,
  `Appendix_FixedPoint.BezoutChain.secConst_injective`,
  `Appendix_FixedPoint.BezoutChain.secConst_surjective`,
  `Appendix_FixedPoint.BezoutChain.section_nontrivial_of_evalZero` (this module).
* `Mathlib/Algebra/Module/Submodule/Equiv.lean`, `LinearEquiv.ofBijective`.
* `Mathlib/LinearAlgebra/Dimension/Finrank.lean`, `LinearEquiv.finrank_eq`.
* `Mathlib/LinearAlgebra/Dimension/StrongRankCondition.lean`,
  `Module.finrank_self`. -/
theorem fsec_zero_eq_one (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) [Nontrivial (sectionQuotient n K G ℓ)] :
    Fsec n K G ℓ 0 = 1 := by
  have e : K ≃ₗ[K] ↥(sectionPiece n K G ℓ 0) :=
    LinearEquiv.ofBijective (secConst n K G ℓ)
      ⟨secConst_injective n K G ℓ, secConst_surjective n K G ℓ⟩
  rw [show Fsec n K G ℓ 0 = Module.finrank K ↥(sectionPiece n K G ℓ 0) from rfl,
    LinearEquiv.finrank_eq e.symm, Module.finrank_self]

/-! ## Cone pieces and the section SES (section-count application, item 3) -/

/-- The degree-`d` piece of the cone: classes admitting a homogeneous
degree-`d` lift, as a `K`-submodule of the cone quotient. This is the
section-step analogue of `sectionPiece` (same submodule structure, one fewer
quotient layer); it plays the role of the stage-`K` Hilbert-function domain
for the section recurrence `hSEC`.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ChartFiltration`,
  `Appendix_FixedPoint.BezoutChain.sectionPiece`
  (the mirrored section-side definition).
* `Mathlib/RingTheory/Ideal/Quotient/Defs.lean`, `Ideal.Quotient.mk`.
* `Mathlib/Algebra/Algebra/Defs.lean`, `Algebra.smul_def`.
* `Mathlib/RingTheory/Ideal/Quotient/Operations.lean`,
  `Ideal.Quotient.mk_algebraMap`.
* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.isHomogeneous_C`, `MvPolynomial.isHomogeneous_zero`,
  `MvPolynomial.IsHomogeneous.add/mul`. -/
noncomputable def conePiece (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K) (d : ℕ) :
    Submodule K (coneQuotient n K G) where
  carrier := {x | ∃ p : MvPolynomial (Fin (n + 2)) K, p.IsHomogeneous d ∧
    Ideal.Quotient.mk (Ideal.span (Set.range G)) p = x}
  add_mem' := by
    intro x y hx hy
    obtain ⟨p, hp, epx⟩ := hx
    obtain ⟨q, hq, eqy⟩ := hy
    refine ⟨p + q, hp.add hq, ?_⟩
    rw [map_add, epx, eqy]
  zero_mem' := by
    refine ⟨0, MvPolynomial.isHomogeneous_zero _ _ d, ?_⟩
    rw [map_zero]
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
    have esmul : c • Ideal.Quotient.mk (Ideal.span (Set.range G)) p
        = algebraMap K (coneQuotient n K G) c
          * Ideal.Quotient.mk (Ideal.span (Set.range G)) p :=
      Algebra.smul_def (A := coneQuotient n K G) c _
    rw [map_mul, ← hmapS, ← esmul, ← epx]

/-- The geometric stage-`K` Hilbert function: dimensions of the cone pieces.
This is the geometric `H (n + 1)` for the section recurrence `hSEC`
(`hgeom_sec_recurrence`); its identification with the closed form
`Gclosed n (n + 1)` is conditional on the `hSES` input shape (residual gap,
blocked on the graded-quotient API — see `heq_gclosed_of_shapes`).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.conePiece`
  (this module).
* `Mathlib/LinearAlgebra/Dimension/Finrank.lean`, `Module.finrank`. -/
noncomputable def Hgeom (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K) : ℕ → ℕ :=
  fun d => Module.finrank K ↥(conePiece n K G d)

/-- Each cone piece is finite: it is the surjective image of the finite
polynomial-ring piece (`homogeneousPiece_finite`). Finiteness of the domain
is an explicit instance hypothesis (supplied by `homogeneousPiece_finite`),
so no local-instance bookkeeping is needed.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.homogeneousPiece_finite` (this module).
* `Mathlib/RingTheory/Finiteness/Basic.lean`,
  `Module.Finite.of_surjective`. -/
theorem conePiece_finite (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K) (d : ℕ)
    [Module.Finite K ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 2)) K d)] :
    Module.Finite K ↥(conePiece n K G d) := by
  let f : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 2)) K d) →ₗ[K]
      ↥(conePiece n K G d) :=
    { toFun := fun x =>
        ⟨Ideal.Quotient.mk (Ideal.span (Set.range G)) x.val, x.val, x.2, rfl⟩
      map_add' := fun x y => Subtype.ext
        (map_add (Ideal.Quotient.mk (Ideal.span (Set.range G))) x.val y.val)
      map_smul' := fun r x => by
        apply Subtype.ext
        change Ideal.Quotient.mk (Ideal.span (Set.range G)) (r • x.val)
          = r • Ideal.Quotient.mk (Ideal.span (Set.range G)) x.val
        rw [Algebra.smul_def (R := K) (A := MvPolynomial (Fin (n + 2)) K),
          map_mul, Ideal.Quotient.mk_algebraMap K _ _,
          Algebra.smul_def (R := K) (A := coneQuotient n K G)] }
  refine Module.Finite.of_surjective f (fun y => ?_)
  obtain ⟨a, ha, haa⟩ := y.2
  exact ⟨⟨a, ha⟩, Subtype.ext haa⟩

/-- Multiplication by `ℓ̄` between cone pieces (the section-step `f` for
`graded_piece_ses`): `×ℓ̄` sends homogeneous degree-`d` lifts to homogeneous
degree-`(d + 1)` lifts (`mkLin_isHomogeneous.mul`). This mirrors the
`gradeMul` quadric step (shift `2`, proved as `baseMul` in
`MkSystemSESData`) at shift `1`.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ChartFiltration`,
  `Appendix_FixedPoint.BezoutChain.mkLin_isHomogeneous`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Regularity.Avoid.MkSystemSESData`,
  `Appendix_FixedPoint.BezoutChain.MkSystemSESData.baseMul`
  (the mirrored quadric-step map).
* `Mathlib/Algebra/Group/Action/Defs.lean`, `mul_smul_comm`. -/
noncomputable def coneMul (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (d : ℕ) :
    ↥(conePiece n K G d) →ₗ[K] ↥(conePiece n K G (d + 1)) where
  toFun x := ⟨Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ) * x.val,
    by
      obtain ⟨p, hp, hpx⟩ := x.2
      exact ⟨mkLin n K ℓ * p, add_comm 1 d ▸ (mkLin_isHomogeneous n K ℓ).mul hp,
        by rw [← hpx, map_mul]⟩⟩
  map_add' x y := Subtype.ext (mul_add
    (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) x.val y.val)
  map_smul' r x := Subtype.ext (mul_smul_comm r
    (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) x.val)

/-- Injectivity of `coneMul` from R1-regularity (`hreg`, i.e. Statement's own
hypothesis): restriction of the injective `ℓ̄ • ·` map. Mirrors the
`gradeMul_injective` quadric-step pattern.

## References

* `Mathlib/Algebra/Group/Action/Defs.lean`, `smul_eq_mul`. -/
theorem coneMul_injective (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (d : ℕ)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ))) :
    Function.Injective (coneMul n K G ℓ d) := by
  intro x y h
  have hmul : Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ) * x.val
      = Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ) * y.val :=
    congrArg Subtype.val h
  have hsmul : (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) • x.val
      = (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) • y.val := by
    rwa [smul_eq_mul, smul_eq_mul]
  exact Subtype.ext (hreg hsmul)

/-- The section projection between graded pieces (the section-step quotient
map for `graded_piece_ses`): send a cone class to its section class. Every
section class with a homogeneous lift comes from the cone class of the same
lift (`secProj_surjective`).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ChartFiltration`,
  `Appendix_FixedPoint.BezoutChain.sectionPiece`.
* `Mathlib/Algebra/Algebra/Defs.lean`, `Algebra.smul_def`.
* `Mathlib/RingTheory/Ideal/Quotient/Operations.lean`,
  `Ideal.Quotient.mk_algebraMap`. -/
noncomputable def secProj (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (d : ℕ) :
    ↥(conePiece n K G d) →ₗ[K] ↥(sectionPiece n K G ℓ d) where
  toFun x := ⟨Ideal.Quotient.mk (Ideal.span
      ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
        Set (coneQuotient n K G))) x.val,
    by
      obtain ⟨p, hp, hpx⟩ := x.2
      exact ⟨p, hp, by rw [hpx]⟩⟩
  map_add' x y := Subtype.ext (map_add (Ideal.Quotient.mk (Ideal.span
      ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
        Set (coneQuotient n K G)))) x.val y.val)
  map_smul' r x := by
    apply Subtype.ext
    change Ideal.Quotient.mk (Ideal.span
        ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
          Set (coneQuotient n K G))) (r • x.val)
      = r • Ideal.Quotient.mk (Ideal.span
        ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
          Set (coneQuotient n K G))) x.val
    rw [Algebra.smul_def (R := K) (A := coneQuotient n K G),
      Algebra.smul_def (R := K) (A := sectionQuotient n K G ℓ),
      map_mul, Ideal.Quotient.mk_algebraMap K _ _]

/-- The value of `secProj` on representatives (definitional unfolding,
factored out so surjectivity and exactness proofs need not unfold
`secProj`). -/
theorem secProj_val (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (d : ℕ) (x : ↥(conePiece n K G d)) :
    (secProj n K G ℓ d x).val = Ideal.Quotient.mk (Ideal.span
      ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
        Set (coneQuotient n K G))) x.val := rfl

/-- `secProj` is surjective onto the section piece (every homogeneous lift
occurs).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.secProj_val`
  (this module).
* `Mathlib/Algebra/Module/Submodule/Lattice.lean` (`Subtype.ext` is core). -/
theorem secProj_surjective (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (d : ℕ) :
    Function.Surjective (secProj n K G ℓ d) := by
  intro y
  obtain ⟨p, hp, hpy⟩ := y.2
  refine ⟨⟨Ideal.Quotient.mk (Ideal.span (Set.range G)) p, p, hp, rfl⟩, ?_⟩
  apply Subtype.ext
  rw [secProj_val]
  exact hpy

/-- Kernel of the section projection is the range of `coneMul` (exactness at
the middle): `ℓ̄` dies in the section (easy inclusion), and a lift mapping to
`0` is divisible by `ℓ̄` with homogeneous cofactor by `DescentData` (hard
inclusion, mirroring `gradeMap_ker_eq`).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ChartFiltration`,
  `Appendix_FixedPoint.BezoutChain.gradeMap_ker_eq`, `Appendix_FixedPoint.BezoutChain.DescentData`.
* `Mathlib/RingTheory/Ideal/Quotient/Defs.lean`,
  `Ideal.Quotient.eq_zero_iff_mem`.
* `Mathlib/RingTheory/Ideal/Span.lean`, `Ideal.mem_span_singleton'`. -/
theorem secKer_eq_range (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (d : ℕ)
    (hdesc : DescentData n K G ℓ d) :
    LinearMap.ker (secProj n K G ℓ (d + 1))
      = LinearMap.range (coneMul n K G ℓ d) := by
  ext x
  constructor
  · intro hx
    rw [LinearMap.mem_ker] at hx
    obtain ⟨p, hp, hpx⟩ := x.2
    have h0 : (secProj n K G ℓ (d + 1) x).val = 0 := congrArg Subtype.val hx
    have hclass : Ideal.Quotient.mk (Ideal.span
        ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
          Set (coneQuotient n K G)))
        (Ideal.Quotient.mk (Ideal.span (Set.range G)) p) = 0 := by
      rw [hpx]
      exact h0
    rw [Ideal.Quotient.eq_zero_iff_mem] at hclass
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hclass
    obtain ⟨q, hq, eq⟩ := hdesc p t hp ht.symm
    refine ⟨⟨Ideal.Quotient.mk (Ideal.span (Set.range G)) q, q, hq, rfl⟩, ?_⟩
    apply Subtype.ext
    change Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)
        * Ideal.Quotient.mk (Ideal.span (Set.range G)) q = x.val
    rw [← hpx, eq, mul_comm]
    exact ht
  · rintro ⟨w, rfl⟩
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    change Ideal.Quotient.mk (Ideal.span
        ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
          Set (coneQuotient n K G)))
        (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ) * w.val)
        = 0
    have hℓ0 : Ideal.Quotient.mk (Ideal.span
        ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
          Set (coneQuotient n K G)))
        (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_span_singleton'.mpr ⟨1, one_mul _⟩)
    rw [map_mul, hℓ0, zero_mul]

/-- Section-step cokernel identification: the abstract cokernel of `coneMul`
is the section piece — via the first isomorphism theorem
(`quotKerEquivRange`) after rewriting the kernel by `secKer_eq_range`.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.secKer_eq_range`
  (this module).
* `Mathlib/LinearAlgebra/Isomorphisms.lean`,
  `LinearMap.quotKerEquivRange`. -/
noncomputable def secCokernelEquiv (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (d : ℕ)
    (hdesc : DescentData n K G ℓ d) :
    (↥(conePiece n K G (d + 1)) ⧸ LinearMap.range (coneMul n K G ℓ d)) ≃ₗ[K]
      ↥(sectionPiece n K G ℓ (d + 1)) := by
  have htop : LinearMap.range (secProj n K G ℓ (d + 1)) = ⊤ :=
    LinearMap.range_eq_top.mpr (secProj_surjective n K G ℓ (d + 1))
  have e₂ : ↥(LinearMap.range (secProj n K G ℓ (d + 1))) ≃ₗ[K]
      ↥(sectionPiece n K G ℓ (d + 1)) := by
    rw [htop]
    exact Submodule.topEquiv
  rw [← secKer_eq_range n K G ℓ d hdesc]
  exact (secProj n K G ℓ (d + 1)).quotKerEquivRange.trans e₂

/-- One full section-recurrence step with identified ends: the graded finrank
recurrence `Hgeom (d+1) = Hgeom d + Fsec (d+1)`. Regularity `hreg`
(R1, i.e. Statement's own hypothesis) enters only via `coneMul_injective`;
the cokernel is identified by `secCokernelEquiv` (from `DescentData`).
Finiteness of the cone pieces is an explicit instance hypothesis (supplied
by `conePiece_finite` from `homogeneousPiece_finite`).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.graded_piece_ses`,
  `Appendix_FixedPoint.BezoutChain.coneMul_injective`,
  `Appendix_FixedPoint.BezoutChain.secCokernelEquiv`,
  `Appendix_FixedPoint.BezoutChain.conePiece_finite`,
  `Appendix_FixedPoint.BezoutChain.Hgeom`, `Appendix_FixedPoint.BezoutChain.Fsec` (this module). -/
theorem hgeom_sec_succ (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (d : ℕ)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    (hdesc : DescentData n K G ℓ d)
    [Module.Finite K ↥(conePiece n K G d)]
    [Module.Finite K ↥(conePiece n K G (d + 1))] :
    Hgeom n K G (d + 1) = Hgeom n K G d + Fsec n K G ℓ (d + 1) := by
  have h := graded_piece_ses K _ _ _ (coneMul n K G ℓ d)
    (secCokernelEquiv n K G ℓ d hdesc) (coneMul_injective n K G ℓ d hreg)
  change Module.finrank K ↥(conePiece n K G (d + 1))
      = Module.finrank K ↥(conePiece n K G d)
        + Module.finrank K ↥(sectionPiece n K G ℓ (d + 1))
  exact h

/-- The cone class of a constant lift is the algebra scalar (single-layer
version of `secMkC_eq_algebraMap`).

## References

* `Mathlib/Algebra/MvPolynomial/Basic.lean`, `MvPolynomial.algebraMap_eq`.
* `Mathlib/RingTheory/Ideal/Quotient/Operations.lean`,
  `Ideal.Quotient.mk_algebraMap`. -/
theorem coneMkC_eq_algebraMap (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K) (c : K) :
    Ideal.Quotient.mk (Ideal.span (Set.range G)) (MvPolynomial.C c)
      = algebraMap K (coneQuotient n K G) c := by
  have hC : (MvPolynomial.C c : MvPolynomial (Fin (n + 2)) K)
      = algebraMap K (MvPolynomial (Fin (n + 2)) K) c := by
    rw [MvPolynomial.algebraMap_eq]
  rw [hC]
  rfl

/-- The constant cone classes: `c ↦ [C c]` inside `conePiece 0` (single-layer
version of `secConst`).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.conePiece`,
  `Appendix_FixedPoint.BezoutChain.coneMkC_eq_algebraMap` (this module).
* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.isHomogeneous_C`.
* `Mathlib/Algebra/Algebra/Defs.lean`, `Algebra.smul_def`. -/
noncomputable def coneConst (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K) :
    K →ₗ[K] ↥(conePiece n K G 0) where
  toFun c := ⟨Ideal.Quotient.mk (Ideal.span (Set.range G)) (MvPolynomial.C c),
    MvPolynomial.C c, MvPolynomial.isHomogeneous_C _ c, rfl⟩
  map_add' c₁ c₂ := by
    apply Subtype.ext
    change Ideal.Quotient.mk (Ideal.span (Set.range G))
          (MvPolynomial.C (c₁ + c₂))
        = Ideal.Quotient.mk (Ideal.span (Set.range G)) (MvPolynomial.C c₁) +
          Ideal.Quotient.mk (Ideal.span (Set.range G)) (MvPolynomial.C c₂)
    simp only [map_add MvPolynomial.C, map_add]
  map_smul' r x := by
    apply Subtype.ext
    change Ideal.Quotient.mk (Ideal.span (Set.range G)) (MvPolynomial.C (r • x))
        = r • Ideal.Quotient.mk (Ideal.span (Set.range G)) (MvPolynomial.C x)
    simp only [smul_eq_mul, map_mul MvPolynomial.C, map_mul,
      Algebra.smul_def (R := K) (A := coneQuotient n K G),
      coneMkC_eq_algebraMap]

/-- The value of `coneConst` on representatives (definitional unfolding). -/
theorem coneConst_val (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K) (c : K) :
    (coneConst n K G c).val
      = Ideal.Quotient.mk (Ideal.span (Set.range G)) (MvPolynomial.C c) := rfl

/-- `coneConst` is injective over a nontrivial cone (nonzero scalars map to
units; single-layer version of `secConst_injective`).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.coneConst_val`,
  `Appendix_FixedPoint.BezoutChain.coneMkC_eq_algebraMap` (this module).
* `Mathlib/LinearAlgebra/Dimension/Finrank.lean` (`LinearMap.ker_eq_bot`,
  `LinearMap.ker_eq_bot'` kernel criteria).
* Core `mul_inv_cancel₀`, `zero_ne_one`. -/
theorem coneConst_injective (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    [Nontrivial (coneQuotient n K G)] :
    Function.Injective (coneConst n K G) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c hc
  by_contra hcne
  have hval : algebraMap K (coneQuotient n K G) c = 0 := by
    have h2 := congrArg Subtype.val hc
    rw [coneConst_val, coneMkC_eq_algebraMap] at h2
    exact h2
  have hmul : algebraMap K (coneQuotient n K G) c
      * algebraMap K (coneQuotient n K G) c⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hcne, map_one]
  rw [hval, zero_mul] at hmul
  exact zero_ne_one hmul

/-- `coneConst` is surjective (single-layer version of
`secConst_surjective`).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.coneConst_val`
  (this module).
* `Mathlib/Algebra/MvPolynomial/Degrees.lean`,
  `MvPolynomial.totalDegree_eq_zero_iff_eq_C`.
* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.totalDegree_zero_iff_isHomogeneous`. -/
theorem coneConst_surjective (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K) :
    Function.Surjective (coneConst n K G) := by
  intro y
  obtain ⟨p, hp, hpy⟩ := y.2
  have htd : p.totalDegree = 0 :=
    (MvPolynomial.totalDegree_zero_iff_isHomogeneous _).mpr hp
  have hC : p = MvPolynomial.C (p.coeff 0) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp htd
  refine ⟨p.coeff 0, ?_⟩
  apply Subtype.ext
  rw [coneConst_val, ← hC]
  exact hpy

/-- The cone piece at level `0` is `1` (over a nontrivial cone).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.coneConst`,
  `Appendix_FixedPoint.BezoutChain.coneConst_injective`,
  `Appendix_FixedPoint.BezoutChain.coneConst_surjective`,
  `Appendix_FixedPoint.BezoutChain.cone_nontrivial_of_evalZero` (this module).
* `Mathlib/Algebra/Module/Submodule/Equiv.lean`, `LinearEquiv.ofBijective`.
* `Mathlib/LinearAlgebra/Dimension/Finrank.lean`, `LinearEquiv.finrank_eq`.
* `Mathlib/LinearAlgebra/Dimension/StrongRankCondition.lean`,
  `Module.finrank_self`. -/
theorem conePiece_zero_eq_one (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    [Nontrivial (coneQuotient n K G)] :
    Hgeom n K G 0 = 1 := by
  have e : K ≃ₗ[K] ↥(conePiece n K G 0) :=
    LinearEquiv.ofBijective (coneConst n K G)
      ⟨coneConst_injective n K G, coneConst_surjective n K G⟩
  rw [show Hgeom n K G 0 = Module.finrank K ↥(conePiece n K G 0) from rfl,
    LinearEquiv.finrank_eq e.symm, Module.finrank_self]

/-- The degree-`0` values agree (both are `1`): the `d = 0` case of the
section recurrence, from the two nontriviality hypotheses (each discharged
from `hG0` by `cone_nontrivial_of_evalZero` /
`section_nontrivial_of_evalZero`).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.fsec_zero_eq_one`,
  `Appendix_FixedPoint.BezoutChain.conePiece_zero_eq_one` (this module). -/
theorem hgeom_sec_zero_eq (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    [Nontrivial (coneQuotient n K G)]
    [Nontrivial (sectionQuotient n K G ℓ)] :
    Fsec n K G ℓ 0 = Hgeom n K G 0 := by
  rw [fsec_zero_eq_one, conePiece_zero_eq_one]

/-- The `hSEC` input shape for `Fsec`/`Hgeom` (`hSEC-for-Fsec`, section-count
application piece): the section Hilbert function satisfies
`Fsec d + (if 1 ≤ d then Hgeom (d-1) else 0) = Hgeom d`. The successor case
is `hgeom_sec_succ` (from `hreg` + `DescentData`, both explicit); the
`d = 0` case is the explicit hypothesis `h0` (discharged by
`hgeom_sec_zero_eq`).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.hgeom_sec_succ`,
  `Appendix_FixedPoint.BezoutChain.hgeom_sec_zero_eq` (this module).
* `Mathlib/Data/Nat/Choose/Basic.lean` (`Nat.exists_eq_succ_of_ne_zero`,
  used here in the same shape as `length_section_eq_two_pow`). -/
theorem hgeom_sec_recurrence (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    (hdesc : ∀ d, DescentData n K G ℓ d)
    (h0 : Fsec n K G ℓ 0 = Hgeom n K G 0) (d : ℕ) :
    Fsec n K G ℓ d + (if 1 ≤ d then Hgeom n K G (d - 1) else 0)
      = Hgeom n K G d := by
  by_cases hd : 1 ≤ d
  · obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 :=
      Nat.exists_eq_succ_of_ne_zero (by omega)
    simp only [hd, ite_true]
    have he : e + 1 - 1 = e := by omega
    rw [he]
    have h := @hgeom_sec_succ n K _ G ℓ e hreg (hdesc e)
      (@conePiece_finite n K _ G e (@homogeneousPiece_finite n K _ e))
      (@conePiece_finite n K _ G (e + 1)
        (@homogeneousPiece_finite n K _ (e + 1)))
    omega
  · have hd0 : d = 0 := by omega
    subst hd0
    simp only [hd, ite_false, add_zero]
    exact h0

/-! ## Geometric filtration and closed-form identification (item 4) -/

/-- The geometric degree filtration of the section: `Cfsec d` is the span of
the section pieces below `d` (`Cfsec (d+1) = Cfsec d ⊔ sectionPiece d`, so
`Cfsec 0 = ⊥`). This is the geometric `Cf` for the `hfilter` input of
`length_section_eq_two_pow`; the step equation needs piece-disjointness and
the top/vanishing need the Artinian bound (all explicit hypotheses of
`cfsec_hfilter`).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ChartFiltration`,
  `Appendix_FixedPoint.BezoutChain.sectionPiece`.
* `Mathlib/Order/Monotone/Basic.lean`, `monotone_nat_of_le_succ`. -/
noncomputable def Cfsec (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) : ℕ → Submodule K (sectionQuotient n K G ℓ)
  | 0 => ⊥
  | d + 1 => Cfsec n K G ℓ d ⊔ sectionPiece n K G ℓ d

/-- `Cfsec` starts at `⊥`. -/
theorem cfsec_zero (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) : Cfsec n K G ℓ 0 = ⊥ := rfl

/-- `Cfsec` accumulates one more section piece per step. -/
theorem cfsec_succ (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (d : ℕ) :
    Cfsec n K G ℓ (d + 1) = Cfsec n K G ℓ d ⊔ sectionPiece n K G ℓ d := rfl

/-- The geometric filtration is monotone. -/
theorem cfsec_mono (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) : Monotone (Cfsec n K G ℓ) := by
  apply monotone_nat_of_le_succ
  intro d
  rw [cfsec_succ]
  exact le_sup_left

/-- The `hfilter` input for `Fsec`/`Cfsec`, conditional on the two genuine
geometric gaps (both explicit): piece-disjointness `hdisj` (subquotient
disjointness: each graded piece meets the span of lower pieces trivially)
and the Artinian bound `B` with stabilization `hstab` and vanishing `hvan`
(Counting finite-length bridge). Ambient finiteness is the proved
bridge `section_finite_of_artinian` (taken as an instance hypothesis here).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.Cfsec`,
  `Appendix_FixedPoint.BezoutChain.cfsec_succ`, `Appendix_FixedPoint.BezoutChain.Fsec`,
  `Appendix_FixedPoint.BezoutChain.section_finite_of_artinian` (this module).
* `Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean`,
  `Submodule.finrank_sup_add_finrank_inf_eq`.
* `Mathlib/Order/Disjoint.lean`, `disjoint_iff_inf_le`.
* `Mathlib/LinearAlgebra/Dimension/Finrank.lean`, `finrank_bot`. -/
theorem cfsec_hfilter (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (B : ℕ)
    [Module.Finite K (sectionQuotient n K G ℓ)]
    (hdisj : ∀ d, d ≤ B → Disjoint (Cfsec n K G ℓ d) (sectionPiece n K G ℓ d))
    (hstab : Cfsec n K G ℓ (B + 1) = ⊤)
    (hvan : ∀ d, B < d → Fsec n K G ℓ d = 0) :
    ∃ (B' : ℕ) (Cf : ℕ → Submodule K (sectionQuotient n K G ℓ)),
      Cf 0 = ⊥ ∧ Cf (B' + 1) = ⊤ ∧
      (∀ d, d ≤ B' →
        Module.finrank K ↥(Cf (d + 1)) = Module.finrank K ↥(Cf d)
          + Fsec n K G ℓ d) ∧
      ∀ d, B' < d → Fsec n K G ℓ d = 0 := by
  refine ⟨B, Cfsec n K G ℓ, rfl, hstab, ?_, hvan⟩
  intro d hd
  have hstep := Submodule.finrank_sup_add_finrank_inf_eq
    (Cfsec n K G ℓ d) (sectionPiece n K G ℓ d)
  have hinf : Cfsec n K G ℓ d ⊓ sectionPiece n K G ℓ d = ⊥ :=
    le_antisymm (disjoint_iff_inf_le.mp (hdisj d hd)) bot_le
  rw [hinf, finrank_bot, add_zero] at hstep
  rw [cfsec_succ]
  exact hstep

/-- Closed-form identification for abstract stage-indexed Hilbert functions
(`Gclosed`-vs-geometry, factored out of `length_section_eq_two_pow`): any
`H` satisfying the `hH0` base shape and the `hSES` recurrence shape equals
`Gclosed` at every stage `k ≤ n + 1`. The geometric instance (with
`H` built from quotient graded pieces) awaits the `hSES` discharge, which
is blocked on the graded-quotient API (out of scope here).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.gclosed_zero`,
  `Appendix_FixedPoint.BezoutChain.gclosed_step` (this module). -/
theorem heq_gclosed_of_shapes (n : ℕ) (H : ℕ → ℕ → ℕ)
    (hH0 : ∀ d, H 0 d = Nat.choose (d + (n + 2) - 1) ((n + 2) - 1))
    (hSES : ∀ k, k < n + 1 → ∀ d,
      H (k + 1) d + (if 2 ≤ d then H k (d - 2) else 0) = H k d)
    (k : ℕ) (hk : k ≤ n + 1) (d : ℕ) : H k d = Gclosed n k d := by
  revert hk d
  induction k with
  | zero => intro _ d; rw [hH0 d, gclosed_zero n d]
  | succ k IH =>
    intro hk d
    have hk' : k < n + 1 := by omega
    have hk'' : k ≤ n + 1 := by omega
    have h1 := hSES k hk' d
    have h2 := gclosed_step n k d hk'
    rw [IH hk'' d, IH hk'' (d - 2)] at h1
    exact Nat.add_right_cancel (h1.trans h2.symm)

/-- The `hSEC` input shape for `Fsec` against the closed form: combining the
geometric section recurrence (`hgeom_sec_recurrence`) with the last-stage
identification hypothesis `hHeq` (`Hgeom = Gclosed n (n+1)`, itself
conditional on the blocked `hSES` input via `heq_gclosed_of_shapes`) gives
exactly the `hSEC` shape `length_section_eq_two_pow` consumes with
`F := Fsec …` and `H := Hwit n`.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.hgeom_sec_recurrence`,
  `Appendix_FixedPoint.BezoutChain.heq_gclosed_of_shapes`,
  `Appendix_FixedPoint.BezoutChain.Hwit` (this module). -/
theorem fsec_hSEC_closed (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    (hdesc : ∀ d, DescentData n K G ℓ d)
    (h0 : Fsec n K G ℓ 0 = Hgeom n K G 0)
    (hHeq : ∀ d, Hgeom n K G d = Gclosed n (n + 1) d) (d : ℕ) :
    Fsec n K G ℓ d + (if 1 ≤ d then Hwit n (n + 1) (d - 1) else 0)
      = Hwit n (n + 1) d := by
  have hrec := hgeom_sec_recurrence n K G ℓ hreg hdesc h0 d
  rw [hHeq d, hHeq (d - 1)] at hrec
  change Fsec n K G ℓ d + (if 1 ≤ d then Gclosed n (n + 1) (d - 1) else 0)
      = Gclosed n (n + 1) d
  exact hrec

/-! ## hSES from graded SES data (section-count application, item 5) -/

/-- Single-step SES recurrence from graded-piece data: the exact inputs of
`graded_piece_ses` (`f` / `e` / `hinj`, in verbatim shape) plus the three
finrank identifications give one `a + b = c` equation, i.e. one
`H (k+1) d + H k (d-2) = H k d` instance of the `hSES` numerical shape of
`length_section_eq_two_pow`. This is the per-`(k,d)` instantiation link
between the graded SES mechanism and `hSES`; `hSES_of_steps` assembles these
steps (with the low-degree agreement `hlow`) into the full `hSES` input.
The geometric instantiation at step `0` from R2 output is
`hSES_step_of_pieceSES` at `k = 0` (conditional on the cokernel
identification); steps `k ≥ 1` need the graded-quotient API (out of
scope — see `## Added hypotheses and deviations` above).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.graded_piece_ses`,
  `Appendix_FixedPoint.BezoutChain.hSES_of_steps`,
  `Appendix_FixedPoint.BezoutChain.length_section_eq_two_pow` (this module).
* Step-`0` geometric instance: `hSES_step_of_pieceSES` at `k = 0`
  (this module). -/
theorem hSES_step_of_pieceSES (K : Type*) [Field K]
    (a b c : ℕ)
    (P Q R : Type*) [AddCommGroup P] [AddCommGroup Q] [AddCommGroup R]
    [Module K P] [Module K Q] [Module K R]
    [Module.Finite K P] [Module.Finite K Q]
    (f : P →ₗ[K] Q) (e : (Q ⧸ LinearMap.range f) ≃ₗ[K] R)
    (hinj : Function.Injective f)
    (ha : a = Module.finrank K R)
    (hb : b = Module.finrank K P)
    (hc : c = Module.finrank K Q) :
    a + b = c := by
  rw [ha, hb, hc]
  have h := graded_piece_ses K P Q R f e hinj
  omega

/-- Assembly of per-step recurrences into the `hSES` input shape of
`length_section_eq_two_pow`: the `2 ≤ d` case is the graded-SES step
(`hstep`, discharged per-`(k,d)` by `hSES_step_of_pieceSES`), the `d < 2`
case is the low-degree agreement (`hlow`: degree-`0`/`1` pieces are
constants/linear forms surviving every quotient — explicit since the stage
pieces for `k ≥ 1` are unstatable without the graded-quotient API).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.hSES_step_of_pieceSES`,
  `Appendix_FixedPoint.BezoutChain.length_section_eq_two_pow`
  (this module). -/
theorem hSES_of_steps (n : ℕ) (H : ℕ → ℕ → ℕ)
    (hstep : ∀ k, k < n + 1 → ∀ d, 2 ≤ d →
      H (k + 1) d + H k (d - 2) = H k d)
    (hlow : ∀ k, k < n + 1 → ∀ d, d < 2 →
      H (k + 1) d = H k d) :
    ∀ k, k < n + 1 → ∀ d,
      H (k + 1) d + (if 2 ≤ d then H k (d - 2) else 0) = H k d := by
  intro k hk d
  by_cases hd : 2 ≤ d
  · simp only [hd, ite_true]; exact hstep k hk d hd
  · simp only [hd, ite_false, add_zero]; exact hlow k hk d (by omega)

/-- Quadrics vanish at the origin: `IsHomogeneous 2` forces `eval 0 = 0`
(the constant coefficient of a positive-degree homogeneous polynomial is `0`).
Discharges the `hG0` hypothesis of the nontriviality lemmas
(`cone_nontrivial_of_evalZero`, `section_nontrivial_of_evalZero`) from
Statement's own `hG`. Proof copied from `exists_regular_quadrics`
(`ResultantLemmas.lean`, `heval0`).

## References

* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.eval_zero`.
* `Mathlib/Algebra/MvPolynomial/Basic.lean`, `MvPolynomial.constantCoeff_eq`.
* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.IsHomogeneous.coeff_eq_zero`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Regularity.Avoid.ResultantLemmas`,
  `Appendix_FixedPoint.BezoutChain.exists_regular_quadrics` (proof source, `heval0`).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.cone_nontrivial_of_evalZero`,
  `Appendix_FixedPoint.BezoutChain.section_nontrivial_of_evalZero` (this module, consumers). -/
theorem evalZero_of_homogTwo (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hG : ∀ i, (G i).IsHomogeneous 2) (i : Fin (n + 1)) :
    MvPolynomial.eval (0 : Fin (n + 2) → K) (G i) = 0 :=
  hG0_of_quadrics n K G hG i

/-! ## Full section-count application (items 1–5 wired into the count) -/

/-- Full section-count application with the geometric witnesses: `H := Hwit n`
(with `hH0`/`hSES` from `hwit_hH0`/`hwit_hSES`), `F := Fsec …` (with `hSEC`
from `fsec_hSEC_closed`), and `hfilter` from `cfsec_hfilter`, applied to
`length_section_eq_two_pow`. The residual inputs are exactly the five
geometric gaps: per-degree `DescentData` (`hdesc`), the degree-`0` agreement
(`h0`), the last-stage identification (`hHeq`), piece-disjointness (`hdisj`),
and the Artinian bound (`B`/`hstab`/`hvan`).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.length_section_eq_two_pow`,
  `Appendix_FixedPoint.BezoutChain.Hwit`,
  `Appendix_FixedPoint.BezoutChain.hwit_hH0`, `Appendix_FixedPoint.BezoutChain.hwit_hSES`,
  `Appendix_FixedPoint.BezoutChain.Fsec`,
  `Appendix_FixedPoint.BezoutChain.fsec_hSEC_closed`,
  `Appendix_FixedPoint.BezoutChain.cfsec_hfilter` (this module). -/
theorem fsec_totalDegree_eq_two_pow (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    (hdesc : ∀ d, DescentData n K G ℓ d)
    (h0 : Fsec n K G ℓ 0 = Hgeom n K G 0)
    (hHeq : ∀ d, Hgeom n K G d = Gclosed n (n + 1) d)
    (B : ℕ) [Module.Finite K (sectionQuotient n K G ℓ)]
    (hdisj : ∀ d, d ≤ B → Disjoint (Cfsec n K G ℓ d) (sectionPiece n K G ℓ d))
    (hstab : Cfsec n K G ℓ (B + 1) = ⊤)
    (hvan : ∀ d, B < d → Fsec n K G ℓ d = 0) :
    totalDegree n K G ℓ = 2 ^ (n + 1) := by
  have hfilter := cfsec_hfilter n K G ℓ B hdisj hstab hvan
  exact length_section_eq_two_pow n K G ℓ (Hwit n) (Fsec n K G ℓ)
    (hwit_hH0 n) (fun k hk d => hwit_hSES n k d hk)
    (fsec_hSEC_closed n K G ℓ hreg hdesc h0 hHeq) hfilter

/-- Section count in Statement's own hypotheses (`hG`, `hreg`, `hZd` — no
`IsAlgClosed` needed: no avoidance is used): the nontriviality inputs come
from `hG` via `evalZero_of_homogTwo`, ambient finiteness from `hreg` + `hZd`
via `section_finite_of_artinian`, and the degree-`0` agreement from
`hgeom_sec_zero_eq`. Unfolding `totalDegree`, this is `bezout_quadratic`
(`Statement.lean`) conditional on exactly the residual geometric inputs
`hdesc`/`hHeq`/`hdisj`/`hstab`/`hvan` (plus the bound `B`).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.fsec_totalDegree_eq_two_pow`,
  `Appendix_FixedPoint.BezoutChain.evalZero_of_homogTwo`,
  `Appendix_FixedPoint.BezoutChain.cone_nontrivial_of_evalZero`,
  `Appendix_FixedPoint.BezoutChain.section_nontrivial_of_evalZero`,
  `Appendix_FixedPoint.BezoutChain.section_finite_of_artinian`,
  `Appendix_FixedPoint.BezoutChain.hgeom_sec_zero_eq`
  (this module). -/
theorem bezout_quadratic_of_shapes (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hG : ∀ i, (G i).IsHomogeneous 2)
    (ℓ : Fin (n + 2) → K)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    (hZd : IsZeroDimensional n K G)
    (hdesc : ∀ d, DescentData n K G ℓ d)
    (hHeq : ∀ d, Hgeom n K G d = Gclosed n (n + 1) d)
    (B : ℕ)
    (hdisj : ∀ d, d ≤ B → Disjoint (Cfsec n K G ℓ d) (sectionPiece n K G ℓ d))
    (hstab : Cfsec n K G ℓ (B + 1) = ⊤)
    (hvan : ∀ d, B < d → Fsec n K G ℓ d = 0) :
    totalDegree n K G ℓ = 2 ^ (n + 1) := by
  have hG0 : ∀ i, MvPolynomial.eval (0 : Fin (n + 2) → K) (G i) = 0 :=
    fun i => evalZero_of_homogTwo n K G hG i
  have hNTc : Nontrivial (coneQuotient n K G) :=
    cone_nontrivial_of_evalZero n K G hG0
  have hNTs : Nontrivial (sectionQuotient n K G ℓ) :=
    section_nontrivial_of_evalZero n K G ℓ hG0
  have hfin : Module.Finite K (sectionQuotient n K G ℓ) :=
    section_finite_of_artinian n K G ℓ hreg hZd
  have h0 : Fsec n K G ℓ 0 = Hgeom n K G 0 :=
    @hgeom_sec_zero_eq n K _ G ℓ hNTc hNTs
  exact @fsec_totalDegree_eq_two_pow n K _ G ℓ hreg hdesc h0 hHeq B hfin
    hdisj hstab hvan

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
/-! ## Section stabilization and vanishing (stabilization lane)

This section closes the `Cfsec`-side Artinian residuals consumed by
`Counting.hfilter_of_bridge` and `Elimination.hfilter_of_cfsecSide`:

* `cfsec_exhaust`: every section element lies in some `Cfsec` level
  (homogeneous-component decomposition; unconditional).
* `cfsec_stab_of_finite` / `cfsec_stab_section`: the filtration stabilizes at
  `⊤` — from ambient finiteness (Noetherian stabilization), resp. from
  `hreg` + `hZd` via `section_finite_of_artinian`. Status: unconditional
  (consumes exactly `hreg` + `hZd`, Statement's own hypotheses).
* `fsec_vanishing_of_piece_vanishing`: `hvan` from piece-level vanishing
  (narrowest conceivable shape). Conditional on exactly
  `[∀ d, B < d → sectionPiece … d = ⊥]`.
* `fsec_vanishing_of_stabAbove`: `hvan` at `B` from `hstab` at `B` plus
  disjointness above `B` (same-`B` alignment; no separate vanishing input).
  Conditional on exactly `[hreg, hZd, hdisjAbove]`.
* `CfsecDisjointData` + `cfsec_disjoint_iff_data`: the `hdisj` residual at one
  level, proved equivalent (`↔`) to the disjointness goal, so provably
  narrowest; `hdisj_full_of_dataAbove` assembles full `hdisj` (level `0` is
  free via `cfsec_zero`). Conditional on exactly `[data above 0]`.
* `hS0_of_nontrivial` / `hS0_of_hG`: the `hS0` residual
  (`finrank (sectionPiece 0) = 1`) as a direct `fsec_zero_eq_one` application,
  resp. discharged from Statement's `hG`. Status: unconditional (consumes
  exactly `hG`).
* `stab_align`: chart-side and section-side stabilization bounds align at
  `max D (B + 1)` (pure order theory + the two monos). Status: unconditional.

No new imports (all names resolve through the existing import block) and no
new edges toward `CountingHandoff`/`ProjectiveLocus`.
-/

/-- Every section element lies in some `Cfsec` level (exhaustion): lift `y`
through both quotient layers to a polynomial `p` (`Ideal.Quotient.mk_surjective`
twice), split `p` into homogeneous components (`sum_homogeneousComponent`),
and note each component lies in its `sectionPiece`, hence in
`Cfsec (p.totalDegree + 1)` by `cfsec_succ` + `cfsec_mono`.

## References

* `Mathlib/RingTheory/Ideal/Quotient/Defs.lean`, `Ideal.Quotient.mk_surjective`.
* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.sum_homogeneousComponent`,
  `MvPolynomial.homogeneousComponent_isHomogeneous`.
* `Mathlib/Algebra/Module/Submodule/Basic.lean`, `Submodule.sum_mem`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.cfsec_succ`,
  `Appendix_FixedPoint.BezoutChain.cfsec_mono` (this module). -/
theorem cfsec_exhaust (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (y : sectionQuotient n K G ℓ) :
    ∃ d, y ∈ Cfsec n K G ℓ d := by
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective s
  set D := p.totalDegree
  have hsum : (∑ i ∈ Finset.range (D + 1),
      (MvPolynomial.homogeneousComponent i) p) = p :=
    MvPolynomial.sum_homogeneousComponent p
  have hmem : ∀ e ∈ Finset.range (D + 1),
      Ideal.Quotient.mk (Ideal.span
          ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
            Set (coneQuotient n K G)))
        (Ideal.Quotient.mk (Ideal.span (Set.range G))
          ((MvPolynomial.homogeneousComponent e) p))
        ∈ Cfsec n K G ℓ (D + 1) := by
    intro e he
    have heD : e + 1 ≤ D + 1 := by
      have hlt := Finset.mem_range.mp he
      omega
    have hpiece :
        Ideal.Quotient.mk (Ideal.span
            ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
              Set (coneQuotient n K G)))
          (Ideal.Quotient.mk (Ideal.span (Set.range G))
            ((MvPolynomial.homogeneousComponent e) p))
          ∈ sectionPiece n K G ℓ e :=
      ⟨(MvPolynomial.homogeneousComponent e) p,
        MvPolynomial.homogeneousComponent_isHomogeneous e p, rfl⟩
    have hle1 : sectionPiece n K G ℓ e ≤ Cfsec n K G ℓ (e + 1) := by
      rw [cfsec_succ]
      exact le_sup_right
    exact cfsec_mono n K G ℓ heD (hle1 hpiece)
  refine ⟨D + 1, ?_⟩
  rw [← hsum, map_sum, map_sum]
  exact Submodule.sum_mem (Cfsec n K G ℓ (D + 1)) hmem

/-- The section filtration stabilizes at `⊤` over a finite section: the
monotone chain `Cfsec` stabilizes (`monotone_stabilizes_iff_noetherian`, with
`IsNoetherian` from `IsNoetherianRing K` + `Module.Finite`), and exhaustion
(`cfsec_exhaust`) forces the stable value to `⊤`.

## References

* `Mathlib/RingTheory/Noetherian/Defs.lean`,
  `monotone_stabilizes_iff_noetherian`.
* `Mathlib/RingTheory/Noetherian/Basic.lean`,
  `isNoetherian_of_isNoetherianRing_of_finite` (the `IsNoetherian` instance).
* `Mathlib/Order/BoundedOrder/Basic.lean`, `top_unique`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.cfsec_exhaust`,
  `Appendix_FixedPoint.BezoutChain.cfsec_mono` (this module). -/
theorem cfsec_stab_of_finite (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    [Module.Finite K (sectionQuotient n K G ℓ)] :
    ∃ B, Cfsec n K G ℓ (B + 1) = ⊤ := by
  obtain ⟨N, hN⟩ := monotone_stabilizes_iff_noetherian.mpr
    (inferInstance : IsNoetherian K (sectionQuotient n K G ℓ))
    (⟨Cfsec n K G ℓ, cfsec_mono n K G ℓ⟩ :
      ℕ →o Submodule K (sectionQuotient n K G ℓ))
  refine ⟨N, top_unique ?_⟩
  intro y _
  obtain ⟨d, hd⟩ := cfsec_exhaust n K G ℓ y
  have hNB : N ≤ max d (N + 1) :=
    le_trans (Nat.le_succ N) (le_max_right d (N + 1))
  have hNeq : Cfsec n K G ℓ (N + 1) = Cfsec n K G ℓ (max d (N + 1)) :=
    (hN (N + 1) (Nat.le_succ N)).symm.trans (hN _ hNB)
  rw [hNeq]
  exact cfsec_mono n K G ℓ (le_max_left d (N + 1)) hd

/-- Section-side stabilization from the geometric hypotheses (`hstab-section`):
`cfsec_stab_of_finite` with ambient finiteness discharged by
`section_finite_of_artinian` from `hreg` + `hZd` (Statement's own hypotheses).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.cfsec_stab_of_finite`,
  `Appendix_FixedPoint.BezoutChain.section_finite_of_artinian` (this module). -/
theorem cfsec_stab_section (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    (hZd : IsZeroDimensional n K G) :
    ∃ B, Cfsec n K G ℓ (B + 1) = ⊤ :=
  @cfsec_stab_of_finite n K _ G ℓ
    (section_finite_of_artinian n K G ℓ hreg hZd)

/-- `hvan` from piece-level vanishing (narrowest conceivable shape): if every
`sectionPiece` above `B` is `⊥`, its finrank (`Fsec`) is `0` there.
Conditional on exactly `[∀ d, B < d → sectionPiece … d = ⊥]`.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.Fsec` (this module).
* `Mathlib/LinearAlgebra/Dimension/Finite.lean`, `finrank_bot`. -/
theorem fsec_vanishing_of_piece_vanishing (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (B : ℕ)
    (hpiece : ∀ d, B < d → sectionPiece n K G ℓ d = ⊥) :
    ∀ d, B < d → Fsec n K G ℓ d = 0 := by
  intro d hd
  change Module.finrank K ↥(sectionPiece n K G ℓ d) = 0
  rw [hpiece d hd, finrank_bot]

/-- `hvan` at `B` from `hstab` at `B` plus disjointness above `B` (same-`B`
alignment): for `d > B` both `Cfsec d` and `Cfsec (d + 1)` are `⊤` by
monotonicity, so the disjointness step equation reads
`finrank ⊤ = finrank ⊤ + Fsec d`, forcing `Fsec d = 0`. No separate vanishing
input is needed. Conditional on exactly `[hreg, hZd, hdisjAbove]` (ambient
finiteness via `section_finite_of_artinian`).

## References

* `Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean`,
  `Submodule.finrank_sup_add_finrank_inf_eq`.
* `Mathlib/Order/Disjoint.lean`, `disjoint_iff_inf_le`.
* `Mathlib/Order/BoundedOrder/Basic.lean`, `top_unique`.
* `Mathlib/LinearAlgebra/Dimension/Finite.lean`, `finrank_bot`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.cfsec_succ`,
  `Appendix_FixedPoint.BezoutChain.cfsec_mono`, `Appendix_FixedPoint.BezoutChain.Fsec` (this
  module). -/
theorem fsec_vanishing_of_stabAbove (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (B : ℕ)
    [Module.Finite K (sectionQuotient n K G ℓ)]
    (hstab : Cfsec n K G ℓ (B + 1) = ⊤)
    (hdisjAbove : ∀ d, B < d →
      Disjoint (Cfsec n K G ℓ d) (sectionPiece n K G ℓ d)) :
    ∀ d, B < d → Fsec n K G ℓ d = 0 := by
  intro d hd
  have hd1 : B + 1 ≤ d := by omega
  have hd2 : B + 1 ≤ d + 1 := by omega
  have htop : ∀ m, B + 1 ≤ m → Cfsec n K G ℓ m = ⊤ := by
    intro m hm
    have hle : Cfsec n K G ℓ (B + 1) ≤ Cfsec n K G ℓ m :=
      cfsec_mono n K G ℓ hm
    rw [hstab] at hle
    exact top_unique hle
  have hstep := Submodule.finrank_sup_add_finrank_inf_eq
    (Cfsec n K G ℓ d) (sectionPiece n K G ℓ d)
  have hinf : Cfsec n K G ℓ d ⊓ sectionPiece n K G ℓ d = ⊥ :=
    le_antisymm (disjoint_iff_inf_le.mp (hdisjAbove d hd)) bot_le
  rw [hinf, finrank_bot, add_zero] at hstep
  rw [← cfsec_succ] at hstep
  rw [htop d hd1, htop (d + 1) hd2] at hstep
  change Module.finrank K ↥(sectionPiece n K G ℓ d) = 0
  omega

/-- Narrowest `hdisj` residual at level `d`: a degree-`d` section class lying
in the lower span vanishes. Proved equivalent to the disjointness goal
(`cfsec_disjoint_iff_data`), so this is provably the exact missing input
(the homogeneous-geometry content: relations among homogeneous lifts
descend in degree).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ChartFiltration`,
  `Appendix_FixedPoint.BezoutChain.sectionPiece`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.Cfsec` (this module). -/
def CfsecDisjointData (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (d : ℕ) : Prop :=
  ∀ y : sectionQuotient n K G ℓ,
    y ∈ sectionPiece n K G ℓ d → y ∈ Cfsec n K G ℓ d → y = 0

/-- The disjointness goal is equivalent to `CfsecDisjointData` (both directions
via `a ⊓ b ≤ ⊥` and `x ∈ ⊥ ↔ x = 0`).

## References

* `Mathlib/Order/Disjoint.lean`, `disjoint_iff_inf_le`.
* `Mathlib/Algebra/Module/Submodule/Lattice.lean`, `Submodule.mem_inf`,
  `Submodule.mem_bot`. -/
theorem cfsec_disjoint_iff_data (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (d : ℕ) :
    Disjoint (Cfsec n K G ℓ d) (sectionPiece n K G ℓ d) ↔
      CfsecDisjointData n K G ℓ d := by
  constructor
  · intro h y h1 h2
    have hle := disjoint_iff_inf_le.mp h
    have hmem : y ∈ (⊥ : Submodule K (sectionQuotient n K G ℓ)) :=
      hle (Submodule.mem_inf.mpr ⟨h2, h1⟩)
    exact (Submodule.mem_bot K).mp hmem
  · intro h
    rw [disjoint_iff_inf_le]
    intro x hx
    rw [Submodule.mem_inf] at hx
    exact (Submodule.mem_bot K).mpr (h x hx.2 hx.1)

/-- One level of `hdisj` from the narrowest data. -/
theorem cfsec_disjoint_of_data (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (d : ℕ)
    (h : CfsecDisjointData n K G ℓ d) :
    Disjoint (Cfsec n K G ℓ d) (sectionPiece n K G ℓ d) :=
  (cfsec_disjoint_iff_data n K G ℓ d).mpr h

/-- Full `hdisj` from data above `0` (level `0` is free via `cfsec_zero`).
Conditional on exactly `[∀ d, 0 < d → CfsecDisjointData … d]`.

## References

* `Mathlib/Order/Disjoint.lean`, `disjoint_bot_left`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.cfsec_zero`,
  `Appendix_FixedPoint.BezoutChain.cfsec_disjoint_of_data` (this module). -/
theorem hdisj_full_of_dataAbove (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hdata : ∀ d, 0 < d → CfsecDisjointData n K G ℓ d) :
    ∀ d, Disjoint (Cfsec n K G ℓ d) (sectionPiece n K G ℓ d) := by
  intro d
  cases d with
  | zero =>
    rw [cfsec_zero]
    exact disjoint_bot_left
  | succ d =>
    exact cfsec_disjoint_of_data n K G ℓ (d + 1)
      (hdata (d + 1) (Nat.zero_lt_succ d))

/-- The `hS0` residual (`finrank (sectionPiece 0) = 1`) as a direct
`fsec_zero_eq_one` application over a nontrivial section.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.fsec_zero_eq_one`
  (this module). -/
theorem hS0_of_nontrivial (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) [Nontrivial (sectionQuotient n K G ℓ)] :
    Module.finrank K ↥(sectionPiece n K G ℓ 0) = 1 :=
  fsec_zero_eq_one n K G ℓ

/-- The `hS0` residual discharged from Statement's `hG` (quadrics vanish at
`0`, so the section is nontrivial). Status: unconditional (consumes exactly
`hG`).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.section_nontrivial_of_evalZero`,
  `Appendix_FixedPoint.BezoutChain.evalZero_of_homogTwo`,
  `Appendix_FixedPoint.BezoutChain.fsec_zero_eq_one` (this module). -/
theorem hS0_of_hG (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hG : ∀ i, (G i).IsHomogeneous 2) :
    Module.finrank K ↥(sectionPiece n K G ℓ 0) = 1 := by
  have hNT : Nontrivial (sectionQuotient n K G ℓ) :=
    section_nontrivial_of_evalZero n K G ℓ
      (fun i => evalZero_of_homogTwo n K G hG i)
  exact @fsec_zero_eq_one n K _ G ℓ hNT

/-- Chart/section stabilization bounds align at `max D (B + 1)` (at-`B`
alignment for `Elimination.chart_bridge_of_final`, whose chart piece and
`Cf` inputs share one bound): both filtrations are monotone, so each
stabilization persists upward. Status: unconditional (pure order theory).

## References

* `Mathlib/Order/BoundedOrder/Basic.lean`, `top_unique`.
* `Mathlib/Order/Monotone/Basic.lean` (`le_max_left`, `le_max_right` are core).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ChartFiltration`,
  `Appendix_FixedPoint.BezoutChain.chartPiece_mono`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.cfsec_mono`
  (this module). -/
theorem stab_align (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (B D : ℕ)
    (hC : Cfsec n K G ℓ (B + 1) = ⊤)
    (hD : chartPiece n K G ℓ D = ⊤) :
    ∃ B', chartPiece n K G ℓ B' = ⊤ ∧ Cfsec n K G ℓ (B' + 1) = ⊤ := by
  refine ⟨max D (B + 1), ?_, ?_⟩
  · have hle : chartPiece n K G ℓ D ≤ chartPiece n K G ℓ (max D (B + 1)) :=
      chartPiece_mono n K G ℓ (le_max_left D (B + 1))
    rw [hD] at hle
    exact top_unique hle
  · have hle : Cfsec n K G ℓ (B + 1) ≤ Cfsec n K G ℓ (max D (B + 1) + 1) :=
      cfsec_mono n K G ℓ ((le_max_right D (B + 1)).trans (Nat.le_succ _))
    rw [hC] at hle
    exact top_unique hle

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
open scoped BigOperators

/-! ## Lattice bridge: `Cfsec` membership as lower sums (lattice-bridge lane)

This section proves the `Cfsec → lower-sum` lattice bridge and closes the
`CfsecDisjointData` residual above `0` (the exact missing input of
`hdisj_full_of_dataAbove`) from the quadrics hypothesis `hG` alone:

* `cfsec_mem_lowerSum`: `y ∈ Cfsec d` unfolds to an explicit lower-sum
  representation `y = ∑ e ∈ range d, [q e]` with each `q e` homogeneous of
  degree `e` (induction on `d`, peeling one `sectionPiece` via
  `Submodule.mem_sup`). The sum shape is verbatim the input shape of
  `Elimination.sectionPiece_disjoint_lowerSum_of_quadrics`, so no further
  geometry is needed.
* `cfsecDisjointData_of_quadrics`: the disjointness data above `0` from `hG`.
* `hdisj_full_of_quadrics`: full piece-disjointness `hdisj` from `hG`
  (level `0` is free via `hdisj_full_of_dataAbove`).

DAG note: `Elimination` imports only `Statement.Definitions` + `ChartFiltration`
(verified at `Elimination.lean` lines 6–7), so the pre-existing
`HilbertFunctionCount → Elimination` edge (this file, line 8) is acyclic and the
Elimination lemma is applied directly — nothing is mirrored.
-/

/-- The `Cfsec → lower-sum` lattice bridge: membership in `Cfsec d` unfolds to
an explicit sum of section classes of homogeneous lifts of degree `< d`.
HilbertFunctionCount on `d`: the `0` case is `⊥`-membership (`cfsec_zero` +
`Submodule.mem_bot`) with the zero lift; the step peels one `sectionPiece`
via `Submodule.mem_sup` and extends the witness by
`fun e => if e = d then p else q e`.

The sum shape is verbatim the `hy2` input shape of
`Elimination.sectionPiece_disjoint_lowerSum_of_quadrics`.

## References

* `Mathlib/LinearAlgebra/Span/Defs.lean`, `Submodule.mem_sup`.
* `Mathlib/Algebra/Module/Submodule/Lattice.lean`, `Submodule.mem_bot`.
* `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`,
  `Finset.sum_range_succ`, `Finset.sum_range_zero` (via `to_additive`),
  `Finset.sum_congr`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.cfsec_zero`,
  `Appendix_FixedPoint.BezoutChain.cfsec_succ` (this module).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.Elimination`,
  `Appendix_FixedPoint.BezoutChain.sectionPiece_disjoint_lowerSum_of_quadrics` (target shape). -/
theorem cfsec_mem_lowerSum (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (d : ℕ) (y : sectionQuotient n K G ℓ)
    (hy : y ∈ Cfsec n K G ℓ d) :
    ∃ q : ℕ → MvPolynomial (Fin (n + 2)) K,
      (∀ e, e < d → (q e).IsHomogeneous e) ∧
      y = ∑ e ∈ Finset.range d, Ideal.Quotient.mk (Ideal.span
          ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
            Set (coneQuotient n K G)))
        (Ideal.Quotient.mk (Ideal.span (Set.range G)) (q e)) := by
  induction d generalizing y with
  | zero =>
    rw [cfsec_zero] at hy
    have hy0 : y = 0 := (Submodule.mem_bot K).mp hy
    refine ⟨fun _ => 0, fun e he => (Nat.not_lt_zero e he).elim, ?_⟩
    rw [Finset.sum_range_zero]
    exact hy0
  | succ d ih =>
    rw [cfsec_succ] at hy
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hy
    obtain ⟨q, hq, hqa⟩ := ih a ha
    obtain ⟨p, hp, hpb⟩ := hb
    refine ⟨fun e => if e = d then p else q e, ?_, ?_⟩
    · intro e he
      by_cases hed : e = d
      · have hqd : (fun e' => if e' = d then p else q e') e = p := by
          rw [hed]
          exact ite_eq_left rfl
        rw [hqd, hed]
        exact hp
      · have hqe : (fun e' => if e' = d then p else q e') e = q e :=
          ite_eq_right hed
        rw [hqe]
        exact hq e (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ he) hed)
    · have hqd : (fun e' => if e' = d then p else q e') d = p :=
        ite_eq_left rfl
      have hqe : ∀ e ∈ Finset.range d,
          (fun e' => if e' = d then p else q e') e = q e := by
        intro e he
        exact ite_eq_right (by have hlt := Finset.mem_range.mp he; omega)
      rw [Finset.sum_range_succ]
      have hpt : (∑ e ∈ Finset.range d, Ideal.Quotient.mk (Ideal.span
              ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
                Set (coneQuotient n K G)))
            (Ideal.Quotient.mk (Ideal.span (Set.range G))
              ((fun e' => if e' = d then p else q e') e)))
          = ∑ e ∈ Finset.range d, Ideal.Quotient.mk (Ideal.span
              ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
                Set (coneQuotient n K G)))
            (Ideal.Quotient.mk (Ideal.span (Set.range G)) (q e)) := by
        apply Finset.sum_congr rfl
        intro e he
        rw [hqe e he]
      rw [hpt, hqd, ← hab, hqa, ← hpb]

/-- The `hdisj` residual above `0` from the quadrics hypothesis alone: a
degree-`d` section class lying in the lower span `Cfsec d` vanishes, by the
lattice bridge (`cfsec_mem_lowerSum`) plus the Elimination geometry
(`sectionPiece_disjoint_lowerSum_of_quadrics`). Status: unconditional
(consumes exactly `hG`).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.CfsecDisjointData`,
  `Appendix_FixedPoint.BezoutChain.cfsec_mem_lowerSum` (this module).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.Elimination`,
  `Appendix_FixedPoint.BezoutChain.sectionPiece_disjoint_lowerSum_of_quadrics`. -/
theorem cfsecDisjointData_of_quadrics (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hG : ∀ i, (G i).IsHomogeneous 2)
    (d : ℕ) (hpos : 0 < d) :
    CfsecDisjointData n K G ℓ d := by
  intro y hy1 hy2
  obtain ⟨q, hq, hy2'⟩ := cfsec_mem_lowerSum n K G ℓ d y hy2
  exact sectionPiece_disjoint_lowerSum_of_quadrics n K G ℓ hG d hpos y hy1 q hq
    hy2'

/-- Full piece-disjointness `hdisj` from the quadrics hypothesis alone (level
`0` is free via `hdisj_full_of_dataAbove`). Status: unconditional (consumes
exactly `hG`).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.hdisj_full_of_dataAbove`,
  `Appendix_FixedPoint.BezoutChain.cfsecDisjointData_of_quadrics`
  (this module). -/
theorem hdisj_full_of_quadrics (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hG : ∀ i, (G i).IsHomogeneous 2) :
    ∀ d, Disjoint (Cfsec n K G ℓ d) (sectionPiece n K G ℓ d) :=
  hdisj_full_of_dataAbove n K G ℓ
    (fun d hd => cfsecDisjointData_of_quadrics n K G ℓ hG d hd)

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
