/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Statement.Definitions
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Finset.Image
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Cone over a finite projective locus has dimension one (R-cone lane)

Target residual from `Geometry/ProjectiveLocus.lean` (`## Obstruction (c)`):
`Counting.infinite_locus_of_not_zeroDim`'s `hcontra`
(`(vanishingLocus n K G).Finite → IsZeroDimensional n K G`), i.e. the affine
cone over a finite projective locus has `Ring.KrullDimLE 1`. This file proves
the `hcontra` shape conditionally on exactly one explicit residual
(`FiniteUnionConeDimOne`), with the two provable links proved unconditionally:

* `affineCone_covered_by_lines`: from homogeneity plus locus finiteness, the
  affine cone is covered by finitely many lines through the origin (the
  "cone = union of lines" half; needs homogeneity so that a nonzero common
  zero marks a locus point, via the scale law
  `eval_smul_of_isHomogeneous_cone` below).
* `polynomial_krullDimLE_one` + `krullDimLE_one_of_surjective`: the affine
  line has dimension `≤ 1` (PID instance chain) and dimension `≤ 1` descends
  along surjections — the dimension half the residual's proof consumes.

## Mathlib API survey (v4.34.0, grep-verified in `.lake/packages/mathlib`)

Present and reused: `IsPrincipalIdealRing.krullDimLE_one`
(`RingTheory/KrullDimension/PID.lean`), fed by
`EuclideanDomain.instIsPrincipalIdealRing`
(`RingTheory/PrincipalIdealDomain.lean`) and
`Polynomial.instEuclideanDomain` (`Algebra/Polynomial/FieldDivision.lean`);
`Ring.krullDimLE_iff`, `ringKrullDim_le_of_surjective`
(`RingTheory/KrullDimension/Basic.lean`); `Projectivization.mk_eq_mk_iff'`,
`rep`, `rep_nonzero`, `mk_rep` (`LinearAlgebra/Projectivization/Basic.lean`).

Absent (hence the residual): any dimension-of-union law (no `ringKrullDim` /
`KrullDimLE` lemma for `Prod`, `Pi`, `sup`, `inf`, or `max` anywhere in
Mathlib); any bridge from affine-point finiteness (`MvPolynomial.zeroLocus` /
`vanishingLocus`) to `KrullDimLE` (the `zeroLocus` hits under
`RingTheory/KrullDimension/` are all spectrum-side
`PrimeSpectrum.zeroLocus`); any `ringKrullDim`-invariance under radicals.
So the step "finite union of lines ⟹ cone quotient has `KrullDimLE 1`" is
taken as the explicit hypothesis `FiniteUnionConeDimOne`, whose proof
also needs `[IsAlgClosed K]` / `[Infinite K]` (not assumed here).

## Grade

`hcontra`: conditional on exactly `[FiniteUnionConeDimOne n K G]` modulo the
discharged data `hG` (at `mkSystem` shape, `hG` is `mkSystem_homogeneous`,
cited by name — this file never imports `Statement/Statement`).

## DAG safety

Imports only clean `Statement.Definitions` (for `coneQuotient`, `vanishingLocus`,
`IsZeroDimensional`) plus narrow Mathlib modules. Never imports
`Statement/Statement`, `Geometry/Counting`, `Geometry/ProjectiveLocus`, or any
`Bridge` module; the homogeneous scale law is mirrored as a `private` lemma
(cited by name) per the `AffineFinite` precedent, so no name clashes arise for
consumers importing both files. No other file imports this one.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
/-! ## Homogeneous scale law (private mirror) -/

/-- Homogeneous scaling law (private mirror of
`ProjectiveLocus.eval_smul_of_isHomogeneous`, cited by name and never
imported): evaluating a homogeneous degree-`m` polynomial at a scaled point
pulls out `a ^ m`. Kept `private` so consumers importing both files see no
duplicate name.

## References

* `Geometry.ProjectiveLocus`, `Appendix_FixedPoint.BezoutChain.eval_smul_of_isHomogeneous`
  (mirrored).
* `Mathlib/Algebra/MvPolynomial/Basic.lean`, `MvPolynomial.as_sum`.
* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.eval_monomial`.
* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.IsHomogeneous`.
* `Mathlib/Data/Finsupp/Weight.lean`, `Finsupp.weight_apply`.
* `Mathlib/Data/Finsupp/Defs.lean`, `Finsupp.mem_support_iff`.
* `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`,
  `Finset.prod_pow_eq_pow_sum`, `Finset.prod_mul_distrib`, `Finset.mul_sum`,
  `map_sum`. -/
private theorem eval_smul_of_isHomogeneous_cone {σ : Type*} {K : Type*}
    [CommSemiring K] {φ : MvPolynomial σ K} {m : ℕ}
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

/-- Common zeros of a homogeneous polynomial are scale-closed: from
`eval v φ = 0` the scale law gives `eval (a • v) φ = a ^ m * 0 = 0`.

## References

* This module, `eval_smul_of_isHomogeneous_cone` (mirrored above). -/
theorem cone_zero_scale_closed {σ : Type*} {K : Type*} [CommSemiring K]
    {φ : MvPolynomial σ K} {m : ℕ}
    (hφ : φ.IsHomogeneous m) (a : K) (v : σ → K)
    (h0 : MvPolynomial.eval v φ = 0) :
    MvPolynomial.eval (a • v) φ = 0 := by
  rw [eval_smul_of_isHomogeneous_cone hφ a v, h0, mul_zero]

/-! ## The affine cone as a finite union of lines -/

/-- The affine cone over the system `G`: common zeros of all equations
(including `0`). Covered by finitely many lines through the origin in
`affineCone_covered_by_lines`.

## References

* This module, `Appendix_FixedPoint.BezoutChain.affineCone_covered_by_lines` (proved below). -/
def AffineCone (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K) :
    Set (Fin (n + 2) → K) :=
  {v | ∀ i, MvPolynomial.eval v (G i) = 0}

/-- A finset of vectors covers the affine cone by lines: every common zero is
`0` or a scalar multiple of a listed vector. Supplied by
`affineCone_covered_by_lines`; consumed as the antecedent of
`FiniteUnionConeDimOne`.

## References

* This module, `Appendix_FixedPoint.BezoutChain.affineCone_covered_by_lines`,
  `Appendix_FixedPoint.BezoutChain.FiniteUnionConeDimOne`. -/
def LineCover (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (t : Finset (Fin (n + 2) → K)) : Prop :=
  ∀ v ∈ AffineCone n K G, v = 0 ∨ ∃ w ∈ t, ∃ a : K, a • w = v

/-- The cone over a finite projective locus is a finite union of lines: from
homogeneity plus locus finiteness, the `rep` vectors of the finitely many
locus points are nonzero and cover the affine cone. A nonzero common zero `v`
marks the locus point `mk v` (all its representatives vanish by
scale-closedness), hence is a multiple of that point's `rep`.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Statement.Definitions`,
  `Appendix_FixedPoint.BezoutChain.vanishingLocus`,
  `Appendix_FixedPoint.BezoutChain.AffineCone`, `Appendix_FixedPoint.BezoutChain.LineCover`.
* `Mathlib/Data/Set/Finite/Basic.lean`, `Set.Finite.exists_finset_coe`.
* `Mathlib/Data/Finset/Image.lean`, `Finset.mem_image`.
* `Mathlib/LinearAlgebra/Projectivization/Basic.lean`,
  `Projectivization.mk_eq_mk_iff'`, `Projectivization.rep`,
  `Projectivization.rep_nonzero`, `Projectivization.mk_rep`.
* This module, `Appendix_FixedPoint.BezoutChain.cone_zero_scale_closed` (proved above). -/
theorem affineCone_covered_by_lines (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (d : Fin (n + 1) → ℕ)
    (hG : ∀ i, (G i).IsHomogeneous (d i))
    (hfin : (vanishingLocus n K G).Finite) :
    ∃ t : Finset (Fin (n + 2) → K),
      (∀ w ∈ t, w ≠ 0) ∧ LineCover n K G t := by
  classical
  obtain ⟨S, hS⟩ := hfin.exists_finset_coe
  refine ⟨S.image Projectivization.rep, ?_, ?_⟩
  · intro w hw
    rw [Finset.mem_image] at hw
    obtain ⟨p, _, rfl⟩ := hw
    exact Projectivization.rep_nonzero p
  · intro v hv
    by_cases hv0 : v = 0
    · exact Or.inl hv0
    · right
      have hmem : Projectivization.mk K v hv0 ∈ vanishingLocus n K G := by
        intro w hw hmk i
        obtain ⟨a, ha⟩ :=
          (Projectivization.mk_eq_mk_iff' K w v hw hv0).mp hmk
        have h0 : MvPolynomial.eval v (G i) = 0 := hv i
        have hsc := cone_zero_scale_closed (hG i) a v h0
        rw [← ha]
        exact hsc
      have hpS : Projectivization.mk K v hv0 ∈ S := by
        rw [← Finset.mem_coe, hS]
        exact hmem
      obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' K
        (Projectivization.rep (Projectivization.mk K v hv0)) v
        (Projectivization.rep_nonzero _) hv0).mp
        (by rw [Projectivization.mk_rep])
      have ha0 : a ≠ 0 := by
        rintro rfl
        rw [zero_smul] at ha
        exact Projectivization.rep_nonzero _ ha.symm
      refine ⟨Projectivization.rep (Projectivization.mk K v hv0),
        Finset.mem_image.mpr ⟨_, hpS, rfl⟩, a⁻¹, ?_⟩
      rw [← ha, ← mul_smul, inv_mul_cancel₀ ha0, one_smul]

/-! ## The affine line has dimension one -/

/-- The affine line has Krull dimension `≤ 1`: `Polynomial K` is Euclidean,
hence a PID, hence `KrullDimLE 1`.

## References

* `Mathlib/Algebra/Polynomial/FieldDivision.lean`,
  `Polynomial.instEuclideanDomain`.
* `Mathlib/RingTheory/PrincipalIdealDomain.lean`,
  `EuclideanDomain.instIsPrincipalIdealRing`.
* `Mathlib/RingTheory/KrullDimension/PID.lean`,
  `IsPrincipalIdealRing.krullDimLE_one`. -/
theorem polynomial_krullDimLE_one (K : Type*) [Field K] :
    Ring.KrullDimLE 1 (Polynomial K) :=
  IsPrincipalIdealRing.krullDimLE_one _

/-- Dimension `≤ 1` descends along surjections (quotients in particular):
from `ringKrullDim S ≤ ringKrullDim R ≤ 1`.

## References

* `Mathlib/RingTheory/KrullDimension/Basic.lean`, `Ring.krullDimLE_iff`,
  `ringKrullDim_le_of_surjective`. -/
theorem krullDimLE_one_of_surjective {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (h : Ring.KrullDimLE 1 R) :
    Ring.KrullDimLE 1 S := by
  rw [Ring.krullDimLE_iff] at h ⊢
  exact (ringKrullDim_le_of_surjective f hf).trans h

/-! ## Residual and `hcontra` assembly -/

/-- Explicit residual R-cone (single): a cone covered by finitely many lines
through the origin has `KrullDimLE 1`. This bundles exactly the missing
in-tree API — the finite-union dimension law plus the Nullstellensatz bridge
from point-set covering to prime spectrum — documented in the module
docstring; its proof additionally needs `[IsAlgClosed K]` and
`[Infinite K]`.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Statement.Definitions`,
  `Appendix_FixedPoint.BezoutChain.coneQuotient`.
* `Mathlib/RingTheory/KrullDimension/Basic.lean`, `Ring.KrullDimLE`.
* This module, `Appendix_FixedPoint.BezoutChain.LineCover` (the antecedent, supplied by
  `Appendix_FixedPoint.BezoutChain.affineCone_covered_by_lines` above). -/
def FiniteUnionConeDimOne (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K) : Prop :=
  ∀ t : Finset (Fin (n + 2) → K), (∀ w ∈ t, w ≠ 0) → LineCover n K G t →
    Ring.KrullDimLE 1 (coneQuotient n K G)

/-- `hcontra` (binder shape copied verbatim from
`Counting.infinite_locus_of_not_zeroDim` and consumed by
`CountingHandoff.hZd_of_hcover_and_hcontra` /
`ProjectiveLocus.hZd_of_chartDimZero_and_hcontra`): finiteness of the
projective locus forces `IsZeroDimensional`, modulo the single residual
`FiniteUnionConeDimOne` and the discharged homogeneity data `hG`.

Conditional on exactly `[FiniteUnionConeDimOne n K G]`.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Counting`,
  `Appendix_FixedPoint.BezoutChain.infinite_locus_of_not_zeroDim` (whose `hcontra` slot this
  discharges; cited by name, never imported).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Statement.Definitions`,
  `Appendix_FixedPoint.BezoutChain.IsZeroDimensional`.
* This module, `Appendix_FixedPoint.BezoutChain.affineCone_covered_by_lines`,
  `Appendix_FixedPoint.BezoutChain.FiniteUnionConeDimOne` (proved/defined above). -/
theorem hcontra_of_finiteUnionConeDimOne (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (d : Fin (n + 1) → ℕ)
    (hG : ∀ i, (G i).IsHomogeneous (d i))
    (hres : FiniteUnionConeDimOne n K G) :
    (vanishingLocus n K G).Finite → IsZeroDimensional n K G := by
  intro hfin
  obtain ⟨t, ht0, htcover⟩ := affineCone_covered_by_lines n K G d hG hfin
  exact hres t ht0 htcover

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

/-! ## Residual discharge: `FiniteUnionConeDimOne` from Ass-control rung `n + 1`

The single residual `FiniteUnionConeDimOne` is discharged here from exactly two
explicit hypotheses — the Ass-control rung at `n + 1` (`havoid`) and the ambient
polynomial dimension bound (`hdim`) — by a prime-chain argument in available API:

* `coneComap` / `coneComap_lt` / `coneComap_contains_span`: comap along the cone
  projection as a strictly monotone map of prime spectra landing above `span G`.
* `finiteUnionConeDimOne_of_havoid`: via `Order.krullDim_le_one_iff`, every prime
  of the cone quotient is minimal or maximal — else a length-2 chain lifts to the
  polynomial ring, where `Order.height_add_one_le` twice plus `havoid` on the
  chain bottom exhibits a series of length `n + 3`
  (`Order.exists_series_of_le_height`), contradicting `hdim` through
  `Order.LTSeries.length_le_krullDim`.
* `hcontra_of_havoid`: the `hcontra` consumer shape from the same hypotheses.

On narrowness. `havoid` quantifies over all primes containing
`span (Set.range G)` because chain bottoms are arbitrary primes over the equation
ideal; assuming the bound only on associated primes would need unmixedness
(`Min ⊆ Ass`) to widen to chain bottoms — the CM track, explicitly out of scope
for this lane. Nothing is lost: `AssHeightBound.le_height_of_span_of_successive`
(cited by name, never imported) already proves exactly this all-primes shape at
`k = n + 1` from successive `SMul`-regularity, so `havoid` is discharged by
regularity alone, with no unmixedness/CM input. The line-cover antecedent
`(t, ht0, hcover)` is therefore discharged vacuously: under Ass-control plus
ambient dimension, the point-set covering is not needed. Likewise `hdim` is the
`≤` half of `PolynomialCatenary.mvPolynomial_ringKrullDim` (cited by name), whose proof
needs the `KrullDimension/Polynomial` API this file cannot import.

Status: `FiniteUnionConeDimOne` (hence `hcontra`): conditional on exactly
`[hdim, havoid]` modulo the discharged data `hG`.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
/-- Comap along the cone projection, as a map of prime spectra.

## References

* `Mathlib/RingTheory/Ideal/Quotient/Defs.lean`, `Ideal.Quotient.mk`.
* `Mathlib/RingTheory/Ideal/Maps.lean`, `Ideal.comap`, `Ideal.IsPrime.comap`
  (instance, so `inferInstance` closes the primality side goal). -/
noncomputable def coneComap (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (x : PrimeSpectrum (coneQuotient n K G)) :
    PrimeSpectrum (MvPolynomial (Fin (n + 2)) K) :=
  ⟨Ideal.comap (Ideal.Quotient.mk (Ideal.span (Set.range G))) x.asIdeal,
    inferInstance⟩

/-- Comap along the cone projection preserves strict inclusion of primes:
monotonicity is `Ideal.comap_mono`; strictness is by `map_comap` (surjective
`mk`) transport of the inequality back down to the quotient spectrum.

## References

* `Mathlib/RingTheory/Spectrum/Prime/Defs.lean`,
  `PrimeSpectrum.asIdeal_lt_asIdeal`, `PrimeSpectrum.ext`.
* `Mathlib/RingTheory/Ideal/Maps.lean`, `Ideal.comap_mono`,
  `Ideal.map_comap_of_surjective`.
* `Mathlib/RingTheory/Ideal/Quotient/Defs.lean`,
  `Ideal.Quotient.mk_surjective`. -/
theorem coneComap_lt (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (x y : PrimeSpectrum (coneQuotient n K G)) (h : x < y) :
    coneComap n K G x < coneComap n K G y := by
  have hab : x.asIdeal < y.asIdeal := (PrimeSpectrum.asIdeal_lt_asIdeal x y).mpr h
  have hle : Ideal.comap (Ideal.Quotient.mk (Ideal.span (Set.range G))) x.asIdeal ≤
      Ideal.comap (Ideal.Quotient.mk (Ideal.span (Set.range G))) y.asIdeal :=
    Ideal.comap_mono hab.le
  have hsurj := Ideal.Quotient.mk_surjective (I := Ideal.span (Set.range G))
  have hne : Ideal.comap (Ideal.Quotient.mk (Ideal.span (Set.range G))) x.asIdeal ≠
      Ideal.comap (Ideal.Quotient.mk (Ideal.span (Set.range G))) y.asIdeal := by
    intro e
    have e2 := congrArg (Ideal.map (Ideal.Quotient.mk (Ideal.span (Set.range G)))) e
    rw [Ideal.map_comap_of_surjective _ hsurj _,
      Ideal.map_comap_of_surjective _ hsurj _] at e2
    have hxy : x = y := PrimeSpectrum.ext e2
    exact absurd hxy (ne_of_lt h)
  have hlt : Ideal.comap (Ideal.Quotient.mk (Ideal.span (Set.range G))) x.asIdeal <
      Ideal.comap (Ideal.Quotient.mk (Ideal.span (Set.range G))) y.asIdeal :=
    lt_of_le_not_ge hle (fun hge => hne (le_antisymm hle hge))
  exact (PrimeSpectrum.asIdeal_lt_asIdeal _ _).mp hlt

/-- Every comap prime contains the equation ideal (`ker mk = span`, then
`ker_le_comap`).

## References

* `Mathlib/RingTheory/Ideal/Quotient/Operations.lean`, `Ideal.mk_ker`.
* `Mathlib/RingTheory/Ideal/Maps.lean`, `Ideal.ker_le_comap`. -/
theorem coneComap_contains_span (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (x : PrimeSpectrum (coneQuotient n K G)) :
    Ideal.span (Set.range G) ≤ (coneComap n K G x).asIdeal := by
  have hker : RingHom.ker (Ideal.Quotient.mk (Ideal.span (Set.range G))) =
      Ideal.span (Set.range G) := Ideal.mk_ker
  rw [← hker]
  exact Ideal.ker_le_comap _

/-- Residual discharge: `FiniteUnionConeDimOne` from Ass-control rung `n + 1`
(`havoid`: every prime over the equation ideal has `Order.height ≥ n + 1`) plus
the ambient polynomial dimension bound (`hdim`). The line-cover antecedent is
discharged vacuously (see the section docstring for why this is the narrowest
sufficient shape and how each hypothesis is discharged by name).

Conditional on exactly `[hdim, havoid]`.

## References

* `Mathlib/RingTheory/KrullDimension/Basic.lean`, `Ring.krullDimLE_iff`.
* `Mathlib/Order/KrullDimension.lean`, `Order.krullDim_le_one_iff`,
  `Order.height_add_one_le`, `Order.exists_series_of_le_height`,
  `Order.LTSeries.length_le_krullDim`.
* `Mathlib/Order/Max.lean`, `not_isMin_iff`, `not_isMax_iff`.
* This module, `Appendix_FixedPoint.BezoutChain.coneComap_lt`,
  `Appendix_FixedPoint.BezoutChain.coneComap_contains_span`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AssHeightBound`,
  `AssHeightBound.le_height_of_span_of_successive` (discharges `havoid` at
  `k = n + 1` from successive regularity; cited by name, never imported).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Dimension.PolynomialCatenary`,
  `Appendix_FixedPoint.BezoutChain.mvPolynomial_ringKrullDim` (discharges `hdim`; cited by name,
  never
  imported). -/
theorem finiteUnionConeDimOne_of_havoid (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hdim : ringKrullDim (MvPolynomial (Fin (n + 2)) K) ≤ ((n + 2 : ℕ) : WithBot ℕ∞))
    (havoid : ∀ P : Ideal (MvPolynomial (Fin (n + 2)) K), ∀ hP : P.IsPrime,
      Ideal.span (Set.range G) ≤ P →
      ((n + 1 : ℕ) : ℕ∞) ≤ Order.height (⟨P, hP⟩ : PrimeSpectrum _)) :
    FiniteUnionConeDimOne n K G := by
  intro _t _ht0 _hcover
  rw [Ring.krullDimLE_iff, Nat.cast_one]
  change Order.krullDim (PrimeSpectrum (coneQuotient n K G)) ≤ 1
  rw [Order.krullDim_le_one_iff]
  intro x
  by_contra hcon
  have hnmin : ¬ IsMin x := fun h => hcon (Or.inl h)
  have hnmax : ¬ IsMax x := fun h => hcon (Or.inr h)
  obtain ⟨y, hyx⟩ := not_isMin_iff.mp hnmin
  obtain ⟨z, hxz⟩ := not_isMax_iff.mp hnmax
  have hYX : coneComap n K G y < coneComap n K G x :=
    coneComap_lt n K G y x hyx
  have hXZ : coneComap n K G x < coneComap n K G z :=
    coneComap_lt n K G x z hxz
  have h1 : Order.height (coneComap n K G y) + 1 ≤ Order.height (coneComap n K G x) :=
    Order.height_add_one_le hYX
  have h2 : Order.height (coneComap n K G x) + 1 ≤ Order.height (coneComap n K G z) :=
    Order.height_add_one_le hXZ
  have hY : ((n + 1 : ℕ) : ℕ∞) ≤ Order.height (coneComap n K G y) :=
    havoid _ (coneComap n K G y).isPrime (coneComap_contains_span n K G y)
  have h4 : ((n + 3 : ℕ) : ℕ∞) ≤ Order.height (coneComap n K G z) := by
    have h3 : Order.height (coneComap n K G y) + (1 + 1) ≤
        Order.height (coneComap n K G z) :=
      calc Order.height (coneComap n K G y) + (1 + 1)
          = Order.height (coneComap n K G y) + 1 + 1 := by rw [add_assoc]
        _ ≤ Order.height (coneComap n K G x) + 1 := add_le_add_left h1 1
        _ ≤ Order.height (coneComap n K G z) := h2
    have e : ((n + 1 : ℕ) : ℕ∞) + (1 + 1) = ((n + 3 : ℕ) : ℕ∞) := by
      push_cast
      ring
    calc ((n + 3 : ℕ) : ℕ∞) = ((n + 1 : ℕ) : ℕ∞) + (1 + 1) := e.symm
      _ ≤ Order.height (coneComap n K G y) + (1 + 1) := add_le_add_left hY (1 + 1)
      _ ≤ Order.height (coneComap n K G z) := h3
  obtain ⟨p, -, hlen⟩ := Order.exists_series_of_le_height _ h4
  have hlen2 : ((p.length : ℕ) : WithBot ℕ∞) ≤
      ringKrullDim (MvPolynomial (Fin (n + 2)) K) :=
    Order.LTSeries.length_le_krullDim p
  rw [hlen] at hlen2
  have hle : ((n + 3 : ℕ) : WithBot ℕ∞) ≤ ((n + 2 : ℕ) : WithBot ℕ∞) :=
    hlen2.trans hdim
  have hfin : n + 3 ≤ n + 2 := by exact_mod_cast hle
  omega

/-- `hcontra` (binder shape copied verbatim from
`Counting.infinite_locus_of_not_zeroDim`, as in
`hcontra_of_finiteUnionConeDimOne`) from Ass-control rung `n + 1` plus the
ambient dimension bound and the discharged homogeneity data `hG`.

Conditional on exactly `[hdim, havoid]` modulo `hG`.

## References

* This module, `Appendix_FixedPoint.BezoutChain.hcontra_of_finiteUnionConeDimOne`,
  `Appendix_FixedPoint.BezoutChain.finiteUnionConeDimOne_of_havoid` (proved above). -/
theorem hcontra_of_havoid (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (d : Fin (n + 1) → ℕ)
    (hG : ∀ i, (G i).IsHomogeneous (d i))
    (hdim : ringKrullDim (MvPolynomial (Fin (n + 2)) K) ≤ ((n + 2 : ℕ) : WithBot ℕ∞))
    (havoid : ∀ P : Ideal (MvPolynomial (Fin (n + 2)) K), ∀ hP : P.IsPrime,
      Ideal.span (Set.range G) ≤ P →
      ((n + 1 : ℕ) : ℕ∞) ≤ Order.height (⟨P, hP⟩ : PrimeSpectrum _)) :
    (vanishingLocus n K G).Finite → IsZeroDimensional n K G :=
  hcontra_of_finiteUnionConeDimOne n K G d hG
    (finiteUnionConeDimOne_of_havoid n K G hdim havoid)

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
