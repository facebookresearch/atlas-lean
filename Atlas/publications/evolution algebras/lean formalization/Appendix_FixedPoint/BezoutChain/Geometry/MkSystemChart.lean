/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Geometry.ChartFiltration
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Order
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Finiteness.Nakayama
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Distinguished-chart computation for `mkSystem` (single-chart lane)

For `G := mkSystem m K F` at the distinguished chart `ℓ = distEll` (the
`{λ ≠ 0}` chart) and point (`zRep`, i.e. `P∞ = [0:⋯:0:1]`) only — concrete,
no general dehomogenization API (none exists in Mathlib v4.34.0,
grep-verified: zero hits for `dehomogen` in `Mathlib/`):

* §1: distinguished chart data — `distEll`, `mkLin_distEll`
  (`mkLin = X_last`), evaluation corollaries, `eval_mkSystem_eq` (the
  concrete dehomogenization identity
  `eval v Qᵢ = eval_{x-part} Fᵢ − λ·xᵢ`).
* §2: explicit affine model — named generators `chartGen i` (`uᵢ = xᵢ/λ`)
  with maximal-ideal membership at `zRep`, relations `chartPoly i`
  (`qᵢ(u) = Fᵢ(u) − uᵢ`), and the `λ = 1` fibre identification
  `dehomog_fiber_one` (chart identification, both directions).
* §3 (hfin): `BasePointFree` input, `chartNonvanishing_of_bpf` (tex Lemma
  `noinfty`(i): `Z ∩ {λ = 0} = ∅`), the affine chart map `toAffineChart`
  with `toAffineChart_mem` / `toAffineChart_injOn`, and the single-chart
  reduction `locus_finite_of_affine_finite` onto the exact residual
  `(affineZero m K F).Finite`.
* §4 (hequiv): the `m = m² + I` push — eval-level relation shadow,
  maximal-ideal membership of the generators, the exact residual
  `DistMaximalBot` (`maximalIdeal = ⊥`), and the proved chain
  `DistMaximalBot → hequiv`
  (`hequiv_dist_of_residuals : distLocRing m K F hF ≃ₗ[K] K`) plus the
  multiplicity-`1` corollary. The finer `m = m² + I` decomposition
  (`DistMSqAbsorb`, `DistMaximalFG`, `nakayama_chart`) is stated as
  exact sub-residuals and discharged in §5.
* §5 (hequiv discharge): the tex Lemma `mult1` computation
  `uᵢ = fᵢ(u) − qᵢ(u)` with `fᵢ(u) ∈ m²`, `qᵢ = 0`, carried out in
  `chartRing` / `locRingAt` vocabulary — exponent combinatorics
  (§5a), the `fᵢ(u) ∈ m²` content (§5b), same-denominator fraction
  tools (§5c), the `qᵢ = 0` identity (§5d), the point-ideal span
  (§5e), and transfer to `DistMSqAbsorb` + `DistMaximalFG` (§5f–§5g)
  then `DistMaximalBot` via the routed Nakayama composition (§5h).
  Delivers the unconditional `hequiv_dist` and `dist_mult_one`.

## Status

* hfin result (`(vanishingLocus m K (mkSystem m K F)).Finite`):
  conditional on exactly `[hFhom, BasePointFree m K F,
  (affineZero m K F).Finite]`. `hFhom` (quadratic input forms) and
  `BasePointFree` (the tex `(bpf)` hypothesis, a theorem input discharged
  upstream by the T1 construction) are explicit inputs; the genuine
  residual is affine finiteness (the tex Lemma `Zfinite` content via PDT /
  completeness, instantiated at the concrete affine system).
* hequiv result (`distLocRing m K F hF ≃ₗ[K] K`): unconditional
  on `[hFhom]` (`hequiv_dist`, via `distMaximalBot_proof`). The former
  `DistMaximalBot` hypothesis discharges through the finer `m = m² + I`
  pair `[DistMSqAbsorb` (the `uᵢ = fᵢ(u) − qᵢ`, `fᵢ(u) ∈ m²` content
  in Nakayama-ready form, proved by `distMSqAbsorb_proof`),
  `DistMaximalFG` (proved by `distMaximalFG_proof`)] composed by
  `nakayama_chart` in `distMaximalBot_proof`. The composition routes
  around the `Localization` instance diamond via `distMaximalSub`'s
  projection-instance ascription (evidence in `DistMaximalBot`'s
  docstring; `LocalMultiplicity` G3 precedent). The `aeval`-level chart
  identification of `Fᵢ(u)` plus degree-2-monomial analysis (no
  in-tree API) is carried out in-file in §5 — cf.
  `SpuriousMultiplicityOne`'s gap note, which this lane closes at the
  distinguished chart/point: `chartGen`, `chartPoly`,
  `chartGen_mem_pointIdeal`, `dehomog_fiber_one`, `hequiv_dist`,
  `dist_mult_one`.

## DAG safety

Imports only clean `Statement.Definitions` + `Geometry.LocalMultiplicity` (both via
`Geometry.ChartFiltration`) plus narrow Mathlib modules. Never imports
`Statement.Statement`, `Geometry.Counting`, `Geometry.ProjectiveLocus`,
`BridgeToFixedPoint.MkSystemSmoothness`, `BridgeToFixedPoint.SpuriousMultiplicityOne`, or
`BridgeToFixedPoint.FixedPointFromBezout`; the three sibling shapes needed
(homogeneous scaling, `zRep`-membership, local Nakayama) are mirrored
under `_chart` names with by-name citations, per the `LocalMultiplicity`
precedent (`jacShapeAt`). Downstream consumers (importing this file,
never imported by it): `Geometry.ChartCompat`, `Geometry.AffineFinite`,
`BridgeToFixedPoint.SpuriousMultiplicityOne`, `BridgeToFixedPoint.ProjectiveFiniteness`,
`BridgeToFixedPoint.FinalDischargeHub`. No cycle: the import direction
`ChartCompat → MkSystemChart → ChartFiltration → LocalMultiplicity` is acyclic
(cf. the `LocalMultiplicity` `HmultChartCompatIso` docstring).

## References

Mathlib v4.34.0 (exact module paths and declaration names, each
grep-verified in-tree) is cited per declaration below.

## Standing context (routine binders)

Named once here; per-decl docstrings below repeat GRADE verdicts and name only
substantive non-routine premises.

* `hF`/`hFhom : ∀ i, (F i).IsHomogeneous 2` — quadratic input forms.
* `hphom : p.IsHomogeneous d` — generic polynomial homogeneity (exponent
  combinatorics, §5).
* `hc : ChartNonvanishing m K (mkSystem m K F) (distEll m K)` — the
  distinguished-chart nonvanishing.
* `hAff : (affineZero m K F).Finite` — affine finiteness (the genuine
  residual of the hfin result; GRADE stays per-decl).
* Instance: `[Field K]` throughout.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
open scoped BigOperators

/-! ## §1 Distinguished chart data -/

/-- The distinguished chart vector: the `λ`-coordinate functional, i.e. `1`
in the last (`z`) slot and `0` elsewhere. Definitional unfolding of
`Definitions.zRep`, so `zRep`-facts transfer by `rfl`. -/
abbrev distEll (m : ℕ) (K : Type*) [Field K] : Fin (m + 2) → K :=
  zRep m K

/-- The chart linear form at the distinguished chart is the last variable:
`mkLin = X_last` (the sum collapses by `Pi.single`). This pins the chart as
`{λ ≠ 0}` at the polynomial level.

## References

* `Statement.Definitions`, `Appendix_FixedPoint.BezoutChain.mkLin`.
* `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`,
  `Finset.sum_eq_single`, `Finset.mem_univ`.
* `Mathlib/Algebra/MvPolynomial/Basic.lean`, `MvPolynomial.C_0`,
  `MvPolynomial.C_1`.
* Core `Pi.single_eq_same`, `Pi.single_eq_of_ne`. -/
theorem mkLin_distEll (m : ℕ) (K : Type*) [Field K] :
    mkLin m K (distEll m K) = MvPolynomial.X (Fin.last (m + 1)) := by
  unfold mkLin distEll zRep
  rw [Finset.sum_eq_single (Fin.last (m + 1))]
  · rw [Pi.single_eq_same _ _, MvPolynomial.C_1, one_mul]
  · intro j _ hne
    rw [Pi.single_eq_of_ne hne _, MvPolynomial.C_0, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Evaluation of the distinguished chart form reads off the last coordinate.

## References

* This module, `Appendix_FixedPoint.BezoutChain.mkLin_distEll`.
* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.eval_X`. -/
theorem eval_mkLin_distEll (m : ℕ) (K : Type*) [Field K]
    (v : Fin (m + 2) → K) :
    MvPolynomial.eval v (mkLin m K (distEll m K)) = v (Fin.last (m + 1)) := by
  rw [mkLin_distEll, MvPolynomial.eval_X]

/-- The distinguished point lies in the distinguished chart (`λ = 1 ≠ 0`).

## References

* This module, `Appendix_FixedPoint.BezoutChain.eval_mkLin_distEll`.
* Core `Pi.single_eq_same`. -/
theorem hℓdist (m : ℕ) (K : Type*) [Field K] :
    MvPolynomial.eval (zRep m K) (mkLin m K (distEll m K)) ≠ 0 := by
  rw [eval_mkLin_distEll]
  have h1 : zRep m K (Fin.last (m + 1)) = 1 := Pi.single_eq_same _ _
  rw [h1]
  exact one_ne_zero

/-- The concrete dehomogenization identity for `mkSystem`: evaluating
`Qᵢ = Fᵢ(x) − z·xᵢ` at `v` splits into the renamed-`Fᵢ` piece (evaluated at
the `x`-part) minus `λ·xᵢ`. Unconditional; the workhorse of §§2–3.

## References

* `Statement.Definitions`, `Appendix_FixedPoint.BezoutChain.mkSystem`.
* `Mathlib/Algebra/MvPolynomial/Rename.lean`, `MvPolynomial.eval_rename`.
* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.eval_X`. -/
theorem eval_mkSystem_eq (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (v : Fin (m + 2) → K) (i : Fin (m + 1)) :
    MvPolynomial.eval v ((mkSystem m K F) i)
      = MvPolynomial.eval (v ∘ Fin.castSucc) (F i)
        - v (Fin.last (m + 1)) * v (Fin.castSucc i) := by
  have hdecomp : ((mkSystem m K F) i)
      = MvPolynomial.rename Fin.castSucc (F i)
        - MvPolynomial.X (Fin.last (m + 1))
          * MvPolynomial.X (Fin.castSucc i) := rfl
  rw [hdecomp, map_sub, MvPolynomial.eval_rename, map_mul,
    MvPolynomial.eval_X, MvPolynomial.eval_X]

/-- Homogeneous scaling of evaluation (local mirror of
`ProjectiveLocus.eval_smul_of_isHomogeneous`, cited by name, never
imported): `eval (a • v) φ = a ^ d * eval v φ`.

## References

* `Geometry.ProjectiveLocus`, `Appendix_FixedPoint.BezoutChain.eval_smul_of_isHomogeneous`
  (mirrored).
* `Mathlib/Algebra/MvPolynomial/Basic.lean`, `MvPolynomial.as_sum`.
* `Mathlib/Data/Finsupp/Weight.lean`, `Finsupp.weight_apply`.
* `Mathlib/Data/Finsupp/Defs.lean`, `Finsupp.mem_support_iff`.
* `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`,
  `Finset.prod_pow_eq_pow_sum`, `Finset.prod_mul_distrib`, `Finset.mul_sum`,
  `map_sum`. -/
theorem eval_smul_chart {σ : Type*} {K : Type*} [Field K]
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

/-- A positive-degree homogeneous polynomial vanishes at the origin
(scaling with `a = 0`).

## References

* This module, `Appendix_FixedPoint.BezoutChain.eval_smul_chart`.
* `Mathlib/Algebra/GroupWithZero/Units/Basic.lean` (`zero_pow` is core
  simp; `smul_zero`/`zero_smul` are core). -/
theorem eval_zero_of_quadric_chart {σ : Type*} {K : Type*} [Field K]
    {φ : MvPolynomial σ K} (hφ : φ.IsHomogeneous 2) :
    MvPolynomial.eval (0 : σ → K) φ = 0 := by
  have h := eval_smul_chart hφ (0 : K) (0 : σ → K)
  rw [zero_smul] at h
  rw [h]
  simp

/-- The `mkSystem` equations vanish at `zRep` (local mirror of
`MkSystemSmoothness.hmem_eval_mkSystem`, cited by name, never imported): the
renamed-`Fᵢ` piece by homogeneity, the `-z·xᵢ` piece since `x = 0` there.

## References

* `BridgeToFixedPoint.MkSystemSmoothness`, `Appendix_FixedPoint.BezoutChain.hmem_eval_mkSystem`
  (mirrored).
* This module, `Appendix_FixedPoint.BezoutChain.eval_zero_of_quadric_chart`.
* `Mathlib/Algebra/MvPolynomial/Rename.lean`, `MvPolynomial.eval_rename`.
* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.eval_X`.
* `Mathlib/Data/Fin/SuccPred.lean`, `Fin.castSucc_ne_last`. -/
theorem hmem_chart (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2) (i : Fin (m + 1)) :
    MvPolynomial.eval (zRep m K) ((mkSystem m K F) i) = 0 := by
  have hdecomp : ((mkSystem m K F) i)
      = MvPolynomial.rename Fin.castSucc (F i)
        - MvPolynomial.X (Fin.last (m + 1))
          * MvPolynomial.X (Fin.castSucc i) := rfl
  have hcomp : (zRep m K) ∘ Fin.castSucc = (0 : Fin (m + 1) → K) := by
    funext x
    simp only [Function.comp_apply, Pi.zero_apply]
    exact Pi.single_eq_of_ne (Fin.castSucc_ne_last x) _
  have h1 : MvPolynomial.eval (zRep m K)
      (MvPolynomial.rename Fin.castSucc (F i)) = 0 := by
    rw [MvPolynomial.eval_rename, hcomp]
    exact eval_zero_of_quadric_chart (hF i)
  have hz : zRep m K (Fin.castSucc i) = 0 :=
    Pi.single_eq_of_ne (Fin.castSucc_ne_last i) _
  have h2 : MvPolynomial.eval (zRep m K)
      (MvPolynomial.X (Fin.last (m + 1))
        * MvPolynomial.X (Fin.castSucc i)) = 0 := by
    rw [map_mul, MvPolynomial.eval_X, MvPolynomial.eval_X, hz, mul_zero]
  rw [hdecomp, map_sub, h1, h2, sub_zero]

/-- The `mkSystem` equations vanish at `zRep`, as a `∀`-statement (the
`hvG` input for chart evaluation at the distinguished point). -/
theorem hvGdist (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2) :
    ∀ i, MvPolynomial.eval (zRep m K) ((mkSystem m K F) i) = 0 :=
  hmem_chart m K F hF

/-! ## §2 Explicit affine model: generators, relations, chart identification -/

/-- The named chart generators `uᵢ = xᵢ/λ`: the fraction `mk(Xᵢ) / ℓ̄^1`
with the homogeneous degree-`1` lift `Xᵢ` (tex Lemma `mult1` coordinates
`uᵢ := xᵢ/λ`; `P∞` is the origin `u = 0`).

## References

* `Statement.Definitions`, `Appendix_FixedPoint.BezoutChain.chartRing` (carrier matched exactly),
  `Appendix_FixedPoint.BezoutChain.mkLin`.
* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.isHomogeneous_X`.
* `Mathlib/Algebra/Group/Submonoid/Membership.lean`,
  `Submonoid.mem_powers_iff`. -/
noncomputable def chartGen (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (i : Fin (m + 1)) : chartRing m K (mkSystem m K F) (distEll m K) :=
  ⟨Localization.mk (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem m K F)))
      (MvPolynomial.X (Fin.castSucc i)))
    ⟨(Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem m K F)))
        (mkLin m K (distEll m K))) ^ 1,
      (Submonoid.mem_powers_iff _ _).mpr ⟨1, rfl⟩⟩,
    1,
    Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem m K F)))
      (MvPolynomial.X (Fin.castSucc i)),
    ⟨MvPolynomial.X (Fin.castSucc i), MvPolynomial.isHomogeneous_X _ _, rfl⟩,
    rfl⟩

/-- The generators vanish at the distinguished point (`P∞` is the origin
in `u`-coordinates): `chartEval` computes on the explicit fraction via
`lift_mk'_spec` to `eval zRep Xᵢ = zRepᵢ = 0`.

## References

* `Statement.Definitions`, `Appendix_FixedPoint.BezoutChain.chartEval`,
  `Appendix_FixedPoint.BezoutChain.chartLocEval`,
  `Appendix_FixedPoint.BezoutChain.coneEval`.
* This module, `Appendix_FixedPoint.BezoutChain.hvGdist`, `Appendix_FixedPoint.BezoutChain.hℓdist`.
* `Mathlib/RingTheory/Localization/Defs.lean`,
  `Localization.mk_eq_mk'_apply`, `IsLocalization.lift_mk'_spec`.
* `Mathlib/Algebra/Ring/Hom/Defs.lean`, `RingHom.comp_apply`.
* `Mathlib/RingTheory/Ideal/Quotient/Defs.lean`, `Ideal.Quotient.lift_mk`
  (an `rfl`-lemma, used via definitional unfolding in `show`).
* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.eval_X`.
* `Mathlib/Data/Fin/SuccPred.lean`, `Fin.castSucc_ne_last`. -/
theorem chartGen_eval_zero (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2) (i : Fin (m + 1)) :
    chartEval m K (mkSystem m K F) (distEll m K) (zRep m K)
      (hvGdist m K F hF) (hℓdist m K) (chartGen m K F i) = 0 := by
  unfold chartEval
  rw [RingHom.comp_apply]
  unfold chartGen
  change chartLocEval m K (mkSystem m K F) (distEll m K) (zRep m K)
      (hvGdist m K F hF) (hℓdist m K)
      (Localization.mk (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem m K F)))
        (MvPolynomial.X (Fin.castSucc i))) _) = 0
  unfold chartLocEval
  rw [Localization.mk_eq_mk'_apply, IsLocalization.lift_mk'_spec, mul_zero]
  change MvPolynomial.eval (zRep m K) (MvPolynomial.X (Fin.castSucc i)) = 0
  rw [MvPolynomial.eval_X]
  exact Pi.single_eq_of_ne (Fin.castSucc_ne_last i) _

/-- The generators lie in the distinguished maximal ideal (chart-level `m`
membership, feeding the `m = m² + I` computation of §4).

## References

* `Statement.Definitions`, `Appendix_FixedPoint.BezoutChain.pointIdeal`.
* This module, `Appendix_FixedPoint.BezoutChain.chartGen_eval_zero`. -/
theorem chartGen_mem_pointIdeal (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2) (i : Fin (m + 1)) :
    chartGen m K F i ∈ pointIdeal m K (mkSystem m K F) (distEll m K)
      (zRep m K) (hvGdist m K F hF) (hℓdist m K) :=
  RingHom.mem_ker.mpr (chartGen_eval_zero m K F hF i)

/-- The dehomogenized relations `qᵢ(u) = Fᵢ(u) − uᵢ` (tex Lemma `mult1`:
`Qᵢ/λ² = fᵢ(u) − uᵢ`), as affine polynomials in the `m + 1` variables `u`. -/
noncomputable def chartPoly (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (i : Fin (m + 1)) : MvPolynomial (Fin (m + 1)) K :=
  F i - MvPolynomial.X i

/-- Eval-level shadow of the tex relation `uᵢ = fᵢ(u) − qᵢ(u)`: evaluating
`qᵢ` splits into `Fᵢ` minus the coordinate. The `m = m² + I` computation
of §4 is the lift of this identity to `chartRing` / `locRingAt`.

## References

* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.eval_X`. -/
theorem eval_chartPoly_relation (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (u : Fin (m + 1) → K) (i : Fin (m + 1)) :
    MvPolynomial.eval u (chartPoly m K F i)
      = MvPolynomial.eval u (F i) - u i := by
  unfold chartPoly
  rw [map_sub, MvPolynomial.eval_X]

/-- Chart identification at the `λ = 1` fibre: for `v` with `v_last = 1`,
the cone equations `Qᵢ(v) = 0` hold iff the affine relations
`qᵢ(x-part) = 0` hold (both directions via `eval_mkSystem_eq`). This is
the concrete dehomogenization isomorphism at the distinguished chart,
stated without any general dehomog API.

## References

* This module, `Appendix_FixedPoint.BezoutChain.eval_mkSystem_eq`.
* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.eval_X`. -/
theorem dehomog_fiber_one (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (v : Fin (m + 2) → K) (hv : v (Fin.last (m + 1)) = 1) :
    (∀ i, MvPolynomial.eval v ((mkSystem m K F) i) = 0)
      ↔ (∀ i, MvPolynomial.eval (v ∘ Fin.castSucc)
        (chartPoly m K F i) = 0) := by
  constructor <;> intro h i
  · have e := h i
    rw [eval_mkSystem_eq, hv, one_mul] at e
    unfold chartPoly
    rw [map_sub, MvPolynomial.eval_X]
    change MvPolynomial.eval (v ∘ Fin.castSucc) (F i)
      - (v ∘ Fin.castSucc) i = 0
    rw [show (v ∘ Fin.castSucc) i = v (Fin.castSucc i) from rfl]
    exact e
  · have e := h i
    unfold chartPoly at e
    rw [map_sub, MvPolynomial.eval_X] at e
    rw [show (v ∘ Fin.castSucc) i = v (Fin.castSucc i) from rfl] at e
    rw [eval_mkSystem_eq, hv, one_mul]
    exact e

/-! ## §3 hfin push: single-chart reduction onto affine finiteness -/

/-- The base-point-free hypothesis (tex `(bpf)`): the input forms have no
common nonzero zero. A theorem input (discharged upstream by the T1
construction for evolution algebras), not a residual. -/
def BasePointFree (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K) : Prop :=
  ∀ a : Fin (m + 1) → K, a ≠ 0 →
    ∃ i, MvPolynomial.eval a (F i) ≠ 0

/-- Tex Lemma `noinfty`(i) (`Z ∩ {λ = 0} = ∅`) in `ChartNonvanishing`
shape: under `BasePointFree`, every locus representative has `λ ≠ 0`.
If `λ = 0`, the `x`-part is nonzero (else the representative is `0`,
via `Fin.eq_castSucc_or_eq_last`) and is a common zero of the `Fᵢ` (via
`eval_mkSystem_eq`), contradicting `BasePointFree`. Unconditional in the
geometry; conditional only on the explicit `BasePointFree` input.

## References

* This module, `Appendix_FixedPoint.BezoutChain.eval_mkSystem_eq`,
  `Appendix_FixedPoint.BezoutChain.eval_mkLin_distEll`.
* `Geometry.ChartFiltration`, `Appendix_FixedPoint.BezoutChain.ChartNonvanishing`.
* `Mathlib/Data/Fin/SuccPred.lean`, `Fin.eq_castSucc_or_eq_last`. -/
theorem chartNonvanishing_of_bpf (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (hBPF : BasePointFree m K F) :
    ChartNonvanishing m K (mkSystem m K F) (distEll m K) := by
  intro p hp v hv hmk
  rw [eval_mkLin_distEll]
  intro hlast
  have ha : v ∘ Fin.castSucc ≠ 0 := by
    intro hcomp
    apply hv
    funext j
    rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
    · exact congrFun hcomp i
    · rw [hlast]
      rfl
  obtain ⟨i, hi⟩ := hBPF (v ∘ Fin.castSucc) ha
  have hmem : MvPolynomial.eval v ((mkSystem m K F) i) = 0 :=
    hp v hv hmk i
  rw [eval_mkSystem_eq, hlast, zero_mul, sub_zero] at hmem
  exact hi hmem

/-- The affine zero set `V(q₀, …, qₘ)` in `𝔸^{m+1}`: the concrete affine
system whose finiteness is the exact hfin residual. -/
def affineZero (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K) :
    Set (Fin (m + 1) → K) :=
  {u | ∀ i, MvPolynomial.eval u (chartPoly m K F i) = 0}

/-- The affine chart map: `p ↦ x/λ` at the canonical representative
(`p.rep (castSucc i) / p.rep last`). Well-defined as a function since
`rep` is a fixed choice; `λ ≠ 0` (from `ChartNonvanishing`) is needed
only for the membership and injectivity proofs. -/
noncomputable def toAffineChart (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (_hc : ChartNonvanishing m K (mkSystem m K F) (distEll m K))
    (p : Projectivization K (Fin (m + 2) → K)) : Fin (m + 1) → K :=
  fun i => p.rep (Fin.castSucc i) / p.rep (Fin.last (m + 1))

/-- The chart map lies in the affine zero set: `u = λ⁻¹ • x`, so
`eval_u Fᵢ = λ⁻² eval_x Fᵢ = λ⁻² (λ xᵢ) = uᵢ` by homogeneous scaling
(`eval_smul_chart`) and the locus equations (`eval_mkSystem_eq`).

## References

* This module, `Appendix_FixedPoint.BezoutChain.eval_smul_chart`,
  `Appendix_FixedPoint.BezoutChain.eval_mkSystem_eq`,
  `Appendix_FixedPoint.BezoutChain.eval_chartPoly_relation`.
* `Geometry.ChartFiltration`, `Appendix_FixedPoint.BezoutChain.chartNonvanishing_at`.
* `Mathlib/Algebra/Group/Action/Defs.lean`, `smul_eq_mul`. -/
theorem toAffineChart_mem (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2)
    (hc : ChartNonvanishing m K (mkSystem m K F) (distEll m K))
    (p : Projectivization K (Fin (m + 2) → K))
    (hp : p ∈ vanishingLocus m K (mkSystem m K F)) :
    toAffineChart m K F hc p ∈ affineZero m K F := by
  have hlam : p.rep (Fin.last (m + 1)) ≠ 0 := by
    have h := chartNonvanishing_at m K (mkSystem m K F) (distEll m K) hc p hp
    rwa [eval_mkLin_distEll] at h
  intro i
  have hmem : MvPolynomial.eval p.rep ((mkSystem m K F) i) = 0 :=
    hp p.rep p.rep_nonzero (Projectivization.mk_rep p) i
  rw [eval_mkSystem_eq] at hmem
  have heval : MvPolynomial.eval (p.rep ∘ Fin.castSucc) (F i)
      = p.rep (Fin.last (m + 1)) * p.rep (Fin.castSucc i) := by
    rw [sub_eq_zero] at hmem
    exact hmem
  have hfun : (p.rep (Fin.last (m + 1)))⁻¹ • (p.rep ∘ Fin.castSucc)
      = toAffineChart m K F hc p := by
    unfold toAffineChart
    funext j
    simp only [Pi.smul_apply, Function.comp_apply]
    rw [smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hscale := eval_smul_chart (hF i) (p.rep (Fin.last (m + 1)))⁻¹
    (p.rep ∘ Fin.castSucc)
  rw [hfun] at hscale
  change MvPolynomial.eval (toAffineChart m K F hc p)
    (chartPoly m K F i) = 0
  rw [eval_chartPoly_relation, hscale, heval]
  unfold toAffineChart
  field_simp
  ring

/-- The chart map is injective on the locus: equal affine coordinates
force the representatives to be scalar multiples (`c = λp/λq`, split by
`Fin.eq_castSucc_or_eq_last` with the `castSucc` case from cross-
multiplication and the `last` case by `div_mul_cancel₀`), hence the
same projective point (via `mk_eq_mk_iff'`).

## References

* This module, `Appendix_FixedPoint.BezoutChain.toAffineChart`.
* `Geometry.ChartFiltration`, `Appendix_FixedPoint.BezoutChain.chartNonvanishing_at`.
* `Mathlib/LinearAlgebra/Projectivization/Basic.lean`,
  `Projectivization.mk_eq_mk_iff'`, `Projectivization.mk_rep`.
* `Mathlib/Data/Fin/SuccPred.lean`, `Fin.eq_castSucc_or_eq_last`.
* `Mathlib/Algebra/Group/Action/Defs.lean`, `smul_eq_mul`.
* `Mathlib/Algebra/GroupWithZero/Units/Basic.lean`,
  `div_mul_cancel₀`. -/
theorem toAffineChart_injOn (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (hc : ChartNonvanishing m K (mkSystem m K F) (distEll m K)) :
    Set.InjOn (toAffineChart m K F hc)
      (vanishingLocus m K (mkSystem m K F)) := by
  intro p hp q hq heq
  have hlamP : p.rep (Fin.last (m + 1)) ≠ 0 := by
    have h := chartNonvanishing_at m K (mkSystem m K F) (distEll m K) hc p hp
    rwa [eval_mkLin_distEll] at h
  have hlamQ : q.rep (Fin.last (m + 1)) ≠ 0 := by
    have h := chartNonvanishing_at m K (mkSystem m K F) (distEll m K) hc q hq
    rwa [eval_mkLin_distEll] at h
  have hsmul : (p.rep (Fin.last (m + 1)) / q.rep (Fin.last (m + 1))) • q.rep
      = p.rep := by
    funext j
    rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
    · have hij : p.rep (Fin.castSucc i) / p.rep (Fin.last (m + 1))
          = q.rep (Fin.castSucc i) / q.rep (Fin.last (m + 1)) := by
        have hcongr := congrFun heq i
        unfold toAffineChart at hcongr
        exact hcongr
      rw [Pi.smul_apply, smul_eq_mul]
      have hcross : p.rep (Fin.castSucc i) * q.rep (Fin.last (m + 1))
          = p.rep (Fin.last (m + 1)) * q.rep (Fin.castSucc i) := by
        have h2 := hij
        field_simp at h2
        exact h2
      field_simp
      linear_combination -hcross
    · rw [Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hlamQ]
  have hmk : Projectivization.mk K p.rep p.rep_nonzero
      = Projectivization.mk K q.rep q.rep_nonzero := by
    rw [Projectivization.mk_eq_mk_iff']
    exact ⟨_, hsmul⟩
  calc p = Projectivization.mk K p.rep p.rep_nonzero :=
        (Projectivization.mk_rep p).symm
    _ = Projectivization.mk K q.rep q.rep_nonzero := hmk
    _ = q := Projectivization.mk_rep q

/-- Single-chart reduction (hfin): the projective locus is finite once
the affine zero set is — the chart image lies in `affineZero`
(`toAffineChart_mem`) and the chart map is injective
(`toAffineChart_injOn`), so finiteness transfers by
`Finite.of_finite_image`. The tex Lemma `Zfinite` content is isolated
exactly in the `(affineZero m K F).Finite` residual.

## References

* This module, `Appendix_FixedPoint.BezoutChain.toAffineChart_mem`,
  `Appendix_FixedPoint.BezoutChain.toAffineChart_injOn`.
* `Mathlib/Data/Set/Finite/Basic.lean`, `Set.Finite.subset`,
  `Set.Finite.of_finite_image`. -/
theorem locus_finite_of_affine_finite (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2)
    (hc : ChartNonvanishing m K (mkSystem m K F) (distEll m K))
    (hAff : (affineZero m K F).Finite) :
    (vanishingLocus m K (mkSystem m K F)).Finite := by
  have hsub : (toAffineChart m K F hc) ''
      (vanishingLocus m K (mkSystem m K F)) ⊆ affineZero m K F := by
    intro u hu
    obtain ⟨p, hp, rfl⟩ := hu
    exact toAffineChart_mem m K F hF hc p hp
  have himg : ((toAffineChart m K F hc) ''
      (vanishingLocus m K (mkSystem m K F))).Finite :=
    hAff.subset hsub
  exact himg.of_finite_image (toAffineChart_injOn m K F hc)

/-- hfin corollary in input shape: locus finiteness from quadratic forms
+ base-point-freeness + affine finiteness.

GRADE (hfin result): conditional on exactly `[hFhom,
BasePointFree m K F, (affineZero m K F).Finite]`. -/
theorem locus_finite_of_bpf_affine (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2)
    (hBPF : BasePointFree m K F)
    (hAff : (affineZero m K F).Finite) :
    (vanishingLocus m K (mkSystem m K F)).Finite :=
  locus_finite_of_affine_finite m K F hF
    (chartNonvanishing_of_bpf m K F hBPF) hAff

/-! ## §4 hequiv push: the `m = m² + I` computation toward `≃ₗ[K] K` -/

/-- The distinguished local ring: `locRingAt` at `zRep` in the
distinguished chart (an `abbrev`, so the `CommRing` / `Algebra K` /
`IsLocalRing` instances flow through). -/
noncomputable abbrev distLocRing (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2) : Type _ :=
  locRingAt m K (mkSystem m K F) (distEll m K) (zRep m K)
    (hvGdist m K F hF) (hℓdist m K)

/-- The distinguished maximal ideal, viewed as a submodule of the local
ring over itself (typed `Submodule`, so the Nakayama application below
sees no `Ideal`/`Submodule` mismatch). The ascription uses `CommRing`-
and `AddCommGroup`-projection instances (rather than TC-direct
`OreLocalization` ones) so the generic Nakayama lemma's instance binders
unify syntactically (the Localization-diamond routing; cf. §5h). -/
noncomputable abbrev distMaximalSub (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2) :
    @Submodule (distLocRing m K F hF) (distLocRing m K F hF)
      (@CommSemiring.toSemiring _ (@CommRing.toCommSemiring _ inferInstance))
      (@AddCommGroup.toAddCommMonoid _ inferInstance)
      inferInstance :=
  IsLocalRing.maximalIdeal (distLocRing m K F hF)

/-- Exact residual R-hequiv-1: the local maximal ideal is absorbed by
itself (`m ≤ m • m`). This is the tex `m = m² + I` content (Lemma
`mult1`, equation `mNak`) after modding out — the chart already quotients
by the `Qᵢ`, so `I = 0` there and the equation reads `m = m²` — stated
in Nakayama-ready submodule form. Its content is the
`uᵢ = fᵢ(u) − qᵢ`, `fᵢ(u) ∈ m²` computation in `chartRing` / `locRingAt`
vocabulary (the `aeval`-level chart identification of `Fᵢ(u)`
plus degree-2-monomial analysis; no in-tree API), carried out in §5
and discharged by `distMSqAbsorb_proof`. -/
def DistMSqAbsorb (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2) : Prop :=
  distMaximalSub m K F hF
    ≤ IsLocalRing.maximalIdeal (distLocRing m K F hF)
      • distMaximalSub m K F hF

/-- Exact residual R-hequiv-2: the local maximal ideal is finitely
generated (as a module over itself). Not automatic: the chart is a
subalgebra of a localization, and Noetherianity does not descend to
subalgebras in-tree. Discharged by `distMaximalFG_proof` (the maximal
ideal is the span of the finite generator-image set, §5g). -/
def DistMaximalFG (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2) : Prop :=
  Submodule.FG (distMaximalSub m K F hF)

/-- Nakayama's lemma in local-ring form (local mirror of
`SpuriousMultiplicityOne.nakayama_maximalIdeal_eq_bot_of_le_smul`, cited by
name, never imported): over a commutative local ring, a finitely
generated submodule absorbed by the maximal ideal is `⊥`. The in-tree
lemma yields `r` with `r - 1 ∈ maximalIdeal` killing `N`; such an `r`
is a unit, hence `N = ⊥`.

## References

* `BridgeToFixedPoint.SpuriousMultiplicityOne`,
  `Appendix_FixedPoint.BezoutChain.nakayama_maximalIdeal_eq_bot_of_le_smul` (mirrored).
* `Mathlib/RingTheory/Finiteness/Nakayama.lean`,
  `Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul`.
* `Mathlib/RingTheory/LocalRing/MaximalIdeal/Basic.lean`,
  `IsLocalRing.notMem_maximalIdeal`. -/
theorem nakayama_chart (R : Type*) [CommRing R] [IsLocalRing R]
    {M : Type*} [AddCommGroup M] [Module R M]
    (N : Submodule R M) (hN : N.FG)
    (hle : N ≤ IsLocalRing.maximalIdeal R • N) : N = ⊥ := by
  obtain ⟨r, hr, hr'⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul
      (IsLocalRing.maximalIdeal R) N hN hle
  have hunit : IsUnit r := by
    by_contra hnu
    have hmem : r ∈ IsLocalRing.maximalIdeal R := by
      by_contra hcon
      exact hnu (IsLocalRing.notMem_maximalIdeal.mp hcon)
    have h1mem : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
      have h := sub_mem hmem hr
      simp at h
    exact (IsLocalRing.notMem_maximalIdeal.mpr isUnit_one) h1mem
  rw [Submodule.eq_bot_iff]
  intro n hn
  have h0 : r • n = 0 := hr' n hn
  obtain ⟨u, hu⟩ := hunit
  have h0' : ((u : Rˣ) : R) • n = 0 := by
    rw [hu]
    exact h0
  have h1 : (((u⁻¹ : Rˣ)) : R) * (((u : Rˣ)) : R) = 1 := u.inv_mul
  calc n = (1 : R) • n := (one_smul _ _).symm
    _ = (((u⁻¹ : Rˣ) : R) * (((u : Rˣ)) : R)) • n := by rw [h1]
    _ = (((u⁻¹ : Rˣ)) : R) • ((((u : Rˣ)) : R) • n) := mul_smul _ _ _
    _ = 0 := by rw [h0', smul_zero]

/-- Exact residual R-hequiv-0 (the hequiv result's hypothesis): the
distinguished local maximal ideal is trivial. This is a proper
mathematical stepping stone (not conclusion-equivalent): the chain to
`hequiv` (`hequiv_dist_of_maximal_bot`, via the proved `LocalMultiplicity`
bundle) and to multiplicity `1` (`dist_mult_one_of_residuals`) is
proved below.

Finer decomposition (discharged in §5h — see below):
`DistMaximalBot` refines to `[DistMSqAbsorb, DistMaximalFG]` via
`nakayama_chart` (proved above). The composition
(`DistMSqAbsorb → DistMaximalFG → DistMaximalBot`) routes around the
`Localization` instance diamond: the `Submodule`-typed `N` elaborates
with `OreLocalization`-path instances (`OreLocalization.instSemiring`,
`OreLocalization.instAddCommMonoidOreLocalization`) while Nakayama's
binders (from `[CommRing R]`) use the `CommRing`-projection path
(`CommRing.toCommSemiring.toSemiring`, `AddCommGroup.toAddCommMonoid`);
the elaborator cannot unify them (mismatch + `whnf` timeout at
200k heartbeats), although they are kernel-defeq (`rfl`) — the exact
diamond `LocalMultiplicity`'s gap G3 documents for quotients of
localizations (`Ring.toSemiring` vs `OreLocalization.instSemiring`:
"defeq, verified by `rfl`, yet unifying them burns all heartbeats").
`distMaximalSub`'s projection-instance ascription makes the two paths
agree syntactically, so `distMaximalBot_proof` (§5h) applies
`nakayama_chart` directly. The mathematical content of
`DistMSqAbsorb` is the `uᵢ = fᵢ(u) − qᵢ`, `fᵢ(u) ∈ m²` computation in
`chartRing` / `locRingAt` vocabulary (the `aeval`-level chart
identification of `Fᵢ(u)` plus degree-2-monomial analysis; no in-tree
API), carried out in §5a–§5g. -/
def DistMaximalBot (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2) : Prop :=
  IsLocalRing.maximalIdeal (distLocRing m K F hF) = ⊥

/-- From a trivial local maximal ideal, the distinguished local ring is
`K` (the exact `hequiv` shape at the distinguished chart/point, via the
`LocalMultiplicity` bundle).

## References

* `Geometry.LocalMultiplicity`, `Appendix_FixedPoint.BezoutChain.hlocEquivOfMaximalBot`. -/
noncomputable def hequiv_dist_of_maximal_bot (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2)
    (hmax : IsLocalRing.maximalIdeal (distLocRing m K F hF) = ⊥) :
    distLocRing m K F hF ≃ₗ[K] K :=
  (hlocEquivOfMaximalBot m K (mkSystem m K F) (distEll m K) (zRep m K)
    (hvGdist m K F hF) (hℓdist m K) hmax).toLinearEquiv

/-- hequiv at the distinguished chart/point from the exact residual
(proved chain: `DistMaximalBot → ≃ₗ[K] K`).

GRADE (hequiv result): conditional on exactly `[hFhom,
DistMaximalBot m K F hF]`. -/
noncomputable def hequiv_dist_of_residuals (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2)
    (hMax : DistMaximalBot m K F hF) :
    distLocRing m K F hF ≃ₗ[K] K :=
  hequiv_dist_of_maximal_bot m K F hF hMax

/-- Tex Lemma `mult1` shape at the distinguished representative: local
multiplicity `1` from the exact residuals (finrank of the `hequiv`
identification).

## References

* This module, `Appendix_FixedPoint.BezoutChain.hequiv_dist_of_residuals`.
* `Mathlib/LinearAlgebra/Dimension/Finrank.lean`,
  `LinearEquiv.finrank_eq`.
* `Mathlib/LinearAlgebra/Dimension/StrongRankCondition.lean`,
  `Module.finrank_self`. -/
theorem dist_mult_one_of_residuals (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2)
    (hMax : DistMaximalBot m K F hF) :
    localMultiplicity m K (mkSystem m K F) (distEll m K) (zRep m K)
      (hvGdist m K F hF) (hℓdist m K) = 1 :=
  (LinearEquiv.finrank_eq
    (hequiv_dist_of_residuals m K F hF hMax)).trans
    (Module.finrank_self K)

/-! ## §5 hequiv discharge: the `m = m²` computation at the distinguished chart

Proves `DistMaximalBot` (hence the unconditional `hequiv`) by the tex Lemma
`mult1` computation `uᵢ = fᵢ(u) − qᵢ(u)` with `fᵢ(u) ∈ m²`, `qᵢ = 0`:

* §5a: exponent combinatorics — splitting degree-`2` (resp. non-pure)
  finsupp exponents into singletons, and monomial consequences
  (`finsupp_split_two`, `monomial_split_two`, `monomial_split_succ`,
  `finsupp_has_castSucc_of_ne_single_last`,
  `finsupp_degree_of_homog_mem`).
* §5b: `aeval chartGen (F i) ∈ P * P` (the `fᵢ(u) ∈ m²` content:
  `aeval_mem_pointIdeal_sq`).
* §5c: same-denominator fraction tools in the chart localization
  (`chartDenomPow`, `chart_mk'_add_same`, `chart_mk'_sum`,
  `chartGen_coe_mk'`, `mk_rename_eq_ell_mul`, `aeval_monomial_coe`,
  `aeval_coe_combined`).
* §5d: `aeval chartGen (F i) = chartGen i` (the `qᵢ = 0` content:
  `aeval_eq_chartGen`).
* §5e: `pointIdeal ≤ span (range chartGen)`
  (`pointIdeal_le_span_chartGen`, via the `chartMonSummand`
  pure/non-pure decomposition and `eval_rep_eq_sum_pure`).
* §5f–§5g: transfer to `DistMSqAbsorb` (`distMSqAbsorb_proof`) +
  `DistMaximalFG` (`distMaximalEqSpan`, `distMaximalFG_proof`).
* §5h: `DistMaximalBot` (`distMaximalBot_proof`) via the routed
  Nakayama composition (`nakayama_chart` on `distMaximalSub`'s
  comm-path ascription), then the unconditional `hequiv_dist`
  and `dist_mult_one`.
-/

/-- An exponent value is bounded by the finsupp degree (`degree = ∑`,
so one term is `≤` the sum).

## References

* `Mathlib/Data/Finsupp/Weight.lean`, `Finsupp.degree_apply`.
* `Mathlib/Algebra/Order/BigOperators/Group/Finset.lean`,
  `Finset.single_le_sum` (via `to_additive`).
* `Mathlib/Data/Finsupp/Defs.lean`, `Finsupp.notMem_support_iff`. -/
theorem finsupp_apply_le_degree {σ : Type*} (e : σ →₀ ℕ) (a : σ) :
    e a ≤ e.degree := by
  rw [Finsupp.degree_apply]
  by_cases ha : a ∈ e.support
  · exact Finset.single_le_sum (fun i _ => Nat.zero_le _) ha
  · rw [Finsupp.notMem_support_iff.mp ha]
    exact Nat.zero_le _

/-- Degree `0` forces the exponent to be `0`.

## References

* This module, `Appendix_FixedPoint.BezoutChain.finsupp_apply_le_degree`. -/
theorem finsupp_eq_zero_of_degree_eq_zero {σ : Type*} (e : σ →₀ ℕ)
    (h : e.degree = 0) : e = 0 := by
  ext x
  simp only [Finsupp.zero_apply]
  have hle := finsupp_apply_le_degree e x
  omega

/-- Positive degree forces nonempty support.

## References

* `Mathlib/Data/Finset/Empty.lean`, `Finset.not_nonempty_iff_eq_empty`.
* `Mathlib/Data/Finsupp/Defs.lean`, `Finsupp.support_eq_empty`. -/
theorem finsupp_support_nonempty_of_degree_pos {σ : Type*} (e : σ →₀ ℕ)
    (h : 0 < e.degree) : e.support.Nonempty := by
  by_contra hcon
  have hcon' : e.support = ∅ := Finset.not_nonempty_iff_eq_empty.mp hcon
  have he : e = 0 := Finsupp.support_eq_empty.mp hcon'
  rw [he, map_zero] at h
  exact absurd h (lt_irrefl 0)

/-- Peeling one singleton off an exponent (`ext` + `omega`, pointwise
`Nat` subtraction).

## References

* `Mathlib/Algebra/Group/Finsupp.lean`, `Finsupp.add_apply`;
  `Mathlib/Data/Finsupp/Single.lean`, `Finsupp.single_eq_same`,
  `Finsupp.single_eq_of_ne`.
* `Mathlib/Data/Finsupp/Order.lean`, `Finsupp.tsub_apply`. -/
theorem finsupp_split_one {σ : Type*} (e : σ →₀ ℕ) (j : σ) (hj : 1 ≤ e j) :
    Finsupp.single j 1 + (e - Finsupp.single j 1) = e := by
  ext x
  rw [Finsupp.add_apply, Finsupp.tsub_apply]
  by_cases hx : x = j
  · subst hx
    rw [Finsupp.single_eq_same]
    omega
  · rw [Finsupp.single_eq_of_ne hx]
    omega

/-- A degree-`1` exponent is a singleton.

## References

* This module, `Appendix_FixedPoint.BezoutChain.finsupp_apply_le_degree`,
  `Appendix_FixedPoint.BezoutChain.finsupp_support_nonempty_of_degree_pos`,
  `Appendix_FixedPoint.BezoutChain.finsupp_split_one`,
  `Appendix_FixedPoint.BezoutChain.finsupp_eq_zero_of_degree_eq_zero`.
* `Mathlib/Data/Finsupp/Weight.lean`, `Finsupp.degree_single`.
* `Mathlib/Data/Finsupp/Defs.lean`, `Finsupp.mem_support_iff`. -/
theorem finsupp_eq_single_of_degree_eq_one {σ : Type*} (e : σ →₀ ℕ)
    (h : e.degree = 1) : ∃ k, e = Finsupp.single k 1 := by
  obtain ⟨k, hk⟩ := finsupp_support_nonempty_of_degree_pos e (by omega)
  have hne : e k ≠ 0 := Finsupp.mem_support_iff.mp hk
  have hk1 : e k = 1 := by
    have hle := finsupp_apply_le_degree e k
    omega
  refine ⟨k, ?_⟩
  have hsplit := finsupp_split_one e k (by omega)
  have hdeg : (e - Finsupp.single k 1).degree = 0 := by
    have hadd : (Finsupp.single k 1 + (e - Finsupp.single k 1)).degree
      = (Finsupp.single k (1 : ℕ)).degree + (e - Finsupp.single k 1).degree :=
      map_add _ _ _
    rw [hsplit, Finsupp.degree_single] at hadd
    omega
  have hzero := finsupp_eq_zero_of_degree_eq_zero _ hdeg
  rw [hzero, add_zero] at hsplit
  exact hsplit.symm

/-- A degree-`2` exponent splits into two singletons (the combinatorial
heart of `fᵢ(u) ∈ m²`: every monomial of the quadratic `Fᵢ` is a product
of two chart generators up to scalar).

## References

* This module, `Appendix_FixedPoint.BezoutChain.finsupp_support_nonempty_of_degree_pos`,
  `Appendix_FixedPoint.BezoutChain.finsupp_split_one`,
  `Appendix_FixedPoint.BezoutChain.finsupp_eq_single_of_degree_eq_one`.
* `Mathlib/Data/Finsupp/Weight.lean`, `Finsupp.degree_single`.
* `Mathlib/Data/Finsupp/Defs.lean`, `Finsupp.mem_support_iff`. -/
theorem finsupp_split_two {σ : Type*} (e : σ →₀ ℕ) (hdeg : e.degree = 2) :
    ∃ j k, e = Finsupp.single j 1 + Finsupp.single k 1 := by
  obtain ⟨j, hj⟩ := finsupp_support_nonempty_of_degree_pos e (by omega)
  have hne : e j ≠ 0 := Finsupp.mem_support_iff.mp hj
  have hj1 : 1 ≤ e j := Nat.one_le_iff_ne_zero.mpr hne
  have hsplit := finsupp_split_one e j hj1
  have hdeg1 : (e - Finsupp.single j 1).degree = 1 := by
    have hadd : (Finsupp.single j 1 + (e - Finsupp.single j 1)).degree
      = (Finsupp.single j (1 : ℕ)).degree + (e - Finsupp.single j 1).degree :=
      map_add _ _ _
    rw [hsplit, Finsupp.degree_single] at hadd
    omega
  obtain ⟨k, hk⟩ := finsupp_eq_single_of_degree_eq_one _ hdeg1
  exact ⟨j, k, by rw [← hsplit, hk]⟩

/-- Monomial consequence of the degree-`2` split: the monomial is
`C c * X j * X k`.

## References

* `Mathlib/Algebra/MvPolynomial/Basic.lean`,
  `MvPolynomial.monomial_single_add`, `MvPolynomial.monomial_zero'`. -/
theorem monomial_split_two {σ : Type*} {R : Type*} [CommSemiring R]
    (e : σ →₀ ℕ) (c : R) (j k : σ)
    (h : e = Finsupp.single j 1 + Finsupp.single k 1) :
    MvPolynomial.monomial e c
      = MvPolynomial.C c * MvPolynomial.X j * MvPolynomial.X k := by
  rw [h, MvPolynomial.monomial_single_add]
  have hk0 : Finsupp.single k (1 : ℕ) = Finsupp.single k 1 + 0 :=
    (add_zero _).symm
  rw [hk0, MvPolynomial.monomial_single_add, MvPolynomial.monomial_zero']
  simp [pow_one]
  ring

/-- Monomial consequence of peeling one singleton: the monomial is
`X i * monomial e' c`.

## References

* `Mathlib/Algebra/MvPolynomial/Basic.lean`,
  `MvPolynomial.monomial_single_add`. -/
theorem monomial_split_succ {σ : Type*} {R : Type*} [CommSemiring R]
    (e : σ →₀ ℕ) (c : R) (i : σ) (e' : σ →₀ ℕ)
    (h : e = Finsupp.single i 1 + e') :
    MvPolynomial.monomial e c
      = MvPolynomial.X i * MvPolynomial.monomial e' c := by
  rw [h, MvPolynomial.monomial_single_add, pow_one]

/-- A non-pure-`z` exponent has `x`-support: if `e ≠ single last d`
then some `castSucc j` has nonzero exponent (via `support ⊆ {last}`
forcing `e = single last d`).

## References

* `Mathlib/Data/Fin/SuccPred.lean`, `Fin.eq_castSucc_or_eq_last`,
  `Fin.castSucc_ne_last`.
* `Mathlib/Data/Finsupp/Defs.lean`, `Finsupp.mem_support_iff`,
  `Finsupp.notMem_support_iff`; `Mathlib/Data/Finsupp/Single.lean`,
  `Finsupp.single_eq_same`, `Finsupp.single_eq_of_ne`.
* `Mathlib/Data/Finsupp/Weight.lean`, `Finsupp.degree_apply`.
* `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`,
  `Finset.sum_subset`, `Finset.sum_singleton`. -/
theorem finsupp_has_castSucc_of_ne_single_last (m : ℕ) (e : Fin (m + 2) →₀ ℕ)
    (d : ℕ) (hdeg : e.degree = d)
    (hne : e ≠ Finsupp.single (Fin.last (m + 1)) d) :
    ∃ j : Fin (m + 1), e (Fin.castSucc j) ≠ 0 := by
  by_contra hcon
  have h0 : ∀ j, e (Fin.castSucc j) = 0 := fun j => by
    by_contra hj
    exact hcon ⟨j, hj⟩
  have hsup : e.support ⊆ {Fin.last (m + 1)} := by
    intro i hi
    simp only [Finset.mem_singleton]
    by_contra hne'
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · exact (Finsupp.mem_support_iff.mp hi) (h0 j)
    · exact hne' rfl
  have hlast : e (Fin.last (m + 1)) = d := by
    have hdeg' : e.degree = e (Fin.last (m + 1)) := by
      rw [Finsupp.degree_apply]
      have hss := Finset.sum_subset hsup
        (fun i _ hi => Finsupp.notMem_support_iff.mp hi)
      rw [hss]
      exact Finset.sum_singleton _ _
    omega
  apply hne
  ext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · rw [h0 j]
    exact (Finsupp.single_eq_of_ne (b := d) (Fin.castSucc_ne_last j)).symm
  · rw [hlast, Finsupp.single_eq_same]

/-- Support exponents of a homogeneous polynomial have the right degree
(`weight 1 = d` unfolds to `degree = d`).

## References

* `Mathlib/RingTheory/MvPolynomial/WeightedHomogeneous.lean`,
  `MvPolynomial.IsWeightedHomogeneous`.
* `Mathlib/Data/Finsupp/Weight.lean`, `Finsupp.weight_apply`,
  `Finsupp.degree_apply`.
* `Mathlib/Data/Finsupp/Defs.lean`, `Finsupp.mem_support_iff`. -/
theorem finsupp_degree_of_homog_mem {σ : Type*} {R : Type*} [CommSemiring R]
    (p : MvPolynomial σ R) {d : ℕ} (h : p.IsHomogeneous d) {e : σ →₀ ℕ}
    (he : e ∈ p.support) : e.degree = d := by
  have hsup : p.coeff e ≠ 0 := Finsupp.mem_support_iff.mp he
  have hwt := h hsup
  rw [Finsupp.weight_apply] at hwt
  simp only [Pi.one_apply, smul_eq_mul, mul_one] at hwt
  rw [Finsupp.degree_apply]
  exact hwt

/-- The `fᵢ(u) ∈ m²` content at chart level: evaluating the quadratic `Fᵢ`
at the chart generators lies in the square of the point ideal. Each
support monomial is `C c * X j * X k` (§5a), hence evaluates to a product
of two point-ideal elements up to a scalar.

## References

* This module, `Appendix_FixedPoint.BezoutChain.finsupp_degree_of_homog_mem`,
  `Appendix_FixedPoint.BezoutChain.finsupp_split_two`,
  `Appendix_FixedPoint.BezoutChain.monomial_split_two`,
  `Appendix_FixedPoint.BezoutChain.chartGen_mem_pointIdeal`.
* `Mathlib/Algebra/MvPolynomial/Basic.lean`, `MvPolynomial.as_sum`.
* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.aeval_X`.
* `Mathlib/Algebra/Module/Submodule/Basic.lean`, `Submodule.sum_mem`.
* `Mathlib/RingTheory/Ideal/Defs.lean`, `Ideal.mul_mem_left`.
* `Mathlib/RingTheory/Ideal/Operations.lean`, `Ideal.mul_mem_mul`. -/
theorem aeval_mem_pointIdeal_sq (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2) (i : Fin (m + 1)) :
    MvPolynomial.aeval (chartGen m K F) (F i) ∈
      pointIdeal m K (mkSystem m K F) (distEll m K) (zRep m K)
        (hvGdist m K F hF) (hℓdist m K) *
      pointIdeal m K (mkSystem m K F) (distEll m K) (zRep m K)
        (hvGdist m K F hF) (hℓdist m K) := by
  rw [(F i).as_sum, map_sum]
  apply Submodule.sum_mem
  intro e he
  have hdeg : e.degree = 2 :=
    finsupp_degree_of_homog_mem (F i) (hF i) he
  obtain ⟨j, k, hsplit⟩ := finsupp_split_two e hdeg
  have hmon := monomial_split_two e ((F i).coeff e) j k hsplit
  have haeval : MvPolynomial.aeval (chartGen m K F)
          (MvPolynomial.monomial e ((F i).coeff e))
        = algebraMap K _ ((F i).coeff e)
          * (chartGen m K F j * chartGen m K F k) := by
    rw [hmon]
    simp [map_mul, MvPolynomial.aeval_X, mul_assoc]
  rw [haeval, ← mul_assoc]
  have hPj := chartGen_mem_pointIdeal m K F hF j
  have hPk := chartGen_mem_pointIdeal m K F hF k
  exact Ideal.mul_mem_mul (Ideal.mul_mem_left _ _ hPj) hPk

/-- Same-denominator addition for `mk'` (both fractions as scalar multiples
of `mk' 1 y`).

## References

* `Mathlib/RingTheory/Localization/Defs.lean`,
  `IsLocalization.mk'_eq_mul_mk'_one`. -/
theorem chart_mk'_add_same {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] {M : Submonoid R} [IsLocalization M S] (a b : R) (y : M) :
    IsLocalization.mk' S a y + IsLocalization.mk' S b y
      = IsLocalization.mk' S (a + b) y := by
  rw [IsLocalization.mk'_eq_mul_mk'_one a y,
    IsLocalization.mk'_eq_mul_mk'_one b y,
    ← add_mul, ← map_add, ← IsLocalization.mk'_eq_mul_mk'_one]

/-- Same-denominator summation for `mk'` (induction via
`chart_mk'_add_same`).

## References

* This module, `Appendix_FixedPoint.BezoutChain.chart_mk'_add_same`.
* `Mathlib/RingTheory/Localization/Defs.lean`,
  `IsLocalization.mk'_zero`.
* `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`,
  `Finset.induction`, `Finset.sum_insert`, `Finset.sum_empty`. -/
theorem chart_mk'_sum {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {M : Submonoid R} [IsLocalization M S] {ι : Type*}
    (s : Finset ι) (f : ι → R) (y : M) :
    ∑ i ∈ s, IsLocalization.mk' S (f i) y
      = IsLocalization.mk' S (∑ i ∈ s, f i) y := by
  classical
  refine Finset.induction ?_ ?_ s
  · simp only [Finset.sum_empty]
    exact (IsLocalization.mk'_zero y).symm
  · intro a s has ih
    rw [Finset.sum_insert has, ih, Finset.sum_insert has, chart_mk'_add_same]

/-- The chart denominator `ℓ̄^d` as an element of the localized submonoid
(proof-irrelevance makes the membership proof interchangeable with the
inline ones in `chartGen`). -/
noncomputable def chartDenomPow (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K) (d : ℕ) :
    Submonoid.powers (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem m K F)))
      (mkLin m K (distEll m K)) : coneQuotient m K (mkSystem m K F)) :=
  ⟨(Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem m K F)))
      (mkLin m K (distEll m K))) ^ d,
    (Submonoid.mem_powers_iff _ _).mpr ⟨d, rfl⟩⟩

/-- The chart generator as an `mk'`-fraction (`rfl`-unfold of `chartGen`
plus `mk_eq_mk'_apply`; the denominator proof is proof-irrelevant).

## References

* This module, `Appendix_FixedPoint.BezoutChain.chartGen`,
  `Appendix_FixedPoint.BezoutChain.chartDenomPow`.
* `Mathlib/RingTheory/Localization/Defs.lean`,
  `Localization.mk_eq_mk'_apply`. -/
theorem chartGen_coe_mk' (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (i : Fin (m + 1)) :
    ((chartGen m K F i : chartRing m K (mkSystem m K F) (distEll m K)) :
      Localization (Submonoid.powers (Ideal.Quotient.mk
        (Ideal.span (Set.range (mkSystem m K F))) (mkLin m K (distEll m K))))) =
    IsLocalization.mk' _
      (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem m K F)))
        (MvPolynomial.X (Fin.castSucc i)))
      (chartDenomPow m K F 1) := by
  change Localization.mk _ _ = _
  rw [Localization.mk_eq_mk'_apply]
  unfold chartDenomPow
  rfl

/-- The renamed equation reads `Fᵢ = ℓ·xᵢ` in the cone quotient
(`mk(Qᵢ) = 0` plus `mkLin distEll = X_last`).

## References

* This module, `Appendix_FixedPoint.BezoutChain.mkLin_distEll`.
* `Statement.Definitions`, `Appendix_FixedPoint.BezoutChain.mkSystem`.
* `Mathlib/RingTheory/Ideal/Quotient/Defs.lean`,
  `Ideal.Quotient.eq_zero_iff_mem`.
* `Mathlib/RingTheory/Ideal/Span.lean`, `Ideal.subset_span`. -/
theorem mk_rename_eq_ell_mul (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (i : Fin (m + 1)) :
    Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem m K F)))
        (MvPolynomial.rename Fin.castSucc (F i))
      = (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem m K F)))
          (mkLin m K (distEll m K))) *
        (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem m K F)))
          (MvPolynomial.X (Fin.castSucc i))) := by
  have hmem : (mkSystem m K F) i ∈ Ideal.span (Set.range (mkSystem m K F)) :=
    Ideal.subset_span ⟨i, rfl⟩
  have hQ0 : Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem m K F)))
        ((mkSystem m K F) i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  have hdecomp : (mkSystem m K F) i
      = MvPolynomial.rename Fin.castSucc (F i)
        - MvPolynomial.X (Fin.last (m + 1))
          * MvPolynomial.X (Fin.castSucc i) := rfl
  rw [hdecomp, map_sub, map_mul] at hQ0
  have hll : Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem m K F)))
          (MvPolynomial.X (Fin.last (m + 1)))
        = Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem m K F)))
          (mkLin m K (distEll m K)) := by
    rw [← mkLin_distEll]
  rw [hll] at hQ0
  exact sub_eq_zero.mp hQ0

/-- Per-monomial ambient identity: `aeval` of a split monomial is the
`mk'`-fraction of the renamed product over `ℓ̄·ℓ̄`.

## References

* This module, `Appendix_FixedPoint.BezoutChain.monomial_split_two`,
  `Appendix_FixedPoint.BezoutChain.chartGen_coe_mk'`.
* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.aeval_X`.
* `Mathlib/Algebra/Algebra/Subalgebra/Basic.lean`,
  `Subalgebra.coe_mul`, `Subalgebra.coe_algebraMap`.
* `Mathlib/Algebra/Algebra/Tower.lean`,
  `IsScalarTower.algebraMap_apply`.
* `Mathlib/RingTheory/Localization/Defs.lean`,
  `IsLocalization.mk'_mul`, `IsLocalization.mul_mk'_eq_mk'_of_mul`. -/
theorem aeval_monomial_coe (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (e : Fin (m + 1) →₀ ℕ) (c : K) (j k : Fin (m + 1))
    (hsplit : e = Finsupp.single j 1 + Finsupp.single k 1) :
    ((MvPolynomial.aeval (chartGen m K F) (MvPolynomial.monomial e c) :
      chartRing m K (mkSystem m K F) (distEll m K)) :
      Localization (Submonoid.powers (Ideal.Quotient.mk
        (Ideal.span (Set.range (mkSystem m K F))) (mkLin m K (distEll m K))))) =
    IsLocalization.mk' _
      ((algebraMap K (coneQuotient m K (mkSystem m K F)) c) *
        ((Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem m K F)))
            (MvPolynomial.X (Fin.castSucc j))) *
          (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem m K F)))
            (MvPolynomial.X (Fin.castSucc k)))))
      ((chartDenomPow m K F 1) * (chartDenomPow m K F 1)) := by
  have hmon := monomial_split_two e c j k hsplit
  have hae : MvPolynomial.aeval (chartGen m K F) (MvPolynomial.monomial e c)
      = algebraMap K _ c * (chartGen m K F j * chartGen m K F k) := by
    rw [hmon]
    simp [map_mul, MvPolynomial.aeval_X, mul_assoc]
  rw [hae]
  simp only [Subalgebra.coe_mul, Subalgebra.coe_algebraMap]
  rw [IsScalarTower.algebraMap_apply K (coneQuotient m K (mkSystem m K F)) _ c]
  rw [chartGen_coe_mk', chartGen_coe_mk']
  rw [← IsLocalization.mk'_mul, IsLocalization.mul_mk'_eq_mk'_of_mul]

/-- Combined ambient identity: `aeval (F i)` is the `mk'`-fraction of the
renamed equation over `ℓ̄·ℓ̄` (per-monomial form summed via
`chart_mk'_sum`, numerators identified with `mk(rename (F i))`).

## References

* This module, `Appendix_FixedPoint.BezoutChain.finsupp_degree_of_homog_mem`,
  `Appendix_FixedPoint.BezoutChain.finsupp_split_two`,
  `Appendix_FixedPoint.BezoutChain.aeval_monomial_coe`,
  `Appendix_FixedPoint.BezoutChain.monomial_split_two`,
  `Appendix_FixedPoint.BezoutChain.chart_mk'_sum`.
* `Mathlib/Algebra/MvPolynomial/Basic.lean`, `MvPolynomial.as_sum`,
  `MvPolynomial.algebraMap_eq`.
* `Mathlib/Algebra/MvPolynomial/Rename.lean`, `MvPolynomial.rename_C`,
  `MvPolynomial.rename_X`.
* `Mathlib/RingTheory/Ideal/Quotient/Operations.lean`,
  `Ideal.Quotient.mk_algebraMap`.
* `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`,
  `Finset.sum_congr`. -/
theorem aeval_coe_combined (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2) (i : Fin (m + 1)) :
    ((MvPolynomial.aeval (chartGen m K F) (F i) :
      chartRing m K (mkSystem m K F) (distEll m K)) :
      Localization (Submonoid.powers (Ideal.Quotient.mk
        (Ideal.span (Set.range (mkSystem m K F))) (mkLin m K (distEll m K))))) =
    IsLocalization.mk' _
      (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem m K F)))
        (MvPolynomial.rename Fin.castSucc (F i)))
      ((chartDenomPow m K F 1) * (chartDenomPow m K F 1)) := by
  have h1 : MvPolynomial.aeval (chartGen m K F) (F i)
      = ∑ e ∈ (F i).support, MvPolynomial.aeval (chartGen m K F)
        (MvPolynomial.monomial e ((F i).coeff e)) := by
    conv_lhs => rw [(F i).as_sum, map_sum]
  have hterm : ∀ e ∈ (F i).support,
      ((MvPolynomial.aeval (chartGen m K F)
          (MvPolynomial.monomial e ((F i).coeff e)) :
        chartRing m K (mkSystem m K F) (distEll m K)) :
        Localization (Submonoid.powers (Ideal.Quotient.mk
          (Ideal.span (Set.range (mkSystem m K F)))
          (mkLin m K (distEll m K)))))
      = IsLocalization.mk' _
        (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem m K F)))
          (MvPolynomial.rename Fin.castSucc
            (MvPolynomial.monomial e ((F i).coeff e))))
        ((chartDenomPow m K F 1) * (chartDenomPow m K F 1)) := by
    intro e he
    have hdeg : e.degree = 2 :=
      finsupp_degree_of_homog_mem (F i) (hF i) he
    obtain ⟨j, k, hsplit⟩ := finsupp_split_two e hdeg
    rw [aeval_monomial_coe m K F e ((F i).coeff e) j k hsplit]
    congr 1
    have hmon := monomial_split_two e ((F i).coeff e) j k hsplit
    have hC : (MvPolynomial.C ((F i).coeff e) :
          MvPolynomial (Fin (m + 2)) K)
          = algebraMap K (MvPolynomial (Fin (m + 2)) K) ((F i).coeff e) := by
      rw [MvPolynomial.algebraMap_eq]
    rw [hmon]
    simp only [map_mul, MvPolynomial.rename_C, MvPolynomial.rename_X, mul_assoc]
    rw [hC, Ideal.Quotient.mk_algebraMap]
  rw [h1]
  have hval : ∀ x : chartRing m K (mkSystem m K F) (distEll m K),
      (x : Localization (Submonoid.powers (Ideal.Quotient.mk
        (Ideal.span (Set.range (mkSystem m K F))) (mkLin m K (distEll m K)))))
        = Subalgebra.val _ x := fun x => rfl
  rw [hval, map_sum]
  simp only [← hval]
  rw [Finset.sum_congr rfl (fun e he => hterm e he), chart_mk'_sum]
  congr 1
  conv_rhs => rw [(F i).as_sum, map_sum, map_sum]

/-- The `qᵢ = 0` chart identity: evaluating `Fᵢ` at the chart generators
recovers the generator (`aeval (F i) = chartGen i`), since both sides are
the fractions `mk(rename Fᵢ)/ℓ̄²` and `mk(xᵢ)/ℓ̄`, equal by
`mk'_eq_iff_eq` via `mk_rename_eq_ell_mul`.

## References

* This module, `Appendix_FixedPoint.BezoutChain.aeval_coe_combined`,
  `Appendix_FixedPoint.BezoutChain.chartGen_coe_mk'`,
  `Appendix_FixedPoint.BezoutChain.mk_rename_eq_ell_mul`.
* `Mathlib/RingTheory/Localization/Defs.lean`,
  `IsLocalization.mk'_eq_iff_eq`.
* `Mathlib/Algebra/Group/Submonoid/Defs.lean`, `Submonoid.coe_mul`. -/
theorem aeval_eq_chartGen (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2) (i : Fin (m + 1)) :
    MvPolynomial.aeval (chartGen m K F) (F i) = chartGen m K F i := by
  apply Subtype.ext
  rw [aeval_coe_combined m K F hF i, chartGen_coe_mk',
    IsLocalization.mk'_eq_iff_eq]
  have hQ := mk_rename_eq_ell_mul m K F i
  have hs1 : ((chartDenomPow m K F 1 :
      Submonoid.powers (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem m K F)))
        (mkLin m K (distEll m K)))) : coneQuotient m K (mkSystem m K F))
      = (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem m K F)))
        (mkLin m K (distEll m K))) ^ 1 := rfl
  rw [Submonoid.coe_mul, hs1, hQ, pow_one]
  congr 1
  ring

/-- The cofactor chart element: the fraction `mk(mon e')/ℓ̄^d'` with its
homogeneous witness. -/
noncomputable def chartCofactor (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (e' : Fin (m + 2) →₀ ℕ) (c : K) (d' : ℕ)
    (hdeg : e'.degree = d') :
    chartRing m K (mkSystem m K F) (distEll m K) :=
  ⟨Localization.mk
      (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem m K F)))
        (MvPolynomial.monomial e' c))
      (chartDenomPow m K F d'),
    d',
    _,
    ⟨MvPolynomial.monomial e' c,
      MvPolynomial.isHomogeneous_monomial c hdeg, rfl⟩,
    rfl⟩

/-- Degree of the cofactor exponent (`d = 1 + deg e'`).

## References

* This module, `Appendix_FixedPoint.BezoutChain.finsupp_degree_of_homog_mem`,
  `Appendix_FixedPoint.BezoutChain.finsupp_split_one`.
* `Mathlib/Data/Finsupp/Weight.lean`, `Finsupp.degree_single`. -/
theorem chartCofactor_deg (m : ℕ) (K : Type*) [Field K]
    (p : MvPolynomial (Fin (m + 2)) K) (d : ℕ)
    (hphom : p.IsHomogeneous d) (e : Fin (m + 2) →₀ ℕ)
    (he : e ∈ p.support) (j : Fin (m + 1))
    (hj : e (Fin.castSucc j) ≠ 0) :
    (e - Finsupp.single (Fin.castSucc j) 1).degree = d - 1 := by
  have hdeg := finsupp_degree_of_homog_mem p hphom he
  have hj1 : 1 ≤ e (Fin.castSucc j) := Nat.one_le_iff_ne_zero.mpr hj
  have hsplit := finsupp_split_one e (Fin.castSucc j) hj1
  have hadd := map_add Finsupp.degree (Finsupp.single (Fin.castSucc j) (1 : ℕ))
    (e - Finsupp.single (Fin.castSucc j) 1)
  rw [hsplit, Finsupp.degree_single] at hadd
  omega

/-- Support exponents off the pure-`z` monomial have `x`-support (bundles
the degree bridge with the §5a dichotomy).

## References

* This module, `Appendix_FixedPoint.BezoutChain.finsupp_degree_of_homog_mem`,
  `Appendix_FixedPoint.BezoutChain.finsupp_has_castSucc_of_ne_single_last`. -/
theorem chartMon_has_castSucc (m : ℕ) (K : Type*) [Field K]
    (p : MvPolynomial (Fin (m + 2)) K) (d : ℕ)
    (hphom : p.IsHomogeneous d) (e : Fin (m + 2) →₀ ℕ)
    (he : e ∈ p.support)
    (hne : e ≠ Finsupp.single (Fin.last (m + 1)) d) :
    ∃ j : Fin (m + 1), e (Fin.castSucc j) ≠ 0 :=
  finsupp_has_castSucc_of_ne_single_last m e d
    (finsupp_degree_of_homog_mem p hphom he) hne

/-- The per-monomial chart summand: pure-`z` monomials contribute the
scalar, non-pure monomials contribute generator-times-cofactor (via a
chosen `x`-index), off-support exponents contribute `0`. -/
noncomputable def chartMonSummand (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (p : MvPolynomial (Fin (m + 2)) K) (d : ℕ)
    (hphom : p.IsHomogeneous d) (e : Fin (m + 2) →₀ ℕ) :
    chartRing m K (mkSystem m K F) (distEll m K) :=
  if he : e ∈ p.support then
    if hne : e = Finsupp.single (Fin.last (m + 1)) d then
      algebraMap K _ (p.coeff e)
    else
      let j : Fin (m + 1) :=
        Classical.choose (chartMon_has_castSucc m K p d hphom e he hne)
      have hj : e (Fin.castSucc j) ≠ 0 :=
        Classical.choose_spec
          (chartMon_has_castSucc m K p d hphom e he hne)
      chartGen m K F j *
        chartCofactor m K F (e - Finsupp.single (Fin.castSucc j) 1)
          (p.coeff e) (d - 1)
          (chartCofactor_deg m K p d hphom e he j hj)
  else 0

/-- Pure-`z` monomial fractions are scalars: `mk(C c · z^d)/ℓ̄^d = c`
(`mk(X_last) = ℓ̄` plus `mk'_eq_iff_eq`).

## References

* This module, `Appendix_FixedPoint.BezoutChain.mkLin_distEll`,
  `Appendix_FixedPoint.BezoutChain.chartDenomPow`.
* `Mathlib/Algebra/MvPolynomial/Basic.lean`,
  `MvPolynomial.monomial_single_add`, `MvPolynomial.monomial_zero'`,
  `MvPolynomial.algebraMap_eq`.
* `Mathlib/RingTheory/Ideal/Quotient/Operations.lean`,
  `Ideal.Quotient.mk_algebraMap`.
* `Mathlib/Algebra/Algebra/Tower.lean`,
  `IsScalarTower.algebraMap_apply`.
* `Mathlib/RingTheory/Localization/Defs.lean`,
  `IsLocalization.mk'_one`, `IsLocalization.mk'_eq_iff_eq`. -/
theorem chartMonPure_coe (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (d : ℕ) (c : K) :
    IsLocalization.mk' (Localization (Submonoid.powers (Ideal.Quotient.mk
        (Ideal.span (Set.range (mkSystem m K F))) (mkLin m K (distEll m K)))))
      (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem m K F)))
        (MvPolynomial.monomial (Finsupp.single (Fin.last (m + 1)) d) c))
      (chartDenomPow m K F d)
    = algebraMap K (Localization (Submonoid.powers (Ideal.Quotient.mk
        (Ideal.span (Set.range (mkSystem m K F)))
        (mkLin m K (distEll m K))))) c := by
  have hmon : MvPolynomial.monomial (Finsupp.single (Fin.last (m + 1)) d) c
      = MvPolynomial.X (Fin.last (m + 1)) ^ d * MvPolynomial.C c := by
    have h0 : Finsupp.single (Fin.last (m + 1)) d
        = Finsupp.single (Fin.last (m + 1)) d + 0 := (add_zero _).symm
    rw [h0, MvPolynomial.monomial_single_add, MvPolynomial.monomial_zero']
  have hll : Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem m K F)))
        (MvPolynomial.X (Fin.last (m + 1)))
      = Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem m K F)))
        (mkLin m K (distEll m K)) := by
    rw [← mkLin_distEll]
  have hC : (MvPolynomial.C c : MvPolynomial (Fin (m + 2)) K)
      = algebraMap K (MvPolynomial (Fin (m + 2)) K) c := by
    rw [MvPolynomial.algebraMap_eq]
  have hmk : Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem m K F)))
        (MvPolynomial.monomial (Finsupp.single (Fin.last (m + 1)) d) c)
      = (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem m K F)))
          (mkLin m K (distEll m K))) ^ d
        * algebraMap K (coneQuotient m K (mkSystem m K F)) c := by
    rw [hmon, map_mul, map_pow, hll, hC, Ideal.Quotient.mk_algebraMap]
  have hsd : ((chartDenomPow m K F d :
      Submonoid.powers (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem m K F)))
        (mkLin m K (distEll m K)))) : coneQuotient m K (mkSystem m K F))
      = (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem m K F)))
        (mkLin m K (distEll m K))) ^ d := rfl
  have h1 : ((1 : Submonoid.powers (Ideal.Quotient.mk
        (Ideal.span (Set.range (mkSystem m K F))) (mkLin m K (distEll m K)))) :
      coneQuotient m K (mkSystem m K F)) = 1 := rfl
  have hR : algebraMap K (Localization (Submonoid.powers (Ideal.Quotient.mk
        (Ideal.span (Set.range (mkSystem m K F))) (mkLin m K (distEll m K))))) c
      = IsLocalization.mk' (Localization (Submonoid.powers (Ideal.Quotient.mk
          (Ideal.span (Set.range (mkSystem m K F))) (mkLin m K (distEll m K)))))
        (algebraMap K (coneQuotient m K (mkSystem m K F)) c)
        (1 : Submonoid.powers (Ideal.Quotient.mk
          (Ideal.span (Set.range (mkSystem m K F))) (mkLin m K (distEll m K)))) := by
    rw [IsScalarTower.algebraMap_apply K (coneQuotient m K (mkSystem m K F))
      (Localization (Submonoid.powers (Ideal.Quotient.mk
        (Ideal.span (Set.range (mkSystem m K F))) (mkLin m K (distEll m K))))) c]
    exact (IsLocalization.mk'_one _ _).symm
  rw [hR, IsLocalization.mk'_eq_iff_eq]
  congr 1
  rw [hmk, hsd, h1, one_mul]

/-- Non-pure monomial fractions factor through a generator:
`mk(mon e)/ℓ̄^d = (mk(Xⱼ)/ℓ̄) · (mk(mon e')/ℓ̄^{d-1})`.

## References

* This module, `Appendix_FixedPoint.BezoutChain.monomial_split_succ`,
  `Appendix_FixedPoint.BezoutChain.chartGen_coe_mk'`,
  `Appendix_FixedPoint.BezoutChain.chartCofactor`, `Appendix_FixedPoint.BezoutChain.chartDenomPow`.
* `Mathlib/RingTheory/Localization/Defs.lean`,
  `Localization.mk_eq_mk'_apply`, `IsLocalization.mk'_mul`,
  `IsLocalization.mk'_eq_iff_eq`.
* `Mathlib/Algebra/Group/Submonoid/Defs.lean`, `Submonoid.coe_mul`. -/
theorem chartMonNonpure_coe (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (e : Fin (m + 2) →₀ ℕ) (c : K) (d : ℕ)
    (j : Fin (m + 1)) (e' : Fin (m + 2) →₀ ℕ)
    (hsplit : e = Finsupp.single (Fin.castSucc j) 1 + e')
    (hdeg' : e'.degree = d - 1) (hd1 : 1 ≤ d) :
    IsLocalization.mk' (Localization (Submonoid.powers (Ideal.Quotient.mk
        (Ideal.span (Set.range (mkSystem m K F))) (mkLin m K (distEll m K)))))
      (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem m K F)))
        (MvPolynomial.monomial e c))
      (chartDenomPow m K F d)
    = ((chartGen m K F j : chartRing m K (mkSystem m K F) (distEll m K)) :
        Localization (Submonoid.powers (Ideal.Quotient.mk
          (Ideal.span (Set.range (mkSystem m K F))) (mkLin m K (distEll m K)))))
      * ((chartCofactor m K F e' c (d - 1) hdeg' :
        chartRing m K (mkSystem m K F) (distEll m K)) :
        Localization (Submonoid.powers (Ideal.Quotient.mk
          (Ideal.span (Set.range (mkSystem m K F))) (mkLin m K (distEll m K))))) := by
  have hmon : MvPolynomial.monomial e c
      = MvPolynomial.X (Fin.castSucc j) * MvPolynomial.monomial e' c :=
    monomial_split_succ e c (Fin.castSucc j) e' hsplit
  have hcofw : ((chartCofactor m K F e' c (d - 1) hdeg' :
      chartRing m K (mkSystem m K F) (distEll m K)) :
      Localization (Submonoid.powers (Ideal.Quotient.mk
        (Ideal.span (Set.range (mkSystem m K F))) (mkLin m K (distEll m K)))))
      = Localization.mk
        (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem m K F)))
          (MvPolynomial.monomial e' c))
        (chartDenomPow m K F (d - 1)) := rfl
  have h1s : ((chartDenomPow m K F 1 :
      Submonoid.powers (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem m K F)))
        (mkLin m K (distEll m K)))) : coneQuotient m K (mkSystem m K F))
      = (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem m K F)))
        (mkLin m K (distEll m K))) ^ 1 := rfl
  have hdm1 : ((chartDenomPow m K F (d - 1) :
      Submonoid.powers (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem m K F)))
        (mkLin m K (distEll m K)))) : coneQuotient m K (mkSystem m K F))
      = (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem m K F)))
        (mkLin m K (distEll m K))) ^ (d - 1) := rfl
  have hsd : ((chartDenomPow m K F d :
      Submonoid.powers (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem m K F)))
        (mkLin m K (distEll m K)))) : coneQuotient m K (mkSystem m K F))
      = (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem m K F)))
        (mkLin m K (distEll m K))) ^ d := rfl
  rw [chartGen_coe_mk', hcofw, Localization.mk_eq_mk'_apply,
    ← IsLocalization.mk'_mul, hmon, map_mul, IsLocalization.mk'_eq_iff_eq]
  rw [Submonoid.coe_mul, h1s, hdm1, hsd]
  congr 1
  rw [pow_one, ← pow_succ', Nat.sub_add_cancel hd1]

/-- The summand at a pure-`z` exponent is the scalar. -/
theorem chartMonSummand_of_pure (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (p : MvPolynomial (Fin (m + 2)) K) (d : ℕ)
    (hphom : p.IsHomogeneous d) (e : Fin (m + 2) →₀ ℕ)
    (he : e ∈ p.support)
    (hpure : e = Finsupp.single (Fin.last (m + 1)) d) :
    chartMonSummand m K F p d hphom e = algebraMap K _ (p.coeff e) := by
  unfold chartMonSummand
  rw [dite_eq_left he, dite_eq_left hpure]

/-- The summand at a non-pure exponent lies in the generator span
(generator-times-cofactor).

## References

* `Mathlib/RingTheory/Ideal/Defs.lean`, `Ideal.mul_mem_right`.
* `Mathlib/RingTheory/Ideal/Span.lean`, `Ideal.subset_span`. -/
theorem chartMonSummand_mem_span (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (p : MvPolynomial (Fin (m + 2)) K) (d : ℕ)
    (hphom : p.IsHomogeneous d) (e : Fin (m + 2) →₀ ℕ)
    (he : e ∈ p.support)
    (hne : e ≠ Finsupp.single (Fin.last (m + 1)) d) :
    chartMonSummand m K F p d hphom e
      ∈ Ideal.span (Set.range (chartGen m K F)) := by
  unfold chartMonSummand
  rw [dite_eq_left he, dite_eq_right hne]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨_, rfl⟩)

/-- Ambient form of the summand at a pure exponent.

## References

* This module, `Appendix_FixedPoint.BezoutChain.chartMonSummand_of_pure`,
  `Appendix_FixedPoint.BezoutChain.chartMonPure_coe`.
* `Mathlib/Algebra/Algebra/Subalgebra/Basic.lean`,
  `Subalgebra.coe_algebraMap`. -/
theorem chartMonSummand_coe_pure (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (p : MvPolynomial (Fin (m + 2)) K) (d : ℕ)
    (hphom : p.IsHomogeneous d) (e : Fin (m + 2) →₀ ℕ)
    (he : e ∈ p.support)
    (hpure : e = Finsupp.single (Fin.last (m + 1)) d) :
    ((chartMonSummand m K F p d hphom e :
      chartRing m K (mkSystem m K F) (distEll m K)) :
      Localization (Submonoid.powers (Ideal.Quotient.mk
        (Ideal.span (Set.range (mkSystem m K F))) (mkLin m K (distEll m K)))))
    = IsLocalization.mk' _
      (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem m K F)))
        (MvPolynomial.monomial e (p.coeff e)))
      (chartDenomPow m K F d) := by
  rw [chartMonSummand_of_pure m K F p d hphom e he hpure,
    Subalgebra.coe_algebraMap]
  have hE2 := chartMonPure_coe m K F d (p.coeff e)
  rw [← hpure] at hE2
  exact hE2.symm

/-- Ambient form of the summand at a non-pure exponent.

## References

* This module, `Appendix_FixedPoint.BezoutChain.finsupp_degree_of_homog_mem`,
  `Appendix_FixedPoint.BezoutChain.finsupp_apply_le_degree`,
  `Appendix_FixedPoint.BezoutChain.finsupp_split_one`,
  `Appendix_FixedPoint.BezoutChain.chartCofactor_deg`,
  `Appendix_FixedPoint.BezoutChain.chartMonNonpure_coe`.
* `Mathlib/Algebra/Algebra/Subalgebra/Basic.lean`,
  `Subalgebra.coe_mul`. -/
theorem chartMonSummand_coe_nonpure (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (p : MvPolynomial (Fin (m + 2)) K) (d : ℕ)
    (hphom : p.IsHomogeneous d) (e : Fin (m + 2) →₀ ℕ)
    (he : e ∈ p.support)
    (hne : e ≠ Finsupp.single (Fin.last (m + 1)) d) :
    ((chartMonSummand m K F p d hphom e :
      chartRing m K (mkSystem m K F) (distEll m K)) :
      Localization (Submonoid.powers (Ideal.Quotient.mk
        (Ideal.span (Set.range (mkSystem m K F))) (mkLin m K (distEll m K)))))
    = IsLocalization.mk' _
      (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem m K F)))
        (MvPolynomial.monomial e (p.coeff e)))
      (chartDenomPow m K F d) := by
  unfold chartMonSummand
  rw [dite_eq_left he, dite_eq_right hne]
  dsimp only
  rw [Subalgebra.coe_mul]
  set j := Classical.choose
    (chartMon_has_castSucc m K p d hphom e he hne)
  have hj : e (Fin.castSucc j) ≠ 0 :=
    Classical.choose_spec
      (chartMon_has_castSucc m K p d hphom e he hne)
  have hj1 : 1 ≤ e (Fin.castSucc j) := Nat.one_le_iff_ne_zero.mpr hj
  have hsplit := finsupp_split_one e (Fin.castSucc j) hj1
  have hdeg := finsupp_degree_of_homog_mem p hphom he
  have hle := finsupp_apply_le_degree e (Fin.castSucc j)
  have hd1 : 1 ≤ d := by omega
  exact (chartMonNonpure_coe m K F e (p.coeff e) d j
    (e - Finsupp.single (Fin.castSucc j) 1) hsplit.symm
    (chartCofactor_deg m K p d hphom e he j hj) hd1).symm

/-- Evaluation of a chart representative vanishes at `zRep` when the chart
element lies in the point ideal (via `lift_mk'_spec` + `lift_mk`).

## References

* `Statement.Definitions`, `Appendix_FixedPoint.BezoutChain.chartEval`,
  `Appendix_FixedPoint.BezoutChain.chartLocEval`,
  `Appendix_FixedPoint.BezoutChain.coneEval`.
* `Mathlib/RingTheory/Localization/Defs.lean`,
  `Localization.mk_eq_mk'_apply`, `IsLocalization.lift_mk'_spec`.
* `Mathlib/Algebra/Ring/Hom/Defs.lean`, `RingHom.comp_apply`. -/
theorem eval_rep_zero_of_mem (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2)
    (x : chartRing m K (mkSystem m K F) (distEll m K))
    (d : ℕ) (s : coneQuotient m K (mkSystem m K F))
    (p : MvPolynomial (Fin (m + 2)) K)
    (hpeq : Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem m K F))) p = s)
    (hval : (x : Localization (Submonoid.powers (Ideal.Quotient.mk
        (Ideal.span (Set.range (mkSystem m K F))) (mkLin m K (distEll m K)))))
      = Localization.mk s
        ⟨(Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem m K F)))
            (mkLin m K (distEll m K))) ^ d,
          (Submonoid.mem_powers_iff _ _).mpr ⟨d, rfl⟩⟩)
    (hx0 : chartEval m K (mkSystem m K F) (distEll m K) (zRep m K)
      (hvGdist m K F hF) (hℓdist m K) x = 0) :
    MvPolynomial.eval (zRep m K) p = 0 := by
  unfold chartEval at hx0
  rw [RingHom.comp_apply] at hx0
  change chartLocEval m K (mkSystem m K F) (distEll m K) (zRep m K)
      (hvGdist m K F hF) (hℓdist m K) (↑x) = 0 at hx0
  unfold chartLocEval at hx0
  rw [hval, Localization.mk_eq_mk'_apply, IsLocalization.lift_mk'_spec,
    mul_zero] at hx0
  rw [← hpeq] at hx0
  change MvPolynomial.eval (zRep m K) p = 0 at hx0
  exact hx0

/-- Evaluation at `zRep` reads off the pure-`z` coefficients: only the
pure monomial survives (every other monomial has a vanishing `x`-factor).

## References

* This module, `Appendix_FixedPoint.BezoutChain.finsupp_degree_of_homog_mem`,
  `Appendix_FixedPoint.BezoutChain.finsupp_has_castSucc_of_ne_single_last`.
* `Mathlib/Algebra/MvPolynomial/Basic.lean`, `MvPolynomial.as_sum`.
* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.eval_monomial`.
* `Mathlib/Algebra/BigOperators/Finsupp/Basic.lean`,
  `Finsupp.prod_single_index`.
* `Mathlib/Algebra/BigOperators/GroupWithZero/Finset.lean`,
  `Finset.prod_eq_zero`.
* `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`,
  `Finset.sum_filter_add_sum_filter_not`, `Finset.sum_congr`,
  `Finset.sum_eq_zero`.
* `Mathlib/Data/Finsupp/Defs.lean`, `Finsupp.mem_support_iff`.
* `Mathlib/Data/Fin/SuccPred.lean`, `Fin.castSucc_ne_last`.
* Core `Pi.single_eq_same`, `Pi.single_eq_of_ne`. -/
theorem eval_rep_eq_sum_pure (m : ℕ) (K : Type*) [Field K]
    (p : MvPolynomial (Fin (m + 2)) K) (d : ℕ)
    (hphom : p.IsHomogeneous d) :
    MvPolynomial.eval (zRep m K) p
      = ∑ e ∈ p.support.filter
          (fun e => e = Finsupp.single (Fin.last (m + 1)) d),
        p.coeff e := by
  have hterm : ∀ e ∈ p.support,
      MvPolynomial.eval (zRep m K) (MvPolynomial.monomial e (p.coeff e))
        = if e = Finsupp.single (Fin.last (m + 1)) d then p.coeff e else 0 := by
    intro e he
    rw [MvPolynomial.eval_monomial]
    by_cases hpure : e = Finsupp.single (Fin.last (m + 1)) d
    · rw [ite_eq_left hpure, hpure]
      have hprod : (Finsupp.single (Fin.last (m + 1)) d).prod
          (fun n en => zRep m K n ^ en) = 1 := by
        have hside : (fun n en => zRep m K n ^ en) (Fin.last (m + 1)) 0 = 1 :=
          pow_zero _
        have hz : zRep m K (Fin.last (m + 1)) = 1 := Pi.single_eq_same _ _
        rw [Finsupp.prod_single_index
          (h := fun n en => zRep m K n ^ en) (a := Fin.last (m + 1)) hside]
        change zRep m K (Fin.last (m + 1)) ^ d = 1
        rw [hz, one_pow]
      rw [hprod, mul_one]
    · rw [ite_eq_right hpure]
      have hdeg := finsupp_degree_of_homog_mem p hphom he
      obtain ⟨j, hj⟩ := finsupp_has_castSucc_of_ne_single_last m e d hdeg hpure
      have hprod0 : e.prod (fun n en => zRep m K n ^ en) = 0 := by
        have hfactor : (fun n en => zRep m K n ^ en) (Fin.castSucc j)
            (e (Fin.castSucc j)) = 0 := by
          have hz0 : zRep m K (Fin.castSucc j) = 0 :=
            Pi.single_eq_of_ne (Fin.castSucc_ne_last j) _
          change zRep m K (Fin.castSucc j) ^ e (Fin.castSucc j) = 0
          rw [hz0]
          exact zero_pow hj
        have hmem : Fin.castSucc j ∈ e.support :=
          Finsupp.mem_support_iff.mpr hj
        unfold Finsupp.prod
        exact Finset.prod_eq_zero hmem hfactor
      rw [hprod0, mul_zero]
  conv_lhs => rw [p.as_sum, map_sum]
  rw [Finset.sum_congr rfl (fun e he => hterm e he)]
  have hsplit := Finset.sum_filter_add_sum_filter_not p.support
    (fun e => e = Finsupp.single (Fin.last (m + 1)) d)
    (fun e => if e = Finsupp.single (Fin.last (m + 1)) d then p.coeff e else 0)
  rw [← hsplit]
  have h0 : ∑ e ∈ p.support.filter
        (fun e => ¬ e = Finsupp.single (Fin.last (m + 1)) d),
      (if e = Finsupp.single (Fin.last (m + 1)) d then p.coeff e else 0)
      = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    rw [Finset.mem_filter] at he
    rw [ite_eq_right he.2]
  rw [h0, add_zero]
  have hfin : ∀ e ∈ p.support.filter
      (fun e => e = Finsupp.single (Fin.last (m + 1)) d),
      (if e = Finsupp.single (Fin.last (m + 1)) d then p.coeff e else 0)
        = p.coeff e := by
    intro e he
    rw [Finset.mem_filter] at he
    rw [ite_eq_left he.2]
  rw [Finset.sum_congr rfl hfin]

/-- The point ideal is spanned by the chart generators: every element
decomposes into summands (`chartMonSummand`), the pure part is
`algebraMap (eval p) = 0`, and the non-pure part lies in the span.

## References

* This module, `Appendix_FixedPoint.BezoutChain.eval_rep_zero_of_mem`,
  `Appendix_FixedPoint.BezoutChain.eval_rep_eq_sum_pure`,
  `Appendix_FixedPoint.BezoutChain.chartMonSummand_of_pure`,
  `Appendix_FixedPoint.BezoutChain.chartMonSummand_mem_span`,
  `Appendix_FixedPoint.BezoutChain.chartMonSummand_coe_pure`,
  `Appendix_FixedPoint.BezoutChain.chartMonSummand_coe_nonpure`,
  `Appendix_FixedPoint.BezoutChain.chart_mk'_sum`.
* `Mathlib/Algebra/MvPolynomial/Basic.lean`, `MvPolynomial.as_sum`.
* `Mathlib/Algebra/Module/Submodule/Basic.lean`, `Submodule.sum_mem`.
* `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`,
  `Finset.sum_filter_add_sum_filter_not`, `Finset.sum_congr`.
* `Mathlib/RingTheory/Localization/Defs.lean`,
  `Localization.mk_eq_mk'_apply`. -/
theorem pointIdeal_le_span_chartGen (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2) :
    pointIdeal m K (mkSystem m K F) (distEll m K) (zRep m K)
        (hvGdist m K F hF) (hℓdist m K)
      ≤ Ideal.span (Set.range (chartGen m K F)) := by
  intro x hx
  obtain ⟨d, s, ⟨p, hphom, hpeq⟩, hval⟩ := x.property
  have heval0 : MvPolynomial.eval (zRep m K) p = 0 :=
    eval_rep_zero_of_mem m K F hF x d s p hpeq hval
      (RingHom.mem_ker.mp hx)
  have hsummand_coe : ∀ e ∈ p.support,
      ((chartMonSummand m K F p d hphom e :
        chartRing m K (mkSystem m K F) (distEll m K)) :
        Localization (Submonoid.powers (Ideal.Quotient.mk
          (Ideal.span (Set.range (mkSystem m K F)))
          (mkLin m K (distEll m K)))))
      = IsLocalization.mk' _
        (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem m K F)))
          (MvPolynomial.monomial e (p.coeff e)))
        (chartDenomPow m K F d) := by
    intro e he
    by_cases hpure : e = Finsupp.single (Fin.last (m + 1)) d
    · exact chartMonSummand_coe_pure m K F p d hphom e he hpure
    · exact chartMonSummand_coe_nonpure m K F p d hphom e he hpure
  have hxeq : x
      = ∑ e ∈ p.support, chartMonSummand m K F p d hphom e := by
    apply Subtype.ext
    show (x : Localization (Submonoid.powers (Ideal.Quotient.mk
        (Ideal.span (Set.range (mkSystem m K F))) (mkLin m K (distEll m K)))))
      = _
    rw [hval, Localization.mk_eq_mk'_apply, ← hpeq]
    have hden : (⟨(Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem m K F)))
          (mkLin m K (distEll m K))) ^ d,
        (Submonoid.mem_powers_iff _ _).mpr ⟨d, rfl⟩⟩ :
        Submonoid.powers (Ideal.Quotient.mk
          (Ideal.span (Set.range (mkSystem m K F)))
          (mkLin m K (distEll m K))))
        = chartDenomPow m K F d := rfl
    rw [hden]
    conv_lhs => rw [p.as_sum, map_sum]
    have hval2 : ∀ y : chartRing m K (mkSystem m K F) (distEll m K),
        (y : Localization (Submonoid.powers (Ideal.Quotient.mk
          (Ideal.span (Set.range (mkSystem m K F)))
          (mkLin m K (distEll m K)))))
        = Subalgebra.val _ y := fun y => rfl
    rw [hval2, map_sum]
    simp only [← hval2]
    rw [Finset.sum_congr rfl (fun e he => hsummand_coe e he), chart_mk'_sum]
  rw [hxeq]
  have hsplit := Finset.sum_filter_add_sum_filter_not p.support
    (fun e => e = Finsupp.single (Fin.last (m + 1)) d)
    (fun e => chartMonSummand m K F p d hphom e)
  rw [← hsplit]
  have hP0 : ∑ e ∈ p.support.filter
        (fun e => e = Finsupp.single (Fin.last (m + 1)) d),
      chartMonSummand m K F p d hphom e = 0 := by
    have hterm : ∀ e ∈ p.support.filter
          (fun e => e = Finsupp.single (Fin.last (m + 1)) d),
        chartMonSummand m K F p d hphom e
          = algebraMap K _ (p.coeff e) := by
      intro e he
      rw [Finset.mem_filter] at he
      exact chartMonSummand_of_pure m K F p d hphom e he.1 he.2
    rw [Finset.sum_congr rfl hterm, ← map_sum]
    have hE4 := eval_rep_eq_sum_pure m K p d hphom
    rw [← hE4, heval0, map_zero]
  have hP : ∑ e ∈ p.support.filter
        (fun e => e = Finsupp.single (Fin.last (m + 1)) d),
      chartMonSummand m K F p d hphom e
      ∈ Ideal.span (Set.range (chartGen m K F)) := by
    rw [hP0]
    exact Submodule.zero_mem _
  refine add_mem hP ?_
  apply Submodule.sum_mem
  intro e he
  rw [Finset.mem_filter] at he
  exact chartMonSummand_mem_span m K F p d hphom e he.1 he.2

set_option maxHeartbeats 1000000 in
-- Cumulative localization-diamond TC tax: verified at 800k
-- heartbeats (every step fits 30k alone; bare generic rewrites time out).
/-- Transfer of `m ≤ m²` to the local ring, by membership analysis: every
maximal-ideal element is a fraction `mk' x y` (`exists_mk'_eq`), its
numerator lies in the chart point ideal (`mk'_mem_maximal_iff`) hence in
the generator span (§5e), each generator image lies in `m * m` (via
`aeval_eq_chartGen` + `aeval_mem_pointIdeal_sq`, transported along
`map_eq_maximalIdeal` at the `map`-side only), and the fraction splits as
numerator-image times a unit fraction (`mk'_eq_mul_mk'_one`).

Elaboration needs `maxHeartbeats 1000000`: cumulative TC tax over the
localization diamond (probed: every step fits 30k heartbeats alone;
bare `map_mul` / `smul_eq_mul` rewrites instead time out, so the proof
grounds them through ascribed `have`s).

## References

* This module, `Appendix_FixedPoint.BezoutChain.pointIdeal_le_span_chartGen`,
  `Appendix_FixedPoint.BezoutChain.aeval_eq_chartGen`,
  `Appendix_FixedPoint.BezoutChain.aeval_mem_pointIdeal_sq`.
* `Mathlib/RingTheory/Localization/AtPrime/Basic.lean`,
  `Localization.AtPrime.map_eq_maximalIdeal`,
  `IsLocalization.AtPrime.mk'_mem_maximal_iff`.
* `Mathlib/RingTheory/Localization/Defs.lean`,
  `IsLocalization.exists_mk'_eq`, `IsLocalization.mk'_eq_mul_mk'_one`.
* `Mathlib/RingTheory/Ideal/Operations.lean`, `Ideal.smul_eq_mul`,
  `Ideal.mul_le`, `Ideal.mul_mem_mul`.
* `Mathlib/RingTheory/Ideal/Defs.lean`, `Ideal.mul_mem_right`.
* `Mathlib/RingTheory/Ideal/Maps.lean`, `Ideal.map_le_iff_le_comap`,
  `Ideal.mem_map_of_mem`, `Ideal.mem_comap`.
* `Mathlib/RingTheory/Ideal/Span.lean`, `Ideal.span_le`.
* `Mathlib/Algebra/Group/Hom/Defs.lean`, `map_mul`. -/
theorem distMSqAbsorb_proof (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2) :
    DistMSqAbsorb m K F hF := by
  unfold DistMSqAbsorb distMaximalSub
  have hle : Ideal.map (algebraMap (chartRing m K (mkSystem m K F) (distEll m K))
          (distLocRing m K F hF))
        (pointIdeal m K (mkSystem m K F) (distEll m K) (zRep m K)
            (hvGdist m K F hF) (hℓdist m K) *
          pointIdeal m K (mkSystem m K F) (distEll m K) (zRep m K)
            (hvGdist m K F hF) (hℓdist m K))
      ≤ Ideal.map (algebraMap (chartRing m K (mkSystem m K F) (distEll m K))
            (distLocRing m K F hF))
          (pointIdeal m K (mkSystem m K F) (distEll m K) (zRep m K)
            (hvGdist m K F hF) (hℓdist m K)) *
        Ideal.map (algebraMap (chartRing m K (mkSystem m K F) (distEll m K))
            (distLocRing m K F hF))
          (pointIdeal m K (mkSystem m K F) (distEll m K) (zRep m K)
            (hvGdist m K F hF) (hℓdist m K)) := by
    rw [Ideal.map_le_iff_le_comap, Ideal.mul_le]
    intro a ha b hb
    rw [Ideal.mem_comap]
    have hmul : algebraMap (chartRing m K (mkSystem m K F) (distEll m K))
            (distLocRing m K F hF) (a * b)
          = algebraMap (chartRing m K (mkSystem m K F) (distEll m K))
              (distLocRing m K F hF) a *
            algebraMap (chartRing m K (mkSystem m K F) (distEll m K))
              (distLocRing m K F hF) b :=
      map_mul _ _ _
    rw [hmul]
    exact Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ ha)
      (Ideal.mem_map_of_mem _ hb)
  have hgen : ∀ i : Fin (m + 1),
      algebraMap (chartRing m K (mkSystem m K F) (distEll m K))
          (distLocRing m K F hF) (chartGen m K F i)
        ∈ IsLocalRing.maximalIdeal (distLocRing m K F hF) *
          IsLocalRing.maximalIdeal (distLocRing m K F hF) := by
    intro i
    have hmem : chartGen m K F i
        ∈ pointIdeal m K (mkSystem m K F) (distEll m K) (zRep m K)
            (hvGdist m K F hF) (hℓdist m K) *
          pointIdeal m K (mkSystem m K F) (distEll m K) (zRep m K)
            (hvGdist m K F hF) (hℓdist m K) := by
      rw [← aeval_eq_chartGen m K F hF i]
      exact aeval_mem_pointIdeal_sq m K F hF i
    have hmemMap := hle (Ideal.mem_map_of_mem _ hmem)
    have hEq : Ideal.map (algebraMap (chartRing m K (mkSystem m K F) (distEll m K))
            (distLocRing m K F hF))
          (pointIdeal m K (mkSystem m K F) (distEll m K) (zRep m K)
            (hvGdist m K F hF) (hℓdist m K))
        = IsLocalRing.maximalIdeal (distLocRing m K F hF) :=
      Localization.AtPrime.map_eq_maximalIdeal
    rw [hEq] at hmemMap
    exact hmemMap
  have hspan : Ideal.span (Set.range (chartGen m K F))
      ≤ Ideal.comap (algebraMap (chartRing m K (mkSystem m K F) (distEll m K))
          (distLocRing m K F hF))
        (IsLocalRing.maximalIdeal (distLocRing m K F hF) *
          IsLocalRing.maximalIdeal (distLocRing m K F hF)) := by
    rw [Ideal.span_le]
    intro y hy
    obtain ⟨i, rfl⟩ := hy
    exact hgen i
  intro z hz
  obtain ⟨x, y, rfl⟩ := IsLocalization.exists_mk'_eq
    (pointIdeal m K (mkSystem m K F) (distEll m K) (zRep m K)
      (hvGdist m K F hF) (hℓdist m K)).primeCompl z
  have hmem : IsLocalization.mk' (distLocRing m K F hF) x y
        ∈ IsLocalRing.maximalIdeal (distLocRing m K F hF)
      ↔ x ∈ pointIdeal m K (mkSystem m K F) (distEll m K) (zRep m K)
        (hvGdist m K F hF) (hℓdist m K) :=
    IsLocalization.AtPrime.mk'_mem_maximal_iff _ _ x y
  rw [hmem] at hz
  have hfx : algebraMap (chartRing m K (mkSystem m K F) (distEll m K))
          (distLocRing m K F hF) x
        ∈ IsLocalRing.maximalIdeal (distLocRing m K F hF) *
          IsLocalRing.maximalIdeal (distLocRing m K F hF) :=
    hspan (pointIdeal_le_span_chartGen m K F hF hz)
  have hmk : IsLocalization.mk' (distLocRing m K F hF) x y
        = algebraMap (chartRing m K (mkSystem m K F) (distEll m K))
            (distLocRing m K F hF) x *
          IsLocalization.mk' (distLocRing m K F hF) 1 y :=
    IsLocalization.mk'_eq_mul_mk'_one x y
  have hsm : IsLocalRing.maximalIdeal (distLocRing m K F hF) •
          IsLocalRing.maximalIdeal (distLocRing m K F hF)
        = IsLocalRing.maximalIdeal (distLocRing m K F hF) *
          IsLocalRing.maximalIdeal (distLocRing m K F hF) :=
    Ideal.smul_eq_mul _ _
  rw [hsm, hmk]
  exact Ideal.mul_mem_right _ _ hfx

/-- The generator-image span sits inside the local maximal ideal: each
generator lies in the chart point ideal (`chartGen_mem_pointIdeal`),
so its image lies in `map f P = maximalIdeal`
(`map_eq_maximalIdeal`, map-side transfer as in §5f).

## References

* This module, `Appendix_FixedPoint.BezoutChain.chartGen_mem_pointIdeal`.
* `Mathlib/RingTheory/Localization/AtPrime/Basic.lean`,
  `Localization.AtPrime.map_eq_maximalIdeal`.
* `Mathlib/RingTheory/Ideal/Maps.lean`, `Ideal.mem_map_of_mem`.
* `Mathlib/RingTheory/Ideal/Span.lean`, `Ideal.span_le`. -/
theorem distSpanImageLeMaximal (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2) :
    Ideal.span ((algebraMap (chartRing m K (mkSystem m K F) (distEll m K))
          (distLocRing m K F hF)) '' Set.range (chartGen m K F))
      ≤ IsLocalRing.maximalIdeal (distLocRing m K F hF) := by
  rw [Ideal.span_le]
  intro w hw
  obtain ⟨g, hg, rfl⟩ := hw
  obtain ⟨i, rfl⟩ := hg
  have hgen : chartGen m K F i ∈ pointIdeal m K (mkSystem m K F)
        (distEll m K) (zRep m K) (hvGdist m K F hF) (hℓdist m K) :=
    chartGen_mem_pointIdeal m K F hF i
  have hmap : algebraMap (chartRing m K (mkSystem m K F) (distEll m K))
          (distLocRing m K F hF) (chartGen m K F i)
        ∈ Ideal.map (algebraMap (chartRing m K (mkSystem m K F) (distEll m K))
            (distLocRing m K F hF))
          (pointIdeal m K (mkSystem m K F) (distEll m K) (zRep m K)
            (hvGdist m K F hF) (hℓdist m K)) :=
    Ideal.mem_map_of_mem _ hgen
  have hEq : Ideal.map (algebraMap (chartRing m K (mkSystem m K F) (distEll m K))
            (distLocRing m K F hF))
          (pointIdeal m K (mkSystem m K F) (distEll m K) (zRep m K)
            (hvGdist m K F hF) (hℓdist m K))
        = IsLocalRing.maximalIdeal (distLocRing m K F hF) :=
    Localization.AtPrime.map_eq_maximalIdeal
  rw [hEq] at hmap
  exact hmap

set_option maxHeartbeats 600000 in
-- Cumulative localization-diamond TC tax, same moves as §5f.
/-- The local maximal ideal sits inside the generator-image span:
fraction analysis (§5f moves) reduces to the numerator, which is a
generator combination (§5e), and generator images land in the span.

## References

* This module, `Appendix_FixedPoint.BezoutChain.pointIdeal_le_span_chartGen`.
* `Mathlib/RingTheory/Localization/AtPrime/Basic.lean`,
  `IsLocalization.AtPrime.mk'_mem_maximal_iff`.
* `Mathlib/RingTheory/Localization/Defs.lean`,
  `IsLocalization.exists_mk'_eq`, `IsLocalization.mk'_eq_mul_mk'_one`.
* `Mathlib/RingTheory/Ideal/Defs.lean`, `Ideal.mul_mem_right`.
* `Mathlib/RingTheory/Ideal/Span.lean`, `Ideal.span_le`,
  `Ideal.subset_span`. -/
theorem distMaximalLeSpanImage (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2) :
    IsLocalRing.maximalIdeal (distLocRing m K F hF)
      ≤ Ideal.span ((algebraMap (chartRing m K (mkSystem m K F) (distEll m K))
          (distLocRing m K F hF)) '' Set.range (chartGen m K F)) := by
  intro z hz
  obtain ⟨x, y, rfl⟩ := IsLocalization.exists_mk'_eq
    (pointIdeal m K (mkSystem m K F) (distEll m K) (zRep m K)
      (hvGdist m K F hF) (hℓdist m K)).primeCompl z
  have hmem : IsLocalization.mk' (distLocRing m K F hF) x y
        ∈ IsLocalRing.maximalIdeal (distLocRing m K F hF)
      ↔ x ∈ pointIdeal m K (mkSystem m K F) (distEll m K) (zRep m K)
        (hvGdist m K F hF) (hℓdist m K) :=
    IsLocalization.AtPrime.mk'_mem_maximal_iff _ _ x y
  rw [hmem] at hz
  have hxspan : x ∈ Ideal.span (Set.range (chartGen m K F)) :=
    pointIdeal_le_span_chartGen m K F hF hz
  have hspanmap : Ideal.span (Set.range (chartGen m K F))
      ≤ Ideal.comap (algebraMap (chartRing m K (mkSystem m K F) (distEll m K))
          (distLocRing m K F hF))
        (Ideal.span ((algebraMap (chartRing m K (mkSystem m K F) (distEll m K))
            (distLocRing m K F hF)) '' Set.range (chartGen m K F))) := by
    rw [Ideal.span_le]
    intro w hw
    obtain ⟨i, rfl⟩ := hw
    have hTi : algebraMap (chartRing m K (mkSystem m K F) (distEll m K))
            (distLocRing m K F hF) (chartGen m K F i)
          ∈ Ideal.span ((algebraMap (chartRing m K (mkSystem m K F) (distEll m K))
              (distLocRing m K F hF)) '' Set.range (chartGen m K F)) :=
      Ideal.subset_span ⟨chartGen m K F i, ⟨i, rfl⟩, rfl⟩
    exact hTi
  have hfx : algebraMap (chartRing m K (mkSystem m K F) (distEll m K))
          (distLocRing m K F hF) x
        ∈ Ideal.span ((algebraMap (chartRing m K (mkSystem m K F) (distEll m K))
            (distLocRing m K F hF)) '' Set.range (chartGen m K F)) :=
    hspanmap hxspan
  have hmk : IsLocalization.mk' (distLocRing m K F hF) x y
        = algebraMap (chartRing m K (mkSystem m K F) (distEll m K))
            (distLocRing m K F hF) x *
          IsLocalization.mk' (distLocRing m K F hF) 1 y :=
    IsLocalization.mk'_eq_mul_mk'_one x y
  rw [hmk]
  exact Ideal.mul_mem_right _ _ hfx

/-- The local maximal ideal is the generator-image span (both
inclusions above).

## References

* This module, `Appendix_FixedPoint.BezoutChain.distMaximalLeSpanImage`,
  `Appendix_FixedPoint.BezoutChain.distSpanImageLeMaximal`.
* Core `le_antisymm`. -/
theorem distMaximalEqSpan (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2) :
    IsLocalRing.maximalIdeal (distLocRing m K F hF)
      = Ideal.span ((algebraMap (chartRing m K (mkSystem m K F) (distEll m K))
          (distLocRing m K F hF)) '' Set.range (chartGen m K F)) :=
  le_antisymm (distMaximalLeSpanImage m K F hF)
    (distSpanImageLeMaximal m K F hF)

/-- Exact residual R-hequiv-2 (`DistMaximalFG`): the local maximal
ideal is finitely generated — it is the span of the finite
generator-image set.

## References

* This module, `Appendix_FixedPoint.BezoutChain.distMaximalEqSpan`.
* `Mathlib/RingTheory/Finiteness/Basic.lean`, `Submodule.fg_span`.
* `Mathlib/Data/Set/Finite/Range.lean`, `Set.finite_range`.
* `Mathlib/Data/Set/Finite/Basic.lean`, `Set.Finite.image`. -/
theorem distMaximalFG_proof (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2) :
    DistMaximalFG m K F hF := by
  unfold DistMaximalFG distMaximalSub
  rw [distMaximalEqSpan m K F hF]
  have hfin : ((algebraMap (chartRing m K (mkSystem m K F) (distEll m K))
          (distLocRing m K F hF)) '' Set.range (chartGen m K F)).Finite :=
    (Set.finite_range _).image _
  exact Submodule.fg_span hfin

set_option maxHeartbeats 400000 in
-- Cumulative localization-diamond TC tax (Nakayama application plus membership moves).
/-- Exact residual R-hequiv-0 (`DistMaximalBot`): the distinguished
local maximal ideal is trivial, via `nakayama_chart` applied to the
`DistMSqAbsorb` + `DistMaximalFG` pair. This discharges the
composition through the Ore/comm instance diamond: `distMaximalSub`'s
projection-instance ascription routes around it (cf. its docstring);
the resulting `Submodule`-equality converts to the `Ideal`-goal by
membership (`Ideal`-vs-`Submodule` membership is syntactic defeq).

## References

* This module, `Appendix_FixedPoint.BezoutChain.nakayama_chart`,
  `Appendix_FixedPoint.BezoutChain.distMaximalFG_proof`,
  `Appendix_FixedPoint.BezoutChain.distMSqAbsorb_proof`,
  `Appendix_FixedPoint.BezoutChain.distMaximalSub`.
* `Mathlib/Algebra/Module/Submodule/Lattice.lean`,
  `Submodule.mem_bot`.
* `Mathlib/Algebra/Module/Submodule/Defs.lean`,
  `Submodule.zero_mem`.
* Core `le_antisymm`, `bot_le`. -/
theorem distMaximalBot_proof (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2) :
    DistMaximalBot m K F hF := by
  unfold DistMaximalBot
  have hbot : distMaximalSub m K F hF = ⊥ :=
    nakayama_chart (distLocRing m K F hF) (distMaximalSub m K F hF)
      (distMaximalFG_proof m K F hF) (distMSqAbsorb_proof m K F hF)
  apply le_antisymm _ bot_le
  intro x hx
  have hxS : x ∈ distMaximalSub m K F hF := hx
  rw [hbot] at hxS
  have hx0 : x = 0 := (Submodule.mem_bot _).mp hxS
  rw [hx0]
  exact Submodule.zero_mem _

/-- Unconditional hequiv at the distinguished chart/point: the §5
discharge (`distMaximalBot_proof`) feeds the proved residual chain.

GRADE (hequiv result): unconditional on `[hFhom]` (the former
`DistMaximalBot` hypothesis is discharged by `distMaximalBot_proof`).

## References

* This module, `Appendix_FixedPoint.BezoutChain.hequiv_dist_of_residuals`,
  `Appendix_FixedPoint.BezoutChain.distMaximalBot_proof`. -/
noncomputable def hequiv_dist (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2) :
    distLocRing m K F hF ≃ₗ[K] K :=
  hequiv_dist_of_residuals m K F hF (distMaximalBot_proof m K F hF)

/-- Unconditional local multiplicity `1` at the distinguished
representative (finrank of the unconditional `hequiv`).

## References

* This module, `Appendix_FixedPoint.BezoutChain.dist_mult_one_of_residuals`,
  `Appendix_FixedPoint.BezoutChain.distMaximalBot_proof`. -/
theorem dist_mult_one (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2) :
    localMultiplicity m K (mkSystem m K F) (distEll m K) (zRep m K)
      (hvGdist m K F hF) (hℓdist m K) = 1 :=
  dist_mult_one_of_residuals m K F hF (distMaximalBot_proof m K F hF)

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
