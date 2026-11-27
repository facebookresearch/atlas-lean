/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.Curve.TwoChartIntegralModel
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.FieldTheory.RatFunc.AsPolynomial

@[expose] public section

open AlgebraicCurve AlgebraicGeometry CategoryTheory

/-- Unfolding and characterization on the concrete `ℤ ⊂ ℚ`, `j = 2` model. -/
example [Fact ((2 : ℚ) ≠ 0)] : (2 : ℚ) ∈ TwoChartIntegralModel.chartAlgFin ℤ ℚ 2 ∧
    TwoChartIntegralModel.chartFinOpen ℤ ℚ 2 ⊔
      TwoChartIntegralModel.chartInfOpen ℤ ℚ 2 = ⊤ ∧
    (TwoChartIntegralModel.polynomialToChartFin ℤ ℚ 2 Polynomial.X : ℚ) = 2 := by
  refine ⟨TwoChartIntegralModel.subset_chartAlg ℤ ℚ _ rfl,
    TwoChartIntegralModel.twoChartCover ℤ ℚ 2, ?_⟩
  rw [TwoChartIntegralModel.polynomialToChartFin_X,
    TwoChartIntegralModel.coe_jChartFin]

/-- The gluing condition for the concrete glued scheme at `j = 2`. -/
example [Fact ((2 : ℚ) ≠ 0)] : TwoChartIntegralModel.fFin ℤ ℚ 2 ≫ TwoChartIntegralModel.ιFin ℤ ℚ 2 =
    TwoChartIntegralModel.fInf ℤ ℚ 2 ≫ TwoChartIntegralModel.ιInf ℤ ℚ 2 := by
  exact TwoChartIntegralModel.glue_condition ℤ ℚ 2

/-- The chart algebra is Mathlib's integral closure of `ℤ[S]` in `ℚ`, up to reducible unfolding. -/
example (S : Set ℚ) :
    TwoChartIntegralModel.chartAlg ℤ ℚ S =
      (integralClosure (Algebra.adjoin ℤ S) ℚ).restrictScalars ℤ := by
  with_reducible rfl

/-- The overlap ring is strictly larger than the finite chart ring: `1/2` lies in the overlap of the
concrete `ℤ ⊂ ℚ`, `j = 2` model but not in its finite chart. -/
example [Fact ((2 : ℚ) ≠ 0)] : (1 / 2 : ℚ) ∈ TwoChartIntegralModel.chartAlgMid ℤ ℚ 2 ∧
    (1 / 2 : ℚ) ∉ TwoChartIntegralModel.chartAlgFin ℤ ℚ 2 := by
  refine ⟨TwoChartIntegralModel.subset_chartAlg ℤ ℚ _ (by norm_num), fun h => ?_⟩
  rw [TwoChartIntegralModel.mem_chartAlg_iff] at h
  have : Algebra.IsIntegral ℤ (Algebra.adjoin ℤ {(2 : ℚ)}) :=
    Algebra.IsIntegral.adjoin fun x hx => by
      rw [Set.mem_singleton_iff.mp hx]
      simpa using isIntegral_algebraMap (R := ℤ) (A := ℚ) (x := 2)
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp (isIntegral_trans (R := ℤ) _ h)
  have hy' : (y : ℚ) = 1 / 2 := by simpa using hy
  have h2 : ((2 * y : ℤ) : ℚ) = 1 := by
    push_cast
    rw [hy']
    norm_num
  have : 2 * y = 1 := by exact_mod_cast h2
  omega

/-- In the overlap ring, `1/2` is the fraction `1 / j` of the localization of the finite chart
away from `j = 2`. -/
example [Fact ((2 : ℚ) ≠ 0)] :
    letI := (TwoChartIntegralModel.inclFin ℤ ℚ 2).toRingHom.toAlgebra
    haveI := TwoChartIntegralModel.isLocalization_away_inclFin ℤ ℚ 2
    (IsLocalization.mk' (TwoChartIntegralModel.chartAlgMid ℤ ℚ 2)
      (1 : TwoChartIntegralModel.chartAlgFin ℤ ℚ 2)
      (⟨TwoChartIntegralModel.jChartFin ℤ ℚ 2, 1, pow_one _⟩ : Submonoid.powers _) : ℚ) =
      1 / 2 := by
  let := (TwoChartIntegralModel.inclFin ℤ ℚ 2).toRingHom.toAlgebra
  have := TwoChartIntegralModel.isLocalization_away_inclFin ℤ ℚ 2
  have h := congrArg Subtype.val (IsLocalization.mk'_spec (TwoChartIntegralModel.chartAlgMid ℤ ℚ 2)
    (1 : TwoChartIntegralModel.chartAlgFin ℤ ℚ 2)
    (⟨TwoChartIntegralModel.jChartFin ℤ ℚ 2, 1, pow_one _⟩ : Submonoid.powers _))
  simp only [Subalgebra.coe_mul, RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, TwoChartIntegralModel.coe_chartIncl,
    TwoChartIntegralModel.coe_jChartFin, map_one, Subalgebra.coe_one] at h
  linear_combination h / 2

/-- The hypotheses do not make the glued scheme a model of `F`: for `F = K(t)` and `j = 1`, the
generator `t` lies in none of the three chart rings, each being the integral closure of `K` in
`K(t)`. -/
example (K : Type) [Field K] [Fact ((1 : RatFunc K) ≠ 0)] :
    (RatFunc.X : RatFunc K) ∉ TwoChartIntegralModel.chartAlgFin K (RatFunc K) 1 ∧
      (RatFunc.X : RatFunc K) ∉ TwoChartIntegralModel.chartAlgInf K (RatFunc K) 1 ∧
      (RatFunc.X : RatFunc K) ∉ TwoChartIntegralModel.chartAlgMid K (RatFunc K) 1 := by
  have key : ∀ S : Set (RatFunc K), S ⊆ {1, 1⁻¹} →
      (RatFunc.X : RatFunc K) ∉ TwoChartIntegralModel.chartAlg K (RatFunc K) S := by
    intro S hS h
    rw [TwoChartIntegralModel.mem_chartAlg_iff] at h
    have : Algebra.IsIntegral K (Algebra.adjoin K S) :=
      Algebra.IsIntegral.adjoin fun x hx => by
        have hx' := hS hx
        simp only [inv_one, Set.mem_insert_iff, Set.mem_singleton_iff, or_self] at hx'
        rw [hx']
        exact isIntegral_one
    exact RatFunc.transcendental_X (isIntegral_trans (R := K) _ h).isAlgebraic
  exact ⟨key _ (by simp), key _ (by simp), key _ subset_rfl⟩

/-- The reduction of the concrete model modulo `2` lies over `Spec (ℤ ⧸ (2))`. -/
example [Fact ((2 : ℚ) ≠ 0)] :
    TwoChartIntegralModel.reductionι ℤ ℚ 2 (Ideal.span {2}) ≫ TwoChartIntegralModel.toBase ℤ ℚ 2 =
      TwoChartIntegralModel.reductionToBase ℤ ℚ 2 (Ideal.span {2}) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {2}))) :=
  TwoChartIntegralModel.reductionι_toBase ℤ ℚ 2 _

/-- Over a field, the two-chart scheme is `CurveModel.glued`, so the results proved for that model
apply to it; for instance, it is an integral scheme. -/
example (K L : Type) [Field K] [Field L] [Algebra K L] (t : L) [Fact (t ≠ 0)] :
    AlgebraicGeometry.IsIntegral (AlgebraicCurve.TwoChartIntegralModel K L t) := by
  rw [TwoChartIntegralModel.twoChartIntegralModel_eq_glued]
  infer_instance

open IntermediateField in
/-- Over a field, the finite chart ring is `CurveModel.chartRing K {t}`, so it is a Dedekind domain
when `L` is finite and separable over `K(t)`. -/
example (K L : Type) [Field K] [Field L] [Algebra K L] (t : L) [Fact (t ≠ 0)]
    [FiniteDimensional K⟮t⟯ L] [Algebra.IsSeparable K⟮t⟯ L] :
    IsDedekindDomain (TwoChartIntegralModel.chartAlgFin K L t) :=
  inferInstance

noncomputable section CoefficientExtension

/-- `ℤ[X]` acting on `ℚ` by `X ↦ 0`. -/
private local instance : Algebra (Polynomial ℤ) ℚ :=
  (Polynomial.aeval (R := ℤ) (0 : ℚ)).toRingHom.toAlgebra

private local instance : IsScalarTower ℤ (Polynomial ℤ) ℚ := .of_algebraMap_eq fun _ => by
  simp [RingHom.algebraMap_toAlgebra]

/-- The coefficient inclusion is not a scalar extension: for `ℤ → ℤ[X]` acting on `ℚ` by
`X ↦ 0` and `S = {2}`, the two chart rings agree, so the inclusion is surjective, while `X` acts
on the target by `0`. -/
example : Function.Surjective (TwoChartIntegralModel.chartCoeffIncl ℤ ℚ (Polynomial ℤ) {2}) ∧
    algebraMap (Polynomial ℤ) (TwoChartIntegralModel.chartAlg (Polynomial ℤ) ℚ {2})
      Polynomial.X = 0 := by
  refine ⟨fun y => ?_, Subtype.ext (by simp [RingHom.algebraMap_toAlgebra])⟩
  have hle : (Algebra.adjoin (Polynomial ℤ) {(2 : ℚ)}).toSubring ≤
      (Algebra.adjoin ℤ {(2 : ℚ)}).toSubring := by
    intro x hx
    refine Algebra.adjoin_induction (p := fun x _ => x ∈ Algebra.adjoin ℤ {(2 : ℚ)})
      (fun x hx => Algebra.subset_adjoin hx) (fun p => ?_) (fun _ _ _ _ => add_mem)
      (fun _ _ _ _ => mul_mem) hx
    rw [RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      Polynomial.aeval_def, Polynomial.eval₂_at_zero]
    exact Subalgebra.algebraMap_mem _ _
  have hy : IsIntegral (Algebra.adjoin ℤ {(2 : ℚ)}) (y : ℚ) :=
    ((TwoChartIntegralModel.mem_chartAlg_iff _ _).mp y.2).map_of_comp_eq
      (Subring.inclusion hle) (RingHom.id ℚ) (by ext; rfl)
  exact ⟨⟨y, (TwoChartIntegralModel.mem_chartAlg_iff _ _).mpr hy⟩, Subtype.ext rfl⟩

end CoefficientExtension
