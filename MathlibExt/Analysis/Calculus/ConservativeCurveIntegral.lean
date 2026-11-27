/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Conservative curve integrals

For a C1 potential on an open neighbourhood of a C1 path, the
electrostatic field `E = -∇φ` integrates to the potential drop
`φ a - φ b`, both in coordinate form and in Mathlib's
curve-integral convention. Path reversal negates the value. The
rotational field on a triangular loop is the standard
nonconservative counterexample.

-/

@[expose] public section

namespace MetaMathlibExt

open Set
open scoped unitInterval RealInnerProductSpace Gradient

private theorem innerSL_eq_toDual (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) :
    innerSL ℝ v = InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)) v :=
  ContinuousLinearMap.ext fun w =>
    (innerSL_apply_apply _ v w).trans InnerProductSpace.toDual_apply_apply.symm

private theorem innerSL_eq_neg_fderiv (n : ℕ) (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (E : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (U : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n))
    (hE : ∀ x ∈ U, E x = -∇ φ x) (hx : x ∈ U) :
    innerSL ℝ (E x) = -(fderiv ℝ φ x) := by
  apply ContinuousLinearMap.ext
  intro w
  rw [hE x hx, innerSL_apply_apply, inner_neg_left,
    ← InnerProductSpace.toDual_apply_apply, toDual_gradient]
  simp

private theorem contDiffOn_extend_segment (a b : EuclideanSpace ℝ (Fin 2)) :
    ContDiffOn ℝ 1 (Path.segment a b).extend I := by
  have hlm : ContDiff ℝ 1 (fun t : ℝ => AffineMap.lineMap a b t) :=
    AffineMap.contDiff_lineMap a b
  exact hlm.contDiffOn.congr (fun x hx => Path.eqOn_extend_segment a b hx)

/-! ### Representation lemmas -/

/-- **Gradient theorem for Mathlib's curve integral.** For `φ` C1 on an open set containing
the range of a C1 path `γ` from `a` to `b`, `∫ᶜ x in γ, dφ x = φ b - φ a`. -/
theorem curveIntegral_fderiv_eq_sub (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (φ : F → ℝ) (U : Set F) (a b : F) (γ : Path a b) (hU : IsOpen U)
    (hφ : ContDiffOn ℝ 1 φ U) (hγ : ContDiffOn ℝ 1 γ.extend I) (hγU : range γ ⊆ U) :
    ∫ᶜ x in γ, fderiv ℝ φ x = φ b - φ a := by
  have hmem : ∀ t : ℝ, t ∈ Ioo (0 : ℝ) 1 → γ.extend t ∈ U := by
    intro t ht
    have htI : t ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht
    rw [Path.extend_apply γ htI]
    exact hγU (mem_range_self _)
  have hcomp : ∀ t : ℝ, t ∈ Ioo (0 : ℝ) 1 →
      HasDerivAt (φ ∘ γ.extend) ((fderiv ℝ φ (γ.extend t)) (deriv γ.extend t)) t := by
    intro t ht
    have htI : t ∈ I := Ioo_subset_Icc_self ht
    have hnhds : I ∈ nhds t := Icc_mem_nhds ht.1 ht.2
    have hφd : DifferentiableAt ℝ φ (γ.extend t) :=
      (hφ.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds (hmem t ht))
    have hγd : DifferentiableAt ℝ γ.extend t :=
      ((hγ.differentiableOn one_ne_zero) t htI).differentiableAt hnhds
    exact HasFDerivAt.comp_hasDerivAt t hφd.hasFDerivAt hγd.hasDerivAt
  have hae : ∀ t : ℝ, t ∈ Ioo (0 : ℝ) 1 →
      curveIntegralFun (fun x => fderiv ℝ φ x) γ t = deriv (φ ∘ γ.extend) t := by
    intro t ht
    have hdw : derivWithin γ.extend I t = deriv γ.extend t :=
      derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)
    rw [curveIntegralFun_def, hdw]
    exact (hcomp t ht).deriv.symm
  have hcongr : (∫ t in (0 : ℝ)..1, curveIntegralFun (fun x => fderiv ℝ φ x) γ t)
      = ∫ t in (0 : ℝ)..1, deriv (φ ∘ γ.extend) t := by
    refine intervalIntegral.integral_congr_ae_restrict ?_
    rw [uIoc_of_le zero_le_one, ← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [MeasureTheory.ae_restrict_mem (by measurability)] with t ht
    exact hae t ht
  have hCI : CurveIntegrable (fun x => fderiv ℝ φ x) γ :=
    (hφ.continuousOn_fderiv_of_isOpen hU le_rfl).curveIntegrable_of_contDiffOn hγ
      (fun t => hγU (mem_range_self t))
  have hI : IntervalIntegrable (curveIntegralFun (fun x => fderiv ℝ φ x) γ)
      MeasureTheory.volume 0 1 := hCI
  have hint : IntervalIntegrable (deriv (φ ∘ γ.extend)) MeasureTheory.volume 0 1 := by
    refine hI.congr_ae ?_
    rw [uIoc_of_le zero_le_one, ← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [MeasureTheory.ae_restrict_mem (by measurability)] with t ht
    exact hae t ht
  have hmaps : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → γ.extend t ∈ U := by
    intro t ht
    rw [Path.extend_apply γ ht]
    exact hγU (mem_range_self _)
  have hcont : ContinuousOn (φ ∘ γ.extend) (Icc (0 : ℝ) 1) :=
    hφ.continuousOn.comp (Path.continuous_extend γ).continuousOn hmaps
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (φ ∘ γ.extend) (deriv (φ ∘ γ.extend) x) x := by
    intro x hx
    have hc := hcomp x hx
    rw [hc.deriv]
    exact hc
  calc ∫ᶜ x in γ, fderiv ℝ φ x
        = ∫ t in (0 : ℝ)..1, deriv (φ ∘ γ.extend) t := by
          rw [curveIntegral_def]
          exact hcongr
      _ = (φ ∘ γ.extend) 1 - (φ ∘ γ.extend) 0 :=
          intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont hderiv hint
      _ = φ b - φ a := by
          rw [Function.comp_apply, Function.comp_apply, Path.extend_one γ,
            Path.extend_zero γ]

/-- The curve integral of the 1-form `x ↦ ⟪E x, ·⟫` is the coordinate integral
`∫₀¹ ⟪E (γ t), γ' t⟫ dt` (no regularity needed). -/
theorem curveIntegral_innerSL_eq_integral_inner_deriv (n : ℕ)
    (E : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (a b : EuclideanSpace ℝ (Fin n))
    (γ : Path a b) :
    ∫ᶜ x in γ, innerSL ℝ (E x) = ∫ t in (0 : ℝ)..1, ⟪E (γ.extend t), deriv γ.extend t⟫ := by
  rw [curveIntegral_eq_intervalIntegral_deriv]
  refine intervalIntegral.integral_congr_ae_restrict (Filter.Eventually.of_forall fun t => ?_)
  exact innerSL_apply_apply _ _ _

/-! ### Headline results -/

private theorem curveIntegral_innerSL_neg_gradient_eq_sub_aux (n : ℕ)
    (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (E : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (U : Set (EuclideanSpace ℝ (Fin n))) (a b : EuclideanSpace ℝ (Fin n)) (γ : Path a b)
    (hU : IsOpen U) (hφ : ContDiffOn ℝ 1 φ U) (hE : ∀ x ∈ U, E x = -∇ φ x)
    (hγ : ContDiffOn ℝ 1 γ.extend I) (hγU : range γ ⊆ U) :
    ∫ᶜ x in γ, innerSL ℝ (E x) = φ a - φ b := by
  have hpt : ∀ t : ℝ, t ∈ Ioo (0 : ℝ) 1 →
      curveIntegralFun (fun x => innerSL ℝ (E x)) γ t
        = curveIntegralFun (fun x => -(fderiv ℝ φ x)) γ t := by
    intro t ht
    have htI : t ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht
    have hmem : γ.extend t ∈ U := by
      rw [Path.extend_apply γ htI]
      exact hγU (mem_range_self _)
    simp only [curveIntegralFun_def,
      innerSL_eq_neg_fderiv n φ E U (γ.extend t) hE hmem]
  have hcongr : (∫ t in (0 : ℝ)..1, curveIntegralFun (fun x => innerSL ℝ (E x)) γ t)
      = ∫ t in (0 : ℝ)..1, curveIntegralFun (fun x => -(fderiv ℝ φ x)) γ t := by
    refine intervalIntegral.integral_congr_ae_restrict ?_
    rw [uIoc_of_le zero_le_one, ← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [MeasureTheory.ae_restrict_mem (by measurability)] with t ht
    exact hpt t ht
  have hmain := curveIntegral_fderiv_eq_sub _ φ U a b γ hU hφ hγ hγU
  calc ∫ᶜ x in γ, innerSL ℝ (E x)
        = ∫ᶜ x in γ, -(fderiv ℝ φ x) := by
          rw [curveIntegral_def, curveIntegral_def]
          exact hcongr
      _ = -(∫ᶜ x in γ, fderiv ℝ φ x) := curveIntegral_fun_neg
      _ = -(φ b - φ a) := by rw [hmain]
      _ = φ a - φ b := by ring

/-- **Electrostatic line integral, coordinate form.** For `φ` C1 on an open neighbourhood `U`
of a C1 path `γ` from `a` to `b` in `ℝⁿ` and `E = -∇φ` on `U`,
`∫₀¹ ⟪E (γ t), γ' t⟫ dt = φ a - φ b`. -/
theorem integral_inner_neg_gradient_eq_sub (n : ℕ) (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (E : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (U : Set (EuclideanSpace ℝ (Fin n))) (a b : EuclideanSpace ℝ (Fin n)) (γ : Path a b)
    (hU : IsOpen U) (hφ : ContDiffOn ℝ 1 φ U) (hE : ∀ x ∈ U, E x = -∇ φ x)
    (hγ : ContDiffOn ℝ 1 γ.extend I) (hγU : range γ ⊆ U) :
    ∫ t in (0 : ℝ)..1, ⟪E (γ.extend t), deriv γ.extend t⟫ = φ a - φ b := by
  rw [← curveIntegral_innerSL_eq_integral_inner_deriv]
  exact curveIntegral_innerSL_neg_gradient_eq_sub_aux n φ E U a b γ hU hφ hE hγ hγU

/-- **Electrostatic line integral, curve-integral convention.** Same hypotheses;
`∫ᶜ x in γ, ⟪E x, ·⟫ = φ a - φ b`. -/
theorem curveIntegral_innerSL_neg_gradient_eq_sub (n : ℕ) (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (E : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (U : Set (EuclideanSpace ℝ (Fin n))) (a b : EuclideanSpace ℝ (Fin n)) (γ : Path a b)
    (hU : IsOpen U) (hφ : ContDiffOn ℝ 1 φ U) (hE : ∀ x ∈ U, E x = -∇ φ x)
    (hγ : ContDiffOn ℝ 1 γ.extend I) (hγU : range γ ⊆ U) :
    ∫ᶜ x in γ, innerSL ℝ (E x) = φ a - φ b := by
  exact curveIntegral_innerSL_neg_gradient_eq_sub_aux n φ E U a b γ hU hφ hE hγ hγU

/-! ### Validation: path reversal and an affine potential -/

/-- **Path reversal.** Along `γ.symm` (from `b` to `a`) the integral is `φ b - φ a`. -/
theorem curveIntegral_symm_innerSL_neg_gradient_eq_sub (n : ℕ)
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (E : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (U : Set (EuclideanSpace ℝ (Fin n))) (a b : EuclideanSpace ℝ (Fin n)) (γ : Path a b)
    (hU : IsOpen U) (hφ : ContDiffOn ℝ 1 φ U) (hE : ∀ x ∈ U, E x = -∇ φ x)
    (hγ : ContDiffOn ℝ 1 γ.extend I) (hγU : range γ ⊆ U) :
    ∫ᶜ x in γ.symm, innerSL ℝ (E x) = φ b - φ a := by
  rw [curveIntegral_symm]
  have hmain :=
    curveIntegral_innerSL_neg_gradient_eq_sub n φ E U a b γ hU hφ hE hγ hγU
  rw [hmain]
  ring

/-- The affine potential `φ x = ⟪c, x⟫ + d` has field `-∇φ = -c` everywhere. -/
theorem neg_gradient_affinePotential (n : ℕ) (c : EuclideanSpace ℝ (Fin n)) (d : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    -∇ (fun y : EuclideanSpace ℝ (Fin n) => ⟪c, y⟫ + d) x = -c := by
  have hF : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => ⟪c, y⟫ + d) (innerSL ℝ c) x :=
    (innerSL ℝ c).hasFDerivAt.add_const d
  rw [innerSL_eq_toDual] at hF
  have hG : HasGradientAt (fun y : EuclideanSpace ℝ (Fin n) => ⟪c, y⟫ + d) c x :=
    hasGradientAt_iff_hasFDerivAt.mpr hF
  have hgrad := hG.gradient
  rw [hgrad]

/-- Affine potential `φ x = ⟪(3,-1), x⟫ + d` along the non-axis-aligned segment
`(0,0) → (1,2)`: the field `E = -(3,-1)` integrates to `φ (0,0) - φ (1,2) = -1`. -/
theorem curveIntegral_affineField_segment (d : ℝ) :
    (∫ᶜ _ in Path.segment (!₂[0, 0] : EuclideanSpace ℝ (Fin 2)) !₂[1, 2],
        innerSL ℝ (-(!₂[3, -1] : EuclideanSpace ℝ (Fin 2)))) = -1 ∧
      (-1 : ℝ) = (⟪(!₂[3, -1] : EuclideanSpace ℝ (Fin 2)), !₂[0, 0]⟫ + d) -
        (⟪(!₂[3, -1] : EuclideanSpace ℝ (Fin 2)), !₂[1, 2]⟫ + d) := by
  constructor
  · rw [curveIntegral_segment_const]
    norm_num [innerSL_apply_apply, PiLp.inner_apply, Fin.sum_univ_two, PiLp.toLp_apply,
      PiLp.sub_apply, PiLp.neg_apply, RCLike.inner_apply, RCLike.conj_to_real,
      Matrix.cons_val_zero, Matrix.cons_val_one]
  · norm_num [PiLp.inner_apply, Fin.sum_univ_two, PiLp.toLp_apply, RCLike.inner_apply,
      RCLike.conj_to_real, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The same affine field along the reversed segment integrates to `+1`. -/
theorem curveIntegral_affineField_segment_symm :
    (∫ᶜ _ in (Path.segment (!₂[0, 0] : EuclideanSpace ℝ (Fin 2)) !₂[1, 2]).symm,
        innerSL ℝ (-(!₂[3, -1] : EuclideanSpace ℝ (Fin 2)))) = 1 := by
  have h := (curveIntegral_affineField_segment (0 : ℝ)).1
  rw [curveIntegral_symm, h]
  norm_num

/-! ### Validation: a nonconservative field -/

/-- The rotational field `(x, y) ↦ (-y, x)` on `ℝ²`. -/
noncomputable def rotationalField (x : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  !₂[-x 1, x 0]

/-- The closed triangle `(0,0) → (1,0) → (0,1) → (0,0)`, a piecewise C1 loop. -/
noncomputable def triangleLoop :
    Path (!₂[0, 0] : EuclideanSpace ℝ (Fin 2)) (!₂[0, 0] : EuclideanSpace ℝ (Fin 2)) :=
  (Path.segment (!₂[0, 0] : EuclideanSpace ℝ (Fin 2)) !₂[1, 0]).trans
    ((Path.segment (!₂[1, 0] : EuclideanSpace ℝ (Fin 2)) !₂[0, 1]).trans
      (Path.segment (!₂[0, 1] : EuclideanSpace ℝ (Fin 2)) !₂[0, 0]))

/-- Around the triangle the rotational field integrates to `1` (twice the enclosed area). -/
theorem curveIntegral_rotationalField_triangleLoop :
    ∫ᶜ x in triangleLoop, innerSL ℝ (rotationalField x) = 1 := by
  have hfun1 : (fun t : ℝ => innerSL ℝ
        (rotationalField (AffineMap.lineMap (!₂[0, 0] : EuclideanSpace ℝ (Fin 2))
          (!₂[1, 0] : EuclideanSpace ℝ (Fin 2)) t))
        ((!₂[1, 0] : EuclideanSpace ℝ (Fin 2)) - (!₂[0, 0] : EuclideanSpace ℝ (Fin 2))))
      = fun _ => (0 : ℝ) := by
    funext t
    simp only [innerSL_apply_apply, rotationalField, AffineMap.lineMap_apply_module,
      PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, PiLp.inner_apply, Fin.sum_univ_two,
      RCLike.inner_apply, RCLike.conj_to_real, Matrix.cons_val_zero,
      Matrix.cons_val_one, smul_eq_mul]
    ring
  have hCI1 : CurveIntegrable (fun x => innerSL ℝ (rotationalField x))
      (Path.segment (!₂[0, 0] : EuclideanSpace ℝ (Fin 2))
        (!₂[1, 0] : EuclideanSpace ℝ (Fin 2))) := by
    rw [curveIntegrable_segment]
    simp only [hfun1]
    exact continuous_const.intervalIntegrable _ _
  have hv1 : (∫ᶜ x in Path.segment (!₂[0, 0] : EuclideanSpace ℝ (Fin 2))
      (!₂[1, 0] : EuclideanSpace ℝ (Fin 2)), innerSL ℝ (rotationalField x)) = 0 := by
    rw [curveIntegral_segment]
    simp only [hfun1, intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_zero]
  have hfun2 : (fun t : ℝ => innerSL ℝ
        (rotationalField (AffineMap.lineMap (!₂[1, 0] : EuclideanSpace ℝ (Fin 2))
          (!₂[0, 1] : EuclideanSpace ℝ (Fin 2)) t))
        ((!₂[0, 1] : EuclideanSpace ℝ (Fin 2)) - (!₂[1, 0] : EuclideanSpace ℝ (Fin 2))))
      = fun _ => (1 : ℝ) := by
    funext t
    simp only [innerSL_apply_apply, rotationalField, AffineMap.lineMap_apply_module,
      PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, PiLp.inner_apply, Fin.sum_univ_two,
      RCLike.inner_apply, RCLike.conj_to_real, Matrix.cons_val_zero,
      Matrix.cons_val_one, smul_eq_mul]
    ring
  have hCI2 : CurveIntegrable (fun x => innerSL ℝ (rotationalField x))
      (Path.segment (!₂[1, 0] : EuclideanSpace ℝ (Fin 2))
        (!₂[0, 1] : EuclideanSpace ℝ (Fin 2))) := by
    rw [curveIntegrable_segment]
    simp only [hfun2]
    exact continuous_const.intervalIntegrable _ _
  have hv2 : (∫ᶜ x in Path.segment (!₂[1, 0] : EuclideanSpace ℝ (Fin 2))
      (!₂[0, 1] : EuclideanSpace ℝ (Fin 2)), innerSL ℝ (rotationalField x)) = 1 := by
    rw [curveIntegral_segment]
    simp only [hfun2, intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
  have hfun3 : (fun t : ℝ => innerSL ℝ
        (rotationalField (AffineMap.lineMap (!₂[0, 1] : EuclideanSpace ℝ (Fin 2))
          (!₂[0, 0] : EuclideanSpace ℝ (Fin 2)) t))
        ((!₂[0, 0] : EuclideanSpace ℝ (Fin 2)) - (!₂[0, 1] : EuclideanSpace ℝ (Fin 2))))
      = fun _ => (0 : ℝ) := by
    funext t
    simp only [innerSL_apply_apply, rotationalField, AffineMap.lineMap_apply_module,
      PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, PiLp.inner_apply, Fin.sum_univ_two,
      RCLike.inner_apply, RCLike.conj_to_real, Matrix.cons_val_zero,
      Matrix.cons_val_one, smul_eq_mul]
    ring
  have hCI3 : CurveIntegrable (fun x => innerSL ℝ (rotationalField x))
      (Path.segment (!₂[0, 1] : EuclideanSpace ℝ (Fin 2))
        (!₂[0, 0] : EuclideanSpace ℝ (Fin 2))) := by
    rw [curveIntegrable_segment]
    simp only [hfun3]
    exact continuous_const.intervalIntegrable _ _
  have hv3 : (∫ᶜ x in Path.segment (!₂[0, 1] : EuclideanSpace ℝ (Fin 2))
      (!₂[0, 0] : EuclideanSpace ℝ (Fin 2)), innerSL ℝ (rotationalField x)) = 0 := by
    rw [curveIntegral_segment]
    simp only [hfun3, intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_zero]
  have hCI23 : CurveIntegrable (fun x => innerSL ℝ (rotationalField x))
      ((Path.segment (!₂[1, 0] : EuclideanSpace ℝ (Fin 2))
          (!₂[0, 1] : EuclideanSpace ℝ (Fin 2))).trans
        (Path.segment (!₂[0, 1] : EuclideanSpace ℝ (Fin 2))
          (!₂[0, 0] : EuclideanSpace ℝ (Fin 2)))) :=
    hCI2.trans hCI3
  have e1 : (∫ᶜ x in (Path.segment (!₂[0, 0] : EuclideanSpace ℝ (Fin 2))
        (!₂[1, 0] : EuclideanSpace ℝ (Fin 2))).trans
          ((Path.segment (!₂[1, 0] : EuclideanSpace ℝ (Fin 2))
            (!₂[0, 1] : EuclideanSpace ℝ (Fin 2))).trans
            (Path.segment (!₂[0, 1] : EuclideanSpace ℝ (Fin 2))
              (!₂[0, 0] : EuclideanSpace ℝ (Fin 2)))),
        innerSL ℝ (rotationalField x))
      = (∫ᶜ x in Path.segment (!₂[0, 0] : EuclideanSpace ℝ (Fin 2))
          (!₂[1, 0] : EuclideanSpace ℝ (Fin 2)), innerSL ℝ (rotationalField x))
        + ∫ᶜ x in (Path.segment (!₂[1, 0] : EuclideanSpace ℝ (Fin 2))
          (!₂[0, 1] : EuclideanSpace ℝ (Fin 2))).trans
          (Path.segment (!₂[0, 1] : EuclideanSpace ℝ (Fin 2))
            (!₂[0, 0] : EuclideanSpace ℝ (Fin 2))),
          innerSL ℝ (rotationalField x) :=
    curveIntegral_trans hCI1 hCI23
  have e2 : (∫ᶜ x in (Path.segment (!₂[1, 0] : EuclideanSpace ℝ (Fin 2))
        (!₂[0, 1] : EuclideanSpace ℝ (Fin 2))).trans
        (Path.segment (!₂[0, 1] : EuclideanSpace ℝ (Fin 2))
          (!₂[0, 0] : EuclideanSpace ℝ (Fin 2))),
        innerSL ℝ (rotationalField x))
      = (∫ᶜ x in Path.segment (!₂[1, 0] : EuclideanSpace ℝ (Fin 2))
          (!₂[0, 1] : EuclideanSpace ℝ (Fin 2)), innerSL ℝ (rotationalField x))
        + ∫ᶜ x in Path.segment (!₂[0, 1] : EuclideanSpace ℝ (Fin 2))
          (!₂[0, 0] : EuclideanSpace ℝ (Fin 2)), innerSL ℝ (rotationalField x) :=
    curveIntegral_trans hCI2 hCI3
  simp only [triangleLoop]
  rw [e1, e2, hv1, hv2, hv3]
  norm_num

/-- The rotational field is not assigned the potential-difference result: its integral around
the closed triangle differs from `φ a - φ a` for every `φ`. -/
theorem curveIntegral_rotationalField_triangleLoop_ne_sub
    (φ : EuclideanSpace ℝ (Fin 2) → ℝ) :
    ∫ᶜ x in triangleLoop, innerSL ℝ (rotationalField x) ≠
      φ !₂[0, 0] - φ !₂[0, 0] := by
  rw [curveIntegral_rotationalField_triangleLoop, sub_self]
  exact one_ne_zero

/-- No C1 potential on any open neighbourhood of the triangle has the rotational field as its
negative gradient. -/
theorem not_exists_potential_rotationalField :
    ¬ ∃ (φ : EuclideanSpace ℝ (Fin 2) → ℝ) (U : Set (EuclideanSpace ℝ (Fin 2))),
      IsOpen U ∧ range triangleLoop ⊆ U ∧ ContDiffOn ℝ 1 φ U ∧
        ∀ x ∈ U, rotationalField x = -∇ φ x := by
  rintro ⟨φ, U, hU, htriU, hφ, hE⟩
  have hsegU : range (Path.segment (!₂[0, 0] : EuclideanSpace ℝ (Fin 2))
          (!₂[1, 0] : EuclideanSpace ℝ (Fin 2))) ⊆ U
        ∧ range (Path.segment (!₂[1, 0] : EuclideanSpace ℝ (Fin 2))
          (!₂[0, 1] : EuclideanSpace ℝ (Fin 2))) ⊆ U
        ∧ range (Path.segment (!₂[0, 1] : EuclideanSpace ℝ (Fin 2))
          (!₂[0, 0] : EuclideanSpace ℝ (Fin 2))) ⊆ U := by
    simp only [triangleLoop, Path.trans_range, union_subset_iff] at htriU
    exact htriU
  obtain ⟨hseg1U, hseg2U, hseg3U⟩ := hsegU
  have h1 : (∫ᶜ x in Path.segment (!₂[0, 0] : EuclideanSpace ℝ (Fin 2))
      (!₂[1, 0] : EuclideanSpace ℝ (Fin 2)), innerSL ℝ (rotationalField x))
      = φ (!₂[0, 0] : EuclideanSpace ℝ (Fin 2)) - φ (!₂[1, 0] : EuclideanSpace ℝ (Fin 2)) :=
    curveIntegral_innerSL_neg_gradient_eq_sub 2 φ rotationalField U _ _ _
      hU hφ hE (contDiffOn_extend_segment _ _) hseg1U
  have h2 : (∫ᶜ x in Path.segment (!₂[1, 0] : EuclideanSpace ℝ (Fin 2))
      (!₂[0, 1] : EuclideanSpace ℝ (Fin 2)), innerSL ℝ (rotationalField x))
      = φ (!₂[1, 0] : EuclideanSpace ℝ (Fin 2)) - φ (!₂[0, 1] : EuclideanSpace ℝ (Fin 2)) :=
    curveIntegral_innerSL_neg_gradient_eq_sub 2 φ rotationalField U _ _ _
      hU hφ hE (contDiffOn_extend_segment _ _) hseg2U
  have h3 : (∫ᶜ x in Path.segment (!₂[0, 1] : EuclideanSpace ℝ (Fin 2))
      (!₂[0, 0] : EuclideanSpace ℝ (Fin 2)), innerSL ℝ (rotationalField x))
      = φ (!₂[0, 1] : EuclideanSpace ℝ (Fin 2)) - φ (!₂[0, 0] : EuclideanSpace ℝ (Fin 2)) :=
    curveIntegral_innerSL_neg_gradient_eq_sub 2 φ rotationalField U _ _ _
      hU hφ hE (contDiffOn_extend_segment _ _) hseg3U
  have hform : ∀ x ∈ U, innerSL ℝ (rotationalField x) = -(fderiv ℝ φ x) :=
    fun x hx => innerSL_eq_neg_fderiv 2 φ rotationalField U x hE hx
  have hfd : ContinuousOn (fderiv ℝ φ) U := hφ.continuousOn_fderiv_of_isOpen hU le_rfl
  have hneg : ContinuousOn (fun x => -(fderiv ℝ φ x)) U := hfd.neg
  have hωcont : ContinuousOn (fun x => innerSL ℝ (rotationalField x)) U :=
    hneg.congr (fun x hx => hform x hx)
  have hCI1 : CurveIntegrable (fun x => innerSL ℝ (rotationalField x))
      (Path.segment (!₂[0, 0] : EuclideanSpace ℝ (Fin 2))
        (!₂[1, 0] : EuclideanSpace ℝ (Fin 2))) :=
    hωcont.curveIntegrable_of_contDiffOn (contDiffOn_extend_segment _ _)
      (fun t => hseg1U (mem_range_self t))
  have hCI2 : CurveIntegrable (fun x => innerSL ℝ (rotationalField x))
      (Path.segment (!₂[1, 0] : EuclideanSpace ℝ (Fin 2))
        (!₂[0, 1] : EuclideanSpace ℝ (Fin 2))) :=
    hωcont.curveIntegrable_of_contDiffOn (contDiffOn_extend_segment _ _)
      (fun t => hseg2U (mem_range_self t))
  have hCI3 : CurveIntegrable (fun x => innerSL ℝ (rotationalField x))
      (Path.segment (!₂[0, 1] : EuclideanSpace ℝ (Fin 2))
        (!₂[0, 0] : EuclideanSpace ℝ (Fin 2))) :=
    hωcont.curveIntegrable_of_contDiffOn (contDiffOn_extend_segment _ _)
      (fun t => hseg3U (mem_range_self t))
  have hCI23 : CurveIntegrable (fun x => innerSL ℝ (rotationalField x))
      ((Path.segment (!₂[1, 0] : EuclideanSpace ℝ (Fin 2))
          (!₂[0, 1] : EuclideanSpace ℝ (Fin 2))).trans
        (Path.segment (!₂[0, 1] : EuclideanSpace ℝ (Fin 2))
          (!₂[0, 0] : EuclideanSpace ℝ (Fin 2)))) :=
    hCI2.trans hCI3
  have e1 : (∫ᶜ x in (Path.segment (!₂[0, 0] : EuclideanSpace ℝ (Fin 2))
        (!₂[1, 0] : EuclideanSpace ℝ (Fin 2))).trans
          ((Path.segment (!₂[1, 0] : EuclideanSpace ℝ (Fin 2))
            (!₂[0, 1] : EuclideanSpace ℝ (Fin 2))).trans
            (Path.segment (!₂[0, 1] : EuclideanSpace ℝ (Fin 2))
              (!₂[0, 0] : EuclideanSpace ℝ (Fin 2)))),
        innerSL ℝ (rotationalField x))
      = (∫ᶜ x in Path.segment (!₂[0, 0] : EuclideanSpace ℝ (Fin 2))
          (!₂[1, 0] : EuclideanSpace ℝ (Fin 2)), innerSL ℝ (rotationalField x))
        + ∫ᶜ x in (Path.segment (!₂[1, 0] : EuclideanSpace ℝ (Fin 2))
          (!₂[0, 1] : EuclideanSpace ℝ (Fin 2))).trans
          (Path.segment (!₂[0, 1] : EuclideanSpace ℝ (Fin 2))
            (!₂[0, 0] : EuclideanSpace ℝ (Fin 2))),
          innerSL ℝ (rotationalField x) :=
    curveIntegral_trans hCI1 hCI23
  have e2 : (∫ᶜ x in (Path.segment (!₂[1, 0] : EuclideanSpace ℝ (Fin 2))
        (!₂[0, 1] : EuclideanSpace ℝ (Fin 2))).trans
        (Path.segment (!₂[0, 1] : EuclideanSpace ℝ (Fin 2))
          (!₂[0, 0] : EuclideanSpace ℝ (Fin 2))),
        innerSL ℝ (rotationalField x))
      = (∫ᶜ x in Path.segment (!₂[1, 0] : EuclideanSpace ℝ (Fin 2))
          (!₂[0, 1] : EuclideanSpace ℝ (Fin 2)), innerSL ℝ (rotationalField x))
        + ∫ᶜ x in Path.segment (!₂[0, 1] : EuclideanSpace ℝ (Fin 2))
          (!₂[0, 0] : EuclideanSpace ℝ (Fin 2)), innerSL ℝ (rotationalField x) :=
    curveIntegral_trans hCI2 hCI3
  have hsum : (∫ᶜ x in triangleLoop, innerSL ℝ (rotationalField x))
      = (φ (!₂[0, 0] : EuclideanSpace ℝ (Fin 2)) - φ (!₂[1, 0] : EuclideanSpace ℝ (Fin 2)))
        + ((φ (!₂[1, 0] : EuclideanSpace ℝ (Fin 2))
          - φ (!₂[0, 1] : EuclideanSpace ℝ (Fin 2)))
          + (φ (!₂[0, 1] : EuclideanSpace ℝ (Fin 2))
            - φ (!₂[0, 0] : EuclideanSpace ℝ (Fin 2)))) := by
    simp only [triangleLoop]
    rw [e1, e2, h1, h2, h3]
  rw [curveIntegral_rotationalField_triangleLoop] at hsum
  have hzero : (φ (!₂[0, 0] : EuclideanSpace ℝ (Fin 2))
      - φ (!₂[1, 0] : EuclideanSpace ℝ (Fin 2)))
        + ((φ (!₂[1, 0] : EuclideanSpace ℝ (Fin 2))
          - φ (!₂[0, 1] : EuclideanSpace ℝ (Fin 2)))
          + (φ (!₂[0, 1] : EuclideanSpace ℝ (Fin 2))
            - φ (!₂[0, 0] : EuclideanSpace ℝ (Fin 2)))) = 0 := by
    ring
  rw [hzero] at hsum
  exact one_ne_zero hsum

end MetaMathlibExt
