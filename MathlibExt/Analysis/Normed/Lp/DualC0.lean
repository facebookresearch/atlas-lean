/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.Dual
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
public import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Duality of `c₀` spaces

For an index type `ι` and `𝕜 = ℝ` or `ℂ`, the space `c₀(ι, 𝕜)` of
sequences vanishing at infinity (along the cofinite filter) is the closed
subspace of `ℓ^∞(ι, 𝕜)` of sequences tending to `0`. Its continuous dual is
isometrically isomorphic to `ℓ¹(ι, 𝕜)`: the isomorphism sends `a ∈ ℓ¹` to
the functional `x ↦ ∑' i, a i * x i`.

The public space is Mathlib's `ZeroAtInftyContinuousMap` on the index type
with its discrete topology, so the standard normed-space and completeness
instances apply. The `ℓ^∞` submodule representation is retained only through
its canonical coordinate-preserving linear isometric equivalence.

This duality is a new derived supporting result. The archived dual-space,
`L^p` and Hahn–Banach material provides related context, not an exact `c₀`
duality target or proof. The coefficient estimate uses finite subsets and
`conj w / ‖w‖`; finite truncations then recover each functional.

## Main declarations

* `c0 𝕜 ι` : the space of sequences `ι → 𝕜` vanishing at infinity.
* `c0Single i a` : the sequence which is `a` at `i` and `0` elsewhere.
* `c0DualPairing` : the pairing `ℓ¹ →L[𝕜] (c₀ →L[𝕜] 𝕜)`.
* `c0DualPairing_apply` : the pairing is given by `∑' i, a i * x i`.
* `c0DualEquiv` : the isometric isomorphism `ℓ¹ ≃ₗᵢ[𝕜] (c₀ →L[𝕜] 𝕜)`.
* `c0Eval i` : evaluation at `i`, equal to pairing with `lp.single 1 i 1`.
-/

@[expose] public section

namespace MathlibExt.Analysis.Normed.Lp.DualC0

open scoped ENNReal Topology ZeroAtInfty
open Filter

universe u v

section C0

/-- The `ℓ^∞` representation of canonical `c₀`, retained for compatibility.
`c0LpEquiv` identifies it isometrically with the standard space. -/
noncomputable def c0Submodule (𝕜 : Type u) [RCLike 𝕜] (ι : Type v) :
    Submodule 𝕜 (lp (fun _ : ι => 𝕜) ∞) where
  carrier := { f | Filter.Tendsto (⇑f) Filter.cofinite (𝓝 0) }
  zero_mem' := by
    show Filter.Tendsto (fun _ : ι => (0 : 𝕜)) Filter.cofinite (𝓝 0)
    exact tendsto_const_nhds
  add_mem' := by
    intro f g hf hg
    show Filter.Tendsto (⇑(f + g)) Filter.cofinite (𝓝 0)
    have hfun : (⇑(f + g) : ι → 𝕜) = fun x => (f : ι → 𝕜) x + (g : ι → 𝕜) x := by
      funext x
      simp
    rw [hfun]
    simpa only [add_zero] using hf.add hg
  smul_mem' := by
    intro c f hf
    show Filter.Tendsto (⇑(c • f)) Filter.cofinite (𝓝 0)
    have hfun : (⇑(c • f) : ι → 𝕜) = fun x => c • (f : ι → 𝕜) x := by
      funext x
      simp [lp.coeFn_smul]
    rw [hfun]
    simpa only [smul_zero] using Filter.Tendsto.const_smul hf c

/-- The canonical `C₀` space on the index type with its discrete topology.
The scalar/index argument order is retained, and no topology on `ι` is assumed. -/
abbrev c0 (𝕜 : Type u) [RCLike 𝕜] (ι : Type v) : Type (max u v) :=
  @ZeroAtInftyContinuousMap ι 𝕜 ⊥ _ _

variable {𝕜 : Type u} [RCLike 𝕜] {ι : Type v}

/-- Canonical `C₀` functions on the discrete index vanish along `cofinite`. -/
theorem c0_tendsto_zero (x : c0 𝕜 ι) : Tendsto (x : ι → 𝕜) cofinite (𝓝 0) := by
  letI : TopologicalSpace ι := ⊥
  letI : DiscreteTopology ι := ⟨rfl⟩
  have h := x.zero_at_infty'
  rw [Filter.cocompact_eq_cofinite] at h
  exact h

/-- A coordinate of a canonical `c₀` element is bounded by its norm. -/
theorem c0_apply_norm_le (x : c0 𝕜 ι) (i : ι) : ‖(x : ι → 𝕜) i‖ ≤ ‖x‖ := by
  letI : TopologicalSpace ι := ⊥
  have h := BoundedContinuousFunction.norm_coe_le_norm x.toBCF i
  rwa [ZeroAtInftyContinuousMap.norm_toBCF_eq_norm] at h

/-- The coordinate-preserving inclusion of canonical `c₀` in `ℓ^∞`. -/
noncomputable def c0ToLp (x : c0 𝕜 ι) : lp (fun _ : ι => 𝕜) ∞ :=
  ⟨(x : ι → 𝕜), memℓp_infty ⟨‖x‖, by
    rintro _ ⟨i, rfl⟩
    exact c0_apply_norm_le x i⟩⟩

noncomputable instance : CoeTC (c0 𝕜 ι) (lp (fun _ : ι => 𝕜) ∞) := ⟨c0ToLp⟩

@[simp] theorem c0ToLp_apply (x : c0 𝕜 ι) (i : ι) : c0ToLp x i = (x : ι → 𝕜) i := rfl

/-- The canonical norm equals the supremum norm of the `ℓ^∞` inclusion. -/
theorem c0_norm (x : c0 𝕜 ι) : ‖x‖ = ‖(x : lp (fun _ : ι => 𝕜) ∞)‖ := by
  letI : TopologicalSpace ι := ⊥
  apply le_antisymm
  · rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm (f := x)]
    apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).mpr
    intro i
    exact lp.norm_apply_le_norm (by simp : (∞ : ℝ≥0∞) ≠ 0) (x : lp (fun _ : ι => 𝕜) ∞) i
  · apply lp.norm_le_of_forall_le (norm_nonneg x)
    exact c0_apply_norm_le x

/-- Build canonical `c₀` from an `ℓ^∞` sequence and its cofinite limit.
This is the migration helper for the former subtype constructor. -/
noncomputable def c0OfLp (x : lp (fun _ : ι => 𝕜) ∞)
    (hx : Tendsto (x : ι → 𝕜) cofinite (𝓝 0)) : c0 𝕜 ι := by
  letI : TopologicalSpace ι := ⊥
  letI : DiscreteTopology ι := ⟨rfl⟩
  exact ZeroAtInftyContinuousMap.mk
    ⟨(x : ι → 𝕜), continuous_of_discreteTopology⟩ (by
      rw [Filter.cocompact_eq_cofinite]
      exact hx)

@[simp] theorem c0OfLp_apply (x : lp (fun _ : ι => 𝕜) ∞)
    (hx : Tendsto (x : ι → 𝕜) cofinite (𝓝 0)) (i : ι) :
    (c0OfLp x hx : ι → 𝕜) i = x i := rfl

/-- The canonical space and its existing `ℓ^∞` submodule representation are
linearly isometric through the unchanged coordinate function. -/
noncomputable def c0LpEquiv : c0 𝕜 ι ≃ₗᵢ[𝕜] ↥(c0Submodule 𝕜 ι) := by
  letI : TopologicalSpace ι := ⊥
  exact
    { toFun x := ⟨(x : lp (fun _ : ι => 𝕜) ∞), c0_tendsto_zero x⟩
      invFun x := c0OfLp (x : lp (fun _ : ι => 𝕜) ∞) x.2
      left_inv x := by
        apply ZeroAtInftyContinuousMap.ext
        intro i
        rfl
      right_inv x := by
        apply Subtype.ext
        apply lp.ext
        rfl
      map_add' x y := by
        apply Subtype.ext
        apply lp.ext
        funext i
        rfl
      map_smul' c x := by
        apply Subtype.ext
        apply lp.ext
        funext i
        rfl
      norm_map' x := (c0_norm x).symm }

variable [DecidableEq ι]

/-- The sequence which is `a` at `i` and `0` elsewhere, as an element of `c₀`. -/
noncomputable def c0Single (i : ι) (a : 𝕜) : c0 𝕜 ι := by
  classical
  refine c0OfLp (lp.single ∞ i a) ?_
  have hev : (fun _ : ι => (0 : 𝕜)) =ᶠ[Filter.cofinite]
      (⇑(lp.single (E := fun _ : ι => 𝕜) ∞ i a : lp (fun _ : ι => 𝕜) ∞)) := by
    show ∀ᶠ j in Filter.cofinite, (0 : 𝕜) = (lp.single (E := fun _ : ι => 𝕜) ∞ i a) j
    rw [Filter.eventually_cofinite]
    refine Set.Finite.subset (Set.finite_singleton i) ?_
    intro j hj
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff] at hj ⊢
    by_contra hne
    exact hj (lp.single_apply_ne (E := fun _ : ι => 𝕜) ∞ i a hne).symm
  exact Filter.Tendsto.congr' hev tendsto_const_nhds

/-- The coordinates of `c0Single i a`. -/
theorem c0Single_apply (i j : ι) (a : 𝕜) :
    ((c0Single (𝕜 := 𝕜) (ι := ι) i a : c0 𝕜 ι) : ι → 𝕜) j = if j = i then a else 0 := by
  show (lp.single (E := fun _ : ι => 𝕜) ∞ i a : ι → 𝕜) j = if j = i then a else 0
  rw [lp.single_apply]
  exact Pi.single_apply i a j

/-- The norm of `c0Single i a` is `‖a‖`. -/
theorem c0Single_norm (i : ι) (a : 𝕜) : ‖c0Single (𝕜 := 𝕜) (ι := ι) i a‖ = ‖a‖ := by
  rw [c0_norm]
  have hp : (0 : ℝ≥0∞) < (∞ : ℝ≥0∞) := by simp
  exact lp.norm_single (E := fun _ : ι => 𝕜) hp i a

/-- A finitely supported sequence, as an element of `c₀`. -/
noncomputable def c0FinsetSum (s : Finset ι) (c : ι → 𝕜) : c0 𝕜 ι :=
  ∑ i ∈ s, c i • c0Single (𝕜 := 𝕜) (ι := ι) i (1 : 𝕜)

/-- The coordinates of a finitely supported sequence. -/
theorem c0FinsetSum_apply (s : Finset ι) (c : ι → 𝕜) (j : ι) :
    ((c0FinsetSum (𝕜 := 𝕜) (ι := ι) s c : c0 𝕜 ι) : ι → 𝕜) j
      = if j ∈ s then c j else 0 := by
  letI : TopologicalSpace ι := ⊥
  let ev : c0 𝕜 ι →+ 𝕜 :=
    { toFun := fun x => (x : ι → 𝕜) j
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change ev (∑ i ∈ s, c i • c0Single i (1 : 𝕜)) = if j ∈ s then c j else 0
  rw [map_sum]
  change (∑ i ∈ s, ((c i • c0Single i (1 : 𝕜) : c0 𝕜 ι) : ι → 𝕜) j) = _
  simp only [ZeroAtInftyContinuousMap.smul_apply, smul_eq_mul, c0Single_apply,
    mul_ite, mul_one, mul_zero]
  exact Finset.sum_ite_eq s j c

/-- A functional applied to a finitely supported sequence. -/
theorem c0FinsetSum_apply_dual (Φ : StrongDual 𝕜 (c0 𝕜 ι)) (s : Finset ι) (c : ι → 𝕜) :
    Φ (c0FinsetSum (𝕜 := 𝕜) (ι := ι) s c) = ∑ i ∈ s, c i * Φ (c0Single i (1 : 𝕜)) := by
  rw [c0FinsetSum, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]

/-- The finite truncation of `x` to the indices in `s`. -/
noncomputable def c0Trunc (s : Finset ι) (x : c0 𝕜 ι) : c0 𝕜 ι :=
  c0FinsetSum (𝕜 := 𝕜) (ι := ι) s (fun i => (x : ι → 𝕜) i)

/-- The coordinates of a finite truncation. -/
theorem c0Trunc_apply (s : Finset ι) (x : c0 𝕜 ι) (j : ι) :
    ((c0Trunc (𝕜 := 𝕜) (ι := ι) s x : c0 𝕜 ι) : ι → 𝕜) j
      = if j ∈ s then (x : ι → 𝕜) j else 0 :=
  c0FinsetSum_apply s _ j

end C0

section Pairing

variable {𝕜 : Type u} [RCLike 𝕜] {ι : Type v}

/-- The norms of the coordinates of an `ℓ¹` sequence are summable. -/
theorem summable_norm_lp_one (a : lp (fun _ : ι => 𝕜) 1) :
    Summable fun i => ‖a i‖ := by
  have h := (memℓp_gen_iff (p := (1 : ℝ≥0∞)) (E := fun _ : ι => 𝕜) (by simp)).mp a.2
  simpa using h

/-- The series defining the pairing of `a ∈ ℓ¹` with `x ∈ c₀` is summable. -/
theorem summable_c0Pairing (a : lp (fun _ : ι => 𝕜) 1) (x : c0 𝕜 ι) :
    Summable fun i => a i * (x : ι → 𝕜) i := by
  apply Summable.of_norm_bounded (g := fun i => ‖a i‖ * ‖x‖)
    ((summable_norm_lp_one a).mul_right ‖x‖)
  intro i
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (c0_apply_norm_le x i) (norm_nonneg _)

/-- The pairing of `a ∈ ℓ¹` with `x ∈ c₀`, as a linear map in `x`. -/
noncomputable def c0PairingLin (a : lp (fun _ : ι => 𝕜) 1) : c0 𝕜 ι →ₗ[𝕜] 𝕜 where
  toFun x := ∑' i, a i * (x : ι → 𝕜) i
  map_add' x y := by
    rw [← Summable.tsum_add (summable_c0Pairing a x) (summable_c0Pairing a y)]
    refine tsum_congr fun i => ?_
    simp [ZeroAtInftyContinuousMap.coe_add, mul_add]
  map_smul' c x := by
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [← tsum_mul_left]
    refine tsum_congr fun i => ?_
    simp [ZeroAtInftyContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul]
    ring

/-- The pairing applied to `a` and `x`, by definition. -/
theorem c0PairingLin_apply (a : lp (fun _ : ι => 𝕜) 1) (x : c0 𝕜 ι) :
    c0PairingLin (𝕜 := 𝕜) (ι := ι) a x = ∑' i, a i * (x : ι → 𝕜) i := rfl

/-- The pairing is bounded by `‖a‖ * ‖x‖`. -/
theorem norm_c0PairingLin_le (a : lp (fun _ : ι => 𝕜) 1) (x : c0 𝕜 ι) :
    ‖c0PairingLin (𝕜 := 𝕜) (ι := ι) a x‖ ≤ ‖a‖ * ‖x‖ := by
  show ‖∑' i, a i * (x : ι → 𝕜) i‖ ≤ ‖a‖ * ‖x‖
  have hnorm : ‖a‖ = ∑' i, ‖a i‖ := by
    rw [lp.norm_eq_tsum_rpow (p := (1 : ℝ≥0∞)) (E := fun _ : ι => 𝕜) (by simp) a]
    simp
  have hsumNorm : Summable fun i => ‖a i * (x : ι → 𝕜) i‖ := by
    apply Summable.of_norm_bounded (g := fun i => ‖a i‖ * ‖x‖)
      ((summable_norm_lp_one a).mul_right ‖x‖)
    intro i
    simp only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), norm_mul]
    exact mul_le_mul_of_nonneg_left (c0_apply_norm_le x i) (norm_nonneg _)
  calc ‖∑' i, a i * (x : ι → 𝕜) i‖
      ≤ ∑' i, ‖a i * (x : ι → 𝕜) i‖ := norm_tsum_le_tsum_norm hsumNorm
    _ ≤ ∑' i, ‖a i‖ * ‖x‖ := by
        refine Summable.tsum_le_tsum (fun i => ?_) hsumNorm
          ((summable_norm_lp_one a).mul_right ‖x‖)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (c0_apply_norm_le x i) (norm_nonneg _)
    _ = (∑' i, ‖a i‖) * ‖x‖ := tsum_mul_right
    _ = ‖a‖ * ‖x‖ := by rw [hnorm]

/-- The pairing of `a ∈ ℓ¹` with `x ∈ c₀`, as a linear map in `a`. -/
noncomputable def c0DualPairingLin : lp (fun _ : ι => 𝕜) 1 →ₗ[𝕜] StrongDual 𝕜 (c0 𝕜 ι) where
  toFun a := (c0PairingLin (𝕜 := 𝕜) (ι := ι) a).mkContinuous ‖a‖ (norm_c0PairingLin_le a)
  map_add' a b := by
    apply ContinuousLinearMap.ext fun x => ?_
    simp only [add_apply, LinearMap.mkContinuous_apply, c0PairingLin_apply]
    show ∑' i, ((a + b : lp (fun _ : ι => 𝕜) 1) : ι → 𝕜) i * (x : ι → 𝕜) i
        = (∑' i, a i * (x : ι → 𝕜) i) + ∑' i, b i * (x : ι → 𝕜) i
    rw [← Summable.tsum_add (summable_c0Pairing a x) (summable_c0Pairing b x)]
    refine tsum_congr fun i => ?_
    rw [lp.coeFn_add, Pi.add_apply, add_mul]
  map_smul' c a := by
    apply ContinuousLinearMap.ext fun x => ?_
    simp only [smul_apply, LinearMap.mkContinuous_apply, c0PairingLin_apply,
      smul_eq_mul, RingHom.id_apply]
    show ∑' i, ((c • a : lp (fun _ : ι => 𝕜) 1) : ι → 𝕜) i * (x : ι → 𝕜) i
        = c * ∑' i, a i * (x : ι → 𝕜) i
    rw [← tsum_mul_left]
    refine tsum_congr fun i => ?_
    rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]

/-- The pairing applied to `a` and `x`. -/
theorem c0DualPairingLin_apply (a : lp (fun _ : ι => 𝕜) 1) (x : c0 𝕜 ι) :
    c0DualPairingLin (𝕜 := 𝕜) (ι := ι) a x = ∑' i, a i * (x : ι → 𝕜) i := rfl

/-- The pairing, as a linear map in `a`, has operator norm at most `‖a‖`. -/
theorem norm_c0DualPairingLin_le (a : lp (fun _ : ι => 𝕜) 1) :
    ‖c0DualPairingLin (𝕜 := 𝕜) (ι := ι) a‖ ≤ ‖a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a)
  intro x
  show ‖∑' i, a i * (x : ι → 𝕜) i‖ ≤ ‖a‖ * ‖x‖
  exact norm_c0PairingLin_le a x

/-- The pairing, as a linear map in `a`, is continuous. -/
theorem c0DualPairingLin_continuous :
    Continuous (c0DualPairingLin (𝕜 := 𝕜) (ι := ι)) :=
  AddMonoidHomClass.continuous_of_bound (c0DualPairingLin (𝕜 := 𝕜) (ι := ι)) 1 fun a => by
    rw [one_mul]
    exact norm_c0DualPairingLin_le a

/-- The canonical pairing `ℓ¹ →L[𝕜] (c₀ →L[𝕜] 𝕜)`. -/
noncomputable def c0DualPairing : lp (fun _ : ι => 𝕜) 1 →L[𝕜] StrongDual 𝕜 (c0 𝕜 ι) :=
  ContinuousLinearMap.mk c0DualPairingLin c0DualPairingLin_continuous

/-- The pairing is given by the sum of coordinatewise products. -/
theorem c0DualPairing_apply (a : lp (fun _ : ι => 𝕜) 1) (x : c0 𝕜 ι) :
    c0DualPairing (𝕜 := 𝕜) (ι := ι) a x = ∑' i, a i * (x : ι → 𝕜) i :=
  c0DualPairingLin_apply a x

/-- The pairing has operator norm at most `‖a‖`. -/
theorem norm_c0DualPairing_le (a : lp (fun _ : ι => 𝕜) 1) :
    ‖c0DualPairing (𝕜 := 𝕜) (ι := ι) a‖ ≤ ‖a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a)
  intro x
  rw [c0DualPairing_apply]
  exact norm_c0PairingLin_le a x

end Pairing

section Coeff

variable {𝕜 : Type u} [RCLike 𝕜] {ι : Type v} [DecidableEq ι]

/-- The coefficients of a dual functional, evaluated on the basis vectors. -/
noncomputable def c0Coeff (Φ : StrongDual 𝕜 (c0 𝕜 ι)) : ι → 𝕜 :=
  fun i => Φ (c0Single i (1 : 𝕜))

/-- The normalized scalar, zero at zero, with `unitScalar w * w = ‖w‖`. -/
noncomputable def c0UnitScalar (w : 𝕜) : 𝕜 :=
  if w = 0 then 0 else (starRingEnd 𝕜) w / (↑‖w‖ : 𝕜)

/-- The scalar identity behind the test vector. -/
theorem c0UnitScalar_mul (w : 𝕜) : c0UnitScalar (𝕜 := 𝕜) w * w = (↑‖w‖ : 𝕜) := by
  by_cases hw : w = 0
  · simp [c0UnitScalar, hw]
  · have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
    simp only [c0UnitScalar, hw, ite_false]
    rw [div_mul_eq_mul_div, RCLike.conj_mul, ← RCLike.ofReal_pow, ← RCLike.ofReal_div]
    congr 1
    rw [pow_two, mul_div_cancel_right₀ _ hpos.ne']

/-- The unit scalar has norm at most one. -/
theorem norm_c0UnitScalar_le (w : 𝕜) : ‖c0UnitScalar (𝕜 := 𝕜) w‖ ≤ 1 := by
  by_cases hw : w = 0
  · simp [c0UnitScalar, hw]
  · have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
    simp only [c0UnitScalar, hw, ite_false]
    rw [norm_div, RCLike.norm_conj, RCLike.norm_ofReal,
      abs_of_nonneg (norm_nonneg _), div_self hpos.ne']

/-- The finite-subset estimate for the coefficients of a dual functional. -/
theorem c0Coeff_finset_sum_le (Φ : StrongDual 𝕜 (c0 𝕜 ι)) (s : Finset ι) :
    ∑ i ∈ s, ‖c0Coeff (𝕜 := 𝕜) (ι := ι) Φ i‖ ≤ ‖Φ‖ := by
  letI : TopologicalSpace ι := ⊥
  classical
  set x : c0 𝕜 ι := c0FinsetSum (𝕜 := 𝕜) (ι := ι) s (fun i => c0UnitScalar (𝕜 := 𝕜) (c0Coeff Φ i))
    with hxdef
  have hnormx : ‖x‖ ≤ 1 := by
    rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm (f := x)]
    apply (BoundedContinuousFunction.norm_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro j
    change ‖((x : c0 𝕜 ι) : ι → 𝕜) j‖ ≤ 1
    rw [hxdef, c0FinsetSum_apply]
    by_cases hj : j ∈ s
    · rw [ite_eq_left hj]
      exact norm_c0UnitScalar_le _
    · rw [ite_eq_right hj, norm_zero]
      exact zero_le_one
  have hPhi : Φ x = (↑(∑ i ∈ s, ‖c0Coeff Φ i‖) : 𝕜) := by
    rw [hxdef, c0FinsetSum_apply_dual]
    rw [show (↑(∑ i ∈ s, ‖c0Coeff Φ i‖) : 𝕜)
        = ∑ i ∈ s, (↑‖c0Coeff Φ i‖ : 𝕜) by simp]
    exact Finset.sum_congr rfl fun i _ => c0UnitScalar_mul _
  calc ∑ i ∈ s, ‖c0Coeff Φ i‖
      = ‖Φ x‖ := by rw [hPhi, RCLike.norm_ofReal, abs_of_nonneg (Finset.sum_nonneg
          fun i _ => norm_nonneg _)]
    _ ≤ ‖Φ‖ * ‖x‖ := Φ.le_opNorm x
    _ ≤ ‖Φ‖ * 1 := mul_le_mul_of_nonneg_left hnormx (norm_nonneg Φ)
    _ = ‖Φ‖ := mul_one _

/-- The coefficients of a dual functional form an `ℓ¹` sequence. -/
theorem c0Coeff_memℓp (Φ : StrongDual 𝕜 (c0 𝕜 ι)) :
    Memℓp (c0Coeff (𝕜 := 𝕜) (ι := ι) Φ) (1 : ℝ≥0∞) := by
  apply memℓp_gen' (E := fun _ : ι => 𝕜) (C := ‖Φ‖)
  intro s
  simp only [ENNReal.toReal_one, Real.rpow_one]
  exact c0Coeff_finset_sum_le Φ s

/-- The `ℓ¹` element of coefficients of a dual functional. -/
noncomputable def c0CoeffLp (Φ : StrongDual 𝕜 (c0 𝕜 ι)) : lp (fun _ : ι => 𝕜) 1 :=
  ⟨c0Coeff (𝕜 := 𝕜) (ι := ι) Φ, c0Coeff_memℓp Φ⟩

/-- The coefficients of a dual functional have `ℓ¹` norm at most `‖Φ‖`. -/
theorem norm_c0CoeffLp_le (Φ : StrongDual 𝕜 (c0 𝕜 ι)) : ‖c0CoeffLp (𝕜 := 𝕜) (ι := ι) Φ‖ ≤ ‖Φ‖ := by
  apply lp.norm_le_of_forall_sum_le (p := (1 : ℝ≥0∞)) (by simp) (norm_nonneg Φ)
  intro s
  simp only [ENNReal.toReal_one, Real.rpow_one, Real.rpow_one]
  exact c0Coeff_finset_sum_le Φ s

end Coeff

section Surjectivity

variable {𝕜 : Type u} [RCLike 𝕜] {ι : Type v} [DecidableEq ι]

/-- The pairing with the coefficient sequence reproduces a functional, by
finite truncation: the partial sums over finite sets tend to `Φ x`. -/
theorem c0DualPairing_surjective : Function.Surjective (c0DualPairing (𝕜 := 𝕜) (ι := ι)) := by
  letI : TopologicalSpace ι := ⊥
  classical
  intro Φ
  refine ⟨c0CoeffLp Φ, ?_⟩
  apply ContinuousLinearMap.ext fun x => ?_
  rw [c0DualPairing_apply]
  have hsum : HasSum (fun i => (c0CoeffLp (𝕜 := 𝕜) (ι := ι) Φ : ι → 𝕜) i * (x : ι → 𝕜) i)
      (Φ x) := by
    show Filter.Tendsto (fun s : Finset ι =>
      ∑ i ∈ s, (c0CoeffLp (𝕜 := 𝕜) (ι := ι) Φ : ι → 𝕜) i * (x : ι → 𝕜) i)
      Filter.atTop (𝓝 (Φ x))
    rw [Metric.tendsto_atTop]
    intro ε hε
    set δ : ℝ := ε / (‖Φ‖ + 1) with hδdef
    have hδpos : 0 < δ := div_pos hε (by positivity)
    have hev : ∀ᶠ i in Filter.cofinite, ‖(x : ι → 𝕜) i‖ < δ := by
      have hx : Filter.Tendsto (⇑(x : lp (fun _ : ι => 𝕜) ∞)) Filter.cofinite (𝓝 0) :=
        c0_tendsto_zero x
      have h := (Metric.tendsto_nhds).mp hx δ hδpos
      exact h.mono fun i hi => by rwa [dist_eq_norm, sub_zero] at hi
    have hfin : { i : ι | ¬ ‖(x : ι → 𝕜) i‖ < δ }.Finite :=
      Filter.eventually_cofinite.mp hev
    refine ⟨hfin.toFinset, fun s hs => ?_⟩
    have htrunc : (∑ i ∈ s, (c0CoeffLp (𝕜 := 𝕜) (ι := ι) Φ : ι → 𝕜) i * (x : ι → 𝕜) i)
        = Φ (c0Trunc (𝕜 := 𝕜) (ι := ι) s x) := by
      rw [c0Trunc, c0FinsetSum_apply_dual]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact mul_comm _ _
    rw [htrunc, dist_eq_norm, ← map_sub]
    have hnorm : ‖c0Trunc (𝕜 := 𝕜) (ι := ι) s x - x‖ ≤ δ := by
      rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm (f := c0Trunc s x - x)]
      apply (BoundedContinuousFunction.norm_le hδpos.le).mpr
      intro j
      change ‖((c0Trunc s x - x : c0 𝕜 ι) : ι → 𝕜) j‖ ≤ δ
      have hsub : ((c0Trunc (𝕜 := 𝕜) (ι := ι) s x - x : c0 𝕜 ι) : ι → 𝕜) j
          = ((c0Trunc (𝕜 := 𝕜) (ι := ι) s x : c0 𝕜 ι) : ι → 𝕜) j - (x : ι → 𝕜) j := by
        simp
      rw [hsub, c0Trunc_apply]
      by_cases hj : j ∈ s
      · rw [ite_eq_left hj, sub_self, norm_zero]
        exact hδpos.le
      · rw [ite_eq_right hj, zero_sub, norm_neg]
        have hlt : ‖(x : ι → 𝕜) j‖ < δ := by
          by_contra hcon
          push Not at hcon
          have hmem : j ∈ hfin.toFinset := hfin.mem_toFinset.mpr (not_lt.mpr hcon)
          exact hj (hs hmem)
        exact hlt.le
    calc ‖Φ (c0Trunc (𝕜 := 𝕜) (ι := ι) s x - x)‖
        ≤ ‖Φ‖ * ‖c0Trunc (𝕜 := 𝕜) (ι := ι) s x - x‖ := Φ.le_opNorm _
      _ ≤ ‖Φ‖ * δ := mul_le_mul_of_nonneg_left hnorm (norm_nonneg Φ)
      _ < ε := by
          have hne : (‖Φ‖ + 1) ≠ 0 := by positivity
          rw [hδdef]
          calc ‖Φ‖ * (ε / (‖Φ‖ + 1))
              < (‖Φ‖ + 1) * (ε / (‖Φ‖ + 1)) :=
                mul_lt_mul_of_pos_right (lt_add_one _) (div_pos hε (by positivity))
            _ = (ε / (‖Φ‖ + 1)) * (‖Φ‖ + 1) := mul_comm _ _
            _ = ε := div_mul_cancel₀ ε hne
  exact (summable_c0Pairing (c0CoeffLp Φ) x).hasSum.unique hsum

/-- The pairing is norm-preserving. -/
theorem c0DualPairing_norm (a : lp (fun _ : ι => 𝕜) 1) :
    ‖c0DualPairing (𝕜 := 𝕜) (ι := ι) a‖ = ‖a‖ := by
  classical
  apply le_antisymm (norm_c0DualPairing_le a)
  have hba : c0CoeffLp (𝕜 := 𝕜) (ι := ι) (c0DualPairing (𝕜 := 𝕜) (ι := ι) a) = a := by
    apply Subtype.ext
    funext i
    show c0DualPairing (𝕜 := 𝕜) (ι := ι) a (c0Single i (1 : 𝕜)) = a i
    rw [c0DualPairing_apply, tsum_eq_single i]
    · simp [c0Single_apply]
    · intro j hj
      show a j * ((c0Single (𝕜 := 𝕜) (ι := ι) i (1 : 𝕜) : c0 𝕜 ι) : ι → 𝕜) j = 0
      rw [c0Single_apply, ite_eq_right hj, mul_zero]
  have hbnorm := norm_c0CoeffLp_le (c0DualPairing (𝕜 := 𝕜) (ι := ι) a)
  rw [hba] at hbnorm
  exact hbnorm

/-- The dual of `c₀` is isometrically isomorphic to `ℓ¹`. -/
noncomputable def c0DualEquiv : lp (fun _ : ι => 𝕜) 1 ≃ₗᵢ[𝕜] StrongDual 𝕜 (c0 𝕜 ι) := by
  classical
  exact LinearIsometryEquiv.ofSurjective
    ⟨(c0DualPairing (𝕜 := 𝕜) (ι := ι)).toLinearMap, fun a => c0DualPairing_norm a⟩
    c0DualPairing_surjective

end Surjectivity

section Eval

variable {𝕜 : Type u} [RCLike 𝕜] {ι : Type v} [DecidableEq ι]

/-- Evaluation at `i`, as a continuous linear functional on `c₀`. -/
noncomputable def c0Eval (i : ι) : StrongDual 𝕜 (c0 𝕜 ι) :=
  (LinearMap.mkContinuous
    { toFun := fun x : c0 𝕜 ι => (x : ι → 𝕜) i
      map_add' := fun x y => by simp
      map_smul' := fun c x => by simp }
    1 fun x => by
      calc ‖(x : ι → 𝕜) i‖ ≤ ‖x‖ := c0_apply_norm_le x i
        _ = 1 * ‖x‖ := (one_mul _).symm)

/-- Evaluation at `i` is given by pairing with `lp.single 1 i 1`. -/
theorem c0DualPairing_single_eq_eval (i : ι) :
    c0DualPairing (𝕜 := 𝕜) (ι := ι) (lp.single (E := fun _ : ι => 𝕜) 1 i (1 : 𝕜))
      = c0Eval (𝕜 := 𝕜) (ι := ι) i := by
  apply ContinuousLinearMap.ext fun x => ?_
  rw [c0DualPairing_apply]
  show ∑' j, (lp.single (E := fun _ : ι => 𝕜) 1 i (1 : 𝕜)) j * (x : ι → 𝕜) j
      = (x : ι → 𝕜) i
  rw [tsum_eq_single i]
  · simp
  · intro j hj
    show (lp.single (E := fun _ : ι => 𝕜) 1 i (1 : 𝕜)) j * (x : ι → 𝕜) j = 0
    rw [lp.single_apply_ne (E := fun _ : ι => 𝕜) 1 i (1 : 𝕜) hj, zero_mul]

end Eval

end MathlibExt.Analysis.Normed.Lp.DualC0
