/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Economics.Producer.CobbDouglasCost
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import MathlibExt.Analysis.Convex.KarushKuhnTucker

/-!
# Interior first-order conditions for producers

We work on the open positive orthant of a finite input space. A partial derivative is the
Fréchet derivative applied to the corresponding coordinate basis vector. The cost argument
uses KKT for a single binding output constraint: positivity of input prices rules out a
zero multiplier. For profit, stationarity is sufficient under concavity but not in general.
-/

open Set Filter
open scoped BigOperators Topology

namespace MathlibExt.Economics.Producer

universe u

local notation "∂[" f ", " x ", " i "]" => fderiv ℝ f x (Pi.basisFun ℝ _ i)

private lemma orthant_mem_nhds {ι : Type*} [Finite ι] {x : ι → ℝ}
    (hx : ∀ i, 0 < x i) : {y | ∀ i, 0 < y i} ∈ 𝓝 x := by
  have hopen : IsOpen (⋂ i : ι, {y : ι → ℝ | 0 < y i}) :=
    isOpen_iInter_of_finite fun i ↦ isOpen_lt continuous_const (continuous_apply i)
  have heq : {y : ι → ℝ | ∀ i, 0 < y i} = ⋂ i : ι, {y | 0 < y i} := by
    ext y
    simp
  rw [heq]
  exact hopen.mem_nhds (by simpa only [mem_iInter, mem_ofPred_eq] using hx)

variable {ι : Type*} [Fintype ι] {f : (ι → ℝ) → ℝ} {x w : ι → ℝ} {p q : ℝ}

private noncomputable def costLinear (w : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  (dotProductBilin ℝ ℝ w).toContinuousLinearMap

private lemma costLinear_apply (w y : ι → ℝ) : costLinear w y = w ⬝ᵥ y := rfl

private lemma costLinear_basis (w : ι → ℝ) (i : ι) :
    costLinear w (Pi.basisFun ℝ ι i) = w i := by
  classical
  rw [costLinear_apply, Pi.basisFun_apply, dotProduct_single_one]

private lemma hasFDerivAt_profit (hf : DifferentiableAt ℝ f x) :
    HasFDerivAt (fun y ↦ p * f y - w ⬝ᵥ y) (p • fderiv ℝ f x - costLinear w) x :=
  (hf.hasFDerivAt.const_mul p).sub (costLinear w).hasFDerivAt

private theorem interior_profit_max_first_order
    (hx : ∀ i, 0 < x i) (hf : DifferentiableAt ℝ f x)
    (hmax : IsMaxOn (fun y ↦ p * f y - w ⬝ᵥ y) {y | ∀ i, 0 < y i} x) :
    ∀ i, p * ∂[f, x, i] = w i := by
  have hz := (hmax.isLocalMax (orthant_mem_nhds hx)).hasFDerivAt_eq_zero
    (hasFDerivAt_profit hf)
  intro i
  have hi := congrArg (fun d : (ι → ℝ) →L[ℝ] ℝ ↦ d (Pi.basisFun ℝ ι i)) hz
  exact sub_eq_zero.mp (by simpa [costLinear_basis] using hi)

private theorem interior_cost_min_first_order [Nonempty ι]
    (hx : ∀ i, 0 < x i) (hf : DifferentiableAt ℝ f x) (hw : ∀ i, 0 < w i)
    (hbind : f x = q) (hregular : fderiv ℝ f x ≠ 0)
    (hmin : IsMinOn (fun y ↦ w ⬝ᵥ y) {y | (∀ i, 0 < y i) ∧ q ≤ f y} x) :
    ∃ μ : ℝ, 0 < μ ∧ (∀ i, w i = μ * ∂[f, x, i]) ∧
      (∀ j, 0 < ∂[f, x, j]) ∧ ∀ i j, ∂[f, x, i] / ∂[f, x, j] = w i / w j := by
  let g : Fin 1 → (ι → ℝ) → ℝ := fun _ y ↦ q - f y
  have hactive (i : Fin 1) : g i x = 0 := sub_eq_zero.mpr hbind.symm
  have hg (i : Fin 1) : HasFDerivAt (g i) (-fderiv ℝ f x) x := hf.hasFDerivAt.const_sub q
  have hmin' : IsLocalMinOn (fun y ↦ w ⬝ᵥ y) {y | ∀ i, g i y ≤ 0} x := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (orthant_mem_nhds hx), self_mem_nhdsWithin]
      with y hy hgy
    exact hmin ⟨hy, sub_nonpos.mp (hgy 0)⟩
  let : Unique {i : Fin 1 // g i x = 0} :=
    ⟨⟨0, hactive 0⟩, fun i ↦ Subtype.ext (Subsingleton.elim _ _)⟩
  have hlicq : LinearIndependent ℝ
      (fun i : {i : Fin 1 // g i x = 0} ↦ fderiv ℝ (g i.val) x) := by
    rw [linearIndependent_unique_iff]
    exact (hg (default : {i : Fin 1 // g i x = 0}).val).fderiv ▸ neg_ne_zero.mpr hregular
  have hcost : HasFDerivAt (fun y ↦ w ⬝ᵥ y) (costLinear w) x :=
    (costLinear w).hasFDerivAt
  obtain ⟨lam, hlam, -, hstat⟩ :=
    MathlibExt.Analysis.Convex.KarushKuhnTucker.karush_kuhn_tucker_inequality
      hcost.differentiableAt (fun i ↦ (hg i).differentiableAt)
      (fun i ↦ (hactive i).le) hmin' hlicq
  have hs : costLinear w + lam 0 • (-fderiv ℝ f x) = 0 := by
    simpa only [hcost.fderiv, Fin.sum_univ_one, (hg 0).fderiv] using hstat
  have hcoord (i : ι) : w i = lam 0 * ∂[f, x, i] := by
    have hi := congrArg (fun d : (ι → ℝ) →L[ℝ] ℝ ↦ d (Pi.basisFun ℝ ι i)) hs
    simpa [costLinear_basis, mul_neg, ← sub_eq_add_neg, sub_eq_zero] using hi
  have hpos : 0 < lam 0 := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    by_contra! h
    have hzero := le_antisymm h (hlam 0)
    have hi := hw i
    rw [hcoord i, hzero, zero_mul] at hi
    exact (lt_irrefl _ hi)
  have hpartial (j : ι) : 0 < ∂[f, x, j] := by
    have h := hw j
    rw [hcoord j] at h
    exact pos_of_mul_pos_right h hpos.le
  refine ⟨lam 0, hpos, hcoord, hpartial, fun i j ↦ ?_⟩
  rw [hcoord i, hcoord j, mul_div_mul_left _ _ hpos.ne']

private lemma concaveOn_profit (hp : 0 ≤ p) (hconc : ConcaveOn ℝ {y | ∀ i, 0 < y i} f) :
    ConcaveOn ℝ {y | ∀ i, 0 < y i} (fun y ↦ p * f y - w ⬝ᵥ y) := by
  have hcost : ConvexOn ℝ {y | ∀ i, 0 < y i} (costLinear w) :=
    (costLinear w).toLinearMap.convexOn hconc.1
  exact (hconc.smul hp).sub hcost

private theorem interior_profit_stationary_is_max_of_concave
    (hx : ∀ i, 0 < x i) (hf : DifferentiableAt ℝ f x)
    (hprofit : ConcaveOn ℝ {y | ∀ i, 0 < y i} (fun y ↦ p * f y - w ⬝ᵥ y))
    (hcoord : ∀ i, p * ∂[f, x, i] = w i) :
    IsMaxOn (fun y ↦ p * f y - w ⬝ᵥ y) {y | ∀ i, 0 < y i} x := by
  let d := p • fderiv ℝ f x - costLinear w
  have hd : d = 0 := by
    apply LinearMap.toContinuousLinearMap.symm.injective
    apply (Pi.basisFun ℝ ι).ext
    intro i
    simpa [d, costLinear_basis] using sub_eq_zero.mpr (hcoord i)
  intro y hy
  have hderiv : HasFDerivAt (fun y ↦ p * f y - w ⬝ᵥ y) d x := hasFDerivAt_profit hf
  have ht := hprofit.neg.add_fderiv_sub_le hx hy hderiv.differentiableAt.neg
  change p * f y - w ⬝ᵥ y ≤ p * f x - w ⬝ᵥ x
  simpa only [hderiv.neg.fderiv, hd, neg_zero, zero_apply, add_zero, Pi.neg_apply,
    neg_le_neg_iff] using ht

-- The spare exponent is assigned to the constant coordinate 1. Weighted AM–GM then
-- bounds the ratio by an affine function of the input bundle.
private lemma cobbDouglas_div_le {a x y : ι → ℝ} (ha : ∀ i, 0 < a i)
    (hsum : ∑ i, a i < 1) (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
    cobbDouglas 1 a y / cobbDouglas 1 a x ≤
      (1 - ∑ i, a i) + ∑ i, a i * (y i / x i) := by
  let w : Option ι → ℝ := fun i ↦ i.elim (1 - ∑ j, a j) a
  let z : Option ι → ℝ := fun i ↦ i.elim 1 (fun j ↦ y j / x j)
  have hw : ∀ i : Option ι, 0 ≤ w i := by
    intro i
    cases i with
    | none => exact sub_nonneg.mpr hsum.le
    | some i => exact (ha i).le
  have hz : ∀ i : Option ι, 0 ≤ z i := by
    intro i
    cases i with
    | none => exact zero_le_one
    | some i => exact div_nonneg (hy i).le (hx i).le
  have hwSum : ∑ i, w i = 1 := by simp [w, Fintype.sum_option]
  have h := Real.geom_mean_le_arith_mean_weighted Finset.univ w z
    (fun i _ ↦ hw i) hwSum (fun i _ ↦ hz i)
  have hfrac (i : ι) : (y i / x i) ^ a i = y i ^ a i / x i ^ a i :=
    Real.div_rpow (hy i).le (hx i).le (a i)
  change (1 * ∏ i, y i ^ a i) / (1 * ∏ i, x i ^ a i) ≤ _
  simpa only [Fintype.prod_option, Fintype.sum_option, w, z, Option.elim_none,
    Option.elim_some, Real.one_rpow, mul_one, one_mul, hfrac, Finset.prod_div_distrib] using h

private lemma concaveOn_cobbDouglas {a : ι → ℝ} (ha : ∀ i, 0 < a i)
    (hsum : ∑ i, a i < 1) : ConcaveOn ℝ {y | ∀ i, 0 < y i} (cobbDouglas 1 a) := by
  have hpos : Convex ℝ {y : ι → ℝ | ∀ i, 0 < y i} := by
    rw [show {y : ι → ℝ | ∀ i, 0 < y i} = ⋂ i : ι, {y | 0 < y i} from by ext; simp]
    refine convex_iInter fun i ↦ ?_
    change Convex ℝ ((LinearMap.proj i : (ι → ℝ) →ₗ[ℝ] ℝ) ⁻¹' Ioi 0)
    exact (convex_Ioi (0 : ℝ)).linear_preimage (LinearMap.proj i : (ι → ℝ) →ₗ[ℝ] ℝ)
  refine ⟨hpos, ?_⟩
  intro x hx y hy s t hs ht hst
  let z := s • x + t • y
  have hz : ∀ i, 0 < z i := hpos hx hy hs ht hst
  have hGz : 0 < cobbDouglas 1 a z := by
    change 0 < 1 * ∏ i, z i ^ a i
    simpa only [one_mul] using
      Finset.prod_pos (s := Finset.univ) (fun i _ ↦ Real.rpow_pos_of_pos (hz i) (a i))
  have hx' := cobbDouglas_div_le ha hsum hz hx
  have hy' := cobbDouglas_div_le ha hsum hz hy
  have h := add_le_add (mul_le_mul_of_nonneg_left hx' hs) (mul_le_mul_of_nonneg_left hy' ht)
  have hmix :
      s * ((1 - ∑ i, a i) + ∑ i, a i * (x i / z i)) +
        t * ((1 - ∑ i, a i) + ∑ i, a i * (y i / z i)) = 1 := calc
    _ = (s + t) * (1 - ∑ i, a i) +
        ∑ i, a i * ((s * x i + t * y i) / z i) := by
      rw [mul_add, mul_add, ← add_add_add_comm, ← add_mul]
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [add_div]
      ring
    _ = 1 := by
      rw [hst, one_mul]
      have hself (i : ι) : (s * x i + t * y i) / z i = 1 := div_self (hz i).ne'
      simp [hself]
  rw [hmix, ← mul_div_assoc, ← mul_div_assoc, ← add_div, div_le_iff₀ hGz, one_mul] at h
  exact h

private theorem quadratic_profit_example :
    HasDerivAt (fun t : ℝ ↦ t ^ 2) 1 (1 / 2) ∧
    IsMinOn (fun t : ℝ ↦ t ^ 2 - t) (Ioi 0) (1 / 2) ∧
    ¬ IsMaxOn (fun t : ℝ ↦ t ^ 2 - t) (Ioi 0) (1 / 2) ∧
    ¬ BddAbove ((fun t : ℝ ↦ t ^ 2 - t) '' Ioi 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using (hasDerivAt_id (1 / 2 : ℝ)).fun_pow 2
  · intro y _
    dsimp
    nlinarith [sq_nonneg (y - 1 / 2)]
  · intro hmax
    have h := hmax (show (1 : ℝ) ∈ Ioi 0 by norm_num)
    norm_num at h
  · rintro ⟨b, hb⟩
    let y := max b 0 + 2
    have hy : 0 < y := by dsimp [y]; positivity
    have hbig : b + 2 ≤ y := add_le_add_left (le_max_left b 0) _
    have hy2 : 2 ≤ y := by dsimp [y]; linarith [le_max_right b 0]
    have h := hb ⟨y, hy, rfl⟩
    dsimp at h
    nlinarith [mul_nonneg hy.le (show 0 ≤ y - 2 by linarith)]

/-- Interior first-order conditions for profit maximization and cost minimization.

At a positive input bundle where production is differentiable, profit maximization implies
that output price times each marginal product equals that input's price. At a binding cost
minimum with nonzero production derivative and positive input prices, the output multiplier
and all marginal products are positive, and marginal-product ratios equal input-price ratios.
Concave production at a nonnegative output price makes profit stationarity sufficient. In
contrast, with quadratic production and unit prices, the stationary bundle `1 / 2` minimizes
profit on the positive half-line, is not a maximizer, and profit is unbounded above. The
Cobb–Douglas technology with positive exponents summing to less than one is concave on
the positive orthant.

Source: A. Mas-Colell, M. D. Whinston and J. R. Green, *Microeconomic Theory*, Oxford University
Press, 1995, Section 5.C (profit maximization and cost minimization). -/
public theorem interior_first_order_conditions :
    (∀ {ι : Type u} [Fintype ι] {f : (ι → ℝ) → ℝ} {x w : ι → ℝ} {p : ℝ},
      (∀ i, 0 < x i) → DifferentiableAt ℝ f x →
      IsMaxOn (fun y ↦ p * f y - w ⬝ᵥ y) {y | ∀ i, 0 < y i} x →
      ∀ i, p * ∂[f, x, i] = w i) ∧
    (∀ {ι : Type u} [Fintype ι] [Nonempty ι] {f : (ι → ℝ) → ℝ} {x w : ι → ℝ} {q : ℝ},
      (∀ i, 0 < x i) → DifferentiableAt ℝ f x → (∀ i, 0 < w i) → f x = q →
      fderiv ℝ f x ≠ 0 → IsMinOn (fun y ↦ w ⬝ᵥ y) {y | (∀ i, 0 < y i) ∧ q ≤ f y} x →
      ∃ μ : ℝ, 0 < μ ∧ (∀ i, w i = μ * ∂[f, x, i]) ∧
        (∀ j, 0 < ∂[f, x, j]) ∧ ∀ i j, ∂[f, x, i] / ∂[f, x, j] = w i / w j) ∧
    (∀ {ι : Type u} [Fintype ι] {f : (ι → ℝ) → ℝ} {x w : ι → ℝ} {p : ℝ},
      (∀ i, 0 < x i) → DifferentiableAt ℝ f x →
      (ConcaveOn ℝ {y | ∀ i, 0 < y i} (fun y ↦ p * f y - w ⬝ᵥ y) →
        (∀ i, p * ∂[f, x, i] = w i) →
        IsMaxOn (fun y ↦ p * f y - w ⬝ᵥ y) {y | ∀ i, 0 < y i} x) ∧
      (0 ≤ p → ConcaveOn ℝ {y | ∀ i, 0 < y i} f →
        ConcaveOn ℝ {y | ∀ i, 0 < y i} (fun y ↦ p * f y - w ⬝ᵥ y))) ∧
    (HasDerivAt (fun t : ℝ ↦ t ^ 2) 1 (1 / 2) ∧
      IsMinOn (fun t : ℝ ↦ t ^ 2 - t) (Ioi 0) (1 / 2) ∧
      ¬ IsMaxOn (fun t : ℝ ↦ t ^ 2 - t) (Ioi 0) (1 / 2) ∧
      ¬ BddAbove ((fun t : ℝ ↦ t ^ 2 - t) '' Ioi 0)) ∧
    (∀ {ι : Type u} [Fintype ι] {a : ι → ℝ}, (∀ i, 0 < a i) → (∑ i, a i) < 1 →
      ConcaveOn ℝ {y | ∀ i, 0 < y i} (cobbDouglas 1 a)) :=
  ⟨fun hx hf ↦ interior_profit_max_first_order hx hf,
    fun hx hf ↦ interior_cost_min_first_order hx hf,
    fun hx hf ↦ ⟨interior_profit_stationary_is_max_of_concave hx hf, concaveOn_profit⟩,
    quadratic_profit_example, fun ha hsum ↦ concaveOn_cobbDouglas ha hsum⟩

end MathlibExt.Economics.Producer
