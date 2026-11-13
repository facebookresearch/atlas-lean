/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Convex.ConstrainedOptimization

/-!
# Tests for convexity, constrained optimization and stability

* Existence: the compact-set statement in the form `∃ x ∈ K, ∀ y ∈ K, f x ≤ f y`, the simplex
  instance on `Fin 3`, and `∑ i, x i ^ 2` on `simplex 3` with minimum `1 / 3` at the centre only.
* No-minimum countermodels: `y ↦ y` on `(0, 1)` (compactness dropped) and a jump on `[0, 1]`
  (continuity dropped). The alternative `1 / y` on `(0, 1]` attains its minimum at `1` (it has no
  maximizer), so it is not a countermodel for minima.
* Uniqueness versus stationarity: `x ^ 3` is stationary at `0`, which is neither a minimizer nor a
  maximizer, not even locally; the double well `(x ^ 2 - 1) ^ 2` has the two global minimizers
  `±1`, so it is neither strictly convex nor convex, although its second derivative at `1` is
  `8 > 0`.
* KKT: necessity by ATLAS's `karush_kuhn_tucker_inequality` for `(y - 2) ^ 2` subject to
  `y - 1 ≤ 0` (the multiplier is forced to be `2`); sufficiency with an equality constraint and a
  negative multiplier, on `ℝ` and on `Fin 2 → ℝ`; and the constraint-qualification countermodel
  read through the necessity theorem.
* Jensen with real weights, for two points, and for `x ↦ x ^ 2` at three points, and the gradient
  form of the supporting plane on `ℝ`.
* The binary mixing models: the binary simplex is `[0, 1]`, the equilibria and energies, and the
  supporting plane at the equilibrium.
-/

@[expose] public section

open scoped Topology
open MathlibExt.Analysis.Convex.ConstrainedOptimization
  MathlibExt.Analysis.Convex.KarushKuhnTucker

namespace MathlibExtTest.Analysis.Convex.ConstrainedOptimization

/-! ### Existence on compact sets -/

/-- Existence of a minimizer on a nonempty compact set (MF11.1), in the form
`∃ x ∈ K, ∀ y ∈ K, f x ≤ f y`; this is Mathlib's `IsCompact.exists_isMinOn`. -/
example {E : Type*} [TopologicalSpace E] {K : Set E} {f : E → ℝ} (hK : IsCompact K)
    (hne : K.Nonempty) (hf : ContinuousOn f K) : ∃ x ∈ K, ∀ y ∈ K, f x ≤ f y := by
  obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hne hf
  exact ⟨x, hx, isMinOn_iff.1 hmin⟩

/-- The first coordinate attains its minimum on `simplex 3` (MF11.1a). -/
example : ∃ x ∈ simplex 3, IsMinOn (fun x : Fin 3 → ℝ => x 0) (simplex 3) x :=
  exists_isMinOn_simplex (by norm_num) (continuous_apply 0).continuousOn

/-- The centre of `simplex 3` is `(1 / 3, 1 / 3, 1 / 3)`. -/
example : simplexCenter 3 = fun _ => 1 / 3 := by
  funext i
  simp [simplexCenter]

/-- On `simplex 3`, `∑ i, x i ^ 2` attains its minimum `1 / 3` at the centre (MF11.1b). -/
example : IsMinOn (fun x : Fin 3 → ℝ => ∑ i, x i ^ 2) (simplex 3) (simplexCenter 3) ∧
    ∑ i, simplexCenter 3 i ^ 2 = 1 / 3 :=
  ⟨isMinOn_sum_sq_simplex (by norm_num), by rw [sum_sq_simplexCenter (by norm_num)]; norm_num⟩

/-- The centre is the only minimizer of `∑ i, x i ^ 2` on `simplex 3`. -/
example : ∃! x, x ∈ simplex 3 ∧ IsMinOn (fun x : Fin 3 → ℝ => ∑ i, x i ^ 2) (simplex 3) x :=
  ⟨simplexCenter 3,
    ⟨simplexCenter_mem_simplex (by norm_num), isMinOn_sum_sq_simplex (by norm_num)⟩,
    fun _ hy => eq_simplexCenter_of_isMinOn_sum_sq (by norm_num) hy.1 hy.2⟩

/-- The vertex `(1, 0, 0)` of `simplex 3` is not a minimizer of `∑ i, x i ^ 2`. -/
example : ¬ IsMinOn (fun x : Fin 3 → ℝ => ∑ i, x i ^ 2) (simplex 3) ![1, 0, 0] := by
  intro h
  have hmem : (![1, 0, 0] : Fin 3 → ℝ) ∈ simplex 3 :=
    mem_simplex.2 ⟨fun i => by fin_cases i <;> simp, by simp [Fin.sum_univ_three]⟩
  have h1 := congrFun (eq_simplexCenter_of_isMinOn_sum_sq (by norm_num) hmem h) 1
  simp [simplexCenter] at h1

/-! ### No-minimum countermodels -/

/-- Compactness cannot be dropped: `y ↦ y` has no minimizer on the bounded, non-closed interval
`(0, 1)` (MF11.1, no-minimum countermodel). -/
example : ¬ ∃ x ∈ Set.Ioo (0 : ℝ) 1, IsMinOn (fun y : ℝ => y) (Set.Ioo 0 1) x := by
  rintro ⟨x, ⟨hx0, hx1⟩, hmin⟩
  have h : x ≤ x / 2 := isMinOn_iff.1 hmin (x / 2) ⟨by linarith, by linarith⟩
  linarith

/-- Continuity cannot be dropped: the function equal to `1` at `0` and to `y` elsewhere has no
minimizer on the compact interval `[0, 1]`. -/
example : ¬ ∃ x ∈ Set.Icc (0 : ℝ) 1,
    IsMinOn (fun y : ℝ => if y = 0 then 1 else y) (Set.Icc 0 1) x := by
  rintro ⟨x, ⟨hx0, hx1⟩, hmin⟩
  rcases eq_or_lt_of_le hx0 with rfl | hxpos
  · have h := isMinOn_iff.1 hmin (1 / 2) ⟨by norm_num, by norm_num⟩
    norm_num at h
  · have h := isMinOn_iff.1 hmin (x / 2) ⟨by linarith, by linarith⟩
    simp only [hxpos.ne', (half_pos hxpos).ne', ite_false] at h
    linarith

/-- `1 / y` on `(0, 1]` is not a countermodel for minima: it attains its minimum at `1`. -/
example : IsMinOn (fun y : ℝ => 1 / y) (Set.Ioc 0 1) 1 :=
  isMinOn_iff.2 fun _ hy => one_div_le_one_div_of_le hy.1 hy.2

/-- `1 / y` has no maximizer on `(0, 1]`. -/
example : ¬ ∃ x ∈ Set.Ioc (0 : ℝ) 1, IsMaxOn (fun y : ℝ => 1 / y) (Set.Ioc 0 1) x := by
  rintro ⟨x, ⟨hx0, hx1⟩, hmax⟩
  have h : 1 / (x / 2) ≤ 1 / x := isMaxOn_iff.1 hmax (x / 2) ⟨by linarith, by linarith⟩
  have h2 : 1 / x < 1 / (x / 2) := one_div_lt_one_div_of_lt (by linarith) (by linarith)
  linarith

/-! ### Uniqueness comes from strict convexity, not from stationarity -/

/-- At most one minimizer under strict convexity (MF11.2): Mathlib's
`StrictConvexOn.eq_of_isMinOn`. -/
example {E : Type*} [AddCommGroup E] [Module ℝ E] {K : Set E} {f : E → ℝ}
    (hf : StrictConvexOn ℝ K f) {x y : E} (hx : x ∈ K) (hy : y ∈ K) (hmx : IsMinOn f K x)
    (hmy : IsMinOn f K y) : x = y :=
  hf.eq_of_isMinOn hmx hmy hx hy

/-- `x ^ 3` is stationary at `0` (MF11.2a). -/
example : deriv (fun x : ℝ => x ^ 3) 0 = 0 := by
  rw [(hasDerivAt_pow 3 (0 : ℝ)).deriv]
  norm_num

/-- Yet `0` is neither a minimizer nor a maximizer of `x ^ 3` on `ℝ` (MF11.2a). -/
example : ¬ IsMinOn (fun x : ℝ => x ^ 3) Set.univ 0 ∧
    ¬ IsMaxOn (fun x : ℝ => x ^ 3) Set.univ 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h1 : (0 : ℝ) ^ 3 ≤ (-1) ^ 3 := isMinOn_iff.1 h (-1) (Set.mem_univ _)
    norm_num at h1
  · have h1 : (1 : ℝ) ^ 3 ≤ 0 ^ 3 := isMaxOn_iff.1 h 1 (Set.mem_univ _)
    norm_num at h1

/-- Not even a local minimum or a local maximum. -/
example : ¬ IsLocalMin (fun x : ℝ => x ^ 3) 0 ∧ ¬ IsLocalMax (fun x : ℝ => x ^ 3) 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h1 : ∀ᶠ y in 𝓝[<] (0 : ℝ), (0 : ℝ) ^ 3 ≤ y ^ 3 := h.filter_mono nhdsWithin_le_nhds
    obtain ⟨y, hy, hneg⟩ := (h1.and self_mem_nhdsWithin).exists
    have h2 : y ^ 3 < 0 := Odd.pow_neg ⟨1, by norm_num⟩ hneg
    norm_num at hy
    linarith
  · have h1 : ∀ᶠ y in 𝓝[>] (0 : ℝ), y ^ 3 ≤ (0 : ℝ) ^ 3 := h.filter_mono nhdsWithin_le_nhds
    obtain ⟨y, hy, hpos⟩ := (h1.and self_mem_nhdsWithin).exists
    have h2 : 0 < y ^ 3 := pow_pos hpos 3
    norm_num at hy
    linarith

/-- `x ↦ x ^ 2` is convex on `ℝ`. -/
private lemma convexOn_sq : ConvexOn ℝ Set.univ fun x : ℝ => x ^ 2 :=
  ⟨convex_univ, fun x _ y _ a b ha hb hab => by
    obtain rfl : b = 1 - a := by linarith
    simp only [smul_eq_mul]
    nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x - y))]⟩

/-- The double well `(x ^ 2 - 1) ^ 2`, a nonconvex model energy with two wells. -/
def doubleWell (x : ℝ) : ℝ :=
  (x ^ 2 - 1) ^ 2

/-- `1` is a global minimizer of the double well. -/
private lemma isMinOn_doubleWell_one : IsMinOn doubleWell Set.univ 1 :=
  isMinOn_iff.2 fun y _ => by
    simp only [doubleWell]
    nlinarith [sq_nonneg (y ^ 2 - 1)]

/-- `-1` is a global minimizer of the double well. -/
private lemma isMinOn_doubleWell_neg_one : IsMinOn doubleWell Set.univ (-1) :=
  isMinOn_iff.2 fun y _ => by
    simp only [doubleWell]
    nlinarith [sq_nonneg (y ^ 2 - 1)]

/-- Nonconvexity breaks uniqueness: the double well has the two distinct global minimizers `1`
and `-1` (MF11.2b). -/
example : IsMinOn doubleWell Set.univ 1 ∧ IsMinOn doubleWell Set.univ (-1) ∧ (1 : ℝ) ≠ -1 :=
  ⟨isMinOn_doubleWell_one, isMinOn_doubleWell_neg_one, by norm_num⟩

/-- Hence the double well is not strictly convex on `ℝ`, by `StrictConvexOn.eq_of_isMinOn`. -/
example : ¬ StrictConvexOn ℝ Set.univ doubleWell := fun h => by
  have h1 := h.eq_of_isMinOn isMinOn_doubleWell_one isMinOn_doubleWell_neg_one
    (Set.mem_univ _) (Set.mem_univ _)
  norm_num at h1

/-- Nor convex: its value `1` at the midpoint `0` of `-1` and `1` exceeds the average `0`. -/
example : ¬ ConvexOn ℝ Set.univ doubleWell := fun h => by
  have h1 := h.2 (Set.mem_univ (1 : ℝ)) (Set.mem_univ (-1 : ℝ)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [doubleWell, smul_eq_mul] at h1
  norm_num at h1

/-- The double well is stationary at `0`, where it has a maximum on `[-1, 1]`, and `0` is not a
minimizer. -/
example : deriv doubleWell 0 = 0 ∧ IsMaxOn doubleWell (Set.Icc (-1) 1) 0 ∧
    ¬ IsMinOn doubleWell Set.univ 0 := by
  refine ⟨?_, isMaxOn_iff.2 fun y hy => ?_, fun h => ?_⟩
  · change deriv (fun x : ℝ => (x ^ 2 - 1) ^ 2) 0 = 0
    rw [(((hasDerivAt_pow 2 (0 : ℝ)).sub_const 1).fun_pow 2).deriv]
    norm_num
  · have h1 : 0 ≤ 1 - y ^ 2 := by nlinarith [hy.1, hy.2]
    simp only [doubleWell]
    nlinarith [mul_nonneg (sq_nonneg y) h1]
  · have h1 : doubleWell 0 ≤ doubleWell 1 := isMinOn_iff.1 h 1 (Set.mem_univ _)
    norm_num [doubleWell] at h1

/-- Local positivity of the second derivative is not global convexity: the second derivative of
the double well at its minimizer `1` is `8 > 0`, yet it is not convex on `ℝ`. -/
example : deriv (deriv doubleWell) 1 = 8 := by
  have h1 : deriv doubleWell = fun x => 4 * x ^ 3 - 4 * x := by
    funext x
    change deriv (fun x : ℝ => (x ^ 2 - 1) ^ 2) x = _
    rw [(((hasDerivAt_pow 2 x).sub_const 1).fun_pow 2).deriv]
    push_cast
    ring
  have h2 : HasDerivAt (fun x : ℝ => 4 * x ^ 3 - 4 * x) 8 1 := by
    convert ((hasDerivAt_pow 3 (1 : ℝ)).const_mul 4).fun_sub ((hasDerivAt_id' (1 : ℝ)).const_mul 4)
      using 1
    norm_num
  rw [h1, h2.deriv]

/-! ### KKT: necessity by reuse, sufficiency, and the constraint qualification -/

/-- KKT necessity, reused (MF11.3b): minimize `(y - 2) ^ 2` subject to `y - 1 ≤ 0`. The
constraint is active at the minimizer `1` with nonzero gradient, so LICQ holds and ATLAS's
`karush_kuhn_tucker_inequality` gives a multiplier with nonnegativity, complementary slackness
and stationarity. -/
example : ∃ lam : Fin 1 → ℝ, (∀ i, 0 ≤ lam i) ∧
    (∀ i, lam i * (fun (_ : Fin 1) (y : ℝ) => y - 1) i 1 = 0) ∧
    fderiv ℝ (fun y : ℝ => (y - 2) ^ 2) 1 +
      ∑ i, lam i • fderiv ℝ ((fun (_ : Fin 1) (y : ℝ) => y - 1) i) 1 = 0 := by
  refine karush_kuhn_tucker_inequality (f := fun y : ℝ => (y - 2) ^ 2)
    (g := fun (_ : Fin 1) (y : ℝ) => y - 1) (x := 1) (by fun_prop) (fun _ => by fun_prop)
    (fun _ => by norm_num) (IsMinOn.isLocalMinOn (isMinOn_iff.2 fun y hy => ?_)) ?_
  · have hy1 : y - 1 ≤ 0 := hy 0
    change ((1 : ℝ) - 2) ^ 2 ≤ (y - 2) ^ 2
    nlinarith
  · rw [linearIndependent_subsingleton_index_iff]
    intro i
    change fderiv ℝ (fun y : ℝ => y - 1) 1 ≠ 0
    rw [fderiv_sub_const, fderiv_fun_id]
    intro h
    simpa using congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) h

/-- The multiplier of the necessity example is forced to be `2`: stationarity at `1` reads
`-2 + lam 0 = 0`. -/
example (lam : Fin 1 → ℝ) (h : fderiv ℝ (fun y : ℝ => (y - 2) ^ 2) 1 +
    ∑ i, lam i • fderiv ℝ ((fun (_ : Fin 1) (y : ℝ) => y - 1) i) 1 = 0) : lam 0 = 2 := by
  have hf : HasDerivAt (fun y : ℝ => (y - 2) ^ 2) (-2) 1 := by
    convert ((hasDerivAt_id' (1 : ℝ)).sub_const 2).fun_pow 2 using 1
    norm_num
  have hg : fderiv ℝ (fun y : ℝ => y - 1) 1 = ContinuousLinearMap.id ℝ ℝ := by
    rw [fderiv_sub_const, fderiv_fun_id]
  have h1 := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) h
  simp only [Fin.sum_univ_one, hf.hasFDerivAt.fderiv, hg] at h1
  simp at h1
  linarith

/-- KKT sufficiency with an affine equality constraint (MF11.3a): minimize `y ^ 2` subject to
`-y ≤ 0` and `y - 1 = 0` on `ℝ`. At `1` the inequality is inactive (`lam = 0`) and the
negative equality multiplier `mu = -2` gives stationarity `2 - 2 = 0`; `1` is feasible, so it is a
global minimizer on the feasible set. -/
example : (1 : ℝ) ∈ {y : ℝ | (∀ i : Fin 1, (fun (_ : Fin 1) (z : ℝ) => -z) i y ≤ 0) ∧
      ∀ j : Fin 1, (fun (_ : Fin 1) (z : ℝ) => z - 1) j y = 0} ∧
    IsMinOn (fun y : ℝ => y ^ 2)
      {y | (∀ i : Fin 1, (fun (_ : Fin 1) (z : ℝ) => -z) i y ≤ 0) ∧
        ∀ j : Fin 1, (fun (_ : Fin 1) (z : ℝ) => z - 1) j y = 0} 1 := by
  refine ⟨⟨fun _ => by norm_num, fun _ => by norm_num⟩, ?_⟩
  have hconv : ConvexOn ℝ Set.univ fun z : ℝ => -z :=
    ⟨convex_univ, fun x _ y _ a b _ _ _ => le_of_eq (by simp only [smul_eq_mul]; ring)⟩
  have hconv' : ConvexOn ℝ Set.univ fun z : ℝ => z - 1 :=
    ⟨convex_univ, fun x _ y _ a b _ _ hab => le_of_eq (by
      simp only [smul_eq_mul]
      linear_combination hab)⟩
  have hconc' : ConcaveOn ℝ Set.univ fun z : ℝ => z - 1 :=
    ⟨convex_univ, fun x _ y _ a b _ _ hab => le_of_eq (by
      simp only [smul_eq_mul]
      linear_combination (-1 : ℝ) * hab)⟩
  have hf : fderiv ℝ (fun y : ℝ => y ^ 2) 1 = ContinuousLinearMap.toSpanSingleton ℝ 2 := by
    simpa using (hasDerivAt_pow 2 (1 : ℝ)).hasFDerivAt.fderiv
  have hh : fderiv ℝ (fun z : ℝ => z - 1) 1 = ContinuousLinearMap.id ℝ ℝ := by
    rw [fderiv_sub_const, fderiv_fun_id]
  refine isMinOn_of_karush_kuhn_tucker_convex_affine (f := fun y : ℝ => y ^ 2)
    (g := fun _ z => -z) (h := fun _ z => z - 1) (x := 1) (lam := fun _ => 0) (mu := fun _ => -2)
    convexOn_sq (fun _ => hconv) (fun _ => hconv') (fun _ => hconc') (by fun_prop)
    (fun _ => by fun_prop) (fun _ => by fun_prop) (fun _ => by norm_num)
    (fun _ => le_rfl) (fun _ => zero_mul _) ?_
  simp only [Fin.sum_univ_one, hf, hh, zero_smul, add_zero]
  ext
  simp

/-- The functional `y ↦ y 0 + y 1` on `Fin 2 → ℝ`. -/
noncomputable def sumCoords : (Fin 2 → ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ) + ContinuousLinearMap.proj 1

/-- KKT sufficiency on `Fin 2 → ℝ` with the simplex constraints `-y i ≤ 0` and
`y 0 + y 1 - 1 = 0` (MF11.3a): the vertex `(0, 1)` minimizes `2 y 0 + y 1`, certified by
`lam = (1, 0)` and the negative equality multiplier `mu = -1`; the vertex is feasible, so it is a
global minimizer on the feasible set. -/
example : ![0, 1] ∈ {y : Fin 2 → ℝ | (∀ i : Fin 2, -y i ≤ 0) ∧ ∀ _ : Fin 1, sumCoords y + -1 = 0} ∧
    IsMinOn (fun y : Fin 2 → ℝ => 2 * y 0 + y 1)
      {y | (∀ i : Fin 2, -y i ≤ 0) ∧ ∀ _ : Fin 1, sumCoords y + -1 = 0} ![0, 1] := by
  refine ⟨⟨fun i => by fin_cases i <;> simp, fun _ => by simp [sumCoords]⟩, ?_⟩
  have hfL : (fun y : Fin 2 → ℝ => 2 * y 0 + y 1) =
      ⇑((2 : ℝ) • ContinuousLinearMap.proj 0 + ContinuousLinearMap.proj 1 :
        (Fin 2 → ℝ) →L[ℝ] ℝ) := by
    funext y
    simp
  have hgL : ∀ i : Fin 2, (fun y : Fin 2 → ℝ => -y i) =
      ⇑(-ContinuousLinearMap.proj i : (Fin 2 → ℝ) →L[ℝ] ℝ) := fun i => by
    funext y
    simp
  refine isMinOn_of_karush_kuhn_tucker_convex_linear_eq (f := fun y : Fin 2 → ℝ => 2 * y 0 + y 1)
    (g := fun i y => -y i) (ℓ := fun _ => sumCoords) (c := fun _ => -1) (x := ![0, 1])
    (lam := ![1, 0]) (mu := fun _ => -1)
    ⟨convex_univ, fun x _ y _ a b _ _ _ => le_of_eq (by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring)⟩
    (fun i => ⟨convex_univ, fun x _ y _ a b _ _ _ => le_of_eq (by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring)⟩)
    (by rw [hfL]; exact ContinuousLinearMap.differentiableAt _)
    (fun i => by rw [hgL i]; exact ContinuousLinearMap.differentiableAt _)
    (fun _ => by simp [sumCoords])
    (fun i => by fin_cases i <;> simp) (fun i => by fin_cases i <;> simp) ?_
  simp only [hfL, hgL, ContinuousLinearMap.fderiv, Fin.sum_univ_two, Fin.sum_univ_one]
  ext y
  simp [sumCoords]
  ring

/-- The constraint-qualification countermodel through ATLAS's necessity theorem (MF11.3c): `0` is
feasible and a minimizer, the data are differentiable, and the KKT conclusion fails
(`not_exists_kkt_multipliers_cq`), so `karush_kuhn_tucker_inequality` forces LICQ to fail, in
agreement with `not_linearIndependent_cq`. -/
example : ¬ LinearIndependent ℝ
    (fun i : {i : Fin 1 // cqConstraint i 0 = 0} => fderiv ℝ (cqConstraint i.val) 0) :=
  fun hLICQ => not_exists_kkt_multipliers_cq <|
    karush_kuhn_tucker_inequality (f := cqObjective) (g := cqConstraint) (x := 0)
      differentiableAt_id
      (fun _ => by change DifferentiableAt ℝ (fun y : ℝ => y ^ 2) 0; fun_prop)
      (fun _ => by change (0 : ℝ) ^ 2 ≤ 0; norm_num) isMinOn_cqObjective.isLocalMinOn hLICQ

/-- The countermodel's feasible set and minimizer (MF11.3c). -/
example : {y : ℝ | ∀ i, cqConstraint i y ≤ 0} = {0} ∧
    IsMinOn cqObjective {y : ℝ | ∀ i, cqConstraint i y ≤ 0} 0 :=
  ⟨cqFeasibleSet_eq, isMinOn_cqObjective⟩

/-! ### Jensen and supporting planes -/

/-- Jensen's inequality with real weights on a finite type,
`f (∑ i, w i • x i) ≤ ∑ i, w i * f (x i)` (MF11.4a): Mathlib's `ConvexOn.map_sum_le`. -/
example {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E] {s : Set E} {f : E → ℝ}
    (hf : ConvexOn ℝ s f) {w : ι → ℝ} {x : ι → E} (h0 : ∀ i, 0 ≤ w i) (h1 : ∑ i, w i = 1)
    (hx : ∀ i, x i ∈ s) : f (∑ i, w i • x i) ≤ ∑ i, w i * f (x i) := by
  simpa only [smul_eq_mul] using hf.map_sum_le (fun i _ => h0 i) h1 fun i _ => hx i

/-- The two-point instance of Jensen's inequality, `f (a • x + b • y) ≤ a * f x + b * f y`. -/
example {E : Type*} [AddCommGroup E] [Module ℝ E] {s : Set E} {f : E → ℝ} (hf : ConvexOn ℝ s f)
    {x y : E} {a b : ℝ} (hx : x ∈ s) (hy : y ∈ s) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    f (a • x + b • y) ≤ a * f x + b * f y := by
  have h := hf.map_sum_le (t := Finset.univ) (w := ![a, b]) (p := ![x, y])
    (fun i _ => by fin_cases i <;> simpa) (by simpa [Fin.sum_univ_two] using hab)
    (fun i _ => by fin_cases i <;> simpa)
  simpa [Fin.sum_univ_two] using h

/-- Jensen for `x ↦ x ^ 2` with uniform weights on three points: the square of the mean is at
most the mean of the squares. -/
example (a b c : ℝ) : ((a + b + c) / 3) ^ 2 ≤ (a ^ 2 + b ^ 2 + c ^ 2) / 3 := by
  have h := convexOn_sq.map_sum_le (t := Finset.univ) (w := fun _ : Fin 3 => (1 : ℝ) / 3)
    (p := ![a, b, c]) (fun _ _ => by norm_num) (by simp) (fun _ _ => Set.mem_univ _)
  simp only [Fin.sum_univ_three, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at h
  linarith

/-- The gradient form of the supporting plane on `ℝ` (MF11.4b), for `x ↦ x ^ 2` at `1`:
`1 + 2 (y - 1) ≤ y ^ 2`. -/
example (y : ℝ) : 1 + 2 * (y - 1) ≤ y ^ 2 := by
  have h := add_inner_gradient_sub_le (f := fun x : ℝ => x ^ 2) (x := 1) (y := y)
    convexOn_sq (Set.mem_univ _) (Set.mem_univ _) (by fun_prop)
  have hg : gradient (fun x : ℝ => x ^ 2) 1 = 2 := by
    rw [gradient_eq_deriv]
    simp
  rw [hg, RCLike.inner_apply] at h
  simp only [one_pow, map_ofNat] at h
  linarith

/-! ### Binary mixing models -/

/-- The binary simplex is the composition interval: `(x, 1 - x) ∈ simplex 2 ↔ x ∈ [0, 1]`. -/
example (x : ℝ) : ![x, 1 - x] ∈ simplex 2 ↔ x ∈ Set.Icc (0 : ℝ) 1 := by
  simp only [mem_simplex, Fin.forall_fin_two, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Set.mem_Icc, sub_nonneg, add_sub_cancel, and_true]

/-- On the binary simplex, `∑ i, x i ^ 2 = 2 E (x) + 1 / 2` for the quadratic mixing energy `E`,
so both are minimized at the same composition. -/
example (x : ℝ) : ∑ i, (![x, 1 - x] : Fin 2 → ℝ) i ^ 2 = 2 * quadraticMixingEnergy x + 1 / 2 := by
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, quadraticMixingEnergy]
  ring

/-- The quadratic model has exactly one constrained minimizer (MF11.4c). -/
example : ∃! x, x ∈ Set.Icc (0 : ℝ) 1 ∧ IsMinOn quadraticMixingEnergy (Set.Icc 0 1) x :=
  existsUnique_isMinOn_quadraticMixingEnergy

/-- The equilibrium composition `1 / 2` has energy `0`; the pure components have energy
`1 / 4`. -/
example : quadraticMixingEnergy (1 / 2) = 0 ∧ quadraticMixingEnergy 0 = 1 / 4 ∧
    quadraticMixingEnergy 1 = 1 / 4 :=
  ⟨quadraticMixingEnergy_half, by norm_num [quadraticMixingEnergy],
    by norm_num [quadraticMixingEnergy]⟩

/-- A pure component is not an equilibrium of the quadratic model. -/
example : ¬ IsMinOn quadraticMixingEnergy (Set.Icc 0 1) 0 := fun h => by
  have h1 := (isMinOn_quadraticMixingEnergy_iff ⟨le_rfl, zero_le_one⟩).1 h
  norm_num at h1

/-- At the equilibrium the supporting plane is horizontal, so the supporting-plane inequality
reads `E (1 / 2) ≤ E y` on `[0, 1]`. -/
example {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    quadraticMixingEnergy (1 / 2) ≤ quadraticMixingEnergy y := by
  have h := quadraticMixingEnergy_add_fderiv_le hy
  simp only [fderiv_quadraticMixingEnergy_half, zero_apply, add_zero] at h
  exact h

/-- The ideal mixing model has exactly one constrained minimizer (MF11.4c). -/
example : ∃! x, x ∈ Set.Icc (0 : ℝ) 1 ∧ IsMinOn idealMixingEnergy (Set.Icc 0 1) x :=
  existsUnique_isMinOn_idealMixingEnergy

/-- The pure components have ideal mixing energy `0`, and the equilibrium `1 / 2` has energy
`-log 2 < 0`. -/
example : idealMixingEnergy 0 = 0 ∧ idealMixingEnergy 1 = 0 ∧
    idealMixingEnergy (1 / 2) = -Real.log 2 ∧ -Real.log 2 < 0 :=
  ⟨by simp [idealMixingEnergy], by simp [idealMixingEnergy], idealMixingEnergy_half,
    neg_neg_of_pos (Real.log_pos (by norm_num))⟩

/-- A pure component is not an equilibrium of the ideal model. -/
example : ¬ IsMinOn idealMixingEnergy (Set.Icc 0 1) 1 := fun h => by
  have h1 := (isMinOn_idealMixingEnergy_iff ⟨zero_le_one, le_rfl⟩).1 h
  norm_num at h1

/-- The supporting plane of the ideal model at the equilibrium is horizontal. -/
example {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    idealMixingEnergy (1 / 2) ≤ idealMixingEnergy y := by
  have h := idealMixingEnergy_add_fderiv_le hy
  simp only [fderiv_idealMixingEnergy_half, zero_apply, add_zero] at h
  exact h

end MathlibExtTest.Analysis.Convex.ConstrainedOptimization
