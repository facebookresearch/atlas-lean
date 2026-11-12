/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import MathlibExt.Analysis.Convex.KarushKuhnTucker
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv

/-!
# Convexity, constrained optimization and stability

Minimizers on compact sets, uniqueness from strict convexity, convex KKT sufficiency with affine
equality constraints, a constraint-qualification countermodel, the supporting-plane inequality in
gradient form, and two binary mixing energies with a unique constrained minimizer.

## i. Overview

*Existence.* A continuous function on a nonempty compact set attains its minimum (Weierstrass);
this is Mathlib's `IsCompact.exists_isMinOn`, reused here. The standard simplex
`simplex n = {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}` is compact and convex, so every
function continuous on it attains its minimum (`exists_isMinOn_simplex`), and `∑ i, x i ^ 2` is
minimized on it exactly at the centre `(n⁻¹, …, n⁻¹)`, with value `n⁻¹`.

*Uniqueness.* A strictly convex function has at most one minimizer on its domain, which is convex
because `StrictConvexOn ℝ K f` contains `Convex ℝ K`; this is Mathlib's
`StrictConvexOn.eq_of_isMinOn`, reused here. Together with existence, a continuous
strictly convex function on a nonempty compact convex set has exactly one minimizer
(`existsUnique_isMinOn_of_strictConvexOn`). Uniqueness comes from strict convexity, never from
stationarity: a vanishing derivative alone gives neither minimality nor uniqueness.

*Necessity versus sufficiency of the KKT conditions.* For the problem of minimizing `f` subject to
`g i y ≤ 0` and `h j y = 0` these are two different statements.
- Necessity (KKT at a local minimizer, *given a constraint qualification*): ATLAS's
  `MathlibExt.Analysis.Convex.KarushKuhnTucker.karush_kuhn_tucker_inequality` proves that at a
  local minimizer satisfying LICQ there are multipliers `lam i ≥ 0` with complementary slackness
  and stationarity. It is reused, not restated. Without a constraint qualification necessity
  fails: minimizing `y` subject to `y ^ 2 ≤ 0` has feasible set `{0}` and minimizer `0`, but no
  multipliers exist (`not_exists_kkt_multipliers_cq`), because the constraint gradient vanishes
  there and LICQ fails (`not_linearIndependent_cq`).
- Sufficiency (KKT *plus convexity* gives a global minimizer, with no constraint
  qualification): `isMinOn_of_karush_kuhn_tucker_convex_affine` treats convex differentiable
  inequality constraints and affine equality constraints, the latter with multipliers `mu j` of
  either sign; `isMinOn_of_karush_kuhn_tucker_convex_linear_eq` is the case `ℓ j y + c j = 0`.
  It extends ATLAS's inequality-only
  `MathlibExt.Analysis.Convex.KarushKuhnTucker.isMinOn_of_karush_kuhn_tucker_convex`. Sufficiency
  does not assert that minimizers carry multipliers.

*Supporting planes and convex combinations.* Jensen's inequality is Mathlib's
`ConvexOn.map_sum_le`, and the first-order inequality `f x + f' x (y - x) ≤ f y` is ATLAS's
`ConvexOn.add_fderiv_sub_le`; both are reused. `add_inner_gradient_sub_le` restates the latter
with the gradient, `f x + ⟪∇f x, y - x⟫ ≤ f y`, in a real Hilbert space.

*Binary mixing and stability.* On the composition interval `[0, 1]` (the binary simplex
`x ↦ (x, 1 - x)`), the quadratic model energy `(x - 1 / 2) ^ 2` and the ideal mixing energy
`x log x + (1 - x) log (1 - x)` are strictly convex, so each has exactly one constrained
minimizer, the equilibrium composition `1 / 2`, and its supporting plane there is horizontal.
These energies are model inputs, not claims about a real mixture. Strict convexity is a global
hypothesis: local positivity of the second derivative does not give it, and a nonconvex double
well has two minimizers (coexistence); the countermodels are in the test file.

## ii. Key results

- `isCompact_simplex`, `exists_isMinOn_simplex` : existence on the standard simplex.
- `isMinOn_sum_sq_simplex`, `eq_simplexCenter_of_isMinOn_sum_sq` : `∑ i, x i ^ 2` is minimized
  exactly at the centre, with value `n⁻¹` (`sum_sq_simplexCenter`).
- `existsUnique_isMinOn_of_strictConvexOn` : existence and uniqueness of the minimizer.
- `isMinOn_of_karush_kuhn_tucker_convex_affine`, `isMinOn_of_karush_kuhn_tucker_convex_linear_eq` :
  convex KKT sufficiency with affine equality constraints.
- `cqFeasibleSet_eq`, `isMinOn_cqObjective`, `not_exists_kkt_multipliers_cq`,
  `not_linearIndependent_cq` : the constraint-qualification countermodel.
- `add_inner_gradient_sub_le` : the supporting-plane inequality in gradient form.
- `existsUnique_isMinOn_quadraticMixingEnergy`, `isMinOn_quadraticMixingEnergy_iff`,
  `quadraticMixingEnergy_add_fderiv_le` and their `idealMixingEnergy` counterparts : the binary
  mixing models.

## iii. Table of contents

- A. Existence of minima on the standard simplex
- B. Uniqueness from strict convexity
- C. Convex KKT sufficiency with affine equality constraints
- D. A constraint-qualification countermodel
- E. The supporting-plane inequality in gradient form
- F. Binary mixing: a quadratic model energy
- G. Binary mixing: the ideal mixing energy

## iv. References

- S. Boyd and L. Vandenberghe, *Convex Optimization* (2004): §3.1.3 (first-order condition),
  §3.1.8 (Jensen's inequality), §5.5.3 (KKT optimality conditions).
- W. Karush, *Minima of Functions of Several Variables with Inequalities as Side Conditions*
  (M.Sc. thesis, Univ. Chicago, 1939); H. W. Kuhn and A. W. Tucker, *Nonlinear Programming*,
  Proc. Second Berkeley Symposium (1951), 481–492.
- ATLAS MF11 planning anchor R11 (Mathlib and MathlibExt substrate) and
  `MathlibExt/Analysis/Convex/KarushKuhnTucker.lean`.
-/

@[expose] public section

namespace MathlibExt.Analysis.Convex.ConstrainedOptimization

/-! ## A. Existence of minima on the standard simplex -/

/-- The standard simplex `{x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}` of weights on `n`
points (MF11.1). Mathlib's `stdSimplex` is deprecated, so the set is written out. -/
def simplex (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}

/-- The centre `(n⁻¹, …, n⁻¹)` of `simplex n`, the uniform weight. -/
noncomputable def simplexCenter (n : ℕ) : Fin n → ℝ :=
  fun _ => (n : ℝ)⁻¹

/-- Membership in `simplex n`. -/
lemma mem_simplex {n : ℕ} {x : Fin n → ℝ} :
    x ∈ simplex n ↔ (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1 :=
  Iff.rfl

/-- `simplex n` is closed. -/
lemma isClosed_simplex (n : ℕ) : IsClosed (simplex n) := by
  have h : simplex n = Set.Ici 0 ∩ {x | ∑ i, x i = 1} := rfl
  rw [h]
  exact isClosed_Ici.inter (isClosed_eq (by fun_prop) continuous_const)

/-- `simplex n` lies in the unit cube `[0, 1] ^ n`. -/
lemma simplex_subset_Icc (n : ℕ) : simplex n ⊆ Set.Icc 0 1 := fun _ hx =>
  ⟨fun i => hx.1 i, fun i =>
    (Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)).trans_eq hx.2⟩

/-- `simplex n` is compact, as a closed subset of the unit cube. -/
lemma isCompact_simplex (n : ℕ) : IsCompact (simplex n) :=
  isCompact_Icc.of_isClosed_subset (isClosed_simplex n) (simplex_subset_Icc n)

/-- `simplex n` is convex. -/
lemma convex_simplex (n : ℕ) : Convex ℝ (simplex n) := by
  intro x hx y hy a b ha hb hab
  refine mem_simplex.2 ⟨fun i => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hx.2, hy.2, mul_one, hab]

/-- For `n ≠ 0` the centre lies in `simplex n`, which is therefore nonempty. -/
lemma simplexCenter_mem_simplex {n : ℕ} (hn : n ≠ 0) : simplexCenter n ∈ simplex n := by
  refine mem_simplex.2 ⟨fun _ => inv_nonneg.2 (Nat.cast_nonneg n), ?_⟩
  simp only [simplexCenter, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn)

/-- Every function continuous on the standard simplex attains its minimum there (MF11.1); this
is `IsCompact.exists_isMinOn` for the compact set `simplex n`. -/
lemma exists_isMinOn_simplex {n : ℕ} (hn : n ≠ 0) {f : (Fin n → ℝ) → ℝ}
    (hf : ContinuousOn f (simplex n)) : ∃ x ∈ simplex n, IsMinOn f (simplex n) x :=
  (isCompact_simplex n).exists_isMinOn ⟨_, simplexCenter_mem_simplex hn⟩ hf

/-- On the hyperplane `∑ i, x i = 1`, the squared distance to the centre of the simplex is
`∑ i, x i ^ 2 - n⁻¹`. -/
lemma sum_sq_sub_simplexCenter {n : ℕ} (hn : n ≠ 0) {x : Fin n → ℝ} (hx : ∑ i, x i = 1) :
    ∑ i, (x i - simplexCenter n i) ^ 2 = ∑ i, x i ^ 2 - (n : ℝ)⁻¹ := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have h : ∀ i, (x i - simplexCenter n i) ^ 2 =
      x i ^ 2 + (-2 * (n : ℝ)⁻¹) * x i + ((n : ℝ)⁻¹) ^ 2 := fun i => by
    simp only [simplexCenter]
    ring
  simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum, hx, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- The value of `∑ i, x i ^ 2` at the centre of `simplex n` is `n⁻¹`. -/
lemma sum_sq_simplexCenter {n : ℕ} (hn : n ≠ 0) :
    ∑ i, simplexCenter n i ^ 2 = (n : ℝ)⁻¹ := by
  simp only [simplexCenter, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- A concrete minimizer on the simplex (MF11.1): `∑ i, x i ^ 2` attains its minimum `n⁻¹` on
`simplex n` at the centre. -/
lemma isMinOn_sum_sq_simplex {n : ℕ} (hn : n ≠ 0) :
    IsMinOn (fun x : Fin n → ℝ => ∑ i, x i ^ 2) (simplex n) (simplexCenter n) := by
  refine isMinOn_iff.2 fun x hx => ?_
  have h := sum_sq_sub_simplexCenter hn hx.2
  have h0 : 0 ≤ ∑ i, (x i - simplexCenter n i) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [sum_sq_simplexCenter hn]
  linarith

/-- The centre is the only minimizer of `∑ i, x i ^ 2` on `simplex n`. -/
lemma eq_simplexCenter_of_isMinOn_sum_sq {n : ℕ} (hn : n ≠ 0) {x : Fin n → ℝ}
    (hx : x ∈ simplex n) (hmin : IsMinOn (fun x : Fin n → ℝ => ∑ i, x i ^ 2) (simplex n) x) :
    x = simplexCenter n := by
  have h1 : ∑ i, x i ^ 2 ≤ ∑ i, simplexCenter n i ^ 2 :=
    isMinOn_iff.1 hmin _ (simplexCenter_mem_simplex hn)
  rw [sum_sq_simplexCenter hn] at h1
  have h2 := sum_sq_sub_simplexCenter hn hx.2
  have h3 : ∑ i, (x i - simplexCenter n i) ^ 2 = 0 :=
    le_antisymm (by linarith) (Finset.sum_nonneg fun i _ => sq_nonneg _)
  rw [Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg _] at h3
  funext i
  exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (h3 i (Finset.mem_univ i)))

/-! ## B. Uniqueness from strict convexity -/

/-- Existence and uniqueness of the minimizer (MF11.2): a function that is continuous and
strictly convex on a nonempty compact set `K` has exactly one minimizer on `K`. Convexity of `K`
is part of `StrictConvexOn`. Existence is `IsCompact.exists_isMinOn` and uniqueness is
`StrictConvexOn.eq_of_isMinOn`. -/
lemma existsUnique_isMinOn_of_strictConvexOn {E : Type*} [TopologicalSpace E] [AddCommGroup E]
    [Module ℝ E] {K : Set E} {f : E → ℝ} (hK : IsCompact K) (hne : K.Nonempty)
    (hcont : ContinuousOn f K) (hf : StrictConvexOn ℝ K f) :
    ∃! x, x ∈ K ∧ IsMinOn f K x := by
  obtain ⟨x, hxK, hx⟩ := hK.exists_isMinOn hne hcont
  exact ⟨x, ⟨hxK, hx⟩, fun y hy => hf.eq_of_isMinOn hy.2 hx hy.1 hxK⟩

/-! ## C. Convex KKT sufficiency with affine equality constraints -/

/-- Convex KKT sufficiency with affine equality constraints (MF11.3a). Minimize `f` subject to
`g i y ≤ 0` and `h j y = 0`, where `f` and every `g i` are convex on the whole space, every `h j`
is affine (convex and concave on the whole space), and all of them are differentiable at `x`.
If `x` satisfies the equality constraints and `lam i ≥ 0` and `mu j` (of either sign) satisfy
complementary slackness `lam i * g i x = 0` and stationarity
`fderiv ℝ f x + ∑ i, lam i • fderiv ℝ (g i) x + ∑ j, mu j • fderiv ℝ (h j) x = 0`, then
`f x ≤ f y` for every feasible `y`; so a feasible `x` is a global minimizer of `f` on the feasible
set. The inequality constraints need not hold at `x` for this bound. No constraint qualification
is needed. The mechanism is the first-order inequality `ConvexOn.add_fderiv_sub_le`; without
equality constraints (`p = 0`) this is the bound of ATLAS's
`MathlibExt.Analysis.Convex.KarushKuhnTucker.isMinOn_of_karush_kuhn_tucker_convex`.
Source: S. Boyd and L. Vandenberghe, *Convex Optimization* (2004), §5.5.3. -/
theorem isMinOn_of_karush_kuhn_tucker_convex_affine {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {m p : ℕ} {f : E → ℝ} {g : Fin m → E → ℝ} {h : Fin p → E → ℝ} {x : E}
    {lam : Fin m → ℝ} {mu : Fin p → ℝ}
    (hf_conv : ConvexOn ℝ Set.univ f) (hg_conv : ∀ i, ConvexOn ℝ Set.univ (g i))
    (hh_conv : ∀ j, ConvexOn ℝ Set.univ (h j)) (hh_conc : ∀ j, ConcaveOn ℝ Set.univ (h j))
    (hf_diff : DifferentiableAt ℝ f x) (hg_diff : ∀ i, DifferentiableAt ℝ (g i) x)
    (hh_diff : ∀ j, DifferentiableAt ℝ (h j) x) (hx : ∀ j, h j x = 0)
    (hlam : ∀ i, 0 ≤ lam i) (hcs : ∀ i, lam i * g i x = 0)
    (hstat : fderiv ℝ f x + ∑ i, lam i • fderiv ℝ (g i) x + ∑ j, mu j • fderiv ℝ (h j) x = 0) :
    IsMinOn f {y | (∀ i, g i y ≤ 0) ∧ ∀ j, h j y = 0} x := by
  refine isMinOn_iff.2 fun y hy => ?_
  have hf_le := hf_conv.add_fderiv_sub_le (Set.mem_univ x) (Set.mem_univ y) hf_diff
  have hg_le : ∀ i, lam i * fderiv ℝ (g i) x (y - x) ≤ 0 := fun i => by
    have h1 := (hg_conv i).add_fderiv_sub_le (Set.mem_univ x) (Set.mem_univ y) (hg_diff i)
    have h2 := mul_le_mul_of_nonneg_left h1 (hlam i)
    have h3 := mul_nonpos_of_nonneg_of_nonpos (hlam i) (hy.1 i)
    rw [mul_add, hcs i, zero_add] at h2
    exact h2.trans h3
  have hh_eq : ∀ j, fderiv ℝ (h j) x (y - x) = 0 := fun j => by
    have h1 := (hh_conv j).add_fderiv_sub_le (Set.mem_univ x) (Set.mem_univ y) (hh_diff j)
    have h2 := (hh_conc j).neg.add_fderiv_sub_le (Set.mem_univ x) (Set.mem_univ y)
      (hh_diff j).neg
    rw [fderiv_neg] at h2
    simp only [Pi.neg_apply, neg_apply, hx j, hy.2 j] at h1 h2
    linarith
  have hstat_v : fderiv ℝ f x (y - x) + ∑ i, lam i * fderiv ℝ (g i) x (y - x) +
      ∑ j, mu j * fderiv ℝ (h j) x (y - x) = 0 := by
    simpa only [add_apply, sum_apply, smul_apply, smul_eq_mul, zero_apply] using
      congrArg (fun L : E →L[ℝ] ℝ => L (y - x)) hstat
  have hsum_g : ∑ i, lam i * fderiv ℝ (g i) x (y - x) ≤ 0 :=
    Finset.sum_nonpos fun i _ => hg_le i
  have hsum_h : ∑ j, mu j * fderiv ℝ (h j) x (y - x) = 0 :=
    Finset.sum_eq_zero fun j _ => by rw [hh_eq j, mul_zero]
  linarith

/-- Convex KKT sufficiency with the affine equality constraints written as `ℓ j y + c j = 0` for
continuous linear functionals `ℓ j` (MF11.3a). This is
`isMinOn_of_karush_kuhn_tucker_convex_affine` for `h j y = ℓ j y + c j`, whose derivative is
`ℓ j`, so stationarity reads
`fderiv ℝ f x + ∑ i, lam i • fderiv ℝ (g i) x + ∑ j, mu j • ℓ j = 0`. -/
lemma isMinOn_of_karush_kuhn_tucker_convex_linear_eq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {m p : ℕ} {f : E → ℝ} {g : Fin m → E → ℝ} {ℓ : Fin p → E →L[ℝ] ℝ}
    {c : Fin p → ℝ} {x : E} {lam : Fin m → ℝ} {mu : Fin p → ℝ}
    (hf_conv : ConvexOn ℝ Set.univ f) (hg_conv : ∀ i, ConvexOn ℝ Set.univ (g i))
    (hf_diff : DifferentiableAt ℝ f x) (hg_diff : ∀ i, DifferentiableAt ℝ (g i) x)
    (hx : ∀ j, ℓ j x + c j = 0)
    (hlam : ∀ i, 0 ≤ lam i) (hcs : ∀ i, lam i * g i x = 0)
    (hstat : fderiv ℝ f x + ∑ i, lam i • fderiv ℝ (g i) x + ∑ j, mu j • ℓ j = 0) :
    IsMinOn f {y | (∀ i, g i y ≤ 0) ∧ ∀ j, ℓ j y + c j = 0} x := by
  have hfd : ∀ j, fderiv ℝ (fun y => ℓ j y + c j) x = ℓ j := fun j => by
    rw [fderiv_add_const, ContinuousLinearMap.fderiv]
  refine isMinOn_of_karush_kuhn_tucker_convex_affine (h := fun j y => ℓ j y + c j) (mu := mu)
    hf_conv hg_conv (fun j => ((ℓ j).toLinearMap.convexOn convex_univ).add_const (c j))
    (fun j => ((ℓ j).toLinearMap.concaveOn convex_univ).add_const (c j)) hf_diff hg_diff
    (fun j => (ℓ j).differentiableAt.add_const (c j)) hx hlam hcs ?_
  simpa only [hfd] using hstat

/-! ## D. A constraint-qualification countermodel -/

/-- Objective `y ↦ y` of the constraint-qualification countermodel on `ℝ` (MF11.3c). -/
def cqObjective : ℝ → ℝ :=
  fun y => y

/-- The single constraint `y ↦ y ^ 2` of the countermodel, indexed by `Fin 1` as in
`MathlibExt.Analysis.Convex.KarushKuhnTucker.karush_kuhn_tucker_inequality`; the problem is to
minimize `cqObjective` subject to `y ^ 2 ≤ 0`. -/
def cqConstraint : Fin 1 → ℝ → ℝ :=
  fun _ y => y ^ 2

/-- The feasible set of the countermodel is `{0}`. -/
lemma cqFeasibleSet_eq : {y : ℝ | ∀ i, cqConstraint i y ≤ 0} = {0} := by
  ext y
  refine ⟨fun hy => ?_, fun hy i => ?_⟩
  · have h0 : y ^ 2 ≤ 0 := hy 0
    exact Set.mem_singleton_iff.2 (pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h0 (sq_nonneg y)))
  · rw [Set.mem_singleton_iff.1 hy]
    change (0 : ℝ) ^ 2 ≤ 0
    norm_num

/-- `0` minimizes the countermodel objective on its feasible set. -/
lemma isMinOn_cqObjective : IsMinOn cqObjective {y : ℝ | ∀ i, cqConstraint i y ≤ 0} 0 := by
  rw [cqFeasibleSet_eq]
  exact isMinOn_iff.2 fun y hy => (Set.mem_singleton_iff.1 hy) ▸ le_rfl

/-- The objective gradient at the minimizer is the identity, which is nonzero. -/
lemma fderiv_cqObjective : fderiv ℝ cqObjective 0 = ContinuousLinearMap.id ℝ ℝ :=
  fderiv_fun_id

/-- The constraint gradient vanishes at the minimizer. -/
lemma fderiv_cqConstraint (i : Fin 1) : fderiv ℝ (cqConstraint i) 0 = 0 := by
  have h : HasDerivAt (fun y : ℝ => y ^ 2) 0 0 := by
    simpa using hasDerivAt_pow 2 (0 : ℝ)
  change fderiv ℝ (fun y : ℝ => y ^ 2) 0 = 0
  simpa using h.hasFDerivAt.fderiv

/-- No multipliers of any sign make the Lagrangian of the countermodel stationary at its
minimizer `0`: the constraint gradient is `0` and the objective gradient is not. -/
lemma not_exists_stationary_multiplier_cq :
    ¬ ∃ lam : Fin 1 → ℝ, fderiv ℝ cqObjective 0 + ∑ i, lam i • fderiv ℝ (cqConstraint i) 0 = 0 := by
  rintro ⟨lam, hlam⟩
  simp only [fderiv_cqObjective, fderiv_cqConstraint, smul_zero, Finset.sum_const_zero,
    add_zero] at hlam
  simpa using congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) hlam

/-- The KKT conditions fail at the minimizer of the countermodel (MF11.3c): the conclusion of
`MathlibExt.Analysis.Convex.KarushKuhnTucker.karush_kuhn_tucker_inequality` is false although `0`
is a (global, hence local) minimizer. KKT necessity needs a constraint qualification. -/
lemma not_exists_kkt_multipliers_cq :
    ¬ ∃ lam : Fin 1 → ℝ, (∀ i, 0 ≤ lam i) ∧ (∀ i, lam i * cqConstraint i 0 = 0) ∧
      fderiv ℝ cqObjective 0 + ∑ i, lam i • fderiv ℝ (cqConstraint i) 0 = 0 :=
  fun ⟨lam, _, _, hstat⟩ => not_exists_stationary_multiplier_cq ⟨lam, hstat⟩

/-- LICQ fails at the minimizer of the countermodel: the only constraint is active and its
gradient is `0`. -/
lemma not_linearIndependent_cq :
    ¬ LinearIndependent ℝ
      (fun i : {i : Fin 1 // cqConstraint i 0 = 0} => fderiv ℝ (cqConstraint i.val) 0) := by
  intro hli
  have hact : cqConstraint 0 0 = 0 := by simp [cqConstraint]
  exact hli.ne_zero ⟨0, hact⟩ (fderiv_cqConstraint 0)

/-! ## E. The supporting-plane inequality in gradient form -/

/-- The supporting-plane inequality with the gradient (MF11.4b): in a real Hilbert space, if `f`
is convex on `s`, `x ∈ s`, `y ∈ s`, and `f` is differentiable at `x`, then
`f x + ⟪∇f x, y - x⟫ ≤ f y`. This is ATLAS's `ConvexOn.add_fderiv_sub_le`, since
`⟪∇f x, v⟫ = fderiv ℝ f x v`. -/
lemma add_inner_gradient_sub_le {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] {s : Set F} {f : F → ℝ} {x y : F} (hf : ConvexOn ℝ s f) (hx : x ∈ s)
    (hy : y ∈ s) (hf_diff : DifferentiableAt ℝ f x) :
    f x + inner ℝ (gradient f x) (y - x) ≤ f y := by
  rw [gradient, InnerProductSpace.toDual_symm_apply]
  exact hf.add_fderiv_sub_le hx hy hf_diff

/-! ## F. Binary mixing: a quadratic model energy -/

/-- The quadratic model mixing energy `(x - 1 / 2) ^ 2` of a binary mixture with composition
`x ∈ [0, 1]`, a point `(x, 1 - x)` of the binary simplex (MF11.4c). A model input, not a claim
about a real mixture. -/
noncomputable def quadraticMixingEnergy (x : ℝ) : ℝ :=
  (x - 1 / 2) ^ 2

/-- The derivative of the quadratic mixing energy is `2 (x - 1 / 2)`. -/
lemma hasDerivAt_quadraticMixingEnergy (x : ℝ) :
    HasDerivAt quadraticMixingEnergy (2 * (x - 1 / 2)) x := by
  change HasDerivAt (fun y : ℝ => (y - 1 / 2) ^ 2) _ x
  simpa using ((hasDerivAt_id' x).sub_const (1 / 2 : ℝ)).fun_pow 2

/-- The quadratic mixing energy is strictly convex on `[0, 1]`, from Mathlib's
`Even.strictConvexOn_pow` for `x ^ 2` and a translation. -/
lemma strictConvexOn_quadraticMixingEnergy :
    StrictConvexOn ℝ (Set.Icc 0 1) quadraticMixingEnergy := by
  have h := (Even.strictConvexOn_pow even_two two_ne_zero).translate_right (-(1 / 2) : ℝ)
  have heq : ((fun x : ℝ => x ^ 2) ∘ fun z => -(1 / 2) + z) = quadraticMixingEnergy := by
    funext z
    simp only [Function.comp, quadraticMixingEnergy]
    ring
  rw [heq, Set.preimage_univ] at h
  exact h.subset (Set.subset_univ _) (convex_Icc 0 1)

/-- The quadratic mixing energy has exactly one minimizer on `[0, 1]` (MF11.4c), by
`existsUnique_isMinOn_of_strictConvexOn`. -/
lemma existsUnique_isMinOn_quadraticMixingEnergy :
    ∃! x, x ∈ Set.Icc (0 : ℝ) 1 ∧ IsMinOn quadraticMixingEnergy (Set.Icc 0 1) x :=
  existsUnique_isMinOn_of_strictConvexOn isCompact_Icc (Set.nonempty_Icc.2 zero_le_one)
    (fun x _ => (hasDerivAt_quadraticMixingEnergy x).continuousAt.continuousWithinAt)
    strictConvexOn_quadraticMixingEnergy

/-- The quadratic mixing energy vanishes at `1 / 2`. -/
lemma quadraticMixingEnergy_half : quadraticMixingEnergy (1 / 2) = 0 := by
  norm_num [quadraticMixingEnergy]

/-- `1 / 2` minimizes the quadratic mixing energy on `[0, 1]`. -/
lemma isMinOn_quadraticMixingEnergy_half :
    IsMinOn quadraticMixingEnergy (Set.Icc 0 1) (1 / 2) :=
  isMinOn_iff.2 fun y _ => by
    rw [quadraticMixingEnergy_half]
    exact sq_nonneg (y - 1 / 2)

/-- The unique minimizer of the quadratic mixing energy on `[0, 1]` is `1 / 2`. -/
lemma isMinOn_quadraticMixingEnergy_iff {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    IsMinOn quadraticMixingEnergy (Set.Icc 0 1) x ↔ x = 1 / 2 :=
  ⟨fun hmin => strictConvexOn_quadraticMixingEnergy.eq_of_isMinOn hmin
      isMinOn_quadraticMixingEnergy_half hx ⟨by norm_num, by norm_num⟩,
    fun hx => hx ▸ isMinOn_quadraticMixingEnergy_half⟩

/-- The supporting plane of the quadratic mixing energy at its minimizer is horizontal. -/
lemma fderiv_quadraticMixingEnergy_half : fderiv ℝ quadraticMixingEnergy (1 / 2) = 0 := by
  have h := hasDerivAt_quadraticMixingEnergy (1 / 2)
  rw [sub_self, mul_zero] at h
  simpa using h.hasFDerivAt.fderiv

/-- The supporting-plane inequality of the quadratic mixing energy at its minimizer `1 / 2`
(MF11.4c), from `ConvexOn.add_fderiv_sub_le` on `[0, 1]`. -/
lemma quadraticMixingEnergy_add_fderiv_le {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    quadraticMixingEnergy (1 / 2) + fderiv ℝ quadraticMixingEnergy (1 / 2) (y - 1 / 2) ≤
      quadraticMixingEnergy y :=
  strictConvexOn_quadraticMixingEnergy.convexOn.add_fderiv_sub_le ⟨by norm_num, by norm_num⟩ hy
    (hasDerivAt_quadraticMixingEnergy _).differentiableAt

/-! ## G. Binary mixing: the ideal mixing energy -/

/-- The ideal mixing energy `x log x + (1 - x) log (1 - x)` (in units of `R T` per mole) of a
binary mixture with composition `x ∈ [0, 1]` (MF11.4c). Since `Real.log 0 = 0`, its values at
`0` and `1` are `0`, the continuous extension. It is `-Real.binEntropy x`. A model input, not a
claim about a real mixture. -/
noncomputable def idealMixingEnergy (x : ℝ) : ℝ :=
  x * Real.log x + (1 - x) * Real.log (1 - x)

/-- The ideal mixing energy is minus Mathlib's binary entropy `Real.binEntropy`. -/
lemma idealMixingEnergy_eq_neg_binEntropy : idealMixingEnergy = -Real.binEntropy := by
  funext x
  simp only [idealMixingEnergy, Pi.neg_apply, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,
    Real.negMulLog_def]
  ring

/-- The ideal mixing energy is strictly convex on `[0, 1]`, from Mathlib's
`Real.strictConcave_binEntropy`. -/
lemma strictConvexOn_idealMixingEnergy : StrictConvexOn ℝ (Set.Icc 0 1) idealMixingEnergy := by
  rw [idealMixingEnergy_eq_neg_binEntropy]
  exact Real.strictConcave_binEntropy.neg

/-- The ideal mixing energy is continuous, from Mathlib's `Real.binEntropy_continuous`. -/
lemma continuous_idealMixingEnergy : Continuous idealMixingEnergy := by
  rw [idealMixingEnergy_eq_neg_binEntropy]
  exact Real.binEntropy_continuous.neg

/-- The ideal mixing energy has exactly one minimizer on `[0, 1]` (MF11.4c), by
`existsUnique_isMinOn_of_strictConvexOn`. -/
lemma existsUnique_isMinOn_idealMixingEnergy :
    ∃! x, x ∈ Set.Icc (0 : ℝ) 1 ∧ IsMinOn idealMixingEnergy (Set.Icc 0 1) x :=
  existsUnique_isMinOn_of_strictConvexOn isCompact_Icc (Set.nonempty_Icc.2 zero_le_one)
    continuous_idealMixingEnergy.continuousOn strictConvexOn_idealMixingEnergy

/-- The ideal mixing energy at `1 / 2` is `-log 2`. -/
lemma idealMixingEnergy_half : idealMixingEnergy (1 / 2) = -Real.log 2 := by
  rw [idealMixingEnergy_eq_neg_binEntropy, Pi.neg_apply, one_div, Real.binEntropy_two_inv]

/-- `1 / 2` minimizes the ideal mixing energy on `[0, 1]`, by Mathlib's
`Real.binEntropy_le_log_two`. -/
lemma isMinOn_idealMixingEnergy_half : IsMinOn idealMixingEnergy (Set.Icc 0 1) (1 / 2) :=
  isMinOn_iff.2 fun y _ => by
    rw [idealMixingEnergy_half, idealMixingEnergy_eq_neg_binEntropy, Pi.neg_apply]
    exact neg_le_neg Real.binEntropy_le_log_two

/-- The unique minimizer of the ideal mixing energy on `[0, 1]` is `1 / 2`, with minimum
`-log 2` (`idealMixingEnergy_half`). -/
lemma isMinOn_idealMixingEnergy_iff {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    IsMinOn idealMixingEnergy (Set.Icc 0 1) x ↔ x = 1 / 2 :=
  ⟨fun hmin => strictConvexOn_idealMixingEnergy.eq_of_isMinOn hmin
      isMinOn_idealMixingEnergy_half hx ⟨by norm_num, by norm_num⟩,
    fun hx => hx ▸ isMinOn_idealMixingEnergy_half⟩

/-- Away from `0` and `1` the derivative of the ideal mixing energy is `log x - log (1 - x)`. -/
lemma hasDerivAt_idealMixingEnergy {x : ℝ} (h0 : x ≠ 0) (h1 : x ≠ 1) :
    HasDerivAt idealMixingEnergy (Real.log x - Real.log (1 - x)) x := by
  rw [idealMixingEnergy_eq_neg_binEntropy]
  convert (Real.hasDerivAt_binEntropy h0 h1).neg using 1
  ring

/-- The supporting plane of the ideal mixing energy at its minimizer is horizontal. -/
lemma fderiv_idealMixingEnergy_half : fderiv ℝ idealMixingEnergy (1 / 2) = 0 := by
  have h := hasDerivAt_idealMixingEnergy (x := 1 / 2) (by norm_num) (by norm_num)
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, sub_self] at h
  simpa using h.hasFDerivAt.fderiv

/-- The supporting-plane inequality of the ideal mixing energy at its minimizer `1 / 2`
(MF11.4c), from `ConvexOn.add_fderiv_sub_le` on `[0, 1]`. -/
lemma idealMixingEnergy_add_fderiv_le {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    idealMixingEnergy (1 / 2) + fderiv ℝ idealMixingEnergy (1 / 2) (y - 1 / 2) ≤
      idealMixingEnergy y :=
  strictConvexOn_idealMixingEnergy.convexOn.add_fderiv_sub_le ⟨by norm_num, by norm_num⟩ hy
    (hasDerivAt_idealMixingEnergy (by norm_num) (by norm_num)).differentiableAt

end MathlibExt.Analysis.Convex.ConstrainedOptimization
