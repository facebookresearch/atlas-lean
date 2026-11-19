/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.ODE.InvariantRegions
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.ODE.ExistUnique

/-!
# Invariant-region checks

Concrete consumers of `MathlibExt.Analysis.ODE.InvariantRegions`: the closed reversible network
`A ⇌ B` with an explicit trajectory, explicit scalar and diagonal exponential solutions, an
instantiation of Mathlib's uniqueness theorem, and boundary checks showing that the
compatibility and Lipschitz hypotheses cannot be dropped.

## i. Overview

These are elaboration, non-vacuity and boundary checks, not new results. Solutions are meant
in the sense of `MathlibExt.Analysis.ODE.InvariantRegions`: `∀ t ∈ I, HasDerivAt x (F (x t)) t`.

## ii. Key results

No new mathematics. The definitions are test data: the `A ⇌ B` network and a trajectory
(`abStoich`, `abExp`, `abSol`), an incompatible outflow (`outStoich`, `outExp`, `outSol`), an
autocatalytic reaction (`autoStoich`, `autoExp`), explicit solutions (`expSol`, `diagRates`,
`diagSol`) and a non-Lipschitz field (`sqrtField`, `sqrtSol`). The lemmas are small facts about
this data.

## iii. Table of contents

- A. Existence and uniqueness from Mathlib
- B. The reversible network `A ⇌ B`
- C. A scalar exponential solution
- D. A diagonal two-species system
- E. Boundary checks

## iv. References

- `MathlibExt.Analysis.ODE.InvariantRegions`
- Mathlib `ODE_solution_unique_univ` (`Mathlib.Analysis.ODE.ExistUnique`)
-/

@[expose] public section

namespace MathlibExtTest.Analysis.ODE.InvariantRegions

open MetaMathlibExt

/-! ## A. Existence and uniqueness from Mathlib -/

/-- The linear field `y ↦ a * y` is `‖a‖₊`-Lipschitz (`lipschitzWith_smul`), so Mathlib's
uniqueness theorem `ODE_solution_unique_univ` applies: every solution of `x' = a * x` on `ℝ`
with `x 0 = x₀` is the explicit solution `t ↦ x₀ * exp (a * t)` of `scalar_exp_solution`, which
also witnesses existence. -/
example (a x₀ : ℝ) (x : ℝ → ℝ) (hx : ∀ t, HasDerivAt x (a * x t) t) (h0 : x 0 = x₀) :
    x = fun t => x₀ * Real.exp (a * t) := by
  have hlip : LipschitzWith ‖a‖₊ (fun y : ℝ => a * y) := lipschitzWith_smul a
  have hsol := scalar_exp_solution (x := fun t => x₀ * Real.exp (a * t)) fun _ => rfl
  exact ODE_solution_unique_univ (v := fun _ y => a * y) (s := fun _ => Set.univ)
    (fun _ => hlip.lipschitzOnWith) (fun t => ⟨hx t, Set.mem_univ _⟩)
    (fun t => ⟨hsol.2 t, Set.mem_univ _⟩) (h0.trans hsol.1.symm)

-- Local existence does not give existence for all time. The field `y ↦ y ^ 2` is locally
-- Lipschitz, so its solutions are locally unique, but the solution `t ↦ 1 / (1 - t)` of
-- `x' = x ^ 2`, `x 0 = 1`, exists only for `t < 1` and blows up as `t → 1⁻`. Section E shows
-- that `y ↦ y ^ 2` has no global Lipschitz constant.

/-! ## B. The reversible network `A ⇌ B` -/

/-- Stoichiometric coefficients of `A ⇌ B`, with species `A = 0`, `B = 1` and reactions
`0 : A → B`, `1 : B → A`: `abStoich i j` is the net change of species `i` in reaction `j`. -/
def abStoich : Fin 2 → Fin 2 → ℤ := ![![-1, 1], ![1, -1]]

/-- Reactant exponents of `A ⇌ B`: reaction `0` has rate `k₊ * y 0` and reaction `1` has rate
`k₋ * y 1`. -/
def abExp : Fin 2 → Fin 2 → ℕ := ![![1, 0], ![0, 1]]

/-- Compatibility for `A ⇌ B`: a reaction that consumes a species has it among its reactants. -/
lemma ab_compat : ∀ i j, abStoich i j < 0 → 1 ≤ abExp j i := by decide

/-- The rate constants `![k₊, k₋]` are nonnegative when `k₊` and `k₋` are. -/
lemma ab_rates_nonneg {kp km : ℝ} (hkp : 0 ≤ kp) (hkm : 0 ≤ km) : ∀ j, 0 ≤ ![kp, km] j :=
  Fin.forall_fin_two.2 ⟨hkp, hkm⟩

/-- The `A ⇌ B` field is `F y = (-(k₊ * y 0) + k₋ * y 1, k₊ * y 0 - k₋ * y 1)`. -/
example (kp km : ℝ) (y : Fin 2 → ℝ) :
    massActionField abStoich abExp ![kp, km] y 0 = -(kp * y 0) + km * y 1 ∧
      massActionField abStoich abExp ![kp, km] y 1 = kp * y 0 - km * y 1 := by
  refine ⟨by simp [massActionField, abStoich, abExp, Fin.sum_univ_two, Fin.prod_univ_two], ?_⟩
  simp [massActionField, abStoich, abExp, Fin.sum_univ_two, Fin.prod_univ_two]
  ring

/-- The weight `w = (1, 1)` annihilates the `A ⇌ B` field, for all rate constants. -/
lemma ab_kernel (kp km : ℝ) (y : Fin 2 → ℝ) :
    ∑ i, (fun _ : Fin 2 => (1 : ℝ)) i * massActionField abStoich abExp ![kp, km] y i = 0 := by
  simp [massActionField, abStoich, abExp, Fin.sum_univ_two, Fin.prod_univ_two]
  ring

/-- `linear_invariant_of_hasDerivAt` with `w = 1`: along any solution of `A ⇌ B` on a convex
set `I` the total `x t 0 + x t 1` is constant. Nonnegativity of the rates is not needed for
this. -/
example (kp km : ℝ) {I : Set ℝ} (hI : Convex ℝ I) {x : ℝ → Fin 2 → ℝ}
    (hx : ∀ t ∈ I, HasDerivAt x (massActionField abStoich abExp ![kp, km] (x t)) t) :
    ∀ t₁ ∈ I, ∀ t₂ ∈ I, x t₁ 0 + x t₁ 1 = x t₂ 0 + x t₂ 1 := by
  intro t₁ ht₁ t₂ ht₂
  simpa [Fin.sum_univ_two] using
    linear_invariant_of_hasDerivAt (ab_kernel kp km) hI hx t₁ ht₁ t₂ ht₂

/-- `massActionField_nonneg_of_eq_zero` at the boundary state `(0, c)` with `c ≥ 0`: the first
component of the field is nonnegative. -/
example (kp km c : ℝ) (hkp : 0 ≤ kp) (hkm : 0 ≤ km) (hc : 0 ≤ c) :
    0 ≤ massActionField abStoich abExp ![kp, km] ![0, c] 0 :=
  massActionField_nonneg_of_eq_zero (ab_rates_nonneg hkp hkm) ab_compat
    (Fin.forall_fin_two.2 ⟨le_rfl, hc⟩) rfl

/-- The value of that component is `k₋ * c`. -/
example (kp km c : ℝ) : massActionField abStoich abExp ![kp, km] ![0, c] 0 = km * c := by
  simp [massActionField, abStoich, abExp, Fin.sum_univ_two, Fin.prod_univ_two]

/-- The invariant simplex of `A ⇌ B`: for rates `k₊, k₋ ≥ 0`, a solution on a convex set `I`
that is nonnegative at `t₀ ∈ I` satisfies `0 ≤ x t 0`, `0 ≤ x t 1` and
`x t 0 + x t 1 = x t₀ 0 + x t₀ 1` at every `t ∈ I` with `t₀ ≤ t`
(`massActionField_orthant_invariant`, and `linear_invariant_of_hasDerivAt` with `w = 1`). -/
example (kp km : ℝ) (hkp : 0 ≤ kp) (hkm : 0 ≤ km) {I : Set ℝ} (hI : Convex ℝ I)
    {x : ℝ → Fin 2 → ℝ}
    (hx : ∀ t ∈ I, HasDerivAt x (massActionField abStoich abExp ![kp, km] (x t)) t)
    {t₀ : ℝ} (ht₀ : t₀ ∈ I) (h₀ : ∀ i, 0 ≤ x t₀ i) {t : ℝ} (ht : t ∈ I) (htt : t₀ ≤ t) :
    0 ≤ x t 0 ∧ 0 ≤ x t 1 ∧ x t 0 + x t 1 = x t₀ 0 + x t₀ 1 := by
  have hpos := massActionField_orthant_invariant (ab_rates_nonneg hkp hkm) ab_compat hI hx ht₀
    h₀ t ht htt
  refine ⟨hpos 0, hpos 1, ?_⟩
  simpa [Fin.sum_univ_two] using
    linear_invariant_of_hasDerivAt (ab_kernel kp km) hI hx t ht t₀ ht₀

/-- An explicit trajectory of `A ⇌ B` with `k₊ = k₋ = 1`:
`x t = (1 + exp (-2 * t), 1 - exp (-2 * t))`. -/
noncomputable def abSol (t : ℝ) : Fin 2 → ℝ := ![1 + Real.exp (-2 * t), 1 - Real.exp (-2 * t)]

/-- `abSol` solves the `A ⇌ B` system with `k₊ = k₋ = 1` on all of `ℝ`. -/
lemma abSol_hasDerivAt (t : ℝ) :
    HasDerivAt abSol (massActionField abStoich abExp ![1, 1] (abSol t)) t := by
  have he : HasDerivAt (fun s => Real.exp (-2 * s)) (-2 * Real.exp (-2 * t)) t := by
    simpa [mul_comm] using ((hasDerivAt_id t).const_mul (-2 : ℝ)).exp
  refine hasDerivAt_pi.2 (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
  · refine (he.const_add 1).congr_deriv ?_
    simp [massActionField, abStoich, abExp, abSol, Fin.sum_univ_two, Fin.prod_univ_two]
    ring
  · refine (he.const_sub 1).congr_deriv ?_
    simp [massActionField, abStoich, abExp, abSol, Fin.sum_univ_two, Fin.prod_univ_two]
    ring

/-- Along the trajectory `abSol`, `linear_invariant_of_hasDerivAt` gives the total
`abSol t 0 + abSol t 1 = 2`, and `massActionField_orthant_invariant` (from `abSol 0 = (2, 0)`)
gives `0 ≤ abSol t 1 = 1 - exp (-2 * t)` for `t ≥ 0`. -/
example (t : ℝ) (ht : 0 ≤ t) : abSol t 0 + abSol t 1 = 2 ∧ 0 ≤ 1 - Real.exp (-2 * t) := by
  have hx : ∀ s ∈ (Set.univ : Set ℝ),
      HasDerivAt abSol (massActionField abStoich abExp ![1, 1] (abSol s)) s :=
    fun s _ => abSol_hasDerivAt s
  have htot := linear_invariant_of_hasDerivAt (ab_kernel 1 1) convex_univ hx t trivial 0 trivial
  have h0 : ∀ i, 0 ≤ abSol 0 i :=
    Fin.forall_fin_two.2 ⟨by norm_num [abSol], by norm_num [abSol]⟩
  have hpos := massActionField_orthant_invariant (ab_rates_nonneg zero_le_one zero_le_one)
    ab_compat convex_univ hx (Set.mem_univ 0) h0 t trivial ht 1
  have htot0 : abSol 0 0 + abSol 0 1 = 2 := by norm_num [abSol]
  exact ⟨by simpa [Fin.sum_univ_two, htot0] using htot, by simpa [abSol] using hpos⟩

/-! ## C. A scalar exponential solution -/

/-- The explicit solution `x t = 3 * exp (-t / 2)` (`a = -1 / 2`, `x₀ = 3`). -/
noncomputable def expSol (t : ℝ) : ℝ := 3 * Real.exp (-1 / 2 * t)

/-- `scalar_exp_solution`: `expSol` solves `x' = -1 / 2 * x` with `x 0 = 3`. -/
example : expSol 0 = 3 ∧ ∀ t, HasDerivAt expSol (-1 / 2 * expSol t) t :=
  scalar_exp_solution fun _ => rfl

/-- `scalar_exp_solution_abs_le` for `expSol` with `c = 1 / 2`:
`|x t| ≤ 3 * exp (-(1 / 2) * t)` for `t ≥ 0`. -/
example {t : ℝ} (ht : 0 ≤ t) : |expSol t| ≤ 3 * Real.exp (-(1 / 2) * t) := by
  have h := scalar_exp_solution_abs_le (x := expSol) (c := 1 / 2) (fun _ => rfl) (by norm_num) ht
  rwa [abs_of_pos (by norm_num : (0 : ℝ) < 3)] at h

/-- The decay bound at `t = 2`: `|x 2| ≤ 3 * exp (-1)`. -/
example : |expSol 2| ≤ 3 * Real.exp (-1) := by
  have h := scalar_exp_solution_abs_le (x := expSol) (c := 1 / 2) (fun _ => rfl) (by norm_num)
    (by norm_num : (0 : ℝ) ≤ 2)
  norm_num at h
  exact h

/-! ## D. A diagonal two-species system -/

/-- Distinct negative rates `d = (-1, -2)`. -/
def diagRates : Fin 2 → ℝ := ![-1, -2]

/-- The explicit solution `x t i = x₀ i * exp (d i * t)` for the rates `diagRates`. -/
noncomputable def diagSol (x₀ : Fin 2 → ℝ) (t : ℝ) : Fin 2 → ℝ :=
  fun i => x₀ i * Real.exp (diagRates i * t)

/-- `diagonal_exp_solution`: `diagSol x₀` solves the diagonal system `x' i = d i * x i` with
`x 0 = x₀`. -/
example (x₀ : Fin 2 → ℝ) :
    diagSol x₀ 0 = x₀ ∧ ∀ t, HasDerivAt (diagSol x₀) (fun i => diagRates i * diagSol x₀ t i) t :=
  diagonal_exp_solution fun _ _ => rfl

/-- `diagonal_exp_solution_abs_le` at `t = 1` with the slower rate `c = 1`:
`|x 1 i| ≤ |x₀ i| * exp (-1)`. -/
example (x₀ : Fin 2 → ℝ) (i : Fin 2) : |diagSol x₀ 1 i| ≤ |x₀ i| * Real.exp (-1) := by
  have hd : ∀ j, diagRates j ≤ -1 := Fin.forall_fin_two.2 ⟨by norm_num [diagRates],
    by norm_num [diagRates]⟩
  simpa using diagonal_exp_solution_abs_le (x := diagSol x₀) (fun _ _ => rfl) hd zero_le_one i

/-! ## E. Boundary checks -/

/-- A zero-order outflow `A → ∅` whose rate does not involve `A`: `N 0 0 = -1`. -/
def outStoich : Fin 1 → Fin 1 → ℤ := fun _ _ => -1

/-- The exponent of `A` in the rate of the outflow is `0`. -/
def outExp : Fin 1 → Fin 1 → ℕ := fun _ _ => 0

/-- The compatibility hypothesis of `massActionField_nonneg_of_eq_zero` fails for the
outflow. -/
example : ¬ ∀ i j, outStoich i j < 0 → 1 ≤ outExp j i := by decide

/-- Without compatibility the boundary sign fails: with rate constant `1`, at the zero state
(so `k ≥ 0`, `y ≥ 0` and `y 0 = 0`), the field is `F y 0 = -1 < 0`. -/
example : massActionField outStoich outExp (fun _ => 1) (fun _ => 0) 0 = -1 ∧
    massActionField outStoich outExp (fun _ => 1) (fun _ => 0) 0 < 0 := by
  simp [massActionField, outStoich, outExp]

/-- The trajectory `x t = -t` of the outflow. -/
def outSol (t : ℝ) : Fin 1 → ℝ := fun _ => -t

/-- Without compatibility the orthant is not invariant: `outSol` solves `x' = F x` for the
outflow with rate constant `1`, starts at `0`, and is negative at `t = 1`. -/
example : (∀ t, HasDerivAt outSol (massActionField outStoich outExp (fun _ => 1) (outSol t)) t) ∧
    (∀ i, 0 ≤ outSol 0 i) ∧ outSol 1 0 < 0 := by
  refine ⟨fun t => hasDerivAt_pi.2 fun _ => ?_, fun _ => by simp [outSol], by simp [outSol]⟩
  simpa [massActionField, outStoich, outExp, outSol] using hasDerivAt_neg' t

/-- The polynomial field `y ↦ y ^ 2` is not globally Lipschitz: there is no `K : ℝ≥0` with
`LipschitzWith K (fun y : ℝ => y ^ 2)`. -/
example : ¬ ∃ K : NNReal, LipschitzWith K (fun y : ℝ => y ^ 2) := by
  rintro ⟨K, hK⟩
  have h := hK.dist_le_mul ((K : ℝ) + 1) 0
  have hK0 : (0 : ℝ) ≤ K := NNReal.coe_nonneg K
  rw [Real.dist_eq, Real.dist_eq, zero_pow two_ne_zero, sub_zero, sub_zero,
    abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at h
  nlinarith

/-- The autocatalytic reaction `2 A → 3 A`: net change `N 0 0 = 1`. -/
def autoStoich : Fin 1 → Fin 1 → ℤ := fun _ _ => 1

/-- The rate of `2 A → 3 A` is quadratic in `A`. -/
def autoExp : Fin 1 → Fin 1 → ℕ := fun _ _ => 2

/-- A mass-action field need not be globally Lipschitz: the field of `2 A → 3 A` with rate
constant `1`, which is `y ↦ fun _ => y 0 ^ 2`, has no global Lipschitz constant. -/
example : ¬ ∃ K : NNReal, LipschitzWith K (massActionField autoStoich autoExp fun _ => 1) := by
  rintro ⟨K, hK⟩
  have hF : massActionField autoStoich autoExp (fun _ => 1) = fun y _ => y 0 ^ 2 := by
    funext y i
    simp [massActionField, autoStoich, autoExp]
  rw [hF] at hK
  have h := hK.dist_le_mul (fun _ => (K : ℝ) + 1) (fun _ => 0)
  have hK0 : (0 : ℝ) ≤ K := NNReal.coe_nonneg K
  rw [dist_pi_const, dist_pi_const, Real.dist_eq, Real.dist_eq, zero_pow two_ne_zero, sub_zero,
    sub_zero, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at h
  nlinarith

/-- The field `y ↦ -√|y 0|` on `Fin 1 → ℝ`, which is not Lipschitz near `0`. -/
noncomputable def sqrtField (y : Fin 1 → ℝ) : Fin 1 → ℝ := fun _ => -√|y 0|

/-- The trajectory `x t = -(t ^ 2 / 4)`. -/
noncomputable def sqrtSol (t : ℝ) : Fin 1 → ℝ := fun _ => -(t ^ 2 / 4)

/-- `sqrtField` has the boundary-sign property. -/
lemma sqrtField_boundary :
    ∀ y : Fin 1 → ℝ, (∀ s, 0 ≤ y s) → ∀ i, y i = 0 → 0 ≤ sqrtField y i := by
  intro y _ i hi
  obtain rfl : i = 0 := Subsingleton.elim _ _
  simp [sqrtField, hi]

/-- `sqrtSol` solves `x' = sqrtField x` on `[0, ∞)`. -/
lemma sqrtSol_hasDerivAt :
    ∀ t ∈ Set.Ici (0 : ℝ), HasDerivAt sqrtSol (sqrtField (sqrtSol t)) t := by
  intro t ht
  refine hasDerivAt_pi.2 fun _ => ?_
  have hsq : √|-(t ^ 2 / 4)| = t / 2 := by
    rw [abs_neg, abs_of_nonneg (by positivity), show t ^ 2 / 4 = (t / 2) ^ 2 by ring,
      Real.sqrt_sq (by linarith [Set.mem_Ici.1 ht])]
  simp only [sqrtField, sqrtSol, hsq]
  exact ((hasDerivAt_pow 2 t).div_const 4).fun_neg.congr_deriv (by norm_num; ring)

/-- The Lipschitz hypothesis of `orthant_invariant_of_boundary_nonneg` cannot be dropped:
`sqrtField` has the boundary-sign property (`sqrtField_boundary`) and `sqrtSol` solves
`x' = sqrtField x` on `[0, ∞)` (`sqrtSol_hasDerivAt`) and starts in the orthant, yet
`sqrtSol 1 0 < 0`. Consequently `sqrtField` is not locally Lipschitz. -/
example : (∀ i, 0 ≤ sqrtSol 0 i) ∧ sqrtSol 1 0 < 0 ∧ ¬ LocallyLipschitz sqrtField := by
  refine ⟨fun _ => by simp [sqrtSol], by norm_num [sqrtSol], fun hlip => ?_⟩
  have h := orthant_invariant_of_boundary_nonneg hlip sqrtField_boundary (convex_Ici 0)
    sqrtSol_hasDerivAt (Set.mem_Ici.2 le_rfl) (fun _ => by simp [sqrtSol]) 1 (by norm_num)
    zero_le_one 0
  norm_num [sqrtSol] at h

end MathlibExtTest.Analysis.ODE.InvariantRegions
