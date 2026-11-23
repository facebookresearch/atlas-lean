/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Algebra.Group.Neighborhood
public import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Hyers–Ulam stability of the Cauchy equation

In 1940, Ulam asked whether a map between Banach spaces that *almost*
satisfies the Cauchy equation `f (x + y) = f x + f y` must be close to a
genuinely additive map. Hyers answered in 1941: if
`‖f (x + y) - f x - f y‖ ≤ δ` for all `x, y`, then there is an additive map
`A` with `‖f x - A x‖ ≤ δ` for all `x`, and `A` is unique. The approximating
map is the limit of the dyadic rescalings `2 ^ (-n) • f (2 ^ n • x)`.

This is a companion to the Banach-space / Hahn–Banach material of
`v1/Atlas/IntroductionToFunctionalAnalysis` (in particular the one-step
Hahn–Banach extension and the norming-functional corollaries: here the
approximating map is built directly, by a limiting argument, rather than by
extension), not one of the 72 v1 targets. Mathlib contains no Hyers–Ulam
stability statement.

Reference: D. H. Hyers, "On the stability of the linear functional equation",
*Proceedings of the National Academy of Sciences USA* 27 (1941), 222–224.

## Main declarations

* `exists_addMonoidHom_of_additive_defect` : Hyers' theorem, with the sharp
  bound `δ`.
* `eq_of_forall_norm_sub_le` : the approximating additive map is unique.
* `exists_addMonoidHom_of_jensen_defect` : the Jensen form: a map whose
  midpoint (Jensen) defect is `≤ δ` is within `4 * δ` of an additive map
  plus the constant `f 0`.
* `exists_continuousLinearMap_of_additive_defect_of_continuousAt` : if `f`
  is continuous at `0`, the approximating map is a continuous linear map.
-/

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.HyersUlam

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace ℝ E] [NormedSpace ℝ F] [CompleteSpace F]

/-- The dyadic approximants `2 ^ (-n) • f (2 ^ n • x)` used in Hyers' proof. -/
noncomputable def approx (f : E → F) (x : E) (n : ℕ) : F :=
  ((2 : ℝ) ^ n)⁻¹ • f ((2 : ℝ) ^ n • x)

/-- Norm of a natural-number multiple in a real normed space. -/
theorem norm_nsmul_eq {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (n : ℕ) (x : G) : ‖n • x‖ = (n : ℝ) * ‖x‖ := by
  rw [← Nat.cast_smul_eq_nsmul ℝ n x, norm_smul, Real.norm_natCast]

/-- **Hyers' theorem (Hyers–Ulam stability of the Cauchy equation).** If
`f : E → F` between real normed spaces, with `F` complete, satisfies
`‖f (x + y) - f x - f y‖ ≤ δ` for all `x, y`, then there is an additive map
`A : E →+ F` with `‖f x - A x‖ ≤ δ` for all `x`. The bound `δ` is sharp:
for `f x = x + c` on `ℝ` the defect is `‖c‖` and the best additive
approximant is the identity, at distance exactly `‖c‖`. -/
theorem exists_addMonoidHom_of_additive_defect {f : E → F} {δ : ℝ}
    (hf : ∀ x y, ‖f (x + y) - f x - f y‖ ≤ δ) :
    ∃ A : E →+ F, ∀ x, ‖f x - A x‖ ≤ δ := by
  -- The doubling estimate: the defect at `(y, y)` controls `f (2 • y) - 2 • f y`.
  have hdouble : ∀ y, ‖f ((2 : ℝ) • y) - (2 : ℝ) • f y‖ ≤ δ := by
    intro y
    have h := hf y y
    rw [sub_sub] at h
    rw [two_smul, two_smul]
    exact h
  -- The approximants move by at most `δ / 2 ^ (n + 1)` in one step.
  have hstep : ∀ (x : E) (n : ℕ),
      dist (approx f x n) (approx f x (n + 1)) ≤ δ / 2 / 2 ^ n := by
    intro x n
    have hpow : (2 : ℝ) ^ (n + 1) • x = (2 : ℝ) • ((2 : ℝ) ^ n • x) := by
      rw [pow_succ, mul_smul, smul_comm]
    have hcoeff : ((2 : ℝ) ^ n)⁻¹ = 2 * ((2 : ℝ) ^ (n + 1))⁻¹ := by
      rw [pow_succ, mul_inv_rev, ← mul_assoc,
        mul_inv_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_mul]
    have hcoeff2 : ((2 : ℝ) ^ (n + 1))⁻¹ * δ = δ / 2 / 2 ^ n := by
      have h2n : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
      have h2n1 : (2 : ℝ) ^ (n + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
      field_simp
      rw [pow_succ]
      ring
    have hmain : approx f x (n + 1) - approx f x n =
        ((2 : ℝ) ^ (n + 1))⁻¹ •
          (f ((2 : ℝ) • ((2 : ℝ) ^ n • x)) - (2 : ℝ) • f ((2 : ℝ) ^ n • x)) := by
      show ((2 : ℝ) ^ (n + 1))⁻¹ • f ((2 : ℝ) ^ (n + 1) • x) -
          ((2 : ℝ) ^ n)⁻¹ • f ((2 : ℝ) ^ n • x) = _
      rw [hpow, hcoeff, ← smul_smul, smul_sub,
        smul_comm (((2 : ℝ) ^ (n + 1))⁻¹) (2 : ℝ) (f ((2 : ℝ) ^ n • x))]
    rw [dist_eq_norm, norm_sub_rev, hmain, norm_smul,
      Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ ((2 : ℝ) ^ (n + 1))⁻¹)]
    calc ((2 : ℝ) ^ (n + 1))⁻¹ *
            ‖f ((2 : ℝ) • ((2 : ℝ) ^ n • x)) - (2 : ℝ) • f ((2 : ℝ) ^ n • x)‖
        ≤ ((2 : ℝ) ^ (n + 1))⁻¹ * δ :=
          mul_le_mul_of_nonneg_left (hdouble _) (by positivity)
      _ = δ / 2 / 2 ^ n := hcoeff2
  -- Hence the approximants form a Cauchy sequence, and `F` is complete.
  have hCauchy : ∀ x, CauchySeq (approx f x) :=
    fun x => cauchySeq_of_le_geometric_two (fun n => hstep x n)
  have hlim : ∀ x, ∃ a, Filter.Tendsto (approx f x) Filter.atTop (nhds a) :=
    fun x => cauchySeq_tendsto_of_complete (hCauchy x)
  choose A hA using hlim
  -- The limit is within `δ` of `f`: the geometric-series bound on the
  -- distance from `approx f x 0 = f x` to the limit.
  have hbound : ∀ x, ‖f x - A x‖ ≤ δ := by
    intro x
    have h0 : approx f x 0 = f x := by simp [approx]
    have hd := dist_le_of_le_geometric_two_of_tendsto₀ (fun n => hstep x n) (hA x)
    rw [h0, dist_eq_norm] at hd
    exact hd
  -- The limit is additive: the scaled defect `2 ^ (-n) • δ` tends to `0`.
  have hadd : ∀ x y, A (x + y) = A x + A y := by
    intro x y
    have hbound_n : ∀ n, ‖approx f (x + y) n - (approx f x n + approx f y n)‖ ≤
        ((2 : ℝ) ^ n)⁻¹ * δ := by
      intro n
      have e : approx f (x + y) n - (approx f x n + approx f y n) =
          ((2 : ℝ) ^ n)⁻¹ • (f ((2 : ℝ) ^ n • x + (2 : ℝ) ^ n • y) -
            f ((2 : ℝ) ^ n • x) - f ((2 : ℝ) ^ n • y)) := by
        show ((2 : ℝ) ^ n)⁻¹ • f ((2 : ℝ) ^ n • (x + y)) -
            (((2 : ℝ) ^ n)⁻¹ • f ((2 : ℝ) ^ n • x) +
              ((2 : ℝ) ^ n)⁻¹ • f ((2 : ℝ) ^ n • y)) = _
        rw [smul_add (((2 : ℝ) ^ n)) x y,
          ← smul_add (((2 : ℝ) ^ n)⁻¹) (f ((2 : ℝ) ^ n • x)) (f ((2 : ℝ) ^ n • y)),
          ← smul_sub (((2 : ℝ) ^ n)⁻¹)
            (f ((2 : ℝ) ^ n • x + (2 : ℝ) ^ n • y))
            (f ((2 : ℝ) ^ n • x) + f ((2 : ℝ) ^ n • y)),
          sub_sub]
      rw [e, norm_smul,
        Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ ((2 : ℝ) ^ n)⁻¹)]
      exact mul_le_mul_of_nonneg_left (hf _ _) (by positivity)
    have hlim0 : Filter.Tendsto (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹ * δ)
        Filter.atTop (nhds 0) := by
      have h2 : Filter.Tendsto (fun n : ℕ => ((1 : ℝ) / 2) ^ n) Filter.atTop
          (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      have h3 : (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹ * δ) =
          (fun n : ℕ => ((1 : ℝ) / 2) ^ n * δ) := by
        funext n
        rw [one_div, inv_pow]
      rw [h3]
      simpa using h2.mul tendsto_const_nhds
    have hdiff : Filter.Tendsto
        (fun n => approx f (x + y) n - (approx f x n + approx f y n))
        Filter.atTop (nhds 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mpr
        (squeeze_zero (fun n => norm_nonneg _) hbound_n hlim0)
    have hlim2 : Filter.Tendsto
        (fun n => approx f (x + y) n - (approx f x n + approx f y n))
        Filter.atTop (nhds (A (x + y) - (A x + A y))) :=
      (hA (x + y)).sub ((hA x).add (hA y))
    have hEq := tendsto_nhds_unique hlim2 hdiff
    exact sub_eq_zero.mp hEq
  refine ⟨{ toFun := A, map_zero' := ?_, map_add' := hadd }, hbound⟩
  have h := hadd 0 0
  rw [add_zero] at h
  exact add_left_cancel (by rw [add_zero]; exact h.symm)

omit [NormedSpace ℝ E] [CompleteSpace F] in
/-- **Uniqueness in Hyers' theorem.** Two additive maps both within `δ` of
the same `f` are equal: their difference is additive, hence `n`-homogeneous,
while staying bounded by `2 * δ`. -/
theorem eq_of_forall_norm_sub_le {f : E → F} {δ : ℝ}
    {A₁ A₂ : E →+ F} (h₁ : ∀ x, ‖f x - A₁ x‖ ≤ δ)
    (h₂ : ∀ x, ‖f x - A₂ x‖ ≤ δ) : A₁ = A₂ := by
  ext x
  have hdiff : ∀ n : ℕ, (n : ℝ) * ‖A₁ x - A₂ x‖ ≤ 2 * δ := by
    intro n
    have h1 : ‖A₁ (n • x) - A₂ (n • x)‖ ≤ 2 * δ := by
      calc ‖A₁ (n • x) - A₂ (n • x)‖
          = ‖(A₁ (n • x) - f (n • x)) + (f (n • x) - A₂ (n • x))‖ := by
            congr 1
            abel
        _ ≤ ‖A₁ (n • x) - f (n • x)‖ + ‖f (n • x) - A₂ (n • x)‖ :=
            norm_add_le _ _
        _ = ‖f (n • x) - A₁ (n • x)‖ + ‖f (n • x) - A₂ (n • x)‖ := by
            rw [norm_sub_rev]
        _ ≤ δ + δ := add_le_add (h₁ _) (h₂ _)
        _ = 2 * δ := by ring
    have h2 : A₁ (n • x) - A₂ (n • x) = n • (A₁ x - A₂ x) := by
      rw [map_nsmul, map_nsmul, smul_sub]
    rw [h2, norm_nsmul_eq] at h1
    exact h1
  rcases eq_or_ne (A₁ x - A₂ x) 0 with h | h
  · exact sub_eq_zero.mp h
  · have hpos : 0 < ‖A₁ x - A₂ x‖ := norm_pos_iff.mpr h
    obtain ⟨n, hn⟩ := exists_nat_gt (2 * δ / ‖A₁ x - A₂ x‖)
    have hmul : 2 * δ < (n : ℝ) * ‖A₁ x - A₂ x‖ := by
      rw [div_lt_iff₀ hpos] at hn
      exact hn
    exact absurd (hdiff n) (not_le.mpr hmul)

/-- **Hyers–Ulam stability of Jensen's functional equation.** If the midpoint
(Jensen) defect `‖f ((1/2) • (x + y)) - (1/2) • (f x + f y)‖` is `≤ δ` for
all `x, y`, then `f` is within `4 * δ` of an additive map plus the constant
`f 0`. The factor `4` comes from doubling the two Jensen estimates at
`(x + y, 0)` and `(x, y)`. -/
theorem exists_addMonoidHom_of_jensen_defect {f : E → F} {δ : ℝ}
    (hf : ∀ x y, ‖f ((1 / 2 : ℝ) • (x + y)) - (1 / 2 : ℝ) • (f x + f y)‖ ≤ δ) :
    ∃ A : E →+ F, ∀ x, ‖f x - A x - f 0‖ ≤ 4 * δ := by
  have hg : ∀ x y, ‖(f (x + y) - f 0) - (f x - f 0) - (f y - f 0)‖ ≤ 4 * δ := by
    intro x y
    have hd1 : ‖(2 : ℝ) • f ((1 / 2 : ℝ) • (x + y)) - (f (x + y) + f 0)‖ ≤
        2 * δ := by
      have h := hf (x + y) 0
      rw [add_zero] at h
      have e : (2 : ℝ) • (f ((1 / 2 : ℝ) • (x + y)) -
          (1 / 2 : ℝ) • (f (x + y) + f 0)) =
          (2 : ℝ) • f ((1 / 2 : ℝ) • (x + y)) - (f (x + y) + f 0) := by
        rw [smul_sub, smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul]
      calc ‖(2 : ℝ) • f ((1 / 2 : ℝ) • (x + y)) - (f (x + y) + f 0)‖
          = ‖(2 : ℝ) • (f ((1 / 2 : ℝ) • (x + y)) -
              (1 / 2 : ℝ) • (f (x + y) + f 0))‖ := by rw [e]
        _ = 2 * ‖f ((1 / 2 : ℝ) • (x + y)) -
              (1 / 2 : ℝ) • (f (x + y) + f 0)‖ := by
            rw [norm_smul]
            norm_num
        _ ≤ 2 * δ := mul_le_mul_of_nonneg_left h (by norm_num)
    have hd2 : ‖(2 : ℝ) • f ((1 / 2 : ℝ) • (x + y)) - f x - f y‖ ≤ 2 * δ := by
      have h := hf x y
      have e : (2 : ℝ) • (f ((1 / 2 : ℝ) • (x + y)) -
          (1 / 2 : ℝ) • (f x + f y)) =
          (2 : ℝ) • f ((1 / 2 : ℝ) • (x + y)) - f x - f y := by
        rw [smul_sub, smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul,
          sub_sub]
      calc ‖(2 : ℝ) • f ((1 / 2 : ℝ) • (x + y)) - f x - f y‖
          = ‖(2 : ℝ) • (f ((1 / 2 : ℝ) • (x + y)) -
              (1 / 2 : ℝ) • (f x + f y))‖ := by rw [e]
        _ = 2 * ‖f ((1 / 2 : ℝ) • (x + y)) - (1 / 2 : ℝ) • (f x + f y)‖ := by
            rw [norm_smul]
            norm_num
        _ ≤ 2 * δ := mul_le_mul_of_nonneg_left h (by norm_num)
    have heq : (f (x + y) - f 0) - (f x - f 0) - (f y - f 0) =
        (f (x + y) + f 0 - (2 : ℝ) • f ((1 / 2 : ℝ) • (x + y))) +
          ((2 : ℝ) • f ((1 / 2 : ℝ) • (x + y)) - f x - f y) := by abel
    rw [heq]
    calc ‖(f (x + y) + f 0 - (2 : ℝ) • f ((1 / 2 : ℝ) • (x + y))) +
            ((2 : ℝ) • f ((1 / 2 : ℝ) • (x + y)) - f x - f y)‖
        ≤ ‖f (x + y) + f 0 - (2 : ℝ) • f ((1 / 2 : ℝ) • (x + y))‖ +
            ‖(2 : ℝ) • f ((1 / 2 : ℝ) • (x + y)) - f x - f y‖ :=
          norm_add_le _ _
      _ = ‖(2 : ℝ) • f ((1 / 2 : ℝ) • (x + y)) - (f (x + y) + f 0)‖ +
            ‖(2 : ℝ) • f ((1 / 2 : ℝ) • (x + y)) - f x - f y‖ := by
          rw [norm_sub_rev (f (x + y) + f 0) ((2 : ℝ) • f ((1 / 2 : ℝ) • (x + y)))]
      _ ≤ 2 * δ + 2 * δ := add_le_add hd1 hd2
      _ = 4 * δ := by ring
  obtain ⟨A, hA⟩ := exists_addMonoidHom_of_additive_defect
    (f := fun x => f x - f 0) (δ := 4 * δ) hg
  refine ⟨A, fun x => ?_⟩
  have h := hA x
  change ‖f x - f 0 - A x‖ ≤ 4 * δ at h
  rw [show f x - f 0 - A x = f x - A x - f 0 by abel] at h
  exact h

/-- **Continuous Hyers–Ulam stability.** If `f` is continuous at `0` (in
particular if `f` itself is continuous), the additive approximant from
Hyers' theorem is continuous, hence a continuous real-linear map. The proof:
continuity of `f` at `0` bounds `f` on a small ball, so the approximant is
bounded on that ball, and an additive map bounded on a ball is continuous
at `0` by the dyadic scaling argument. -/
theorem exists_continuousLinearMap_of_additive_defect_of_continuousAt
    {f : E → F} {δ : ℝ} (hδ : 0 ≤ δ) (hf : ∀ x y, ‖f (x + y) - f x - f y‖ ≤ δ)
    (hcont : ContinuousAt f 0) :
    ∃ A : E →L[ℝ] F, ∀ x, ‖f x - A x‖ ≤ δ := by
  obtain ⟨A₀, hA₀⟩ := exists_addMonoidHom_of_additive_defect hf
  -- `f` is bounded on some ball around `0`.
  have hball : ∃ r : ℝ, 0 < r ∧ ∀ x, ‖x‖ < r → ‖f x‖ ≤ ‖f 0‖ + 1 := by
    have h1 := (Metric.continuousAt_iff.mp hcont) 1 one_pos
    obtain ⟨r, hr, hrx⟩ := h1
    refine ⟨r, hr, fun x hx => ?_⟩
    have h2 : dist (f x) (f 0) < 1 := by
      apply hrx
      rw [dist_eq_norm, sub_zero]
      exact hx
    have h3 : ‖f x - f 0‖ < 1 := by rwa [dist_eq_norm] at h2
    calc ‖f x‖ = ‖f 0 + (f x - f 0)‖ := by rw [add_sub_cancel]
      _ ≤ ‖f 0‖ + ‖f x - f 0‖ := norm_add_le _ _
      _ ≤ ‖f 0‖ + 1 := by linarith
  obtain ⟨r, hr, hfr⟩ := hball
  -- `A₀` is continuous at `0`: for `‖h‖ < r / n`, scale up by `n`.
  have hA₀cont0 : ContinuousAt A₀ 0 := by
    rw [Metric.continuousAt_iff]
    intro ε hε
    set B : ℝ := ‖f 0‖ + 1 + δ with hBdef
    have hB : 0 ≤ B := add_nonneg (add_nonneg (norm_nonneg _) zero_le_one) hδ
    obtain ⟨n, hn⟩ := exists_nat_gt (B / ε)
    have hn_pos : (0 : ℝ) < n := lt_of_le_of_lt (div_nonneg hB hε.le) hn
    have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
    refine ⟨r / n, div_pos hr hn_pos, fun h hh => ?_⟩
    have hhn : ‖h‖ < r / n := by simpa [dist_eq_norm] using hh
    have hnh : ‖(n : ℕ) • h‖ < r := by
      calc ‖(n : ℕ) • h‖ = (n : ℝ) * ‖h‖ := by rw [norm_nsmul_eq]
        _ < (n : ℝ) * (r / n) := mul_lt_mul_of_pos_left hhn hn_pos
        _ = r := by
          rw [mul_div_assoc', mul_comm (n : ℝ) r, mul_div_assoc,
            div_self hn_ne, mul_one]
    have hbound_nh : ‖A₀ ((n : ℕ) • h)‖ ≤ B := by
      calc ‖A₀ ((n : ℕ) • h)‖ ≤ ‖f ((n : ℕ) • h)‖ + δ := by
            have hz := hA₀ ((n : ℕ) • h)
            have htri : ‖A₀ ((n : ℕ) • h)‖ ≤
                ‖f ((n : ℕ) • h)‖ + ‖f ((n : ℕ) • h) - A₀ ((n : ℕ) • h)‖ := by
              calc ‖A₀ ((n : ℕ) • h)‖
                  = ‖f ((n : ℕ) • h) +
                      (A₀ ((n : ℕ) • h) - f ((n : ℕ) • h))‖ := by
                    rw [add_sub_cancel]
                _ ≤ ‖f ((n : ℕ) • h)‖ +
                    ‖A₀ ((n : ℕ) • h) - f ((n : ℕ) • h)‖ := norm_add_le _ _
                _ = ‖f ((n : ℕ) • h)‖ +
                    ‖f ((n : ℕ) • h) - A₀ ((n : ℕ) • h)‖ := by
                    rw [norm_sub_rev]
            exact htri.trans (add_le_add_right hz _)
        _ ≤ (‖f 0‖ + 1) + δ := add_le_add_left (hfr _ hnh) _
        _ = B := by rw [hBdef]
    have hA₀h : ‖A₀ h‖ = ‖A₀ ((n : ℕ) • h)‖ / (n : ℝ) := by
      have e : ‖A₀ ((n : ℕ) • h)‖ = (n : ℝ) * ‖A₀ h‖ := by
        rw [map_nsmul, norm_nsmul_eq]
      rw [e, mul_div_cancel_left₀ _ hn_ne]
    have hfin : ‖A₀ ((n : ℕ) • h)‖ / (n : ℝ) < ε := by
      have hle : ‖A₀ ((n : ℕ) • h)‖ / (n : ℝ) ≤ B / (n : ℝ) :=
        div_le_div_of_nonneg_right hbound_nh hn_pos.le
      have hlt : B / (n : ℝ) < ε := by
        rw [div_lt_iff₀ hn_pos]
        have hn' : B < (n : ℝ) * ε := by
          rw [div_lt_iff₀ hε] at hn
          exact hn
        linarith
      exact hle.trans_lt hlt
    rw [map_zero, dist_eq_norm, sub_zero, hA₀h]
    exact hfin
  have hA₀cont : Continuous A₀ := continuous_of_continuousAt_zero A₀ hA₀cont0
  refine ⟨A₀.toRealLinearMap hA₀cont, fun x => ?_⟩
  simpa only [AddMonoidHom.coe_toRealLinearMap] using hA₀ x

end MathlibExt.Analysis.FunctionalAnalysis.HyersUlam
