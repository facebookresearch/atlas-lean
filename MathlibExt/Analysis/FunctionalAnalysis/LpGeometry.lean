/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Convex.StrictConvexSpace
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.PiLp

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Geometry of finite `ℓ^p` spaces

The two-coordinate space `PiLp p (Fin 2 → ℝ)` already exhibits the sharp
geometry of `ℓ^p` spaces. The vectors `u = (1, 1)` and `v = (1, -1)` witness
that the parallelogram law holds in `PiLp p (Fin 2 → ℝ)` if and only if
`p = 2`; in particular no inner product on this space induces its `ℓ^p` norm
unless `p = 2`. For `1 < p < ∞` the same two-coordinate picture gives the
strict convexity of the unit ball: the midpoint of two distinct unit vectors
has norm `< 1`, proved coordinatewise from the strict convexity of
`t ↦ |t| ^ p`. The endpoints fail: at `p = 1` the vectors `(1, 0)` and
`(0, 1)` have midpoint of norm `1`, and at `p = ∞` the vectors `(1, 1)` and
`(1, -1)` have midpoint `(1, 0)` of norm `1`.

Classical reference: Rudin, *Functional Analysis*, 2nd edition, Chapter 4
(the parallelogram law and the characterization of inner product spaces) and
Chapter 3 / the `L^p`-space material (strict convexity of `L^p` for
`1 < p < ∞`). This is a companion to the book's parallelogram-law proposition
and its `L^p`-norm material, not one of the numbered `v1` targets.

## Main declarations

* `lpTwoPlus`, `lpTwoMinus` : the vectors `(1, 1)` and `(1, -1)` in
  `PiLp p (Fin 2 → ℝ)`.
* `parallelogram_eq_iff_piLp_two` : the parallelogram identity for these two
  vectors holds iff `p = 2`.
* `not_innerProductSpace_piLp_two` : for `p ≠ 2`, no `InnerProductSpace ℝ`
  instance on `PiLp p (Fin 2 → ℝ)` induces the `ℓ^p` norm.
* `piLp_two_strictConvex` : for `1 < p < ∞`, the midpoint of two distinct
  unit vectors in `PiLp p (Fin 2 → ℝ)` has norm `< 1`.
* `strictConvexSpace_piLp_two` : the corresponding standard `StrictConvexSpace` instance.
* `not_strictConvex_piLp_two_one`, `not_strictConvex_piLp_two_top` :
  strict convexity fails at the endpoints `p = 1` and `p = ∞`.
* `not_strictConvexSpace_piLp_two_one`, `not_strictConvexSpace_piLp_two_top` :
  those endpoint failures as negations of the standard class.
-/

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.LpGeometry

variable {p : ENNReal} [Fact (1 ≤ p)]

/-- Positivity of `p.toReal` from `1 ≤ p`; used for the finite-`p` norm formula. -/
private theorem toReal_pos_of_fact (hp : p ≠ ⊤) : 0 < p.toReal := by
  rw [ENNReal.toReal_pos_iff]
  exact ⟨(show (0 : ENNReal) < 1 from zero_lt_one).trans_le Fact.out,
    lt_top_iff_ne_top.mpr hp⟩

/-- **The vector $(1, 1)$ in $\ell^p_2$.** For $p \in [0, \infty]$, write $\ell^p_2$ for the
space $\mathbb{R}^2$ regarded as the $\ell^p$ product of two copies of $\mathbb{R}$ (normed by the
$\ell^p$ norm when $p \ge 1$). The vector $u_p \in \ell^p_2$ is $(1, 1)$, that is, $e_0 + e_1$,
where $e_0 = (1, 0)$ and $e_1 = (0, 1)$ are the standard basis vectors. -/
noncomputable def lpTwoPlus (p : ENNReal) : PiLp p (fun _ : Fin 2 => ℝ) :=
  PiLp.single p 0 1 + PiLp.single p 1 1

/-- **The vector $(1, -1)$ in $\ell^p_2$.** For $p \in [0, \infty]$, write $\ell^p_2$ for the
space $\mathbb{R}^2$ regarded as the $\ell^p$ product of two copies of $\mathbb{R}$ (normed by the
$\ell^p$ norm when $p \ge 1$). The vector $v_p \in \ell^p_2$ is $(1, -1)$, that is, $e_0 - e_1$,
where $e_0 = (1, 0)$ and $e_1 = (0, 1)$ are the standard basis vectors. -/
noncomputable def lpTwoMinus (p : ENNReal) : PiLp p (fun _ : Fin 2 => ℝ) :=
  PiLp.single p 0 1 - PiLp.single p 1 1

omit [Fact (1 ≤ p)] in
theorem lpTwoPlus_apply_zero : lpTwoPlus p 0 = 1 := by
  simp [lpTwoPlus]

omit [Fact (1 ≤ p)] in
theorem lpTwoPlus_apply_one : lpTwoPlus p 1 = 1 := by
  simp [lpTwoPlus]

omit [Fact (1 ≤ p)] in
theorem lpTwoMinus_apply_zero : lpTwoMinus p 0 = 1 := by
  simp [lpTwoMinus]

omit [Fact (1 ≤ p)] in
theorem lpTwoMinus_apply_one : lpTwoMinus p 1 = -1 := by
  simp [lpTwoMinus]

omit [Fact (1 ≤ p)] in
/-- **Sum of $(1, 1)$ and $(1, -1)$ in $\ell^p_2$.** For every $p \in [0, \infty]$, write $\ell^p_2$
for the space $\mathbb{R}^2$ regarded as the $\ell^p$ product of two copies of $\mathbb{R}$. The
vectors $u_p = (1, 1)$ and $v_p = (1, -1)$ of $\ell^p_2$ satisfy $u_p + v_p = 2 e_0$, where
$e_0 = (1, 0)$ is the first standard basis vector. -/
theorem lpTwoPlus_add_lpTwoMinus :
    lpTwoPlus p + lpTwoMinus p = (2 : ℝ) • PiLp.single p 0 (1 : ℝ) := by
  show (PiLp.single p 0 1 + PiLp.single p 1 1) + (PiLp.single p 0 1 - PiLp.single p 1 1) = _
  module

omit [Fact (1 ≤ p)] in
/-- **Difference of $(1, 1)$ and $(1, -1)$ in $\ell^p_2$.** For every $p \in [0, \infty]$, write
$\ell^p_2$ for the space $\mathbb{R}^2$ regarded as the $\ell^p$ product of two copies of
$\mathbb{R}$. The vectors $u_p = (1, 1)$ and $v_p = (1, -1)$ of $\ell^p_2$ satisfy
$u_p - v_p = 2 e_1$, where $e_1 = (0, 1)$ is the second standard basis vector. -/
theorem lpTwoPlus_sub_lpTwoMinus :
    lpTwoPlus p - lpTwoMinus p = (2 : ℝ) • PiLp.single p 1 (1 : ℝ) := by
  show (PiLp.single p 0 1 + PiLp.single p 1 1) - (PiLp.single p 0 1 - PiLp.single p 1 1) = _
  module

/-- **Norm of $(1, 1) + (1, -1)$ in $\ell^p_2$.** For every $p \in [1, \infty]$, let $\ell^p_2$ be
$\mathbb{R}^2$ with the $\ell^p$ norm, and let $u_p = (1, 1)$ and $v_p = (1, -1)$. Then
$\|u_p + v_p\| = 2$. -/
theorem norm_add_lpTwo : ‖lpTwoPlus p + lpTwoMinus p‖ = 2 := by
  rw [lpTwoPlus_add_lpTwoMinus, norm_smul, PiLp.norm_single]
  norm_num

/-- **The difference of the parallelogram witnesses has norm two.** For every extended real
$p \in [1, \infty]$, in $\mathbb{R}^2$ with the $\ell^p$ norm the vectors $u = (1, 1)$ and
$v = (1, -1)$ satisfy $\|u - v\| = 2$. -/
theorem norm_sub_lpTwo : ‖lpTwoPlus p - lpTwoMinus p‖ = 2 := by
  rw [lpTwoPlus_sub_lpTwoMinus, norm_smul, PiLp.norm_single]
  norm_num

/-- **The $\ell^p$ norm of $(1, 1)$ for finite $p$.** For every real $p$ with $1 \le p < \infty$,
the vector $(1, 1)$ of $\mathbb{R}^2$ has $\ell^p$ norm $\|(1, 1)\|_p = 2^{1/p}$, where
$\|(x, y)\|_p = (|x|^p + |y|^p)^{1/p}$. -/
theorem norm_lpTwoPlus_of_ne_top (hp : p ≠ ⊤) :
    ‖lpTwoPlus p‖ = (2 : ℝ) ^ (1 / p.toReal) := by
  have hq : 0 < p.toReal := toReal_pos_of_fact hp
  rw [PiLp.norm_eq_sum hq]
  congr 1
  rw [Fin.sum_univ_two, lpTwoPlus_apply_zero, lpTwoPlus_apply_one]
  norm_num [norm_one, Real.one_rpow]

/-- **The $\ell^p$ norm of $(1, -1)$ for finite $p$.** For every real $p$ with $1 \le p < \infty$,
the vector $(1, -1)$ of $\mathbb{R}^2$ has $\ell^p$ norm $\|(1, -1)\|_p = 2^{1/p}$, where
$\|(x, y)\|_p = (|x|^p + |y|^p)^{1/p}$. -/
theorem norm_lpTwoMinus_of_ne_top (hp : p ≠ ⊤) :
    ‖lpTwoMinus p‖ = (2 : ℝ) ^ (1 / p.toReal) := by
  have hq : 0 < p.toReal := toReal_pos_of_fact hp
  rw [PiLp.norm_eq_sum hq]
  congr 1
  rw [Fin.sum_univ_two, lpTwoMinus_apply_zero, lpTwoMinus_apply_one]
  norm_num [norm_one, norm_neg, Real.one_rpow]

/-- **The $\ell^\infty$ norm of $(1, 1)$.** In $\mathbb{R}^2$ with the $\ell^\infty$ norm
$\|(x, y)\|_\infty = \max(|x|, |y|)$, the vector $(1, 1)$ has norm $\|(1, 1)\|_\infty = 1$. -/
theorem norm_lpTwoPlus_top : ‖lpTwoPlus (⊤ : ENNReal)‖ = 1 := by
  have hcoord : ∀ i : Fin 2, ‖lpTwoPlus (⊤ : ENNReal) i‖ = 1 := by
    intro i
    fin_cases i <;> simp [lpTwoPlus_apply_zero, lpTwoPlus_apply_one]
  rw [PiLp.norm_eq_ciSup]
  simp [hcoord]

/-- **The $\ell^\infty$ norm of $(1, -1)$.** In $\mathbb{R}^2$ with the $\ell^\infty$ norm
$\|(x, y)\|_\infty = \max(|x|, |y|)$, the vector $(1, -1)$ has norm $\|(1, -1)\|_\infty = 1$. -/
theorem norm_lpTwoMinus_top : ‖lpTwoMinus (⊤ : ENNReal)‖ = 1 := by
  have hcoord : ∀ i : Fin 2, ‖lpTwoMinus (⊤ : ENNReal) i‖ = 1 := by
    intro i
    fin_cases i <;> simp [lpTwoMinus_apply_zero, lpTwoMinus_apply_one]
  rw [PiLp.norm_eq_ciSup]
  simp [hcoord]

/-- **The squared $\ell^p$ norm of $(1, 1)$ for finite $p$.** For every real $p$ with
$1 \le p < \infty$, the vector $(1, 1)$ of $\mathbb{R}^2$ satisfies $\|(1, 1)\|_p^2 = 2^{2/p}$,
where $\|(x, y)\|_p = (|x|^p + |y|^p)^{1/p}$ is the $\ell^p$ norm. -/
theorem norm_sq_lpTwoPlus_of_ne_top (hp : p ≠ ⊤) :
    ‖lpTwoPlus p‖ ^ 2 = (2 : ℝ) ^ ((2 : ℝ) / p.toReal) := by
  have hq : 0 < p.toReal := toReal_pos_of_fact hp
  calc ‖lpTwoPlus p‖ ^ 2 = ((2 : ℝ) ^ (1 / p.toReal)) ^ 2 := by
        rw [norm_lpTwoPlus_of_ne_top hp]
    _ = (2 : ℝ) ^ ((1 / p.toReal) * (2 : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_cast
    _ = (2 : ℝ) ^ ((2 : ℝ) / p.toReal) := by
        congr 1
        field_simp

/-- **The parallelogram law for $(1, 1)$ and $(1, -1)$ holds only for the $\ell^2$ norm.** Let
$p \in [1, \infty]$ and equip $\mathbb{R}^2$ with the $\ell^p$ norm. The vectors $u = (1, 1)$ and
$v = (1, -1)$ satisfy $\|u + v\|^2 + \|u - v\|^2 = 2 (\|u\|^2 + \|v\|^2)$ if and only if
$p = 2$. -/
theorem parallelogram_eq_iff_piLp_two :
    ‖lpTwoPlus p + lpTwoMinus p‖ ^ 2 + ‖lpTwoPlus p - lpTwoMinus p‖ ^ 2 =
        2 * (‖lpTwoPlus p‖ ^ 2 + ‖lpTwoMinus p‖ ^ 2) ↔ p = 2 := by
  constructor
  · intro h
    by_cases htop : p = ⊤
    · subst htop
      rw [norm_add_lpTwo, norm_sub_lpTwo, norm_lpTwoPlus_top, norm_lpTwoMinus_top] at h
      norm_num at h
    · have h2 : ‖lpTwoPlus p‖ ^ 2 = 2 := by
        have hLHS : ‖lpTwoPlus p + lpTwoMinus p‖ ^ 2 +
            ‖lpTwoPlus p - lpTwoMinus p‖ ^ 2 = 8 := by
          rw [norm_add_lpTwo, norm_sub_lpTwo]
          norm_num
        have hnorms : ‖lpTwoMinus p‖ = ‖lpTwoPlus p‖ := by
          rw [norm_lpTwoPlus_of_ne_top htop, norm_lpTwoMinus_of_ne_top htop]
        rw [hLHS, hnorms] at h
        linarith
      rw [norm_sq_lpTwoPlus_of_ne_top htop] at h2
      have hq : 0 < p.toReal := toReal_pos_of_fact htop
      have hexp : (2 : ℝ) / p.toReal = 1 := by
        have h3 : (2 : ℝ) ^ ((2 : ℝ) / p.toReal) = (2 : ℝ) ^ (1 : ℝ) := by
          rw [h2, Real.rpow_one]
        exact (Real.rpow_right_inj (by norm_num : (0 : ℝ) < 2)
          (by norm_num : (2 : ℝ) ≠ 1)).mp h3
      have hq2 : p.toReal = 2 := by
        field_simp at hexp
        linarith
      rw [← ENNReal.toReal_eq_toReal_iff' htop (by simp : (2 : ENNReal) ≠ ⊤)]
      rw [hq2]
      simp
  · rintro rfl
    exact parallelogram_law_with_norm ℝ _ _

/-- **The parallelogram law fails on $\mathbb{R}^2$ with the $\ell^p$ norm for $p \neq 2$.** Let
$p \in [1, \infty]$ with $p \neq 2$ and equip $\mathbb{R}^2$ with the $\ell^p$ norm. Then the
vectors $u = (1, 1)$ and $v = (1, -1)$ satisfy
$\|u + v\|^2 + \|u - v\|^2 \neq 2 (\|u\|^2 + \|v\|^2)$. -/
theorem parallelogram_fails_piLp_two (hp : p ≠ 2) :
    ‖lpTwoPlus p + lpTwoMinus p‖ ^ 2 + ‖lpTwoPlus p - lpTwoMinus p‖ ^ 2 ≠
      2 * (‖lpTwoPlus p‖ ^ 2 + ‖lpTwoMinus p‖ ^ 2) :=
  fun h => hp (parallelogram_eq_iff_piLp_two.mp h)

/-- **The $\ell^p$ norm on $\mathbb{R}^2$ comes from no inner product unless $p = 2$.** Let
$p \in [1, \infty]$ with $p \neq 2$. Then the normed space $\mathbb{R}^2$ with the $\ell^p$ norm
carries no real inner product space structure, that is, there is no real inner product with
$\langle x, x \rangle = \|x\|^2$ for every $x$.

Any such inner product would satisfy the parallelogram law, which fails for $(1, 1)$ and
$(1, -1)$. -/
theorem not_innerProductSpace_piLp_two (hp : p ≠ 2) :
    ¬ Nonempty (InnerProductSpace ℝ (PiLp p (fun _ : Fin 2 => ℝ))) := by
  rintro ⟨inst⟩
  exact parallelogram_fails_piLp_two hp
    (@parallelogram_law_with_norm ℝ _ _ _ inst (lpTwoPlus p) (lpTwoMinus p))

/-- Pointwise convexity estimate for `t ↦ |t| ^ q` at the midpoint. -/
private theorem abs_add_div_two_rpow_le {q : ℝ} (hq : 1 < q) (a b : ℝ) :
    |(a + b) / 2| ^ q ≤ (|a| ^ q + |b| ^ q) / 2 := by
  have htri : |(a + b) / 2| ≤ (|a| + |b|) / 2 := by
    have h := abs_add_le a b
    rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
    linarith
  have hconv := (convexOn_rpow hq.le).2
    (Set.mem_Ici.mpr (abs_nonneg a)) (Set.mem_Ici.mpr (abs_nonneg b))
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  calc |(a + b) / 2| ^ q ≤ ((|a| + |b|) / 2) ^ q :=
        Real.rpow_le_rpow (abs_nonneg _) htri (zero_lt_one.trans hq).le
    _ = ((1 / 2 : ℝ) • |a| + (1 / 2 : ℝ) • |b|) ^ q := by
        congr 1
        simp [smul_eq_mul]
        ring_nf
    _ ≤ (1 / 2 : ℝ) • |a| ^ q + (1 / 2 : ℝ) • |b| ^ q := hconv
    _ = (|a| ^ q + |b| ^ q) / 2 := by
        simp [smul_eq_mul]
        ring_nf

/-- Pointwise strict convexity estimate for `t ↦ |t| ^ q` at the midpoint. -/
private theorem abs_add_div_two_rpow_lt {q : ℝ} (hq : 1 < q) {a b : ℝ} (hab : a ≠ b) :
    |(a + b) / 2| ^ q < (|a| ^ q + |b| ^ q) / 2 := by
  by_cases habs : |a| = |b|
  · rcases abs_eq_abs.mp habs with hEq | hNeg
    · exact absurd hEq hab
    · have hb : b = -a := by rw [hNeg]; simp
      subst hb
      have ha : a ≠ 0 := by
        rintro rfl
        exact hab neg_zero.symm
      have hLHS : |(a + -a) / 2| ^ q = 0 := by
        rw [add_neg_cancel, zero_div, abs_zero]
        exact Real.zero_rpow (zero_lt_one.trans hq).ne'
      rw [hLHS]
      have hpos : 0 < |a| ^ q := Real.rpow_pos_of_pos (abs_pos.mpr ha) q
      have hbabs : |-a| ^ q = |a| ^ q := by rw [abs_neg]
      rw [hbabs]
      linarith
  · have htri : |(a + b) / 2| ≤ (|a| + |b|) / 2 := by
      have h := abs_add_le a b
      rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
      linarith
    have hconv := (strictConvexOn_rpow hq).2
      (Set.mem_Ici.mpr (abs_nonneg a)) (Set.mem_Ici.mpr (abs_nonneg b)) habs
      (show (0 : ℝ) < 1 / 2 by norm_num) (show (0 : ℝ) < 1 / 2 by norm_num)
      (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
    calc |(a + b) / 2| ^ q ≤ ((|a| + |b|) / 2) ^ q :=
          Real.rpow_le_rpow (abs_nonneg _) htri (zero_lt_one.trans hq).le
      _ = ((1 / 2 : ℝ) • |a| + (1 / 2 : ℝ) • |b|) ^ q := by
          congr 1
          simp [smul_eq_mul]
          ring_nf
      _ < (1 / 2 : ℝ) • |a| ^ q + (1 / 2 : ℝ) • |b| ^ q := hconv
      _ = (|a| ^ q + |b| ^ q) / 2 := by
          simp [smul_eq_mul]
          ring_nf

/-- For a unit vector in `PiLp p (Fin 2 → ℝ)`, the sum of the `p`-th powers of
the coordinate norms is `1`. -/
private theorem sum_norm_rpow_eq_one_of_norm_eq_one (hp : p ≠ ⊤)
    {z : PiLp p (fun _ : Fin 2 => ℝ)} (hz : ‖z‖ = 1) :
    ∑ i, ‖z i‖ ^ p.toReal = 1 := by
  have hq : 0 < p.toReal := toReal_pos_of_fact hp
  have hS : 0 ≤ ∑ i, ‖z i‖ ^ p.toReal :=
    Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _
  have h1 : (∑ i, ‖z i‖ ^ p.toReal) ^ (1 / p.toReal) = 1 := by
    rw [← PiLp.norm_eq_sum hq]
    exact hz
  have h2 := congrArg (fun t => t ^ p.toReal) h1
  simp only [← Real.rpow_mul hS, one_div, inv_mul_cancel₀ hq.ne', Real.rpow_one,
    Real.one_rpow] at h2
  exact h2

/-- **Midpoints of distinct $\ell^p$ unit vectors in $\mathbb{R}^2$ have norm less than one.**
Let $1 < p < \infty$ and equip $\mathbb{R}^2$ with the $\ell^p$ norm. If $x \neq y$ are vectors
with $\|x\| = \|y\| = 1$, then $\|\tfrac{1}{2} (x + y)\| < 1$. -/
theorem piLp_two_strictConvex (hp1 : 1 < p.toReal) (hp : p ≠ ⊤)
    (x y : PiLp p (fun _ : Fin 2 => ℝ)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : x ≠ y) :
    ‖(1 / 2 : ℝ) • (x + y)‖ < 1 := by
  have hq : 0 < p.toReal := lt_trans zero_lt_one hp1
  obtain ⟨i0, hi0⟩ : ∃ i, x i ≠ y i := by
    by_contra hcon
    exact hxy (PiLp.ext fun i => by by_contra hi; exact hcon ⟨i, hi⟩)
  have hle : ∀ i : Fin 2, |(x i + y i) / 2| ^ p.toReal ≤
      (‖x i‖ ^ p.toReal + ‖y i‖ ^ p.toReal) / 2 := by
    intro i
    have h := abs_add_div_two_rpow_le hp1 (x i) (y i)
    simpa only [Real.norm_eq_abs] using h
  have hlt : |(x i0 + y i0) / 2| ^ p.toReal <
      (‖x i0‖ ^ p.toReal + ‖y i0‖ ^ p.toReal) / 2 := by
    have h := abs_add_div_two_rpow_lt hp1 hi0
    simpa only [Real.norm_eq_abs] using h
  have hsum : ∑ i, |(x i + y i) / 2| ^ p.toReal < 1 := by
    calc ∑ i, |(x i + y i) / 2| ^ p.toReal
        < ∑ i, (‖x i‖ ^ p.toReal + ‖y i‖ ^ p.toReal) / 2 :=
          Finset.sum_lt_sum (fun i _ => hle i) ⟨i0, Finset.mem_univ _, hlt⟩
      _ = (∑ i, ‖x i‖ ^ p.toReal + ∑ i, ‖y i‖ ^ p.toReal) / 2 := by
          rw [← Finset.sum_div, ← Finset.sum_add_distrib]
      _ = 1 := by
          rw [sum_norm_rpow_eq_one_of_norm_eq_one hp hx,
            sum_norm_rpow_eq_one_of_norm_eq_one hp hy]
          norm_num
  have hnorm : ‖(1 / 2 : ℝ) • (x + y)‖ =
      (∑ i, |(x i + y i) / 2| ^ p.toReal) ^ (1 / p.toReal) := by
    rw [PiLp.norm_eq_sum hq]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [PiLp.smul_apply, PiLp.add_apply, Real.norm_eq_abs, smul_eq_mul]
    congr 1
    ring_nf
  rw [hnorm]
  calc (∑ i, |(x i + y i) / 2| ^ p.toReal) ^ (1 / p.toReal)
      < (1 : ℝ) ^ (1 / p.toReal) :=
        Real.rpow_lt_rpow (Finset.sum_nonneg fun i _ =>
          Real.rpow_nonneg (abs_nonneg _) _) hsum (by positivity)
    _ = 1 := Real.one_rpow _

/-- **$\mathbb{R}^2$ with the $\ell^p$ norm is strictly convex for $1 < p < \infty$.** For
$1 < p < \infty$, the real normed space $\mathbb{R}^2$ with the $\ell^p$ norm is a strictly
convex space: every closed ball of positive radius centred at the origin is a strictly convex
set. -/
theorem strictConvexSpace_piLp_two (hp1 : 1 < p.toReal) (hp : p ≠ ⊤) :
    StrictConvexSpace ℝ (PiLp p (fun _ : Fin 2 => ℝ)) := by
  apply StrictConvexSpace.of_norm_combo_lt_one
  intro x y hx hy hxy
  refine ⟨1 / 2, 1 / 2, by norm_num, ?_⟩
  simpa only [smul_add] using piLp_two_strictConvex hp1 hp x y hx hy hxy

/-- **Two distinct $\ell^1$ unit vectors in $\mathbb{R}^2$ with a unit midpoint.** In
$\mathbb{R}^2$ with the $\ell^1$ norm there exist vectors $x \neq y$ with $\|x\| = \|y\| = 1$
and $\|\tfrac{1}{2} (x + y)\| = 1$.

For example, the unit vectors $(1, 0)$ and $(0, 1)$ have midpoint $(1/2, 1/2)$ of norm $1$. -/
theorem not_strictConvex_piLp_two_one :
    ∃ x y : PiLp (1 : ENNReal) (fun _ : Fin 2 => ℝ), ‖x‖ = 1 ∧ ‖y‖ = 1 ∧ x ≠ y ∧
      ‖(1 / 2 : ℝ) • (x + y)‖ = 1 := by
  have hfact : Fact (1 ≤ (1 : ENNReal)) := ⟨le_rfl⟩
  refine ⟨PiLp.single 1 0 1, PiLp.single 1 1 1, ?_, ?_, ?_, ?_⟩
  · simp [PiLp.norm_single]
  · simp [PiLp.norm_single]
  · intro h
    have h1 := congrArg (fun z : PiLp (1 : ENNReal) (fun _ : Fin 2 => ℝ) => z (1 : Fin 2)) h
    simp only [PiLp.single_eq_same] at h1
    norm_num at h1
  · show ‖(1 / 2 : ℝ) • lpTwoPlus (1 : ENNReal)‖ = 1
    have h1top : (1 : ENNReal) ≠ ⊤ := by simp
    rw [norm_smul, norm_lpTwoPlus_of_ne_top h1top]
    norm_num [ENNReal.toReal_one, Real.rpow_one]

/-- **$\mathbb{R}^2$ with the $\ell^1$ norm is not strictly convex.** The real normed space
$\mathbb{R}^2$ with the $\ell^1$ norm is not a strictly convex space: not every closed ball of
positive radius centred at the origin is a strictly convex set. -/
theorem not_strictConvexSpace_piLp_two_one :
    ¬ StrictConvexSpace ℝ (PiLp (1 : ENNReal) (fun _ : Fin 2 => ℝ)) := by
  intro h
  let _ := h
  obtain ⟨x, y, hx, hy, hxy, hmid⟩ := not_strictConvex_piLp_two_one
  have hlt := (norm_midpoint_lt_iff (x := x) (y := y) (hx.trans hy.symm)).2 hxy
  exact hlt.ne (hmid.trans hx.symm)

/-- **Two distinct $\ell^\infty$ unit vectors in $\mathbb{R}^2$ with a unit midpoint.** In
$\mathbb{R}^2$ with the $\ell^\infty$ norm there exist vectors $x \neq y$ with
$\|x\| = \|y\| = 1$ and $\|\tfrac{1}{2} (x + y)\| = 1$.

For example, the unit vectors $(1, 1)$ and $(1, -1)$ have midpoint $(1, 0)$ of norm $1$. -/
theorem not_strictConvex_piLp_two_top :
    ∃ x y : PiLp (⊤ : ENNReal) (fun _ : Fin 2 => ℝ), ‖x‖ = 1 ∧ ‖y‖ = 1 ∧ x ≠ y ∧
      ‖(1 / 2 : ℝ) • (x + y)‖ = 1 := by
  have hfact : Fact (1 ≤ (⊤ : ENNReal)) := ⟨le_top⟩
  refine ⟨lpTwoPlus ⊤, lpTwoMinus ⊤, ?_, ?_, ?_, ?_⟩
  · exact norm_lpTwoPlus_top
  · exact norm_lpTwoMinus_top
  · intro h
    have h1 : lpTwoPlus (⊤ : ENNReal) 1 = lpTwoMinus (⊤ : ENNReal) 1 := by rw [h]
    rw [lpTwoPlus_apply_one, lpTwoMinus_apply_one] at h1
    norm_num at h1
  · have hsum : lpTwoPlus (⊤ : ENNReal) + lpTwoMinus (⊤ : ENNReal) =
        (2 : ℝ) • PiLp.single (⊤ : ENNReal) 0 (1 : ℝ) := lpTwoPlus_add_lpTwoMinus
    rw [hsum, smul_smul]
    norm_num [PiLp.norm_single]

/-- **$\mathbb{R}^2$ with the $\ell^\infty$ norm is not strictly convex.** The real normed space
$\mathbb{R}^2$ with the $\ell^\infty$ norm is not a strictly convex space: not every closed ball
of positive radius centred at the origin is a strictly convex set. -/
theorem not_strictConvexSpace_piLp_two_top :
    ¬ StrictConvexSpace ℝ (PiLp (⊤ : ENNReal) (fun _ : Fin 2 => ℝ)) := by
  intro h
  let _ := h
  obtain ⟨x, y, hx, hy, hxy, hmid⟩ := not_strictConvex_piLp_two_top
  have hlt := (norm_midpoint_lt_iff (x := x) (y := y) (hx.trans hy.symm)).2 hxy
  exact hlt.ne (hmid.trans hx.symm)

end MathlibExt.Analysis.FunctionalAnalysis.LpGeometry
