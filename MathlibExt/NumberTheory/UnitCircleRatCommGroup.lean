/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PythagoreanTripleGroups
import Mathlib.NumberTheory.PythagoreanTriples

/-!
# Amato's group law on rational points of the unit circle

Amato's product makes the rational unit-circle points with nonzero first coordinate
an infinite commutative group.
-/

namespace MetaMathlibExt

namespace unitCircleRat_commGroup

private def points : Set (ℚ × ℚ) :=
  {p | p.1 ≠ 0 ∧ p.1 ^ 2 + p.2 ^ 2 = 1}

private theorem denominator_ne_zero {p q : ℚ × ℚ} (hp : p ∈ points) (hq : q ∈ points) :
    1 + p.2 * q.2 ≠ 0 := by
  apply ne_of_gt
  -- Twice the denominator is the sum of the squares of both first coordinates and of p.2 + q.2.
  nlinarith only [hp.2, hq.2, sq_pos_of_ne_zero hp.1, sq_nonneg q.1, sq_nonneg (p.2 + q.2)]

private theorem mul_mem {p q : ℚ × ℚ} (hp : p ∈ points) (hq : q ∈ points) :
    unitCircleRatMul p q ∈ points := by
  have hd := denominator_ne_zero hp hq
  refine ⟨div_ne_zero (mul_ne_zero hp.1 hq.1) hd, ?_⟩
  dsimp only [unitCircleRatMul]
  rw [div_pow, div_pow, ← add_div]
  apply (div_eq_iff (pow_ne_zero 2 hd)).2
  rw [mul_pow, eq_sub_of_add_eq hp.2, eq_sub_of_add_eq hq.2]
  ring

private theorem mul_assoc {p q r : ℚ × ℚ} (hp : p ∈ points) (hq : q ∈ points) (hr : r ∈ points) :
    unitCircleRatMul (unitCircleRatMul p q) r = unitCircleRatMul p (unitCircleRatMul q r) := by
  have hpq := denominator_ne_zero hp hq
  have hqr := denominator_ne_zero hq hr
  have h₁ := denominator_ne_zero (mul_mem hp hq) hr
  have h₂ := denominator_ne_zero hp (mul_mem hq hr)
  simp only [unitCircleRatMul] at h₁ h₂
  simp only [unitCircleRatMul, Prod.mk.injEq]
  constructor <;> field_simp <;> ring

private theorem mul_inv {p : ℚ × ℚ} (hp : p ∈ points) :
    unitCircleRatMul p (p.1, -p.2) = (1, 0) := by
  have hd : 1 + p.2 * -p.2 = p.1 ^ 2 := by nlinarith only [hp.2]
  simp only [unitCircleRatMul, hd, ← pow_two, add_neg_cancel, zero_div]
  rw [div_self (pow_ne_zero 2 hp.1)]

private theorem infinite_points : points.Infinite := by
  have hden (t : ℚ) : 1 + t ^ 2 ≠ 0 := by positivity
  let e := circleEquivGen hden
  let f (t : ℚ) : ℚ × ℚ := e t
  have hf : Function.Injective f := fun _ _ h => e.injective (Subtype.ext h)
  refine Set.infinite_of_injOn_mapsTo hf.injOn (s := ({0} : Set ℚ)ᶜ) ?_ ?_
  · intro t ht
    have ht₀ : t ≠ 0 := by simpa using ht
    refine ⟨?_, (e t).2.1⟩
    change (e t : ℚ × ℚ).1 ≠ 0
    simp only [e, circleEquivGen_apply]
    exact div_ne_zero (mul_ne_zero (by norm_num) ht₀) (hden t)
  · exact (Set.finite_singleton 0).infinite_compl

end unitCircleRat_commGroup

/-- **Amato's group law on rational points of the unit circle.** Let
$P = \{(x, y) \in \mathbb{Q}^2 : x \neq 0,\ x^2 + y^2 = 1\}$ and let $\odot$ be Amato's product
$(x, y) \odot (x', y') = (x x' / (1 + y y'), (y + y') / (1 + y y'))$. Then $(1, 0) \in P$; for all
$p, q \in P$ we have $p \odot q \in P$; $\odot$ is associative and commutative on $P$; for every
$(x, y) \in P$ we have $(x, y) \odot (1, 0) = (x, y)$ and $(x, y) \odot (x, -y) = (1, 0)$; and $P$
is infinite.

$P$ is the set of points $(a/c, b/c)$ coming from primitive Pythagorean triples $(a, b, c)$ with
$a \neq 0$: writing a rational point of the unit circle over its reduced common denominator gives
a primitive triple. Rules (II) and (III) of (14) in the source concern fraction representatives
and hold automatically in $\mathbb{Q}$.

Source: Roberto Amato, *Groups and Monoid in the Set of Pythagorean Triples*, INTEGERS 24 (2024),
Article A5, Theorem 4 (`integers-2024-A5-thm-4`). -/
public theorem unitCircleRat_commGroup :
    let P : Set (ℚ × ℚ) := {p | p.1 ≠ 0 ∧ p.1 ^ 2 + p.2 ^ 2 = 1}
    (1, 0) ∈ P ∧
      (∀ p ∈ P, ∀ q ∈ P, unitCircleRatMul p q ∈ P) ∧
      (∀ p ∈ P, ∀ q ∈ P, ∀ r ∈ P,
        unitCircleRatMul (unitCircleRatMul p q) r = unitCircleRatMul p (unitCircleRatMul q r)) ∧
      (∀ p ∈ P, ∀ q ∈ P, unitCircleRatMul p q = unitCircleRatMul q p) ∧
      (∀ p ∈ P, unitCircleRatMul p (1, 0) = p) ∧
      (∀ p ∈ P, unitCircleRatMul p (p.1, -p.2) = (1, 0)) ∧
      P.Infinite := by
  dsimp only
  refine ⟨⟨by norm_num, by norm_num⟩, fun _ hp _ hq => unitCircleRat_commGroup.mul_mem hp hq,
    fun _ hp _ hq _ hr => unitCircleRat_commGroup.mul_assoc hp hq hr, ?_, ?_,
    fun _ hp => unitCircleRat_commGroup.mul_inv hp, unitCircleRat_commGroup.infinite_points⟩
  · intro p _ q _
    simp only [unitCircleRatMul, mul_comm p.1 q.1, mul_comm p.2 q.2, add_comm p.2 q.2]
  · rintro ⟨x, y⟩ -
    simp [unitCircleRatMul]

end MetaMathlibExt
