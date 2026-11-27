/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.DirichletCharacter.Quadratic
public import MathlibExt.NumberTheory.QuadraticForms.Reduced
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Set.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Coefficient bounds and values of reduced binary quadratic forms

For a Gauss-reduced positive definite binary quadratic form $q(x, y) = ax^2 + bxy + cy^2$ with
$d = 4ac - b^2$, this file proves the bounds
$$a \le \sqrt{d/3}, \qquad \frac{\sqrt d}{2} \le c \le \frac{d}{3a},$$
the strict bound $c > \sqrt d / 2$ when $d$ is not four times a square (in particular when $-d$ is
a fundamental discriminant and $d \ne 4$), and the lower bound $q(m, n) \ge c$ for all integers
$m, n$ with $n \ne 0$. Consequently the number of pairs $(m, n) \in \mathbb{Z} \times
\mathbb{Z}_{\ge 1}$ with $q(m, n) \le t$ is $0$ for $t < c$, and so for $t < \sqrt d / 2$.

Source: J. Oesterlé, *Nombres de classes des corps quadratiques imaginaires*, Séminaire Bourbaki,
vol. 1983/84, exposé 631, Astérisque 121–122 (1985), 309–323, §1.3 (p. 312).
-/

@[expose] public section

namespace BinaryQuadraticForm

variable {a b c : ℤ}

/-- For a Gauss-reduced form, $4ac - b^2 \ge 3ac$. -/
theorem IsGaussReduced.three_mul_le_discr (h : IsGaussReduced a b c) :
    3 * a * c ≤ 4 * a * c - b ^ 2 := by
  have hb : b ^ 2 ≤ a ^ 2 := by
    have := sq_le_sq' h.neg_le h.le_of_abs_le
    simpa using this
  have hac : a ^ 2 ≤ a * c := by nlinarith [h.pos, h.le]
  nlinarith

/-- For a Gauss-reduced form, $3a^2 \le 4ac - b^2$. -/
theorem IsGaussReduced.three_mul_sq_le_discr (h : IsGaussReduced a b c) :
    3 * a ^ 2 ≤ 4 * a * c - b ^ 2 := by
  have := h.three_mul_le_discr
  nlinarith [h.pos, h.le]

/-- For a Gauss-reduced form, $4ac - b^2 \le 4c^2$. -/
theorem IsGaussReduced.discr_le_four_mul_sq (h : IsGaussReduced a b c) :
    4 * a * c - b ^ 2 ≤ 4 * c ^ 2 := by
  have hc : 0 < c := lt_of_lt_of_le h.pos h.le
  nlinarith [sq_nonneg b, h.le]

/-- For a Gauss-reduced form, $4ac - b^2 = 4c^2$ forces $b = 0$ and $a = c$. -/
theorem IsGaussReduced.eq_of_discr_eq_four_mul_sq (h : IsGaussReduced a b c)
    (he : 4 * a * c - b ^ 2 = 4 * c ^ 2) : b = 0 ∧ a = c := by
  have hc : 0 < c := lt_of_lt_of_le h.pos h.le
  have hb2 : b ^ 2 = 4 * c * (a - c) := by linarith
  have h1 : 4 * c * (a - c) ≤ 0 := by nlinarith [h.le]
  have hb0 : b ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg b)
  have hb : b = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hb0
  refine ⟨hb, ?_⟩
  have : c * (a - c) = 0 := by nlinarith
  rcases mul_eq_zero.mp this with h2 | h2
  · omega
  · omega

/-- **Coefficient bounds for a reduced positive definite binary quadratic form.**
Let $ax^2 + bxy + cy^2$ be Gauss reduced: $a > 0$, $b^2 - 4ac < 0$, $|b| \le a \le c$, and
$b \ge 0$ whenever $|b| = a$ or $a = c$. Put $d = 4ac - b^2 > 0$. Then
$$a \le \sqrt{d/3}, \qquad \frac{\sqrt d}{2} \le c \le \frac{d}{3a}.$$

Source: J. Oesterlé, *Nombres de classes des corps quadratiques imaginaires*, Séminaire Bourbaki,
vol. 1983/84, exposé 631, Astérisque 121–122 (1985), 309–323, §1.3 (p. 312): "Pour une telle
forme, on a $a \le \sqrt{d/3}$, $\frac{d}{3a} \ge c \ge \frac{\sqrt d}{2}$". -/
theorem IsGaussReduced.coefficient_bounds (h : IsGaussReduced a b c) :
    (0 : ℝ) < ((4 * a * c - b ^ 2 : ℤ) : ℝ) ∧
      (a : ℝ) ≤ √(((4 * a * c - b ^ 2 : ℤ) : ℝ) / 3) ∧
      √((4 * a * c - b ^ 2 : ℤ) : ℝ) / 2 ≤ c ∧
      (c : ℝ) ≤ ((4 * a * c - b ^ 2 : ℤ) : ℝ) / (3 * a) := by
  have ha : (0 : ℝ) < a := by exact_mod_cast h.pos
  have hc : (0 : ℝ) < c := by exact_mod_cast lt_of_lt_of_le h.pos h.le
  have h1 : ((3 * a * c : ℤ) : ℝ) ≤ ((4 * a * c - b ^ 2 : ℤ) : ℝ) := by
    exact_mod_cast h.three_mul_le_discr
  have h2 : ((3 * a ^ 2 : ℤ) : ℝ) ≤ ((4 * a * c - b ^ 2 : ℤ) : ℝ) := by
    exact_mod_cast h.three_mul_sq_le_discr
  have h3 : ((4 * a * c - b ^ 2 : ℤ) : ℝ) ≤ ((4 * c ^ 2 : ℤ) : ℝ) := by
    exact_mod_cast h.discr_le_four_mul_sq
  push_cast at h1 h2 h3
  rw [show ((4 * a * c - b ^ 2 : ℤ) : ℝ) = 4 * (a : ℝ) * c - (b : ℝ) ^ 2 by push_cast; ring]
  have hDpos : 0 < 4 * (a : ℝ) * c - (b : ℝ) ^ 2 := by nlinarith
  refine ⟨hDpos, ?_, ?_, ?_⟩
  · apply Real.le_sqrt_of_sq_le
    linarith
  · rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith
  · rw [le_div_iff₀ (by positivity)]
    linarith

/-- **Strict coefficient bound.** For a Gauss-reduced form $ax^2 + bxy + cy^2$ with
$d = 4ac - b^2$ not of the form $4k^2$ with $k$ an integer, $c > \sqrt d / 2$.

Source: J. Oesterlé, *Nombres de classes des corps quadratiques imaginaires*, Séminaire Bourbaki,
vol. 1983/84, exposé 631, Astérisque 121–122 (1985), 309–323, §1.3 (p. 312), "(et même
$c > \frac{\sqrt d}{2}$ si $d \ne 4$)", stated there for $-d$ the discriminant of an imaginary
quadratic field. -/
theorem IsGaussReduced.sqrt_discr_div_two_lt (h : IsGaussReduced a b c)
    (hd : ¬ ∃ k : ℤ, 4 * a * c - b ^ 2 = 4 * k ^ 2) :
    √((4 * a * c - b ^ 2 : ℤ) : ℝ) / 2 < c := by
  have hc : (0 : ℝ) < c := by exact_mod_cast lt_of_lt_of_le h.pos h.le
  have hne : 4 * a * c - b ^ 2 ≠ 4 * c ^ 2 := fun he => hd ⟨c, he⟩
  have hlt : 4 * a * c - b ^ 2 < 4 * c ^ 2 := lt_of_le_of_ne h.discr_le_four_mul_sq hne
  have hlt' : ((4 * a * c - b ^ 2 : ℤ) : ℝ) < ((4 * c ^ 2 : ℤ) : ℝ) := by exact_mod_cast hlt
  push_cast at hlt'
  rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
  apply (Real.sqrt_lt' (by positivity)).mpr
  push_cast
  nlinarith

/-- A fundamental discriminant of the form $-4k^2$ is $-4$. -/
theorem sq_eq_one_of_isFundamentalDiscriminant_neg_four_mul_sq {k : ℤ}
    (hD : MetaMathlibExt.IsFundamentalDiscriminant (-(4 * k ^ 2))) : k ^ 2 = 1 := by
  rcases hD with ⟨_, hmod⟩ | ⟨m, hm, hsq, _⟩
  · omega
  · have hmk : m = -k ^ 2 := by linarith
    subst hmk
    have hunit : IsUnit k := hsq k ⟨-1, by ring⟩
    rcases Int.isUnit_iff.mp hunit with h1 | h1 <;> subst h1 <;> norm_num

/-- **Strict coefficient bound for fundamental discriminants.** For a Gauss-reduced form
$ax^2 + bxy + cy^2$ such that $-d = b^2 - 4ac$ is a fundamental discriminant and $d \ne 4$,
$c > \sqrt d / 2$. Indeed a fundamental discriminant $-4k^2$ is $4m$ with $m = -k^2$ squarefree,
so $k^2 = 1$ and $d = 4$.

Source: J. Oesterlé, *Nombres de classes des corps quadratiques imaginaires*, Séminaire Bourbaki,
vol. 1983/84, exposé 631, Astérisque 121–122 (1985), 309–323, §1.3 (p. 312), "(et même
$c > \frac{\sqrt d}{2}$ si $d \ne 4$)". -/
theorem IsGaussReduced.sqrt_discr_div_two_lt_of_isFundamentalDiscriminant
    (h : IsGaussReduced a b c) (hD : MetaMathlibExt.IsFundamentalDiscriminant (b ^ 2 - 4 * a * c))
    (hd4 : 4 * a * c - b ^ 2 ≠ 4) :
    √((4 * a * c - b ^ 2 : ℤ) : ℝ) / 2 < c := by
  refine h.sqrt_discr_div_two_lt ?_
  rintro ⟨k, hk⟩
  have hD' : MetaMathlibExt.IsFundamentalDiscriminant (-(4 * k ^ 2)) := by
    have : b ^ 2 - 4 * a * c = -(4 * k ^ 2) := by linarith
    rwa [this] at hD
  have := sq_eq_one_of_isFundamentalDiscriminant_neg_four_mul_sq hD'
  exact hd4 (by rw [hk, this]; norm_num)

/-- **Values of a reduced form off the first axis.** Let $q(x, y) = ax^2 + bxy + cy^2$ be a
Gauss-reduced form with integer coefficients. Then $q(m, n) \ge c$ for all integers $m, n$ with
$n \ne 0$.

Source: J. Oesterlé, *Nombres de classes des corps quadratiques imaginaires*, Séminaire Bourbaki,
vol. 1983/84, exposé 631, Astérisque 121–122 (1985), 309–323, §1.3 (p. 312), where it underlies
"Le nombre $N_q(t)$ des couples $(m,n) \in \mathbb{Z} \times \mathbb{N}^*$ tels que
$q(m,n) \le t$ est nul pour $t < c$". -/
theorem IsGaussReduced.le_eval_of_ne_zero (h : IsGaussReduced a b c) {m n : ℤ} (hn : n ≠ 0) :
    c ≤ a * m ^ 2 + b * m * n + c * n ^ 2 := by
  have ha := h.pos
  have hac := h.le
  have hb := h.abs_le
  have hbmn : -(a * (|m| * |n|)) ≤ b * m * n := by
    have h1 := neg_abs_le (b * m * n)
    rw [abs_mul, abs_mul] at h1
    have h2 : |b| * (|m| * |n|) ≤ a * (|m| * |n|) :=
      mul_le_mul_of_nonneg_right hb (by positivity)
    nlinarith
  have hm2 : m ^ 2 = |m| ^ 2 := (sq_abs m).symm
  have hn2 : n ^ 2 = |n| ^ 2 := (sq_abs n).symm
  have hn1 : 1 ≤ |n| := Int.one_le_abs hn
  have hm0 : 0 ≤ |m| := abs_nonneg m
  rw [hm2, hn2]
  rcases le_or_gt |n| |m| with hle | hlt
  · -- $q(m, n) \ge a|m|(|m| - |n|) + c n^2 \ge c n^2 \ge c$.
    have e1 : 0 ≤ a * |m| * (|m| - |n|) := by
      have : 0 ≤ |m| - |n| := by linarith
      positivity
    have hc : 0 < c := lt_of_lt_of_le ha hac
    have hn2' : 1 ≤ |n| ^ 2 := by nlinarith
    have e2 : c ≤ c * |n| ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hn2' hc.le]
    nlinarith
  · -- $q(m, n) \ge a m^2 + c|n|(|n| - |m|) \ge c$.
    have e1 : a * (|m| * |n|) ≤ c * (|m| * |n|) :=
      mul_le_mul_of_nonneg_right hac (by positivity)
    have e2 : c ≤ c * |n| * (|n| - |m|) := by
      have hc : 0 < c := lt_of_lt_of_le ha hac
      have : 1 ≤ |n| - |m| := by linarith
      have hp : 1 ≤ |n| * (|n| - |m|) := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hp hc.le]
    nlinarith [sq_nonneg |m|]

/-- **No values below $c$ off the first axis.** For a Gauss-reduced form
$q(x, y) = ax^2 + bxy + cy^2$, the set of pairs
$(m, n) \in \mathbb{Z} \times \mathbb{Z}_{\ge 1}$ with $q(m, n) \le t$ is empty for every real
$t < c$; so its cardinality $N_q(t)$ is $0$.

Source: J. Oesterlé, *Nombres de classes des corps quadratiques imaginaires*, Séminaire Bourbaki,
vol. 1983/84, exposé 631, Astérisque 121–122 (1985), 309–323, §1.3 (p. 312): "Le nombre $N_q(t)$
des couples $(m,n) \in \mathbb{Z} \times \mathbb{N}^*$ tels que $q(m,n) \le t$ est nul pour
$t < c$". -/
theorem IsGaussReduced.setOf_eval_le_eq_empty (h : IsGaussReduced a b c) {t : ℝ}
    (ht : t < c) :
    {p : ℤ × ℤ | 1 ≤ p.2 ∧ ((a * p.1 ^ 2 + b * p.1 * p.2 + c * p.2 ^ 2 : ℤ) : ℝ) ≤ t} =
      ∅ := by
  ext ⟨m, n⟩
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_le]
  intro hn
  have hle := h.le_eval_of_ne_zero (m := m) (n := n) (by omega)
  have hle' : (c : ℝ) ≤ ((a * m ^ 2 + b * m * n + c * n ^ 2 : ℤ) : ℝ) := by exact_mod_cast hle
  linarith

/-- **Values of a reduced form off the first axis** (the page statement). Let
$q(x, y) = ax^2 + bxy + cy^2$ be a Gauss-reduced form with integer coefficients and put
$d = 4ac - b^2$. Then $q(m, n) \ge c$ for all integers $m, n$ with $n \ne 0$. Consequently the
number $N_q(t)$ of pairs $(m, n) \in \mathbb{Z} \times \mathbb{Z}_{\ge 1}$ with $q(m, n) \le t$ is
$0$ for every real $t < c$, and in particular for every $t < \sqrt d / 2$.

Source: J. Oesterlé, *Nombres de classes des corps quadratiques imaginaires*, Séminaire Bourbaki,
vol. 1983/84, exposé 631, Astérisque 121–122 (1985), 309–323, §1.3 (p. 312): "Le nombre $N_q(t)$
des couples $(m,n) \in \mathbb{Z} \times \mathbb{N}^*$ tels que $q(m,n) \le t$ est nul pour
$t < c$ (et a fortiori pour $t < \frac{\sqrt d}{2}$)". -/
theorem IsGaussReduced.values_off_axis (h : IsGaussReduced a b c) :
    (∀ m n : ℤ, n ≠ 0 → c ≤ a * m ^ 2 + b * m * n + c * n ^ 2) ∧
      (∀ t : ℝ, t < c →
        {p : ℤ × ℤ | 1 ≤ p.2 ∧ ((a * p.1 ^ 2 + b * p.1 * p.2 + c * p.2 ^ 2 : ℤ) : ℝ) ≤ t}.ncard
          = 0) ∧
      (∀ t : ℝ, t < √((4 * a * c - b ^ 2 : ℤ) : ℝ) / 2 →
        {p : ℤ × ℤ | 1 ≤ p.2 ∧ ((a * p.1 ^ 2 + b * p.1 * p.2 + c * p.2 ^ 2 : ℤ) : ℝ) ≤ t}.ncard
          = 0) := by
  refine ⟨fun m n hn => h.le_eval_of_ne_zero hn, fun t ht => ?_, fun t ht => ?_⟩
  · rw [h.setOf_eval_le_eq_empty ht, Set.ncard_empty]
  · have hc := h.coefficient_bounds.2.2.1
    rw [h.setOf_eval_le_eq_empty (lt_of_lt_of_le ht hc), Set.ncard_empty]

end BinaryQuadraticForm
