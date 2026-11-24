/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.GCD.Basic

/-!
# Diagonal billiard unfolding in a rectangle

`billiardUnfoldingDiagonalLemma` gives the coprime tile counts for commensurable side lengths
and identifies the possible corners after folding back.
-/

public section

namespace MathlibExt.Geometry.ScottishBook147Wanted

/--
**Lattice step of the billiard unfolding in a rectangle.** For a natural number $j$, let
$\varepsilon_j = 1$ if $j$ is odd and $\varepsilon_j = 0$ if $j$ is even. Let $a, b > 0$ be real
numbers with $a n = b m$ for some positive integers $m, n$. Then there are a real number $t > 0$
and natural numbers $k > 0$, $l > 0$ and $N$ such that $t = k a = l b$, $N + 2 = k + l$, $k$ and
$l$ are coprime, and the point $(\varepsilon_k a, \varepsilon_l b)$ is one of $(a, 0)$, $(0, b)$,
$(a, b)$.

In the billiard argument for the $a \times b$ rectangle, the unfolded diagonal from the
corner $(0, 0)$ first meets a corner of the tiling at $(t, t)$ (coprimality is the first-hit
condition), $N$ counts the reflections, and folding back yields the corner
$(\varepsilon_k a, \varepsilon_l b)$. This lemma covers only that lattice step; it does not
formalize the reflected trajectory and does not prove Problem 147.

Source: H. Auerbach and S. Mazur, Problem 147 of the Scottish Book; the
typescript labels the entry Theorem (Problem Mazur). Elementary unfolding
argument for polygonal billiards, see e.g. S. Tabachnikov, Geometry and
Billiards.
-/
theorem billiardUnfoldingDiagonalLemma :
    ∀ a b : ℝ, 0 < a → 0 < b →
      (∃ m n : ℕ, 0 < m ∧ 0 < n ∧ a * (n : ℝ) = b * (m : ℝ)) →
      ∃ t : ℝ, ∃ k l N : ℕ, 0 < t ∧ 0 < k ∧ 0 < l ∧ t = (k : ℝ) * a ∧
        t = (l : ℝ) * b ∧ N + 2 = k + l ∧ Nat.Coprime k l ∧
        (if k % 2 = 1 then a else 0, if l % 2 = 1 then b else 0) ∈
          ({(a, 0), (0, b), (a, b)} : Set (ℝ × ℝ)) := by
  intro a b ha _ ⟨m, n, hm, hn, hab⟩
  obtain ⟨g, k, l, hg, hcop, rfl, rfl⟩ := Nat.exists_coprime' (Nat.gcd_pos_of_pos_left m hn)
  have hk := Nat.pos_of_mul_pos_right hn
  have hl := Nat.pos_of_mul_pos_right hm
  have hstep : (k : ℝ) * a = (l : ℝ) * b := by
    apply mul_right_cancel₀ (Nat.cast_ne_zero.mpr hg.ne' : (g : ℝ) ≠ 0)
    simpa only [Nat.cast_mul, mul_left_comm, mul_comm, mul_assoc] using hab
  refine ⟨k * a, k, l, k + l - 2, mul_pos (Nat.cast_pos.mpr hk) ha, hk, hl, rfl,
    hstep, by omega, hcop, ?_⟩
  by_cases hkodd : k % 2 = 1
  · by_cases hlodd : l % 2 = 1 <;> simp [hkodd, hlodd]
  · have hlodd : l % 2 = 1 := by
      by_contra h
      have := Nat.eq_one_of_dvd_coprimes hcop (show 2 ∣ k by omega) (show 2 ∣ l by omega)
      omega
    simp [hkodd, hlodd]

end MathlibExt.Geometry.ScottishBook147Wanted
