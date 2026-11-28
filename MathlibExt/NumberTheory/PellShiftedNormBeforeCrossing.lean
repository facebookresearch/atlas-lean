/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PellRotatedSquare
import all MathlibExt.NumberTheory.PellRotatedSquarePellShiftedNormBijOnIci
import Mathlib.Tactic.Linarith

/-!
# The shifted Pell norm up to its last crossing

The tail bijection identifies the last crossing with the point where the affine sum
of the Pell coordinates attains the bound. Before that point, the affine sum is
smaller, and the Pell equation gives separate bounds when either shifted coordinate
has not yet reached zero.

## References

- Kun Yi Ong and Eddie Shahril Bin Ismail, *Integer Solutions of Pell Equation in a Closed
  Rotated Square Region*, INTEGERS 25 (2025), Article A112, pp. 1–14, Lemma 3.6 (p. 11).
  The proof uses the tail description of Lemma 3.7 (pp. 11–12).
- David M. Burton, *Elementary Number Theory*, 7th ed., McGraw-Hill, 2011, Section 15.5
  (Pell's equation; cited by Ong and Ismail for the natural-number coordinates in Proposition 1.2).
-/

namespace MetaMathlibExt

@[expose] public section

/-- **The shifted Pell norm function is at most the bound up to its last crossing.** Let $D$ be
an integer, let $(\alpha, \beta)$ be the fundamental solution of the Pell equation
$X^2 - D Y^2 = 1$, put $\varepsilon = \alpha + \beta \sqrt{D}$ and
$\bar\varepsilon = \alpha - \beta \sqrt{D}$, and let
$u(x) = (\varepsilon^x + \bar\varepsilon^x) / 2$ and
$v(x) = (\varepsilon^x - \bar\varepsilon^x) / (2 \sqrt{D})$ for real $x$. Let $a$ and $b$ be
integers, let $i, j \in \{1, -1\}$, let $f_{i,j}(x) = |i u(x) + a| + |j v(x) + b|$, let
$K = |a| + \max(|b| + 1, \sqrt{1 + D b^2})$ and let $x_1 = \sup \{y \ge 0 : f_{i,j}(y) = K\}$.
Then $f_{i,j}(x) \le K$ for every real $x$ with $0 \le x \le x_1$.

Source: Kun Yi Ong and Eddie Shahril Bin Ismail, *Integer Solutions of Pell Equation in a Closed
Rotated Square Region*, INTEGERS 25 (2025), Article A112, Lemma 3.6
(`integers-2025-A112-lem-3-6`). -/
public theorem pellShiftedNorm_le_pellShiftBound {D : ℤ} {w : Pell.Solution₁ D}
    (hw : Pell.IsFundamental w) (a b : ℤ) {i j : ℤ} (hi : i = 1 ∨ i = -1) (hj : j = 1 ∨ j = -1)
    {x : ℝ} (hx₀ : 0 ≤ x)
    (hx : x ≤ sSup {y : ℝ | 0 ≤ y ∧
      pellShiftedNorm D w.x w.y a b i j y = pellShiftBound D a b}) :
    pellShiftedNorm D w.x w.y a b i j x ≤ pellShiftBound D a b := by
  let u := pellU D w.x w.y
  let v := pellV D w.x w.y
  let A : ℝ := i * a
  let B : ℝ := j * b
  let f := pellShiftedNorm D w.x w.y a b i j
  let K := pellShiftBound D a b
  let x₁ : ℝ := sSup {y : ℝ | 0 ≤ y ∧ f y = K}
  change x ≤ x₁ at hx
  change f x ≤ K
  obtain ⟨haffine, hmono, hbij⟩ := pellShiftedNorm_bijOn_Ici hw a b hi hj
  have hcross : f x₁ = K := by
    obtain ⟨y, hy, hfy⟩ := hbij.surjOn (show K ∈ Set.Ici K from le_rfl)
    have h₁ : x₁ ∈ Set.Ici x₁ := le_rfl
    exact le_antisymm ((hmono.monotoneOn h₁ hy hy).trans_eq hfy) (hbij.mapsTo h₁)
  obtain ⟨_, _, hmu, hmv, hnorm⟩ := pell_coordinates hw
  have heq : u x ^ 2 - (D : ℝ) * v x ^ 2 = 1 := hnorm x
  have hD : (1 : ℝ) ≤ D := by exact_mod_cast (Int.add_one_le_iff.mpr hw.d_pos)
  have hux : 1 ≤ u x := by
    simpa only [u, pellU_zero] using hmu (by simp) hx₀ hx₀
  have hvx : 0 ≤ v x := by
    simpa only [v, pellV_zero] using hmv.monotoneOn (by simp) hx₀ hx₀
  have hA : |A| = |(a : ℝ)| := by rcases hi with h | h <;> simp [A, h]
  have hB : |B| = |(b : ℝ)| := by rcases hj with h | h <;> simp [B, h]
  have hK₁ : |A| + (|B| + 1) ≤ K := by
    rw [hA, hB]
    exact add_le_add le_rfl (le_max_left _ _)
  have hK₂ : |A| + Real.sqrt (1 + D * (b : ℝ) ^ 2) ≤ K := by
    rw [hA]
    exact add_le_add le_rfl (le_max_right _ _)
  have hlast : f x₁ = u x₁ + v x₁ + A + B := haffine x₁ le_rfl
  have hf : f x = |u x + A| + |v x + B| :=
    congrArg₂ (· + ·) (signed_abs i hi (u x) a) (signed_abs j hj (v x) b)
  rw [hf]
  by_cases hU : 0 ≤ u x + A
  · by_cases hV : 0 ≤ v x + B
    · rw [abs_of_nonneg hU, abs_of_nonneg hV, ← hcross, hlast]
      have hu := hmu hx₀ (hx₀.trans hx) hx
      have hv := hmv.monotoneOn hx₀ (hx₀.trans hx) hx
      change u x ≤ u x₁ at hu
      change v x ≤ v x₁ at hv
      change u x + A + (v x + B) ≤ u x₁ + v x₁ + A + B
      linarith only [hu, hv]
    · rw [abs_of_nonneg hU, abs_of_neg (lt_of_not_ge hV)]
      by_cases hsmall : u x ≤ v x + 1
      · linarith only [hsmall, le_abs_self A, neg_le_abs B, hK₁]
      · -- If `u - v > 1`, moving from `v` to `|b|` increases `u` by at least `|b| - v`.
        let c := |(b : ℝ)| - v x
        have hc : 0 ≤ c := by
          dsimp only [c]
          linarith only [lt_of_not_ge hV, neg_le_abs B, hB]
        have hvpos : 0 < v x := by
          by_contra! h
          have hv0 := le_antisymm h hvx
          have hu1 : u x = 1 := by
            apply (sq_eq_sq₀ (zero_le_one.trans hux) zero_le_one).mp
            simpa [hv0] using heq
          exact hsmall (by simp [hu1, hv0])
        have hDu : u x ≤ (D : ℝ) * v x := by
          apply (mul_le_mul_iff_of_pos_right hvpos).mp
          have h := mul_nonneg (show 0 ≤ u x - v x - 1 by linarith only [lt_of_not_ge hsmall])
            (show 0 ≤ u x + 1 by linarith only [hux])
          nlinarith only [heq, h, hvx]
        have hinc : u x + c ≤ Real.sqrt (1 + D * (b : ℝ) ^ 2) := by
          apply Real.le_sqrt_of_sq_le
          rw [← sq_abs (b : ℝ), show |(b : ℝ)| = v x + c by dsimp only [c]; ring]
          nlinarith only [heq, mul_nonneg (sub_nonneg.mpr hDu) hc,
            mul_nonneg (sub_nonneg.mpr hD) (sq_nonneg c)]
        have hB' : -B ≤ |(b : ℝ)| := (neg_le_abs B).trans_eq hB
        dsimp only [c] at hinc
        linarith only [hinc, le_abs_self A, hB', hK₂]
  · rw [abs_of_neg (lt_of_not_ge hU)]
    have hvu : v x ≤ u x := by
      have heq : u x ^ 2 - (D : ℝ) * v x ^ 2 = 1 := hnorm x
      apply (sq_le_sq₀ hvx (zero_le_one.trans hux)).mp
      nlinarith only [heq, le_mul_of_one_le_left (sq_nonneg (v x)) hD]
    have habs : |v x + B| ≤ v x + |B| := by
      simpa only [abs_of_nonneg hvx] using abs_add_le (v x) B
    linarith only [habs, hvu, neg_le_abs A, hK₁]

end

end MetaMathlibExt
