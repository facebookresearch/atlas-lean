/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.MaximumNimJosephus
import all MathlibExt.Combinatorics.MaximumNimJosephus

/-!
# Maximum Nim Grundy numbers at non-multiples

For the rule $f(x) = \lfloor x/k \rfloor$ with $k \ge 2$, the closed window from $x - f(x)$ to $x$
has Grundy numbers $0, \dots, f(x)$, each occurring once. The left endpoint never decreases:
when the rule increases it stays put, and otherwise it advances by one. The new right endpoint
has a different Grundy number from every retained position because it can move to each one.
At a non-multiple $x$ of $k$, the legal options are exactly the preceding closed window with its
leftmost position removed. The discarded value becomes the new mex, and the floor identity
identifies its position.

## References

* Shoei Takahashi, Hikaru Manabe, and Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
  INTEGERS 24 (2024), Article G5, pp. 1–16 (<https://math.colgate.edu/~integers/yg5/yg5.pdf>).
  Lemma 3(ii), pp. 3–4, gives the non-multiple formula, using Lemma 2 and Lemma 1(ii).
* Lionel Levine, *Fractal Sequences and Restricted Nim*, Ars Combinatoria 80 (2006), pp. 113–127
  (<https://pi.math.cornell.edu/~levine/restrictednim.pdf>). Lemma 2.1 is the original
  regular-rule recurrence cited by Lemma 1 of Takahashi, Manabe, and Miyadera.
-/

namespace MetaMathlibExt

private theorem floorGrundy_eq_mex_window (k x : ℕ) :
    maximumNimGrundy (· / k) x =
      maximumNimMex ((Finset.Ico (x - x / k) x).image (maximumNimGrundy (· / k))) := by
  have hdiv := Nat.div_le_self x k
  rw [maximumNimGrundy_eq, min_eq_left hdiv]
  congr 1
  ext n
  simp only [Finset.mem_image, Finset.mem_attach, true_and, Finset.mem_Ico]
  constructor
  · rintro ⟨⟨u, hu⟩, rfl⟩
    rw [Finset.mem_Icc] at hu
    exact ⟨x - u, ⟨by omega, by omega⟩, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    have hxy : x - (x - y) = y := Nat.sub_sub_self hy.2.le
    exact ⟨⟨x - y, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩,
      congrArg (maximumNimGrundy (· / k)) hxy⟩

private theorem floorGrundy_le_div (k x : ℕ) : maximumNimGrundy (· / k) x ≤ x / k :=
  (maximumNimGrundy_le_min_rule (· / k) x).trans (min_le_left _ _)

private theorem floorGrundy_injOn_window (k x : ℕ) :
    Set.InjOn (maximumNimGrundy (· / k)) (↑(Finset.Icc (x - x / k) x) : Set ℕ) := by
  induction x with
  | zero =>
    intro a ha b hb _
    simp only [Finset.mem_coe, Finset.mem_Icc] at ha hb
    omega
  | succ x ih =>
    -- This includes multiples: when the quotient increases, the left endpoint stays fixed.
    have hstep : x - x / k ≤ (x + 1) - (x + 1) / k := by
      rw [Nat.succ_div]
      split <;> omega
    have hne (a : ℕ) (ha : (x + 1) - (x + 1) / k ≤ a) (hal : a < x + 1) :
        maximumNimGrundy (· / k) a ≠ maximumNimGrundy (· / k) (x + 1) := by
      have hmove : x + 1 - a ≤ min ((x + 1) / k) (x + 1) :=
        le_min (by omega) (Nat.sub_le _ _)
      simpa only [Nat.sub_sub_self hal.le] using
        maximumNimGrundy_sub_ne_of_move (· / k) (x + 1) (x + 1 - a) (by omega) hmove
    intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_Icc] at ha hb
    by_cases ha' : a = x + 1
    · subst a
      by_contra h
      exact hne b hb.1 (by omega) hab.symm
    by_cases hb' : b = x + 1
    · subst b
      exact (hne a ha.1 (by omega) hab).elim
    exact ih (Finset.mem_Icc.mpr ⟨hstep.trans ha.1, by omega⟩)
      (Finset.mem_Icc.mpr ⟨hstep.trans hb.1, by omega⟩) hab

private theorem floorGrundy_image_window (k x : ℕ) :
    (Finset.Icc (x - x / k) x).image (maximumNimGrundy (· / k)) =
      Finset.range (x / k + 1) := by
  apply Finset.eq_of_subset_of_card_le
  · intro n hn
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hn
    have hyx : y / k ≤ x / k := Nat.div_le_div_right (Finset.mem_Icc.mp hy).2
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le ((floorGrundy_le_div k y).trans hyx))
  · rw [Finset.card_range, Finset.card_image_of_injOn (floorGrundy_injOn_window k x), Nat.card_Icc]
    have := Nat.div_le_self x k
    omega

/-- **Maximum Nim Grundy numbers at non-multiples of the divisor.** Let $k \ge 2$ and let $G$
be the Grundy number of Maximum Nim with rule function $f(y) = \lfloor y/k \rfloor$. If $x$ is a
natural number not divisible by $k$, then $G(x) = G(\lfloor (k-1)x/k \rfloor)$.

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Lemma 3(ii) (`integers-2024-G5-lem-3`). -/
public theorem maximumNimGrundy_eq_F_of_not_dvd (k x : ℕ) (hk : 2 ≤ k) (hkx : ¬k ∣ x) :
    maximumNimGrundy (· / k) x = maximumNimGrundy (· / k) ((k - 1) * x / k) := by
  have hx : x ≠ 0 := fun h => hkx (h ▸ Nat.dvd_zero k)
  obtain ⟨y, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hx
  have hdiv := Nat.div_le_self y k
  have hindex : y + 1 - y / k - 1 = y - y / k := by omega
  rw [← maximumNim_sub_div_sub_one_eq k (y + 1) hk hkx, floorGrundy_eq_mex_window,
    maximumNimMex_eq_iff, Nat.succ_div_of_not_dvd hkx, hindex]
  let a := y - y / k
  have ha : a ∈ Finset.Icc a y := Finset.mem_Icc.mpr ⟨le_rfl, Nat.sub_le _ _⟩
  constructor
  · intro hm
    obtain ⟨b, hb, heq⟩ := Finset.mem_image.mp hm
    rw [Finset.mem_Ico] at hb
    have hb' : b ∈ Finset.Icc a y := Finset.mem_Icc.mpr ⟨by dsimp [a]; omega, by omega⟩
    have hba : b = a := floorGrundy_injOn_window k y hb' ha heq
    dsimp [a] at hba
    omega
  · intro n hn
    have hle : maximumNimGrundy (· / k) a ≤ y / k :=
      (floorGrundy_le_div k a).trans (Nat.div_le_div_right (Nat.sub_le _ _))
    have hm : n ∈ Finset.range (y / k + 1) :=
      Finset.mem_range.mpr (hn.trans (Nat.lt_succ_of_le hle))
    rw [← floorGrundy_image_window] at hm
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hm
    have hba : b ≠ a := by
      intro h
      subst b
      exact (Nat.lt_irrefl _) hn
    refine Finset.mem_image.mpr ⟨b, Finset.mem_Ico.mpr ?_, rfl⟩
    rw [Finset.mem_Icc] at hb
    dsimp [a] at hba
    omega

end MetaMathlibExt
