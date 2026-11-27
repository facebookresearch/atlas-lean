/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.LemkeHowson
public import Mathlib.Topology.UnitInterval

/-!
# Nash equilibria of two-by-two bimatrix games

The row and column players maximise their own payoffs. Index `0` means top for the row player
and left for the column player. A unilateral deviation changes expected payoff by the change in
probability of action `0` times that action's advantage. This gives a division-free test even on
the boundary. With no ties against pure opponents, it also determines the whole equilibrium set.
-/

@[expose] public section

namespace MathlibExt.GameTheory.TwoByTwo

open Convexity LemkeHowsonWanted Set

noncomputable section

private lemma second_weight (x : StdSimplex ℝ (Fin 2)) : x.weights 1 = 1 - x.weights 0 := by
  linarith [x.total_fin_two]

/-- A mixed strategy on two actions is specified uniquely by the probability `t ∈ [0,1]` of
playing action `0`. The inverse sends `t` to the strategy with probabilities `(t, 1−t)`. -/
def firstProbEquiv : StdSimplex ℝ (Fin 2) ≃ Icc (0 : ℝ) 1 :=
  StdSimplex.equivIcc.trans unitInterval.symmHomeomorph.toEquiv

/-- The interval coordinate of a real mixed strategy on two actions is its probability of
playing action `0`. -/
@[simp] theorem firstProbEquiv_apply (x : StdSimplex ℝ (Fin 2)) :
    (firstProbEquiv x : ℝ) = x.weights 0 := by
  change 1 - x.weights 1 = _
  linarith [second_weight x]

/-- For every real `t ∈ [0,1]`, the two-action strategy assigned to `t` by the inverse
coordinate map plays action `0` with probability `t`. -/
@[simp] theorem firstProbEquiv_symm_weights_zero (t : Icc (0 : ℝ) 1) :
    (firstProbEquiv.symm t).weights 0 = t := by
  rw [← firstProbEquiv_apply, Equiv.apply_symm_apply]

/-- In a real 2×2 bimatrix game, the row player's payoff for top minus that for bottom against
pure column `j` (`0` for left, `1` for right): `A 0 j − A 1 j`. -/
def rowGap (A : Fin 2 → Fin 2 → ℝ) (j : Fin 2) : ℝ := A 0 j - A 1 j

/-- In a real 2×2 bimatrix game, the column player's payoff for left minus that for right against
pure row `i` (`0` for top, `1` for bottom): `B i 0 − B i 1`. -/
def colGap (B : Fin 2 → Fin 2 → ℝ) (i : Fin 2) : ℝ := B i 0 - B i 1

private abbrev Responds (t h : ℝ) : Prop := (0 < h → t = 1) ∧ (h < 0 → t = 0)

private lemma optimal_iff_responds (x : StdSimplex ℝ (Fin 2)) (h : ℝ) :
    (∀ z : StdSimplex ℝ (Fin 2), (z.weights 0 - x.weights 0) * h ≤ 0) ↔
      Responds (x.weights 0) h := by
  have hx : x.weights 0 ∈ Icc 0 1 := ⟨x.weights_nonneg 0, x.weights_apply_le_one 0⟩
  constructor
  · intro H
    constructor
    · intro hp
      have h₁ := H (StdSimplex.single 0)
      simp only [StdSimplex.weights_single, Finsupp.single_eq_same] at h₁
      by_contra hne
      exact (not_lt_of_ge h₁) (mul_pos (sub_pos.mpr (lt_of_le_of_ne hx.2 hne)) hp)
    · intro hn
      have h₀ := H (StdSimplex.single 1)
      norm_num [StdSimplex.weights_single, Finsupp.single_apply] at h₀
      by_contra! hne
      exact (not_lt_of_ge h₀) (mul_neg_of_pos_of_neg (lt_of_le_of_ne hx.1 (Ne.symm hne)) hn)
  · rintro ⟨h₁, h₀⟩ z
    rcases lt_trichotomy h 0 with hn | rfl | hp
    · rw [h₀ hn, sub_zero]
      exact mul_nonpos_of_nonneg_of_nonpos (z.weights_nonneg 0) hn.le
    · simp
    · rw [h₁ hp]
      exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (z.weights_apply_le_one 0)) hp.le

private abbrev blend (t a b : ℝ) := t * a + (1 - t) * b
private abbrev pick (h : ℝ) : ℝ := if 0 < h then 1 else 0

private lemma responds_of_ne {t h : ℝ} (hh : h ≠ 0) : Responds t h ↔ t = pick h := by
  rcases lt_or_gt_of_ne hh with hn | hp
  · simp [Responds, pick, hn, hn.not_gt]
  · simp [Responds, pick, hp, hp.not_gt]

private lemma blend_pos {t a b : ℝ} (ht : t ∈ Icc 0 1) (ha : 0 < a) (hb : 0 < b) :
    0 < blend t a b := by
  rcases le_total a b with h | h
  · nlinarith only [ha, mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr h)]
  · nlinarith only [hb, mul_nonneg ht.1 (sub_nonneg.mpr h)]

private lemma dominant_iff {s t a b c d : ℝ} (ht : t ∈ Icc 0 1) (hab : 0 < a * b)
    (hc : c ≠ 0) (hd : d ≠ 0) :
    (Responds s (blend t a b) ∧ Responds t (blend s c d)) ↔
      s = pick a ∧ t = pick (if 0 < a then c else d) := by
  have hrow : Responds s (blend t a b) ↔ s = pick a := by
    rcases mul_pos_iff.mp hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · have h := blend_pos ht ha hb
      simp [Responds, pick, h, h.not_gt, ha]
    · have h : blend t a b < 0 := by
        nlinarith only [blend_pos ht (neg_pos.mpr ha) (neg_pos.mpr hb)]
      simp [Responds, pick, h, h.not_gt, ha.not_gt]
  rw [hrow]
  apply and_congr_right
  rintro rfl
  by_cases ha : 0 < a
  · simpa [pick, ha, blend] using (responds_of_ne (t := t) hc)
  · simpa [pick, ha, blend] using (responds_of_ne (t := t) hd)

private lemma root_mem {a b : ℝ} (hab : a * b < 0) : b / (b - a) ∈ Ioo 0 1 := by
  rcases mul_neg_iff.mp hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have hd : b - a < 0 := by linarith
    exact ⟨div_pos_of_neg_of_neg hb hd, (div_lt_iff_of_neg hd).2 (by linarith)⟩
  · have hd : 0 < b - a := by linarith
    exact ⟨div_pos hb hd, (div_lt_iff₀ hd).2 (by linarith)⟩

private lemma blend_eq_zero_iff {t a b : ℝ} (hab : a * b < 0) :
    blend t a b = 0 ↔ t = b / (b - a) := by
  have hd : b - a ≠ 0 := by
    rintro h
    rw [sub_eq_zero.mp h] at hab
    exact (not_lt_of_ge (mul_self_nonneg a)) hab
  rw [eq_div_iff hd]
  unfold blend
  constructor <;> intro h <;> linarith

private lemma indifferent {t h : ℝ} (ht : Responds t h) (h₁ : t ≠ 1) (h₀ : t ≠ 0) : h = 0 :=
  le_antisymm (not_lt.mp fun hp => h₁ (ht.1 hp)) (not_lt.mp fun hn => h₀ (ht.2 hn))

private lemma crossing_iff {s t a b c d : ℝ} (hab : a * b < 0) (hcd : c * d < 0) :
    (Responds s (blend t a b) ∧ Responds t (blend s c d)) ↔
      (s = d / (d - c) ∧ t = b / (b - a)) ∨
      (0 < a * c ∧ ((s = 1 ∧ t = pick c) ∨ (s = 0 ∧ t = pick d))) := by
  have hcd' := mul_ne_zero_iff.mp hcd.ne
  have top : Responds t (blend 1 c d) ↔ t = pick c := by simpa [blend] using responds_of_ne hcd'.1
  have bot : Responds t (blend 0 c d) ↔ t = pick d := by simpa [blend] using responds_of_ne hcd'.2
  -- At a pure row, the column's response is unique. Is that row itself a best response?
  have corners : (Responds 1 (blend (pick c) a b) ↔ 0 < a * c) ∧
      (Responds 0 (blend (pick d) a b) ↔ 0 < a * c) := by
    rcases mul_neg_iff.mp hab with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
      rcases mul_neg_iff.mp hcd with ⟨hc, hd⟩ | ⟨hc, hd⟩ <;>
      simp only [pick, blend, Responds, mul_pos_iff] <;> split_ifs <;> grind
  constructor
  · rintro ⟨hr, hc⟩
    by_cases h₁ : s = 1
    · subst s
      obtain rfl := top.mp hc
      exact Or.inr ⟨corners.1.mp hr, Or.inl ⟨rfl, rfl⟩⟩
    by_cases h₀ : s = 0
    · subst s
      obtain rfl := bot.mp hc
      exact Or.inr ⟨corners.2.mp hr, Or.inr ⟨rfl, rfl⟩⟩
    have ht := (blend_eq_zero_iff hab).mp (indifferent hr h₁ h₀)
    have ht' : t ∈ Ioo 0 1 := ht ▸ root_mem hab
    exact Or.inl ⟨(blend_eq_zero_iff hcd).mp (indifferent hc ht'.2.ne ht'.1.ne'), ht⟩
  · rintro (⟨hs, ht⟩ | ⟨h, ⟨rfl, ht⟩ | ⟨rfl, ht⟩⟩)
    · simp [(blend_eq_zero_iff hab).mpr ht, (blend_eq_zero_iff hcd).mpr hs, Responds]
    · exact ⟨ht ▸ corners.1.mpr h, top.mpr ht⟩
    · exact ⟨ht ▸ corners.2.mpr h, bot.mpr ht⟩

variable (A B : Fin 2 → Fin 2 → ℝ) (x y : StdSimplex ℝ (Fin 2))

local notation "α" => rowGap A 0
local notation "β" => rowGap A 1
local notation "γ" => colGap B 0
local notation "δ" => colGap B 1
local notation "p" => x.weights 0
local notation "q" => y.weights 0

/-- **Division-free classification.** In a real 2×2 game `(A,B)` write `p = Pr(top)` and
`q = Pr(left)` in `[0,1]`. Put `α = A₀₀−A₁₀`, `β = A₀₁−A₁₁`, `γ = B₀₀−B₀₁`, `δ = B₁₀−B₁₁`.
The profile is Nash iff a positive `qα+(1−q)β` forces `p=1` and a negative value forces `p=0`,
and a positive `pγ+(1−p)δ` forces `q=1` and a negative value forces `q=0`. Zero advantage
imposes no restriction on that player's own mix; the opponent's condition still applies. -/
theorem isBimatrixNash_iff : IsBimatrixNash A B x y ↔
    ((0 < q * α + (1 - q) * β → p = 1) ∧ (q * α + (1 - q) * β < 0 → p = 0)) ∧
    ((0 < p * γ + (1 - p) * δ → q = 1) ∧ (p * γ + (1 - p) * δ < 0 → q = 0)) := by
  change _ ↔ Responds _ _ ∧ Responds _ _
  rw [← optimal_iff_responds, ← optimal_iff_responds, IsBimatrixNash]
  apply and_congr <;> apply forall_congr' <;> intro z <;> rw [← sub_nonpos] <;>
    simp only [bilinPayoff, Fin.sum_univ_two, second_weight, rowGap, colGap] <;> ring_nf

/-- If the two real payoff matrices of a 2×2 game are constant (not necessarily the same
constant), every pair of mixed strategies is a Nash equilibrium: the entire square
`(Pr(top), Pr(left)) ∈ [0,1]²` is allowed. -/
theorem isBimatrixNash_const (a b : ℝ) : IsBimatrixNash (fun _ _ => a) (fun _ _ => b) x y := by
  simp [isBimatrixNash_iff, rowGap, colGap]

/-- In a real 2×2 game, let `p = Pr(top)` and `q = Pr(left)` in `[0,1]`. Let `α,β` be the
row player's top-minus-bottom payoffs against left and right, and `γ,δ` the column player's
left-minus-right payoffs against top and bottom. If `αβ > 0` and neither `γ` nor `δ` is zero,
the unique equilibrium has `p=1` if `α>0` and `p=0` otherwise. Its `q` is `1` exactly when
the column gap at that row (`γ` at top, `δ` at bottom) is positive, and `0` otherwise. -/
theorem isBimatrixNash_iff_of_row_dominance (hA : 0 < α * β) (hT : γ ≠ 0) (hB : δ ≠ 0) :
    IsBimatrixNash A B x y ↔ p = (if 0 < α then 1 else 0) ∧
      q = (if 0 < (if 0 < α then γ else δ) then 1 else 0) :=
  (isBimatrixNash_iff A B x y).trans
    (dominant_iff ⟨y.weights_nonneg 0, y.weights_apply_le_one 0⟩ hA hT hB)

/-- In a real 2×2 game, let `p = Pr(top)` and `q = Pr(left)` in `[0,1]`. Let `α,β` be the
row player's top-minus-bottom payoffs against left and right, and `γ,δ` the column player's
left-minus-right payoffs against top and bottom. If `γδ > 0` and neither `α` nor `β` is zero,
the unique equilibrium has `q=1` if `γ>0` and `q=0` otherwise. Its `p` is `1` exactly when
the row gap at that column (`α` at left, `β` at right) is positive, and `0` otherwise. -/
theorem isBimatrixNash_iff_of_col_dominance (hB : 0 < γ * δ) (hL : α ≠ 0) (hR : β ≠ 0) :
    IsBimatrixNash A B x y ↔ q = (if 0 < γ then 1 else 0) ∧
      p = (if 0 < (if 0 < γ then α else β) then 1 else 0) :=
  (isBimatrixNash_iff A B x y).trans <| and_comm.trans
    (dominant_iff ⟨x.weights_nonneg 0, x.weights_apply_le_one 0⟩ hB hL hR)

/-- In a real 2×2 game, write `α,β` for the top-minus-bottom row payoffs against left and
right, and `γ,δ` for the left-minus-right column payoffs against top and bottom. If `αβ<0`
and `γδ<0`, the mixing coordinates `δ/(δ−γ)` for `Pr(top)` and `β/(β−α)` for `Pr(left)`
both belong to the open interval `(0,1)`. -/
theorem mixedProbabilities_mem_Ioo (hA : α * β < 0) (hB : γ * δ < 0) :
    δ / (δ - γ) ∈ Ioo 0 1 ∧ β / (β - α) ∈ Ioo 0 1 := ⟨root_mem hB, root_mem hA⟩

/-- **Equilibria with crossing payoff differences.** In a real 2×2 game let `p=Pr(top)` and
`q=Pr(left)` in `[0,1]`. Let `α,β` denote the row player's top-minus-bottom payoffs against
left and right, and `γ,δ` the column player's left-minus-right payoffs against top and bottom.
Suppose `αβ<0` and `γδ<0`. The entire equilibrium set consists of the interior point
`(δ/(δ−γ), β/(β−α))` and, only if `αγ>0`, two corners: `(1,1),(0,0)` for `γ>0` or
`(1,0),(0,1)` for `γ<0`. Thus for `αγ<0` the interior point is the only equilibrium;
no equilibrium has just one player mixing strictly. -/
theorem isBimatrixNash_iff_of_crossing (hA : α * β < 0) (hB : γ * δ < 0) :
    IsBimatrixNash A B x y ↔
      (p = δ / (δ - γ) ∧ q = β / (β - α)) ∨
      (0 < α * γ ∧ ((p = 1 ∧ q = (if 0 < γ then 1 else 0)) ∨
        (p = 0 ∧ q = (if 0 < δ then 1 else 0)))) :=
  (isBimatrixNash_iff A B x y).trans (crossing_iff hA hB)

end

end MathlibExt.GameTheory.TwoByTwo
