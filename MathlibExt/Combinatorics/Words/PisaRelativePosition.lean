/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Rat.Defs
public import MathlibExt.Combinatorics.Words.RelativePositionBinaryWords
import Mathlib.Data.List.GetD
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Relative position of the extended Pisa fixed point

Let `k ≥ 1`, `l ≥ 0` and `m ≥ 1`, and let `w` be a one-sided fixed point of the extended Pisa
substitution `σ : a ↦ aᵏ b aˡ, b ↦ aᵐ`, with `a` encoded as `true` and `b` as `false`. The main
result, `pisa_relativePosition_of_letterPosition_b`, expresses the relative position function
`r(n) = p_b(n) - p_a(n)` of `w` through the positions `p_b(n)` of the letter `b`.

The proof follows Theorem 4.20 and Corollary 4.21 of arXiv:2410.12173v1, the preprint of the
article by Coons, Ramsey and Strungaru cited in the docstring of the main result. Cut
`w = σ(w)` into the blocks `σ(w₀) σ(w₁) ⋯`. Every block starts with `a`, so `a` occurs infinitely
often in `w`. The block `σ(a) = aᵏ b aˡ` contains exactly one `b`, at offset `k`, and the block
`σ(b) = aᵐ` contains none, so the `n`-th `b` of `w` is the `b` of the block of the `n`-th `a`.
If that `a` is at position `j = p_a(n)`, the first `j` letters of `w` contain `n - 1` letters `a`
and `j - n + 1` letters `b`, hence
`p_b(n) = (n - 1)(k + l + 1) + (p_a(n) - n + 1) m + k`;
solving this identity for `p_a(n)` gives the formula for `r(n)`. The hypothesis `w 0 = true` of
the main result follows from the fixed point equation, and the proof does not use it.
-/

namespace MetaMathlibExt

namespace pisa_relativePosition_of_letterPosition_b

/-- The image under `ϱ` of the prefix of length `j` of `w`. -/
private def img (ϱ : Bool → List Bool) (w : ℕ → Bool) (j : ℕ) : List Bool :=
  (List.ofFn fun i : Fin j => w i).flatMap ϱ

private theorem img_zero (ϱ : Bool → List Bool) (w : ℕ → Bool) : img ϱ w 0 = [] := by
  simp [img]

private theorem img_succ (ϱ : Bool → List Bool) (w : ℕ → Bool) (j : ℕ) :
    img ϱ w (j + 1) = img ϱ w j ++ ϱ (w j) := by
  rw [img, List.ofFn_succ']
  simp [img]

/-- In a fixed point of `ϱ`, the image of the letter at position `j` follows the image of the
first `j` letters. -/
private theorem apply_length_add {ϱ : Bool → List Bool} {w : ℕ → Bool}
    (hfix : IsSubstitutionImage ϱ w w) (j : ℕ) {i : ℕ} (hi : i < (ϱ (w j)).length) :
    w ((img ϱ w j).length + i) = (ϱ (w j)).getD i false := by
  have hlen : (img ϱ w j).length + i < (img ϱ w (j + 1)).length := by
    rw [img_succ, List.length_append]
    omega
  have h : w _ = (img ϱ w (j + 1)).getD _ false := hfix.2 (j + 1) _ hlen
  rw [h, img_succ, List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]

private theorem count_congr {p q : ℕ → Prop} [DecidablePred p] [DecidablePred q] {n : ℕ}
    (h : ∀ i < n, p i ↔ q i) : Nat.count p n = Nat.count q n := by
  simp only [Nat.count_eq_card_filter_range]
  exact congrArg Finset.card (Finset.filter_congr fun i hi => h i (Finset.mem_range.1 hi))

/-- The extended Pisa substitution `a ↦ aᵏ b aˡ`, `b ↦ aᵐ`. -/
private def pisa (k l m : ℕ) : Bool → List Bool := fun x : Bool =>
  if x then List.replicate k true ++ [false] ++ List.replicate l true else List.replicate m true

variable {k l m : ℕ} {w : ℕ → Bool}

private theorem length_pisa_true : (pisa k l m true).length = k + 1 + l := by
  simp [pisa]
  omega

private theorem length_pisa_false : (pisa k l m false).length = m := by
  simp [pisa]

/-- The only `b` of `aᵏ b aˡ` is at position `k`. -/
private theorem getD_pisa_true {i : ℕ} (hi : i < k + 1 + l) :
    (pisa k l m true).getD i false = decide (i ≠ k) := by
  simp only [pisa, ite_true]
  rcases lt_trichotomy i k with h | rfl | h
  · rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by simp; omega),
      List.getD_replicate _ h]
    simp [h.ne]
  · rw [List.getD_append _ _ _ _ (by simp), List.getD_append_right _ _ _ _ (by simp)]
    simp
  · rw [List.getD_append_right _ _ _ _ (by simp; omega),
      List.getD_replicate _ (by simp; omega)]
    simp [h.ne']

private theorem getD_pisa_false {i : ℕ} (hi : i < m) :
    (pisa k l m false).getD i false = true := by
  simp only [pisa, Bool.false_eq_true, ite_false]
  exact List.getD_replicate _ hi

/-- Every block of the fixed point starts with `a`. -/
private theorem apply_length_img (hk : 1 ≤ k) (hm : 1 ≤ m)
    (hfix : IsSubstitutionImage (pisa k l m) w w) (j : ℕ) :
    w (img (pisa k l m) w j).length = true := by
  cases h : w j with
  | false =>
    have := apply_length_add hfix j (i := 0) (by rw [h, length_pisa_false]; omega)
    rwa [Nat.add_zero, h, getD_pisa_false (by omega)] at this
  | true =>
    have := apply_length_add hfix j (i := 0) (by rw [h, length_pisa_true]; omega)
    rw [Nat.add_zero, h, getD_pisa_true (by omega)] at this
    exact this.trans (decide_eq_true (by omega))

private theorem le_length_img (hk : 1 ≤ k) (hm : 1 ≤ m) (j : ℕ) :
    j ≤ (img (pisa k l m) w j).length := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [img_succ, List.length_append]
    cases w j
    · rw [length_pisa_false]
      omega
    · rw [length_pisa_true]
      omega

/-- The letter `a` occurs infinitely often in the fixed point. -/
private theorem infinite_true (hk : 1 ≤ k) (hm : 1 ≤ m)
    (hfix : IsSubstitutionImage (pisa k l m) w w) : (Set.ofPred fun i => w i = true).Infinite :=
  Set.infinite_of_forall_exists_gt fun N =>
    ⟨_, apply_length_img hk hm hfix (N + 1),
      Nat.lt_of_lt_of_le (Nat.lt_succ_self N) (le_length_img (w := w) (l := l) hk hm (N + 1))⟩

private theorem count_add_count (j : ℕ) :
    Nat.count (fun i => w i = true) j + Nat.count (fun i => w i = false) j = j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.count_succ, Nat.count_succ]
    cases w j <;> simp <;> omega

/-- The image of a prefix with `c` letters `a` and `d` letters `b` has length
`c (k + 1 + l) + d m`. -/
private theorem length_img (j : ℕ) :
    (img (pisa k l m) w j).length =
      Nat.count (fun i => w i = true) j * (k + 1 + l) + Nat.count (fun i => w i = false) j * m := by
  induction j with
  | zero => simp [img_zero]
  | succ j ih =>
    rw [img_succ, List.length_append, ih, Nat.count_succ, Nat.count_succ]
    cases w j
    · simp [length_pisa_false]
      ring
    · simp [length_pisa_true]
      ring

/-- Each block `aᵏ b aˡ` contains one `b`, and each block `aᵐ` none. -/
private theorem count_false_length_img (hfix : IsSubstitutionImage (pisa k l m) w w) (j : ℕ) :
    Nat.count (fun i => w i = false) (img (pisa k l m) w j).length =
      Nat.count (fun i => w i = true) j := by
  induction j with
  | zero => simp [img_zero]
  | succ j ih =>
    rw [img_succ, List.length_append, Nat.count_add, ih, Nat.count_succ]
    cases h : w j with
    | false =>
      rw [length_pisa_false, Nat.count_of_forall_not
        (p := fun i => w ((img (pisa k l m) w j).length + i) = false) fun i hi => ?_]
      · simp
      · rw [apply_length_add hfix j (by rw [h, length_pisa_false]; exact hi), h,
          getD_pisa_false hi]
        simp
    | true =>
      rw [length_pisa_true, count_congr
        (p := fun i => w ((img (pisa k l m) w j).length + i) = false) (q := fun i => i = k)
        fun i hi => ?_]
      · have hone : Nat.count (fun i => i = k) (k + 1 + l) = 1 := by
          rw [Nat.count_eq_card_filter_range, Finset.filter_eq']
          simp [show k < k + 1 + l by omega]
        simp [hone]
      · rw [apply_length_add hfix j (by rw [h, length_pisa_true]; exact hi), h,
          getD_pisa_true hi]
        simp

/-- The `(n + 1)`-th `b` of the fixed point is the `b` of the block of its `(n + 1)`-th `a`:
`p_b(n + 1) + n m = n (k + 1 + l) + p_a(n + 1) m + k`. -/
private theorem letterPosition_false_succ (hk : 1 ≤ k) (hm : 1 ≤ m)
    (hfix : IsSubstitutionImage (pisa k l m) w w) (n : ℕ) :
    letterPosition w false (n + 1) + n * m =
      n * (k + 1 + l) + letterPosition w true (n + 1) * m + k := by
  have hinf := infinite_true hk hm hfix
  have hwj : w (Nat.nth (fun i => w i = true) n) = true := Nat.nth_mem_of_infinite hinf n
  have hcj := Nat.count_nth_of_infinite hinf n
  have hj : letterPosition w true (n + 1) = Nat.nth (fun i => w i = true) n := by
    simp [letterPosition]
  rw [hj]
  generalize Nat.nth (fun i => w i = true) n = j at hwj hcj
  have hlt : k < (pisa k l m (w j)).length := by
    rw [hwj, length_pisa_true]
    omega
  have hb : w ((img (pisa k l m) w j).length + k) = false := by
    rw [apply_length_add hfix j hlt, hwj, getD_pisa_true (by omega)]
    simp
  have hcount : Nat.count (fun i => w i = false) ((img (pisa k l m) w j).length + k) = n := by
    rw [Nat.count_add, count_false_length_img hfix, hcj, Nat.count_of_forall_not
      (p := fun i => w ((img (pisa k l m) w j).length + i) = false) fun i hi => ?_, Nat.add_zero]
    rw [apply_length_add hfix j (by omega), hwj, getD_pisa_true (by omega)]
    simp
    omega
  have hpos : letterPosition w false (n + 1) = (img (pisa k l m) w j).length + k := by
    have := Nat.nth_count (p := fun i => w i = false) hb
    rw [hcount] at this
    simpa [letterPosition] using this
  have hsum := count_add_count (w := w) j
  rw [hcj] at hsum
  rw [hpos, length_img, hcj]
  generalize Nat.count (fun i => w i = false) j = c at hsum ⊢
  subst hsum
  ring

end pisa_relativePosition_of_letterPosition_b

-- The hypothesis `h₀` follows from `hfix` and is kept for fidelity with the source statement.
set_option linter.unusedVariables false in
/-- **Relative position of the extended Pisa fixed point via the positions of $b$.** Let
$k \ge 1$, $l \ge 0$ and $m \ge 1$ be natural numbers, let $\sigma$ be the substitution
$a \mapsto a^k b a^l$, $b \mapsto a^m$, and let $w$ be a one-sided fixed point of $\sigma$ (so
$\sigma(w) = w$) that begins with $a$. Let $p_a(n)$ and $p_b(n)$ be the positions (counted from
$0$) of the $n$-th $a$ and the $n$-th $b$ in $w$, and let $r(n) = p_b(n) - p_a(n)$. Then for
every $n \ge 1$,
$$r(n) = \frac{m - 1}{m}\,p_b(n) + \frac{k + l + 1 - m}{m}\,n + \frac{m - l - 1}{m}.$$

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Corollary 58
(`jis-2025-25.1.5-cor-58`). -/
public theorem pisa_relativePosition_of_letterPosition_b (k l m : ℕ) (hk : 1 ≤ k)
    (hm : 1 ≤ m) {w : ℕ → Bool}
        (hfix : IsSubstitutionImage (fun x : Bool => if x then List.replicate k true ++ [false] ++
        List.replicate l true else List.replicate m true) w w)
    (h₀ : w 0 = true) (n : ℕ) (hn : 1 ≤ n) :
    (relativePosition w n : ℚ) = (m - 1) / m * letterPosition w false n +
      (k + l + 1 - m) / m * n + (m - l - 1) / m := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have h := pisa_relativePosition_of_letterPosition_b.letterPosition_false_succ hk hm hfix n
  have hq : (letterPosition w false (n + 1) : ℚ) + n * m =
      n * (k + 1 + l) + letterPosition w true (n + 1) * m + k := by
    exact_mod_cast h
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  simp only [relativePosition, Int.cast_sub, Int.cast_natCast]
  field_simp
  push_cast
  linear_combination hq

end MetaMathlibExt
