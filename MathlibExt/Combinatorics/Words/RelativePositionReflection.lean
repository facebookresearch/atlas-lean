/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Words.RelativePositionInjective

/-! # Reflection of binary words -/

namespace MetaMathlibExt

/-- **Reflection of binary words and relative position.** Let $\mathcal{W}$ be the set of
infinite words over $\{a, b\}$ in which both letters occur infinitely often, and let
$a\mathcal{W}$ and $b\mathcal{W}$ be its words that begin with $a$ and with $b$. For a word $w$
let $\bar w$ be its reflection, obtained by exchanging $a$ and $b$ at every position, and let
$r_w(n) = p_b(n) - p_a(n)$ be its relative position function, where $p_a(n)$ and $p_b(n)$ are
the positions of the $n$-th $a$ and the $n$-th $b$ in $w$. Then (a) the map $w \mapsto \bar w$
sends $a\mathcal{W}$ onto $b\mathcal{W}$ and $b\mathcal{W}$ onto $a\mathcal{W}$; and (b) for all
$w, w' \in \mathcal{W}$, $\bar w = w'$ if and only if $r_w(n) = -r_{w'}(n)$ for every $n \ge 1$.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Proposition 11
(`jis-2025-25.1.5-prop-11`). -/
public theorem reflection_image_and_relativePosition :
    ((fun w : ℕ → Bool => fun i => !w i) '' {w | BothLettersInfinite w ∧ w 0 = true} =
        {w | BothLettersInfinite w ∧ w 0 = false}) ∧
      ((fun w : ℕ → Bool => fun i => !w i) '' {w | BothLettersInfinite w ∧ w 0 = false} =
        {w | BothLettersInfinite w ∧ w 0 = true}) ∧
      ∀ w w' : ℕ → Bool, BothLettersInfinite w → BothLettersInfinite w' →
        ((fun i => !w i) = w' ↔ ∀ n, 1 ≤ n → relativePosition w n = -relativePosition w' n) := by
  have swap (w : ℕ → Bool) (α : Bool) : (fun i => (!w i) = α) = (fun i => w i = !α) := by
    funext i
    cases w i <;> cases α <;> simp
  have infinite (w : ℕ → Bool) (hw : BothLettersInfinite w) :
      BothLettersInfinite (fun i => !w i) := by
    unfold BothLettersInfinite
    rw [swap w true, swap w false]
    exact ⟨hw.2, hw.1⟩
  have image (α : Bool) :
      (fun w : ℕ → Bool => fun i => !w i) '' {w | BothLettersInfinite w ∧ w 0 = α} =
        {w | BothLettersInfinite w ∧ w 0 = !α} := by
    ext v
    constructor
    · rintro ⟨w, ⟨hw, hhead⟩, rfl⟩
      exact ⟨infinite w hw, congrArg Bool.not hhead⟩
    · rintro ⟨hv, hhead⟩
      exact ⟨fun i => !v i, ⟨infinite v hv, by simpa using congrArg Bool.not hhead⟩,
        funext fun i => Bool.not_not (v i)⟩
  have position (w : ℕ → Bool) (α : Bool) (n : ℕ) :
      letterPosition (fun i => !w i) α n = letterPosition w (!α) n := by
    unfold letterPosition
    rw [swap w α]
  have relative (w : ℕ → Bool) (n : ℕ) :
      relativePosition (fun i => !w i) n = -relativePosition w n := by
    simp only [relativePosition, position, Bool.not_false, Bool.not_true, Int.neg_sub]
  refine ⟨image true, image false, fun w w' hw hw' => ?_⟩
  rw [eq_iff_relativePosition_eq (infinite w hw) hw']
  simp only [relative, neg_eq_iff_eq_neg]

end MetaMathlibExt
