/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-!
# Dominant colors on power-step strings modulo a prime

Let `c : ZMod p → Fin 3` be rainbow-free for `x - y = z ^ k`: no solution has `c x`, `c y`, `c z`
pairwise distinct. For `a i : ZMod p` and `ℓ : ℕ`, the `aᵏ`-string at `i` of length `ℓ` is
`i aᵏ, (i + 1) aᵏ, …, (i + ℓ - 1) aᵏ`. If it takes exactly two colors, it contains the color `c a`.

A string taking two colors changes color between two consecutive terms `y = (i + t) aᵏ` and
`x = (i + t + 1) aᵏ`. Since `x - y = aᵏ`, the solution `(x, y, a)` is not rainbow, which forces
`c a = c y` or `c a = c x`. This is the proof of Lemma 4.5 in Katie Ansaldi, Gabriel Cowley,
Eric Green, Kihyun Kim and JT Rapp, *Rainbow Free Colorings and Rainbow Numbers for x-y=z^2*,
arXiv:2305.15133v1 (2023), which treats `x - y = z ^ k`. The proof does not use the hypotheses
that `c` is surjective, that `a ≠ 0` and that `p` is prime, which the statement keeps.

## Main results

* `MetaMathlibExt.color_dominant_powStrings_of_rainbowFree_zmod`: in an exact rainbow-free
  3-coloring of `ℤ/pℤ` for `x - y = z ^ k`, every bichromatic `aᵏ`-string with `a ≠ 0` contains
  the color `c a`.
-/

public section

namespace MetaMathlibExt

namespace color_dominant_powStrings_of_rainbowFree_zmod

/-- A string `f 0, f 1, …, f (ℓ - 1)` that takes at least two values changes value between two
consecutive positions. -/
private theorem exists_succ_ne_of_one_lt_card_image {α : Type*} [DecidableEq α] (f : ℕ → α)
    (ℓ : ℕ) (h : 1 < ((Finset.range ℓ).image f).card) : ∃ t, t + 1 < ℓ ∧ f t ≠ f (t + 1) := by
  by_contra! hne
  have hconst : ∀ t < ℓ, f t = f 0 := by
    intro t ht
    induction t with
    | zero => rfl
    | succ n ih => rw [← hne n ht, ih (by omega)]
  have hsub : (Finset.range ℓ).image f ⊆ {f 0} := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hx
    exact Finset.mem_singleton.2 (hconst t (Finset.mem_range.1 ht))
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_singleton] at hcard
  omega

end color_dominant_powStrings_of_rainbowFree_zmod

-- The statement keeps the hypotheses `hc` (the coloring is exact) and `ha`, which the proof does
-- not use.
set_option linter.unusedVariables false in
open color_dominant_powStrings_of_rainbowFree_zmod in
/-- **Dominant colors on power-step strings modulo a prime.** Let $p$ be a prime and $k$ a natural
number, and let $c$ be a coloring of $\mathbb{Z}/p\mathbb{Z}$ with three colors that uses every
color and is rainbow-free for $x - y = z^k$: no $x, y, z \in \mathbb{Z}/p\mathbb{Z}$ with
$x - y = z^k$ have $c(x), c(y), c(z)$ pairwise distinct. Let $a \ne 0$ and $i$ be elements of
$\mathbb{Z}/p\mathbb{Z}$ and let $\ell$ be a natural number. If the elements $(i + t)a^k$ for
$0 \le t < \ell$ take exactly two colors, then one of these elements has the color $c(a)$.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Lemma 9
(`integers-2024-A105-lem-9`). -/
theorem color_dominant_powStrings_of_rainbowFree_zmod (p k : ℕ) [Fact p.Prime]
    (c : ZMod p → Fin 3) (hc : Function.Surjective c)
    (hrf : ∀ x y z : ZMod p, x - y = z ^ k → ¬ (c x ≠ c y ∧ c y ≠ c z ∧ c x ≠ c z))
    (a : ZMod p) (ha : a ≠ 0) (i : ZMod p) (ℓ : ℕ)
    (hbi : ((Finset.range ℓ).image fun t : ℕ => c ((i + t) * a ^ k)).card = 2) :
    c a ∈ (Finset.range ℓ).image fun t : ℕ => c ((i + t) * a ^ k) := by
  obtain ⟨t, ht, hne⟩ :=
    exists_succ_ne_of_one_lt_card_image (fun t : ℕ => c ((i + t) * a ^ k)) ℓ (by omega)
  -- The consecutive terms `y = (i + t) aᵏ` and `x = (i + t + 1) aᵏ` differ by `aᵏ`.
  have hsol : (i + ((t + 1 : ℕ) : ZMod p)) * a ^ k - (i + (t : ZMod p)) * a ^ k = a ^ k := by
    push_cast
    ring
  by_contra hmem
  refine hrf _ _ a hsol ⟨Ne.symm hne, fun h => hmem ?_, fun h => hmem ?_⟩
  · exact Finset.mem_image.2 ⟨t, Finset.mem_range.2 (by omega), h⟩
  · exact Finset.mem_image.2 ⟨t + 1, Finset.mem_range.2 ht, h⟩

end MetaMathlibExt
