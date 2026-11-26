/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.ChocolateBarNSProperty
import Mathlib.Data.Fin.VecNotation

/-! # Nim-sum image identity for two NS functions

The nim-sum image of two truncated NS functions agrees with the image obtained by
keeping both coordinates fixed.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 5, equation (19).
-/

namespace MetaMathlibExt.HasNSProperty

@[expose] public section

/-- **Nim-sum image identity for two NS functions.** Let $g, h : \mathbb{N} \to \mathbb{N}$ have
the NS property and let $x, y, z \in \mathbb{N}$ with $x \le g(z)$ and $y \le h(z)$. Writing
$\oplus$ for the nim-sum (bitwise exclusive or) of natural numbers, the sets
$\{x \oplus y \oplus w : w < z\}$ and $\{\min(g(w), x) \oplus \min(h(w), y) \oplus w : w < z\}$
are equal, where $w$ ranges over the natural numbers.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 5, equation (19) (`integers-2025-G3-lem-5`). -/
public theorem image_xor_xor_eq {g h : ℕ → ℕ} (hg : HasNSProperty g)
    (hh : HasNSProperty h) {x y z : ℕ} (hx : x ≤ g z) (hy : y ≤ h z) :
    {c | ∃ w < z, c = x ^^^ y ^^^ w} = {c | ∃ w' < z, c = min (g w') x ^^^ min (h w') y ^^^ w'}
    := by
  have eq := MetaMathlibExt.image_foldl_xor_eq_image_min (f := ![g, h]) (x := ![x, y]) (z := z)
    (Fin.forall_fin_two.mpr ⟨hg, hh⟩) (Fin.forall_fin_two.mpr ⟨hx, hy⟩)
  simpa [min_comm] using eq

end

end MetaMathlibExt.HasNSProperty
