/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.ChocolateBarNSProperty

/-!
# Nim-sum images for an NS function

The nim-sum image below a width is unchanged when the height is clamped by an NS function.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 5, equation (20).
-/

namespace MetaMathlibExt.HasNSProperty

/-- **Nim-sum image identity for one NS function.** Let $g : \mathbb{N} \to \mathbb{N}$ have the
NS property and let $x, z \in \mathbb{N}$ with $x \le g(z)$. Writing $\oplus$ for the nim-sum
(bitwise exclusive or) of natural numbers, the sets $\{x \oplus w : w < z\}$ and
$\{\min(g(w), x) \oplus w : w < z\}$ are equal, where $w$ ranges over the natural numbers.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 5, equation (20) (`integers-2025-G3-lem-5`). -/
public theorem image_xor_eq {g : ℕ → ℕ} (hg : HasNSProperty g)
    {x z : ℕ} (hx : x ≤ g z) :
    {c | ∃ w < z, c = x ^^^ w} = {c | ∃ w' < z, c = min (g w') x ^^^ w'} := by
  have h := image_foldl_xor_eq_image_min (m := 1) (f := fun _ ↦ g) (x := fun _ ↦ x)
    (fun _ ↦ hg) (fun _ ↦ hx)
  simpa only [List.ofFn_succ, List.ofFn_zero, List.foldl_cons, List.foldl_nil, Nat.zero_xor,
    min_comm x] using h

end MetaMathlibExt.HasNSProperty
