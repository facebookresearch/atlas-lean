/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Notation

/-!
# Adding one to a remainder without wrap-around

If a natural number has remainder below the last residue, adding one increases its remainder by one.
-/

public section

namespace MetaMathlibExt

/--
**Adding one to a remainder without wrap-around.** Let $x$ and $C$ be natural numbers with
$C \ge 2$. If $x \bmod C \ne (C - 1) \bmod C$, that is, if $x$ is not congruent to $C - 1$
modulo $C$, then $(x + 1) \bmod C = (x \bmod C) + 1$.

Source: M. Prunescu and J. M. Shunia, *On Modular Representations of C-Recursive Integer Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.3, Lemma 6.
-/
theorem add_one_mod_eq_mod_add_one_of_ne
    (x C : ℕ) (hC : 2 ≤ C) (hne : x % C ≠ (C - 1) % C) :
    (x + 1) % C = x % C + 1 := by
  rw [Nat.mod_eq_of_lt (show C - 1 < C by omega)] at hne
  have hlt := Nat.mod_lt x (show 0 < C by omega)
  rw [← Nat.mod_add_mod]
  exact Nat.mod_eq_of_lt (by omega)

end MetaMathlibExt
