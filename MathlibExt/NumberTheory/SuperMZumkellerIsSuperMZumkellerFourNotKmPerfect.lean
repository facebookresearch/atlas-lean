/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.NumberTheory.SuperMZumkeller

/-!
# Four is super-m-Zumkeller but not `k`-m-perfect

The number `4` is super-m-Zumkeller, and for no natural number `k ≥ 2` is `4` `k`-m-perfect.
This is the paper's counterexample to the converse of Theorem 6.

Source: Harish Patodia, "Super m-Zumkeller Numbers", Theorem 6.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.SuperMZumkellerWanted

/-- **$4$ is super-m-Zumkeller but not $k$-m-perfect for $k \ge 2$.** The number $4$ is
super-m-Zumkeller, and for no natural number $k \ge 2$ is $4$ a $k$-m-perfect number. This is the
paper's counterexample to the converse of Theorem 6.

Source: Harish Patodia, "Super m-Zumkeller Numbers", Theorem 6. -/
theorem isSuperMZumkeller_four_not_kmPerfect :
    IsSuperMZumkeller 4 ∧ ∀ k : ℕ, 2 ≤ k → ¬ IsKMPerfect k 4 := by
  constructor
  · exact ⟨{8}, by decide, by decide⟩
  · intro k hk h
    have hT : divisorProd 4 = 8 := by decide
    unfold IsKMPerfect at h
    rw [hT] at h
    have hge : (16 : ℕ) ≤ 4 ^ k :=
      calc (16 : ℕ) = 4 ^ 2 := by decide
      _ ≤ 4 ^ k := Nat.pow_le_pow_right (by decide) hk
    omega

end MathlibExt.NumberTheory.SuperMZumkellerWanted
