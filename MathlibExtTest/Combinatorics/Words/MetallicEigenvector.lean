/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Words.MetallicEigenvector

/-! # Tests for integer matrices with a metallic-mean eigenvector -/

namespace MetaMathlibExt.metallic_eigenvector_iff

-- The boundary case k = 1 allows negative off-diagonal entries.
example : ∃ c : ℝ, ((!![0, -1; -1, 1] : Matrix (Fin 2) (Fin 2) ℤ).map
    (Int.cast : ℤ → ℝ)).mulVec ![(1 + Real.sqrt 5) / 2, 1] =
      c • ![(1 + Real.sqrt 5) / 2, 1] := by
  simpa only [Nat.cast_one, one_pow, show (1 : ℝ) + 4 = 5 by norm_num] using
    (metallic_eigenvector_iff 1 le_rfl !![0, -1; -1, 1]).1.2 ⟨-1, 1, by norm_num⟩

-- Equal off-diagonal entries do not suffice: the diagonal difference must match k.
example :
    let τ : ℝ := (2 + Real.sqrt (2 ^ 2 + 4)) / 2
    ¬ ∃ c : ℝ, ((!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ).map
      (Int.cast : ℤ → ℝ)).mulVec ![τ, 1] = c • ![τ, 1] := by
  dsimp only
  intro heig
  have hiff := (metallic_eigenvector_iff 2 (by decide) !![1, 1; 1, 0]).1
  obtain ⟨m, n, h⟩ := hiff.mp (by simpa only [Nat.cast_ofNat] using heig)
  have h00 : (1 : ℤ) = 2 * m + n := congrFun (congrFun h 0) 0
  have h10 : (1 : ℤ) = m := congrFun (congrFun h 1) 0
  have h11 : (0 : ℤ) = n := congrFun (congrFun h 1) 1
  omega

-- A scalar matrix has a double root, for every metallic parameter.
open Polynomial in
example (k : ℕ) (hk : 1 ≤ k) (n : ℤ) :
    ((!![n, 0; 0, n] : Matrix (Fin 2) (Fin 2) ℤ).map
      (Int.cast : ℤ → ℝ)).charpoly = (X - C (n : ℝ)) ^ 2 := by
  simpa [sq] using (metallic_eigenvector_iff k hk !![n, 0; 0, n]).2 0 n (by simp)

end MetaMathlibExt.metallic_eigenvector_iff
