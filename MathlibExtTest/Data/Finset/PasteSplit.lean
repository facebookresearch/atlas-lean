/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Logic.Equiv.Prod
public import MathlibExt.Data.Finset.PasteSplit
public import MathlibExt.LinearAlgebra.Matrix.DetFinSmall
public import MathlibExt.Algebra.BigOperators.SeparableSum
public import MathlibExt.Analysis.Fourier.ZModAddCharSum

@[expose] public section

/-!
# Tests for the general helpers extracted from the AME development
-/

namespace MathlibExtTest.Data.Finset.PasteSplit

open MetaMathlibExt

-- `pasteOn` glues two functions along a finset.
example (x : ({0, 1} : Finset (Fin 3)) → ℕ) (z : {i : Fin 3 // i ∉ ({0, 1} : Finset (Fin 3))} → ℕ)
    (i : ({0, 1} : Finset (Fin 3))) : pasteOn _ x z i.1 = x i := pasteOn_mem _ x z i

-- Gluing with the inverse of Mathlib's equivalence computes as `pasteOn`.
example (A : Finset (Fin 3)) (x : A → ℕ) (z : {i : Fin 3 // i ∉ A} → ℕ) :
    (Equiv.piEquivPiSubtypeProd (fun i : Fin 3 => i ∈ A) (fun _ => ℕ)).symm (x, z) =
      pasteOn A x z := rfl

-- The inverse on the complement uses the inverse of the supplied permutation.
example (S : Finset (Fin 3)) (e : Equiv.Perm (Fin 3)) (y : ↥((S.map e.toEmbedding)ᶜ)) :
    ((finsetMapComplEquiv e S).symm y).1 = e.symm y.1 := rfl

-- The closed-form determinants agree with `Matrix.det` on a concrete matrix.
example : detFinThreeInt (Matrix.of ![![1, 2, 3], ![4, 5, 6], ![7, 8, 10]]) = -3 := by decide

example : (Matrix.of ![![(1 : ℤ), 2, 3], ![4, 5, 6], ![7, 8, 10]]).det = -3 := by
  rw [detFinThreeInt_eq]
  decide

-- A character sum of a nonzero linear form vanishes.
example (c : Fin 2 → ZMod 5) (hc : c ≠ 0) :
    (∑ z : Fin 2 → ZMod 5, ZMod.stdAddChar (∑ i, c i * z i)) = 0 := by
  rw [sum_stdAddChar_dot]
  simp [hc]

-- A separable double sum factors.
example (K : ℤ) (B Q : Fin 3 → ℤ) :
    (∑ u, ∑ v, K * B u * Q v) = K * (∑ u, B u) * (∑ v, Q v) :=
  sum_separable K B Q

end MathlibExtTest.Data.Finset.PasteSplit
