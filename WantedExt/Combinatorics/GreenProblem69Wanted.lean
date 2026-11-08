/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Green Problem 69
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.DFinsupp
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Combinatorics.GreenProblem69Wanted

/-! Source record `UM-00000157-Q001`. -/
/-- The cube `{0, 1}^n ⊆ 𝔽₃^n`. -/
def cubeOrigin (n : ℕ) : Set (Fin n → ZMod 3) :=
  { x | ∀ i : Fin n, x i = 0 ∨ x i = 1 }

/-- A cube: the image of `{0, 1}^n` under a linear automorphism of `𝔽₃^n`. -/
def IsCube (n : ℕ) (A : Set (Fin n → ZMod 3)) : Prop :=
  ∃ e : (Fin n → ZMod 3) ≃ₗ[ZMod 3] (Fin n → ZMod 3),
    A = Set.image (e : (Fin n → ZMod 3) → (Fin n → ZMod 3)) (cubeOrigin n)

/-- The sumset `A_1 + ⋯ + A_100` is all of `𝔽₃^n`. -/
def SumsetEqUniv (n : ℕ) (A : Fin 100 → Set (Fin n → ZMod 3)) : Prop :=
  ∀ v : Fin n → ZMod 3,
    ∃ a : Fin 100 → Fin n → ZMod 3,
      (∀ i, a i ∈ A i) ∧ v = Finset.sum (Finset.univ : Finset (Fin 100)) a

/-- For every `n ≥ 1`, the sum of any 100 cubes in `𝔽₃^n` is all of `𝔽₃^n`. -/
def conjecture : Prop :=
  ∀ (n : ℕ), 1 ≤ n →
    ∀ (A : Fin 100 → Set (Fin n → ZMod 3)),
      (∀ i, IsCube n (A i)) → SumsetEqUniv n A

-- Carried source audit `UM-00000157-Q001` (see the Moved/ record).

/--
Resolved true: Solved: Yang Yu (arXiv:2510.01300v2) proves that over Z_3 the union of any four
linear bases is an additive basis, so any four cubes (images of {0,1}^n under linear
automorphisms) already sum to F_3^n, and the remaining summands can be taken to be 0. Ben
Green's author-maintained 100 Open Problems (December 2025) marks this problem, current Problem
26, Solved on that basis; the analogue over F_p remains open. Source: Yang Yu, The Permanent
Rank of a Matrix (Part Three) Note on the Additive Basis Conjecture, arXiv:2510.01300v2,
https://arxiv.org/abs/2510.01300v2. Moved from `OpenConjectures/Combinatorics/GreenProblem69`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.GreenProblem69Wanted
