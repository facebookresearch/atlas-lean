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
/-- **The standard cube in $\mathbb{F}_3^n$.** For $n \in \mathbb{N}$, the standard cube is the set
$\{0, 1\}^n \subseteq \mathbb{F}_3^n$ of vectors each of whose coordinates is $0$ or $1$. -/
def cubeOrigin (n : ℕ) : Set (Fin n → ZMod 3) :=
  { x | ∀ i : Fin n, x i = 0 ∨ x i = 1 }

/-- **Cubes in $\mathbb{F}_3^n$.** A set $A \subseteq \mathbb{F}_3^n$ is a cube if there is an
$\mathbb{F}_3$-linear automorphism $e$ of $\mathbb{F}_3^n$ with $A = e(\{0, 1\}^n)$, the image of
the standard cube $\{0, 1\}^n$ under $e$. -/
def IsCube (n : ℕ) (A : Set (Fin n → ZMod 3)) : Prop :=
  ∃ e : (Fin n → ZMod 3) ≃ₗ[ZMod 3] (Fin n → ZMod 3),
    A = Set.image (e : (Fin n → ZMod 3) → (Fin n → ZMod 3)) (cubeOrigin n)

/-- **A sumset of $100$ sets equal to $\mathbb{F}_3^n$.** For sets
$A_1, \dots, A_{100} \subseteq \mathbb{F}_3^n$, the property that every $v \in \mathbb{F}_3^n$ can
be written as $v = a_1 + \dots + a_{100}$ with $a_i \in A_i$ for each $i$, that is,
$A_1 + \dots + A_{100} = \mathbb{F}_3^n$. -/
def SumsetEqUniv (n : ℕ) (A : Fin 100 → Set (Fin n → ZMod 3)) : Prop :=
  ∀ v : Fin n → ZMod 3,
    ∃ a : Fin 100 → Fin n → ZMod 3,
      (∀ i, a i ∈ A i) ∧ v = Finset.sum (Finset.univ : Finset (Fin 100)) a

/-- **Green's problem on sums of $100$ cubes in $\mathbb{F}_3^n$.** The statement that for every
$n \ge 1$ and every family $A_1, \dots, A_{100}$ of cubes in $\mathbb{F}_3^n$ (not necessarily
distinct), that is, images of $\{0, 1\}^n$ under linear automorphisms of $\mathbb{F}_3^n$, the
sumset $A_1 + \dots + A_{100}$ is all of $\mathbb{F}_3^n$. -/
def conjecture : Prop :=
  ∀ (n : ℕ), 1 ≤ n →
    ∀ (A : Fin 100 → Set (Fin n → ZMod 3)),
      (∀ i, IsCube n (A i)) → SumsetEqUniv n A

-- Carried source audit `UM-00000157-Q001` (see the Moved/ record).

/--
**Any $100$ cubes sum to all of $\mathbb{F}_3^n$.** For every $n \ge 1$ and every family
$A_1, \dots, A_{100}$ of cubes in $\mathbb{F}_3^n$ (not necessarily distinct), that is, images
of $\{0, 1\}^n$ under linear automorphisms of $\mathbb{F}_3^n$, the sumset
$A_1 + \dots + A_{100}$ is all of $\mathbb{F}_3^n$.

Yang Yu proves that over $\mathbb{F}_3$ the union of any four linear bases is an additive basis,
so any four cubes already sum to $\mathbb{F}_3^n$, and the remaining summands can be taken to be
$0$. Ben Green's author-maintained 100 Open Problems (December 2025) marks this problem, current
Problem 26, solved on that basis; the analogue over $\mathbb{F}_p$ remains open.

Source: Yang Yu, The Permanent
Rank of a Matrix (Part Three) Note on the Additive Basis Conjecture, arXiv:2510.01300v2,
https://arxiv.org/abs/2510.01300v2. Moved from `OpenConjectures/Combinatorics/GreenProblem69`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.GreenProblem69Wanted
