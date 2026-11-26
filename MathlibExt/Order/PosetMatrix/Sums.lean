/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Matrix.Block
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Order.Sum.Order
public import MathlibExt.Order.PosetMatrix

/-!
# Direct and ordinal sums of poset matrices

The direct and ordinal block sums of two poset matrices represent the corresponding sums of posets.
-/

namespace MetaMathlibExt

open Matrix

/-- **Direct and ordinal sums of poset matrices represent sums of posets.** A poset matrix $M$ of
order $n$, a Boolean matrix with rows and columns indexed by $0, \dots, n - 1$, represents a
partial order $P$ when there is a bijection $e$ from $\{0, \dots, n - 1\}$ to $P$ such that
$e(i) \le e(j)$ if and only if $M_{ij}$ is true. Let $A$ and $B$ be poset matrices of orders $m$
and $k$ representing partial orders $P$ and $Q$. Let $A \oplus B$ and $A \boxplus B$ be the
matrices $N$ of order $m + k$ with $N_{ij} = A_{ij}$ for $i, j < m$, $N_{m+i, m+j} = B_{ij}$ for
$i, j < k$, and $N_{ij}$ false for all $j < m \le i$, where $N_{ij}$ for $i < m \le j$ is false
in $A \oplus B$ and true in $A \boxplus B$. Then $A \oplus B$ is a poset matrix representing the
disjoint sum $P + Q$, in which no element of $P$ is comparable with an element of $Q$, and
$A \boxplus B$ is a poset matrix representing the ordinal sum $P \oplus Q$, in which every
element of $P$ lies below every element of $Q$.

Only sums of two terms are stated; sums of $r$ terms follow by iterating.

Source: Salah Uddin Mohammad, Md. Shah Noor, and Md. Rashed Talukder, *Recognition and
Enumeration of the Quasi-Full Rooted Trees*, Journal of Integer Sequences 28 (2025),
Article 25.6.3, Theorem 4 (`jis-2025-25.6.3-thm-4`). -/
public theorem directSum_ordinalSum_represents {P Q : Type*} [PartialOrder P]
    [PartialOrder Q] (m k : ℕ) (A : Matrix (Fin m) (Fin m) Bool) (B : Matrix (Fin k) (Fin k) Bool)
    (hA : IsPosetMatrix m A) (hB : IsPosetMatrix k B) (eA : Fin m ≃ P)
    (heA : ∀ i j, eA i ≤ eA j ↔ A i j = true) (eB : Fin k ≃ Q)
    (heB : ∀ i j, eB i ≤ eB j ↔ B i j = true) :
    (IsPosetMatrix (m + k) (reindex finSumFinEquiv finSumFinEquiv
        (fromBlocks A (Matrix.of fun _ _ => false) (Matrix.of fun _ _ => false) B)) ∧
      ∃ e : Fin (m + k) ≃ P ⊕ Q, ∀ i j, e i ≤ e j ↔
        reindex finSumFinEquiv finSumFinEquiv
          (fromBlocks A (Matrix.of fun _ _ => false) (Matrix.of fun _ _ => false) B) i j =
            true) ∧
    (IsPosetMatrix (m + k) (reindex finSumFinEquiv finSumFinEquiv
        (fromBlocks A (Matrix.of fun _ _ => true) (Matrix.of fun _ _ => false) B)) ∧
      ∃ e : Fin (m + k) ≃ P ⊕ₗ Q, ∀ i j, e i ≤ e j ↔
        reindex finSumFinEquiv finSumFinEquiv
          (fromBlocks A (Matrix.of fun _ _ => true) (Matrix.of fun _ _ => false) B) i j =
            true) := by
  -- Both sums have a constant upper-right block and a false lower-left block.
  have poset (b : Bool) : IsPosetMatrix (m + k) (reindex finSumFinEquiv finSumFinEquiv
      (fromBlocks A (Matrix.of fun _ _ => b) (Matrix.of fun _ _ => false) B)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro i j
      induction i using Fin.addCases <;> induction j using Fin.addCases
      · simpa [submatrix] using hA.upper _ _
      · intro hij
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hij
        omega
      · simp [submatrix]
      · simpa [submatrix] using hB.upper _ _
    · intro i
      induction i using Fin.addCases <;> simp [submatrix, hA.diagonal, hB.diagonal]
    · intro i j l
      induction i using Fin.addCases <;> induction j using Fin.addCases <;>
        induction l using Fin.addCases
      case left.left.left i j l => simpa [submatrix] using hA.transitive i j l
      case right.right.right i j l => simpa [submatrix] using hB.transitive i j l
      all_goals simp +contextual [submatrix]
  let e := finSumFinEquiv.symm.trans (eA.sumCongr eB)
  refine ⟨⟨poset false, e, ?_⟩, ⟨poset true, e.trans toLex, ?_⟩⟩
  all_goals
    intro i j
    induction i using Fin.addCases <;> induction j using Fin.addCases <;>
      simp [e, submatrix, heA, heB]

end MetaMathlibExt
