/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Notation
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Hom.Basic

/-!
# Classical permutation pattern containment

`HasPattern` expresses classical pattern containment by an increasing sequence of positions.
The decision procedure checks the index and value comparisons on the finite set of position maps.

## References

* Juan B. Gil, Felix H. Xu, and William Y. Zhu, *Odd-Indexed Fibonacci Numbers via Pattern-Avoiding
  Permutations*, INTEGERS 25 (2025), Article A79, pp. 1–19, Section 1.
* Tian Han, *Joint Distributions of 10 Classical Statistics over Permutations Avoiding Two Patterns
  of Length 3*, INTEGERS 26 (2026), Article A18, pp. 1–22, Section 1.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.Enumerative.OddFibonacciWanted

/-- **Classical pattern containment in a permutation.** Let $\sigma$ be a permutation of
$\{0, 1, \dots, n-1\}$ and let $\pi$ be a map from $\{0, 1, \dots, k-1\}$ to itself. Then
$\sigma$ contains the pattern $\pi$ if there are positions $e_0 < e_1 < \dots < e_{k-1}$ in
$\{0, 1, \dots, n-1\}$ such that for all $i, j < k$, $\sigma(e_i) < \sigma(e_j)$ holds exactly
when $\pi(i) < \pi(j)$. -/
def HasPattern {n k : ℕ} (σ : Equiv.Perm (Fin n))
    (π : Fin k → Fin k) : Prop :=
  ∃ e : Fin k → Fin n, (∀ i j : Fin k, i < j → e i < e j) ∧
    ∀ i j : Fin k, σ (e i) < σ (e j) ↔ π i < π j

/-- **Pattern containment by an order embedding.** A classical occurrence of `π` in `σ`
is an order embedding of the pattern's positions into the permutation's positions that
identifies all the corresponding strict value comparisons. -/
theorem hasPattern_iff_exists_orderEmbedding {n k : ℕ} (σ : Equiv.Perm (Fin n))
    (π : Fin k → Fin k) :
    HasPattern σ π ↔ ∃ e : Fin k ↪o Fin n, ∀ i j, σ (e i) < σ (e j) ↔ π i < π j := by
  constructor
  · rintro ⟨e, he, h⟩
    exact ⟨OrderEmbedding.ofStrictMono e (fun _ _ hij => he _ _ hij), h⟩
  · rintro ⟨e, h⟩
    exact ⟨e, fun _ _ hij => e.strictMono hij, h⟩

end MathlibExt.Combinatorics.Enumerative.OddFibonacciWanted

namespace MetaMathlibExt

open MathlibExt.Combinatorics.Enumerative.OddFibonacciWanted (HasPattern)

/-- Classical pattern containment `HasPattern σ π` is decidable by checking each map of
pattern indices to positions for strictly increasing positions and matching value comparisons. -/
instance instDecidableHasPattern {n k : ℕ} (σ : Equiv.Perm (Fin n)) (π : Fin k → Fin k) :
    Decidable (HasPattern σ π) := by
  unfold HasPattern
  infer_instance

end MetaMathlibExt
