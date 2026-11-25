/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.GCDMonoid.Multiset
public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.Combinatorics.Enumerative.Partition.Basic

/-!
# The Landau function

The Landau function is the maximum least common multiple of the parts of an
integer partition of `n`.

## References

- [E. Rowland, M. Stipulanti, R. Yassawi, *An elementary proof of Bridy's
  theorem*](https://arxiv.org/abs/2308.10977)
-/

@[expose] public section

namespace Nat

namespace Partition

/-- **Least common multiple of the parts of a partition.** For a natural number $n$ and a
partition $p$ of $n$, this is the least common multiple of the parts of $p$, taken with
the convention that it equals $1$ when $p$ has no parts. -/
def partsLCM {n : ℕ} (p : n.Partition) : ℕ :=
  p.parts.lcm

@[simp]
theorem partsLCM_zero (p : Partition 0) : p.partsLCM = 1 := by
  simp [partsLCM]

@[simp]
theorem partsLCM_one (p : Partition 1) : p.partsLCM = 1 := by
  simp [partsLCM]

end Partition

/-- **Landau's function.** For a natural number $n$, Landau's function at $n$ is the maximum, over
all partitions $p$ of $n$, of the least common multiple of the parts of $p$. -/
def landauFunction (n : ℕ) : ℕ :=
  Finset.univ.sup (fun p : n.Partition => p.partsLCM)

/-- **The Landau function bounds the LCM of the parts.** For every natural number $n$ and every
partition $p$ of $n$, the least common multiple of the parts of $p$ is at most the Landau function
at $n$. -/
theorem Partition.partsLCM_le_landauFunction {n : ℕ} (p : n.Partition) :
    p.partsLCM ≤ landauFunction n := by
  exact Finset.le_sup (Finset.mem_univ p)

/-- **The Landau function is attained.** For every natural number $n$, some partition of $n$
has least common multiple of its parts equal to the Landau function at $n$. -/
theorem exists_partition_partsLCM_eq_landauFunction (n : ℕ) :
    ∃ p : n.Partition, p.partsLCM = landauFunction n := by
  obtain ⟨p, _, hp⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset n.Partition)
    ⟨Partition.indiscrete n, Finset.mem_univ _⟩ Partition.partsLCM
  exact ⟨p, hp.symm⟩

@[simp]
theorem landauFunction_zero : landauFunction 0 = 1 := by
  simp [landauFunction]

@[simp]
theorem landauFunction_one : landauFunction 1 = 1 := by
  simp [landauFunction]

end Nat
