/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Hindman
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Preorder.Finite

/-!
# Hindman's finite sums theorem on the natural numbers

`Hindman.FS_partition_regular` in `Mathlib.Combinatorics.Hindman` proves Hindman's theorem for
streams in any additive semigroup: in a finite cover of the finite sums of a stream, one part
contains all the finite sums of another stream. This file deduces the version for sets of natural
numbers: every finite coloring of `ℕ = {0, 1, 2, …}` has an infinite set `A` whose finite sums,
the sums of the nonempty finite subsets of `A`, all have the same color.

## Main statements

* `MetaMathlibExt.exists_infinite_finiteSums_monochromatic`: for every finite coloring
  `c : ℕ → Fin r` there are an infinite set `A ⊆ ℕ` and a color `k` such that
  `c (∑ a ∈ F, a) = k` for every nonempty finite `F ⊆ A`.

## Proof

On `ℕ` the stream form alone says little, since the constant stream `0, 0, …` has the single
finite sum `0`. So we cover the finite sums of the constant stream `1, 1, …`, which are positive,
by the sets `{n | c n = k ∧ 0 < n}`. One of them contains all the finite sums of a stream `b`, and
the terms of `b` are then positive. Let `dₙ` be the sum of the `bᵢ` over the block of indices
`2ⁿ ≤ i < 2ⁿ⁺¹`. Then `dₙ ≥ 2ⁿ > n`, so the range `A` of `d` is infinite. A nonempty finite
`F ⊆ A` is the image under `d` of a set of indices on which `d` is injective. As the blocks are
disjoint, the sum of `F` is then the sum of `b` over a nonempty finite set of indices, which is a
finite sum of `b`.
-/

namespace MetaMathlibExt

namespace exists_infinite_finiteSums_monochromatic

/-- Every finite sum of a stream of positive natural numbers is positive. -/
private theorem pos_of_FS {a : Stream' ℕ} {m : ℕ} (hm : Hindman.FS a m)
    (ha : ∀ i, 0 < a.get i) : 0 < m := by
  induction hm with
  | head a => exact ha 0
  | of_tail a m _ ih => exact ih fun i => Stream'.get_tail ▸ ha (i + 1)
  | cons a m _ ih => exact Nat.add_pos_left (ha 0) m

/-- The finite sums of a stream `b` of positive natural numbers contain the finite sums of an
infinite set, namely the set of sums of `b` over the disjoint blocks of indices
`[2 ^ n, 2 ^ (n + 1))`. -/
private theorem exists_infinite_of_pos {b : Stream' ℕ} (hb : ∀ i, 0 < b.get i) :
    ∃ A : Set ℕ, A.Infinite ∧ ∀ F : Finset ℕ, F.Nonempty → (F : Set ℕ) ⊆ A →
      Hindman.FS b (∑ a ∈ F, a) := by
  classical
  set block : ℕ → Finset ℕ := fun n => Finset.Ico (2 ^ n) (2 ^ (n + 1)) with hblock
  have hcard (n : ℕ) : (block n).card = 2 ^ n := by
    simp only [hblock, Nat.card_Ico, pow_succ]
    omega
  have hdisj (i j : ℕ) (hij : i ≠ j) : Disjoint (block i) (block j) := by
    rw [Finset.disjoint_left]
    intro x hxi hxj
    simp only [hblock, Finset.mem_Ico] at hxi hxj
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · have := Nat.pow_le_pow_right Nat.two_pos h
      omega
    · have := Nat.pow_le_pow_right Nat.two_pos h
      omega
  -- The block sums `d n` grow without bound, so their range is infinite.
  set d : ℕ → ℕ := fun n => ∑ i ∈ block n, b.get i
  have hd (n : ℕ) : n < d n :=
    calc n < 2 ^ n := Nat.lt_two_pow_self
      _ = (block n).card := (hcard n).symm
      _ ≤ d n := by
        simpa using Finset.card_nsmul_le_sum (block n) (fun i => b.get i) 1 fun i _ => hb i
  refine ⟨Set.range d, Set.infinite_of_forall_exists_gt fun n => ⟨d n, ⟨n, rfl⟩, hd n⟩, ?_⟩
  -- Write `F` as the image under `d` of the indices `g x`, `x ∈ F`, on which `d` is injective.
  intro F hF hFd
  set g := Function.invFun d
  have hg (x : ℕ) (hx : x ∈ F) : d (g x) = x := Function.invFun_eq (hFd hx)
  have hginj : Set.InjOn g F := fun x hx y hy hxy => by
    rw [← hg x hx, ← hg y hy, hxy]
  have hsum : ∑ a ∈ F, a = ∑ i ∈ (F.image g).biUnion block, b.get i := by
    rw [Finset.sum_biUnion fun i _ j _ hij => hdisj i j hij, Finset.sum_image hginj]
    exact Finset.sum_congr rfl fun x hx => (hg x hx).symm
  rw [hsum]
  refine Hindman.FS.finsetSum b _ ((hF.image g).biUnion fun i _ => ?_)
  rw [← Finset.card_pos, hcard]
  exact Nat.two_pow_pos i

end exists_infinite_finiteSums_monochromatic

open exists_infinite_finiteSums_monochromatic in
/-- **Hindman's finite sums theorem.** For every finite coloring of
$\mathbb{N} = \{0, 1, 2, \dots\}$ there is an infinite set $A \subseteq \mathbb{N}$ whose set of
finite sums $\mathrm{FS}(A) = \{\sum_{a \in F} a : F \subseteq A \text{ finite and nonempty}\}$ is
monochromatic.

Source: Mauro Di Nasso and Renling Jin, *From Schur's Theorem to the Pairwise Sum Theorem*,
INTEGERS 25 (2025), Article A105, Theorem 1.1 (`integers-2025-A105-thm-1-1`). -/
public theorem exists_infinite_finiteSums_monochromatic {r : ℕ} (c : ℕ → Fin r) :
    ∃ A : Set ℕ, A.Infinite ∧ ∃ k : Fin r, ∀ F : Finset ℕ, F.Nonempty → (F : Set ℕ) ⊆ A →
      c (∑ a ∈ F, a) = k := by
  -- The finite sums of the constant stream `1, 1, …` are positive, so the sets
  -- `{n | c n = k ∧ 0 < n}` cover them.
  obtain ⟨_, ⟨k, rfl⟩, b, hb⟩ := Hindman.FS_partition_regular (Stream'.const 1)
    (Set.range fun k : Fin r => {n | c n = k ∧ 0 < n}) (Set.finite_range _)
    fun m hm => Set.mem_sUnion.2 ⟨_, ⟨c m, rfl⟩, rfl, pos_of_FS hm fun _ => Nat.one_pos⟩
  obtain ⟨A, hA, hAb⟩ := exists_infinite_of_pos fun i => (hb _ (Hindman.FS.singleton b i)).2
  exact ⟨A, hA, k, fun F hF hFA => (hb _ (hAb F hF hFA)).1⟩

end MetaMathlibExt
