/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.SortingNetworks.ZeroOne

/-!
# Sorting distinct inputs suffices: the permutation principle

A companion of the 0-1 principle (`ZeroOne.lean`; see Knuth, *The Art of Computer Programming*,
Volume 3, Section 5.3.4): a comparator network sorts every input as soon as it sorts every input
with distinct values, in particular as soon as it sorts the `n!` permutations of `Fin n`.

Main results:

* `sorts_of_sorts_injective`: sorting every injective input `Fin n → ℕ` suffices. A Boolean input
  `v` is the monotone image `k ↦ decide (n ≤ k)` of the distinct-valued `spread v`
  (`spread_injective`, `decide_le_spread`), so the 0-1 principle applies.
* `sorts_of_sorts_perm` (**the permutation principle**): sorting every permutation of `Fin n`
  suffices. An injective input is the monotone image of the permutation that ranks it
  (`rank`, `rank_lt_rank`, `rank_injective`, `rankPerm`).

## Cost model

No cost model: these are statements about which inputs certify a network.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.SortingNetworks

variable {n : ℕ}

/-- **Spread of a Boolean input.** For a Boolean input $v$ on $n$ wires, the spread of $v$ is the
input with natural-number values whose value on wire $i < n$ is $n + i$ if $v(i)$ is true and $i$
if $v(i)$ is false.

The values of the spread are pairwise distinct. -/
def spread (v : Fin n → Bool) (i : Fin n) : ℕ := (if v i then n else 0) + i

theorem spread_injective (v : Fin n → Bool) : Function.Injective (spread v) := by
  intro i j h
  have hi := i.isLt
  have hj := j.isLt
  unfold spread at h
  apply Fin.ext
  split_ifs at h <;> omega

/-- **A Boolean input is a threshold of its spread.** For every Boolean input $v$ on $n$ wires,
applying the threshold map that sends a natural number $k$ to true if $n \le k$ and to false
otherwise to the spread of $v$ gives back $v$: for every wire $i$, the spread of $v$ at $i$ is at
least $n$ exactly when $v(i)$ is true.

Since the threshold map is monotone, $v$ is a monotone image of its spread. -/
theorem decide_le_spread (v : Fin n → Bool) : (fun k => decide (n ≤ k)) ∘ spread v = v := by
  funext i
  have := i.isLt
  simp only [Function.comp, spread]
  by_cases h : v i = true
  · simp [h]
  · simp only [Bool.not_eq_true] at h
    simp only [h, Bool.false_eq_true, ↓reduceIte, Nat.zero_add, decide_eq_false_iff_not, not_le]
    exact this

/-- **Sorting distinct inputs suffices**: a network that sorts every input with distinct natural
values sorts every input over every linear order. -/
theorem sorts_of_sorts_injective {net : Network n}
    (h : ∀ w : Fin n → ℕ, Function.Injective w → Monotone (run net w)) (α : Type*)
    [LinearOrder α] : Sorts net α := by
  refine sorts_of_sorts_bool (fun v => ?_) α
  have hf : Monotone fun k : ℕ => decide (n ≤ k) := fun a b hab => by
    simp only [decide_eq_true_eq, Bool.le_iff_imp]
    omega
  rw [← decide_le_spread v, run_comp hf]
  exact hf.comp (h _ (spread_injective v))

/-! ## The permutation principle -/

/-- **Rank among the values of an input.** For a map $w$ from $\{0, \dots, n-1\}$ to the natural
numbers and an index $i < n$, the rank of $w(i)$ among the values of $w$ is the number of indices
$j < n$ with $w(j) < w(i)$. It is less than $n$, so it is again an index in $\{0, \dots, n-1\}$. -/
def rank (w : Fin n → ℕ) (i : Fin n) : Fin n :=
  ⟨(Finset.univ.filter fun j => w j < w i).card, by
    calc (Finset.univ.filter fun j => w j < w i).card
        < (Finset.univ : Finset (Fin n)).card :=
          Finset.card_lt_card ⟨Finset.filter_subset _ _, fun h => by
            have := Finset.mem_filter.1 (h (Finset.mem_univ i)); omega⟩
      _ = n := Finset.card_fin n⟩

theorem rank_lt_rank {w : Fin n → ℕ} {i j : Fin n} (h : w i < w j) : rank w i < rank w j := by
  simp only [rank, Fin.mk_lt_mk]
  refine Finset.card_lt_card ⟨fun k hk => ?_, fun hsub => ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢; omega
  · have := hsub (Finset.mem_filter.2 ⟨Finset.mem_univ i, h⟩)
    simp at this

theorem rank_injective {w : Fin n → ℕ} (hw : Function.Injective w) :
    Function.Injective (rank w) := by
  intro i j h
  by_contra hne
  rcases lt_or_gt_of_ne (fun e => hne (hw e)) with hlt | hlt
  · exact absurd h (rank_lt_rank hlt).ne
  · exact absurd h (rank_lt_rank hlt).ne'

/-- **The ranking permutation.** For an injective map $w$ from $\{0, \dots, n-1\}$ to the natural
numbers, the ranking permutation of $w$ is the permutation of $\{0, \dots, n-1\}$ that sends each
$i$ to the rank of $w(i)$ among the values of $w$, that is, to the number of indices $j$ with
$w(j) < w(i)$. Since $w$ is injective, this map is a bijection.

The ranking permutation has the same relative order as $w$. -/
noncomputable def rankPerm {w : Fin n → ℕ} (hw : Function.Injective w) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (rank w) (Finite.injective_iff_bijective.1 (rank_injective hw))

/-- **The permutation principle.** A comparator network on $n$ wires that sorts each of the $n!$
permutations $\sigma$ of $\{0, \dots, n-1\}$, viewed as the input whose value on wire $i$ is
$\sigma(i)$, sorts every input over every linear order. -/
theorem sorts_of_sorts_perm {net : Network n}
    (h : ∀ σ : Equiv.Perm (Fin n), Monotone (run net σ)) (α : Type*) [LinearOrder α] :
    Sorts net α := by
  refine sorts_of_sorts_injective (fun w hw => ?_) α
  set σ := rankPerm hw
  have hσ : ∀ i, σ i = rank w i := fun i => rfl
  -- `w` is a monotone image of `σ`
  let g : Fin n → ℕ := fun k => w (σ.symm k)
  have hg : Monotone g := by
    intro k k' hkk'
    by_contra hlt
    push Not at hlt
    have := rank_lt_rank (w := w) (i := σ.symm k') (j := σ.symm k) hlt
    rw [← hσ, ← hσ, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
    exact absurd hkk' (not_le.2 this)
  have hw' : w = g ∘ σ := by
    funext i
    simp [g]
  rw [hw', run_comp hg]
  exact hg.comp (h σ)

end Cslib.Algorithms.Lean.SortingNetworks
