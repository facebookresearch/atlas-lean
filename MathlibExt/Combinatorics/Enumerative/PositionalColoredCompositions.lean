/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Nat.ModEq

/-!
# Positional colored compositions

The number of compositions with colors at prescribed positions satisfies a two-term recurrence
when the first part is uncolored.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Positional colored compositions.** For natural numbers $m$, $k$ and $\ell$, $c_{m,k}(\ell)$
is the number of $(m, k)$-colored compositions of $\ell$: compositions of $\ell$ in which every
part whose position, counted from $1$, is congruent to $k$ modulo $m$ gets one of $p$ colors,
where $p$ is the part, and the other parts are uncolored. Equivalently, $c_{m,k}(\ell)$ is the
sum, over all compositions $(p_1, \dots, p_r)$ of $\ell$, of the product of the parts $p_i$ with
$i \equiv k \pmod m$.

The paper takes $m \ge 1$. For $m = 0$, congruence modulo $0$ is equality, so only the part at
position exactly $k$ is colored.

Source: Andrew Li and Hua Wang, *Combinatorics of Positional Colored Compositions*, INTEGERS 26
(2026), Article A49, Definition 1. -/
public def positionalColoredCompositionCount (m k ℓ : ℕ) : ℕ :=
  ∑ c : Composition ℓ, (c.blocks.mapIdx fun i p => if (i + 1) % m = k % m then p else 1).prod

/-- **Colored compositions of zero.** For all natural numbers $m$ and $k$, $c_{m,k}(0) = 1$: the
only composition of $0$ is the empty one.

Source: Andrew Li and Hua Wang, *Combinatorics of Positional Colored Compositions*, INTEGERS 26
(2026), Article A49, Definition 1. -/
public theorem positionalColoredCompositionCount_zero (m k : ℕ) :
    positionalColoredCompositionCount m k 0 = 1 := by
  have h : (Finset.univ : Finset (Composition 0)) = {Composition.ones 0} := by decide
  simp [positionalColoredCompositionCount, h, Composition.ones]

namespace PositionalColoredCompositions

/-- Increase the first part in the left copy, or prepend a unit part in the right copy. -/
private def extend {n : ℕ} (hn : 1 ≤ n) :
    Composition n ⊕ Composition n → Composition (n + 1)
  | .inl ⟨[], _, hs⟩ => by simp at hs; omega
  | .inl ⟨p :: ps, hp, hs⟩ =>
    ⟨(p + 1) :: ps, by
      simpa using fun i (hi : i ∈ ps) => hp (List.mem_cons_of_mem _ hi), by
      simp only [List.sum_cons] at hs ⊢
      omega⟩
  | .inr c =>
    ⟨1 :: c.blocks, by simpa using fun i (hi : i ∈ c.blocks) => c.blocks_pos hi, by
      simp [Nat.add_comm]⟩

/-- Undo the extension according to the size of the first part. -/
private def shorten {n : ℕ} : Composition (n + 1) → Composition n ⊕ Composition n
  | ⟨[], _, hs⟩ => by simp at hs
  | ⟨0 :: _, hp, _⟩ => by have := hp List.mem_cons_self; omega
  | ⟨1 :: ps, hp, hs⟩ =>
    .inr ⟨ps, fun hi => hp (List.mem_cons_of_mem _ hi), by simp only [List.sum_cons] at hs; omega⟩
  | ⟨(p + 2) :: ps, hp, hs⟩ =>
    .inl ⟨(p + 1) :: ps, by
      simpa using fun i (hi : i ∈ ps) => hp (List.mem_cons_of_mem _ hi), by
      simp only [List.sum_cons] at hs ⊢
      omega⟩

private def extendEquiv {n : ℕ} (hn : 1 ≤ n) :
    Composition n ⊕ Composition n ≃ Composition (n + 1) where
  toFun := extend hn
  invFun := shorten
  left_inv := by
    rintro (⟨_ | ⟨_ | p, ps⟩, hp, hs⟩ | c)
    · simp at hs; omega
    · have := hp List.mem_cons_self; omega
    · rfl
    · rfl
  right_inv := by
    rintro ⟨_ | ⟨_ | _ | p, ps⟩, hp, hs⟩
    · simp at hs
    · have := hp List.mem_cons_self; omega
    · rfl
    · rfl

end PositionalColoredCompositions

open PositionalColoredCompositions

-- The source assumes a positive modulus. Modular cancellation also works at modulus zero.
set_option linter.unusedVariables false in
/-- **A recurrence for positional colored compositions.** For natural numbers $m$, $k$ and $\ell$
with $m \ge 1$, $m \nmid k$ and $\ell \ge 1$,
$c_{m,k+1}(\ell + 1) = c_{m,k+1}(\ell) + c_{m,k}(\ell)$.

The paper prints the hypotheses $k \ge 1$, $\ell \ge 2$ and $1 \le m \le \ell - 1$, which allow
$m \mid k$; there the identity fails: for $m = 1$, $k = 1$ and $\ell = 2$ one has
$c_{1,2}(3) = 8$ but $c_{1,2}(2) + c_{1,1}(2) = 6$. The paper's argument (remove a first part
$1$ or decrease the first part) needs the first part to be uncolored, which is the condition
$m \nmid k$.

Source: Andrew Li and Hua Wang, *Combinatorics of Positional Colored Compositions*, INTEGERS 26
(2026), Article A49, Theorem 6 (`integers-2026-A49-thm-6`). -/
public theorem positionalColoredCompositionCount_succ (m k ℓ : ℕ) (hm : 1 ≤ m)
    (hmk : ¬ m ∣ k) (hℓ : 1 ≤ ℓ) :
    positionalColoredCompositionCount m (k + 1) (ℓ + 1) =
      positionalColoredCompositionCount m (k + 1) ℓ + positionalColoredCompositionCount m k ℓ := by
  have firstUncolored : ¬ 1 % m = (k + 1) % m := fun h => hmk (Nat.right_modEq_add_iff.mp h)
  have shift (i : ℕ) : (i + 1 + 1) % m = (k + 1) % m ↔ (i + 1) % m = k % m :=
    Nat.ModEq.add_iff_right (Nat.ModEq.refl 1)
  unfold positionalColoredCompositionCount
  rw [← Equiv.sum_comp (extendEquiv hℓ), Fintype.sum_sum_type]
  congr 1
  · apply Finset.sum_congr rfl
    rintro ⟨_ | ⟨p, ps⟩, hp, hs⟩ _
    · simp at hs; omega
    · simp [extendEquiv, extend, List.mapIdx_cons, firstUncolored]
  · apply Finset.sum_congr rfl
    intro c _
    simp [extendEquiv, extend, List.mapIdx_cons, shift]

end

end MetaMathlibExt
