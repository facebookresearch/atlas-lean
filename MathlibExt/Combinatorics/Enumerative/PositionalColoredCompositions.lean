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

The count weights a composition by the product of its parts in a given residue class
of positions. When the first part is uncolored, splitting on its size gives a recurrence.
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

namespace positionalColoredCompositionCount_succ

private def growFirst {ℓ : ℕ} (hℓ : 1 ≤ ℓ) : Composition ℓ → Composition (ℓ + 1)
  | ⟨[], _, hs⟩ => by simp at hs; omega
  | ⟨p :: ps, hp, hs⟩ =>
    ⟨(p + 1) :: ps, by
      intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · exact Nat.succ_pos _
      · exact hp (List.mem_cons_of_mem _ hi), by
      simp only [List.sum_cons] at hs ⊢
      omega⟩

private def prependOne {ℓ : ℕ} (c : Composition ℓ) : Composition (ℓ + 1) :=
  ⟨1 :: c.blocks, by
    intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · decide
    · exact c.blocks_pos hi, by simp [Nat.add_comm]⟩

/-- Split at the first part. The two inverse operations increase it or prepend a one. -/
private def firstPartEquiv {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    Composition (ℓ + 1) ≃ Composition ℓ ⊕ Composition ℓ where
  toFun
    | ⟨[], _, hs⟩ => by simp at hs
    | ⟨0 :: _, hp, _⟩ => by simp at hp
    | ⟨1 :: ps, hp, hs⟩ => .inr ⟨ps, fun hi => hp (List.mem_cons_of_mem _ hi), by
        simp only [List.sum_cons] at hs
        omega⟩
    | ⟨(p + 2) :: ps, hp, hs⟩ => .inl ⟨(p + 1) :: ps, by
        intro i hi
        rcases List.mem_cons.mp hi with rfl | hi
        · exact Nat.succ_pos _
        · exact hp (List.mem_cons_of_mem _ hi), by
        simp only [List.sum_cons] at hs ⊢
        omega⟩
  invFun := Sum.elim (growFirst hℓ) prependOne
  left_inv := by
    rintro ⟨_ | ⟨(_ | _ | p), ps⟩, hp, hs⟩
    · simp at hs
    · simp at hp
    · rfl
    · rfl
  right_inv := by
    rintro (⟨_ | ⟨(_ | p), ps⟩, hp, hs⟩ | c)
    · simp at hs
      omega
    · simp at hp
    · rfl
    · rfl

private abbrev weight (m k : ℕ) (ps : List ℕ) :=
  (ps.mapIdx fun i p => if (i + 1) % m = k % m then p else 1).prod

private theorem weight_cons {m k : ℕ} (hm : 1 ≤ m) (hmk : ¬ m ∣ k) (p : ℕ) (ps : List ℕ) :
    weight m (k + 1) (p :: ps) = weight m k ps := by
  have shift (i : ℕ) : (i + 1) % m = (k + 1) % m ↔ i % m = k % m :=
    Nat.ModEq.add_iff_right (Nat.ModEq.refl 1)
  have first : 0 % m ≠ k % m := fun h =>
    hmk (Nat.dvd_of_mod_eq_zero (h.symm.trans (Nat.mod_eq_of_lt hm)))
  simp only [weight, List.mapIdx_cons, shift, ite_eq_right first, List.prod_cons, one_mul]

end positionalColoredCompositionCount_succ

open positionalColoredCompositionCount_succ in
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
  change (∑ c : Composition (ℓ + 1), weight m (k + 1) c.blocks) = _
  rw [← Equiv.sum_comp (firstPartEquiv hℓ).symm, Fintype.sum_sum_type]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    rintro ⟨_ | ⟨p, ps⟩, hp, hs⟩ _
    · simp at hs
      omega
    · change weight m (k + 1) ((p + 1) :: ps) = weight m (k + 1) (p :: ps)
      rw [weight_cons hm hmk, weight_cons hm hmk]
  · apply Finset.sum_congr rfl
    intro c _
    exact weight_cons hm hmk 1 c.blocks

end

end MetaMathlibExt
