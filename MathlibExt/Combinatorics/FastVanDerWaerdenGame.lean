/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.LinearCombination

/-!
# Fast van der Waerden game

This module defines Maker's bounded winning condition and symmetry for finite sets of rationals.
The theorem `isSymmetricOfType_cases` classifies the possible symmetry types of a set of size
at least four.
-/

@[expose] public section

namespace MetaMathlibExt.FastVanDerWaerdenGame

open Finset

/-- **Containing a homothetic copy.** Let $S$ and $M$ be finite sets of natural numbers. $M$
contains a homothetic copy of $S$ if there are a natural number $a > 0$ and an integer $b$ such
that $as + b \in M$ for every $s \in S$, that is, $aS + b \subseteq M$. This is Maker's winning
condition.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40, Section 1. -/
def ContainsCopy (S M : Finset ℕ) : Prop :=
  ∃ a : ℕ, 0 < a ∧ ∃ b : ℤ, ∀ s ∈ S, ∃ m ∈ M, (m : ℤ) = a * s + b

/-- **Maker wins within $p$ moves.** Let $S$ be a finite set of natural numbers. In the
$S$-game, Maker and Breaker alternately claim unclaimed natural numbers, and Maker wins once the
numbers Maker has claimed contain a copy $aS + b = \{as + b : s \in S\}$ of $S$, where $a$ is a
positive integer and $b$ is an integer. Let $M$ and $B$ be finite sets of natural numbers
(claimed by Maker and by Breaker) and $p$ a natural number, with Maker to move. Maker wins
within $p$ moves if $M$ already contains such a copy of $S$, or if $p \ge 1$ and there is a
number $x \notin M \cup B$ such that for every number $y \ne x$ with $y \notin M \cup B$, Maker
wins within $p - 1$ moves from the position where Maker has claimed $M \cup \{x\}$ and Breaker
has claimed $B \cup \{y\}$.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40, Sections 1
and 5 (`p`-move strategy). -/
def MakerWinsWithin (S : Finset ℕ) : ℕ → Finset ℕ → Finset ℕ → Prop
  | 0, M, _ => ContainsCopy S M
  | p + 1, M, B => ContainsCopy S M ∨
      ∃ x : ℕ, x ∉ M ∧ x ∉ B ∧
        ∀ y : ℕ, y ≠ x → y ∉ M → y ∉ B → MakerWinsWithin S p (insert x M) (insert y B)

/-- **Copies of finite sets of rationals.** Let $A$ and $B$ be finite sets of rational numbers.
$B$ is a copy of $A$ if there are rationals $a > 0$ and $b$ such that
$B = aA + b = \{ax + b : x \in A\}$.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40, Section 5. -/
def IsRatCopy (A B : Finset ℚ) : Prop :=
  ∃ a b : ℚ, 0 < a ∧ B = A.image fun x => a * x + b

/-- **Reflections of finite sets of rationals.** Let $A$ and $B$ be finite sets of rational
numbers. $B$ is a reflection of $A$ if there are rationals $a < 0$ and $b$ such that
$B = aA + b = \{ax + b : x \in A\}$.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40, Section 6. -/
def IsRatReflection (A B : Finset ℚ) : Prop :=
  ∃ a b : ℚ, a < 0 ∧ B = A.image fun x => a * x + b

/-- **Symmetric sets of a given type.** Let $S = \{s_0 < s_1 < \dots < s_{n-1}\}$ be a finite
set of $n$ rational numbers and let $i, j < n$. Then $S$ is called symmetric of type $(i, j)$ if
$i < j$ and $S \setminus \{s_i\}$ is a copy of $S \setminus \{s_j\}$.

Positions are counted from $0$, so the paper's type $(i + 1, j + 1)$ is the type $(i, j)$ here.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40,
Definition 2. -/
def IsSymmetricOfType (S : Finset ℚ) (i j : Fin S.card) : Prop :=
  i < j ∧ IsRatCopy (S.erase (S.orderEmbOfFin rfl j)) (S.erase (S.orderEmbOfFin rfl i))

/-- **Symmetric sets of rationals.** A finite set $S$ of rational numbers is symmetric if it is
symmetric of some type $(i, j)$ with $i, j < |S|$.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40,
Definition 2. -/
def IsSymmetric (S : Finset ℚ) : Prop :=
  ∃ i j : Fin S.card, IsSymmetricOfType S i j

/-- **The zero-geometric set $S_2(n, k)$.** For a natural number $n$ and a rational number $k$,
$S_2(n, k)$ is the finite set of rationals $\{0\} \cup \{k^i : 0 \le i < n - 1\}$, that is,
$\{0, 1, k, \dots, k^{n-2}\}$ when $n \ge 2$ and $\{0\}$ when $n \le 1$.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40,
Definition 3. -/
def zeroGeometricSet (n : ℕ) (k : ℚ) : Finset ℚ :=
  insert 0 ((range (n - 1)).image fun i => k ^ i)

/-- **Every finite set contains a copy of the empty set.** Every finite set $M$ of natural
numbers contains a homothetic copy of the empty set.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40, Section 1. -/
theorem containsCopy_empty (M : Finset ℕ) : ContainsCopy ∅ M :=
  ⟨1, Nat.one_pos, 0, by simp⟩

/-- **Winning within zero moves.** Let $S$ be a finite set of natural numbers, and let $M$ and
$B$ be finite sets of natural numbers. Maker wins the $S$-game within $0$ moves from the position
where Maker has claimed $M$ and Breaker has claimed $B$ if and only if $M$ contains a copy
$aS + b = \{as + b : s \in S\}$ of $S$, where $a$ is a positive integer and $b$ is an integer.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40, Section 5. -/
theorem makerWinsWithin_zero (S M B : Finset ℕ) :
    MakerWinsWithin S 0 M B ↔ ContainsCopy S M := Iff.rfl

/-- **Every finite set of rationals is a copy of itself.** For every finite set $A$ of rational
numbers, $A$ is a copy of $A$.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40, Section 5. -/
theorem isRatCopy_refl (A : Finset ℚ) : IsRatCopy A A :=
  ⟨1, 0, one_pos, by simp⟩

/-- **The zero-geometric set $S_2(1, k)$ is $\{0\}$.** For every rational number $k$, the
zero-geometric set $S_2(1, k)$ equals $\{0\}$.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40,
Definition 3. -/
theorem zeroGeometricSet_one (k : ℚ) : zeroGeometricSet 1 k = {0} := by
  simp [zeroGeometricSet]

/-- **The zero-geometric set $S_2(n + 2, k)$.** For every natural number $n$ and every rational
$k$, $S_2(n + 2, k) = \{0\} \cup \{k^i : 0 \le i \le n\} = \{0, 1, k, \dots, k^n\}$.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40,
Definition 3. -/
theorem zeroGeometricSet_add_two (n : ℕ) (k : ℚ) :
    zeroGeometricSet (n + 2) k = insert 0 ((range (n + 1)).image fun i => k ^ i) := rfl

/-- An increasing affine copy matches the surviving elements in rank order. -/
private theorem affine_eq_at_rank {S : Finset ℚ} {n : ℕ} (hn : S.card = n + 1)
    (i j : Fin (n + 1)) {a b : ℚ} (ha : 0 < a)
    (hcopy : S.erase (S.orderEmbOfFin hn i) =
      (S.erase (S.orderEmbOfFin hn j)).image fun x => a * x + b) (k : Fin n) :
    a * S.orderEmbOfFin hn (j.succAbove k) + b = S.orderEmbOfFin hn (i.succAbove k) := by
  let s := S.orderEmbOfFin hn
  have hmem (p : Fin (n + 1)) (l : Fin n) : s (p.succAbove l) ∈ S.erase (s p) :=
    mem_erase.mpr ⟨s.injective.ne (p.succAbove_ne l), S.orderEmbOfFin_mem hn _⟩
  have hcard : (S.erase (s i)).card = n := by
    rw [card_erase_of_mem (S.orderEmbOfFin_mem hn i), hn, Nat.add_sub_cancel]
  have hmono : StrictMono (fun x : ℚ => a * x + b) :=
    fun _ _ h => add_lt_add_left (mul_lt_mul_of_pos_left h ha) _
  have hsource := orderEmbOfFin_unique hcard (f := fun l => a * s (j.succAbove l) + b)
    (fun l => hcopy ▸ mem_image_of_mem _ (hmem j l))
    (hmono.comp (s.strictMono.comp (Fin.strictMono_succAbove j)))
  have htarget := orderEmbOfFin_unique hcard (hmem i)
    (s.strictMono.comp (Fin.strictMono_succAbove i))
  exact congrFun (hsource.trans htarget.symm) k

/-- **Possible types of a symmetric set.** Let $S$ be a finite set of rational numbers with
$n \ge 4$ elements. If $S$ is symmetric of type $(i, j)$, with positions counted from $0$, then
$(i, j)$ is $(0, n - 1)$, $(1, n - 1)$ or $(0, n - 2)$. In the paper's one-based numbering these
are the types $(1, n)$, $(2, n)$ and $(1, n - 1)$.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40, Lemma 2
(`integers-2026-A40-lem-2`). -/
theorem isSymmetricOfType_cases (S : Finset ℚ) (hS : 4 ≤ S.card)
    (i j : Fin S.card) (h : IsSymmetricOfType S i j) :
    (i.val = 0 ∧ j.val = S.card - 1) ∨ (i.val = 1 ∧ j.val = S.card - 1) ∨
      (i.val = 0 ∧ j.val = S.card - 2) := by
  obtain ⟨hij, a, b, ha, hcopy⟩ := h
  have hn : S.card = (S.card - 1) + 1 := by omega
  let i' := i.cast hn
  let j' := j.cast hn
  let s := S.orderEmbOfFin hn
  have hmatch := affine_eq_at_rank hn i' j' ha (b := b) hcopy
  -- The identity cannot carry one deletion to the other: the domain still contains sᵢ.
  have hne : ¬ (a = 1 ∧ b = 0) := by
    rintro ⟨rfl, rfl⟩
    have hi := mem_image_of_mem (fun x : ℚ => 1 * x + 0)
      (mem_erase.mpr ⟨(S.orderEmbOfFin rfl).injective.ne hij.ne, S.orderEmbOfFin_mem rfl i⟩)
    rw [← hcopy] at hi
    simp at hi
  -- Outside the interval of shifted ranks, the affine map fixes each surviving element.
  have fixed (k : Fin (S.card - 1)) (hk : k.val < i.val ∨ j.val ≤ k.val) :
      a * s (j'.succAbove k) + b = s (j'.succAbove k) := by
    refine (hmatch k).trans (congrArg s ?_)
    rcases hk with hk | hk
    · rw [Fin.succAbove_of_castSucc_lt _ _ (show k.val < i.val from hk),
        Fin.succAbove_of_castSucc_lt _ _ (show k.val < j.val from lt_trans hk hij)]
    · have hik : i.val ≤ k.val := Nat.le_trans (Nat.le_of_lt hij) hk
      rw [Fin.succAbove_of_le_castSucc _ _ hik,
        Fin.succAbove_of_le_castSucc _ _ (show j.val ≤ k.val from hk)]
  have unique (k l : Fin (S.card - 1))
      (hk : k.val < i.val ∨ j.val ≤ k.val) (hl : l.val < i.val ∨ j.val ≤ l.val) : k = l := by
    by_contra hkl
    let x := s (j'.succAbove k)
    let y := s (j'.succAbove l)
    have hxy : x ≠ y := (s.injective.comp (Fin.strictMono_succAbove j').injective).ne hkl
    have hprod : (a - 1) * (x - y) = 0 := by
      linear_combination fixed k hk - fixed l hl
    have ha1 := sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right (sub_ne_zero.mpr hxy))
    exact hne ⟨ha1, by simpa [ha1] using fixed k hk⟩
  -- Apply uniqueness to the first two ranks, the last two ranks, and the two ends.
  have hfirst := unique ⟨0, by omega⟩ ⟨1, by omega⟩
  have hlast := unique ⟨S.card - 3, by omega⟩ ⟨S.card - 2, by omega⟩
  have hends := unique ⟨0, by omega⟩ ⟨S.card - 2, by omega⟩
  simp only [Fin.ext_iff] at hfirst hlast hends
  omega

end MetaMathlibExt.FastVanDerWaerdenGame
