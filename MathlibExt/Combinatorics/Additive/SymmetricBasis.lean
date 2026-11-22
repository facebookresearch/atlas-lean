/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Image
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Finset

/-- **Rohrbach's symmetric basis theorem.** Let $A$ be a finite set of natural numbers and $a$ a
natural number with $\{a - x : x \in A\} = A$, where $a - x$ denotes truncated subtraction
($a - x = 0$ when $x > a$). If every natural number $m \le a$ is a sum $x + y$ of two elements
$x, y \in A$, then every natural number $m \le 2a$ is such a sum.

The symmetry condition forces every element of $A$ to be at most $a$, so it says exactly that $A$
is invariant under $x \mapsto a - x$.

This is Rohrbach's theorem on symmetric restricted additive bases.

Source: Jukka Kohonen, "A Meet-in-the-Middle Algorithm for Finding Extremal
Restricted Additive 2-Bases", Journal of Integer Sequences 17 (2014), Article
14.6.8, theorem `theorem:symmrest`, lines 274–288, with notation and basis
definitions at lines 226–248,
<https://cs.uwaterloo.ca/journals/JIS/VOL17/Kohonen2/kohonen5.tex>. -/
theorem exists_add_eq_of_image_sub_eq_self (A : Finset ℕ) (a : ℕ)
    (hsymm : A.image (fun x => a - x) = A)
    (hadmissible : ∀ m : ℕ, m ≤ a → ∃ x ∈ A, ∃ y ∈ A, x + y = m) :
    ∀ m : ℕ, m ≤ 2 * a → ∃ x ∈ A, ∃ y ∈ A, x + y = m := by
  have hmax : ∀ x ∈ A, x ≤ a := by
    intro x hx
    rw [← hsymm] at hx
    obtain ⟨y, _, rfl⟩ := mem_image.mp hx
    exact Nat.sub_le _ _
  intro m hm
  by_cases hma : m ≤ a
  · exact hadmissible m hma
  · obtain ⟨x, hx, y, hy, hxy⟩ := hadmissible (2 * a - m) (by omega)
    have hax : a - x ∈ A := by
      rw [← hsymm]
      exact mem_image.mpr ⟨x, hx, rfl⟩
    have hay : a - y ∈ A := by
      rw [← hsymm]
      exact mem_image.mpr ⟨y, hy, rfl⟩
    refine ⟨a - x, hax, a - y, hay, ?_⟩
    have hxle := hmax x hx
    have hyle := hmax y hy
    omega

end Finset
