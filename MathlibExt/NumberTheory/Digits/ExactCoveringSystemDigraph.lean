/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.List.Chain
public import Mathlib.Order.RelIso.Basic
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Tactic.Ring

/-!
# Exact covering system digraphs

The edge rules are affine maps on the integers. Translating the vertices by `n ↦ n + k`
preserves the slope of each rule and changes its offset from `a` to `a - (d - 1) * k`.
Reflecting the vertices by `n ↦ -(n + k)`
preserves the slope of each rule and changes its offset from `a` to `-a + (d - 1) * k`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Edge relation of an exact covering system digraph.** Let $r \in \mathbb{N}$ and let
$d_1, \dots, d_r$ and $a_1, \dots, a_r$ be integers. The digraph
$G(d_1 n + a_1, \dots, d_r n + a_r)$ has vertex set $\mathbb{Z}$ and an edge $x \to y$ iff
$y = d_i x + a_i$ for some $i \in \{1, \dots, r\}$.

When the pairs $(a_i, d_i)$ form an exact covering system this is the paper's digraph $G_S$;
the definition itself places no condition on the $d_i$ and $a_i$.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Section 1
(definition of `G_S`). -/
def ecsdAdj {r : ℕ} (d a : Fin r → ℤ) (m n : ℤ) : Prop :=
  ∃ i, n = d i * m + a i

/-- **Out-neighbours in a two-rule digraph.** For all integers $d_1, d_2, a_1, a_2, x, y$, the
digraph $G(d_1 n + a_1, d_2 n + a_2)$ has an edge $x \to y$ iff $y = d_1 x + a_1$ or
$y = d_2 x + a_2$.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Section 1
(definition of `G_S`). -/
theorem ecsdAdj_two (d₁ d₂ a₁ a₂ m n : ℤ) :
    ecsdAdj ![d₁, d₂] ![a₁, a₂] m n ↔ n = d₁ * m + a₁ ∨ n = d₂ * m + a₂ := by
  simp [ecsdAdj, Fin.exists_fin_two]

/-- **$k$-descendants in a digraph on the integers.** Let $R$ be a digraph on $\mathbb{Z}$, let
$k \in \mathbb{N}$ and let $m, n \in \mathbb{Z}$. Then $n$ is a $k$-descendant of $m$ in $R$ when
there is a directed walk of exactly $k$ edges from $m$ to $n$, that is, integers
$m = x_0, x_1, \dots, x_k = n$ such that $R$ has an edge $x_{i-1} \to x_i$ for every
$1 \le i \le k$.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Section 1
(definition of `k`-descendant). -/
def IsKDescendant (R : ℤ → ℤ → Prop) : ℕ → ℤ → ℤ → Prop
  | 0, m, n => n = m
  | k + 1, m, n => ∃ x, IsKDescendant R k m x ∧ R x n

/-- **The only $0$-descendant of a vertex is itself.** Let $R$ be a digraph on $\mathbb{Z}$ and let
$m, n \in \mathbb{Z}$. Then $n$ is a $0$-descendant of $m$ in $R$ if and only if $n = m$.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Section 1
(definition of `k`-descendant). -/
theorem isKDescendant_zero (R : ℤ → ℤ → Prop) (m n : ℤ) :
    IsKDescendant R 0 m n ↔ n = m :=
  Iff.rfl

/-- **The $1$-descendants are the out-neighbours.** Let $R$ be a digraph on $\mathbb{Z}$ and let
$m, n \in \mathbb{Z}$. Then $n$ is a $1$-descendant of $m$ in $R$ if and only if $R$ has an edge
$m \to n$.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Section 1
(definition of successor). -/
theorem isKDescendant_one (R : ℤ → ℤ → Prop) (m n : ℤ) :
    IsKDescendant R 1 m n ↔ R m n := by
  simp [IsKDescendant]

/-- **Cycles of a digraph on the integers.** Let $R$ be a digraph on $\mathbb{Z}$, given by its edge
relation. A list $c = (c_1, \dots, c_t)$ of integers is a cycle of $R$ when it is nonempty, its
entries are pairwise distinct, and $R$ has the edges $c_1 \to c_2, \dots, c_{t-1} \to c_t$ and
$c_t \to c_1$ (for $t = 1$ this means a loop $c_1 \to c_1$).

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Section 2
(cycles `C = (c₁, …, c_t)`). -/
def IsDigraphCycle (R : ℤ → ℤ → Prop) (c : List ℤ) : Prop :=
  c ≠ [] ∧ c.Nodup ∧ (c ++ c.take 1).IsChain R

/-- **One-vertex cycles of a digraph on the integers.** Let $R$ be a digraph on $\mathbb{Z}$ and let
$x \in \mathbb{Z}$. The one-element list $(x)$ is a cycle of $R$ if and only if $R$ has a loop
$x \to x$.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Section 2
(cycles of length 1). -/
theorem isDigraphCycle_singleton (R : ℤ → ℤ → Prop) (x : ℤ) :
    IsDigraphCycle R [x] ↔ R x x := by
  simp [IsDigraphCycle]

/-- **Two-vertex cycles of a digraph on the integers.** Let $R$ be a digraph on $\mathbb{Z}$ and let
$x, y \in \mathbb{Z}$. The list $(x, y)$ is a cycle of $R$ if and only if $x \ne y$ and $R$ has both
edges $x \to y$ and $y \to x$.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Section 2
(2-cycles). -/
theorem isDigraphCycle_pair (R : ℤ → ℤ → Prop) (x y : ℤ) :
    IsDigraphCycle R [x, y] ↔ x ≠ y ∧ R x y ∧ R y x := by
  simp [IsDigraphCycle]

/-- **Translation isomorphism of exact covering system digraphs.** Let $r \in \mathbb{N}$, let
$d_1, \dots, d_r$, $a_1, \dots, a_r$ and $k$ be integers, and put $a_i' = a_i - (d_i - 1)k$.
Then the map $x \mapsto x + k$ is a digraph isomorphism from
$G(d_1 n + a_1, \dots, d_r n + a_r)$ onto $G(d_1 n + a_1', \dots, d_r n + a_r')$.

The paper's exact-covering hypothesis on the rules is not needed.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Theorem 1
(`integers-2026-A107-thm-1`). -/
theorem ecsdAdj_shift_relIso {r : ℕ} (d a : Fin r → ℤ) (k : ℤ) :
    ∃ e : ecsdAdj d a ≃r ecsdAdj d (fun i => a i - (d i - 1) * k), ∀ n, e n = n + k := by
  let e := Equiv.addRight k
  refine ⟨⟨e, ?_⟩, fun _ => rfl⟩
  intro m n
  refine exists_congr fun i => ?_
  have h : d i * e m + (a i - (d i - 1) * k) = e (d i * m + a i) := by
    change d i * (m + k) + (a i - (d i - 1) * k) = d i * m + a i + k
    ring
  exact h.symm ▸ e.injective.eq_iff

/-- **Reflection isomorphism of exact covering system digraphs.** Let $r \in \mathbb{N}$, let
$d_1, \dots, d_r$, $a_1, \dots, a_r$ and $k$ be integers, and put $a_i' = -a_i + (d_i - 1)k$.
Then the map $x \mapsto -(x + k)$ is a digraph isomorphism from
$G(d_1 n + a_1, \dots, d_r n + a_r)$ onto $G(d_1 n + a_1', \dots, d_r n + a_r')$.

The paper's exact-covering hypothesis on the rules is not needed.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Theorem 2
(`integers-2026-A107-thm-2`). -/
theorem ecsdAdj_neg_shift_relIso {r : ℕ} (d a : Fin r → ℤ) (k : ℤ) :
    ∃ e : ecsdAdj d a ≃r ecsdAdj d (fun i => -a i + (d i - 1) * k), ∀ n, e n = -(n + k) := by
  let e := (Equiv.addRight k).trans (Equiv.neg ℤ)
  refine ⟨⟨e, ?_⟩, fun _ => rfl⟩
  intro m n
  refine exists_congr fun i => ?_
  have h : d i * e m + (-a i + (d i - 1) * k) = e (d i * m + a i) := by
    change d i * -(m + k) + (-a i + (d i - 1) * k) = -(d i * m + a i + k)
    ring
  exact h.symm ▸ e.injective.eq_iff

end

end MetaMathlibExt
