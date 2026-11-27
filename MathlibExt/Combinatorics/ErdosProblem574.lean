/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Order.Real
import Mathlib.Algebra.Field.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic

/-!
# Erdős Problem 574

Erdős Problem 574 asked whether, for every $k \ge 2$, the ratio
$\mathrm{ex}(n; \{C_{2k-1}, C_{2k}\}) / (n/2)^{1 + 1/k}$ tends to $1$ as
$n \to \infty$. It does not: the one-sided blow-up of the Wenger graph
$W_2(q)$ over a field with $q$ elements, which replaces each line by two
copies with the same neighbours, is $\{C_5, C_6\}$-free and has
$2q^4 = 2(n/3)^{4/3}$ edges on $n = 3q^3$ vertices, against the predicted
$(n/2)^{4/3}$, so at $k = 3$ the ratio is at least $8/7$ infinitely often.
The main result is `conjecture_refuted`.

The graph is Wenger's (R. Wenger, *Extremal graphs with no $C_4$'s, $C_6$'s,
or $C_{10}$'s*, J. Combin. Theory Ser. B 52 (1991), 113–116). Replacing each
vertex on one side of a bipartite graph of girth greater than $2k$ by $k - 1$
copies with the same neighbourhood keeps it $C_{2k}$-free: this is
Construction 4.28 of Z. Füredi and M. Simonovits, *The history of degenerate
(bipartite) extremal graph problems*, arXiv:1306.5167, who attribute it to
F. Lazebnik, V. A. Ustimenko and A. J. Woldar (Discrete Math. 1999). The
blow-up here is its case $k = 3$. Füredi and Simonovits apply the same case
to Benson's girth-8 graph for the lower bound of their Theorem 4.31, due to
Z. Füredi, A. Naor and J. Verstraëte (Adv. Math. 2006). The freeness and the
edge count of the blow-up are proved here directly.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.ErdosProblem574Wanted

/-! Source record `EP-574` (Erdős Problem 574). -/

/-- **Graphs without cycles of lengths $2k-1$ and $2k$.** For a natural number $k$, a simple
graph $G$ is free of the cycle lengths $2k-1$ and $2k$ when it contains no copy of the cycle
graph $C_{2k-1}$ and no copy of the cycle graph $C_{2k}$, where a copy is an injective graph
homomorphism, that is, a subgraph that need not be induced.

Here $C_m$ is the cycle graph on $m$ vertices, which has no edges for $m \le 1$ and is a single
edge for $m = 2$, and $2k-1$ is computed in the natural numbers, so it is $0$ when $k = 0$. -/
def IsFreeOf574Cycles {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  (SimpleGraph.cycleGraph (2 * k - 1)).Free G ∧
    (SimpleGraph.cycleGraph (2 * k)).Free G

/-- **Extremal number for cycles of lengths $2k-1$ and $2k$.** For natural numbers $k$ and
$n$, $\mathrm{ex}(n; \{C_{2k-1}, C_{2k}\})$ is the supremum of the numbers of edges of the simple
graphs on the vertex set $\{0, \dots, n-1\}$ that contain no copy of the cycle graph $C_{2k-1}$
and no copy of the cycle graph $C_{2k}$, where the supremum of the empty set is $0$. Here $2k-1$
is computed in the natural numbers, so it is $0$ when $k = 0$. -/
noncomputable def extremalNumber (k n : ℕ) : ℕ :=
  sSup { e : ℕ | ∃ G : SimpleGraph (Fin n), IsFreeOf574Cycles G k ∧ G.edgeSet.ncard = e }

/-- **Erdős Problem 574.** The statement that for every natural number $k \ge 2$ the ratio
$\mathrm{ex}(n; \{C_{2k-1}, C_{2k}\}) / (n/2)^{1 + 1/k}$ tends to $1$ as $n \to \infty$, that is,
$\mathrm{ex}(n; \{C_{2k-1}, C_{2k}\}) = (1 + o(1)) (n/2)^{1 + 1/k}$. Here
$\mathrm{ex}(n; \{C_{2k-1}, C_{2k}\})$ is the extremal number: the supremum of the numbers of
edges of simple graphs on $n$ vertices that contain no copy of the cycle graph $C_{2k-1}$ and no
copy of the cycle graph $C_{2k}$. -/
noncomputable def conjecture : Prop :=
  ∀ k : ℕ, 2 ≤ k →
    Filter.Tendsto
      (fun n : ℕ => (extremalNumber k n : ℝ) / (((n : ℝ) / 2) ^ (1 + 1 / (k : ℝ))))
      Filter.atTop (nhds 1)

/- The Wenger graph $W_2(q)$ and its one-sided blow-up, over a field $K$:
points and lines are triples over $K$, and the blow-up replaces each line by
two copies. -/
namespace Wenger

variable {K : Type*} [Field K]

/-- Adjacency in the Wenger graph: the point `p` and the line `l` are joined
when `p₂ + l₂ = p₁ * l₁` and `p₃ + l₃ = p₁ * l₁²`. -/
def adj (p l : K × K × K) : Prop :=
  p.2.1 + l.2.1 = p.1 * l.1 ∧ p.2.2 + l.2.2 = p.1 * l.1 ^ 2

/-- A line adjacent to a point is determined by its first coordinate. -/
private theorem lineEqOfAdj {p l l' : K × K × K} (h : adj p l) (h' : adj p l')
    (h1 : l.1 = l'.1) : l = l' := by
  have h2 : l.2.1 = l'.2.1 := by
    have e1 := h.1; have e2 := h'.1; rw [← h1] at e2
    have : l.2.1 = l'.2.1 := by linear_combination e1 - e2
    exact this
  have h3 : l.2.2 = l'.2.2 := by
    have e1 := h.2; have e2 := h'.2; rw [← h1] at e2
    have : l.2.2 = l'.2.2 := by linear_combination e1 - e2
    exact this
  exact Prod.ext h1 (Prod.ext h2 h3)

/-- No two distinct points and two distinct lines form a 4-cycle in the
Wenger graph: the Vandermonde system in the lines' first coordinates forces
the two points to coincide. -/
private theorem noFour {p₀ p₁ l₀ l₁ : K × K × K}
    (hp : p₀ ≠ p₁) (hl : l₀ ≠ l₁)
    (h00 : adj p₀ l₀) (h10 : adj p₁ l₀) (h11 : adj p₁ l₁) (h01 : adj p₀ l₁) :
    False := by
  set d₀ : K := p₀.1 - p₁.1 with hd₀
  set d₁ : K := p₁.1 - p₀.1 with hd₁
  set b₀ : K := l₀.1 with hb₀
  set b₁ : K := l₁.1 with hb₁
  have hS0 : d₀ + d₁ = 0 := by rw [hd₀, hd₁]; ring
  have hS1 : d₀ * b₀ + d₁ * b₁ = 0 := by
    have e00 := h00.1; have e10 := h10.1; have e11 := h11.1; have e01 := h01.1
    have g0 : p₀.2.1 - p₁.2.1 = d₀ * b₀ := by
      simp only [hd₀, hb₀]; linear_combination e00 - e10
    have g1 : p₁.2.1 - p₀.2.1 = d₁ * b₁ := by
      simp only [hd₁, hb₁]; linear_combination e11 - e01
    linear_combination -g0 - g1
  have hbne : b₀ ≠ b₁ := by
    intro hbb
    apply hl
    exact lineEqOfAdj h10 h11 hbb
  have hd0 : d₀ = 0 := by
    have hprod : d₀ * (b₀ - b₁) = 0 := by linear_combination hS1 - b₁ * hS0
    rcases mul_eq_zero.mp hprod with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) hbne
  apply hp
  have h1 : p₀.1 = p₁.1 := by
    have h1' := hd0; rw [hd₀] at h1'; exact sub_eq_zero.mp h1'
  have h2 : p₀.2.1 = p₁.2.1 := by
    have e00 := h00.1; have e10 := h10.1
    have g0 : p₀.2.1 - p₁.2.1 = d₀ * b₀ := by
      simp only [hd₀, hb₀]; linear_combination e00 - e10
    rw [hd0, zero_mul, sub_eq_zero] at g0; exact g0
  have h3 : p₀.2.2 = p₁.2.2 := by
    have e00 := h00.2; have e10 := h10.2
    have g0 : p₀.2.2 - p₁.2.2 = d₀ * b₀ ^ 2 := by
      simp only [hd₀, hb₀]; linear_combination e00 - e10
    rw [hd0, zero_mul, sub_eq_zero] at g0; exact g0
  exact Prod.ext h1 (Prod.ext h2 h3)

/-- No three distinct points and three distinct lines form a 6-cycle in the
Wenger graph: the Vandermonde system in the lines' first coordinates forces
two of the points to coincide. The lines' first coordinates are distinct
because any two lines of the cycle share a point. -/
private theorem noSix {p₀ p₁ p₂ l₀ l₁ l₂ : K × K × K}
    (hp01 : p₀ ≠ p₁)
    (hl01 : l₀ ≠ l₁) (hl12 : l₁ ≠ l₂) (hl20 : l₂ ≠ l₀)
    (h00 : adj p₀ l₀) (h10 : adj p₁ l₀) (h11 : adj p₁ l₁)
    (h21 : adj p₂ l₁) (h22 : adj p₂ l₂) (h02 : adj p₀ l₂) :
    False := by
  set d₀ : K := p₀.1 - p₁.1 with hd₀
  set d₁ : K := p₁.1 - p₂.1 with hd₁
  set d₂ : K := p₂.1 - p₀.1 with hd₂
  set b₀ : K := l₀.1 with hb₀
  set b₁ : K := l₁.1 with hb₁
  set b₂ : K := l₂.1 with hb₂
  have hS0 : d₀ + d₁ + d₂ = 0 := by rw [hd₀, hd₁, hd₂]; ring
  have hS1 : d₀ * b₀ + d₁ * b₁ + d₂ * b₂ = 0 := by
    have g0 : p₀.2.1 - p₁.2.1 = d₀ * b₀ := by
      simp only [hd₀, hb₀]; linear_combination h00.1 - h10.1
    have g1 : p₁.2.1 - p₂.2.1 = d₁ * b₁ := by
      simp only [hd₁, hb₁]; linear_combination h11.1 - h21.1
    have g2 : p₂.2.1 - p₀.2.1 = d₂ * b₂ := by
      simp only [hd₂, hb₂]; linear_combination h22.1 - h02.1
    linear_combination -g0 - g1 - g2
  have hS2 : d₀ * b₀ ^ 2 + d₁ * b₁ ^ 2 + d₂ * b₂ ^ 2 = 0 := by
    have g0 : p₀.2.2 - p₁.2.2 = d₀ * b₀ ^ 2 := by
      simp only [hd₀, hb₀]; linear_combination h00.2 - h10.2
    have g1 : p₁.2.2 - p₂.2.2 = d₁ * b₁ ^ 2 := by
      simp only [hd₁, hb₁]; linear_combination h11.2 - h21.2
    have g2 : p₂.2.2 - p₀.2.2 = d₂ * b₂ ^ 2 := by
      simp only [hd₂, hb₂]; linear_combination h22.2 - h02.2
    linear_combination -g0 - g1 - g2
  have hb01 : b₀ ≠ b₁ := by
    intro hbb
    apply hl01
    exact lineEqOfAdj h10 h11 hbb
  have hb12 : b₁ ≠ b₂ := by
    intro hbb
    apply hl12
    exact lineEqOfAdj h21 h22 hbb
  have hb20 : b₂ ≠ b₀ := by
    intro hbb
    apply hl20
    exact lineEqOfAdj h02 h00 hbb
  have hd0 : d₀ = 0 := by
    have hprod : d₀ * (b₀ - b₁) * (b₀ - b₂) = 0 := by
      linear_combination hS2 - (b₁ + b₂) * hS1 + b₁ * b₂ * hS0
    rcases mul_eq_zero.mp hprod with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact h'
      · exact absurd (sub_eq_zero.mp h') hb01
    · exact absurd (sub_eq_zero.mp h) (Ne.symm hb20)
  apply hp01
  have h1 : p₀.1 = p₁.1 := by
    have h1' := hd0; rw [hd₀] at h1'; exact sub_eq_zero.mp h1'
  have h2 : p₀.2.1 = p₁.2.1 := by
    have g0 : p₀.2.1 - p₁.2.1 = d₀ * b₀ := by
      simp only [hd₀, hb₀]; linear_combination h00.1 - h10.1
    rw [hd0, zero_mul, sub_eq_zero] at g0; exact g0
  have h3 : p₀.2.2 = p₁.2.2 := by
    have g0 : p₀.2.2 - p₁.2.2 = d₀ * b₀ ^ 2 := by
      simp only [hd₀, hb₀]; linear_combination h00.2 - h10.2
    rw [hd0, zero_mul, sub_eq_zero] at g0; exact g0
  exact Prod.ext h1 (Prod.ext h2 h3)

/-- The one-sided blow-up of the Wenger graph: every line is replaced by two
copies, each adjacent to the same points as the original line. -/
def blowGraph : SimpleGraph ((K × K × K) ⊕ ((K × K × K) × Fin 2)) where
  Adj x y :=
    match x, y with
    | .inl p, .inr (l, _) => adj p l
    | .inr (l, _), .inl p => adj p l
    | _, _ => False
  symm := ⟨fun x y h => by
    rcases x with p | ⟨l, t⟩ <;> rcases y with p' | ⟨l', t'⟩ <;> exact h⟩
  loopless := ⟨fun x h => by
    rcases x with p | ⟨l, t⟩ <;> exact h⟩

private theorem notAdjInlInl {p p' : K × K × K} :
    ¬ (blowGraph (K := K)).Adj (.inl p) (.inl p') := by simp [blowGraph]

private theorem notAdjInrInr {a b : (K × K × K) × Fin 2} :
    ¬ (blowGraph (K := K)).Adj (.inr a) (.inr b) := by simp [blowGraph]

private theorem adjOfInl {p : K × K × K}
    {x : (K × K × K) ⊕ ((K × K × K) × Fin 2)}
    (h : (blowGraph (K := K)).Adj (.inl p) x) :
    ∃ l t, x = .inr (l, t) ∧ adj p l := by
  rcases x with p' | ⟨l, t⟩
  · exact absurd h notAdjInlInl
  · exact ⟨l, t, rfl, h⟩

private theorem adjOfInr {l : K × K × K} {t : Fin 2}
    {x : (K × K × K) ⊕ ((K × K × K) × Fin 2)}
    (h : (blowGraph (K := K)).Adj (.inr (l, t)) x) :
    ∃ p, x = .inl p ∧ adj p l := by
  rcases x with p | ⟨l', t'⟩
  · exact ⟨p, rfl, h⟩
  · exact absurd h notAdjInrInr

/-- Cycle data in the blow-up cannot exist: either the three underlying lines
are distinct, giving a 6-cycle in the Wenger graph, or two coincide, giving a
4-cycle (or three copies of one line, impossible with only two copies). -/
private theorem blowNoSixData {p₀ p₁ p₂ l₀ l₁ l₂ : K × K × K} {t₀ t₁ t₂ : Fin 2}
    (hp01 : p₀ ≠ p₁) (hp12 : p₁ ≠ p₂) (hp20 : p₂ ≠ p₀)
    (hb01 : (l₀, t₀) ≠ (l₁, t₁)) (hb12 : (l₁, t₁) ≠ (l₂, t₂))
    (hb20 : (l₂, t₂) ≠ (l₀, t₀))
    (h00 : adj p₀ l₀) (h10 : adj p₁ l₀) (h11 : adj p₁ l₁)
    (h21 : adj p₂ l₁) (h22 : adj p₂ l₂) (h02 : adj p₀ l₂) :
    False := by
  by_cases h01 : l₀ = l₁
  · by_cases h20 : l₂ = l₀
    · have ht01 : t₀ ≠ t₁ := by
        intro heq; apply hb01; rw [h01, heq]
      have ht12 : t₁ ≠ t₂ := by
        intro heq; apply hb12; rw [← h01, ← h20, heq]
      have ht20 : t₂ ≠ t₀ := by
        intro heq; apply hb20; rw [h20, heq]
      have e01 : t₀.val ≠ t₁.val := fun h => ht01 (Fin.ext h)
      have e12 : t₁.val ≠ t₂.val := fun h => ht12 (Fin.ext h)
      have e20 : t₂.val ≠ t₀.val := fun h => ht20 (Fin.ext h)
      have l0 := t₀.isLt; have l1 := t₁.isLt; have l2 := t₂.isLt
      omega
    · exact noFour hp20 (fun h => h20 h.symm)
        (by rw [h01]; exact h21) h00 h02 h22
  · by_cases h12 : l₁ = l₂
    · by_cases h20 : l₂ = l₀
      · have ht01 : t₀ ≠ t₁ := by
          intro heq; apply hb01; rw [h20.symm, h12, heq]
        have ht12 : t₁ ≠ t₂ := by
          intro heq; apply hb12; rw [h12, heq]
        have ht20 : t₂ ≠ t₀ := by
          intro heq; apply hb20; rw [h20, heq]
        have e01 : t₀.val ≠ t₁.val := fun h => ht01 (Fin.ext h)
        have e12 : t₁.val ≠ t₂.val := fun h => ht12 (Fin.ext h)
        have e20 : t₂.val ≠ t₀.val := fun h => ht20 (Fin.ext h)
        have l0 := t₀.isLt; have l1 := t₁.isLt; have l2 := t₂.isLt
        omega
      · exact noFour hp01 (fun h => h20 (h12.symm.trans h))
          (by rw [h12]; exact h02) h11 h10 h00
    · by_cases h20 : l₂ = l₀
      · exact noFour hp12 (fun h => h12 h.symm)
          (by rw [h20]; exact h10) h22 h21 h11
      · exact noSix hp01 (fun h => h01 h) (fun h => h12 h) (fun h => h20 h)
          h00 h10 h11 h21 h22 h02

private theorem sumCases {A B : Type*} (x : A ⊕ B) :
    (∃ a, x = .inl a) ∨ (∃ b, x = .inr b) := by
  cases x with
  | inl a => exact Or.inl ⟨a, rfl⟩
  | inr b => exact Or.inr ⟨b, rfl⟩

/-- **The blow-up of the Wenger graph has no 6-cycle.** For every field $K$, the blow-up of the
Wenger graph over $K$ contains no copy of the cycle graph $C_6$. Such a copy alternates between
three points and three line copies. Since each line has only two copies, the three underlying
lines are either distinct, giving a 6-cycle in the Wenger graph, or exactly two of them
coincide, giving a 4-cycle; the Wenger graph has neither. -/
theorem blowGraph_free_six : (SimpleGraph.cycleGraph 6).Free (blowGraph (K := K)) := by
  rintro ⟨f⟩
  have hadj : ∀ i j : Fin 6, (SimpleGraph.cycleGraph 6).Adj i j →
      (blowGraph (K := K)).Adj (f i) (f j) := fun i j h => f.toHom.map_adj h
  have h01 := hadj 0 1 (by decide)
  have h12 := hadj 1 2 (by decide)
  have h23 := hadj 2 3 (by decide)
  have h34 := hadj 3 4 (by decide)
  have h45 := hadj 4 5 (by decide)
  have h50 := hadj 5 0 (by decide)
  rcases sumCases (f 0) with ⟨p₀, hp0⟩ | ⟨⟨l₂, t₂⟩, hl2⟩
  · rw [hp0] at h01 h50
    obtain ⟨l₀, t₀, h1, h00⟩ := adjOfInl h01
    rw [h1] at h12
    obtain ⟨p₁, h2, h10⟩ := adjOfInr h12
    rw [h2] at h23
    obtain ⟨l₁, t₁, h3, h11⟩ := adjOfInl h23
    rw [h3] at h34
    obtain ⟨p₂, h4, h21⟩ := adjOfInr h34
    rw [h4] at h45
    obtain ⟨l₂', t₂', h5, h22⟩ := adjOfInl h45
    rw [h5] at h50
    have h02 : adj p₀ l₂' := h50
    have hp01 : p₀ ≠ p₁ := by
      intro heq
      have hEq : f 0 = f 2 := by rw [hp0, h2, heq]
      exact (by decide : (0 : Fin 6) ≠ 2) (f.injective hEq)
    have hp12 : p₁ ≠ p₂ := by
      intro heq
      have hEq : f 2 = f 4 := by rw [h2, h4, heq]
      exact (by decide : (2 : Fin 6) ≠ 4) (f.injective hEq)
    have hp20 : p₂ ≠ p₀ := by
      intro heq
      have hEq : f 4 = f 0 := by rw [h4, hp0, heq]
      exact (by decide : (4 : Fin 6) ≠ 0) (f.injective hEq)
    have hb01 : (l₀, t₀) ≠ (l₁, t₁) := by
      intro heq
      have hEq : f 1 = f 3 := by rw [h1, h3, heq]
      exact (by decide : (1 : Fin 6) ≠ 3) (f.injective hEq)
    have hb12 : (l₁, t₁) ≠ (l₂', t₂') := by
      intro heq
      have hEq : f 3 = f 5 := by rw [h3, h5, heq]
      exact (by decide : (3 : Fin 6) ≠ 5) (f.injective hEq)
    have hb20 : (l₂', t₂') ≠ (l₀, t₀) := by
      intro heq
      have hEq : f 5 = f 1 := by rw [h5, h1, heq]
      exact (by decide : (5 : Fin 6) ≠ 1) (f.injective hEq)
    exact blowNoSixData hp01 hp12 hp20 hb01 hb12 hb20 h00 h10 h11 h21 h22 h02
  · rw [hl2] at h01 h50
    obtain ⟨p₀, h1, h02⟩ := adjOfInr h01
    rw [h1] at h12
    obtain ⟨l₀, t₀, h2, h00⟩ := adjOfInl h12
    rw [h2] at h23
    obtain ⟨p₁, h3, h10⟩ := adjOfInr h23
    rw [h3] at h34
    obtain ⟨l₁, t₁, h4, h11⟩ := adjOfInl h34
    rw [h4] at h45
    obtain ⟨p₂, h5, h21⟩ := adjOfInr h45
    rw [h5] at h50
    have h22 : adj p₂ l₂ := h50
    have hp01 : p₀ ≠ p₁ := by
      intro heq
      have hEq : f 1 = f 3 := by rw [h1, h3, heq]
      exact (by decide : (1 : Fin 6) ≠ 3) (f.injective hEq)
    have hp12 : p₁ ≠ p₂ := by
      intro heq
      have hEq : f 3 = f 5 := by rw [h3, h5, heq]
      exact (by decide : (3 : Fin 6) ≠ 5) (f.injective hEq)
    have hp20 : p₂ ≠ p₀ := by
      intro heq
      have hEq : f 5 = f 1 := by rw [h5, h1, heq]
      exact (by decide : (5 : Fin 6) ≠ 1) (f.injective hEq)
    have hb01 : (l₀, t₀) ≠ (l₁, t₁) := by
      intro heq
      have hEq : f 2 = f 4 := by rw [h2, h4, heq]
      exact (by decide : (2 : Fin 6) ≠ 4) (f.injective hEq)
    have hb12 : (l₁, t₁) ≠ (l₂, t₂) := by
      intro heq
      have hEq : f 4 = f 0 := by rw [h4, hl2, heq]
      exact (by decide : (4 : Fin 6) ≠ 0) (f.injective hEq)
    have hb20 : (l₂, t₂) ≠ (l₀, t₀) := by
      intro heq
      have hEq : f 0 = f 2 := by rw [hl2, h2, heq]
      exact (by decide : (0 : Fin 6) ≠ 2) (f.injective hEq)
    exact blowNoSixData hp01 hp12 hp20 hb01 hb12 hb20 h00 h10 h11 h21 h22 h02

/-- **The blow-up of the Wenger graph has no 5-cycle.** For every field $K$, the blow-up of the
Wenger graph over $K$ contains no copy of the cycle graph $C_5$, since it is bipartite: every
edge joins a point to a copy of a line. -/
theorem blowGraph_free_five : (SimpleGraph.cycleGraph 5).Free (blowGraph (K := K)) := by
  rintro ⟨f⟩
  have hadj : ∀ i j : Fin 5, (SimpleGraph.cycleGraph 5).Adj i j →
      (blowGraph (K := K)).Adj (f i) (f j) := fun i j h => f.toHom.map_adj h
  have h01 := hadj 0 1 (by decide)
  have h12 := hadj 1 2 (by decide)
  have h23 := hadj 2 3 (by decide)
  have h34 := hadj 3 4 (by decide)
  have h40 := hadj 4 0 (by decide)
  rcases sumCases (f 0) with ⟨p₀, hp0⟩ | ⟨⟨l₀, t₀⟩, hl0⟩
  · rw [hp0] at h01 h40
    obtain ⟨l₁, t₁, h1, -⟩ := adjOfInl h01
    rw [h1] at h12
    obtain ⟨p₂, h2, -⟩ := adjOfInr h12
    rw [h2] at h23
    obtain ⟨l₃, t₃, h3, -⟩ := adjOfInl h23
    rw [h3] at h34
    obtain ⟨p₄, h4, -⟩ := adjOfInr h34
    rw [h4] at h40
    exact absurd h40 notAdjInlInl
  · rw [hl0] at h01 h40
    obtain ⟨p₁, h1, -⟩ := adjOfInr h01
    rw [h1] at h12
    obtain ⟨l₂, t₂, h2, -⟩ := adjOfInl h12
    rw [h2] at h23
    obtain ⟨p₃, h3, -⟩ := adjOfInr h23
    rw [h3] at h34
    obtain ⟨l₄, t₄, h4, -⟩ := adjOfInl h34
    rw [h4] at h40
    exact absurd h40 notAdjInrInr

/-- The line through the point `p` with first coordinate `b`: the unique line
adjacent to `p` with that first coordinate. -/
def wline (p : K × K × K) (b : K) : K × K × K := (b, p.1 * b - p.2.1, p.1 * b ^ 2 - p.2.2)

private theorem wline_adj (p : K × K × K) (b : K) : adj p (wline p b) := by
  constructor <;> simp [wline]

private theorem wline_eq {p l : K × K × K} (h : adj p l) : l = wline p l.1 := by
  have h2 : l.2.1 = p.1 * l.1 - p.2.1 := by linear_combination h.1
  have h3 : l.2.2 = p.1 * l.1 ^ 2 - p.2.2 := by linear_combination h.2
  exact Prod.ext rfl (Prod.ext h2 h3)

/-- The point through the line `l` with first coordinate `a`: the unique point
adjacent to `l` with that first coordinate. -/
def wpoint (l : K × K × K) (a : K) : K × K × K := (a, a * l.1 - l.2.1, a * l.1 ^ 2 - l.2.2)

private theorem wpoint_adj (l : K × K × K) (a : K) : adj (wpoint l a) l := by
  constructor <;> simp [wpoint]

private theorem wpoint_eq {p l : K × K × K} (h : adj p l) : p = wpoint l p.1 := by
  have h2 : p.2.1 = p.1 * l.1 - l.2.1 := by linear_combination h.1
  have h3 : p.2.2 = p.1 * l.1 ^ 2 - l.2.2 := by linear_combination h.2
  exact Prod.ext rfl (Prod.ext h2 h3)

instance blowGraphDecidableAdj [DecidableEq K] :
    DecidableRel (blowGraph (K := K)).Adj := fun x y => by
  rcases x with p | ⟨l, t⟩ <;> rcases y with p' | ⟨l', t'⟩ <;>
    simp only [blowGraph] <;> first | infer_instance | (unfold adj; infer_instance)

variable [Fintype K] [DecidableEq K]

private theorem neighborFinsetInl (p : K × K × K) :
    (blowGraph (K := K)).neighborFinset (.inl p) =
      (Finset.univ : Finset (K × Fin 2)).image
        (fun bt => (Sum.inr (wline p bt.1, bt.2) :
          (K × K × K) ⊕ ((K × K × K) × Fin 2))) := by
  ext y
  rw [SimpleGraph.mem_neighborFinset, Finset.mem_image]
  rcases y with p' | ⟨l, t⟩
  · constructor
    · intro h; exact absurd h notAdjInlInl
    · intro h
      obtain ⟨⟨b, t⟩, -, hbt⟩ := h
      simp at hbt
  · constructor
    · intro h
      exact ⟨(l.1, t), Finset.mem_univ _,
        congrArg (fun l' => (Sum.inr (l', t) : (K × K × K) ⊕ ((K × K × K) × Fin 2)))
          (wline_eq h).symm⟩
    · intro h
      obtain ⟨⟨b, t'⟩, -, hbt⟩ := h
      have hlt := Sum.inr.inj hbt
      rw [Prod.mk.injEq] at hlt
      rw [← hlt.1]
      exact wline_adj p b

private theorem degreeInl (p : K × K × K) :
    (blowGraph (K := K)).degree (.inl p) = 2 * Fintype.card K := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, neighborFinsetInl]
  have hinj : Function.Injective (fun bt : K × Fin 2 => (Sum.inr (wline p bt.1, bt.2) :
      (K × K × K) ⊕ ((K × K × K) × Fin 2))) := by
    rintro ⟨b, t⟩ ⟨b', t'⟩ h
    simp only [Sum.inr.injEq, Prod.mk.injEq] at h
    have hb : b = b' := by
      have := congrArg Prod.fst h.1
      simpa [wline] using this
    simp only [Prod.mk.injEq]
    exact ⟨hb, h.2⟩
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin]
  ring

private theorem neighborFinsetInr (l : K × K × K) (t : Fin 2) :
    (blowGraph (K := K)).neighborFinset (.inr (l, t)) =
      (Finset.univ : Finset K).image
        (fun a => (Sum.inl (wpoint l a) : (K × K × K) ⊕ ((K × K × K) × Fin 2))) := by
  ext y
  rw [SimpleGraph.mem_neighborFinset, Finset.mem_image]
  rcases y with p | ⟨l', t'⟩
  · constructor
    · intro h
      exact ⟨p.1, Finset.mem_univ _,
        congrArg (fun p' => (Sum.inl p' : (K × K × K) ⊕ ((K × K × K) × Fin 2)))
          (wpoint_eq h).symm⟩
    · intro h
      obtain ⟨a, -, ha⟩ := h
      rw [← ha]
      exact wpoint_adj l a
  · constructor
    · intro h; exact absurd h notAdjInrInr
    · intro h
      obtain ⟨a, -, ha⟩ := h
      simp at ha

private theorem degreeInr (l : K × K × K) (t : Fin 2) :
    (blowGraph (K := K)).degree (.inr (l, t)) = Fintype.card K := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, neighborFinsetInr]
  have hinj : Function.Injective (fun a : K => (Sum.inl (wpoint l a) :
      (K × K × K) ⊕ ((K × K × K) × Fin 2))) := by
    intro a a' h
    have := congrArg Prod.fst (Sum.inl.inj h)
    simpa [wpoint] using this
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]

private theorem blowGraph_edgeFinset_card :
    (blowGraph (K := K)).edgeFinset.card = 2 * (Fintype.card K) ^ 4 := by
  have hP : Fintype.card (K × K × K) = (Fintype.card K) ^ 3 := by
    simp only [Fintype.card_prod]; ring
  have hsum : ∑ v, (blowGraph (K := K)).degree v = 4 * (Fintype.card K) ^ 4 := by
    calc ∑ v, (blowGraph (K := K)).degree v
        = (∑ p : K × K × K, (blowGraph (K := K)).degree (.inl p))
            + ∑ bt : (K × K × K) × Fin 2, (blowGraph (K := K)).degree (.inr bt) :=
          Fintype.sum_sum_type _
      _ = (∑ _p : K × K × K, 2 * Fintype.card K)
            + ∑ _bt : (K × K × K) × Fin 2, Fintype.card K := by
          congr 1
          · exact Finset.sum_congr rfl fun p _ => degreeInl p
          · exact Finset.sum_congr rfl fun bt _ => by
              obtain ⟨l, t⟩ := bt; exact degreeInr l t
      _ = 4 * (Fintype.card K) ^ 4 := by
          rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Finset.card_univ,
            smul_eq_mul, smul_eq_mul, hP, Fintype.card_prod, Fintype.card_fin, hP]
          ring
  have h := SimpleGraph.sum_degrees_eq_twice_card_edges (blowGraph (K := K))
  rw [hsum] at h
  omega

omit [DecidableEq K] in
/-- **Edge count of the blow-up.** Over a field with $q$ elements, the blow-up
has $2q^4$ edges. -/
theorem blowGraph_edgeSet_ncard :
    (blowGraph (K := K)).edgeSet.ncard = 2 * (Fintype.card K) ^ 4 := by
  classical
  rw [← blowGraph_edgeFinset_card]
  exact Set.ncard_eq_toFinset_card' _

end Wenger

open Filter

/-- A free graph on a vertex type with `n` elements witnesses the lower bound
for the extremal number, after transporting it to `Fin n`. -/
private theorem le_extremalNumber_of_card {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hfree : IsFreeOf574Cycles G 3) {n : ℕ} (hc : Fintype.card V = n) :
    G.edgeSet.ncard ≤ extremalNumber 3 n := by
  classical
  let G' := G.overFin hc
  have hfree' : IsFreeOf574Cycles G' 3 := by
    have e : G' ≃g G := (G.overFinIso hc).symm
    exact ⟨(SimpleGraph.free_congr_right e).mpr hfree.1,
      (SimpleGraph.free_congr_right e).mpr hfree.2⟩
  have hcard : G.edgeSet.ncard = G'.edgeSet.ncard := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact Nat.card_congr (G.overFinIso hc).mapEdgeSet
  rw [hcard]
  apply le_csSup
  · refine ⟨Fintype.card (Sym2 (Fin n)), ?_⟩
    rintro e ⟨H, -, rfl⟩
    have hle : H.edgeSet.ncard ≤ Nat.card (Sym2 (Fin n)) := by
      have h := Set.ncard_le_ncard (s := H.edgeSet) (t := Set.univ) (Set.subset_univ _)
        (Set.finite_univ (α := Sym2 (Fin n)))
      rwa [Set.ncard_univ] at h
    rw [Nat.card_eq_fintype_card] at hle
    exact hle
  · exact ⟨G', hfree', rfl⟩

/-- **Lower bound for the extremal number at $k = 3$.** For every natural number $m$,
$\mathrm{ex}(3 \cdot (2^{m+1})^3; \{C_5, C_6\}) \ge 2 \cdot (2^{m+1})^4$, where
$\mathrm{ex}(n; \{C_5, C_6\})$ is the supremum of the numbers of edges of simple graphs on $n$
vertices that contain no copy of the cycle graph $C_5$ and no copy of the cycle graph $C_6$.
The witness is the blow-up of the Wenger graph over the field with $2^{m+1}$ elements, which
has $2 \cdot (2^{m+1})^4$ edges on $3 \cdot (2^{m+1})^3$ vertices and is $\{C_5, C_6\}$-free. -/
theorem extremalNumber_three_lower (m : ℕ) :
    2 * (2 ^ (m + 1)) ^ 4 ≤ extremalNumber 3 (3 * (2 ^ (m + 1)) ^ 3) := by
  classical
  let K := GaloisField 2 (m + 1)
  let : Fintype K := Fintype.ofFinite K
  let : DecidableEq K := Classical.decEq K
  have hcardK : Fintype.card K = 2 ^ (m + 1) := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 (m + 1) (Nat.succ_ne_zero m)]
  have hcardV : Fintype.card ((K × K × K) ⊕ ((K × K × K) × Fin 2))
      = 3 * (2 ^ (m + 1)) ^ 3 := by
    have hP : Fintype.card (K × K × K) = (2 ^ (m + 1)) ^ 3 := by
      rw [← hcardK]; simp only [Fintype.card_prod]; ring
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, hP]
    ring
  have hle := le_extremalNumber_of_card (Wenger.blowGraph (K := K))
    ⟨Wenger.blowGraph_free_five, Wenger.blowGraph_free_six⟩ hcardV
  rw [Wenger.blowGraph_edgeSet_ncard, hcardK] at hle
  exact hle

/-- At $k = 3$ the ratio is at least $8/7$ at the orders $3 \cdot (2^{m+1})^3$:
the denominator is $(3/2)^{4/3} q^4$ with $q = 2^{m+1}$, and
$(3/2)^{4/3} \le 7/4$ since $(3/2)^4 < (7/4)^3$. -/
private theorem ratio_lower_bound (m : ℕ) :
    (8 : ℝ) / 7 ≤ (extremalNumber 3 (3 * (2 ^ (m + 1)) ^ 3) : ℝ) /
      ((((3 * (2 ^ (m + 1)) ^ 3 : ℕ) : ℝ) / 2) ^ (1 + 1 / ((3 : ℕ) : ℝ))) := by
  set Q : ℝ := (2 : ℝ) ^ (m + 1) with hQ
  have hQpos : 0 < Q := by positivity
  have hexp : (1 : ℝ) + 1 / ((3 : ℕ) : ℝ) = 4 / 3 := by norm_num
  have hD : ((((3 * (2 ^ (m + 1)) ^ 3 : ℕ) : ℝ) / 2) ^ (1 + 1 / ((3 : ℕ) : ℝ)))
      = ((3 : ℝ) / 2) ^ ((4 : ℝ) / 3) * Q ^ 4 := by
    rw [hexp]
    have hcast : (((3 * (2 ^ (m + 1)) ^ 3 : ℕ) : ℝ) / 2) = (3 / 2) * Q ^ 3 := by
      push_cast
      rw [← hQ]
      ring
    rw [hcast, Real.mul_rpow (by norm_num) (by positivity)]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hQpos),
      show ((3 : ℕ) : ℝ) * (4 / 3) = (4 : ℝ) by norm_num]
    exact Real.rpow_natCast Q 4
  have h34 : ((3 : ℝ) / 2) ^ ((4 : ℝ) / 3) ≤ 7 / 4 := by
    by_contra h
    push Not at h
    have hpos : (0 : ℝ) ≤ (3 : ℝ) / 2 := by norm_num
    have hcube : (((3 : ℝ) / 2) ^ ((4 : ℝ) / 3)) ^ 3 = (81 : ℝ) / 16 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hpos,
        show ((4 : ℝ) / 3) * ((3 : ℕ) : ℝ) = 4 by norm_num]
      rw [show ((3 : ℝ) / 2) ^ (4 : ℝ) = ((3 : ℝ) / 2) ^ (4 : ℕ) from
        Real.rpow_natCast _ _]
      norm_num
    have hlt : (7 / 4 : ℝ) ^ 3 < (((3 : ℝ) / 2) ^ ((4 : ℝ) / 3)) ^ 3 :=
      pow_lt_pow_left₀ h (by norm_num) (by norm_num)
    rw [hcube] at hlt
    norm_num at hlt
  have hDpos : 0 < ((((3 * (2 ^ (m + 1)) ^ 3 : ℕ) : ℝ) / 2) ^
      (1 + 1 / ((3 : ℕ) : ℝ))) := by
    rw [hD]; positivity
  have hDle : ((((3 * (2 ^ (m + 1)) ^ 3 : ℕ) : ℝ) / 2) ^ (1 + 1 / ((3 : ℕ) : ℝ)))
      ≤ (7 / 4) * Q ^ 4 := by
    rw [hD]; gcongr
  have hlower : (2 : ℝ) * Q ^ 4 ≤ (extremalNumber 3 (3 * (2 ^ (m + 1)) ^ 3) : ℝ) := by
    have h := extremalNumber_three_lower m
    have hcast : ((2 * (2 ^ (m + 1)) ^ 4 : ℕ) : ℝ) = 2 * Q ^ 4 := by
      push_cast
      rw [hQ]
    rw [← hcast]
    exact_mod_cast h
  rw [le_div_iff₀ hDpos]
  calc (8 / 7 : ℝ) * ((((3 * (2 ^ (m + 1)) ^ 3 : ℕ) : ℝ) / 2) ^
        (1 + 1 / ((3 : ℕ) : ℝ)))
      ≤ (8 / 7) * ((7 / 4) * Q ^ 4) := by gcongr
    _ = 2 * Q ^ 4 := by ring
    _ ≤ (extremalNumber 3 (3 * (2 ^ (m + 1)) ^ 3) : ℝ) := hlower

/--
**Erdős Problem 574 is false.** It is not the case that for every natural number $k \ge 2$ the
ratio $\mathrm{ex}(n; \{C_{2k-1}, C_{2k}\}) / (n/2)^{1 + 1/k}$ tends to $1$ as $n \to \infty$.
Here $\mathrm{ex}(n; \{C_{2k-1}, C_{2k}\})$ is the extremal number: the supremum of the numbers
of edges of simple graphs on $n$ vertices that contain no copy of the cycle graph $C_{2k-1}$ and
no copy of the cycle graph $C_{2k}$.

The case $k = 3$ already fails. Replacing each vertex on one side of a bipartite graph of girth
greater than $2k$ by $k - 1$ copies with the same neighbourhood keeps it bipartite and
$C_{2k}$-free (Füredi–Simonovits, Construction 4.28, which they attribute to Lazebnik,
Ustimenko and Woldar). For $k = 3$, the Wenger graph over a field with $q$ elements is
bipartite with no 4-cycle and no 6-cycle, and doubling its lines gives a $\{C_5, C_6\}$-free
graph with $2q^4 = 2(n/3)^{4/3}$ edges on $n = 3q^3$ vertices, against the predicted
$(n/2)^{4/3}$: at these $n$ the ratio is at least $2 (2/3)^{4/3} > 8/7$, and the fields with
$2^{m+1}$ elements give infinitely many of them. Applied to Benson's girth-8 graph instead, the
same construction gives the lower bound of Füredi–Simonovits, Theorem 4.31, due to Füredi,
Naor and Verstraëte (Adv. Math. 2006).

Lazebnik, Ustimenko and Woldar (Discrete Math. 1999), per Füredi–Simonovits
(arXiv:1306.5167, Construction 4.28), blow up one side of Benson's girth-12 bipartite graph to
get bipartite $C_{10}$-free graphs (hence also $C_9$-free) with
$4(n/5)^{6/5} > 0.5798\, n^{6/5}$ edges for infinitely many $n$, refuting the case $k = 5$.

Source: Zoltán Füredi and Miklós Simonovits, The history of degenerate
(bipartite) extremal graph problems, in Erdős Centennial, Bolyai Soc. Math. Stud. 25 (2013),
arXiv:1306.5167, https://arxiv.org/abs/1306.5167. Moved from
`OpenConjectures/Combinatorics/ErdosProblem574`.
-/
public theorem conjecture_refuted : ¬ conjecture := by
  intro hconj
  have hk := hconj 3 (by norm_num)
  have hpow : ∀ m : ℕ, m + 1 ≤ 2 ^ (m + 1) := by
    intro m
    induction m with
    | zero => norm_num
    | succ k ih =>
      have h2 : (2 : ℕ) ^ (k + 2) = 2 * 2 ^ (k + 1) := by rw [pow_succ]; ring
      omega
  have hsub : Filter.Tendsto (fun m : ℕ => 3 * (2 ^ (m + 1)) ^ 3) Filter.atTop
      Filter.atTop := by
    apply tendsto_atTop_mono (f := fun m : ℕ => m)
      (g := fun m : ℕ => 3 * (2 ^ (m + 1)) ^ 3)
    · intro m
      have h1 := hpow m
      have h2 : (2 : ℕ) ^ (m + 1) ≤ (2 ^ (m + 1)) ^ 3 :=
        Nat.le_self_pow (by norm_num) _
      omega
    · exact tendsto_id
  have hcomp := hk.comp hsub
  have hev : ∀ᶠ m in Filter.atTop, (extremalNumber 3 (3 * (2 ^ (m + 1)) ^ 3) : ℝ) /
      ((((3 * (2 ^ (m + 1)) ^ 3 : ℕ) : ℝ) / 2) ^ (1 + 1 / ((3 : ℕ) : ℝ))) < 15 / 14 := by
    have h1 := hcomp.eventually (Iio_mem_nhds (show (1 : ℝ) < 15 / 14 by norm_num))
    simpa only [Function.comp_apply, Set.mem_Iio, Nat.cast_ofNat] using h1
  obtain ⟨m, hm⟩ := hev.exists
  have hge := ratio_lower_bound m
  linarith

end MathlibExt.Combinatorics.ErdosProblem574Wanted
