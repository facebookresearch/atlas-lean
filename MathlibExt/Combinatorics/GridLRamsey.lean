/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Combinatorics.HalesJewett
import Mathlib.Order.Interval.Finset.Nat

/-!
# Monochromatic L-shapes in grid colorings

Every finite coloring of a sufficiently large square grid contains a monochromatic L.
We also prove the one-color bounds and a criterion for a monochromatic L from forced blue points
on a diagonal.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Grid Ramsey property for Ls.** Let $k$ and $n$ be natural numbers and write
$[n] = \{1, \dots, n\}$. An L in the grid $[n] \times [n]$ is a triple of points $(x, y)$,
$(x + d, y)$, $(x + d, y + d)$ with $x$, $y$, $d$ positive integers, $x + d \le n$ and
$y + d \le n$. The pair $(k, n)$ has the grid Ramsey property for Ls when every coloring of
$\mathbb{N} \times \mathbb{N}$ with $k$ colors gives the three points of some L in
$[n] \times [n]$ the same color, that is, contains a monochromatic L. Only the colors on
$[n] \times [n]$ matter.

The grid Ramsey number $R_k(L)$ is the least $n$ with this property. The property is monotone
in $n$, so $R_k(L) \le N$ says exactly that $(k, N)$ has it.

Source: Isaac Mammel, William Smith, and Carl Yerger, *Ramsey Theory on the Integer
Grid: The "L" Problem*, INTEGERS 25 (2025), Article A21, Theorem 1 and the
definition of `R_k(L)` following it. -/
public def GridLRamseyProperty (k n : ℕ) : Prop :=
  ∀ c : ℕ × ℕ → Fin k, ∃ x y d : ℕ, 0 < x ∧ 0 < y ∧ 0 < d ∧ x + d ≤ n ∧ y + d ≤ n ∧
    c (x, y) = c (x + d, y) ∧ c (x + d, y) = c (x + d, y + d)

/-- **Grid Ramsey theorem for Ls.** Write $[n] = \{1, \dots, n\}$. For every positive integer
$k$ there is a positive integer $n$ such that every coloring of the grid $[n] \times [n]$ with
$k$ colors contains a monochromatic L: positive integers $x$, $y$, $d$ with $x + d \le n$ and
$y + d \le n$ such that the points $(x, y)$, $(x + d, y)$ and $(x + d, y + d)$ all have the
same color.

Source: Isaac Mammel, William Smith, and Carl Yerger, *Ramsey Theory on the Integer
Grid: The "L" Problem*, INTEGERS 25 (2025), Article A21, Theorem 1 (quoted there
from earlier work). -/
public theorem exists_gridLRamseyProperty (k : ℕ) (hk : 0 < k) :
    ∃ n : ℕ, 0 < n ∧ GridLRamseyProperty k n := by
  classical
  obtain ⟨ι, _, hι⟩ := Combinatorics.Line.exists_mono_in_high_dimension (Fin 3) (Fin k)
  refine ⟨k + Fintype.card ι, by omega, ?_⟩
  intro c
  -- Count the letters 1 and 2 for the horizontal coordinate, and just 2 for the vertical.
  let coord (p : Fin 3 → Bool) (w : ι → Fin 3) :=
    k + (Finset.univ.filter fun i => p (w i)).card
  let hor (a : Fin 3) := a != 0
  let ver (a : Fin 3) := a == 2
  obtain ⟨l, color, hcolor⟩ := hι fun w => c (coord hor w, coord ver w)
  let wild := Finset.univ.filter fun i => l.idxFun i = none
  have hd : 0 < wild.card := by
    obtain ⟨i, hi⟩ := l.proper
    exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  let fixed (p : Fin 3 → Bool) := Finset.univ.filter fun i => (l.idxFun i).any p
  -- Each wildcard contributes one extra count exactly when the chosen letter satisfies p.
  have eval (p : Fin 3 → Bool) (a : Fin 3) :
      coord p (l a) = k + (fixed p).card + wild.card * (p a).toNat := by
    simp only [coord, fixed, wild, Finset.card_filter, Finset.sum_mul, Nat.add_assoc,
      ← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    cases hi : l.idxFun i <;> cases hp : p a <;> simp [hi, hp]
  simp only [eval] at hcolor
  have bound (p : Fin 3 → Bool) (hp : p 2 = true) :
      k + (fixed p).card + wild.card ≤ k + Fintype.card ι := by
    have h : coord p (l 2) ≤ k + Fintype.card ι := Nat.add_le_add_left (Finset.card_le_univ _) k
    simpa only [eval, hp, Bool.toNat_true, Nat.mul_one] using h
  refine ⟨k + (fixed hor).card, k + (fixed ver).card, wild.card, by omega, by omega, hd,
    bound hor rfl, bound ver rfl, ?_, ?_⟩
  · simpa [hor, ver] using (hcolor 0).trans (hcolor 1).symm
  · simpa [hor, ver] using (hcolor 1).trans (hcolor 2).symm

/-- **Monotonicity of the grid Ramsey property for Ls.** Let $k$, $m$, $n$ be natural numbers
with $m \le n$. For a natural number $N$ write $[N] = \{1, \dots, N\}$; given a coloring, a
monochromatic L in $[N] \times [N]$ is a triple of points $(x, y)$, $(x + d, y)$, $(x + d, y + d)$
of the same color with $x$, $y$, $d$ positive integers, $x + d \le N$ and $y + d \le N$. If every
coloring of $\mathbb{N} \times \mathbb{N}$ with $k$ colors has a monochromatic L in
$[m] \times [m]$, then every such coloring has a monochromatic L in $[n] \times [n]$, because a
larger grid contains every L of a smaller one.

Source: Isaac Mammel, William Smith, and Carl Yerger, *Ramsey Theory on the Integer
Grid: The "L" Problem*, INTEGERS 25 (2025), Article A21 (definition of `R_k(L)`). -/
public theorem GridLRamseyProperty.mono {k m n : ℕ} (h : GridLRamseyProperty k m)
    (hmn : m ≤ n) : GridLRamseyProperty k n := by
  intro c
  obtain ⟨x, y, d, hx, hy, hd, hxd, hyd, h1, h2⟩ := h c
  exact ⟨x, y, d, hx, hy, hd, by omega, by omega, h1, h2⟩

/-- **One color does not force an L on the $1 \times 1$ grid.** The grid L-Ramsey property
fails for $k = 1$ color and grid size $n = 1$: not every coloring of the grid
$\{1\} \times \{1\}$ with one color contains a monochromatic L, that is, three points
$(x, y), (x + d, y), (x + d, y + d)$ of the grid of the same color, with $x, y, d$ positive
integers. In fact this grid contains no L at all, since that needs $x + d \le 1$ with
$x, d \ge 1$.

Source: Isaac Mammel, William Smith, and Carl Yerger, *Ramsey Theory on the Integer
Grid: The "L" Problem*, INTEGERS 25 (2025), Article A21 (definition of an L). -/
public theorem not_gridLRamseyProperty_one_one : ¬ GridLRamseyProperty 1 1 := by
  intro h
  obtain ⟨x, y, d, hx, _, hd, hxd, _⟩ := h fun _ => 0
  omega

/-- **With one color the 2 × 2 grid contains an L.** Write $[n] = \{1, \dots, n\}$. An L in the
grid $[n] \times [n]$ is a triple of points $(x, y)$, $(x + d, y)$, $(x + d, y + d)$ with $x$, $y$,
$d$ positive integers, $x + d \le n$ and $y + d \le n$. Every coloring of
$\mathbb{N} \times \mathbb{N}$ with a single color gives the three points of some L in
$[2] \times [2]$ the same color, namely the L $(1, 1)$, $(2, 1)$, $(2, 2)$.

Since $[1] \times [1]$ contains no L at all, the grid Ramsey number for one color, the least $n$
such that every coloring with one color has a monochromatic L in $[n] \times [n]$, is
$R_1(L) = 2$.

Source: Isaac Mammel, William Smith, and Carl Yerger, *Ramsey Theory on the Integer
Grid: The "L" Problem*, INTEGERS 25 (2025), Article A21 (definition of `R_k(L)`). -/
public theorem gridLRamseyProperty_one_two : GridLRamseyProperty 1 2 := by
  intro c
  exact ⟨1, 1, 1, by omega, by omega, by omega, by omega, by omega,
    Subsingleton.elim _ _, Subsingleton.elim _ _⟩

/-- **Forced blue points on a diagonal give a monochromatic L.** Let $n \ge 3$, write
$[n] = \{1, \dots, n\}$, let $c$ be a coloring of $\mathbb{N} \times \mathbb{N}$ with $3$ colors
and let red and blue be two distinct colors. Let $s \ge 1$ and let $X$ be a finite set of
natural numbers such that every $x \in X$ satisfies $x \ge 1$ and $x + s \le n$, the point
$(x + s, x)$ is blue, and the points $(x, x)$ and $(x + s, x + s)$ are red (so red at
$(x + s, x)$ would complete the red L $(x, x)$, $(x + s, x)$, $(x + s, x + s)$). If
$\binom{|X|}{2} > n - 2$, then $c$ has a monochromatic L in $[n] \times [n]$: positive integers
$x$, $y$, $d$ with $x + d \le n$ and $y + d \le n$ such that the points $(x, y)$, $(x + d, y)$
and $(x + d, y + d)$ all have the same color.

The paper states the threshold as $|X| \ge \lceil \sqrt{2n - 15/4} + 1/2 \rceil$, meant as the
least $b$ with $\binom{b}{2} > n - 2$. This closed form is one too small when
$\sqrt{2n - 15/4} + 1/2$ is an integer, and the lemma then fails: for $n = 3$, color the
diagonal red, $(2, 1)$, $(3, 2)$, $(2, 3)$ blue, $(3, 1)$ green and $(1, 2)$, $(1, 3)$ red; with
$s = 1$ there are two forced blue points and no monochromatic L.

Source: Isaac Mammel, William Smith, and Carl Yerger, *Ramsey Theory on the Integer
Grid: The "L" Problem*, INTEGERS 25 (2025), Article A21, Lemma 1. -/
public theorem exists_mono_L_of_forced_blue_diagonal (n : ℕ) (hn : 3 ≤ n)
    (c : ℕ × ℕ → Fin 3) (red blue : Fin 3) (hrb : red ≠ blue) (s : ℕ) (hs : 0 < s)
    (X : Finset ℕ)
    (hX : ∀ x ∈ X, 0 < x ∧ x + s ≤ n ∧ c (x + s, x) = blue ∧ c (x, x) = red ∧
      c (x + s, x + s) = red)
    (hcard : n - 2 < X.card.choose 2) :
    ∃ x y d : ℕ, 0 < x ∧ 0 < y ∧ 0 < d ∧ x + d ≤ n ∧ y + d ≤ n ∧
      c (x, y) = c (x + d, y) ∧ c (x + d, y) = c (x + d, y + d) := by
  by_contra h
  -- Two points on a diagonal and the corner between them form an L.
  have noL {x y u v : ℕ} (hx : 0 < x) (hy : 0 < y) (hxu : x < u)
      (hu : u ≤ n) (hv : v ≤ n) (hdiag : u + y = x + v)
      (h₁ : c (x, y) = c (u, y)) (h₂ : c (u, y) = c (u, v)) : False := by
    apply h
    refine ⟨x, y, u - x, hx, hy, by omega, ?_⟩
    rw [show x + (u - x) = u by omega, show y + (u - x) = v by omega]
    exact ⟨hu, hv, h₁, h₂⟩
  have third : ∀ r b : Fin 3, r ≠ b →
      ∃ g : Fin 3, ∀ t : Fin 3, t ≠ r → t ≠ b → t = g := by decide
  obtain ⟨green, hgreen⟩ := third red blue hrb
  -- A red corner completes a red L on the main diagonal, a blue one a blue L
  -- on the original shifted diagonal. Every such corner must therefore be green.
  have corner {a b : ℕ} (ha : a ∈ X) (hb : b ∈ X) (hab : a < b) :
      c (b + s, a) = green := by
    obtain ⟨ha₀, _, haBlue, haRed, _⟩ := hX a ha
    obtain ⟨_, hbn, hbBlue, _, hbRed⟩ := hX b hb
    apply hgreen
    · intro hr
      exact noL ha₀ ha₀ (by omega) hbn hbn (by omega) (haRed.trans hr.symm) (hr.trans hbRed.symm)
    · intro hb'
      exact noL (by omega) ha₀ (by omega) hbn (by omega) (by omega)
        (haBlue.trans hb'.symm) (hb'.trans hbBlue.symm)
  -- For two corners on one subdiagonal, the connecting corner is also forced green.
  have clash {a b u v : ℕ} (ha : a ∈ X) (hb : b ∈ X) (hu : u ∈ X) (hv : v ∈ X)
      (hab : a < b) (huv : u < v) (hau : a < u) (hgap : b + s - a = v + s - u) : False := by
    have hcross := corner ha hv (hau.trans huv)
    have hun := (hX u hu).2.1
    exact noL (by omega) (hX a ha).1 (by omega) (hX v hv).2.1 (by omega) (by omega)
      ((corner ha hb hab).trans hcross.symm) (hcross.trans (corner hu hv huv).symm)
  -- The subdiagonal index of a corner lies between 2 and n - 1.
  let pairs := (X ×ˢ X).filter fun p => p.1 < p.2
  let index := fun p : ℕ × ℕ => p.2 + s - p.1
  have hcount : (Finset.Icc 2 (n - 1)).card < pairs.card := by
    rw [Nat.card_Icc, Nat.sub_add_cancel (by omega : 1 ≤ n), Finset.card_product_filter_lt]
    exact hcard
  have hindex : Set.MapsTo index (↑pairs) (↑(Finset.Icc 2 (n - 1))) := by
    rintro ⟨a, b⟩ hp
    obtain ⟨hmem, hab⟩ := Finset.mem_filter.mp hp
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hmem
    have ha₀ := (hX a ha).1
    have hbn := (hX b hb).2.1
    apply Finset.mem_Icc.mpr
    change 2 ≤ b + s - a ∧ b + s - a ≤ n - 1
    constructor <;> omega
  obtain ⟨⟨a, b⟩, hp, ⟨u, v⟩, hq, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcount hindex
  simp only [pairs, Finset.mem_filter, Finset.mem_product] at hp hq
  obtain ⟨⟨ha, hb⟩, hab⟩ := hp
  obtain ⟨⟨hu, hv⟩, huv⟩ := hq
  change b + s - a = v + s - u at heq
  rcases lt_trichotomy a u with hau | rfl | hua
  · exact clash ha hb hu hv hab huv hau heq
  · exact hne (Prod.ext rfl (by omega))
  · exact clash hu hv ha hb huv hab hua heq.symm

end

end MetaMathlibExt
