/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Interval.Finset.Nat

import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import MathlibExt.Combinatorics.DensityHalesJewett

/-!
# Squares in dense subsets of the grid (Erdős Problem 658)

Every sufficiently large grid subset of fixed positive density contains an axis-parallel square.

Source: T. F. Bloom, Erdős Problems, Problem #658, https://www.erdosproblems.com/658 (status PROVED
(LEAN)). UnsolvedMath record UM-30006972 (`EP-658`), dataset ulamai/UnsolvedMath v1.8.0.

The square is axis-parallel, `(a, b), (a + d, b), (a, b + d), (a + d, b + d)` with `d ≥ 1` (Graham's
version); this implies the version allowing squares in any orientation, so it is the stronger
statement. It follows from the density Hales-Jewett theorem, which MathlibExt proves
(`density_hales_jewett`). Compared with the formal-conjectures
statement `ErdosProblems/658.lean` (equivalent; no code imported).
-/

@[expose] public section

namespace MathlibExt.Combinatorics.DenseGridSquareErdosProblem658Wanted

open scoped BigOperators

/-- **Erdős Problem 658 (axis-parallel squares in dense subsets of the grid).** The statement that
for every real number $\delta > 0$ there is a natural number $N_0$ such that for every $N \ge N_0$,
every set $A \subseteq \{1, \dots, N\}^2$ of pairs of natural numbers with $|A| \ge \delta N^2$
contains the four vertices $(a, b)$, $(a + d, b)$, $(a, b + d)$ and $(a + d, b + d)$ of an
axis-parallel square, for some natural numbers $a$, $b$ and $d \ge 1$. -/
def denseGridContainsSquare : Prop :=
  ∀ δ > (0 : ℝ), ∀ᶠ N : ℕ in Filter.atTop, ∀ A : Finset (ℕ × ℕ),
    A ⊆ Finset.Icc 1 N ×ˢ Finset.Icc 1 N → δ * (N : ℝ) ^ 2 ≤ A.card →
      ∃ a b d : ℕ, 0 < d ∧ (a, b) ∈ A ∧ (a + d, b) ∈ A ∧ (a, b + d) ∈ A ∧ (a + d, b + d) ∈ A

private theorem sum_line {n : ℕ} (l : Combinatorics.Line (Fin 4) (Fin n))
    (f : Fin 4 → ℕ) (a : Fin 4) :
    (∑ i, f (l a i)) =
      (∑ i, (l.idxFun i).elim 0 f) +
        (Finset.univ.filter fun i => l.idxFun i = none).card * f a := by
  classical
  rw [← Finset.sum_const_nat (f := fun _ => f a) fun _ _ => rfl,
    Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases hi : l.idxFun i <;> simp [hi]

/--
**Erdős Problem 658 is true.** For every real number $\delta > 0$ there is a natural number $N_0$
such that for every $N \ge N_0$, every set $A \subseteq \{1, \dots, N\}^2$ of pairs of natural
numbers with $|A| \ge \delta N^2$ contains the four vertices $(a, b)$, $(a + d, b)$, $(a, b + d)$
and $(a + d, b + d)$ of an axis-parallel square, for some natural numbers $a$, $b$ and $d \ge 1$.

This follows from the density Hales–Jewett theorem of Furstenberg and Katznelson; Solymosi gave a
quantitative proof.

Source: T. F. Bloom, Erdős Problems, Problem #658,
https://www.erdosproblems.com/658 (status PROVED (LEAN)); resolution: H. Furstenberg and Y.
Katznelson, A density version of the Hales-Jewett theorem, J. Anal. Math. (1991), 64-119,
erdosproblems.com/658: the qualitative statement follows from the density Hales-Jewett theorem; a
quantitative proof was given by Solymosi (Combin. Probab. Comput. 2004),
https://www.erdosproblems.com/658.
-/
public theorem denseGridContainsSquare_holds : denseGridContainsSquare := by
  classical
  intro δ hδ
  obtain ⟨n, hn⟩ := Combinatorics.DensityHalesJewettWanted.density_hales_jewett
    4 (by decide) (δ / 4) (by positivity)
  filter_upwards [Filter.eventually_ge_atTop (max n 1)] with N hN
  intro A hA hcard
  have hnN : n ≤ N := (le_max_left _ _).trans hN
  have hN₁ : 1 ≤ N := (le_max_right _ _).trans hN
  -- Encode the four letters as the points of the unit square.
  let x : Fin 4 → ℕ := fun a => a.val % 2
  let y : Fin 4 → ℕ := fun a => a.val / 2
  let grid := Finset.Icc 1 (N + n) ×ˢ Finset.Icc 1 (N + n)
  let pairs := A ×ˢ (Finset.univ : Finset (Fin n → Fin 4))
  let translate : (ℕ × ℕ) × (Fin n → Fin 4) → ℕ × ℕ :=
    fun z => (z.1.1 + ∑ i, x (z.2 i), z.1.2 + ∑ i, y (z.2 i))
  have hmaps : ∀ z ∈ pairs, translate z ∈ grid := by
    rintro ⟨p, w⟩ hz
    have hp : p ∈ A := (Finset.mem_product.mp hz).1
    obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp (hA hp)
    obtain ⟨hp₁l, hp₁u⟩ := Finset.mem_Icc.mp hp₁
    obtain ⟨hp₂l, hp₂u⟩ := Finset.mem_Icc.mp hp₂
    have hsum (f : Fin 4 → ℕ) (hf : ∀ a, f a ≤ 1) : (∑ i, f (w i)) ≤ n := calc
      _ ≤ ∑ _i : Fin n, 1 := Finset.sum_le_sum fun i _ => hf (w i)
      _ = n := by simp
    have hx := hsum x (fun a => by dsimp [x]; omega)
    have hy := hsum y (fun a => by have := a.isLt; dsimp [y]; omega)
    dsimp only [grid, translate]
    simp only [Finset.mem_product, Finset.mem_Icc]
    omega
  have hgrid : grid.Nonempty := ⟨(1, 1), by simp [grid]; omega⟩
  have hbound : grid.card • (δ / 4 * (4 : ℝ) ^ n) ≤ (pairs.card : ℝ) := by
    have hsize : (N + n : ℝ) ^ 2 ≤ (2 * N) ^ 2 := by
      have hnN' : (n : ℝ) ≤ N := by exact_mod_cast hnN
      gcongr
      simpa only [two_mul] using add_le_add_right hnN' (N : ℝ)
    simp only [grid, pairs, nsmul_eq_mul, Finset.card_product, Nat.card_Icc,
      Nat.add_sub_cancel, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat]
    calc
      _ = ((N + n : ℝ) ^ 2 * (δ / 4)) * 4 ^ n := by ring
      _ ≤ ((2 * N : ℝ) ^ 2 * (δ / 4)) * 4 ^ n := by gcongr
      _ = (δ * (N : ℝ) ^ 2) * 4 ^ n := by ring
      _ ≤ (A.card : ℝ) * 4 ^ n := by gcongr
  -- Averaging over translated sums gives a dense set of words for one sum.
  obtain ⟨t, _, ht⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to hmaps hgrid hbound
  let fiber := pairs.filter fun z => translate z = t
  have hinj : Set.InjOn Prod.snd (↑fiber : Set ((ℕ × ℕ) × (Fin n → Fin 4))) := by
    rintro ⟨p, w⟩ hz ⟨p', w'⟩ hz' (rfl : w = w')
    have heq := (Finset.mem_filter.mp hz).2.trans (Finset.mem_filter.mp hz').2.symm
    simp only [translate, Prod.mk.injEq] at heq
    exact congrArg (fun q => (q, w))
      (Prod.ext (Nat.add_right_cancel heq.1) (Nat.add_right_cancel heq.2))
  obtain ⟨l, hl⟩ := hn (fiber.image Prod.snd) (by
    rw [Finset.card_image_of_injOn hinj]
    exact ht)
  have hexists (k : Fin 4) : ∃ p ∈ A, translate (p, l k) = t := by
    obtain ⟨⟨p, w⟩, hz, (rfl : w = l k)⟩ := Finset.mem_image.mp (hl k)
    obtain ⟨hz, heq⟩ := Finset.mem_filter.mp hz
    exact ⟨p, (Finset.mem_product.mp hz).1, heq⟩
  choose p hp htranslate using hexists
  -- Every free coordinate contributes one copy of the letter to the sum.
  let d := (Finset.univ.filter fun i => l.idxFun i = none).card
  have hd : 0 < d := by
    obtain ⟨i, hi⟩ := l.proper
    exact Finset.card_pos.mpr ⟨i, by simp [hi]⟩
  have hcoords (k : Fin 4) :
      (p k).1 + ((∑ i, (l.idxFun i).elim 0 x) + d * x k) = t.1 ∧
      (p k).2 + ((∑ i, (l.idxFun i).elim 0 y) + d * y k) = t.2 := by
    have hx : (p k).1 + (∑ i, x (l k i)) = t.1 := congrArg Prod.fst (htranslate k)
    have hy : (p k).2 + (∑ i, y (l k i)) = t.2 := congrArg Prod.snd (htranslate k)
    rw [sum_line] at hx hy
    exact ⟨hx, hy⟩
  -- With the translated sum fixed, the letter 3 gives the lower-left vertex.
  have h0 := hcoords 0
  have h1 := hcoords 1
  have h2 := hcoords 2
  have h3 := hcoords 3
  norm_num [x, y] at h0 h1 h2 h3
  have h10 : ((p 3).1 + d, (p 3).2) = p 2 := Prod.ext (by omega) (by omega)
  have h01 : ((p 3).1, (p 3).2 + d) = p 1 := Prod.ext (by omega) (by omega)
  have h11 : ((p 3).1 + d, (p 3).2 + d) = p 0 := Prod.ext (by omega) (by omega)
  exact ⟨(p 3).1, (p 3).2, d, hd, hp 3, h10 ▸ hp 2, h01 ▸ hp 1, h11 ▸ hp 0⟩

end MathlibExt.Combinatorics.DenseGridSquareErdosProblem658Wanted
