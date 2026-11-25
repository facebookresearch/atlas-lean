/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Finset.Card
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Prod
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Topology.MetricSpace.Defs

import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Erdős Problem 755

Clemen, Dumitrescu and Liu, *The number of regular simplices in higher dimensions*,
[arXiv:2507.19841](https://arxiv.org/abs/2507.19841), Theorem 2, give the
asymptotic maximum number of equilateral triangles in dimension six.

For the upper bound we work with the graph of pairs having many equilateral
completions. The triangle bound for `K₄`-free graphs and fixed-size sampling
force many copies of `K₄` if the triangle density is too large. Averaging over
the six completions and extracting a Cartesian box produces four mutually
orthogonal two-dimensional direction spaces, impossible in dimension six.
For the lower bound we use a balanced subset of three orthogonal circles.

The counting definitions retain the namespace and interface of the statement
originally imported from Formal Conjectures, `ErdosProblems/755.lean`.
-/

open Filter
open scoped Asymptotics EuclideanGeometry Finset

namespace MathlibExt.Geometry.ErdosProblem755Wanted

@[expose] public section

/-- **Equilateral triangle with given side.** For a real number $s$, a finite set $T$ of
points in the Euclidean space $\mathbb{R}^d$ is an equilateral triangle of side $s$ when $T$ has
exactly three elements and any two distinct points of $T$ are at distance $s$. -/
def IsEquilateralTriangle {d : ℕ} (side : ℝ)
    (T : Finset (EuclideanSpace ℝ (Fin d))) : Prop :=
  T.card = 3 ∧ ∀ p ∈ T, ∀ q ∈ T, p ≠ q → dist p q = side

/-- **Unit equilateral triangle.** A finite set $T$ of points in the Euclidean space $\mathbb{R}^d$
is a unit equilateral triangle when it is an equilateral triangle of side $1$: $T$ has exactly
three elements and any two distinct points of $T$ are at distance $1$. -/
def IsUnitEquilateralTriangle {d : ℕ}
    (T : Finset (EuclideanSpace ℝ (Fin d))) : Prop :=
  IsEquilateralTriangle 1 T

/-- **Equilateral triangle of any size.** A finite set $T$ of points in the Euclidean space
$\mathbb{R}^d$ is an equilateral triangle of any size when there is a real number $s > 0$ such
that $T$ is an equilateral triangle of side $s$: $T$ has exactly three elements and any two
distinct points of $T$ are at distance $s$. -/
def IsAnySizeEquilateralTriangle {d : ℕ}
    (T : Finset (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∃ side : ℝ, 0 < side ∧ IsEquilateralTriangle side T

/-- **Number of unit equilateral triangles in a point set.** For a finite set $P$ of points in
the Euclidean space $\mathbb{R}^d$, this is the number of three-element subsets of $P$ that are
unit equilateral triangles, that is, whose three points are pairwise at distance $1$. -/
noncomputable def unitEquilateralTriangleCount (d : ℕ)
    (P : Finset (EuclideanSpace ℝ (Fin d))) : ℕ :=
  open scoped Classical in
  ((P.powersetCard 3).filter fun T => IsUnitEquilateralTriangle T).card

/-- **Number of equilateral triangles in a point set.** For a finite set $P$ of points in the
Euclidean space $\mathbb{R}^d$, this is the number of three-element subsets of $P$ that are
equilateral triangles of some positive side length $s$, that is, whose three points are pairwise
at distance $s$. -/
noncomputable def anySizeEquilateralTriangleCount (d : ℕ)
    (P : Finset (EuclideanSpace ℝ (Fin d))) : ℕ :=
  open scoped Classical in
  ((P.powersetCard 3).filter fun T => IsAnySizeEquilateralTriangle T).card

/-- **Maximum number of unit equilateral triangles.** For natural numbers $d$ and $n$, $T_1(d, n)$
is the supremum in $\mathbb{N}$, over all sets $P$ of exactly $n$ points in the Euclidean space
$\mathbb{R}^d$, of the number of unit equilateral triangles spanned by $P$ (the three-element
subsets of $P$ whose points are pairwise at distance $1$). When such sets exist this is the
largest such number; when none exist (only for $d = 0$ and $n \ge 2$) it is $0$. -/
noncomputable def TUnit (d n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ P : Finset (EuclideanSpace ℝ (Fin d)),
    P.card = n ∧ unitEquilateralTriangleCount d P = m}

/-- **Maximum number of equilateral triangles.** For natural numbers $d$ and $n$, $T(d, n)$ is the
supremum in $\mathbb{N}$, over all sets $P$ of exactly $n$ points in the Euclidean space
$\mathbb{R}^d$, of the number of equilateral triangles of positive side length spanned by $P$
(the three-element subsets of $P$ whose points are pairwise at the same positive distance). When
such sets exist this is the largest such number; when none exist (only for $d = 0$ and $n \ge 2$)
it is $0$. -/
noncomputable def TAnySize (d n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ P : Finset (EuclideanSpace ℝ (Fin d)),
    P.card = n ∧ anySizeEquilateralTriangleCount d P = m}

/-- **Statement of Erdős Problem 755.** Let $T_1(n)$ be the largest number of unit equilateral
triangles spanned by a set of $n$ points in $\mathbb{R}^6$, and let $T(n)$ be the largest number
of equilateral triangles of positive side length spanned by a set of $n$ points in
$\mathbb{R}^6$; a triangle spanned by a set is a three-element subset of it whose points are
pairwise at the same distance. The statement asserts both of the following: there is a function
$o : \mathbb{N} \to \mathbb{R}$ with $o(n) \to 0$ as $n \to \infty$ such that
$T_1(n) \le (1/27 + o(n))\, n^3$ for all sufficiently large $n$; and $T(n)$ is asymptotically
equivalent to $n^3/27$ as $n \to \infty$. -/
def conjecture : Prop :=
  (∃ o : ℕ → ℝ,
    o =o[atTop] (fun _ : ℕ => (1 : ℝ)) ∧
      ∀ᶠ n in atTop,
        (TUnit 6 n : ℝ) ≤ ((1 / 27 : ℝ) + o n) * (n : ℝ) ^ 3) ∧
  ((fun n : ℕ => (TAnySize 6 n : ℝ)) ~[atTop]
    (fun n : ℕ => (1 / 27 : ℝ) * (n : ℝ) ^ 3))

end

open Finset


open Classical in
private noncomputable def count {α : Type*} [Fintype α] (p : α → Prop) : ℕ :=
  (univ.filter p).card

private theorem count_eq_card {α : Type*} [Fintype α] (p : α → Prop) :
    count p = Nat.card {a // p a} := by
  classical
  rw [Nat.card_eq_fintype_card]
  exact (Fintype.card_subtype p).symm

private theorem count_congr {α β : Type*} [Fintype α] [Fintype β]
    {p : α → Prop} {q : β → Prop} (e : α ≃ β) (h : ∀ a, p a ↔ q (e a)) :
    count p = count q := by
  rw [count_eq_card, count_eq_card]
  exact Nat.card_congr (e.subtypeEquiv h)

private theorem count_mono {α : Type*} [Fintype α] {p q : α → Prop}
    (h : ∀ a, p a → q a) : count p ≤ count q := by
  classical
  exact card_le_card (fun a ha ↦ mem_filter.mpr ⟨mem_univ _, h a (mem_filter.mp ha).2⟩)

private theorem count_le {α : Type*} [Fintype α] (p : α → Prop) :
    count p ≤ Fintype.card α := by
  classical
  exact card_filter_le _ _

private theorem count_fiber {α β : Type*} [Fintype α] [Fintype β]
    (p : α → β → Prop) : count (fun ab : α × β ↦ p ab.1 ab.2) = ∑ a, count (p a) := by
  classical
  rw [count, card_eq_sum_card_fiberwise (f := Prod.fst) (t := univ) (by simp)]
  apply sum_congr rfl
  intro a _
  rw [filter_filter, ← Fintype.card_subtype, count_eq_card, ← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  exact
    { toFun := fun x ↦ ⟨x.val.2, by simpa only [← x.property.2] using x.property.1⟩
      invFun := fun b ↦ ⟨(a, b.val), b.property, rfl⟩
      left_inv := fun ⟨⟨_, _⟩, _, h⟩ ↦ by subst a; rfl
      right_inv := fun _ ↦ rfl }

private theorem count_fiber_swap {α β : Type*} [Fintype α] [Fintype β]
    (p : α → β → Prop) : count (fun ab : α × β ↦ p ab.1 ab.2) =
      ∑ b, count (fun a ↦ p a b) :=
  (count_congr (Equiv.prodComm α β) (p := fun ab ↦ p ab.1 ab.2)
    (q := fun ba ↦ p ba.2 ba.1) (fun _ ↦ Iff.rfl)).trans (count_fiber fun b a ↦ p a b)

private theorem exists_large_fiber {α β : Type*} [Fintype α] [Fintype β] [Nonempty α]
    (p : α → β → Prop) (c : ℝ)
    (h : c * Fintype.card α ≤ (count (fun ab : α × β ↦ p ab.1 ab.2) : ℝ)) :
    ∃ a, c ≤ (count (p a) : ℝ) := by
  by_contra! hf
  rw [count_fiber, Nat.cast_sum] at h
  have hg := sum_lt_sum_of_nonempty (s := (univ : Finset α)) (f := fun a ↦ (count (p a) : ℝ))
    (g := fun _ ↦ c) univ_nonempty fun a _ ↦ hf a
  simp only [sum_const, card_univ, nsmul_eq_mul] at hg
  exact (not_lt_of_ge h) (by simpa only [mul_comm c] using hg)

private abbrev Slices (α : Type*) [Fintype α] (r : ℕ) :=
  {s : Finset α // s ∈ (univ : Finset α).powersetCard r}

private theorem slices_card {α : Type*} [Fintype α] (r : ℕ) :
    Fintype.card (Slices α r) = (Fintype.card α).choose r := by
  simp [Slices]

private theorem count_slices {α : Type*} [Fintype α] (r : ℕ) (p : α → Prop) :
    count (fun s : Slices α r ↦ ∀ a ∈ s.val, p a) = (count p).choose r := by
  classical
  rw [count_eq_card]
  change _ = (univ.filter p).card.choose r
  rw [← card_powersetCard, ← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  apply Nat.card_congr (β := ↥((univ.filter p).powersetCard r))
  refine
    { toFun := fun s ↦ ⟨s.val.val, mem_powersetCard.mpr ⟨?_, (mem_powersetCard.mp s.val.2).2⟩⟩
      invFun := fun s ↦ ⟨⟨s.val, mem_powersetCard.mpr
        ⟨subset_univ _, (mem_powersetCard.mp s.2).2⟩⟩, ?_⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  · intro a ha
    exact mem_filter.mpr ⟨mem_univ _, s.2 a ha⟩
  · intro a ha
    exact (mem_filter.mp ((mem_powersetCard.mp s.2).1 ha)).2

private theorem choose_three_lower {m : ℕ} (hm : 4 ≤ m) :
    (m : ℝ) ^ 3 / 24 ≤ (m.choose 3 : ℝ) := by
  have h1 := Nat.choose_succ_right_eq m 1
  have h2 := Nat.choose_succ_right_eq m 2
  norm_num at h1 h2
  have h1' := congrArg (fun n : ℕ ↦ (n : ℝ)) h1
  have h2' := congrArg (fun n : ℕ ↦ (n : ℝ)) h2
  push_cast [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_sub (by omega : 2 ≤ m)] at h1' h2'
  have hm' : (4 : ℝ) ≤ m := by exact_mod_cast hm
  have hmul₁ : (m : ℝ) / 2 * (m / 2) ≤ (m - 1) * (m - 2) :=
    mul_le_mul (by linarith) (by linarith) (by positivity) (by linarith)
  have hmul₂ := mul_le_mul_of_nonneg_left hmul₁ (Nat.cast_nonneg m)
  linear_combination hmul₂ / 6 - h2' / 3 - h1' * ((m : ℝ) - 2) / 6

private theorem slices_three_upper {n : ℕ} : (n.choose 3 : ℝ) ≤ (n : ℝ) ^ 3 := by
  exact_mod_cast Nat.choose_le_pow n 3

private theorem dense_fibers {α β : Type*} [Fintype α] [Fintype β] [Nonempty α]
    (p : α → β → Prop) {δ : ℝ} (hδ : 0 < δ)
    (h : δ * Fintype.card α * Fintype.card β ≤
      (count (fun ab : α × β ↦ p ab.1 ab.2) : ℝ)) :
    δ / 2 * Fintype.card β ≤
      (count (fun b ↦ δ / 2 * Fintype.card α ≤ (count (fun a ↦ p a b) : ℝ)) : ℝ) := by
  classical
  let good : β → Prop := fun b ↦ δ / 2 * Fintype.card α ≤ (count (fun a ↦ p a b) : ℝ)
  have hle (b : β) : (count (fun a ↦ p a b) : ℝ) ≤
      (if good b then (Fintype.card α : ℝ) else 0) + δ / 2 * Fintype.card α := by
    by_cases hb : good b
    · rw [ite_eq_left hb]
      have hc : (count (fun a ↦ p a b) : ℝ) ≤ Fintype.card α := by exact_mod_cast count_le _
      linarith [show 0 ≤ δ / 2 * Fintype.card α by positivity]
    · rw [ite_eq_right hb, zero_add]
      exact (lt_of_not_ge hb).le
  rw [count_fiber_swap, Nat.cast_sum] at h
  have hg := sum_le_sum (s := (univ : Finset β)) fun b _ ↦ hle b
  simp only [sum_add_distrib, ← sum_filter, sum_const, card_univ, nsmul_eq_mul] at hg
  change _ ≤ (count good : ℝ) * Fintype.card α + _ at hg
  change δ / 2 * Fintype.card β ≤ (count good : ℝ)
  have hn : 0 < (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
  apply le_of_mul_le_mul_right _ hn
  linarith only [h, hg]

private theorem dense_triple_fiber {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (p : α → β → Prop) {δ : ℝ} (hδ : 0 < δ) (hsize : 4 ≤ δ / 2 * Fintype.card α)
    (h : δ * Fintype.card α * Fintype.card β ≤
      (count (fun ab : α × β ↦ p ab.1 ab.2) : ℝ)) :
    ∃ s : Slices α 3, δ ^ 4 / 384 * Fintype.card β ≤
      (count (fun b ↦ ∀ a ∈ s.val, p a b) : ℝ) := by
  classical
  let good : β → Prop := fun b ↦ δ / 2 * Fintype.card α ≤ (count (fun a ↦ p a b) : ℝ)
  let q (s : Slices α 3) (b : β) : Prop := ∀ a ∈ s.val, p a b
  have hgood : δ / 2 * Fintype.card β ≤ (count good : ℝ) := dense_fibers p hδ h
  let K : ℝ := (δ / 2 * Fintype.card α) ^ 3 / 24
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hfor (b : β) (hb : good b) : K ≤ (count (fun s ↦ q s b) : ℝ) := by
    rw [show count (fun s ↦ q s b) = (count (fun a ↦ p a b)).choose 3 from count_slices 3 _]
    have hd : 4 ≤ count (fun a ↦ p a b) := by exact_mod_cast hsize.trans hb
    apply le_trans _ (choose_three_lower hd)
    dsimp [K]
    gcongr
  have hsum : (count good : ℝ) * K ≤ (count (fun sb : Slices α 3 × β ↦ q sb.1 sb.2) : ℝ) := by
    rw [count_fiber_swap, Nat.cast_sum]
    calc
      _ = ∑ b ∈ univ.filter good, K := by simp [count, nsmul_eq_mul]
      _ ≤ ∑ b ∈ univ.filter good, (count (fun s ↦ q s b) : ℝ) :=
        sum_le_sum fun b hb ↦ hfor b (mem_filter.mp hb).2
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ ↦ by positivity)
  have hn : 0 < (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
  have hδ' : 0 ≤ δ ^ 4 / 384 * Fintype.card β := by positivity
  have hm := mul_le_mul_of_nonneg_right hgood hK
  have hbound := mul_le_mul_of_nonneg_left (slices_three_upper (n := Fintype.card α)) hδ'
  have hcalc : δ ^ 4 / 384 * Fintype.card β * Fintype.card (Slices α 3) ≤
      (count (fun sb : Slices α 3 × β ↦ q sb.1 sb.2) : ℝ) := calc
    _ ≤ δ ^ 4 / 384 * Fintype.card β * (Fintype.card α : ℝ) ^ 3 := by rwa [slices_card]
    _ = δ / 2 * Fintype.card β * K := by dsimp [K]; ring
    _ ≤ _ := hm.trans hsum
  have hexist : 0 < count (fun sb : Slices α 3 × β ↦ q sb.1 sb.2) := by
    have hp : 0 < δ / 2 * Fintype.card β * K := by
      have hnβ : 0 < (Fintype.card β : ℝ) := by exact_mod_cast Fintype.card_pos
      dsimp [K]
      positivity
    exact_mod_cast hp.trans_le (hm.trans hsum)
  obtain ⟨x, _⟩ := card_pos.mp hexist
  let : Nonempty (Slices α 3) := ⟨x.1⟩
  exact exists_large_fiber q _ hcalc

/-- Finite fiber extraction: a dense relation on `k` coordinates contains a box
with three choices per coordinate, once the alphabet is sufficiently large. -/
private theorem dense_box (k : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ {α : Type*} [Fintype α], N ≤ Fintype.card α →
      ∀ R : (Fin k → α) → Prop,
        δ * (Fintype.card α : ℝ) ^ k ≤ (count R : ℝ) →
        ∃ A : Fin k → Slices α 3, ∀ f : Fin k → α, (∀ i, f i ∈ (A i).val) → R f := by
  classical
  induction k generalizing δ with
  | zero =>
    refine ⟨0, ?_⟩
    intro α _ _ R h
    refine ⟨Fin.elim0, fun f _ ↦ ?_⟩
    have hp : 0 < count R := by
      simp only [pow_zero, mul_one] at h
      exact_mod_cast hδ.trans_le h
    obtain ⟨g, hg⟩ := card_pos.mp hp
    have he : f = g := Subsingleton.elim _ _
    exact he ▸ (mem_filter.mp hg).2
  | succ k ih =>
    have hδ' : 0 < δ ^ 4 / 384 := by positivity
    obtain ⟨N, hN⟩ := ih (δ ^ 4 / 384) hδ'
    obtain ⟨M, hM⟩ := exists_nat_ge (8 / δ)
    refine ⟨max (max N M) 1, ?_⟩
    intro α _ hsize R hR
    have hN' : N ≤ Fintype.card α := le_trans (le_max_left ..) ((le_max_left ..).trans hsize)
    have hM' : M ≤ Fintype.card α := le_trans (le_max_right ..) ((le_max_left ..).trans hsize)
    let : Nonempty α := Fintype.card_pos_iff.mp (lt_of_lt_of_le Nat.zero_lt_one
      ((le_max_right ..).trans hsize))
    let p (a : α) (f : Fin k → α) := R (Fin.cons a f)
    have heq : count (fun ab : α × (Fin k → α) ↦ p ab.1 ab.2) = count R :=
      count_congr (Fin.consEquiv (fun _ ↦ α)) fun _ ↦ Iff.rfl
    have hs : 4 ≤ δ / 2 * Fintype.card α := by
      have hm := hM.trans (show (M : ℝ) ≤ Fintype.card α by exact_mod_cast hM')
      have hm' := (div_le_iff₀ hδ).mp hm
      linarith
    have hp : δ * Fintype.card α * Fintype.card (Fin k → α) ≤
        (count (fun ab : α × (Fin k → α) ↦ p ab.1 ab.2) : ℝ) := by
      rw [heq, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
      rwa [pow_succ', ← mul_assoc] at hR
    obtain ⟨s, hs⟩ := dense_triple_fiber p hδ hs hp
    rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] at hs
    obtain ⟨A, hA⟩ := hN hN' _ hs
    refine ⟨Fin.cons s A, fun f hf ↦ ?_⟩
    simpa [p] using hA (Fin.tail f) (fun i ↦ hf i.succ) (f 0) (by simpa using hf 0)

open SimpleGraph

private def CliqueMap {α : Type*} (G : SimpleGraph α) {k : ℕ} (f : Fin k → α) : Prop :=
  Pairwise fun i j ↦ G.Adj (f i) (f j)

private theorem cliqueMap_injective {α : Type*} {G : SimpleGraph α} {k : ℕ}
    {f : Fin k → α} (h : CliqueMap G f) : Function.Injective f :=
  fun _ _ e ↦ by_contra fun hn ↦ (G.ne_of_adj (h hn)) e

open Classical in
private theorem cliqueMap_image {α : Type*} {G : SimpleGraph α} {k : ℕ}
    {f : Fin k → α} (h : CliqueMap G f) : G.IsNClique k (univ.image f) := by
  classical
  refine ⟨?_, ?_⟩
  swap
  · rw [card_image_of_injective _ (cliqueMap_injective h), card_univ, Fintype.card_fin]
  intro a ha b hb hab
  obtain ⟨i, _, rfl⟩ := mem_image.mp ha
  obtain ⟨j, _, rfl⟩ := mem_image.mp hb
  exact h (ne_of_apply_ne f hab)

open Classical in
private theorem cliqueMap_and_range {α : Type*} {G : SimpleGraph α} {k : ℕ} {s : Finset α}
    (hs : G.IsNClique k s) (e : Fin k ≃ s) :
    CliqueMap G (fun i ↦ (e i).val) ∧ univ.image (fun i ↦ (e i).val) = s := by
  classical
  refine ⟨fun i j hij ↦ hs.1 (e i).2 (e j).2 (fun he ↦ hij (e.injective (Subtype.ext he))), ?_⟩
  ext a
  constructor
  · rintro (ha : a ∈ univ.image (fun i ↦ (e i).val))
    obtain ⟨i, _, rfl⟩ := mem_image.mp ha
    exact (e i).2
  · intro ha
    exact mem_image.mpr ⟨e.symm ⟨a, ha⟩, mem_univ _, by simp⟩

private theorem cliqueFree_iff_no_map {α : Type*} (G : SimpleGraph α) (k : ℕ) :
    G.CliqueFree k ↔ ∀ f : Fin k → α, ¬ CliqueMap G f := by
  refine ⟨fun h _ hf ↦ h _ (cliqueMap_image hf), fun h s hs ↦ ?_⟩
  exact h _ (cliqueMap_and_range hs (equivFinOfCardEq hs.2).symm).1

open Classical in
/-- Ordering an unordered clique gives exactly `k!` clique maps. -/
private theorem count_cliqueMaps {α : Type*} [Fintype α] (G : SimpleGraph α) (k : ℕ) :
    count (CliqueMap (k := k) G) = (G.cliqueFinset k).card * k.factorial := by
  classical
  let S := ↥(G.cliqueFinset k)
  let e (s : S) : Fin k ≃ s.val := (equivFinOfCardEq (mem_cliqueFinset_iff.mp s.2).2).symm
  let sMap (f : {f // CliqueMap (k := k) G f}) : S :=
    ⟨univ.image f.val, mem_cliqueFinset_iff.mpr (cliqueMap_image f.2)⟩
  let fe (f : {f // CliqueMap (k := k) G f}) : Fin k ≃ (sMap f).val :=
    Equiv.ofBijective (fun i ↦ ⟨f.val i, mem_image_of_mem _ (mem_univ _)⟩)
      ⟨fun _ _ h ↦ cliqueMap_injective f.2 (congrArg Subtype.val h), fun a ↦ by
        obtain ⟨i, _, hi⟩ := mem_image.mp a.2
        exact ⟨i, Subtype.ext hi⟩⟩
  let reorder (s : S) (p : Equiv.Perm (Fin k)) : {f // CliqueMap (k := k) G f} :=
    ⟨fun i ↦ (e s (p i)).val, (cliqueMap_and_range (mem_cliqueFinset_iff.mp s.2) (p.trans (e s))).1⟩
  have hreorder (s : S) (p : Equiv.Perm (Fin k)) : sMap (reorder s p) = s :=
    Subtype.ext (cliqueMap_and_range (mem_cliqueFinset_iff.mp s.2) (p.trans (e s))).2
  let equiv : {f // CliqueMap (k := k) G f} ≃ S × Equiv.Perm (Fin k) :=
    { toFun := fun f ↦ (sMap f, (fe f).trans (e (sMap f)).symm)
      invFun := fun sp ↦ reorder sp.1 sp.2
      left_inv := fun f ↦ Subtype.ext (funext fun i ↦
        congrArg Subtype.val ((e (sMap f)).apply_symm_apply (fe f i)))
      right_inv := fun ⟨s, p⟩ ↦ by
        apply Prod.ext (hreorder s p)
        apply Equiv.ext
        intro i
        apply (e (sMap (reorder s p))).injective
        simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
        apply Subtype.ext
        change (e s (p i)).val = (e (sMap (reorder s p)) (p i)).val
        rw [hreorder] }
  rw [count_eq_card, Nat.card_congr equiv, Nat.card_eq_fintype_card, Fintype.card_prod,
    Fintype.card_coe, Fintype.card_perm, Fintype.card_fin]

open Classical in
private theorem count_adj_pairs {α : Type*} [Fintype α] (G : SimpleGraph α) :
    count (fun a : α × α ↦ G.Adj a.1 a.2) = 2 * G.edgeFinset.card := by
  classical
  rw [count_fiber, ← G.sum_degrees_eq_twice_card_edges]
  apply sum_congr rfl
  intro a _
  rw [← G.card_neighborFinset_eq_degree, neighborFinset_eq_filter]
  rfl

private def Triangle {α : Type*} (G : SimpleGraph α) (u v w : α) : Prop :=
  G.Adj u v ∧ G.Adj u w ∧ G.Adj v w

private theorem count_cliqueTriples {α : Type*} [Fintype α] (G : SimpleGraph α) :
    count (CliqueMap (k := 3) G) = count (fun x : α × α × α ↦ Triangle G x.1 x.2.1 x.2.2) := by
  classical
  let e₂ : (Fin 2 → α) ≃ α × α := (Fin.consEquiv (fun _ ↦ α)).symm.trans
    (Equiv.prodCongr (Equiv.refl α) (Equiv.funUnique (Fin 1) α))
  let e : (Fin 3 → α) ≃ α × α × α := (Fin.consEquiv (fun _ ↦ α)).symm.trans
    (Equiv.prodCongr (Equiv.refl α) e₂)
  apply count_congr e
  intro f
  change CliqueMap G f ↔ Triangle G (f 0) (f 1) (f 2)
  refine ⟨fun h ↦ ⟨h (by decide), h (by decide), h (by decide)⟩, fun ⟨h₀₁, h₀₂, h₁₂⟩ i j hij ↦ ?_⟩
  fin_cases i <;> fin_cases j <;>
    first | exact False.elim (hij rfl) | exact h₀₁ | exact h₀₂ | exact h₁₂ |
      exact G.adj_symm h₀₁ | exact G.adj_symm h₀₂ | exact G.adj_symm h₁₂

private theorem adj_pairs_le {α : Type*} [Fintype α] (G : SimpleGraph α) {r : ℕ}
    (hr : 1 ≤ r) (h : G.CliqueFree (r + 1)) :
    r * (count (fun a : α × α ↦ G.Adj a.1 a.2) : ℝ) ≤ (r - 1 : ℝ) * (Fintype.card α : ℝ) ^ 2 := by
  classical
  rw [count_adj_pairs]
  have ht := Nat.mul_le_mul_left (2 * r) h.card_edgeFinset_le
  have ht' := ht.trans (SimpleGraph.mul_turanNumber_le (n := Fintype.card α) (r := r))
  have hc := (show ((2 * r * G.edgeFinset.card : ℕ) : ℝ) ≤
      (((r - 1) * Fintype.card α ^ 2 : ℕ) : ℝ) by exact_mod_cast ht')
  push_cast [Nat.cast_sub hr] at hc ⊢
  simpa only [mul_assoc, mul_left_comm] using hc

private theorem neighborhood_cliqueFree {α : Type*} {G : SimpleGraph α}
    (h : G.CliqueFree 4) (a : α) : (G.induce (G.neighborSet a)).CliqueFree 3 := by
  classical
  rw [cliqueFree_iff_no_map] at h ⊢
  intro f hf
  apply h (Fin.cons a (fun i ↦ (f i).val))
  intro i j
  refine Fin.cases ?_ (fun i ↦ ?_) i <;> refine Fin.cases ?_ (fun j ↦ ?_) j
  · exact fun hij ↦ (hij rfl).elim
  · exact fun _ ↦ (f j).2
  · exact fun _ ↦ G.adj_symm (f i).2
  · exact fun hij ↦ hf (fun e ↦ hij (congrArg Fin.succ e))

open Classical in
private theorem count_triangles_at {α : Type*} [Fintype α] (G : SimpleGraph α) (a : α) :
    count (fun bc : α × α ↦ Triangle G a bc.1 bc.2) =
      count (fun bc : G.neighborSet a × G.neighborSet a ↦
        (G.induce (G.neighborSet a)).Adj bc.1 bc.2) := by
  classical
  rw [count_eq_card, count_eq_card]
  apply Nat.card_congr
  exact
    { toFun := fun ⟨⟨b, c⟩, h₁, h₂, h₃⟩ ↦ ⟨(⟨b, h₁⟩, ⟨c, h₂⟩), h₃⟩
      invFun := fun ⟨⟨b, c⟩, h⟩ ↦ ⟨(b.val, c.val), b.2, c.2, h⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

private theorem count_and {α : Type*} [Fintype α] (P : Prop) (Q : α → Prop) [Decidable P] :
    count (fun a ↦ P ∧ Q a) = if P then count Q else 0 := by
  classical
  by_cases h : P <;> simp [count, h]

open Classical in
private theorem degree_sum_sq {α : Type*} [Fintype α] (G : SimpleGraph α) :
    (∑ a : α, ∑ b : α, if G.Adj a b then (G.degree a : ℝ) else 0) =
      ∑ a : α, (G.degree a : ℝ) ^ 2 := by
  classical
  apply sum_congr rfl
  intro a _
  rw [← sum_filter, sum_const, nsmul_eq_mul]
  rw [← neighborFinset_eq_filter, card_neighborFinset_eq_degree, pow_two]

/-- The triangle version of the Turán bound for a `K₄`-free graph.
Apply Mantel in each neighborhood, and count the degrees at the ends of each edge. -/
private theorem cliqueFree_triangle_bound {α : Type*} [Fintype α] (G : SimpleGraph α)
    (h : G.CliqueFree 4) : (count (CliqueMap (k := 3) G) : ℝ) ≤
      (2 / 9 : ℝ) * (Fintype.card α : ℝ) ^ 3 := by
  classical
  let n : ℝ := Fintype.card α
  let t : ℝ := count (fun x : α × α × α ↦ Triangle G x.1 x.2.1 x.2.2)
  let e : ℝ := count (fun a : α × α ↦ G.Adj a.1 a.2)
  let s : ℝ := ∑ a : α, (G.degree a : ℝ) ^ 2
  have hMantel : 2 * t ≤ s := by
    have hsum (a : α) :
        2 * (count (fun bc : α × α ↦ Triangle G a bc.1 bc.2) : ℝ) ≤ (G.degree a : ℝ) ^ 2 := by
      rw [count_triangles_at]
      have hh := adj_pairs_le (r := 2) _ (by decide) (neighborhood_cliqueFree h a)
      rw [card_neighborSet_eq_degree] at hh
      simpa only [Nat.cast_ofNat, show (2 : ℝ) - 1 = 1 by norm_num, one_mul] using hh
    change 2 * (count _ : ℝ) ≤ _
    rw [count_fiber (fun a (bc : α × α) ↦ Triangle G a bc.1 bc.2), Nat.cast_sum, mul_sum]
    exact sum_le_sum (fun a _ ↦ hsum a)
  let common (a b : α) := count (fun c ↦ G.Adj a c ∧ G.Adj b c)
  have hcommon (a b : α) : (G.degree a : ℝ) + G.degree b ≤ n + common a b := by
    have hi : (G.neighborFinset a ∩ G.neighborFinset b).card = common a b := by
      congr 1
      ext c
      simp
    have hu : (G.neighborFinset a ∪ G.neighborFinset b).card ≤ Fintype.card α := card_le_univ _
    have heq := card_union_add_card_inter (G.neighborFinset a) (G.neighborFinset b)
    rw [hi, card_neighborFinset_eq_degree, card_neighborFinset_eq_degree] at heq
    dsimp [n]
    exact_mod_cast (show G.degree a + G.degree b ≤ Fintype.card α + common a b by omega)
  have hpairs : e = ∑ a : α, ∑ b : α, if G.Adj a b then (1 : ℝ) else 0 := by
    change (count _ : ℝ) = _
    rw [count_fiber, Nat.cast_sum]
    apply sum_congr rfl
    intro a _
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
    congr 1
  have htri : t = ∑ a : α, ∑ b : α, if G.Adj a b then (common a b : ℝ) else 0 := by
    have he := count_congr (Equiv.prodAssoc α α α) (p := fun x ↦ Triangle G x.1.1 x.1.2 x.2)
      (q := fun x ↦ Triangle G x.1 x.2.1 x.2.2) (fun _ ↦ Iff.rfl)
    change (count _ : ℝ) = _
    rw [← he, count_fiber (fun (ab : α × α) c ↦ Triangle G ab.1 ab.2 c),
      Nat.cast_sum, Fintype.sum_prod_type]
    simp only [Triangle, count_and, Nat.cast_ite, Nat.cast_zero, common]
  have hEnds : 2 * s ≤ n * e + t := by
    have hsum : (∑ a : α, ∑ b : α, if G.Adj a b then (G.degree a : ℝ) + G.degree b else 0) ≤
        ∑ a : α, ∑ b : α, if G.Adj a b then n + common a b else 0 :=
      sum_le_sum (fun a _ ↦ sum_le_sum fun b _ ↦ by
        by_cases hab : G.Adj a b <;> simp [hab, hcommon a b])
    have hswap : (∑ a : α, ∑ b : α, if G.Adj a b then (G.degree b : ℝ) else 0) = s := by
      rw [sum_comm]
      dsimp only [s]
      rw [← degree_sum_sq G]
      apply sum_congr rfl
      intro a _
      apply sum_congr rfl
      intro b _
      rw [G.adj_comm]
    have hh : (∑ a : α, ∑ b : α, if G.Adj a b then n else 0) = n * e := by
      rw [hpairs, mul_sum]
      apply sum_congr rfl
      intro a _
      rw [mul_sum]
      apply sum_congr rfl
      intro b _
      by_cases hab : G.Adj a b <;> simp [hab]
    simp_rw [ite_add_zero, sum_add_distrib] at hsum
    rw [degree_sum_sq G, hswap, hh, ← htri] at hsum
    linarith only [hsum]
  have hTuran : 3 * e ≤ 2 * n ^ 2 := by
    have hh := adj_pairs_le (r := 3) G (by decide) h
    norm_num at hh
    exact hh
  have hne := mul_le_mul_of_nonneg_left hTuran (show 0 ≤ n by positivity)
  rw [count_cliqueTriples]
  change t ≤ 2 / 9 * n ^ 3
  linarith only [hMantel, hEnds, hne]

/-- For a prescribed `k`-subset of sample positions, all assignments on its complement
are equally available. -/
private theorem clique_sample_fiber {α : Type*} [Fintype α] (G : SimpleGraph α)
    {m k : ℕ} (s : Slices (Fin m) k) :
    count (fun f : Fin m → α ↦ (G.comap f).IsClique (s.val : Set (Fin m))) =
      count (CliqueMap (k := k) G) * Fintype.card α ^ (m - k) := by
  classical
  let e : Fin k ≃ s.val := (equivFinOfCardEq (mem_powersetCard.mp s.2).2).symm
  let equiv : (Fin m → α) ≃ (Fin k → α) × ((i : {i // i ∉ s.val}) → α) :=
    (Equiv.piEquivPiSubtypeProd (fun i ↦ i ∈ s.val) (fun _ ↦ α)).trans
      (Equiv.prodCongr (Equiv.piCongrLeft (fun _ ↦ α) e).symm (Equiv.refl _))
  have he : ∀ f : Fin m → α, (G.comap f).IsClique (s.val : Set (Fin m)) ↔
      CliqueMap G (equiv f).1 := by
    intro f
    change (G.comap f).IsClique (s.val : Set (Fin m)) ↔ CliqueMap G (fun i ↦ f (e i).val)
    refine ⟨fun h i j hij ↦ h (e i).2 (e j).2 (fun q ↦ hij (e.injective (Subtype.ext q))), ?_⟩
    intro h i hi j hj hij
    have hn : e.symm ⟨i, hi⟩ ≠ e.symm ⟨j, hj⟩ :=
      fun eq ↦ hij (congrArg Subtype.val (e.symm.injective eq))
    simpa using h hn
  rw [count_congr equiv (q := fun fg ↦ CliqueMap G fg.1) he]
  rw [count_eq_card, count_eq_card]
  let t : Type _ := {i : Fin m // i ∉ s.val}
  have hk : Fintype.card t = m - k := by
    have hc := Fintype.card_subtype_compl (fun i : Fin m ↦ i ∈ s.val)
    change Fintype.card t = _ at hc
    simpa [Fintype.card_coe, (mem_powersetCard.mp s.2).2] using hc
  let es : {fg : (Fin k → α) × (t → α) // CliqueMap G fg.1} ≃
      {f // CliqueMap (k := k) G f} × (t → α) :=
    { toFun := fun x ↦ (⟨x.1.1, x.2⟩, x.1.2)
      invFun := fun x ↦ ⟨(x.1.1, x.2), x.1.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  rw [Nat.card_congr es, Nat.card_prod, Nat.card_eq_fintype_card (α := t → α), Fintype.card_fun, hk]

private theorem clique_sample_count {α : Type*} [Fintype α] (G : SimpleGraph α)
    (m k : ℕ) : (∑ f : Fin m → α, count (fun s : Slices (Fin m) k ↦
      (G.comap f).IsClique (s.val : Set (Fin m)))) =
      m.choose k * count (CliqueMap (k := k) G) * Fintype.card α ^ (m - k) := by
  classical
  rw [← count_fiber (fun f (s : Slices (Fin m) k) ↦ (G.comap f).IsClique (s.val : Set (Fin m))),
    count_fiber_swap (fun f (s : Slices (Fin m) k) ↦ (G.comap f).IsClique (s.val : Set (Fin m))),
    sum_congr rfl (fun s _ ↦ clique_sample_fiber G s)]
  simp [mul_assoc]

open Classical in
private theorem sample_count_eq {α : Type*} [Fintype α] (G : SimpleGraph α) (k : ℕ) :
    count (fun s : Slices α k ↦ G.IsClique (s.val : Set α)) = (G.cliqueFinset k).card := by
  rw [count_eq_card, ← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  exact
    { toFun := fun s ↦ ⟨s.val.val, mem_cliqueFinset_iff.mpr ⟨s.2, (mem_powersetCard.mp s.val.2).2⟩⟩
      invFun := fun s ↦ ⟨⟨s.val, mem_powersetCard.mpr
        ⟨subset_univ _, (mem_cliqueFinset_iff.mp s.2).2⟩⟩, (mem_cliqueFinset_iff.mp s.2).1⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

private theorem choose_three_eq {m : ℕ} (hm : 2 ≤ m) :
    6 * (m.choose 3 : ℝ) = (m : ℝ) * (m - 1) * (m - 2) := by
  have h1 := Nat.choose_succ_right_eq m 1
  have h2 := Nat.choose_succ_right_eq m 2
  norm_num at h1 h2
  have h1' := congrArg (fun n : ℕ ↦ (n : ℝ)) h1
  have h2' := congrArg (fun n : ℕ ↦ (n : ℝ)) h2
  push_cast [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_sub hm] at h1' h2'
  linear_combination 2 * h2' + ((m : ℝ) - 2) * h1'

private theorem count_exists_le {α β : Type*} [Fintype α] [Fintype β] (p : α → β → Prop) :
    count (fun a ↦ ∃ b, p a b) ≤ count (fun ab : α × β ↦ p ab.1 ab.2) := by
  classical
  rw [count_eq_card, count_eq_card]
  apply Nat.card_le_card_of_surjective (fun x ↦ ⟨x.val.1, x.val.2, x.2⟩)
  rintro ⟨a, b, hb⟩
  exact ⟨⟨(a, b), hb⟩, rfl⟩

/-- Supersaturation from fixed-size sampling. Sampling with replacement lets the
triangle and `K₄` incidences factor into a count on the chosen positions and a
power of the alphabet size. -/
private theorem triangle_supersaturation (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ {α : Type*} [Fintype α] [Nonempty α] (G : SimpleGraph α),
      (2 / 9 + ε) * (Fintype.card α : ℝ) ^ 3 ≤ (count (CliqueMap (k := 3) G) : ℝ) →
      c * (Fintype.card α : ℝ) ^ 4 ≤ (count (CliqueMap (k := 4) G) : ℝ) := by
  classical
  obtain ⟨m₀, hm₀⟩ := exists_nat_ge (6 / ε)
  let m := max m₀ 4
  have hm : 4 ≤ m := le_max_right ..
  have hm' : 6 ≤ ε * (m : ℝ) := by
    have hmul := (div_le_iff₀ hε).mp (hm₀.trans (by exact_mod_cast le_max_left m₀ 4 :
      (m₀ : ℝ) ≤ m))
    linarith only [hmul]
  let M : ℝ := m
  have hM : 0 < M := by dsimp [M]; exact_mod_cast (show 0 < m by omega)
  refine ⟨ε / (2 * M ^ 4), by positivity, ?_⟩
  intro α _ _ G hG
  let n : ℝ := Fintype.card α
  have hn : 0 < n := by dsimp [n]; exact_mod_cast Fintype.card_pos
  let t : ℝ := count (CliqueMap (k := 3) G)
  let q : ℝ := count (CliqueMap (k := 4) G)
  let tr (f : Fin m → α) : Prop := ¬(G.comap f).CliqueFree 4
  have htr (f : Fin m → α) : tr f ↔ ∃ s : Slices (Fin m) 4,
      (G.comap f).IsClique (s.val : Set (Fin m)) := by
    change (¬∀ s, ¬(G.comap f).IsNClique 4 s) ↔ _
    push Not
    refine ⟨fun ⟨s, hs⟩ ↦ ⟨⟨s, mem_powersetCard.mpr ⟨subset_univ _, hs.2⟩⟩, hs.1⟩,
      fun ⟨s, hs⟩ ↦ ⟨s.val, hs, (mem_powersetCard.mp s.2).2⟩⟩
  have hbad : (count tr : ℝ) ≤ (m.choose 4 : ℝ) * q * n ^ (m - 4) := by
    have he := count_congr (Equiv.refl _) (p := tr)
      (q := fun f ↦ ∃ s : Slices (Fin m) 4, (G.comap f).IsClique (s.val : Set (Fin m))) htr
    rw [he]
    have hle := count_exists_le (fun f (s : Slices (Fin m) 4) ↦
      (G.comap f).IsClique (s.val : Set (Fin m)))
    rw [count_fiber (fun f (s : Slices (Fin m) 4) ↦ (G.comap f).IsClique (s.val : Set (Fin m))),
      clique_sample_count] at hle
    dsimp [n, q]
    exact_mod_cast hle
  have hpoint (f : Fin m → α) :
      (count (CliqueMap (k := 3) (G.comap f)) : ℝ) ≤
      (2 / 9 : ℝ) * M ^ 3 + (if tr f then M ^ 3 else 0) := by
    by_cases hb : tr f
    · rw [ite_eq_left hb]
      have hle := count_le (CliqueMap (k := 3) (G.comap f))
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at hle
      have hh : (count (CliqueMap (k := 3) (G.comap f)) : ℝ) ≤ M ^ 3 := by
        dsimp [M]
        exact_mod_cast hle
      linarith [show 0 ≤ (2 / 9 : ℝ) * M ^ 3 by positivity]
    · rw [ite_eq_right hb, add_zero]
      simpa [M] using cliqueFree_triangle_bound (G.comap f) (not_not.mp hb)
  have hsum := sum_le_sum (s := (univ : Finset (Fin m → α))) (fun f _ ↦ hpoint f)
  simp only [sum_add_distrib, ← sum_filter, sum_const, card_univ, nsmul_eq_mul, Fintype.card_fun,
    Fintype.card_fin, Nat.cast_pow] at hsum
  simp_rw [count_cliqueMaps, ← sample_count_eq, Nat.cast_mul] at hsum
  norm_num [Nat.factorial] at hsum
  rw [← sum_mul, ← Nat.cast_sum, clique_sample_count, Nat.cast_mul, Nat.cast_mul,
    Nat.cast_pow] at hsum
  have hc : (univ.filter tr).card = count tr := by
    unfold count
    congr
  rw [hc] at hsum
  change (m.choose 3 : ℝ) * t * n ^ (m - 3) * 6 ≤
    n ^ m * (2 / 9 * M ^ 3) + (count tr : ℝ) * M ^ 3 at hsum
  have hq : (m.choose 4 : ℝ) ≤ M ^ 4 := by dsimp [M]; exact_mod_cast Nat.choose_le_pow m 4
  have hbad' : (count tr : ℝ) ≤ M ^ 4 * q * n ^ (m - 4) := by
    apply hbad.trans
    gcongr
  have htotal := hsum.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_right hbad' (show 0 ≤ M ^ 3 by positivity)))
  have hnorm : 6 * (m.choose 3 : ℝ) * (t / n ^ 3) ≤
      2 / 9 * M ^ 3 + M ^ 4 * (q / n ^ 4) * M ^ 3 := by
    apply le_of_mul_le_mul_right _ (show 0 < n ^ m by positivity)
    have hpow (k : ℕ) (hk : k ≤ m) : n ^ m = n ^ k * n ^ (m - k) := by
      rw [← pow_add, Nat.add_sub_of_le hk]
    have h3 : t / n ^ 3 * n ^ m = t * n ^ (m - 3) := by
      rw [hpow 3 (by omega)]; field_simp
    have h4 : q / n ^ 4 * n ^ m = q * n ^ (m - 4) := by
      rw [hpow 4 hm]; field_simp
    linear_combination htotal + 6 * (m.choose 3 : ℝ) * h3 - M ^ 7 * h4
  have ht₁ : 2 / 9 + ε ≤ t / n ^ 3 := (le_div_iff₀ (by positivity)).mpr hG
  have ht₂ : t / n ^ 3 ≤ 1 := by
    apply (div_le_iff₀ (by positivity)).mpr
    rw [one_mul]
    have hle := count_le (CliqueMap (k := 3) G)
    rw [Fintype.card_fun, Fintype.card_fin] at hle
    dsimp [t, n]
    exact_mod_cast hle
  have hchoose : M ^ 3 - 3 * M ^ 2 ≤ 6 * (m.choose 3 : ℝ) := by
    rw [choose_three_eq (by omega)]
    dsimp [M]
    linarith [show 0 ≤ (m : ℝ) by positivity]
  have hlow : (2 / 9 + ε) * M ^ 3 - 3 * M ^ 2 ≤ 6 * (m.choose 3 : ℝ) * (t / n ^ 3) := by
    have h₁ := mul_le_mul_of_nonneg_right ht₁ (show 0 ≤ M ^ 3 by positivity)
    have h₂ := mul_le_mul_of_nonneg_right ht₂ (show 0 ≤ 3 * M ^ 2 by positivity)
    have h₃ := mul_le_mul_of_nonneg_right hchoose (show 0 ≤ t / n ^ 3 by positivity)
    linarith only [h₁, h₂, h₃]
  have hεM := mul_le_mul_of_nonneg_right hm' (show 0 ≤ M ^ 2 / 2 by positivity)
  have hfin : ε / 2 * M ^ 3 ≤ M ^ 4 * (q / n ^ 4) * M ^ 3 := by
    change 6 * (M ^ 2 / 2) ≤ ε * M * (M ^ 2 / 2) at hεM
    linarith only [hεM, hlow, hnorm]
  have hfin' := le_of_mul_le_mul_right hfin (show 0 < M ^ 3 by positivity)
  apply (le_div_iff₀ (show 0 < n ^ 4 by positivity)).mp
  have hh := (div_le_iff₀ (show 0 < 2 * M ^ 4 by positivity)).mpr
    (show ε ≤ q / n ^ 4 * (2 * M ^ 4) by linarith only [hfin'])
  exact hh

open scoped RealInnerProductSpace

private abbrev Point := EuclideanSpace ℝ (Fin 6)

private def Witness {E : Type*} [MetricSpace E] (a b x : E) : Prop :=
  a ≠ b ∧ a ≠ x ∧ b ≠ x ∧ dist a b = dist a x ∧ dist a b = dist b x

private theorem Witness.symm {E : Type*} [MetricSpace E] {a b x : E} (h : Witness a b x) :
    Witness b a x := by
  rcases h with ⟨hn, ha, hb, hac, hbc⟩
  exact ⟨hn.symm, hb, ha, (dist_comm b a).trans hbc, (dist_comm b a).trans hac⟩

private theorem cross_distance {E : Type*} [MetricSpace E] {a b : Fin 3 → E} {x : E}
    (h : ∀ p q, Witness (a p) (b q) x) (p q : Fin 3) : dist (a p) (b q) = dist (a 0) (b 0) := by
  calc
    _ = dist (a p) x := (h p q).2.2.2.1
    _ = dist (a p) (b 0) := (h p 0).2.2.2.1.symm
    _ = dist (b 0) x := (h p 0).2.2.2.2
    _ = _ := (h 0 0).2.2.2.2.symm

private theorem differences_orthogonal {a b c d : Point}
    (h₁ : dist a c = dist b d) (h₂ : dist a d = dist b d) (h₃ : dist b c = dist b d) :
    ⟪a - b, c - d⟫ = 0 := by
  have eq (p q : Point) := norm_sub_sq_real p q
  simp only [← dist_eq_norm] at eq
  simp only [inner_sub_left, inner_sub_right]
  linarith only [eq a c, eq a d, eq b c, eq b d,
    congrArg (fun r : ℝ ↦ r ^ 2) h₁, congrArg (fun r : ℝ ↦ r ^ 2) h₂,
    congrArg (fun r : ℝ ↦ r ^ 2) h₃]

/-- A line meets a sphere in at most two points: the squared-distance equation
along the line through `a` and `b` has roots only at parameters zero and one. -/
private theorem sphere_differences {a b c x : Point} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h₁ : dist a x = dist b x) (h₂ : dist a x = dist c x) (r : ℝ) :
    c - a ≠ r • (b - a) := by
  intro hr
  let u := b - a
  let w := a - x
  have hbw : b - x = w + u := by dsimp [w, u]; abel
  have hcw : c - x = w + r • u := by rw [← hr]; dsimp [w]; abel
  have hb : ‖w‖ ^ 2 = ‖w + u‖ ^ 2 := by
    simpa only [dist_eq_norm, hbw] using congrArg (fun s : ℝ ↦ s ^ 2) h₁
  have hc : ‖w‖ ^ 2 = ‖w + r • u‖ ^ 2 := by
    simpa only [dist_eq_norm, hcw] using congrArg (fun s : ℝ ↦ s ^ 2) h₂
  rw [norm_add_sq_real] at hb hc
  rw [real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hc
  have hroot : (r * (r - 1)) * ‖u‖ ^ 2 = 0 := by linear_combination r * hb - hc
  have hu : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hab.symm)
  rcases mul_eq_zero.mp hroot with hh | hh
  · rcases mul_eq_zero.mp hh with rfl | ho
    · apply hac
      exact (sub_eq_zero.mp (by simpa using hr)).symm
    · have h : r = 1 := sub_eq_zero.mp ho
      rw [h, one_smul] at hr
      exact hbc (sub_left_injective hr).symm
  · exact (pow_ne_zero 2 hu) hh

/-- Four three-point classes with a fixed equilateral witness for each pair of
classes would contribute eight nonzero pairwise orthogonal directions in `ℝ⁶`. -/
private theorem no_witness_box (a : Fin 4 → Fin 3 → Point)
    (ha : ∀ i, Function.Injective (a i))
    (h : ∀ ⦃i j⦄, i ≠ j → ∃ x, ∀ p q, Witness (a i p) (a j q) x) : False := by
  let U (i : Fin 4) := a i 1 - a i 0
  let V (i : Fin 4) := a i 2 - a i 0
  let coeff (i : Fin 4) := ⟪U i, V i⟫ / ⟪U i, U i⟫
  let W (i : Fin 4) := V i - coeff i • U i
  have hU (i : Fin 4) : U i ≠ 0 := sub_ne_zero.mpr (fun e ↦ (by decide : (1 : Fin 3) ≠ 0) (ha i e))
  have hW (i : Fin 4) : W i ≠ 0 := by
    intro hw
    have hij : i ≠ i + 1 := by fin_cases i <;> decide
    obtain ⟨x, hx⟩ := h hij
    have hdist (p : Fin 3) : dist (a i p) x = dist (a (i + 1) 0) x :=
      (hx p 0).2.2.2.1.symm.trans (hx p 0).2.2.2.2
    have hne (p q : Fin 3) (hne : p ≠ q) : a i p ≠ a i q := fun e ↦ hne (ha i e)
    apply sphere_differences (hne _ _ (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide))
      ((hdist 0).trans (hdist 1).symm) ((hdist 0).trans (hdist 2).symm) (coeff i)
    exact sub_eq_zero.mp hw
  have hUW (i : Fin 4) : ⟪U i, W i⟫ = 0 := by
    have hi : ⟪U i, U i⟫ ≠ 0 := by
      rw [real_inner_self_eq_norm_sq]
      exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (hU i))
    dsimp only [W, coeff]
    rw [inner_sub_right, real_inner_smul_right, div_mul_cancel₀ _ hi, sub_self]
  have hortho {i j : Fin 4} (hij : i ≠ j) (p q : Fin 3) :
      ⟪a i p - a i 0, a j q - a j 0⟫ = 0 := by
    obtain ⟨x, hx⟩ := h hij
    exact differences_orthogonal (cross_distance hx p q) (cross_distance hx p 0)
      (cross_distance hx 0 q)
  let D (ip : Fin 4 × Fin 2) : Point := Fin.cases (U ip.1) (fun _ ↦ W ip.1) ip.2
  have hD (ip : Fin 4 × Fin 2) : D ip ≠ 0 := by
    obtain ⟨i, p⟩ := ip
    fin_cases p
    · exact hU i
    · exact hW i
  have hDD : Pairwise fun ip jq ↦ ⟪D ip, D jq⟫ = 0 := by
    rintro ⟨i, p⟩ ⟨j, q⟩ hn
    by_cases hi : i = j
    · subst j
      have hpq : p ≠ q := fun e ↦ hn (Prod.ext rfl e)
      fin_cases p <;> fin_cases q
      · exact (hpq rfl).elim
      · exact hUW i
      · exact (real_inner_comm (U i) (W i)).trans (hUW i)
      · exact (hpq rfl).elim
    · have h₁ : ⟪U i, U j⟫ = 0 := hortho hi 1 1
      have h₂ : ⟪U i, V j⟫ = 0 := hortho hi 1 2
      have h₃ : ⟪V i, U j⟫ = 0 := hortho hi 2 1
      have h₄ : ⟪V i, V j⟫ = 0 := hortho hi 2 2
      fin_cases p <;> fin_cases q
      · exact h₁
      · change ⟪U i, W j⟫ = 0
        simp only [W, inner_sub_right, real_inner_smul_right, h₁, h₂, mul_zero, sub_zero]
      · change ⟪W i, U j⟫ = 0
        simp only [W, inner_sub_left, real_inner_smul_left, h₁, h₃, mul_zero, sub_zero]
      · change ⟪W i, W j⟫ = 0
        simp only [W, inner_sub_right, inner_sub_left, real_inner_smul_right, real_inner_smul_left,
          h₁, h₂, h₃, h₄, mul_zero, sub_zero]
  have hlin := linearIndependent_of_ne_zero_of_inner_eq_zero (𝕜 := ℝ) hD hDD
  have hdim := hlin.fintype_card_le_finrank
  have hfin : Module.finrank ℝ Point = 6 := by
    rw [(WithLp.linearEquiv 2 ℝ (Fin 6 → ℝ)).finrank_eq, Module.finrank_pi, Fintype.card_fin]
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, hfin] at hdim
  omega

private abbrev Pair4 := {ij : Fin 4 × Fin 4 // ij.1 < ij.2}

private theorem pair4_card : Fintype.card Pair4 = 6 := by decide

private theorem count_witness_functions {α : Type*} [Fintype α] (p : Pair4 → α → Prop) :
    count (fun f : Pair4 → α ↦ ∀ i, p i (f i)) = ∏ i, count (p i) := by
  classical
  let e : {f : Pair4 → α // ∀ i, p i (f i)} ≃ ((i : Pair4) → {a // p i a}) :=
    { toFun := fun f i ↦ ⟨f.val i, f.2 i⟩
      invFun := fun f ↦ ⟨fun i ↦ (f i).val, fun i ↦ (f i).2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  rw [count_eq_card, Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_pi]
  apply prod_congr rfl
  intro i _
  rw [count_eq_card, Nat.card_eq_fintype_card]

private def RichGraph {α : Type*} [Fintype α] (v : α → Point) (δ : ℝ) : SimpleGraph α where
  Adj a b := a ≠ b ∧ δ * Fintype.card α ≤ (count (fun x ↦ Witness (v a) (v b) (v x)) : ℝ)
  symm := ⟨fun a b h ↦ ⟨h.1.symm, h.2.trans (by
    exact_mod_cast (count_mono (fun _ hx ↦ Witness.symm hx) :
      count (fun x ↦ Witness (v a) (v b) (v x)) ≤ count (fun x ↦ Witness (v b) (v a) (v x))))⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

private theorem count_zero_of_not {α : Type*} [Fintype α] {p : α → Prop} (h : ∀ a, ¬p a) :
    count p = 0 := by
  classical
  simp [count, h]

private theorem count_or_le {α : Type*} [Fintype α] (p q : α → Prop) :
    count (fun a ↦ p a ∨ q a) ≤ count p + count q := by
  classical
  rw [count_eq_card, count_eq_card, count_eq_card, ← Nat.card_sum]
  let f : {a // p a ∨ q a} → {a // p a} ⊕ {a // q a} := fun a ↦
    if hp : p a.val then Sum.inl ⟨a.val, hp⟩ else Sum.inr ⟨a.val, a.2.resolve_left hp⟩
  refine Nat.card_le_card_of_injective f fun a b hab ↦ Subtype.ext ?_
  have hval (x : {z // p z ∨ q z}) : Sum.elim Subtype.val Subtype.val (f x) = x.val := by
    unfold f
    split <;> rfl
  simpa only [hval] using congrArg (Sum.elim Subtype.val Subtype.val) hab

private theorem witness_swap_last {E : Type*} [MetricSpace E] {a b x : E} (h : Witness a b x) :
    Witness a x b := by
  rcases h with ⟨hn, ha, hb, hac, hbc⟩
  exact ⟨ha, hn, hb.symm, hac.symm, hac.symm.trans (hbc.trans (dist_comm b x))⟩

private theorem count_witness_le_rich {α : Type*} [Fintype α] (v : α → Point) {δ : ℝ} (hδ : 0 < δ) :
    (count (fun x : α × α × α ↦ Witness (v x.1) (v x.2.1) (v x.2.2)) : ℝ) ≤
      (count (CliqueMap (k := 3) (RichGraph v δ)) : ℝ) + 3 * δ * (Fintype.card α : ℝ) ^ 3 := by
  classical
  let G := RichGraph v δ
  let R : α × α × α → Prop := fun x ↦ Witness (v x.1) (v x.2.1) (v x.2.2)
  let lacks₁ : α × α × α → Prop := fun x ↦ R x ∧ ¬G.Adj x.1 x.2.1
  let lacks₂ : α × α × α → Prop := fun x ↦ R x ∧ ¬G.Adj x.1 x.2.2
  let lacks₃ : α × α × α → Prop := fun x ↦ R x ∧ ¬G.Adj x.2.1 x.2.2
  have h₁ : (count lacks₁ : ℝ) ≤ δ * (Fintype.card α : ℝ) ^ 3 := by
    let p (ab : α × α) (c : α) := Witness (v ab.1) (v ab.2) (v c) ∧ ¬G.Adj ab.1 ab.2
    have he := count_congr (Equiv.prodAssoc α α α).symm (p := lacks₁)
      (q := fun abc ↦ p abc.1 abc.2) (fun _ ↦ Iff.rfl)
    rw [he, count_fiber p, Nat.cast_sum]
    have hb (ab : α × α) : (count (p ab) : ℝ) ≤ δ * Fintype.card α := by
      by_cases ha : G.Adj ab.1 ab.2
      · rw [count_zero_of_not (fun _ h ↦ h.2 ha), Nat.cast_zero]
        positivity
      · by_cases hne : ab.1 = ab.2
        · rw [count_zero_of_not (fun _ h ↦ h.1.1 (congrArg v hne)), Nat.cast_zero]
          positivity
        · have hr : (count (fun c ↦ Witness (v ab.1) (v ab.2) (v c)) : ℝ) ≤
              δ * Fintype.card α := (lt_of_not_ge (fun hh ↦ ha ⟨hne, hh⟩)).le
          apply le_trans _ hr
          exact_mod_cast (count_mono (fun _ h ↦ h.1) : count (p ab) ≤ _)
    calc
      _ ≤ ∑ _ : α × α, δ * Fintype.card α := sum_le_sum (fun a _ ↦ hb a)
      _ = _ := by simp [nsmul_eq_mul]; ring
  have h₂ : count lacks₂ = count lacks₁ := by
    apply count_congr (Equiv.prodCongr (Equiv.refl α) (Equiv.prodComm α α))
    intro a
    exact ⟨fun h ↦ ⟨witness_swap_last h.1, h.2⟩, fun h ↦ ⟨witness_swap_last h.1, h.2⟩⟩
  have h₃ : count lacks₃ = count lacks₁ := by
    apply count_congr ((Equiv.prodComm α (α × α)).trans (Equiv.prodAssoc α α α))
    intro a
    -- The cyclic permutation `(a,b,c) ↦ (b,c,a)`.
    change lacks₃ a ↔ lacks₁ (a.2.1, a.2.2, a.1)
    exact ⟨fun h ↦ ⟨witness_swap_last h.1.symm, h.2⟩,
      fun h ↦ ⟨(witness_swap_last h.1).symm, h.2⟩⟩
  have hc : count R ≤ (count (fun x : α × α × α ↦ Triangle G x.1 x.2.1 x.2.2) +
      (count lacks₁ + (count lacks₂ + count lacks₃))) := by
    apply (count_mono (q := fun x ↦ Triangle G x.1 x.2.1 x.2.2 ∨
      (lacks₁ x ∨ lacks₂ x ∨ lacks₃ x)) ?_).trans
    · exact (count_or_le _ _).trans (Nat.add_le_add_left
        ((count_or_le _ _).trans (Nat.add_le_add_left (count_or_le _ _) _)) _)
    · intro x hx
      by_cases ha : G.Adj x.1 x.2.1
      · by_cases hb : G.Adj x.1 x.2.2
        · by_cases hc : G.Adj x.2.1 x.2.2
          · exact Or.inl ⟨ha, hb, hc⟩
          · exact Or.inr (Or.inr (Or.inr ⟨hx, hc⟩))
        · exact Or.inr (Or.inr (Or.inl ⟨hx, hb⟩))
      · exact Or.inr (Or.inl ⟨hx, ha⟩)
  rw [h₂, h₃, ← count_cliqueTriples] at hc
  have hc' : (count R : ℝ) ≤ (count (CliqueMap (k := 3) G) : ℝ) + 3 * count lacks₁ := by
    exact_mod_cast (show count R ≤ count (CliqueMap (k := 3) G) + 3 * count lacks₁ by omega)
  linarith only [hc', h₁]

/-- Fix all six witnesses at once by averaging over their assignments. -/
private theorem fix_witnesses {α : Type*} [Fintype α] [Nonempty α] (v : α → Point)
    {δ c : ℝ} (hδ : 0 < δ)
    (hK : c * (Fintype.card α : ℝ) ^ 4 ≤ (count (CliqueMap (k := 4) (RichGraph v δ)) : ℝ)) :
    ∃ w : Pair4 → α, c * δ ^ 6 * (Fintype.card α : ℝ) ^ 4 ≤
      (count (fun f : Fin 4 → α ↦ ∀ ij : Pair4, Witness (v (f ij.val.1)) (v (f ij.val.2))
        (v (w ij))) : ℝ) := by
  classical
  let G := RichGraph v δ
  let n : ℝ := Fintype.card α
  let p (f : Fin 4 → α) (w : Pair4 → α) : Prop := ∀ ij : Pair4,
    Witness (v (f ij.val.1)) (v (f ij.val.2)) (v (w ij))
  have hrow (f : Fin 4 → α) (hf : CliqueMap G f) : (δ * n) ^ 6 ≤ (count (p f) : ℝ) := by
    unfold p
    rw [count_witness_functions (fun ij x ↦ Witness (v (f ij.val.1)) (v (f ij.val.2)) (v x)),
      Nat.cast_prod]
    calc
      (δ * n) ^ 6 = ∏ _ : Pair4, δ * n := by rw [prod_const, card_univ, pair4_card]
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ ↦ le_of_lt (mul_pos hδ (by positivity)))
        (fun ij _ ↦ (hf (ne_of_lt ij.2)).2)
  have hsum : (count (CliqueMap (k := 4) G) : ℝ) * (δ * n) ^ 6 ≤
      (count (fun fw : (Fin 4 → α) × (Pair4 → α) ↦ p fw.1 fw.2) : ℝ) := by
    rw [count_fiber p, Nat.cast_sum]
    calc
      _ = ∑ _ ∈ univ.filter (CliqueMap (k := 4) G), (δ * n) ^ 6 := by
        simp only [sum_const, nsmul_eq_mul]
        congr 1
      _ ≤ ∑ f ∈ univ.filter (CliqueMap (k := 4) G), (count (p f) : ℝ) :=
        sum_le_sum (fun f hf ↦ hrow f (mem_filter.mp hf).2)
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ ↦ by positivity)
  have hmain : c * δ ^ 6 * n ^ 4 * Fintype.card (Pair4 → α) ≤
      (count (fun wf : (Pair4 → α) × (Fin 4 → α) ↦ p wf.2 wf.1) : ℝ) := by
    rw [← count_congr (Equiv.prodComm (Fin 4 → α) (Pair4 → α))
      (p := fun fw ↦ p fw.1 fw.2) (q := fun wf ↦ p wf.2 wf.1) (fun _ ↦ Iff.rfl)]
    rw [Fintype.card_fun, pair4_card, Nat.cast_pow]
    calc
      _ = c * n ^ 4 * (δ * n) ^ 6 := by dsimp [n]; ring
      _ ≤ _ := (mul_le_mul_of_nonneg_right hK (by positivity)).trans hsum
  exact exists_large_fiber (fun w f ↦ p f w) _ hmain

private theorem witness_boxes_impossible {α : Type*} [Fintype α] (v : α → Point)
    (hv : Function.Injective v) (w : Pair4 → α) (A : Fin 4 → Slices α 3)
    (hA : ∀ f : Fin 4 → α, (∀ i, f i ∈ (A i).val) → ∀ ij : Pair4,
      Witness (v (f ij.val.1)) (v (f ij.val.2)) (v (w ij))) : False := by
  classical
  let e (i : Fin 4) : Fin 3 ≃ (A i).val := (equivFinOfCardEq (mem_powersetCard.mp (A i).2).2).symm
  let a (i : Fin 4) (p : Fin 3) : Point := v (e i p).val
  apply no_witness_box a (fun i _ _ h ↦ (e i).injective (Subtype.ext (hv h)))
  have hlt (i j : Fin 4) (hij : i < j) : ∃ x, ∀ p q, Witness (a i p) (a j q) x := by
    refine ⟨v (w ⟨(i, j), hij⟩), fun p q ↦ ?_⟩
    let f : Fin 4 → α := Function.update (Function.update (fun k ↦ (e k 0).val) i
      (e i p).val) j (e j q).val
    have hf (k : Fin 4) : f k ∈ (A k).val := by
      by_cases hkj : k = j
      · subst k
        simp [f]
      · by_cases hki : k = i
        · subst k
          simp [f, Function.update_of_ne hkj]
        · simp [f, Function.update_of_ne hkj, Function.update_of_ne hki]
    have h := hA f hf ⟨(i, j), hij⟩
    simpa [a, f, Function.update_of_ne (ne_of_lt hij)] using h
  intro i j hij
  rcases lt_or_gt_of_ne hij with hl | hl
  · exact hlt i j hl
  · obtain ⟨x, hx⟩ := hlt j i hl
    exact ⟨x, fun p q ↦ (hx q p).symm⟩

/-- The upper bound on ordered equilateral triples of any positive side length. -/
private theorem witness_density (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ {α : Type} [Fintype α], N ≤ Fintype.card α →
      ∀ v : α → Point, Function.Injective v →
        (count (fun x : α × α × α ↦ Witness (v x.1) (v x.2.1) (v x.2.2)) : ℝ) ≤
          (2 / 9 + ε) * (Fintype.card α : ℝ) ^ 3 := by
  let δ := ε / 6
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨c, hc, hs⟩ := triangle_supersaturation (ε / 2) (by positivity)
  obtain ⟨N, hN⟩ := dense_box 4 (c * δ ^ 6) (by positivity)
  refine ⟨max N 1, ?_⟩
  intro α _ hn v hv
  let : Nonempty α := Fintype.card_pos_iff.mp (lt_of_lt_of_le Nat.zero_lt_one
    ((le_max_right ..).trans hn))
  by_contra! ht
  have hR := count_witness_le_rich v hδ
  have hK : (2 / 9 + ε / 2) * (Fintype.card α : ℝ) ^ 3 ≤
      (count (CliqueMap (k := 3) (RichGraph v δ)) : ℝ) := by
    dsimp [δ] at hR
    linarith only [hR, ht]
  obtain ⟨w, hw⟩ := fix_witnesses v hδ (hs _ hK)
  obtain ⟨A, hA⟩ := hN ((le_max_left ..).trans hn) _ hw
  exact witness_boxes_impossible v hv w A hA

private theorem witness_triangle_iff {a b c : Point} :
    Witness a b c ↔ IsAnySizeEquilateralTriangle ({a, b, c} : Finset Point) := by
  classical
  constructor
  · rintro ⟨hab, hac, hbc, h₁, h₂⟩
    refine ⟨dist a b, dist_pos.mpr hab, ?_, ?_⟩
    · simp [hab, hac, hbc]
    · intro x hx y hy hxy
      simp only [mem_insert, mem_singleton] at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
      · exact (hxy rfl).elim
      · rfl
      · exact h₁.symm
      · rw [dist_comm]
      · exact (hxy rfl).elim
      · exact h₂.symm
      · rw [dist_comm, ← h₁]
      · rw [dist_comm, ← h₂]
      · exact (hxy rfl).elim
  · rintro ⟨s, _, hc, h⟩
    have hab : a ≠ b := by
      rintro rfl
      by_cases he : a = c <;> simp [he] at hc
    have hac : a ≠ c := by
      rintro rfl
      simp [hab, hab.symm] at hc
    have hbc : b ≠ c := by
      rintro rfl
      simp [hab] at hc
    have h₁ := h a (by simp) b (by simp) hab
    have h₂ := h a (by simp) c (by simp) hac
    have h₃ := h b (by simp) c (by simp) hbc
    exact ⟨hab, hac, hbc, h₁.trans h₂.symm, h₁.trans h₃.symm⟩

/-- Orient each three-element triangle by the six permutations of a chosen enumeration. -/
private theorem count_equilateral_orderings (P : Finset Point) :
    6 * anySizeEquilateralTriangleCount 6 P ≤
      count (fun x : P × P × P ↦ Witness x.1.val x.2.1.val x.2.2.val) := by
  classical
  let S := (P.powersetCard 3).filter IsAnySizeEquilateralTriangle
  let e (s : S) : Fin 3 ≃ s.val :=
    (equivFinOfCardEq (mem_powersetCard.mp (mem_filter.mp s.2).1).2).symm
  let F (sp : S × Equiv.Perm (Fin 3)) (i : Fin 3) : P :=
    ⟨(e sp.1 (sp.2 i)).val, (mem_powersetCard.mp (mem_filter.mp sp.1.2).1).1 (e sp.1 (sp.2 i)).2⟩
  have h_image (sp : S × Equiv.Perm (Fin 3)) :
      ({(F sp 0).val, (F sp 1).val, (F sp 2).val} : Finset Point) = sp.1.val := by
    ext x
    constructor
    · simp only [mem_insert, mem_singleton]
      rintro (rfl | rfl | rfl)
      · exact (e sp.1 (sp.2 0)).2
      · exact (e sp.1 (sp.2 1)).2
      · exact (e sp.1 (sp.2 2)).2
    · intro hx
      obtain ⟨i, hi⟩ := (sp.2.trans (e sp.1)).surjective ⟨x, hx⟩
      have he : (F sp i).val = x := congrArg Subtype.val hi
      fin_cases i <;> simp [← he]
  let E : S × Equiv.Perm (Fin 3) →
      {x : P × P × P // Witness x.1.val x.2.1.val x.2.2.val} := fun sp ↦
    ⟨(F sp 0, F sp 1, F sp 2), witness_triangle_iff.mpr (by
      rw [h_image sp]
      exact (mem_filter.mp sp.1.2).2)⟩
  have hE : Function.Injective E := by
    intro sp tp h
    have hfun : F sp = F tp := by
      funext i
      have he := congrArg Subtype.val h
      fin_cases i
      · exact congrArg Prod.fst he
      · exact congrArg (fun x ↦ x.2.1) he
      · exact congrArg (fun x ↦ x.2.2) he
    have hst : sp.1 = tp.1 := Subtype.ext (by
      rw [← h_image sp, ← h_image tp, hfun])
    refine Prod.ext hst (Equiv.ext fun i ↦ ?_)
    apply (e tp.1).injective
    apply Subtype.ext
    have hi := congrArg (fun g : Fin 3 → P ↦ (g i).val) hfun
    change (e sp.1 (sp.2 i)).val = (e tp.1 (tp.2 i)).val at hi
    rwa [hst] at hi
  have hcard := Nat.card_le_card_of_injective E hE
  rw [Nat.card_eq_fintype_card (α := S × _), Fintype.card_prod, Fintype.card_coe,
    Fintype.card_perm, Fintype.card_fin, ← count_eq_card] at hcard
  norm_num [Nat.factorial] at hcard
  simpa [S, anySizeEquilateralTriangleCount, Nat.mul_comm] using hcard

private theorem pointset_upper (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ P : Finset Point, N ≤ P.card →
      (anySizeEquilateralTriangleCount 6 P : ℝ) ≤ (1 / 27 + ε) * (P.card : ℝ) ^ 3 := by
  obtain ⟨N, hN⟩ := witness_density (6 * ε) (by positivity)
  refine ⟨N, fun P hP ↦ ?_⟩
  have h₁ : 6 * (anySizeEquilateralTriangleCount 6 P : ℝ) ≤
      (count (fun x : P × P × P ↦ Witness x.1.val x.2.1.val x.2.2.val) : ℝ) := by
    exact_mod_cast count_equilateral_orderings P
  have h₂ := hN (α := P) (by simpa using hP) Subtype.val Subtype.val_injective
  rw [Fintype.card_coe] at h₂
  linarith only [h₁, h₂]

private theorem anySize_le_choose {d : ℕ} (P : Finset (EuclideanSpace ℝ (Fin d))) :
    anySizeEquilateralTriangleCount d P ≤ P.card.choose 3 := by
  classical
  rw [← card_powersetCard]
  exact card_filter_le _ _

private theorem unit_le_anySize {d : ℕ} (P : Finset (EuclideanSpace ℝ (Fin d))) :
    unitEquilateralTriangleCount d P ≤ anySizeEquilateralTriangleCount d P := by
  classical
  apply card_le_card
  intro T hT
  obtain ⟨hsub, hunit⟩ := mem_filter.mp hT
  exact mem_filter.mpr ⟨hsub, 1, zero_lt_one, hunit⟩

private theorem bounded_anySize (d n : ℕ) :
    BddAbove {m : ℕ | ∃ P : Finset (EuclideanSpace ℝ (Fin d)),
      P.card = n ∧ anySizeEquilateralTriangleCount d P = m} := by
  refine ⟨n.choose 3, ?_⟩
  rintro m ⟨P, hP, rfl⟩
  simpa only [hP] using anySize_le_choose P

private theorem TUnit_le_TAnySize (d n : ℕ) : TUnit d n ≤ TAnySize d n := by
  let S : Set ℕ := {m | ∃ P : Finset (EuclideanSpace ℝ (Fin d)),
    P.card = n ∧ unitEquilateralTriangleCount d P = m}
  change sSup S ≤ _
  by_cases hS : S.Nonempty
  · apply csSup_le hS
    rintro m ⟨P, hP, rfl⟩
    exact (unit_le_anySize P).trans (le_csSup (bounded_anySize d n) ⟨P, hP, rfl⟩)
  · rw [Set.not_nonempty_iff_eq_empty.mp hS, csSup_empty]
    exact bot_le

private theorem TAnySize_upper (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (TAnySize 6 n : ℝ) ≤ (1 / 27 + ε) * (n : ℝ) ^ 3 := by
  obtain ⟨N, hN⟩ := pointset_upper ε hε
  filter_upwards [eventually_ge_atTop N] with n hn
  let S : Set ℕ := {m | ∃ P : Finset Point, P.card = n ∧ anySizeEquilateralTriangleCount 6 P = m}
  by_cases hS : S.Nonempty
  · obtain ⟨P, hp, he⟩ := Nat.sSup_mem hS (bounded_anySize 6 n)
    rw [show TAnySize 6 n = anySizeEquilateralTriangleCount 6 P from he.symm, ← hp]
    exact hN P (hp ▸ hn)
  · have hz : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    rw [show TAnySize 6 n = sSup S from rfl, hz, csSup_empty, Nat.bot_eq_zero]
    simp only [Nat.cast_zero]
    positivity

/-- The first coordinate of the chosen points on a unit circle; it is
positive and strictly decreases as the index increases. -/
private noncomputable def circleX (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

private theorem circleX_pos (n : ℕ) : 0 < circleX n := by
  unfold circleX
  positivity

private theorem circleX_le_one (n : ℕ) : circleX n ≤ 1 := by
  unfold circleX
  apply div_le_one_of_le₀
  · exact le_add_of_nonneg_left (Nat.cast_nonneg n)
  · positivity

private noncomputable def circleY (n : ℕ) : ℝ := √(1 - circleX n ^ 2)

private theorem circle_norm_sq (n : ℕ) : circleX n ^ 2 + circleY n ^ 2 = 1 := by
  have hh : circleX n ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (circleX_pos n).le (circleX_le_one n) _
  rw [circleY, Real.sq_sqrt (by linarith only [hh])]
  ring

private abbrev circleIndex : Fin 3 × Fin 2 ≃ Fin 6 := finProdFinEquiv

/-- Put the `n`th point of each unit circle in its own pair of coordinates. -/
private noncomputable def circlePoint (i : Fin 3) (n : ℕ) : Point :=
  WithLp.toLp 2 (fun k ↦
    if (circleIndex.symm k).1 = i then
      if (circleIndex.symm k).2 = 0 then circleX n else circleY n
    else 0)

private theorem circlePoint_coord (i : Fin 3) (n : ℕ) (k : Fin 3 × Fin 2) :
    (circlePoint i n).ofLp (circleIndex k) =
      if k.1 = i then if k.2 = 0 then circleX n else circleY n else 0 := by
  simp [circlePoint]

private theorem circlePoint_injective :
    Function.Injective (fun p : Fin 3 × ℕ ↦ circlePoint p.1 p.2) := by
  rintro ⟨i, n⟩ ⟨j, m⟩ h
  have hc := congrArg (fun a : Point ↦ a.ofLp (circleIndex (i, 0))) h
  change (circlePoint i n).ofLp (circleIndex (i, 0)) =
    (circlePoint j m).ofLp (circleIndex (i, 0)) at hc
  by_cases hij : i = j
  · subst j
    simp only [circlePoint_coord, ite_true, circleX, one_div, inv_inj] at hc
    have hn : (n : ℝ) = m := add_right_cancel hc
    exact Prod.ext rfl (by exact_mod_cast hn)
  · have hz : circleX n = 0 := by simpa [circlePoint_coord, hij] using hc
    exact ((circleX_pos n).ne' hz).elim

private theorem circlePoint_eq_iff {i j : Fin 3} {n m : ℕ} :
    circlePoint i n = circlePoint j m ↔ i = j ∧ n = m := by
  refine ⟨fun h ↦ Prod.mk.inj (circlePoint_injective h), ?_⟩
  rintro ⟨rfl, rfl⟩
  rfl

private theorem circlePoint_dist {i j : Fin 3} (hij : i ≠ j) (n m : ℕ) :
    dist (circlePoint i n) (circlePoint j m) = √2 := by
  rw [EuclideanSpace.dist_eq]
  congr 1
  rw [← circleIndex.sum_comp]
  simp only [circlePoint_coord, Fintype.sum_prod_type, Fin.sum_univ_two, Real.dist_eq, sq_abs]
  have hterm (k : Fin 3) :
      ((if k = i then circleX n else 0) - (if k = j then circleX m else 0)) ^ 2 +
        ((if k = i then circleY n else 0) - (if k = j then circleY m else 0)) ^ 2 =
          (if k = i then (1 : ℝ) else 0) + (if k = j then 1 else 0) := by
    by_cases hki : k = i
    · subst k
      simp [hij, circle_norm_sq]
    · by_cases hkj : k = j
      · subst k
        simp [hij.symm, circle_norm_sq]
      · simp [hki, hkj]
  simp only [ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false]
  simp_rw [hterm]
  norm_num [sum_add_distrib]

/-- Choose `⌊n/3⌋` points in each circle, then fill to exactly `n` points.
Every transversal of the first three sets is an equilateral triangle. -/
private theorem pointset_lower (n : ℕ) :
    ∃ P : Finset Point, P.card = n ∧ (n / 3) ^ 3 ≤ anySizeEquilateralTriangleCount 6 P := by
  classical
  let m := n / 3
  let incl (a : Fin 3 × Fin m) : Fin 3 × Fin n := (a.1, Fin.castLE (Nat.div_le_self ..) a.2)
  have hinc : Function.Injective incl := fun a b eq ↦
    Prod.ext (congrArg (fun x : Fin 3 × Fin n ↦ x.1) eq) (Fin.ext (congrArg (fun x ↦ x.2.val) eq))
  let A : Finset (Fin 3 × Fin n) := univ.image incl
  have hA : A.card ≤ n := by
    rw [show A.card = 3 * m by simp [A, card_image_of_injective _ hinc]]
    dsimp [m]
    omega
  obtain ⟨B, hAB, hB⟩ := exists_superset_card_eq hA (by simp; omega)
  let F (a : Fin 3 × Fin n) : Point := circlePoint a.1 a.2.val
  let P := B.image F
  have hF : Function.Injective F := fun a b eq ↦
    Prod.ext (circlePoint_eq_iff.mp eq).1 (Fin.ext (circlePoint_eq_iff.mp eq).2)
  refine ⟨P, by rw [card_image_of_injective _ hF, hB], ?_⟩
  have hP (i : Fin 3) (x : Fin m) : circlePoint i x.val ∈ P :=
    mem_image.mpr ⟨incl (i, x), hAB (mem_image_of_mem incl (mem_univ _)), rfl⟩
  let τ (a : Fin m × Fin m × Fin m) : Finset Point :=
    {circlePoint 0 a.1.val, circlePoint 1 a.2.1.val, circlePoint 2 a.2.2.val}
  have hτ : Function.Injective τ := by
    intro a b hab
    have h₀ : circlePoint 0 a.1.val ∈ τ b := hab ▸ (by simp [τ])
    have h₁ : circlePoint 1 a.2.1.val ∈ τ b := hab ▸ (by simp [τ])
    have h₂ : circlePoint 2 a.2.2.val ∈ τ b := hab ▸ (by simp [τ])
    have e₀ : a.1.val = b.1.val := by simpa [τ, circlePoint_eq_iff] using h₀
    have e₁ : a.2.1.val = b.2.1.val := by simpa [τ, circlePoint_eq_iff] using h₁
    have e₂ : a.2.2.val = b.2.2.val := by simpa [τ, circlePoint_eq_iff] using h₂
    exact Prod.ext (Fin.ext e₀) (Prod.ext (Fin.ext e₁) (Fin.ext e₂))
  have hW (a : Fin m × Fin m × Fin m) :
      Witness (circlePoint 0 a.1.val) (circlePoint 1 a.2.1.val) (circlePoint 2 a.2.2.val) := by
    have hne (i j : Fin 3) (h : i ≠ j) (x y : ℕ) : circlePoint i x ≠ circlePoint j y :=
      fun e ↦ h (circlePoint_eq_iff.mp e).1
    refine ⟨hne _ _ (by decide) _ _, hne _ _ (by decide) _ _, hne _ _ (by decide) _ _, ?_, ?_⟩
    · exact (circlePoint_dist (by decide) _ _).trans (circlePoint_dist (by decide) _ _).symm
    · exact (circlePoint_dist (by decide) _ _).trans (circlePoint_dist (by decide) _ _).symm
  have hmem (a : Fin m × Fin m × Fin m) :
      τ a ∈ (P.powersetCard 3).filter IsAnySizeEquilateralTriangle := by
    have hw := witness_triangle_iff.mp (hW a)
    refine mem_filter.mpr ⟨mem_powersetCard.mpr ⟨?_, ?_⟩, hw⟩
    · intro x hx
      simp only [τ, mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> exact hP _ _
    · obtain ⟨_, _, hc, _⟩ := hw
      exact hc
  have hcount := card_le_card_of_injOn (s := (univ : Finset (Fin m × Fin m × Fin m))) τ
    (fun a _ ↦ hmem a) hτ.injOn
  simpa [m, anySizeEquilateralTriangleCount, pow_succ, Nat.mul_comm, Nat.mul_left_comm] using hcount

private theorem TAnySize_lower (n : ℕ) : (n / 3) ^ 3 ≤ TAnySize 6 n := by
  obtain ⟨P, hP, h⟩ := pointset_lower n
  exact h.trans (le_csSup (bounded_anySize 6 n) ⟨P, hP, rfl⟩)

open scoped Topology

private theorem floor_third_tendsto : Tendsto (fun n : ℕ ↦ ((n / 3 : ℕ) : ℝ) / n) atTop
    (𝓝 (1 / 3 : ℝ)) := by
  have hinv : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hlo : Tendsto (fun n : ℕ ↦ (1 / 3 : ℝ) - (n : ℝ)⁻¹) atTop (𝓝 (1 / 3 : ℝ)) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hinv
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hpos : 0 < (n : ℝ) := by exact_mod_cast hn
    have hm : (n : ℝ) ≤ 3 * ((n / 3 : ℕ) : ℝ) + 3 := by
      exact_mod_cast (show n ≤ 3 * (n / 3) + 3 by omega)
    apply (le_div_iff₀ hpos).mpr
    rw [sub_mul, inv_mul_cancel₀ hpos.ne']
    linarith only [hm]
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hpos : 0 < (n : ℝ) := by exact_mod_cast hn
    have hm : 3 * ((n / 3 : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (show 3 * (n / 3) ≤ n by omega)
    apply (div_le_iff₀ hpos).mpr
    linarith only [hm]

private theorem TAnySize_ratio :
    Tendsto (fun n : ℕ ↦ (TAnySize 6 n : ℝ) / (n : ℝ) ^ 3) atTop (𝓝 (1 / 27 : ℝ)) := by
  have hlo : Tendsto (fun n : ℕ ↦ (((n / 3 : ℕ) : ℝ) / n) ^ 3) atTop (𝓝 (1 / 27 : ℝ)) := by
    convert floor_third_tendsto.pow 3 using 1
    norm_num
  rw [tendsto_order]
  constructor
  · intro a ha
    have h := (tendsto_order.mp hlo).1 a ha
    filter_upwards [h, eventually_gt_atTop (0 : ℕ)] with n hn hn₀
    apply hn.trans_le
    rw [div_pow]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast TAnySize_lower n
  · intro a ha
    have hε : 0 < (a - 1 / 27) / 2 := by linarith
    filter_upwards [TAnySize_upper ((a - 1 / 27) / 2) hε, eventually_gt_atTop (0 : ℕ)] with n hn hn₀
    have hpos : 0 < (n : ℝ) ^ 3 := by positivity
    exact ((div_le_iff₀ hpos).mpr hn).trans_lt (by linarith)

/-- **Erdős Problem 755 holds (Clemen–Dumitrescu–Liu).** Let $T_1(n)$ be the largest number of unit
equilateral triangles spanned by a set of $n$ points in $\mathbb{R}^6$, and let $T(n)$ be the
largest number of equilateral triangles of positive side length spanned by a set of $n$ points in
$\mathbb{R}^6$; a triangle spanned by a set is a three-element subset of it whose points are
pairwise at the same distance. Then there is a function $o : \mathbb{N} \to \mathbb{R}$ with
$o(n) \to 0$ as $n \to \infty$ such that $T_1(n) \le (1/27 + o(n))\, n^3$ for all sufficiently
large $n$, and $T(n)$ is asymptotically equivalent to $n^3/27$ as $n \to \infty$.

Source: Felix Christian Clemen, Adrian Dumitrescu, and Dingyuan Liu, *The number of regular
simplices in higher dimensions*, Theorem 2, [arXiv:2507.19841](https://arxiv.org/abs/2507.19841).
-/
public theorem conjecture_holds : conjecture := by
  constructor
  · refine ⟨fun n ↦ (TAnySize 6 n : ℝ) / (n : ℝ) ^ 3 - 1 / 27, ?_, ?_⟩
    · apply (Asymptotics.isLittleO_one_iff ℝ).mpr
      have hconst : Tendsto (fun _ : ℕ ↦ (1 / 27 : ℝ)) atTop (𝓝 (1 / 27 : ℝ)) :=
        tendsto_const_nhds
      simpa only [sub_self] using TAnySize_ratio.sub hconst
    · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      have hpos : 0 < (n : ℝ) ^ 3 := by positivity
      have he : (1 / 27 + ((TAnySize 6 n : ℝ) / (n : ℝ) ^ 3 - 1 / 27)) * (n : ℝ) ^ 3 =
          (TAnySize 6 n : ℝ) := by
        rw [show (1 / 27 : ℝ) + ((TAnySize 6 n : ℝ) / (n : ℝ) ^ 3 - 1 / 27) =
          (TAnySize 6 n : ℝ) / (n : ℝ) ^ 3 by ring, div_mul_cancel₀ _ hpos.ne']
      rw [he]
      exact_mod_cast TUnit_le_TAnySize 6 n
  · apply (Asymptotics.isEquivalent_iff_tendsto_one ?_).mpr
    · have ht := TAnySize_ratio.div_const (1 / 27 : ℝ)
      norm_num at ht
      refine ht.congr' (Eventually.of_forall fun n ↦ ?_)
      simp only [Pi.div_apply, div_div, mul_comm ((n : ℝ) ^ 3)]
    · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      positivity

end MathlibExt.Geometry.ErdosProblem755Wanted
