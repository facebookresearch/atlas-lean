/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`FormalConjectures/ErdosProblems/755.lean` (Formal Conjectures):
Copyright 2026 The Formal Conjectures Authors.
Authors: The Formal Conjectures Authors.
The adapted portions are the equilateral-triangle definitions, the conjecture,
and the statement of its resolution.

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

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Order.Lattice.Nat

import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.Tactic.FinCases

/-!
# Erdős Problem 755

We prove the asymptotic upper bound for unit equilateral triangles and the asymptotic formula
for equilateral triangles of any size in six-dimensional Euclidean space.

Source record `FC-ErdosProblem755`, ported from FormalConjectures
`ErdosProblems/755.lean` and checked against erdosproblems.com/755.
The equilateral-triangle counting API is inlined from FC
(`IsEquilateralTriangle`, `IsUnitEquilateralTriangle`,
`IsAnySizeEquilateralTriangle`, `unitEquilateralTriangleCount`,
`anySizeEquilateralTriangleCount`, `TUnit`, `TAnySize`; absent from
pinned Mathlib). `test` lemmas are not ported. The upstream
`answer(True)` is dropped. Status: resolved true by [CDL25b]. An external Lean proof is linked in
the registry.

The upper bound uses the forbidden configuration from Clemen, Dumitrescu, and Liu.
Finite sampling reduces the counting estimate to Turán's theorem for simple graphs.
The lower bound uses the Lenz construction on three orthogonal circles.
-/

namespace MathlibExt.Geometry.ErdosProblem755Wanted

open Filter
open scoped Asymptotics EuclideanGeometry Finset

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
open scoped BigOperators NNReal Real Topology

/-! ## Finite sampling and repeated slices -/

open scoped Classical in
private noncomputable def indicator (p : Prop) : ℝ := if p then 1 else 0

private noncomputable def density {α : Type*} [Fintype α] (p : α → Prop) : ℝ :=
  𝔼 a, indicator (p a)

private theorem density_nonneg {α : Type*} [Fintype α] (p : α → Prop) :
    0 ≤ density p :=
  Finset.expect_nonneg fun a _ => by simp only [indicator]; split <;> norm_num

private theorem density_le_one {α : Type*} [Fintype α] [Nonempty α] (p : α → Prop) :
    density p ≤ 1 :=
  Finset.expect_le univ_nonempty fun a _ => by simp only [indicator]; split <;> norm_num

private theorem density_or_le {α : Type*} [Fintype α] (p q : α → Prop) :
    density (fun a => p a ∨ q a) ≤ density p + density q := by
  rw [density, density, density, ← Finset.expect_add_distrib]
  apply Finset.expect_le_expect
  intro a _
  by_cases hp : p a <;> by_cases hq : q a <;> norm_num [indicator, hp, hq]

private theorem density_eq_of_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (p : β → Prop) : density (p ∘ e) = density p := by
  apply Fintype.expect_equiv e
  intro a
  rfl

private theorem expect_pow_three_le {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    (𝔼 a, f a) ^ 3 ≤ 𝔼 a, f a ^ 3 := by
  have hc : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h := (convexOn_pow (𝕜 := ℝ) 3).map_sum_le
    (t := (univ : Finset α)) (w := fun _ => (Fintype.card α : ℝ)⁻¹)
    (p := f) (by intro a ha; positivity)
    (by simp [hc])
    (fun a _ => hf a)
  simpa only [smul_eq_mul, ← Finset.mul_sum, Fintype.expect_eq_sum_div_card,
    div_eq_inv_mul] using h

private theorem density_prod {α β : Type*} [Fintype α] [Fintype β]
    (p : α → β → Prop) :
    density (fun ab : α × β => p ab.1 ab.2) = 𝔼 a, density (p a) := by
  unfold density
  rw [← Finset.univ_product_univ]
  exact Finset.expect_product' _ _ fun a b => indicator (p a b)

open scoped Classical in
private theorem density_prod_separable {α β : Type*} [Fintype α] [Fintype β]
    (p : α → Prop) (q : β → Prop) :
    density (fun ab : α × β => p ab.1 ∧ q ab.2) = density p * density q := by
  rw [density_prod (fun a b => p a ∧ q b)]
  change (𝔼 a, density (fun b => p a ∧ q b)) = (𝔼 a, indicator (p a)) * density q
  rw [Finset.expect_mul _ (fun a => indicator (p a)) (density q)]
  apply Finset.expect_congr rfl
  intro a _
  by_cases ha : p a <;> simp [ha, indicator, density]

private theorem density_cube {α : Type*} [Fintype α] (p : α → Prop) :
    density (fun abc : α × α × α => p abc.1 ∧ p abc.2.1 ∧ p abc.2.2) = density p ^ 3 := by
  rw [density_prod_separable p (fun bc : α × α => p bc.1 ∧ p bc.2),
    density_prod_separable p p, pow_succ, pow_two, mul_assoc]

open scoped Classical in
private theorem density_coord_eq {α : Type*} [Fintype α] [Nonempty α]
    (a : α) : density (fun b => b = a) = (Fintype.card α : ℝ)⁻¹ := by
  simp [density, indicator]

private theorem density_collision {α : Type*} [Fintype α] [Nonempty α] :
    density (fun abc : α × α × α =>
      abc.1 = abc.2.1 ∨ abc.1 = abc.2.2 ∨ abc.2.1 = abc.2.2) ≤
      3 / (Fintype.card α : ℝ) := by
  have h : ∀ a : α, density (fun b => a = b) = (Fintype.card α : ℝ)⁻¹ := by
    intro a
    simpa only [eq_comm] using density_coord_eq a
  let p (abc : α × α × α) := abc.1 = abc.2.1
  let q (abc : α × α × α) := abc.1 = abc.2.2
  let r (abc : α × α × α) := abc.2.1 = abc.2.2
  have h₁ : density p = (Fintype.card α : ℝ)⁻¹ := by
    change density (fun abc : α × α × α => abc.1 = abc.2.1) = _
    rw [density_prod (fun a (bc : α × α) => a = bc.1)]
    have he (a : α) : density (fun bc : α × α => a = bc.1) =
        (Fintype.card α : ℝ)⁻¹ := by
      rw [density_prod (fun b (_ : α) => a = b)]
      change (𝔼 b : α, 𝔼 _c : α, indicator (a = b)) = _
      simpa only [Fintype.expect_const] using (show (𝔼 b, indicator (a = b)) = _ from h a)
    simp only [he, Fintype.expect_const]
  have h₂ : density q = (Fintype.card α : ℝ)⁻¹ := by
    change density (fun abc : α × α × α => abc.1 = abc.2.2) = _
    rw [density_prod (fun a (bc : α × α) => a = bc.2)]
    have he (a : α) : density (fun bc : α × α => a = bc.2) =
        (Fintype.card α : ℝ)⁻¹ := by
      rw [density_prod (fun (_ : α) c => a = c)]
      simp [h]
    simp only [he, Fintype.expect_const]
  have h₃ : density r = (Fintype.card α : ℝ)⁻¹ := by
    change density (fun abc : α × α × α => abc.2.1 = abc.2.2) = _
    rw [density_prod (fun (_ : α) (bc : α × α) => bc.1 = bc.2)]
    have he : density (fun bc : α × α => bc.1 = bc.2) =
        (Fintype.card α : ℝ)⁻¹ := by
      rw [density_prod (fun b c : α => b = c)]
      simp [h]
    simp only [he, Fintype.expect_const]
  calc
    _ ≤ density p + (density q + density r) :=
      (density_or_le p _).trans (add_le_add_right (density_or_le q r) _)
    _ = _ := by rw [h₁, h₂, h₃, div_eq_mul_inv]; ring

open scoped Classical in
private theorem exists_three_slices {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (r : α → β → Prop) {δ : ℝ}
    (hδ : 0 < δ) (hn : 6 / (Fintype.card α : ℝ) ≤ δ ^ 3)
    (hr : δ ≤ 𝔼 a, density (r a)) :
    ∃ a b c : α, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      δ ^ 3 / 2 ≤ density (fun y => r a y ∧ r b y ∧ r c y) := by
  let valid (abc : α × α × α) :=
    abc.1 ≠ abc.2.1 ∧ abc.1 ≠ abc.2.2 ∧ abc.2.1 ≠ abc.2.2
  let good (abc : α × α × α) (y : β) := r abc.1 y ∧ r abc.2.1 y ∧ r abc.2.2 y
  have hmean : δ ^ 3 ≤ 𝔼 abc, density (good abc) := by
    have hswap : (𝔼 a, density (r a)) = 𝔼 y, density (fun a => r a y) :=
      Finset.expect_comm _ _ _
    rw [hswap] at hr
    calc
      δ ^ 3 ≤ (𝔼 y, density (fun a => r a y)) ^ 3 := by gcongr
      _ ≤ 𝔼 y, density (fun a => r a y) ^ 3 :=
        expect_pow_three_le _ fun y => density_nonneg _
      _ = 𝔼 abc, density (good abc) := by
        simp_rw [← density_cube]
        exact Finset.expect_comm _ _ _
  have hinvalid : density (fun abc => ¬ valid abc) ≤ 3 / (Fintype.card α : ℝ) := by
    simpa only [valid, not_and_or, not_not] using (density_collision (α := α))
  have hpoint (abc : α × α × α) : density (good abc) ≤
      (if valid abc then density (good abc) else 0) + (indicator (¬ valid abc)) := by
    by_cases h : valid abc
    · simp [indicator, h]
    · simpa [indicator, h] using density_le_one (good abc)
  have hbound := (hmean.trans
    (Finset.expect_le_expect (fun abc _ => hpoint abc)))
  rw [Finset.expect_add_distrib] at hbound
  change δ ^ 3 ≤ (𝔼 abc, if valid abc then density (good abc) else 0) +
    density (fun abc => ¬ valid abc) at hbound
  have hn' : 2 * (3 / (Fintype.card α : ℝ)) ≤ δ ^ 3 := by
    convert hn using 1
    ring
  have havg : δ ^ 3 / 2 ≤ 𝔼 abc, if valid abc then density (good abc) else 0 := by
    linarith only [hn', hinvalid, hbound]
  obtain ⟨⟨a, b, c⟩, _, habc⟩ := Finset.exists_le_of_le_expect univ_nonempty havg
  by_cases h : valid (a, b, c)
  · exact ⟨a, b, c, h.1, h.2.1, h.2.2, by simpa [h, good] using habc⟩
  · have hpos : 0 < δ ^ 3 / 2 := by positivity
    simp [h, not_le.mpr hpos] at habc

private theorem density_pos_exists {α : Type*} [Fintype α] {p : α → Prop}
    (hp : 0 < density p) : ∃ a, p a := by
  by_contra! h
  simp [density, indicator, h] at hp

private noncomputable def sliceThreshold : ℕ → ℝ → ℝ
  | 0, _ => 1
  | k + 1, δ => min (δ ^ 3) (sliceThreshold k (δ ^ 3 / 2))

private theorem sliceThreshold_pos (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    0 < sliceThreshold k δ := by
  induction k generalizing δ with
  | zero => simp [sliceThreshold]
  | succ k ih =>
    exact lt_min (by positivity) (ih (by positivity))

private theorem exists_box {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (k : ℕ) {δ : ℝ} (hδ : 0 < δ) (hn : 6 / (Fintype.card α : ℝ) ≤ sliceThreshold k δ)
    (p : (Fin k → α) × β → Prop) (hp : δ ≤ density p) :
    ∃ (X : Fin k → Fin 3 → α) (y : β), (∀ i, Function.Injective (X i)) ∧
      ∀ f : Fin k → Fin 3, p (fun i => X i (f i), y) := by
  induction k generalizing δ with
  | zero =>
    obtain ⟨⟨x, y⟩, hxy⟩ := density_pos_exists (hδ.trans_le hp)
    refine ⟨fun i => i.elim0, y, fun i => i.elim0, fun f => ?_⟩
    simpa only [Subsingleton.elim (fun i : Fin 0 => (i.elim0 : Fin 3 → α) (f i)) x] using hxy
  | succ k ih =>
    let r (a : α) (y : (Fin k → α) × β) := p (Fin.cons a y.1, y.2)
    let e := (Equiv.prodAssoc α (Fin k → α) β).symm.trans
      ((Fin.consEquiv (fun _ : Fin (k + 1) => α)).prodCongr (Equiv.refl β))
    have hr : δ ≤ 𝔼 a, density (r a) := by
      rw [← density_prod r]
      exact (density_eq_of_equiv e p).symm ▸ hp
    have hfirst : 6 / (Fintype.card α : ℝ) ≤ δ ^ 3 := hn.trans (min_le_left _ _)
    obtain ⟨a, b, c, hab, hac, hbc, habc⟩ := exists_three_slices r hδ hfirst hr
    let u : Fin 3 → α := ![a, b, c]
    have hu : Function.Injective u := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [u]
    obtain ⟨X, y, hX, hy⟩ := ih (by positivity) (hn.trans (min_le_right _ _))
      (fun z => r a z ∧ r b z ∧ r c z) habc
    let X' : Fin (k + 1) → Fin 3 → α := Fin.cons u X
    have hX' : ∀ i, Function.Injective (X' i) := Fin.cases hu hX
    refine ⟨X', y, hX', fun f => ?_⟩
    have h := hy (Fin.tail f)
    have heq : (fun i => X' i (f i)) =
        Fin.cons (u (f 0)) (fun i => X i (f i.succ)) := by
      ext i
      exact Fin.cases rfl (fun _ => rfl) i
    rw [heq]
    generalize hf : f 0 = i
    fin_cases i
    · exact h.1
    · exact h.2.1
    · exact h.2.2


/-! ## Triangles in graphs without a four-clique -/

open scoped Classical in
private noncomputable def trianglesIn {α : Type*} (G : SimpleGraph α) (s : Finset α) :
    Finset (Finset α) := (s.powersetCard 3).filter fun t => G.IsClique t

private theorem mem_trianglesIn {α : Type*} {G : SimpleGraph α} {s t : Finset α} :
    t ∈ trianglesIn G s ↔ t ⊆ s ∧ t.card = 3 ∧ G.IsClique t := by
  simp [trianglesIn, and_assoc]

open scoped Classical in
/-- Each outside portion determines at most one triangle meeting the fixed triangle. -/
private theorem touching_triangles_bound {α : Type*} {G : SimpleGraph α}
    (hG : G.CliqueFree 4) {s t : Finset α} (ht : t ∈ trianglesIn G s) :
    ((trianglesIn G s \ trianglesIn G (s \ t)).card : ℝ) ≤
      ((s \ t).card : ℝ) ^ 2 / 3 + (s \ t).card + 1 := by
  obtain ⟨hts, htc, htG⟩ := mem_trianglesIn.mp ht
  let u := s \ t
  let H := G.induce (u : Set α)
  let small : Finset (Finset α) := {∅} ∪ u.image singleton
  let edges : Finset (Finset α) :=
    H.edgeFinset.image fun e => e.toFinset.map (Function.Embedding.subtype _)
  have hu : ∀ v, v ∈ trianglesIn G s \ trianglesIn G u →
      v ⊆ s ∧ v.card = 3 ∧ G.IsClique v ∧ ¬ v ⊆ u := by
    intro v hv
    obtain ⟨⟨hvs, hvc, hvG⟩, hn⟩ := (mem_sdiff.mp hv).imp mem_trianglesIn.mp id
    exact ⟨hvs, hvc, hvG, fun hvu => hn (mem_trianglesIn.mpr ⟨hvu, hvc, hvG⟩)⟩
  have hcard : (trianglesIn G s \ trianglesIn G u).card ≤ (small ∪ edges).card := by
    apply Finset.card_le_card_of_injOn (fun v => v \ t)
    · intro v hv
      obtain ⟨hvs, hvc, hvG, hvu⟩ := hu v hv
      have hsub : v \ t ⊆ u := fun x hx =>
        mem_sdiff.mpr ⟨hvs (mem_sdiff.mp hx).1, (mem_sdiff.mp hx).2⟩
      have hlt : (v \ t).card < v.card := by
        apply card_lt_card
        refine Finset.ssubset_iff_subset_ne.mpr ⟨sdiff_subset, ?_⟩
        intro h
        exact hvu (h ▸ hsub)
      have hcases : (v \ t).card = 0 ∨ (v \ t).card = 1 ∨ (v \ t).card = 2 := by omega
      rcases hcases with h | h | h
      · have he := card_eq_zero.mp h
        simp [small, he]
      · obtain ⟨x, hx⟩ := card_eq_one.mp h
        have hxu : x ∈ u := hsub (by simp [hx])
        exact mem_union_left _ (mem_union_right _ (mem_image.mpr ⟨x, hxu, hx.symm⟩))
      · obtain ⟨x, y, hxy, hx⟩ := card_eq_two.mp h
        have hx' : x ∈ v \ t := by simp [hx]
        have hy' : y ∈ v \ t := by simp [hx]
        have hxv : x ∈ v := sdiff_subset hx'
        have hyv : y ∈ v := sdiff_subset hy'
        let x' : (u : Set α) := ⟨x, hsub (by simp [hx])⟩
        let y' : (u : Set α) := ⟨y, hsub (by simp [hx])⟩
        refine mem_union_right _ (mem_image.mpr ⟨s(x', y'), ?_, ?_⟩)
        · exact SimpleGraph.mem_edgeFinset.mpr (hvG hxv hyv hxy)
        · simp [Sym2.toFinset_mk_eq, x', y', hx]
    · intro v hv w hw he
      change v \ t = w \ t at he
      obtain ⟨_, hvc, hvG, _⟩ := hu v hv
      obtain ⟨_, hwc, hwG, _⟩ := hu w hw
      have hc : G.IsClique (↑(v ∪ w) : Set α) := by
        intro x hx y hy hxy
        have step : ∀ a ∈ v, ∀ b ∈ w, a ≠ b → G.Adj a b := by
          intro a ha b hb hab
          by_cases hat : a ∈ t
          · by_cases hbt : b ∈ t
            · exact htG hat hbt hab
            · have hb' : b ∈ v \ t := by
                rw [he]
                exact mem_sdiff.mpr ⟨hb, hbt⟩
              exact hvG ha (mem_sdiff.mp hb').1 hab
          · have ha' : a ∈ w \ t := by
              rw [← he]
              exact mem_sdiff.mpr ⟨ha, hat⟩
            exact hwG (mem_sdiff.mp ha').1 hb hab
        rcases mem_union.mp hx with hx | hx
        · rcases mem_union.mp hy with hy | hy
          · exact hvG hx hy hxy
          · exact step x hx y hy hxy
        · rcases mem_union.mp hy with hy | hy
          · exact (step y hy x hx hxy.symm).symm
          · exact hwG hx hy hxy
      have hle : (v ∪ w).card ≤ 3 := by
        by_contra! hn
        obtain ⟨q, hq, hqc⟩ := exists_subset_card_eq (show 4 ≤ (v ∪ w).card by omega)
        exact hG q ⟨hc.subset (coe_subset.mpr hq), hqc⟩
      exact (eq_of_subset_of_card_le subset_union_left (hvc ▸ hle)).trans
        (eq_of_subset_of_card_le subset_union_right (hwc ▸ hle)).symm
  have hH : H.CliqueFree 4 := by
    rw [SimpleGraph.cliqueFree_induce_iff]
    exact fun q _ => hG q
  have hedge := hH.card_edgeFinset_le (r := 3)
  rw [SimpleGraph.turanNumber_three] at hedge
  change H.edgeFinset.card ≤ Fintype.card (↑u : Type _) ^ 2 / 3 at hedge
  rw [Fintype.card_coe] at hedge
  have hnat : H.edgeFinset.card * 3 ≤ u.card ^ 2 :=
    (Nat.mul_le_mul_right 3 hedge).trans (Nat.div_mul_le_self _ _)
  have hreal : (H.edgeFinset.card : ℝ) * 3 ≤ (u.card : ℝ) ^ 2 := by exact_mod_cast hnat
  have hsmall : small.card ≤ 1 + u.card :=
    (card_union_le _ _).trans (by simpa [small] using Nat.add_le_add_left card_image_le 1)
  have halle : (trianglesIn G s \ trianglesIn G u).card ≤ 1 + u.card + H.edgeFinset.card :=
    hcard.trans ((card_union_le _ _).trans (Nat.add_le_add hsmall card_image_le))
  have hallr : ((trianglesIn G s \ trianglesIn G u).card : ℝ) ≤
      1 + u.card + H.edgeFinset.card := by exact_mod_cast halle
  change _ ≤ (u.card : ℝ) ^ 2 / 3 + u.card + 1
  linarith only [hreal, hallr]

open scoped Classical in
private theorem card_trianglesIn_le {α : Type*} (G : SimpleGraph α)
    (hG : G.CliqueFree 4) (s : Finset α) :
    ((trianglesIn G s).card : ℝ) ≤ (s.card : ℝ) ^ 3 / 27 := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    rcases (trianglesIn G s).eq_empty_or_nonempty with he | ⟨t, ht⟩
    · rw [he, card_empty, Nat.cast_zero]
      positivity
    · obtain ⟨hts, htc, _⟩ := mem_trianglesIn.mp ht
      let u := s \ t
      have hu : u.card + 3 = s.card := htc ▸ card_sdiff_add_card_eq_card hts
      have hss : u ⊂ s := Finset.ssubset_iff_subset_ne.mpr ⟨sdiff_subset, by
        intro he
        rw [he] at hu
        omega⟩
      have hi := ih u hss
      have hsub : trianglesIn G u ⊆ trianglesIn G s := by
        intro v hv
        obtain ⟨hvu, hvc, hvG⟩ := mem_trianglesIn.mp hv
        exact mem_trianglesIn.mpr ⟨hvu.trans sdiff_subset, hvc, hvG⟩
      have hsplit := card_sdiff_add_card_eq_card hsub
      have hsplit' : ((trianglesIn G s \ trianglesIn G u).card : ℝ) +
          (trianglesIn G u).card = (trianglesIn G s).card := by exact_mod_cast hsplit
      have ht' := touching_triangles_bound hG ht
      change _ ≤ (u.card : ℝ) ^ 2 / 3 + u.card + 1 at ht'
      have hsum : (s.card : ℝ) = (u.card : ℝ) + 3 := by exact_mod_cast hu.symm
      calc
        ((trianglesIn G s).card : ℝ) ≤ (u.card : ℝ) ^ 2 / 3 + u.card + 1 +
            (u.card : ℝ) ^ 3 / 27 := by linarith only [hsplit', hi, ht']
        _ = (s.card : ℝ) ^ 3 / 27 := by rw [hsum]; ring

/-!
## The expanded four-clique

An expansion chooses a triangle through each pair of the four core vertices, with a separate
witness vertex for each pair. In a sample with no injective expansion, retain the pairs with
at least ten possible witnesses. Any four-clique in that graph would allow a choice of distinct
witnesses outside the core, by Hall's theorem.
-/

private abbrev CorePair := {p : Fin 4 × Fin 4 // p.1 < p.2}
private abbrev PatternVertex := Fin 4 ⊕ CorePair

private def expansion {α : Type*} (T : α → α → α → Prop) (f : PatternVertex → α) : Prop :=
  ∀ p : CorePair, T (f (.inl p.1.1)) (f (.inl p.1.2)) (f (.inr p))

open scoped Classical in
private noncomputable def tripleSet {α : Type*} (a b c : α) : Finset α := {a, b, c}

open scoped Classical in
private theorem tripleSet_swap {α : Type*} (a b c : α) :
    tripleSet a b c = tripleSet b a c := by
  ext x
  simp [tripleSet, or_left_comm]

open scoped Classical in
private theorem tripleSet_rotate {α : Type*} (a b c : α) :
    tripleSet a b c = tripleSet b c a := by
  ext x
  simp [tripleSet, or_left_comm, or_comm]

private def triangleOf {α : Type*} (P : Finset α → Prop) (a b c : α) : Prop :=
  (tripleSet a b c).card = 3 ∧ P (tripleSet a b c)

open scoped Classical in
private noncomputable def completions {α : Type*} [Fintype α]
    (P : Finset α → Prop) (a b : α) : Finset α :=
  univ.filter (triangleOf P a b)

open scoped Classical in
private noncomputable def codegreeGraph {α : Type*} [Fintype α]
    (P : Finset α → Prop) : SimpleGraph α where
  Adj a b := 10 ≤ (completions P a b).card
  symm := ⟨by
    intro a b hab
    have he : completions P a b = completions P b a := by
      unfold completions
      congr 1
      funext x
      rw [triangleOf, triangleOf, tripleSet_swap a b x]
    exact he ▸ hab⟩
  loopless := ⟨by
    intro a ha
    have h : completions P a a = ∅ := by
      apply eq_empty_iff_forall_notMem.2
      intro x hx
      have hxc := (mem_filter.mp hx).2.1
      have ht : tripleSet a a x ⊆ ({a, x} : Finset α) := by simp [tripleSet]
      have hle := (card_le_card ht).trans (card_insert_le a ({x} : Finset α))
      simp at hle
      omega
    simp [h] at ha⟩

open scoped Classical in
private theorem codegreeGraph_cliqueFree {α : Type*} [Fintype α]
    (P : Finset α → Prop) (h : ∀ e : PatternVertex ↪ α, ¬ expansion (triangleOf P) e) :
    (codegreeGraph P).CliqueFree 4 := by
  intro t ht
  let core : Fin 4 ↪ α := (Fintype.equivOfCardEq (by simp [ht.card_eq] :
    Fintype.card (Fin 4) = Fintype.card t)).toEmbedding.trans (Function.Embedding.subtype _)
  let W (p : CorePair) := completions P (core p.1.1) (core p.1.2) \ univ.image core
  have hW (p : CorePair) : 6 ≤ (W p).card := by
    have hadj : 10 ≤ (completions P (core p.1.1) (core p.1.2)).card := by
      apply ht.isClique
      · exact ((Fintype.equivOfCardEq _ : Fin 4 ≃ t) p.1.1).property
      · exact ((Fintype.equivOfCardEq _ : Fin 4 ≃ t) p.1.2).property
      · exact fun he => p.2.ne (core.injective he)
    have hc : (univ.image core).card = 4 := by
      simp [card_image_of_injective _ core.injective]
    have hle := card_le_card_sdiff_add_card (s :=
      completions P (core p.1.1) (core p.1.2)) (t := univ.image core)
    change _ ≤ (W p).card + _ at hle
    omega
  obtain ⟨f, hfinj, hf⟩ := (all_card_le_biUnion_card_iff_exists_injective W).1 (by
    intro s
    by_cases hs : s.Nonempty
    · obtain ⟨p, hp⟩ := hs
      have hc := card_le_univ s
      have h₆ : Fintype.card CorePair = 6 := by decide
      rw [h₆] at hc
      exact hc.trans ((hW p).trans (card_le_card (subset_biUnion_of_mem W hp)))
    · rw [not_nonempty_iff_eq_empty.mp hs]
      simp)
  have hdisj (i : Fin 4) (p : CorePair) : core i ≠ f p := by
    intro he
    apply (mem_sdiff.mp (hf p)).2
    exact mem_image.mpr ⟨i, mem_univ _, he⟩
  let e : PatternVertex ↪ α :=
    ⟨Sum.elim core f, by
      rintro (i | p) (j | q) he
      · exact congrArg Sum.inl (core.injective he)
      · exact (hdisj i q he).elim
      · exact (hdisj j p he.symm).elim
      · exact congrArg Sum.inr (hfinj he)⟩
  apply h e
  intro p
  exact (mem_filter.mp (mem_sdiff.mp (hf p)).1).2

open scoped Classical in
private noncomputable def trianglesFor {α : Type*} [Fintype α]
    (P : Finset α → Prop) : Finset (Finset α) :=
  (univ.powersetCard 3).filter P

open scoped Classical in
private theorem card_trianglesFor_le {α : Type*} [Fintype α] (P : Finset α → Prop)
    (h : ∀ e : PatternVertex ↪ α, ¬ expansion (triangleOf P) e) :
    ((trianglesFor P).card : ℝ) ≤
      (Fintype.card α : ℝ) ^ 3 / 27 + 10 * (Fintype.card α : ℝ) ^ 2 := by
  let G := codegreeGraph P
  let bad (ab : α × α) : Finset (Finset α) :=
    if G.Adj ab.1 ab.2 then ∅ else
      (completions P ab.1 ab.2).image (tripleSet ab.1 ab.2)
  have hbad (ab : α × α) : (bad ab).card ≤ 10 := by
    by_cases hadj : G.Adj ab.1 ab.2
    · simp [bad, hadj]
    · change (if G.Adj ab.1 ab.2 then ∅ else
        (completions P ab.1 ab.2).image (tripleSet ab.1 ab.2)).card ≤ 10
      rw [ite_eq_right hadj]
      exact card_image_le.trans (Nat.le_of_lt (lt_of_not_ge hadj))
  have hsub : trianglesFor P ⊆ trianglesIn G univ ∪ univ.biUnion bad := by
    intro t ht
    have htcard := (mem_powersetCard_univ.mp (mem_filter.mp ht).1)
    have htP := (mem_filter.mp ht).2
    by_cases hcl : G.IsClique t
    · exact mem_union_left _ (mem_trianglesIn.mpr ⟨subset_univ _, htcard, hcl⟩)
    · classical
      have huse (a b c : α) (he : t = tripleSet a b c) (hn : ¬ G.Adj a b) :
          t ∈ univ.biUnion bad := by
        apply mem_biUnion.mpr
        refine ⟨(a, b), mem_univ _, ?_⟩
        change t ∈ (if G.Adj a b then ∅ else _)
        rw [ite_eq_right hn]
        refine mem_image.mpr ⟨c, mem_filter.mpr ⟨mem_univ _, ?_⟩, he.symm⟩
        change (tripleSet a b c).card = 3 ∧ P (tripleSet a b c)
        rw [← he]
        exact ⟨htcard, htP⟩
      obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.mp htcard
      apply mem_union_right
      have hnot : ¬(G.Adj a b ∧ G.Adj a c ∧ G.Adj b c) := by
        simpa only [tripleSet, ← SimpleGraph.is3Clique_triple_iff, SimpleGraph.isNClique_iff,
          htcard, and_true] using hcl
      push Not at hnot
      by_cases h₁ : G.Adj a b
      · by_cases h₂ : G.Adj a c
        · exact huse b c a (tripleSet_rotate ..) (hnot h₁ h₂)
        · exact huse a c b (by ext x; simp [tripleSet, or_comm (a := x = b)]) h₂
      · exact huse a b c rfl h₁
  have hunion : ((univ : Finset (α × α)).biUnion bad).card ≤
      10 * Fintype.card α ^ 2 := by
    calc
      _ ≤ ∑ p : α × α, (bad p).card := card_biUnion_le
      _ ≤ ∑ _p : α × α, 10 := sum_le_sum fun p _ => hbad p
      _ = _ := by simp [Fintype.card_prod, pow_two, mul_comm]
  have hsum := (card_le_card hsub).trans (card_union_le _ _)
  have hsum' : ((trianglesFor P).card : ℝ) ≤ (trianglesIn G univ).card +
      ((univ : Finset (α × α)).biUnion bad).card := by exact_mod_cast hsum
  have hbound : (((univ : Finset (α × α)).biUnion bad).card : ℝ) ≤
      10 * (Fintype.card α : ℝ) ^ 2 := by exact_mod_cast hunion
  have hc := card_trianglesIn_le G (codegreeGraph_cliqueFree P h) univ
  rw [card_univ] at hc
  linarith only [hsum', hbound, hc]

/-! ## The geometric obstruction -/

private abbrev E := EuclideanSpace ℝ (Fin 6)

private theorem inner_sub_sub_of_cross_dist (a b c d : E)
    (hab : dist a c = dist a d) (hcd : dist b c = dist b d) :
    inner ℝ (a - b) (c - d) = 0 := by
  have h₁ := congrArg (fun x : ℝ => x ^ 2) hab
  have h₂ := congrArg (fun x : ℝ => x ^ 2) hcd
  simp only [dist_eq_norm, norm_sub_sq_real] at h₁ h₂
  rw [inner_sub_left, inner_sub_right, inner_sub_right]
  linarith

private theorem no_four_orthogonal_triples
    (X : Fin 4 → Fin 3 → E) (hX : ∀ i, Function.Injective (X i))
    (h : ∀ i j : Fin 4, i ≠ j → ∃ w : E, ∀ a b : Fin 3,
      dist (X i a) (X j b) = dist (X i a) w ∧
      dist (X i a) (X j b) = dist (X j b) w) : False := by
  classical
  let v (i : Fin 4) (a : {x : Fin 3 // x ≠ 0}) := X i a - X i 0
  let V i := Submodule.span ℝ (Set.range (v i))
  have hV (i : Fin 4) : Module.finrank ℝ (V i) = 2 := by
    obtain ⟨w, hw⟩ := h i (i + 1) (by omega)
    have hs : EuclideanGeometry.Cospherical (Set.range (X i)) := by
      refine ⟨w, dist (X (i + 1) 0) w, ?_⟩
      rintro _ ⟨a, rfl⟩
      exact (hw a 0).1.symm.trans (hw a 0).2
    have hi := hs.affineIndependent (p := X i) (fun _ hx => hx) (hX i)
    have hv : LinearIndependent ℝ (v i) :=
      (affineIndependent_iff_linearIndependent_vsub ℝ (X i) 0).mp hi
    change Set.finrank ℝ (Set.range (v i)) = _
    rw [← linearIndependent_iff_card_eq_finrank_span.mp hv]
    rw [Fintype.card_subtype_compl]
    simp
  have hor : OrthogonalFamily ℝ (fun i => V i) (fun i => (V i).subtypeₗᵢ) := by
    apply OrthogonalFamily.of_pairwise
    intro i j hij
    obtain ⟨w, hw⟩ := h i j hij
    change Submodule.IsOrtho (Submodule.span ℝ (Set.range (v i)))
      (Submodule.span ℝ (Set.range (v j)))
    rw [Submodule.isOrtho_span]
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    apply inner_sub_sub_of_cross_dist
    · exact (hw a b).1.trans (hw a 0).1.symm
    · exact (hw 0 b).1.trans (hw 0 0).1.symm
  let L : (∀ i, V i) →ₗ[ℝ] E :=
    ∑ i, (V i).subtype.comp (LinearMap.proj (R := ℝ) i)
  have hL (f : ∀ i, V i) : L f = ∑ i, (f i : E) := by
    simp [L]
  have hinj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro f hf
    funext i
    have hz := congrArg (inner ℝ (f i : E)) hf
    rw [hL, inner_zero_right] at hz
    have hh := hor.inner_right_fintype f i (f i)
    exact inner_self_eq_zero.mp (hh.symm.trans hz)
  have hdim := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_pi_fintype, finrank_euclideanSpace_fin] at hdim
  simp [hV] at hdim

/-! ## The Lenz lower bound -/

private noncomputable def circleX (t : ℕ) : ℝ := ((t : ℝ) + 2)⁻¹

private theorem circleX_pos (t : ℕ) : 0 < circleX t := by
  unfold circleX
  positivity

private noncomputable def circleCoords (t : ℕ) : Fin 2 → ℝ :=
  ![circleX t, Real.sqrt (1 - (circleX t) ^ 2)]

private theorem circleCoords_sq (t : ℕ) : ∑ i, (circleCoords t i) ^ 2 = 1 := by
  have hx : circleX t ≤ 1 := inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) t])
  have hsq : circleX t ^ 2 ≤ 1 := by nlinarith [circleX_pos t]
  rw [Fin.sum_univ_two]
  simp only [circleCoords, Matrix.cons_val_zero, Matrix.cons_val_one,
    Real.sq_sqrt (sub_nonneg.mpr hsq)]
  ring

private noncomputable def circlePointAux (p : Fin 3 × ℕ) : EuclideanSpace ℝ (Fin 3 × Fin 2) :=
  WithLp.toLp 2 (fun ij => if ij.1 = p.1 then circleCoords p.2 ij.2 else 0)

private noncomputable def circleReindex : EuclideanSpace ℝ (Fin 3 × Fin 2) ≃ₗᵢ[ℝ] E :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    (Fintype.equivOfCardEq (by simp : Fintype.card (Fin 3 × Fin 2) = Fintype.card (Fin 6)))

private noncomputable def circlePoint (p : Fin 3 × ℕ) : E :=
  circleReindex (circlePointAux p)

private theorem circlePoint_injective : Function.Injective circlePoint := by
  intro p q h
  have hpq := circleReindex.injective h
  have hx := congrArg (fun x : EuclideanSpace ℝ (Fin 3 × Fin 2) => x (p.1, 0)) hpq
  change (if p.1 = p.1 then circleX p.2 else 0) =
    (if p.1 = q.1 then circleX q.2 else 0) at hx
  by_cases hi : p.1 = q.1
  · have he : ((p.2 : ℝ) + 2)⁻¹ = ((q.2 : ℝ) + 2)⁻¹ := by
      simpa [hi, circleX] using hx
    have hn : (p.2 : ℝ) = (q.2 : ℝ) := add_right_cancel (inv_injective he)
    exact Prod.ext hi (Nat.cast_injective hn)
  · have he : circleX p.2 = 0 := by simpa [hi] using hx
    exact ((circleX_pos _).ne' he).elim

private theorem circlePoint_dist (p q : Fin 3 × ℕ) (hpq : p.1 ≠ q.1) :
    dist (circlePoint p) (circlePoint q) = Real.sqrt 2 := by
  rw [circlePoint, circlePoint, circleReindex.dist_map]
  apply (sq_eq_sq₀ dist_nonneg (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (by norm_num), EuclideanSpace.dist_sq_eq, Fintype.sum_prod_type]
  have hrow (i : Fin 3) :
      (∑ j : Fin 2, dist (circlePointAux p (i, j)) (circlePointAux q (i, j)) ^ 2) =
        (if i = p.1 then (1 : ℝ) else 0) + (if i = q.1 then 1 else 0) := by
    change (∑ j : Fin 2, dist (if i = p.1 then circleCoords p.2 j else 0)
      (if i = q.1 then circleCoords q.2 j else 0) ^ 2) = _
    by_cases hip : i = p.1 <;> by_cases hiq : i = q.1
    · exact (hpq (hip.symm.trans hiq)).elim
    · simp only [hip, hpq, ite_false, Real.dist_eq, sub_zero, sq_abs, add_zero]
      exact circleCoords_sq _
    · simp only [hiq, hpq.symm, ite_false, Real.dist_eq, zero_sub, sq_abs,
        neg_sq, zero_add]
      exact circleCoords_sq _
    · simp [hip, hiq]
  simp_rw [hrow]
  rw [sum_add_distrib]
  simp
  norm_num

private theorem count_le_choose (P : Finset E) :
    anySizeEquilateralTriangleCount 6 P ≤ P.card.choose 3 := by
  classical
  exact (card_filter_le _ _).trans_eq (card_powersetCard ..)

private theorem bdd_anySize (n : ℕ) : BddAbove {m : ℕ | ∃ P : Finset E,
    P.card = n ∧ anySizeEquilateralTriangleCount 6 P = m} := by
  refine ⟨n.choose 3, ?_⟩
  rintro m ⟨P, rfl, rfl⟩
  exact count_le_choose P

open scoped Classical in
private theorem lower_anySize (n : ℕ) : (n / 3) ^ 3 ≤ TAnySize 6 n := by
  let m := n / 3
  let f : Fin 3 × Fin m ↪ E := ⟨fun p => circlePoint (p.1, p.2.val), by
    intro p q he
    have h := circlePoint_injective he
    exact Prod.ext (congrArg (fun x : Fin 3 × ℕ => x.1) h) (Fin.ext (congrArg Prod.snd h))⟩
  let S := univ.map f
  have hS : S.card = 3 * m := by simp [S, Fintype.card_prod]
  obtain ⟨P, hSP, hP⟩ := Infinite.exists_superset_card_eq S n (by rw [hS]; omega)
  let τ (g : Fin 3 → Fin m) := univ.image fun i => f (i, g i)
  have ht : m ^ 3 ≤ anySizeEquilateralTriangleCount 6 P := by
    unfold anySizeEquilateralTriangleCount
    rw [← Fintype.card_fin m, ← Fintype.card_fin 3, ← Fintype.card_fun, ← card_univ]
    apply card_le_card_of_injOn τ
    · intro g _
      apply mem_filter.mpr
      have hp : (τ g).card = 3 := by
        rw [card_image_of_injective]
        · simp
        · intro i j hij
          exact congrArg Prod.fst (f.injective hij)
      refine ⟨mem_powersetCard.mpr ⟨?_, hp⟩, ⟨Real.sqrt 2, by positivity, hp, ?_⟩⟩
      · apply image_subset_iff.mpr
        intro i _
        exact hSP (mem_map_of_mem f (mem_univ _))
      · intro x hx y hy hxy
        obtain ⟨i, _, rfl⟩ := mem_image.mp hx
        obtain ⟨j, _, rfl⟩ := mem_image.mp hy
        apply circlePoint_dist
        intro h
        change i = j at h
        exact hxy (by rw [h])
    · intro g _ g' _ h
      funext i
      have hi : f (i, g i) ∈ τ g' := h ▸ mem_image_of_mem _ (mem_univ _)
      obtain ⟨j, _, he⟩ := mem_image.mp hi
      have hij := f.injective he
      have hji : j = i := congrArg Prod.fst hij
      subst j
      exact (congrArg Prod.snd hij).symm
  exact ht.trans (le_csSup (bdd_anySize n) ⟨P, hP, rfl⟩)

open scoped Classical in
private theorem unit_le_anySize (n : ℕ) : TUnit 6 n ≤ TAnySize 6 n := by
  apply csSup_le' (fun m hm => ?_)
  obtain ⟨P, hP, rfl⟩ := hm
  have hc : unitEquilateralTriangleCount 6 P ≤ anySizeEquilateralTriangleCount 6 P := by
    apply card_le_card
    intro t ht
    obtain ⟨ht₁, ht₂⟩ := mem_filter.mp ht
    exact mem_filter.mpr ⟨ht₁, ⟨1, zero_lt_one, ht₂⟩⟩
  exact hc.trans (le_csSup (bdd_anySize n) ⟨P, hP, rfl⟩)

/-!
## Estimating the triangle count by sampling

Sample vertices independently with replacement. Each three-element set of sample indices
has the same probability of spanning a triangle. A union bound over injections of the pattern
vertices bounds the contribution from samples containing an expansion.
-/

open scoped Classical in
private theorem expect_comp_embedding {ι κ α : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [Fintype α] [Nonempty α] (e : ι ↪ κ) (w : (ι → α) → ℝ) :
    (𝔼 f : κ → α, w (f ∘ e)) = 𝔼 g, w g := by
  let r := Equiv.ofInjective e e.injective
  let e' := (Equiv.piEquivPiSubtypeProd (fun k => k ∈ Set.range e) (fun _ => α)).trans
      ((r.symm.arrowCongr (Equiv.refl α)).prodCongr (Equiv.refl _))
  calc
    _ = 𝔼 p, w (Prod.fst p) := Fintype.expect_equiv e' _ _ fun f => by
      rfl
    _ = _ := by
      rw [← Finset.univ_product_univ]
      rw [Finset.expect_product' univ univ (fun g _ => w g)]
      simp only [Fintype.expect_const]

private theorem density_comp_embedding {ι κ α : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [Fintype α] [Nonempty α] (e : ι ↪ κ) (p : (ι → α) → Prop) :
    density (fun f : κ → α => p (f ∘ e)) = density p :=
  expect_comp_embedding e (fun g => indicator (p g))

open scoped Classical in
private theorem density_exists_le {ι α : Type*} [Fintype ι] [Fintype α]
    (p : ι → α → Prop) :
    density (fun a => ∃ i, p i a) ≤ ∑ i, density (p i) := by
  unfold density
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_le_expect
  intro a _
  by_cases h : ∃ i, p i a
  · obtain ⟨i, hi⟩ := h
    have hle : indicator (p i a) ≤ ∑ j, indicator (p j a) :=
      Finset.single_le_sum (f := fun j => indicator (p j a))
        (fun j _ => by unfold indicator; split <;> norm_num) (mem_univ i)
    simpa [indicator, hi, show ∃ j, p j a from ⟨i, hi⟩] using hle
  · simpa only [indicator, ite_eq_right h] using
      (sum_nonneg (s := (univ : Finset ι)) fun i _ =>
        show 0 ≤ indicator (p i a) from by unfold indicator; split <;> norm_num)

open scoped Classical in
private noncomputable def imageOf {ι κ : Type*} [Fintype ι] (f : ι → κ) : Finset κ :=
  univ.image f

open scoped Classical in
private theorem imageOf_comp {ι κ α : Type*} [Fintype ι] (f : κ → α) (g : ι → κ) :
    imageOf (f ∘ g) = (imageOf g).image f := by
  simp [imageOf, Finset.image_image]

open scoped Classical in
private theorem imageOf_enumerate {κ : Type*} {s : Finset κ} {n : ℕ}
    (e : Fin n ≃ s) : imageOf (fun i => (e i : κ)) = s := by
  ext v
  simp only [imageOf, mem_image, mem_univ, true_and]
  exact ⟨fun ⟨i, hi⟩ => hi ▸ (e i).property,
    fun hv => ⟨e.symm ⟨v, hv⟩, congrArg Subtype.val (e.apply_symm_apply ⟨v, hv⟩)⟩⟩

open scoped Classical in
private theorem sample_triangles_mean {κ α : Type*} [Fintype κ] [Fintype α] [Nonempty α]
    (Q : Finset α → Prop) :
    (𝔼 f : κ → α, ((trianglesFor (fun t => Q (t.image f))).card : ℝ)) =
      ((Fintype.card κ).choose 3 : ℝ) * density (fun g : Fin 3 → α => Q (imageOf g)) := by
  have hpoint (f : κ → α) :
      ((trianglesFor (fun t => Q (t.image f))).card : ℝ) =
        ∑ t ∈ (univ : Finset κ).powersetCard 3, indicator (Q (t.image f)) := by
    simp [trianglesFor, indicator]
  simp_rw [hpoint, Finset.expect_sum_comm]
  have hterm (t : Finset κ) (ht : t ∈ (univ : Finset κ).powersetCard 3) :
      (𝔼 f : κ → α, indicator (Q (t.image f))) =
        density (fun g : Fin 3 → α => Q (imageOf g)) := by
    let e : Fin 3 ≃ t := Fintype.equivOfCardEq (by simp [mem_powersetCard_univ.mp ht])
    let j : Fin 3 ↪ κ := e.toEmbedding.trans (Function.Embedding.subtype _)
    have h := density_comp_embedding j (fun g => Q (imageOf g))
    have hj : imageOf j = t := imageOf_enumerate e
    simpa only [imageOf_comp, hj, density] using h
  rw [sum_congr rfl hterm, sum_const, nsmul_eq_mul, card_powersetCard, card_univ]

open scoped Classical in
private theorem triangle_count_le_sample {κ α : Type*} [Fintype κ] [Fintype α] [Nonempty α]
    (Q : Finset α → Prop) :
    ((Fintype.card κ).choose 3 : ℝ) * density (fun g : Fin 3 → α => Q (imageOf g)) ≤
      (Fintype.card κ : ℝ) ^ 3 / 27 + 10 * (Fintype.card κ : ℝ) ^ 2 +
      ((Fintype.card κ).choose 3 : ℝ) * (Fintype.card (PatternVertex ↪ κ) : ℝ) *
        density (expansion (fun a b c => Q (tripleSet a b c))) := by
  let bad (f : κ → α) :=
    ∃ e : PatternVertex ↪ κ, expansion (fun a b c => Q (tripleSet a b c)) (f ∘ e)
  have hbad : density bad ≤ (Fintype.card (PatternVertex ↪ κ) : ℝ) *
      density (expansion (fun a b c => Q (tripleSet a b c))) := by
    refine (density_exists_le _).trans_eq ?_
    simp only [density_comp_embedding, sum_const, card_univ, nsmul_eq_mul]
  let B := (Fintype.card κ : ℝ) ^ 3 / 27 + 10 * (Fintype.card κ : ℝ) ^ 2
  let M := ((Fintype.card κ).choose 3 : ℝ)
  have hpoint (f : κ → α) : ((trianglesFor (fun t => Q (t.image f))).card : ℝ) ≤
      B + M * indicator (bad f) := by
    by_cases h : bad f
    · have hcount : ((trianglesFor (fun t => Q (t.image f))).card : ℝ) ≤ M := by
        have hn : (trianglesFor (fun t => Q (t.image f))).card ≤ (Fintype.card κ).choose 3 :=
          (card_filter_le _ _).trans_eq
            ((card_powersetCard 3 (univ : Finset κ)).trans (by rw [card_univ]))
        dsimp only [M]
        exact_mod_cast hn
      have hB : 0 ≤ B := by dsimp [B]; positivity
      simpa [indicator, h] using hcount.trans (le_add_of_nonneg_left hB)
    · have hn (e : PatternVertex ↪ κ) :
          ¬ expansion (triangleOf fun t => Q (t.image f)) e := by
        intro he
        apply h
        refine ⟨e, fun p => ?_⟩
        simpa [Function.comp_def, tripleSet] using (he p).2
      simpa [B, indicator, h] using card_trianglesFor_le (fun t => Q (t.image f)) hn
  rw [← sample_triangles_mean (κ := κ) Q]
  calc
    _ ≤ (𝔼 f : κ → α, (B + M * indicator (bad f))) := Finset.expect_le_expect fun f _ => hpoint f
    _ = B + M * density bad := by
      rw [Finset.expect_add_distrib, Fintype.expect_const,
        ← Finset.mul_expect univ (fun f => indicator (bad f)) M]
      rfl
    _ ≤ _ := by
      rw [mul_assoc]
      exact add_le_add (le_refl B) (mul_le_mul_of_nonneg_left hbad (by positivity : 0 ≤ M))

open scoped Classical in
private theorem density_eq_card_triangles {α : Type*} [Fintype α]
    (Q : Finset α → Prop) (hQ : ∀ t, Q t → t.card = 3) :
    density (fun f : Fin 3 → α => Q (imageOf f)) =
      6 * ((trianglesFor Q).card : ℝ) / (Fintype.card α : ℝ) ^ 3 := by
  let good : Finset (Fin 3 → α) := univ.filter fun f => Q (imageOf f)
  have hgood : (good : Set (Fin 3 → α)).MapsTo imageOf (trianglesFor Q) := by
    intro f hf
    have hQf := (mem_filter.mp hf).2
    exact mem_filter.mpr ⟨mem_powersetCard_univ.mpr (hQ _ hQf), hQf⟩
  have hfiber (t : Finset α) (ht : t ∈ trianglesFor Q) :
      (good.filter fun f => imageOf f = t).card = 6 := by
    let S := good.filter fun f => imageOf f = t
    have htc := mem_powersetCard_univ.mp (mem_filter.mp ht).1
    have htQ := (mem_filter.mp ht).2
    have himage (f : S) : imageOf f.val = t := (mem_filter.mp f.property).2
    let incl (f : S) (i : Fin 3) : t := ⟨f.val i, by
      rw [← himage f]
      exact mem_image_of_mem _ (mem_univ _)⟩
    have hbij (f : S) : Function.Bijective (incl f) := by
      apply (Fintype.bijective_iff_surjective_and_card _).mpr
      refine ⟨?_, by simp [htc]⟩
      intro v
      have hv : v.val ∈ imageOf f.val :=
        (congrArg (fun U : Finset α => v.val ∈ U) (himage f)).mpr v.property
      obtain ⟨i, _, hi⟩ := mem_image.mp hv
      exact ⟨i, Subtype.ext hi⟩
    let e : S ≃ (Fin 3 ≃ t) :=
      { toFun := fun f => Equiv.ofBijective (incl f) (hbij f)
        invFun := fun g => ⟨fun i => (g i : α), by
          have he := imageOf_enumerate g
          exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, he.symm ▸ htQ⟩, he⟩⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => Equiv.ext fun _ => rfl }
    change S.card = _
    rw [← Fintype.card_coe, Fintype.card_congr e,
      Fintype.card_equiv (Fintype.equivOfCardEq (by simp [htc]) : Fin 3 ≃ t)]
    decide
  have hc := card_eq_sum_card_fiberwise hgood
  rw [sum_congr rfl hfiber, sum_const, nsmul_eq_mul] at hc
  have hc' : (good.card : ℝ) = (trianglesFor Q).card * 6 := by exact_mod_cast hc
  rw [density, Fintype.expect_eq_sum_div_card]
  simp only [indicator, Finset.sum_boole, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  change (good.card : ℝ) / _ = _
  rw [hc', mul_comm]

/-! ## The asymptotic upper bound -/

private theorem expansion_density_lt {α : Type*} [Fintype α] [Nonempty α]
    (v : α ↪ E) (T : α → α → α → Prop)
    (hdist : ∀ a b c, T a b c →
      dist (v a) (v b) = dist (v a) (v c) ∧ dist (v a) (v b) = dist (v b) (v c))
    {δ : ℝ} (hδ : 0 < δ) (hn : 6 / (Fintype.card α : ℝ) ≤ sliceThreshold 4 δ) :
    density (expansion T) < δ := by
  by_contra! h
  let e := (Equiv.sumPiEquivProdPi (fun _ : PatternVertex => α)).symm
  obtain ⟨X, w, hX, hbox⟩ := exists_box 4 hδ hn (expansion T ∘ e)
    ((density_eq_of_equiv e (expansion T)).symm ▸ h)
  have hT (p : CorePair) (a b : Fin 3) :
      T (X p.1.1 a) (X p.1.2 b) (w p) := by
    let f (i : Fin 4) := if i = p.1.1 then a else if i = p.1.2 then b else 0
    have h' := hbox f p
    change T (X p.1.1 (f p.1.1)) (X p.1.2 (f p.1.2)) (w p) at h'
    simpa [f, p.2.ne.symm] using h'
  apply no_four_orthogonal_triples (fun i a => v (X i a)) (fun i => v.injective.comp (hX i))
  intro i j hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · let p : CorePair := ⟨(i, j), hij⟩
    exact ⟨v (w p), fun a b => hdist _ _ _ (hT p a b)⟩
  · let p : CorePair := ⟨(j, i), hji⟩
    refine ⟨v (w p), fun a b => ?_⟩
    obtain ⟨h₁, h₂⟩ := hdist _ _ _ (hT p b a)
    exact ⟨(dist_comm ..).trans h₂, (dist_comm ..).trans h₁⟩

private theorem sample_ratio_limit :
    Tendsto (fun m : ℕ => ((m : ℝ) ^ 3 / 27 + 10 * (m : ℝ) ^ 2) / (m.choose 3 : ℝ))
      atTop (𝓝 (6 / 27 : ℝ)) := by
  have hpos : ∀ᶠ m : ℕ in atTop, 0 < (m : ℝ) :=
    (eventually_ge_atTop 1).mono fun m hm => by exact_mod_cast hm
  have hden₀ : Tendsto (fun m : ℕ => (m.choose 3 : ℝ) / ((m : ℝ) ^ 3 / 6)) atTop
      (𝓝 1) := by
    have hz : ∀ᶠ m : ℕ in atTop, (m : ℝ) ^ 3 / 6 ≠ 0 := hpos.mono fun m hm => by positivity
    exact (Asymptotics.isEquivalent_iff_tendsto_one hz).mp
      (by simpa [Nat.factorial] using isEquivalent_choose 3)
  have hden : Tendsto (fun m : ℕ => (m.choose 3 : ℝ) / (m : ℝ) ^ 3) atTop
      (𝓝 (1 / 6 : ℝ)) := by
    convert (hden₀.div_const 6) using 1
    funext m
    ring
  have hnum₀ := (tendsto_const_div_atTop_nhds_zero_nat (10 : ℝ)).const_add (1 / 27 : ℝ)
  have hnum : Tendsto (fun m : ℕ => ((m : ℝ) ^ 3 / 27 + 10 * (m : ℝ) ^ 2) / (m : ℝ) ^ 3)
      atTop (𝓝 (1 / 27 : ℝ)) := by
    rw [add_zero] at hnum₀
    apply hnum₀.congr'
    filter_upwards [hpos] with m hm
    field_simp
  have h := hnum.div hden (by norm_num)
  have hlim : (1 / 27 : ℝ) / (1 / 6) = 6 / 27 := by norm_num
  rw [hlim] at h
  apply h.congr'
  filter_upwards [hpos, eventually_ge_atTop (3 : ℕ)] with m hm hm3
  have hchoose : (m.choose 3 : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hm3).ne'
  change _ / ((m : ℝ) ^ 3) / ((m.choose 3 : ℝ) / (m : ℝ) ^ 3) = _
  field_simp

open scoped Classical in
private theorem triangles_upper_aux {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ {α : Type} [Fintype α] [Nonempty α],
      N ≤ Fintype.card α → ∀ (v : α ↪ E) (Q : Finset α → Prop),
      (∀ t, Q t → t.card = 3) →
      (∀ a b c, Q (tripleSet a b c) →
        dist (v a) (v b) = dist (v a) (v c) ∧ dist (v a) (v b) = dist (v b) (v c)) →
      ((trianglesFor Q).card : ℝ) ≤ (1 / 27 + ε) * (Fintype.card α : ℝ) ^ 3 := by
  have hevent := sample_ratio_limit.eventually (gt_mem_nhds
    (show (6 / 27 : ℝ) < 6 / 27 + 3 * ε by linarith))
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.mp hevent
  let m := max 3 m₀
  have hm3 : 3 ≤ m := le_max_left _ _
  have hm : ((m : ℝ) ^ 3 / 27 + 10 * (m : ℝ) ^ 2) / (m.choose 3 : ℝ) <
      6 / 27 + 3 * ε := hm₀ m (le_max_right _ _)
  have hmchoose : 0 < (m.choose 3 : ℝ) := by exact_mod_cast Nat.choose_pos hm3
  let C := (Fintype.card (PatternVertex ↪ Fin m) : ℝ)
  let δ := 3 * ε / (C + 1)
  have hδ : 0 < δ := by dsimp [δ, C]; positivity
  obtain ⟨N, hN⟩ := exists_nat_ge (6 / sliceThreshold 4 δ)
  refine ⟨N, fun {α} _ _ hcard v Q hQ hdist => ?_⟩
  have hnpos : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hthreshold : 6 / (Fintype.card α : ℝ) ≤ sliceThreshold 4 δ := by
    rw [div_le_iff₀ hnpos, mul_comm]
    have hN' : (6 : ℝ) / sliceThreshold 4 δ ≤ Fintype.card α :=
      hN.trans (by exact_mod_cast hcard)
    exact (div_le_iff₀ (sliceThreshold_pos _ hδ)).mp hN'
  let D := density (expansion (fun a b c => Q (tripleSet a b c)))
  have hD : D < δ := expansion_density_lt v _ hdist hδ hthreshold
  have hCD : C * D ≤ 3 * ε := by
    have hC : 0 ≤ C := by positivity
    calc
      _ ≤ C * δ := mul_le_mul_of_nonneg_left hD.le hC
      _ ≤ (C + 1) * δ := by gcongr; linarith
      _ = _ := by
        dsimp [δ]
        field_simp
  have hs := triangle_count_le_sample (κ := Fin m) Q
  simp only [Fintype.card_fin, density_eq_card_triangles Q hQ] at hs
  have hsample :
      6 * ((trianglesFor Q).card : ℝ) / (Fintype.card α : ℝ) ^ 3 ≤
        (((m : ℝ) ^ 3 / 27 + 10 * (m : ℝ) ^ 2) / (m.choose 3 : ℝ)) + C * D := by
    have h := (le_div_iff₀' hmchoose).mpr hs
    convert h using 1
    dsimp [C, D]
    field_simp
  have hbound : 6 * ((trianglesFor Q).card : ℝ) / (Fintype.card α : ℝ) ^ 3 ≤
      6 * (1 / 27 + ε) := by
    linarith only [hsample, hCD, hm]
  have hpow : 0 < (Fintype.card α : ℝ) ^ 3 := by positivity
  have h' := (div_le_iff₀ hpow).mp hbound
  linarith only [h']

open scoped Classical in
private theorem anySize_card_via_subtype (P : Finset E) :
    (trianglesFor (fun t : Finset P =>
      IsAnySizeEquilateralTriangle (t.map (Function.Embedding.subtype (· ∈ P))))).card =
      anySizeEquilateralTriangleCount 6 P := by
  let j : P ↪ E := Function.Embedding.subtype (· ∈ P)
  let Q (t : Finset P) := IsAnySizeEquilateralTriangle (t.map j)
  let e : Finset P ↪ Finset E := ⟨Finset.map j, Finset.map_injective _⟩
  change (trianglesFor Q).card = ((P.powersetCard 3).filter IsAnySizeEquilateralTriangle).card
  rw [← card_map e]
  congr 1
  ext t
  constructor
  · intro ht
    obtain ⟨s, hs, rfl⟩ := mem_map.mp ht
    obtain ⟨hcard, hQ⟩ := (mem_filter.mp hs).imp mem_powersetCard_univ.mp id
    refine mem_filter.mpr ⟨mem_powersetCard.mpr ⟨?_, by simpa [e] using hcard⟩, hQ⟩
    intro x hx
    obtain ⟨v, _, rfl⟩ := mem_map.mp hx
    exact v.property
  · intro ht
    obtain ⟨⟨hsub, hcard⟩, hQ⟩ := (mem_filter.mp ht).imp mem_powersetCard.mp id
    let s := t.subtype (· ∈ P)
    have hm : s.map j = t := subtype_map_of_mem hsub
    refine mem_map.mpr ⟨s, mem_filter.mpr ⟨mem_powersetCard_univ.mpr ?_, ?_⟩, hm⟩
    · simpa only [card_map] using (congrArg Finset.card hm).trans hcard
    · rwa [show Q s ↔ IsAnySizeEquilateralTriangle t from hm ▸ Iff.rfl]

open scoped Classical in
private theorem distances_of_triangle {a b c : E}
    (h : IsAnySizeEquilateralTriangle ({a, b, c} : Finset E)) :
    dist a b = dist a c ∧ dist a b = dist b c := by
  obtain ⟨r, _, hc, hdist⟩ := h
  have hpair (x y : E) : ({x, y} : Finset E).card ≤ 2 := by
    simpa using card_insert_le x ({y} : Finset E)
  have hab : a ≠ b := by
    intro he
    subst b
    have hz := hpair a c
    simp at hc
    omega
  have hac : a ≠ c := by
    intro he
    subst c
    have hz := hpair b a
    simp at hc
    omega
  have hbc : b ≠ c := by
    intro he
    subst c
    have hz := hpair a b
    simp at hc
    omega
  have hab' := hdist a (by simp) b (by simp) hab
  exact ⟨hab'.trans (hdist a (by simp) c (by simp) hac).symm,
    hab'.trans (hdist b (by simp) c (by simp) hbc).symm⟩

open scoped Classical in
private theorem eventually_upper_anySize {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (TAnySize 6 n : ℝ) ≤ (1 / 27 + ε) * (n : ℝ) ^ 3 := by
  obtain ⟨N, hN⟩ := triangles_upper_aux hε
  filter_upwards [eventually_ge_atTop (max N 1)] with n hn
  have hm : {m : ℕ | ∃ P : Finset E,
      P.card = n ∧ anySizeEquilateralTriangleCount 6 P = m}.Nonempty := by
    obtain ⟨P, hP⟩ := Infinite.exists_subset_card_eq E n
    exact ⟨_, P, hP, rfl⟩
  have hmax := Nat.sSup_mem hm (bdd_anySize n)
  obtain ⟨P, hP, hmax⟩ := hmax
  change anySizeEquilateralTriangleCount 6 P = TAnySize 6 n at hmax
  have hPn : 0 < P.card := by omega
  let : Nonempty P := nonempty_coe_sort.mpr (card_pos.mp hPn)
  let j : P ↪ E := Function.Embedding.subtype (· ∈ P)
  let Q (t : Finset P) := IsAnySizeEquilateralTriangle (t.map j)
  have hQ (t : Finset P) (ht : Q t) : t.card = 3 := by
    obtain ⟨r, _, hr⟩ := ht
    simpa only [card_map] using hr.1
  have hd (a b c : P) (ht : Q (tripleSet a b c)) :
      dist (j a) (j b) = dist (j a) (j c) ∧
        dist (j a) (j b) = dist (j b) (j c) :=
    distances_of_triangle (by simpa [Q, tripleSet] using ht)
  have hb : N ≤ Fintype.card P := by simp [hP]; omega
  have h := hN hb j Q hQ hd
  rw [Fintype.card_coe, hP] at h
  rw [← hmax, ← anySize_card_via_subtype P]
  exact h

private theorem floor_thirds_limit :
    Tendsto (fun n : ℕ => ((n / 3 : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 (1 / 3 : ℝ)) := by
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) :=
    (eventually_ge_atTop 1).mono fun n hn => by exact_mod_cast hn
  have hl' : Tendsto (fun n : ℕ => 1 / 3 - 1 / (n : ℝ)) atTop (𝓝 (1 / 3 : ℝ)) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).const_sub (1 / 3 : ℝ)
  refine hl'.squeeze' tendsto_const_nhds ?_ ?_
  · filter_upwards [hpos] with n hn
    rw [le_div_iff₀ hn]
    have hsub := (Nat.mod_lt n (by decide : 0 < 3))
    have hdecomp := Nat.div_add_mod n 3
    have hmod : ((n % 3 : ℕ) : ℝ) ≤ 3 := by exact_mod_cast hsub.le
    have hreal : 3 * ((n / 3 : ℕ) : ℝ) + ((n % 3 : ℕ) : ℝ) = n := by exact_mod_cast hdecomp
    field_simp
    linarith only [hmod, hreal]
  · filter_upwards [hpos] with n hn
    apply (div_le_iff₀ hn).2
    exact (Nat.cast_div_le (m := n) (n := 3)).trans_eq (by push_cast; ring)

private theorem anySize_limit :
    Tendsto (fun n : ℕ => (TAnySize 6 n : ℝ) / (n : ℝ) ^ 3) atTop (𝓝 (1 / 27 : ℝ)) := by
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) :=
    (eventually_ge_atTop 1).mono fun n hn => by exact_mod_cast hn
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · have hl : Tendsto (fun n : ℕ => ((n / 3 : ℕ) : ℝ) ^ 3 / (n : ℝ) ^ 3) atTop
        (𝓝 (1 / 27 : ℝ)) := by
      convert floor_thirds_limit.pow 3 using 1
      · funext n
        exact (div_pow ..).symm
      · norm_num
    filter_upwards [hl.eventually (lt_mem_nhds ha)] with n hn
    have hnat := lower_anySize n
    have hcast : ((n / 3 : ℕ) : ℝ) ^ 3 ≤ (TAnySize 6 n : ℝ) := by exact_mod_cast hnat
    exact hn.trans_le (div_le_div_of_nonneg_right hcast (by positivity))
  · let ε := (a - 1 / 27) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    filter_upwards [eventually_upper_anySize hε, hpos] with n hcount hn
    exact ((div_le_iff₀ (by positivity : 0 < (n : ℝ) ^ 3)).2 hcount).trans_lt
      (by dsimp [ε]; linarith)

/--
**Erdős Problem 755 holds (Clemen–Dumitrescu–Liu).** Let $T_1(n)$ be the largest number of unit
equilateral triangles spanned by a set of $n$ points in $\mathbb{R}^6$, and let $T(n)$ be the
largest number of equilateral triangles of positive side length spanned by a set of $n$ points in
$\mathbb{R}^6$; a triangle spanned by a set is a three-element subset of it whose points are
pairwise at the same distance. Then there is a function $o : \mathbb{N} \to \mathbb{R}$ with
$o(n) \to 0$ as $n \to \infty$ such that $T_1(n) \le (1/27 + o(n))\, n^3$ for all sufficiently
large $n$, and $T(n)$ is asymptotically equivalent to $n^3/27$ as $n \to \infty$.

Source: Felix
Christian Clemen, Adrian Dumitrescu, and Dingyuan Liu, The number of regular simplices in higher
dimensions, arXiv:2507.19841 (2025), https://arxiv.org/abs/2507.19841. Moved from
`OpenConjectures/Geometry/ErdosProblem755`. Resolved true: Resolved externally by Clemen,
Dumitrescu, and Liu. This repository records the statement, not an internal proof; a separate
pinned Lean proof is cited in the registry.
-/
public theorem conjecture_holds : conjecture := by
  let o (n : ℕ) : ℝ := (TAnySize 6 n : ℝ) / (n : ℝ) ^ 3 - 1 / 27
  have ho : Tendsto o atTop (𝓝 0) := by
    simpa only [sub_self] using anySize_limit.sub_const (1 / 27 : ℝ)
  constructor
  · refine ⟨o, (Asymptotics.isLittleO_one_iff ℝ).2 ho, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have hu : (TUnit 6 n : ℝ) ≤ (TAnySize 6 n : ℝ) := by exact_mod_cast unit_le_anySize n
    refine hu.trans_eq ?_
    dsimp [o]
    field_simp
    ring
  · apply Asymptotics.isEquivalent_of_tendsto_one
    convert anySize_limit.const_mul 27 using 1
    · funext n
      change (TAnySize 6 n : ℝ) / ((1 / 27 : ℝ) * (n : ℝ) ^ 3) =
        27 * ((TAnySize 6 n : ℝ) / (n : ℝ) ^ 3)
      ring
    · norm_num
end MathlibExt.Geometry.ErdosProblem755Wanted
