/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Counting steps in Javanpeykar's Theorem 4.5.2

A. Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi curves*, Algebra Number
Theory 8 (2014), 89–140, finds a non-Weierstrass point of bounded height on a Belyi curve
(Theorem 4.5.2, pp. 122–123). Two steps of that proof are pure counting, once the geometry has
been turned into numbers. This file proves those counting steps, with the geometry as hypotheses:

* `Javanpeykar.two_mul_add_one_le_of_riemannHurwitz`,
  `Javanpeykar.genus_le_degree_of_riemannHurwitz` and
  `Javanpeykar.three_le_degree_of_riemannHurwitz`: the Riemann–Hurwitz count behind
  "g ≤ deg π" (Lemma 3.2.2, p. 106) and "deg π ≥ 3" when `g ≥ 1` (proof of Proposition 3.5.1,
  p. 112), for a map ramified only above three points;
* `Finset.exists_mem_notMem_of_card_lt_mul`: if `F i`, for `i ∈ I`, are pairwise disjoint finite
  sets with at least `d` elements each and `#W < #I * d`, then some `F i` has an element outside
  `W`;
* `Javanpeykar.exists_mem_fiber_notMem_of_card_le`: the instance of the previous item used in the
  proof of Theorem 4.5.2, p. 123, "Since the number of Weierstrass points on Y is at most g³ − g,
  there exists an integer 1 ≤ i ≤ (deg π)² such that the fibre π⁻¹(aᵢ) contains a
  non-Weierstrass point".
-/

@[expose] public section

set_option autoImplicit false

namespace Finset

/-- **A pairwise disjoint family has a point outside a small set.** Let `F i`, for `i ∈ I`, be
pairwise disjoint finite sets with at least `d` elements each, and let `W` be a finite set with
fewer than `#I * d` elements. Then some `F i` with `i ∈ I` has an element outside `W`.

The union of the `F i` has at least `#I * d` elements, so it is not contained in `W`. -/
theorem exists_mem_notMem_of_card_lt_mul {ι α : Type*} {I : Finset ι} {F : ι → Finset α}
    {W : Finset α} {d : ℕ} (hdisj : (I : Set ι).PairwiseDisjoint F)
    (hcard : ∀ i ∈ I, d ≤ (F i).card) (hW : W.card < I.card * d) :
    ∃ i ∈ I, ∃ x ∈ F i, x ∉ W := by
  classical
  have hU : I.card * d ≤ (I.biUnion F).card := by
    rw [card_biUnion hdisj]
    refine le_trans ?_ (sum_le_sum hcard)
    rw [sum_const, nsmul_eq_mul, Nat.cast_id]
  obtain ⟨x, hx, hxW⟩ := exists_mem_notMem_of_card_lt_card (hW.trans_le hU)
  obtain ⟨i, hi, hxi⟩ := mem_biUnion.mp hx
  exact ⟨i, hi, x, hxi, hxW⟩

end Finset

namespace Javanpeykar

open Finset

/-- **The Riemann–Hurwitz count for a map ramified above three points.** Let `ι` be a finite
type (the points of a curve `Y` above the three branch points `0`, `1`, `∞`), `b : ι → Fin 3` a
surjection (the branch point below each of them; it is surjective because every fibre is
nonempty), and `e : ι → ℕ` (the ramification indices), with `∑_{b y = t} e y = d` for each of the
three branch points `t`. If the Riemann–Hurwitz equation
`2 g - 2 = -2 d + ∑_y (e y - 1)` holds in `ℤ`, then `2 g + 1 ≤ d`.

The sum `∑_y (e y - 1)` is `3 d - n` with `n ≥ 3` the number of points above `0`, `1`, `∞`, so
`2 g - 2 ≤ d - 3`. No positivity of the `e y` is needed. Source: A. Javanpeykar, *Polynomial
bounds for Arakelov invariants of Belyi curves*, Algebra Number Theory 8 (2014), Lemma 3.2.2,
p. 106 ("g ≤ deg π ... the statement follows from the Riemann–Hurwitz formula"). -/
theorem two_mul_add_one_le_of_riemannHurwitz {ι : Type*} [Fintype ι] {b : ι → Fin 3}
    (hb : Function.Surjective b) {e : ι → ℕ} {d g : ℕ}
    (hfib : ∀ t, ∑ y ∈ univ.filter (fun y => b y = t), e y = d)
    (hRH : 2 * (g : ℤ) - 2 = -2 * d + ∑ y, ((e y : ℤ) - 1)) :
    2 * g + 1 ≤ d := by
  have hsum : ∑ y, e y = 3 * d := by
    rw [← Finset.sum_fiberwise univ b e]
    simp [hfib]
  have hcard : 3 ≤ Fintype.card ι := by
    simpa using Fintype.card_le_of_surjective b hb
  have hsumZ : ∑ y, ((e y : ℤ) - 1) = 3 * d - Fintype.card ι := by
    rw [Finset.sum_sub_distrib]
    have h1 : ∑ y : ι, (e y : ℤ) = 3 * (d : ℤ) := by exact_mod_cast hsum
    simp [h1]
  have hcardZ : (3 : ℤ) ≤ Fintype.card ι := by exact_mod_cast hcard
  have : (2 * g + 1 : ℤ) ≤ d := by linarith
  exact_mod_cast this

/-- **`g ≤ deg π` for a map ramified above three points.** Under the hypotheses of
`Javanpeykar.two_mul_add_one_le_of_riemannHurwitz` (the Riemann–Hurwitz equation for a map of
degree `d` from a curve of genus `g`, ramified only above three points), `g ≤ d`.

Source: A. Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi curves*, Algebra
Number Theory 8 (2014), Lemma 3.2.2, p. 106: "Let π : Y → X(2) be a Belyi cover with Y of genus
g. Then, g ≤ deg π." -/
theorem genus_le_degree_of_riemannHurwitz {ι : Type*} [Fintype ι] {b : ι → Fin 3}
    (hb : Function.Surjective b) {e : ι → ℕ} {d g : ℕ}
    (hfib : ∀ t, ∑ y ∈ univ.filter (fun y => b y = t), e y = d)
    (hRH : 2 * (g : ℤ) - 2 = -2 * d + ∑ y, ((e y : ℤ) - 1)) :
    g ≤ d := by
  have := two_mul_add_one_le_of_riemannHurwitz hb hfib hRH
  omega

/-- **`deg π ≥ 3` in positive genus.** Under the hypotheses of
`Javanpeykar.two_mul_add_one_le_of_riemannHurwitz` (the Riemann–Hurwitz equation for a map of
degree `d` from a curve of genus `g`, ramified only above three points), if `1 ≤ g` then
`3 ≤ d`.

Source: A. Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi curves*, Algebra
Number Theory 8 (2014), proof of Proposition 3.5.1, p. 112: "Since g ≥ 1 and π : Y → X(2) is a
Belyi cover, the inequality deg π ≥ 3 holds." -/
theorem three_le_degree_of_riemannHurwitz {ι : Type*} [Fintype ι] {b : ι → Fin 3}
    (hb : Function.Surjective b) {e : ι → ℕ} {d g : ℕ}
    (hfib : ∀ t, ∑ y ∈ univ.filter (fun y => b y = t), e y = d)
    (hRH : 2 * (g : ℤ) - 2 = -2 * d + ∑ y, ((e y : ℤ) - 1)) (hg : 1 ≤ g) :
    3 ≤ d := by
  have := two_mul_add_one_le_of_riemannHurwitz hb hfib hRH
  omega

/-- **A fibre with a point outside a small set.** Let `F : ℕ → Finset α` be a family of finite
sets (the fibres `π⁻¹(aᵢ)`) that are pairwise disjoint for `i ∈ [1, d²]` and have `d` elements
each, and let `W` be a finite set (the Weierstrass points) with at most `g³ - g` elements, where
`1 ≤ g ≤ d`. Then some `F i` with `1 ≤ i ≤ d²` has an element outside `W`.

The fibres have `d² · d = d³ ≥ g³ > g³ - g` points in all, so this is the case `I = [1, d²]` of
`Finset.exists_mem_notMem_of_card_lt_mul`. Source: A. Javanpeykar, *Polynomial bounds for
Arakelov invariants of Belyi curves*, Algebra Number Theory 8 (2014), proof of Theorem 4.5.2,
p. 123: "Since the number of Weierstrass points on Y is at most g³ − g, there exists an integer
1 ≤ i ≤ (deg π)² such that the fibre π⁻¹(aᵢ) contains a non-Weierstrass point". -/
theorem exists_mem_fiber_notMem_of_card_le {α : Type*} {F : ℕ → Finset α}
    {W : Finset α} {d g : ℕ} (hg : 1 ≤ g) (hgd : g ≤ d)
    (hdisj : (Icc 1 (d ^ 2) : Set ℕ).PairwiseDisjoint F)
    (hcard : ∀ i ∈ Icc 1 (d ^ 2), (F i).card = d) (hW : W.card ≤ g ^ 3 - g) :
    ∃ i ∈ Icc 1 (d ^ 2), ∃ x ∈ F i, x ∉ W := by
  refine exists_mem_notMem_of_card_lt_mul hdisj (fun i hi => (hcard i hi).ge) ?_
  have h2 : g ^ 3 - g < g ^ 3 := Nat.sub_lt (by positivity) hg
  have h3 : g ^ 3 ≤ d ^ 3 := Nat.pow_le_pow_left hgd 3
  have h4 : (Icc 1 (d ^ 2)).card * d = d ^ 3 := by
    rw [Nat.card_Icc, Nat.add_sub_cancel]
    ring
  omega

end Javanpeykar
