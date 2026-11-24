/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`FormalConjectures/ErdosProblems/755.lean` (Formal Conjectures), for the counting
definitions and the statement of Erdős Problem 755.
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: The Formal Conjectures Authors
-/

module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Order.Lattice.Nat
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Data.Fintype.Perm
import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import MathlibExt.Combinatorics.DensityHalesJewett

/-!
# Equilateral triangles among points in six dimensions

`conjecture_holds` proves the asymptotic of Clemen, Dumitrescu and Liu for the maximum number
of equilateral triangles in a set of `n` points in `ℝ⁶`, and the resulting upper bound for
unit triangles. Three orthogonal circles give the lower bound.

For the upper bound, sample `m` points with replacement and record which triples of indices
span equilateral triangles. For sufficiently large point sets, density Hales–Jewett gives
three choices at each index realizing any pattern of fixed positive density in every
combination. Four indices with every pair in some triangle would then give four mutually
orthogonal planes, as in the geometric obstruction of Clemen, Dumitrescu and Liu.
In a pattern without four such indices,
we can move weight between vertices that share no triangle without decreasing the weighted
count. Repeating leaves at most one contributing triangle. AM–GM bounds its weight by `m³/27`.
Averaging over patterns and then letting `m` grow gives the sharp leading coefficient.
-/

@[expose] public section

open Filter
open scoped Asymptotics

namespace MathlibExt.Geometry.ErdosProblem755Wanted

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

open Finset Asymptotics EuclideanGeometry
open scoped Topology Real DirectSum

private theorem counts_bounded (d n : ℕ) :
    BddAbove {m : ℕ | ∃ P : Finset (EuclideanSpace ℝ (Fin d)),
      P.card = n ∧ anySizeEquilateralTriangleCount d P = m} := by
  classical
  refine ⟨n.choose 3, ?_⟩
  rintro m ⟨Q, hQ, rfl⟩
  simpa [anySizeEquilateralTriangleCount, card_powersetCard, hQ] using
    (card_filter_le (Q.powersetCard 3) IsAnySizeEquilateralTriangle)

private theorem unit_le_any (d n : ℕ) : TUnit d n ≤ TAnySize d n := by
  classical
  apply csSup_le'
  rintro k ⟨P, hP, rfl⟩
  refine le_trans ?_ (le_csSup (counts_bounded d n) ⟨P, hP, rfl⟩)
  unfold unitEquilateralTriangleCount anySizeEquilateralTriangleCount
  apply Finset.card_le_card
  intro T hT
  obtain ⟨hsub, hunit⟩ := Finset.mem_filter.mp hT
  exact Finset.mem_filter.mpr ⟨hsub, 1, zero_lt_one, hunit⟩

private theorem reduce_to_any_size
    (h : (fun n : ℕ => (TAnySize 6 n : ℝ)) ~[atTop]
        (fun n : ℕ => (1 / 27 : ℝ) * (n : ℝ) ^ 3)) : conjecture := by
  obtain ⟨φ, hφ, hfactor⟩ := h.exists_eq_mul
  refine ⟨⟨fun n => (φ n - 1) / 27, (isLittleO_one_iff ℝ).2 ?_, ?_⟩, h⟩
  · simpa using (hφ.sub (tendsto_const_nhds (x := (1 : ℝ)))).div_const 27
  · filter_upwards [hfactor] with n hn
    calc
      (TUnit 6 n : ℝ) ≤ (TAnySize 6 n : ℝ) := by exact_mod_cast unit_le_any 6 n
      _ = φ n * (1 / 27 * (n : ℝ) ^ 3) := hn
      _ = _ := by ring

-- Parametrize three unit circles in disjoint coordinate planes.
private noncomputable def circlePoint (i : Fin 3) (t : ℕ) : EuclideanSpace ℝ (Fin 6) :=
  let x := Real.cos (Real.arctan (t : ℝ))
  let y := Real.sin (Real.arctan (t : ℝ))
  ![!₂[x, y, 0, 0, 0, 0], !₂[0, 0, x, y, 0, 0], !₂[0, 0, 0, 0, x, y]] i

private theorem circle_dist {i j : Fin 3} (h : i ≠ j) (a b : ℕ) :
    dist (circlePoint i a) (circlePoint j b) = √2 := by
  rw [EuclideanSpace.dist_eq]
  congr 1
  have ha := Real.cos_sq_add_sin_sq (Real.arctan (a : ℝ))
  have hb := Real.cos_sq_add_sin_sq (Real.arctan (b : ℝ))
  fin_cases i <;> fin_cases j <;> first | contradiction |
    simp [circlePoint, Fin.sum_univ_succ, Real.dist_eq, sq_abs]; linarith

private theorem circle_inj {i j : Fin 3} {a b : ℕ} (h : circlePoint i a = circlePoint j b) :
    i = j ∧ a = b := by
  have hij : i = j := by
    by_contra hn
    have := circle_dist hn a b
    rw [h, dist_self] at this
    exact (ne_of_gt (show 0 < √(2 : ℝ) by positivity)) this.symm
  subst j
  refine ⟨rfl, Nat.cast_injective (R := ℝ) ?_⟩
  have eval (k : Fin 6) := congrArg (fun p : EuclideanSpace ℝ (Fin 6) => p k) h
  have hc : Real.cos (Real.arctan a) = Real.cos (Real.arctan b) := by
    fin_cases i
    · exact eval 0
    · exact eval 2
    · exact eval 4
  have hs : Real.sin (Real.arctan a) = Real.sin (Real.arctan b) := by
    fin_cases i
    · exact eval 1
    · exact eval 3
    · exact eval 5
  rw [← Real.tan_arctan (a : ℝ), Real.tan_eq_sin_div_cos, hs, hc,
    ← Real.tan_eq_sin_div_cos, Real.tan_arctan]

-- Every transversal of the three circles determines a distinct equilateral triangle.
private theorem lenz_lower (n : ℕ) : (n / 3) ^ 3 ≤ TAnySize 6 n := by
  classical
  let k := n / 3
  let S := univ.image fun x : Fin 3 × Fin k => circlePoint x.1 x.2
  have hcS : S.card ≤ n := calc
    S.card ≤ Fintype.card (Fin 3 × Fin k) := card_image_le.trans_eq card_univ
    _ ≤ n := by simp [k]; omega
  obtain ⟨P, hSP, hP⟩ := Infinite.exists_superset_card_eq S n hcS
  let tri (v : Fin 3 → Fin k) := univ.image fun i => circlePoint i (v i)
  have hinj (v : Fin 3 → Fin k) : Function.Injective fun i => circlePoint i (v i) :=
    fun _ _ h => (circle_inj h).1
  have he (v : Fin 3 → Fin k) : IsAnySizeEquilateralTriangle (tri v) := by
    refine ⟨√2, by positivity, ⟨?_, ?_⟩⟩
    · simp [tri, card_image_of_injective _ (hinj v)]
    · intro x hx y hy hxy
      obtain ⟨i, _, rfl⟩ := mem_image.mp hx
      obtain ⟨j, _, rfl⟩ := mem_image.mp hy
      exact circle_dist (by rintro rfl; exact hxy rfl) _ _
  have hsub (v : Fin 3 → Fin k) : tri v ⊆ P := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := mem_image.mp hx
    exact hSP (mem_image.mpr ⟨(i, v i), mem_univ _, rfl⟩)
  have hi : Function.Injective tri := by
    intro v w hvw
    funext i
    have hh : circlePoint i (v i) ∈ tri w := hvw ▸ mem_image_of_mem _ (mem_univ i)
    obtain ⟨j, _, hj⟩ := mem_image.mp hh
    obtain ⟨rfl, ht⟩ := circle_inj hj
    exact Fin.ext ht.symm
  have hcount : (n / 3) ^ 3 ≤ anySizeEquilateralTriangleCount 6 P := calc
    _ = (univ.image tri).card := by simp [card_image_of_injective _ hi, k]
    _ ≤ _ := by
      apply card_le_card
      rintro T hT
      obtain ⟨v, _, rfl⟩ := mem_image.mp hT
      exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨hsub v, (he v).choose_spec.2.1⟩, he v⟩
  exact hcount.trans (le_csSup (counts_bounded 6 n) ⟨P, hP, rfl⟩)

-- A common triangle completion for each pair of triples forces four orthogonal planes.
private theorem no_four_triples (p : Fin 4 → Fin 3 → EuclideanSpace ℝ (Fin 6))
    (hinj : ∀ i, Function.Injective (p i))
    (hedge : ∀ i j, i ≠ j → ∃ w, ∀ a b,
      dist (p i a) (p j b) = dist (p i a) w ∧ dist (p i a) (p j b) = dist (p j b) w) :
    False := by
  classical
  have hd (i j : Fin 4) (hij : i ≠ j) : ∃ r, ∀ a b, dist (p i a) (p j b) = r := by
    obtain ⟨w, hw⟩ := hedge i j hij
    refine ⟨dist (p i 0) w, fun a b => ?_⟩
    exact (hw a b).2.trans ((hw 0 b).2.symm.trans (hw 0 b).1)
  let V i := vectorSpan ℝ (Set.range (p i))
  have rankV (i : Fin 4) : Module.finrank ℝ (V i) = 2 := by
    obtain ⟨j, hji⟩ := exists_ne i
    obtain ⟨r, hr⟩ := hd i j hji.symm
    have hs : Cospherical (Set.range (p i)) := by
      refine ⟨p j 0, r, ?_⟩
      rintro _ ⟨a, rfl⟩
      exact hr a 0
    exact (hs.affineIndependent Set.Subset.rfl (hinj i)).finrank_vectorSpan (by decide)
  have ho : Pairwise fun i j => (V i).IsOrtho (V j) := by
    intro i j hij
    obtain ⟨r, hr⟩ := hd j i hij.symm
    rw [show V i = _ from vectorSpan_range_eq_span_range_vsub_right ℝ (p i) 0,
      show V j = _ from vectorSpan_range_eq_span_range_vsub_right ℝ (p j) 0,
      Submodule.isOrtho_span]
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact inner_vsub_vsub_of_dist_eq_of_dist_eq
      ((hr 0 0).trans (hr b 0).symm) ((hr 0 a).trans (hr b a).symm)
  have hi : iSupIndep V := (OrthogonalFamily.of_pairwise ho).independent
  have hdim := LinearMap.finrank_le_finrank_of_injective hi.dfinsupp_lsum_injective
  change Module.finrank ℝ (⨁ i, V i) ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin 6)) at hdim
  simp [Module.finrank_directSum, rankV] at hdim

section

variable {I : Type*}

-- Each vertex weight counts its copies. The weight of a triple counts its transversals.
private def weight (H : Finset (Finset I)) (w : I → ℕ) := ∑ e ∈ H, ∏ i ∈ e, w i

private def link [DecidableEq I] (H : Finset (Finset I)) (w : I → ℕ) (a : I) :=
  ∑ e ∈ H, if a ∈ e then ∏ i ∈ e.erase a, w i else 0

private def shift [DecidableEq I] (w : I → ℕ) (a b : I) (i : I) :=
  if i = a then 0 else if i = b then w a + w b else w i

-- Merging two vertices in no common edge changes the total by their link-weight difference.
private theorem move_weight [DecidableEq I] (H : Finset (Finset I)) (w : I → ℕ)
    {a b : I} (hab : a ≠ b) (hn : ∀ e ∈ H, a ∈ e → b ∉ e) :
    weight H (shift w a b) + w a * link H w a = weight H w + w a * link H w b := by
  unfold weight link
  simp only [mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun e he => ?_
  have same {s : Finset I} (ha : a ∉ s) (hb : b ∉ s) :
      s.prod (shift w a b) = s.prod w := by
    apply prod_congr rfl
    intro i hi
    simp [shift, ne_of_mem_of_not_mem hi ha, ne_of_mem_of_not_mem hi hb]
  by_cases ha : a ∈ e
  · have hb := hn e he ha
    rw [← mul_prod_erase e (shift w a b) ha, ← mul_prod_erase e w ha]
    simp [shift, ha, hb]
  by_cases hb : b ∈ e
  · rw [← mul_prod_erase e (shift w a b) hb, ← mul_prod_erase e w hb,
      same (fun h => ha (mem_of_mem_erase h)) (notMem_erase _ _)]
    simp [shift, hab.symm, ha, hb, add_mul, add_comm]
  simp [ha, hb, same ha hb]

private theorem three_amgm (x y z : ℕ) : 27 * (x * y * z) ≤ (x + y + z) ^ 3 := by
  have third : 0 ≤ ((3 : ℝ)⁻¹) := by norm_num
  have h := Real.geom_mean_le_arith_mean3_weighted third third third
    (Nat.cast_nonneg x) (Nat.cast_nonneg y) (Nat.cast_nonneg z) (by norm_num)
  have hc := pow_le_pow_left₀ (by positivity) h 3
  have cube (a : ℕ) : ((a : ℝ) ^ (3 : ℝ)⁻¹) ^ 3 = a :=
    Real.rpow_inv_natCast_pow (Nat.cast_nonneg a) (by decide : (3 : ℕ) ≠ 0)
  simp only [mul_pow, cube] at hc
  exact_mod_cast (show 27 * ((x : ℝ) * y * z) ≤ (x + y + z : ℝ) ^ 3 by linarith only [hc])

-- Merge toward the larger link until AM–GM applies to the sole possible edge.
private theorem weighted_bound [Fintype I] (H : Finset (Finset I)) (h3 : ∀ e ∈ H, e.card = 3)
    (hfree : ∀ (f : Fin 4 ↪ I), ∃ i j, i ≠ j ∧ ∀ e ∈ H, f i ∈ e → f j ∉ e)
    (w : I → ℕ) : 27 * weight H w ≤ (∑ i, w i) ^ 3 := by
  classical
  let s := univ.filter fun i => w i ≠ 0
  have hs : ∀ i, i ∈ s ↔ w i ≠ 0 := fun _ => by simp [s]
  by_cases small : s.card ≤ 3
  · have off (e : Finset I) (h : ¬e ⊆ s) : e.prod w = 0 := by
      obtain ⟨i, hi, hout⟩ := not_subset.mp h
      exact prod_eq_zero hi (by simpa [hs] using hout)
    by_cases exists_edge : ∃ e ∈ H, e ⊆ s
    · obtain ⟨e, he, hsub⟩ := exists_edge
      have hterm : weight H w = e.prod w := by
        apply sum_eq_single_of_mem e he
        intro b hb hne
        apply off
        intro hb'
        exact hne ((eq_of_subset_of_card_le hb' (small.trans_eq (h3 b hb).symm)).trans
          (eq_of_subset_of_card_le hsub (small.trans_eq (h3 e he).symm)).symm)
      rw [hterm]
      calc
        _ ≤ (∑ i ∈ e, w i) ^ 3 := by
          obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.mp (h3 e he)
          simpa [hab, hac, hbc, mul_assoc, add_assoc] using three_amgm (w a) (w b) (w c)
        _ ≤ _ := Nat.pow_le_pow_left (sum_le_sum_of_subset (subset_univ e)) _
    · have hz : weight H w = 0 := sum_eq_zero fun e he => off e fun hin => exists_edge ⟨e, he, hin⟩
      simp [hz]
  · obtain ⟨f : Fin 4 ↪ I, hf⟩ := Function.Embedding.exists_of_card_le_finset
      (s := s) (show Fintype.card (Fin 4) ≤ s.card by simp; omega)
    obtain ⟨i, j, hij, hsep⟩ := hfree f
    have move {a b : I} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b)
        (hn : ∀ e ∈ H, a ∈ e → b ∉ e) (hl : link H w a ≤ link H w b) :
        27 * weight H w ≤ (∑ i, w i) ^ 3 := by
      let u := shift w a b
      have less : (univ.filter fun i => u i ≠ 0).card < s.card := by
        apply card_lt_card
        apply Finset.ssubset_iff_subset_ne.mpr
        constructor
        · intro x hx
          by_cases h : x = b
          · simpa [h] using hb
          have hx' : x ≠ a ∧ w x ≠ 0 := by simpa [u, shift, h] using hx
          exact (hs x).2 hx'.2
        · intro heq
          have := heq.symm ▸ ha
          simp [u, shift] at this
      have hrec := weighted_bound H h3 hfree u
      have hweight := move_weight H w hab hn
      have hle := Nat.mul_le_mul_left (w a) hl
      have hmono : weight H w ≤ weight H u := by dsimp [u]; omega
      have hsum : ∑ i, u i = ∑ i, w i := by
        rw [← add_sum_erase univ u (mem_univ a), ← add_sum_erase univ w (mem_univ a)]
        have hbe : b ∈ univ.erase a := by simp [hab.symm]
        rw [← add_sum_erase _ u hbe, ← add_sum_erase _ w hbe]
        have heq : ∑ i ∈ (univ.erase a).erase b, u i = ∑ i ∈ (univ.erase a).erase b, w i := by
          refine sum_congr rfl fun i hi => ?_
          simp only [mem_erase, mem_univ, and_true] at hi
          simp [u, shift, hi.1, hi.2]
        rw [heq]
        simp [u, shift, hab.symm, add_assoc]
      exact (Nat.mul_le_mul_left _ hmono).trans (hsum ▸ hrec)
    rcases le_total (link H w (f i)) (link H w (f j)) with hl | hl
    · exact move (hf (Set.mem_range_self i)) (hf (Set.mem_range_self j)) (f.injective.ne hij)
        hsep hl
    · exact move (hf (Set.mem_range_self j)) (hf (Set.mem_range_self i)) (f.injective.ne hij.symm)
        (fun e he hj hi => hsep e he hi hj) hl
termination_by (univ.filter fun i => w i ≠ 0).card
decreasing_by exact less

end

-- Use words over the alphabet of all ternary m-tuples. A line varies all m letters freely.
private theorem dense_box (m : ℕ) (hm : 0 < m) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N, ∀ n ≥ N, ∀ A : Finset (Fin m → Fin n),
      δ * (n : ℝ) ^ m ≤ A.card →
        ∃ p : Fin m → Fin 3 ↪ Fin n, ∀ v : Fin m → Fin 3, (fun i => p i (v i)) ∈ A := by
  classical
  let k := Fintype.card (Fin m → Fin 3)
  have hk : 2 ≤ k := by
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
    simp [k, pow_succ]
    have := Nat.one_le_pow r 3 (by decide)
    omega
  obtain ⟨d, hd⟩ := MathlibExt.Combinatorics.DensityHalesJewettWanted.density_hales_jewett
    k hk δ hδ
  refine ⟨3 ^ d, ?_⟩
  intro n hn A hA
  have hn' : 0 < n := lt_of_lt_of_le (pow_pos (by decide) _) hn
  let _ : NeZero n := ⟨hn'.ne'⟩
  let e := Fintype.equivFin (Fin m → Fin 3)
  obtain ⟨code : (Fin d → Fin 3) ↪ Fin n⟩ :=
    Function.Embedding.nonempty_of_card_le (α := Fin d → Fin 3) (β := Fin n) (by simpa using hn)
  let word (x : Fin d → Fin k) (i : Fin m) := code (fun j => e.symm (x j) i)
  let B (t : Fin m → Fin n) := univ.filter fun x => t + word x ∈ A
  -- Averaging over translations preserves density, so one translated word space is dense.
  have hsum : ∑ t, (B t).card = k ^ d * A.card := by
    simp only [B, card_filter]
    rw [sum_comm]
    have hx (x : Fin d → Fin k) : ∑ t : Fin m → Fin n, (if t + word x ∈ A then 1 else 0) =
        A.card := by
      rw [show (∑ t : Fin m → Fin n, (if t + word x ∈ A then 1 else 0 : ℕ)) = _ from
        Equiv.sum_comp (Equiv.addRight (word x)) (fun t => if t ∈ A then 1 else 0)]
      simp
    simp [hx]
  have hex : ∃ t, δ * (k : ℝ) ^ d ≤ (B t).card := by
    by_contra! h
    have hs := sum_lt_sum_of_nonempty (s := univ) univ_nonempty (fun t _ => h t)
    have he : ∑ t, ((B t).card : ℝ) = (k : ℝ) ^ d * A.card := by exact_mod_cast hsum
    rw [he] at hs
    simp only [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_pow] at hs
    have := mul_le_mul_of_nonneg_left hA (show 0 ≤ (k : ℝ) ^ d by positivity)
    linarith only [this, hs]
  obtain ⟨t, ht⟩ := hex
  obtain ⟨l, hl⟩ := hd (B t) ht
  let g (i : Fin m) (a : Fin 3) := word (l (e fun _ => a)) i
  have hcoordinate (v : Fin m → Fin 3) (i : Fin m) :
      word (l (e v)) i = g i (v i) := by
    apply congrArg code
    funext j
    cases hj : l.idxFun j <;> simp [Combinatorics.Line.coe_apply, hj]
  have hginj (i : Fin m) : Function.Injective (g i) := by
    intro a b hab
    obtain ⟨j, hj⟩ := l.proper
    have hh := congrFun (code.injective hab) j
    simpa [Combinatorics.Line.coe_apply, hj] using hh
  refine ⟨fun i => ⟨fun a => t i + g i a, fun a b h => hginj i (add_left_cancel h)⟩, ?_⟩
  intro v
  change (fun i => t i + g i (v i)) ∈ A
  simpa only [B, mem_filter, mem_univ, true_and, Pi.add_def, hcoordinate] using hl (e v)

-- A sample records each triple of indices whose image belongs to the triangle family.
private def pattern {m n : ℕ} (H : Finset (Finset (Fin n))) (x : Fin m → Fin n) :=
  (univ.powersetCard 3).filter fun s => s.image x ∈ H

-- A bijection between triples leaves all coordinates outside the source triple free.
private theorem assignment_count {m n : ℕ} (s : Finset (Fin m)) (t : Finset (Fin n))
    (hs : s.card = 3) (ht : t.card = 3) :
    6 * n ^ (m - 3) ≤ (univ.filter fun f : Fin m → Fin n => s.image f = t).card := by
  classical
  let build (z : (s ≃ t) × ({i // i ∉ s} → Fin n)) (i : Fin m) :=
    if h : i ∈ s then (z.1 ⟨i, h⟩ : Fin n) else z.2 ⟨i, h⟩
  have hb (z) : s.image (build z) = t := by
    ext j
    constructor
    · rintro hj
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hj
      simp [build, hi]
    · intro hj
      obtain ⟨i, hi⟩ := z.1.surjective (⟨j, hj⟩ : t)
      exact mem_image.mpr ⟨i, i.2, by simpa [build, i.2] using congrArg Subtype.val hi⟩
  have hbi : Function.Injective build := by
    intro z w h
    apply Prod.ext
    · apply Equiv.ext
      intro i
      simpa [build, i.2] using congrFun h i
    · funext i
      simpa [build, i.2] using congrFun h i
  let e : s ≃ t := Fintype.equivOfCardEq (by simp [hs, ht])
  calc
    _ = Fintype.card ((s ≃ t) × ({i // i ∉ s} → Fin n)) := by
      simp [Fintype.card_equiv e, Fintype.card_subtype_compl, hs, Nat.factorial]
    _ = (univ.image build).card := by simp [card_image_of_injective _ hbi]
    _ ≤ _ := by
      apply card_le_card
      intro x hx
      obtain ⟨z, _, rfl⟩ := mem_image.mp hx
      exact mem_filter.mpr ⟨mem_univ _, hb z⟩

private theorem sample_count {m n : ℕ} (H : Finset (Finset (Fin n)))
    (h3 : ∀ t ∈ H, t.card = 3) :
    m.choose 3 * (H.card * (6 * n ^ (m - 3))) ≤
      ∑ x : Fin m → Fin n, (pattern H x).card := by
  classical
  simp only [pattern, card_filter]
  rw [sum_comm]
  have h (s : Finset (Fin m)) (hs : s ∈ univ.powersetCard 3) :
      H.card * (6 * n ^ (m - 3)) ≤ ∑ x : Fin m → Fin n, if s.image x ∈ H then 1 else 0 := by
    rw [← card_filter]
    let f (x : Fin m → Fin n) := s.image x
    rw [card_eq_sum_card_fiberwise (f := f) (t := H)
      (s := univ.filter fun x => s.image x ∈ H) (fun x hx => (mem_filter.mp hx).2)]
    rw [← smul_eq_mul, ← sum_const]
    refine sum_le_sum fun t ht => ?_
    have heq : ({x ∈ univ.filter (fun x : Fin m → Fin n => s.image x ∈ H) | f x = t}) =
        univ.filter (fun x : Fin m → Fin n => s.image x = t) := by
      ext x
      simp [f]
      grind
    rw [heq]
    exact assignment_count s t (mem_powersetCard.mp hs).2 (h3 t ht)
  simpa using sum_le_sum h

private theorem edge_dist {m : ℕ} {s : Finset (Fin m)} {x : Fin m → EuclideanSpace ℝ (Fin 6)}
    (hs : s.card = 3) (ht : IsAnySizeEquilateralTriangle (s.image x))
    {i j k : Fin m} (hi : i ∈ s) (hj : j ∈ s) (hk : k ∈ s)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    dist (x i) (x j) = dist (x i) (x k) ∧ dist (x i) (x j) = dist (x j) (x k) := by
  obtain ⟨r, _, hc, hd⟩ := ht
  have hinj := card_image_iff.mp (hc.trans hs.symm)
  have heq {a b : Fin m} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) : dist (x a) (x b) = r :=
    hd _ (mem_image_of_mem _ ha) _ (mem_image_of_mem _ hb) (fun h => hab (hinj ha hb h))
  rw [heq hi hj hij, heq hi hk hik, heq hj hk hjk]
  trivial

-- A pattern shared by a whole box satisfies the geometric four-triple exclusion.
private theorem box_bound {m n : ℕ}
    (H : Finset (Finset (Fin n))) (p : Fin n → EuclideanSpace ℝ (Fin 6))
    (geom : ∀ t ∈ H, IsAnySizeEquilateralTriangle (t.image p))
    (F : Finset (Finset (Fin m))) (g : Fin m → Fin 3 ↪ Fin n) (hp : Function.Injective p)
    (hg : ∀ v : Fin m → Fin 3, pattern H (fun i => g i (v i)) = F) :
    27 * F.card ≤ m ^ 3 := by
  classical
  have mem {s : Finset (Fin m)} (he : s ∈ F) (v : Fin m → Fin 3) :
      s.card = 3 ∧ IsAnySizeEquilateralTriangle (s.image fun i => p (g i (v i))) := by
    rw [← hg v] at he
    obtain ⟨hs, ht⟩ := mem_filter.mp he
    exact ⟨(mem_powersetCard.mp hs).2, by simpa [image_image, Function.comp_def] using geom _ ht⟩
  have free (f : Fin 4 ↪ Fin m) : ∃ i j, i ≠ j ∧ ∀ e ∈ F, f i ∈ e → f j ∉ e := by
    by_contra! h
    apply no_four_triples (fun i a => p (g (f i) a)) (fun i => hp.comp (g _).injective)
    intro i j hij
    obtain ⟨s, hs, hi, hj⟩ := h i j hij
    have hc := (mem hs (fun _ => 0)).1
    obtain ⟨k, hk, hki, hkj⟩ : ∃ k ∈ s, k ≠ f i ∧ k ≠ f j := by
      by_contra! e
      have he : s ⊆ {f i, f j} := by
        intro a ha
        simp only [mem_insert, mem_singleton]
        by_cases ha' : a = f i
        · exact Or.inl ha'
        · exact Or.inr (e a ha ha')
      have := card_le_card he
      simp [f.injective.ne hij, hc] at this
    refine ⟨p (g k 0), fun a b => ?_⟩
    let v (l : Fin m) : Fin 3 := if l = f i then a else if l = f j then b else 0
    have ht := (mem hs v).2
    have hd := edge_dist hc ht hi hj hk (f.injective.ne hij) hki.symm hkj.symm
    simpa [v, hki, hkj, f.injective.ne hij.symm] using hd
  simpa [weight] using weighted_bound F (fun e he => (mem he (fun _ => 0)).1) free (fun _ => 1)

-- Sparse patterns contribute at most one extra triangle on average for fixed sample size.
private theorem sample_upper (m : ℕ) (hm : 3 ≤ m) :
    ∃ N, ∀ n ≥ N, ∀ H : Finset (Finset (Fin n)),
      (∀ t ∈ H, t.card = 3) →
      ∀ p : Fin n ↪ EuclideanSpace ℝ (Fin 6),
        (∀ t ∈ H, IsAnySizeEquilateralTriangle (t.image p)) →
        (m.choose 3 : ℝ) * 6 * (H.card / (n : ℝ) ^ 3) ≤ (m : ℝ) ^ 3 / 27 + 1 := by
  classical
  let Ω := Finset (Finset (Fin m))
  let M : ℝ := Fintype.card (Finset (Fin m))
  let C : ℝ := Fintype.card Ω
  have hM : 0 < M := Nat.cast_pos.mpr Fintype.card_pos
  have hC : 0 < C := Nat.cast_pos.mpr Fintype.card_pos
  obtain ⟨N, hd⟩ := dense_box m (by omega) (1 / (C * M)) (by positivity)
  refine ⟨max N 1, fun n hn H h3 p hgeom => ?_⟩
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  let f : (Fin m → Fin n) → Ω := pattern H
  let B (F : Ω) := univ.filter fun x => f x = F
  let L := (m : ℝ) ^ 3 / 27
  have hB (F : Ω) : ((B F).card : ℝ) * F.card ≤ (B F).card * L + n ^ m / C := by
    by_cases high : 1 / (C * M) * (n : ℝ) ^ m ≤ (B F).card
    · obtain ⟨g, hg⟩ := hd n (by omega) (B F) high
      have bound := box_bound H p hgeom F g p.injective (fun v => (mem_filter.mp (hg v)).2)
      have hh : (F.card : ℝ) ≤ L := by
        dsimp [L]
        have : 27 * (F.card : ℝ) ≤ (m : ℝ) ^ 3 := by exact_mod_cast bound
        linarith
      exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans
        (le_add_of_nonneg_right (by positivity))
    · have hF : (F.card : ℝ) ≤ M := by
        dsimp [M]
        exact_mod_cast card_le_univ F
      calc
        _ ≤ (1 / (C * M) * (n : ℝ) ^ m) * M :=
          mul_le_mul (le_of_not_ge high) hF (by positivity) (by positivity)
        _ = (n : ℝ) ^ m / C := by field_simp
        _ ≤ _ := le_add_of_nonneg_left (by dsimp [L]; positivity)
  have hfiber (w : Ω → ℝ) :
      ∑ F, ((B F).card : ℝ) * w F = ∑ x, w (f x) := by
    simpa only [B, sum_const, nsmul_eq_mul] using (sum_fiberwise' univ f w)
  have hmass : ∑ F, ((B F).card : ℝ) = (n : ℝ) ^ m := by
    simpa using hfiber (fun _ => 1)
  have hsum := sum_le_sum (s := univ) (fun F _ => hB F)
  rw [hfiber (fun F => (F.card : ℝ)), sum_add_distrib, ← sum_mul, hmass] at hsum
  simp only [sum_const, card_univ, nsmul_eq_mul] at hsum
  change ∑ x, ((pattern H x).card : ℝ) ≤ (n : ℝ) ^ m * L + C * ((n : ℝ) ^ m / C) at hsum
  have hlow : (m.choose 3 : ℝ) * (H.card * (6 * (n : ℝ) ^ (m - 3))) ≤
      ∑ x : Fin m → Fin n, ((pattern H x).card : ℝ) := by exact_mod_cast sample_count H h3
  have hpow : (n : ℝ) ^ (m - 3) * (n : ℝ) ^ 3 = (n : ℝ) ^ m := by
    rw [← pow_add, Nat.sub_add_cancel hm]
  have hpos : 0 < (n : ℝ) ^ (m - 3) := by positivity
  rw [show C * ((n : ℝ) ^ m / C) = (n : ℝ) ^ m by field_simp] at hsum
  rw [← hpow] at hsum
  have hscaled : (m.choose 3 : ℝ) * 6 * H.card ≤ (L + 1) * (n : ℝ) ^ 3 := by
    apply (mul_le_mul_iff_of_pos_right hpos).mp
    nlinarith only [hlow.trans hsum]
  rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
  exact hscaled

private theorem extremal_family (n : ℕ) : ∃ (H : Finset (Finset (Fin n)))
    (p : Fin n ↪ EuclideanSpace ℝ (Fin 6)), H.card = TAnySize 6 n ∧
      (∀ t ∈ H, t.card = 3) ∧ ∀ t ∈ H, IsAnySizeEquilateralTriangle (t.image p) := by
  classical
  let A := {m : ℕ | ∃ P : Finset (EuclideanSpace ℝ (Fin 6)), P.card = n ∧
    anySizeEquilateralTriangleCount 6 P = m}
  have hex : A.Nonempty := by
    obtain ⟨P, hP⟩ := Finset.exists_card_eq (α := EuclideanSpace ℝ (Fin 6)) n
    exact ⟨_, P, hP, rfl⟩
  obtain ⟨Q, hQ, hcount⟩ := Nat.sSup_mem hex (counts_bounded 6 n)
  obtain ⟨p : Fin n ↪ EuclideanSpace ℝ (Fin 6), hp⟩ :=
    Function.Embedding.exists_of_card_eq_finset (α := Fin n) (s := Q) (by simpa using hQ.symm)
  let H := (univ.powersetCard 3).filter fun t => IsAnySizeEquilateralTriangle (t.map p)
  refine ⟨H, p, ?_, fun t ht => (mem_powersetCard.mp (mem_filter.mp ht).1).2, ?_⟩
  · change H.card = sSup A
    rw [← hcount, anySizeEquilateralTriangleCount, ← hp, powersetCard_map, filter_map, card_map]
    rfl
  · intro t ht
    simpa only [← map_eq_image] using (mem_filter.mp ht).2

-- First let the point count grow for each sample size, then let the sample size grow.
private theorem any_size_limit : Tendsto (fun n : ℕ => (TAnySize 6 n : ℝ) / n ^ 3) atTop
    (𝓝 (1 / 27 : ℝ)) := by
  have hfloor : Tendsto (fun n : ℕ => ((n / 3 : ℕ) : ℝ) / n) atTop (𝓝 (1 / 3 : ℝ)) := by
    have h := (tendsto_nat_floor_mul_div_atTop (show 0 ≤ (1 / 3 : ℝ) by norm_num)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    have floor_three (k : ℕ) : ⌊(k : ℝ) / 3⌋₊ = k / 3 := Nat.floor_div_eq_div k 3
    simpa only [Function.comp_def, one_div_mul_eq_div, floor_three] using h
  apply tendsto_order.mpr
  constructor
  · intro l hl
    have hl' : l < (1 / 3 : ℝ) ^ 3 := by norm_num at hl ⊢; exact hl
    filter_upwards [(hfloor.pow 3).eventually_const_lt hl'] with n hn
    apply hn.trans_le
    rw [div_pow]
    exact div_le_div_of_nonneg_right (by exact_mod_cast lenz_lower n) (by positivity)
  · intro u hu
    have hne : ∀ᶠ m : ℕ in atTop, (m : ℝ) ^ 3 / (3 : ℕ).factorial ≠ 0 := by
      filter_upwards [eventually_gt_atTop 0] with m hm
      positivity
    have hcoef := (isEquivalent_iff_tendsto_one hne).mp (isEquivalent_choose 3)
    have hc : Tendsto (fun m : ℕ => (m.choose 3 : ℝ) / ((m : ℝ) ^ 3 / 6) * u) atTop (𝓝 u) := by
      simpa [Nat.factorial] using hcoef.mul_const u
    have he : Tendsto (fun m : ℕ => (1 / 27 : ℝ) + 1 / (m : ℝ) ^ 3) atTop (𝓝 (1 / 27)) := by
      simpa [div_pow] using
        (tendsto_const_nhds (x := (1 / 27 : ℝ))).add
          ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 3)
    obtain ⟨m, hm, hm'⟩ := ((eventually_ge_atTop 3).and (he.eventually_lt hc hu)).exists
    have hm0 : 0 < (m : ℝ) := Nat.cast_pos.mpr (by omega)
    have hb : (m : ℝ) ^ 3 / 27 + 1 < (m.choose 3 : ℝ) * 6 * u := by
      field_simp at hm' ⊢
      nlinarith only [hm']
    obtain ⟨N, hN⟩ := sample_upper m hm
    filter_upwards [eventually_ge_atTop N] with n hn
    obtain ⟨H, p, hH, h3, hg⟩ := extremal_family n
    have hh := hN n hn H h3 p hg
    rw [hH] at hh
    exact lt_of_mul_lt_mul_left (hh.trans_lt hb) (by positivity)

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
  apply reduce_to_any_size
  apply isEquivalent_of_tendsto_one
  have h := any_size_limit.const_mul 27
  norm_num at h
  apply h.congr'
  filter_upwards with n
  change 27 * ((TAnySize 6 n : ℝ) / n ^ 3) = _ / _
  ring

end MathlibExt.Geometry.ErdosProblem755Wanted
