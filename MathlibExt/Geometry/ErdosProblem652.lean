/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import MathlibExt.Geometry.Metric
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Data.Finset.Sort
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Erdős Problem 652

The constants `erdosAlpha k` tend to infinity. A circle grid supplies admissible constants,
and a partition by circles and lines bounds the number of pins with few distinct distances.

Source record `EP-652` (Erdős Problem 652).
-/

@[expose] public section

namespace MathlibExt.Geometry.ErdosProblem652Wanted

/-- **Euclidean plane for Erdős Problem 652.** The real Euclidean plane is the space
$\mathbb{R}^2$ of pairs of real numbers with the Euclidean inner product and norm. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- **Points with few distinct distances.** For a finite set $X$ of points in the Euclidean plane
and a real number $t$, the number of points $x \in X$ such that the number of distinct distances
from $x$ to the other points of $X$ is less than $t$. -/
noncomputable def countSmallPoints (X : Finset Plane) (threshold : ℝ) : ℕ := by
  classical
  exact (X.filter (fun x => (distinctDistancesFrom X x : ℝ) < threshold)).card

/-- **Many points with few distinct distances.** For natural numbers $n$, $k$ and a real number
$c$, the property that some set $X$ of exactly $n$ points in the Euclidean plane contains at
least $k$ points $x$ such that the number of distinct distances from $x$ to the other points of
$X$ is less than $c\sqrt{n}$.

For $1 \le k \le n$ this says that, with the points of $X$ ordered by this number, the $k$-th
smallest value is less than $c\sqrt{n}$. -/
def HasSmallKth (n k : ℕ) (bound : ℝ) : Prop :=
  ∃ X : Finset Plane, X.card = n ∧
    k ≤ countSmallPoints X (bound * Real.sqrt (n : ℝ))

/-- **Admissible constants in Erdős Problem 652.** A real number $c$ is admissible for
$k \in \mathbb{N}$ if there is $N$ such that for every $n \ge N$ some set $X$ of exactly $n$
points in the Euclidean plane contains at least $k$ points $x$ such that the number of distinct
distances from $x$ to the other points of $X$ is less than $c\sqrt{n}$. -/
def isAdmissibleBound (k : ℕ) (bound : ℝ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → HasSmallKth n k bound

/-- **The Erdős constant $\alpha_k$.** For $k \in \mathbb{N}$, $\alpha_k$ is the infimum of the
set of real numbers that are admissible for $k$: the reals $c$ for which there is $N$ such
that for every $n \ge N$ some set $X$ of exactly $n$ points in the Euclidean plane contains
at least $k$ points $x$ such that the number of distinct distances from $x$ to the other points
of $X$ is less than $c\sqrt{n}$. If this set is empty or unbounded below, $\alpha_k = 0$. -/
noncomputable def erdosAlpha (k : ℕ) : ℝ :=
  sInf { bound : ℝ | isAdmissibleBound k bound }

/-- **Erdős Problem 652.** For a finite set $X$ of points in the Euclidean plane and $x \in X$,
let $R_X(x)$ be the number of distinct distances from $x$ to the other points of $X$. For
$k \in \mathbb{N}$ let $\alpha_k$ be the infimum of the reals $c$ for which there is $N$ such
that for every $n \ge N$ some set $X$ of exactly $n$ points in the plane has at least $k$
points $x$ with $R_X(x) < c\sqrt{n}$ (an empty set or a set unbounded below is given infimum
$0$). The proposition is that $\alpha_k \to \infty$ as $k \to \infty$. -/
def conjecture : Prop :=
  Filter.Tendsto erdosAlpha Filter.atTop Filter.atTop

noncomputable section

open Finset

private def point (x y : ℝ) : Plane := !₂[x, y]

private lemma dist_sq_coordinates (p q : Plane) :
    dist p q ^ 2 = (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 := by
  simp [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs]

/-! ### Admissibility via a circle grid

Use the pins `(i, 0)` and a grid with points `(u, √(s² + 1 + v - u²))` for `u, v < s`.
For a fixed pin the squared distances are a fixed translation of `v - 2iu`, which takes
only `O(k s)` values. Taking a subset of the grid together with the pins gives exact cardinality.
-/

private def pins (k : ℕ) : Finset Plane := (range k).image fun i : ℕ => point i 0

private lemma pins_card (k : ℕ) : (pins k).card = k := by
  rw [pins, card_image_of_injective, card_range]
  intro a b hab
  exact_mod_cast (show (a : ℝ) = b from congrArg (fun p : Plane => p 0) hab)

private def gridPoint (s : ℕ) (v : ℕ × ℕ) : Plane :=
  point v.1 (Real.sqrt ((s : ℝ) ^ 2 + 1 + v.2 - (v.1 : ℝ) ^ 2))

private def grid (s : ℕ) := ((range s) ×ˢ (range s)).image (gridPoint s)

private lemma grid_rad {s i : ℕ} (hi : i < s) (j : ℕ) :
    0 ≤ (s : ℝ) ^ 2 + 1 + j - (i : ℝ) ^ 2 := by
  have h : (i : ℝ) ≤ s := by exact_mod_cast hi.le
  nlinarith [pow_le_pow_left₀ (by positivity) h 2, Nat.cast_nonneg (α := ℝ) j]

private lemma grid_card (s : ℕ) : (grid s).card = s ^ 2 := by
  classical
  rw [grid, card_image_of_injOn, card_product, card_range, pow_two]
  rintro ⟨i, j⟩ hij ⟨u, v⟩ huv he
  have : (i : ℝ) = u := congrArg (fun p : Plane => p 0) he
  have : i = u := by exact_mod_cast this
  subst u
  have h := congrArg (fun p : Plane => (p 1) ^ 2) he
  change (Real.sqrt _) ^ 2 = (Real.sqrt _) ^ 2 at h
  have hi := mem_range.mp (mem_product.mp hij).1
  rw [Real.sq_sqrt (grid_rad hi j), Real.sq_sqrt (grid_rad hi v)] at h
  congr 1
  exact_mod_cast (show (j : ℝ) = v by linarith)

private lemma grid_dist_card (k s i : ℕ) (hi : i < k) :
    ((grid s).image (fun p => dist p (point i 0))).card ≤ (2 * k + 1) * s := by
  classical
  let f (t : ℕ) := Real.sqrt ((s : ℝ) ^ 2 + 1 + (i : ℝ) ^ 2 - 2 * i * s + t)
  apply le_trans (card_le_card (t := (range ((2 * k + 1) * s)).image f) ?_)
    (card_image_le.trans (card_range _).le)
  simp only [grid, image_subset_iff, forall_mem_image, mem_product, mem_range]
  rintro ⟨u, v⟩ ⟨hu, hv⟩
  apply mem_image.mpr
  refine ⟨2 * i * (s - u) + v, mem_range.mpr ?_, ?_⟩
  · have := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hi.le) (Nat.sub_le s u)
    nlinarith
  · have h := dist_sq_coordinates (gridPoint s (u, v)) (point i 0)
    change dist _ _ ^ 2 = ((u : ℝ) - i) ^ 2 + (Real.sqrt _ - 0) ^ 2 at h
    rw [sub_zero, Real.sq_sqrt (grid_rad hu v)] at h
    dsimp [f]
    push_cast [Nat.cast_sub hu.le]
    rw [← Real.sqrt_sq (dist_nonneg (x := gridPoint s (u, v)) (y := point i 0))]
    congr 1
    linear_combination -h

private lemma admissible_nonempty (k : ℕ) : {c : ℝ | isAdmissibleBound k c}.Nonempty := by
  classical
  refine ⟨10 * (k + 1), max k 1, ?_⟩
  intro n hn
  have hk := (le_max_left k 1).trans hn
  have h1 := (le_max_right k 1).trans hn
  let s := n.sqrt + 1
  have hbig : n ≤ ((pins k) ∪ grid s).card := by
    refine (Nat.lt_succ_sqrt' n).le.trans ?_
    rw [← grid_card]
    exact card_le_card subset_union_right
  obtain ⟨X, hPX, hX, hcard⟩ := exists_subsuperset_card_eq
    (show pins k ⊆ pins k ∪ grid s from subset_union_left) (by simpa [pins_card] using hk) hbig
  refine ⟨X, hcard, ?_⟩
  rw [countSmallPoints]
  apply (pins_card k).ge.trans
  apply card_le_card
  intro p hp
  refine mem_filter.mpr ⟨hPX hp, ?_⟩
  obtain ⟨i, hi, rfl⟩ := mem_image.mp (show p ∈ (range k).image (fun i : ℕ => point i 0) from hp)
  have hsub : X.erase (point i 0) ⊆ pins k ∪ grid s := (erase_subset ..).trans hX
  have hle := card_le_card (image_subset_image (f := fun q => dist q (point i 0)) hsub)
  rw [image_union] at hle
  have h := hle.trans (card_union_le ..)
  have hd : distinctDistancesFrom X (point i 0) ≤ k + (2 * k + 1) * s := by
    unfold distinctDistancesFrom
    convert h.trans (Nat.add_le_add (card_image_le.trans (pins_card k).le)
      (grid_dist_card k s i (mem_range.mp hi))) using 1
    congr 1
    ext t
    simp
  have hs : (n.sqrt : ℝ) ≤ Real.sqrt n := Real.nat_sqrt_le_real_sqrt
  have ht : (1 : ℝ) ≤ Real.sqrt n := (Real.le_sqrt (by norm_num) (by positivity)).mpr (by
    simpa using (show (1 : ℝ) ≤ n by exact_mod_cast h1))
  have hd' : (distinctDistancesFrom X (point i 0) : ℝ) ≤
      (k : ℝ) + (2 * k + 1) * (n.sqrt + 1 : ℝ) := by exact_mod_cast hd
  nlinarith [mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ 2 * k + 1),
    mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg (α := ℝ) k)]

/-! ### Counting cells on a circle

A cell records the signs of a family of line and circle cuts. In the rational parametrization
of a circle, the sign of each cut is determined by a polynomial of degree at most two.
The roots, the intervals between them, and the omitted point give at most `4 |T| + 2` cells.
-/

open Polynomial

/-- Coefficients of a circle or line test. Its nonnegative locus selects one side of the cut. -/
private structure Cut where
  radial : ℝ
  xCoeff : ℝ
  yCoeff : ℝ
  constant : ℝ

private instance cutDecidableEq : DecidableEq Cut := Classical.decEq _

private def value (t : Cut) (q : Plane) :=
  t.radial * (q 0 ^ 2 + q 1 ^ 2) + t.xCoeff * q 0 + t.yCoeff * q 1 + t.constant

private def cell (T : Finset Cut) (q : Plane) := T.filter fun t => 0 ≤ value t q

private def rootRank (S : Finset ℝ) (x : ℝ) :=
  (S.filter (· < x)).card + (S.filter (· ≤ x)).card

private lemma rootRank_le (S : Finset ℝ) (x : ℝ) : rootRank S x ≤ 2 * S.card := by
  dsimp [rootRank]
  have := card_filter_le S (· < x)
  have := card_filter_le S (· ≤ x)
  omega

private lemma root_counts_mono (S : Finset ℝ) {x y : ℝ} (h : x ≤ y) :
    (S.filter (· < x)).card ≤ (S.filter (· < y)).card ∧
    (S.filter (· ≤ x)).card ≤ (S.filter (· ≤ y)).card :=
  ⟨card_le_card (monotone_filter_right S fun _ _ hx => hx.trans_le h),
    card_le_card (monotone_filter_right S fun _ _ hx => hx.trans h)⟩

private lemma rank_strict (S : Finset ℝ) {x y z : ℝ} (hz : z ∈ S) (hxy : x < y)
    (hx : x ≤ z) (hy : z ≤ y) : rootRank S x < rootRank S y := by
  obtain ⟨h₁, h₂⟩ := root_counts_mono S hxy.le
  dsimp [rootRank]
  rcases eq_or_lt_of_le hy with rfl | h
  · apply Nat.add_lt_add_of_le_of_lt h₁
    apply card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr
      ⟨monotone_filter_right S (fun _ _ h => h.trans hxy.le), ?_⟩
    intro he
    have hz' : z ∈ S.filter (· ≤ x) := he ▸ mem_filter.mpr ⟨hz, le_rfl⟩
    exact hxy.not_ge (mem_filter.mp hz').2
  · apply Nat.add_lt_add_of_lt_of_le _ h₂
    apply card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨monotone_filter_right S (fun _ _ h => h.trans hxy), ?_⟩
    intro he
    have hz' : z ∈ S.filter (· < x) := he ▸ mem_filter.mpr ⟨hz, h⟩
    exact hx.not_gt (mem_filter.mp hz').2

private lemma eval_sign_same {S : Finset ℝ} {p : ℝ[X]} (hS : p.roots.toFinset ⊆ S)
    {x y : ℝ} (he : rootRank S x = rootRank S y) : 0 ≤ p.eval x ↔ 0 ≤ p.eval y := by
  classical
  suffices aux : ∀ a b : ℝ, rootRank S a = rootRank S b →
      0 ≤ p.eval a → 0 ≤ p.eval b from ⟨aux x y he, aux y x he.symm⟩
  intro a b hab ha
  by_contra! hb
  have hp : p ≠ 0 := by rintro rfl; simp at hb
  rcases lt_trichotomy a b with h | rfl | h
  · obtain ⟨z, hz, hez⟩ := intermediate_value_Icc' h.le p.continuous.continuousOn ⟨hb.le, ha⟩
    have hmem : z ∈ S := hS (by simpa [mem_roots hp, IsRoot] using hez)
    exact hab.not_lt (rank_strict S hmem h hz.1 hz.2)
  · exact hb.not_ge ha
  · obtain ⟨z, hz, hez⟩ := intermediate_value_Icc h.le p.continuous.continuousOn ⟨hb.le, ha⟩
    have hmem : z ∈ S := hS (by simpa [mem_roots hp, IsRoot] using hez)
    exact hab.symm.not_lt (rank_strict S hmem h hz.1 hz.2)

private def offset (p : Plane) (r : ℝ) (t : Cut) :=
  value t p + t.radial * r ^ 2

private def slopeX (p : Plane) (t : Cut) := 2 * t.radial * p 0 + t.xCoeff

private def slopeY (p : Plane) (t : Cut) := 2 * t.radial * p 1 + t.yCoeff

private def cutPoly (p : Plane) (r : ℝ) (t : Cut) : ℝ[X] :=
  C (offset p r t - slopeX p t * r) * X ^ 2 + C (2 * slopeY p t * r) * X +
    C (offset p r t + slopeX p t * r)

private def parameter (p : Plane) (r : ℝ) (q : Plane) := (q 1 - p 1) / (r + (q 0 - p 0))

private lemma circle_sign (p q : Plane) (r : ℝ) (h : dist q p = r)
    (hne : r + (q 0 - p 0) ≠ 0) (t : Cut) :
    0 ≤ value t q ↔ 0 ≤ (cutPoly p r t).eval (parameter p r q) := by
  let x := q 0 - p 0
  let y := q 1 - p 1
  have hc : x ^ 2 + y ^ 2 = r ^ 2 := by rw [← h, dist_sq_coordinates]
  have hv : value t q = offset p r t + slopeX p t * x + slopeY p t * y := by
    dsimp [value, offset, slopeX, slopeY, x, y] at *
    linear_combination t.radial * hc
  rw [hv]
  simp only [cutPoly, eval_add, eval_mul, eval_C, eval_pow, eval_X, parameter]
  change _ ↔ 0 ≤ _ * (y / (r + x)) ^ 2 + _ * (y / (r + x)) + _
  have hid : (offset p r t - slopeX p t * r) * (y / (r + x)) ^ 2 +
      2 * slopeY p t * r * (y / (r + x)) + (offset p r t + slopeX p t * r) =
      (offset p r t + slopeX p t * x + slopeY p t * y) * (1 + (y / (r + x)) ^ 2) := by
    field_simp [show r + x ≠ 0 from hne]
    linear_combination -(slopeX p t * (r + x) + slopeY p t * y) * hc
  rw [hid, mul_nonneg_iff_of_pos_right (by positivity)]

private lemma card_coded {α β γ : Type*} [DecidableEq β] (S : Finset α) (f : α → β)
    (g : α → γ) (U : Finset γ) (hg : ∀ x ∈ S, g x ∈ U)
    (h : ∀ x ∈ S, ∀ y ∈ S, g x = g y → f x = f y) : (S.image f).card ≤ U.card := by
  classical
  have ex (v : S.image f) := mem_image.mp v.prop
  let rep (v : S.image f) := (ex v).choose
  have hrep (v : S.image f) : rep v ∈ S ∧ f (rep v) = v := (ex v).choose_spec
  apply card_le_card_of_injective (f := fun v => ⟨g (rep v), hg _ (hrep v).1⟩)
  intro v w eq
  have hvw := h _ (hrep v).1 _ (hrep w).1 (congrArg Subtype.val eq)
  exact Subtype.ext ((hrep v).2.symm.trans (hvw.trans (hrep w).2))

private lemma eq_of_coordinates {q z : Plane} (h0 : q 0 = z 0) (h1 : q 1 = z 1) : q = z := by
  ext i
  fin_cases i <;> assumption

private lemma circle_cells (T : Finset Cut) (P : Finset Plane) (p : Plane) (r : ℝ)
    (hc : ∀ q ∈ P, dist q p = r) : (P.image (cell T)).card ≤ 4 * T.card + 2 := by
  classical
  let S := T.biUnion fun t => (cutPoly p r t).roots.toFinset
  have hs : S.card ≤ T.card * 2 := by
    apply card_biUnion_le_card_mul
    intro t _
    exact (Multiset.toFinset_card_le _).trans ((card_roots' _).trans natDegree_quadratic_le)
  let code (q : Plane) := if r + (q 0 - p 0) = 0 then 2 * S.card + 1 else
    rootRank S (parameter p r q)
  refine (card_coded P (cell T) code (range (4 * T.card + 2)) ?_ ?_).trans (card_range _).le
  · intro q _
    have hle := rootRank_le S (parameter p r q)
    simp only [mem_range, code]
    split <;> omega
  · intro q hq z hz he
    have exc (u : Plane) (hu : u ∈ P) (h : r + (u 0 - p 0) = 0) : u 1 = p 1 := by
      have h' := dist_sq_coordinates u p
      rw [hc u hu] at h'
      rw [show u 0 - p 0 = -r by linarith] at h'
      nlinarith
    by_cases hq0 : r + (q 0 - p 0) = 0 <;> by_cases hz0 : r + (z 0 - p 0) = 0
    · rw [eq_of_coordinates (show q 0 = z 0 by linarith) ((exc q hq hq0).trans (exc z hz hz0).symm)]
    · simp only [code, hq0, ite_true, hz0, ite_false] at he
      have := rootRank_le S (parameter p r z)
      omega
    · simp only [code, hq0, ite_false, hz0, ite_true] at he
      have := rootRank_le S (parameter p r q)
      omega
    · simp only [code, hq0, ite_false, hz0, ite_false] at he
      apply filter_congr
      intro t ht
      rw [circle_sign p q r (hc q hq) hq0, circle_sign p z r (hc z hz) hz0]
      exact eval_sign_same (fun a ha => mem_biUnion.mpr ⟨t, ht, ha⟩) he

/-! ### Partition by distance ranks and sides of lines

Use two pins as anchors and place a circular cut at every `L`-th distance from each anchor.
Within one cell the two ranks modulo `L` determine both distances. The side of the line
through the anchors distinguishes the two possible intersections of their distance circles,
so the cell contains at most `L²` points. Including the line through every pair of pins
ensures that within each cell, the two distances to any distinct pair of pins determine the point.
-/

private def sideCut (a b : Plane) : Cut :=
  ⟨0, -(b 1 - a 1), b 0 - a 0, (b 1 - a 1) * a 0 - (b 0 - a 0) * a 1⟩

private def radialCut (a : Plane) (r : ℝ) : Cut :=
  ⟨1, -2 * a 0, -2 * a 1, a 0 ^ 2 + a 1 ^ 2 - r ^ 2⟩

private lemma radial_nonneg (a q : Plane) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ value (radialCut a r) q ↔ r ≤ dist q a := by
  rw [← sq_le_sq₀ hr dist_nonneg, dist_sq_coordinates]
  dsimp [value, radialCut]
  constructor <;> intro h <;> linarith only [h]

private lemma side_inj (a b q z : Plane) (hab : a ≠ b)
    (h₁ : dist q a = dist z a) (h₂ : dist q b = dist z b)
    (hsgn : 0 ≤ value (sideCut a b) q ↔ 0 ≤ value (sideCut a b) z) : q = z := by
  let dx := b 0 - a 0
  let dy := b 1 - a 1
  let x := q 0 - a 0
  let y := q 1 - a 1
  let u := z 0 - a 0
  let v := z 1 - a 1
  have hlen : x ^ 2 + y ^ 2 = u ^ 2 + v ^ 2 := by
    rw [← dist_sq_coordinates, ← dist_sq_coordinates, h₁]
  have hdot : dx * x + dy * y = dx * u + dy * v := by
    have h := congrArg (· ^ 2) h₂
    rw [dist_sq_coordinates, dist_sq_coordinates] at h
    dsimp [dx, dy, x, y, u, v] at *
    linear_combination (hlen - h) / 2
  have hcross : (dx * y - dy * x) ^ 2 = (dx * v - dy * u) ^ 2 := by
    linear_combination (dx ^ 2 + dy ^ 2) * hlen - (dx * x + dy * y + dx * u + dy * v) * hdot
  have hsign : 0 ≤ dx * y - dy * x ↔ 0 ≤ dx * v - dy * u := by
    dsimp [dx, dy, x, y, u, v, sideCut, value] at *
    convert hsgn using 2 <;> ring
  have hc : dx * y - dy * x = dx * v - dy * u := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hcross with he | he
    · exact he
    · by_cases hh : 0 ≤ dx * y - dy * x
      · have := hsign.mp hh
        linarith
      · have := mt hsign.mpr hh
        linarith
  have hd : dx ^ 2 + dy ^ 2 ≠ 0 := by
    intro he
    apply hab
    apply eq_of_coordinates <;> dsimp [dx, dy] at * <;> nlinarith [sq_nonneg dx, sq_nonneg dy]
  have hx : (dx ^ 2 + dy ^ 2) * (x - u) = 0 := by linear_combination dx * hdot - dy * hc
  have hy : (dx ^ 2 + dy ^ 2) * (y - v) = 0 := by linear_combination dy * hdot + dx * hc
  have := (mul_eq_zero.mp hx).resolve_left hd
  have := (mul_eq_zero.mp hy).resolve_left hd
  apply eq_of_coordinates <;> dsimp [x, y, u, v] at * <;> linarith

private def radii (X : Finset Plane) (a : Plane) := X.image fun q => dist q a

private lemma radii_card (X : Finset Plane) (a : Plane) :
    (radii X a).card ≤ distinctDistancesFrom X a + 1 := by
  classical
  unfold distinctDistancesFrom
  refine (card_le_card (t := insert 0 ((X.erase a).image fun q => dist q a)) ?_).trans ?_
  · rintro r hr
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hr
    by_cases he : q = a
    · simp [he]
    · exact mem_insert_of_mem (mem_image_of_mem _ (mem_erase.mpr ⟨he, hq⟩))
  · convert card_insert_le .. using 1
    congr 2
    ext
    simp

private def barriers (a : Plane) (S : Finset ℝ) (L : ℕ) : Finset Cut :=
  (range (S.card / L + 1)).image fun j => radialCut a
    (if hj : L * j < S.card then S.orderEmbOfFin rfl ⟨L * j, hj⟩ else 0)

private lemma barriers_card (a : Plane) (S : Finset ℝ) (L : ℕ) :
    (barriers a S L).card ≤ S.card / L + 1 := card_image_le.trans (card_range _).le

private def rankIn (S : Finset ℝ) (r : ℝ) : ℕ :=
  if h : r ∈ S then ((S.orderIsoOfFin rfl).symm ⟨r, h⟩).val else 0

private lemma rank_spec (S : Finset ℝ) (r : ℝ) (hr : r ∈ S) :
    ∃ i : Fin S.card, i.val = rankIn S r ∧ S.orderEmbOfFin rfl i = r := by
  refine ⟨(S.orderIsoOfFin rfl).symm ⟨r, hr⟩, by simp [rankIn, hr], ?_⟩
  simp only [← coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]

private lemma cell_bit {T : Finset Cut} {q z : Plane} (he : cell T q = cell T z)
    {t : Cut} (ht : t ∈ T) : 0 ≤ value t q ↔ 0 ≤ value t z := by
  simpa [cell, ht] using (show t ∈ cell T q ↔ t ∈ cell T z by rw [he])

private lemma block_dist {T : Finset Cut} {X : Finset Plane} {a q z : Plane} {L : ℕ}
    (hL : 0 < L) (hq : q ∈ X) (hz : z ∈ X) (hT : barriers a (radii X a) L ⊆ T)
    (hc : cell T q = cell T z)
    (he : rankIn (radii X a) (dist q a) % L = rankIn (radii X a) (dist z a) % L) :
    dist q a = dist z a := by
  let S := radii X a
  obtain ⟨i, hi, hi'⟩ := rank_spec S _ (mem_image_of_mem _ hq)
  obtain ⟨j, hj, hj'⟩ := rank_spec S _ (mem_image_of_mem _ hz)
  change rankIn S _ % L = rankIn S _ % L at he
  rw [← hi, ← hj] at he
  have monot {u v : Fin S.card} {p w : Plane} (hp : S.orderEmbOfFin rfl u = dist p a)
      (hw : S.orderEmbOfFin rfl v = dist w a) (hc' : cell T p = cell T w) :
      L * (v.val / L) ≤ u.val := by
    have hv := Nat.mul_div_le v.val L
    let b : Fin S.card := ⟨_, hv.trans_lt v.isLt⟩
    let r := S.orderEmbOfFin rfl b
    have hr : 0 ≤ r := by
      obtain ⟨_, _, eq⟩ := mem_image.mp (S.orderEmbOfFin_mem rfl b)
      change 0 ≤ (S.orderEmbOfFin rfl) b
      rw [← eq]
      exact dist_nonneg
    have hmem : radialCut a r ∈ T := by
      apply hT
      apply mem_image.mpr
      refine ⟨v.val / L, mem_range.mpr ?_, ?_⟩
      · exact Nat.lt_succ_of_le (Nat.div_le_div_right v.isLt.le)
      · simp only [show L * (v.val / L) < (radii X a).card from hv.trans_lt v.isLt, dite_true]
        rfl
    have hh := (cell_bit hc' hmem).mpr
    rw [radial_nonneg a _ hr, radial_nonneg a _ hr, ← hp, ← hw] at hh
    have hle := (S.orderEmbOfFin rfl).monotone (show b ≤ v from hv)
    exact (S.orderEmbOfFin rfl).le_iff_le.mp (hh hle)
  have huv := monot hi' hj' hc
  have hvu := monot hj' hi' hc.symm
  have cut (x : ℕ) : x < L * (x / L + 1) := by
    rw [Nat.mul_add_one]
    have := Nat.mod_add_div x L
    have := Nat.mod_lt x hL
    omega
  have hquot : i.val / L = j.val / L := by
    apply le_antisymm
    · by_contra! h
      exact (cut j.val).not_ge ((Nat.mul_le_mul_left L h).trans hvu)
    · by_contra! h
      exact (cut i.val).not_ge ((Nat.mul_le_mul_left L h).trans huv)
  have hij : i = j := by
    apply Fin.ext
    have h := Nat.mod_add_div i.val L
    rw [he, hquot, Nat.mod_add_div] at h
    exact h.symm
  exact hi'.symm.trans (hij ▸ hj')

private def cuts (K X : Finset Plane) (a b : Plane) (L : ℕ) : Finset Cut :=
  ((K ×ˢ K).image fun v => sideCut v.1 v.2) ∪
    (barriers a (radii X a) L ∪ barriers b (radii X b) L)

private lemma cell_size (K X : Finset Plane) {a b : Plane} (ha : a ∈ K) (hb : b ∈ K)
    (hne : a ≠ b) {L : ℕ} (hL : 0 < L) (c : Finset Cut) :
    (X.filter fun q => cell (cuts K X a b L) q = c).card ≤ L * L := by
  classical
  let g (p q : Plane) := rankIn (radii X p) (dist q p) % L
  refine (card_le_card_of_injOn (t := range L ×ˢ range L) (fun q => (g a q, g b q))
    (fun _ _ => mem_product.mpr ⟨mem_range.mpr (Nat.mod_lt _ hL), mem_range.mpr (Nat.mod_lt _ hL)⟩)
    ?_).trans (by simp)
  intro q hq z hz he
  obtain ⟨hq, hqc⟩ := mem_filter.mp hq
  obtain ⟨hz, hzc⟩ := mem_filter.mp hz
  have hc := hqc.trans hzc.symm
  exact side_inj a b q z hne
    (block_dist hL hq hz (subset_union_left.trans subset_union_right) hc (congrArg Prod.fst he))
    (block_dist hL hq hz (subset_union_right.trans subset_union_right) hc (congrArg Prod.snd he))
    (cell_bit hc (mem_union_left _ (mem_image_of_mem (fun v : Plane × Plane => sideCut v.1 v.2)
      (show (a, b) ∈ K ×ˢ K from mem_product.mpr ⟨ha, hb⟩))))

/-! ### Double counting pin–point incidences

For a fixed pin, points with a unique distance in their cell are bounded by the number of
radii times the number of cells per circle. For a fixed point, each pin counted as
repeated supplies a different partner in the same cell. Indeed, two pins sharing a partner
would give the same two distances to two points on the same side of their joining line.
-/

private def repeated (X : Finset Plane) (T : Finset Cut) (p q : Plane) : Prop :=
  ∃ z ∈ X, z ≠ q ∧ cell T z = cell T q ∧ dist z p = dist q p

open Classical in
private lemma single_count (X : Finset Plane) (T : Finset Cut) (p : Plane) :
    (X.filter fun q => ¬ repeated X T p q).card ≤ (4 * T.card + 2) * (radii X p).card := by
  classical
  let Y := X.filter fun q => ¬ repeated X T p q
  apply card_le_mul_card_image_of_maps_to (f := fun q => dist q p)
    (fun q hq => mem_image_of_mem _ (mem_filter.mp hq).1)
  intro r _
  let Z := Y.filter fun q => dist q p = r
  have hn : Set.InjOn (cell T) (Z : Set Plane) := by
    intro q hq z hz he
    by_contra hne
    obtain ⟨hq, hrq⟩ := mem_filter.mp hq
    obtain ⟨hz, hrz⟩ := mem_filter.mp hz
    exact (mem_filter.mp hz).2 ⟨q, (mem_filter.mp hq).1, hne, he, hrq.trans hrz.symm⟩
  exact (card_image_of_injOn hn).symm.le.trans
    (circle_cells T Z p r (fun q hq => (mem_filter.mp hq).2))

open Classical in
private lemma repeated_count (K X : Finset Plane) {a b : Plane} (ha : a ∈ K) (hb : b ∈ K)
    (hab : a ≠ b) {L : ℕ} (hL : 0 < L) (q : Plane) :
    (K.filter fun p => repeated X (cuts K X a b L) p q).card ≤ L * L := by
  classical
  let T := cuts K X a b L
  let J := K.filter fun p => repeated X T p q
  let rep (p : J) := ((mem_filter.mp p.prop).2).choose
  have spec (p : J) : rep p ∈ X ∧ rep p ≠ q ∧ cell T (rep p) = cell T q ∧
      dist (rep p) p = dist q p := ((mem_filter.mp p.prop).2).choose_spec
  refine (card_le_card_of_injective (s := J) (t := X.filter fun z => cell T z = cell T q)
    (f := fun p => ⟨rep p, mem_filter.mpr ⟨(spec p).1, (spec p).2.2.1⟩⟩) ?_).trans
    (cell_size K X ha hb hab hL _)
  intro p w he
  by_contra hne
  have hne' : p.val ≠ w.val := fun eq => hne (Subtype.ext eq)
  have hrep : rep p = rep w := congrArg Subtype.val he
  have hT : sideCut p w ∈ T := mem_union_left _ (mem_image.mpr
    ⟨(p.val, w.val), mem_product.mpr ⟨(mem_filter.mp p.prop).1, (mem_filter.mp w.prop).1⟩, rfl⟩)
  exact (spec p).2.1 (side_inj p w (rep p) q hne' (spec p).2.2.2
    (hrep ▸ (spec w).2.2.2) (cell_bit (spec p).2.2.1 hT))

private lemma count_inequality (K X : Finset Plane) {a b : Plane} (ha : a ∈ K) (hb : b ∈ K)
    (hab : a ≠ b) {L D : ℕ} (hL : 0 < L) (hD : ∀ p ∈ K, (radii X p).card ≤ D) :
    K.card * X.card ≤ K.card * ((4 * (cuts K X a b L).card + 2) * D) + X.card * (L * L) := by
  classical
  let T := cuts K X a b L
  let R := repeated X T
  have swap : (∑ p ∈ K, (X.filter (R p)).card) = ∑ q ∈ X, (K.filter fun p => R p q).card := by
    simp only [card_filter]
    rw [sum_comm]
  calc
    K.card * X.card = ∑ p ∈ K, ((X.filter fun q => ¬ R p q).card + (X.filter (R p)).card) := by
      simp [card_filter_add_card_filter_not, add_comm]
    _ = (∑ p ∈ K, (X.filter fun q => ¬ R p q).card) +
        ∑ q ∈ X, (K.filter fun p => R p q).card := by rw [sum_add_distrib, swap]
    _ ≤ _ := by
      apply Nat.add_le_add
      · apply sum_le_card_nsmul
        exact fun p hp => (single_count X T p).trans (Nat.mul_le_mul_left _ (hD p hp))
      · apply sum_le_card_nsmul
        exact fun q _ => repeated_count K X ha hb hab hL q

/-- For an admissible constant below `A`, take a configuration of square cardinality `m²`.
The pins use at most `m * (A + 1)` radii each. Choose `L` in terms of `A` so that at most
half of the points at each pin have a unique distance in their cell. The repeated incidences
then force `k ≤ 2 L²`. The square can be taken large enough to absorb all the line cuts. -/
private lemma many_pins_lower (A k : ℕ) (c : ℝ) (had : isAdmissibleBound k c)
    (hk : let L := 2 * (A + 1) * (8 * (A + 1) + 1); 2 * (L * L) + 1 ≤ k) : (A : ℝ) ≤ c := by
  classical
  by_contra! hc
  obtain ⟨N, hN⟩ := had
  let B := A + 1
  let L := 2 * B * (8 * B + 1)
  let s := N + 4 * k ^ 2 + 10
  let m := L * s
  have hB : 0 < B := Nat.succ_pos _
  have hL : 0 < L := by dsimp [L]; positivity
  have hs : 0 < s := by dsimp [s]; omega
  have hm : 0 < m := Nat.mul_pos hL hs
  have hlarge : N ≤ m ^ 2 := by
    calc N ≤ s := by dsimp [s]; omega
         _ ≤ m := Nat.le_mul_of_pos_left _ hL
         _ ≤ m ^ 2 := by nlinarith
  obtain ⟨X, hX, hpoints⟩ := hN (m ^ 2) hlarge
  obtain ⟨K, hK, hk'⟩ := exists_subset_card_eq hpoints
  have hD (p : Plane) (hp : p ∈ K) : (radii X p).card ≤ m * B := by
    have h := (mem_filter.mp (hK hp)).2
    change (distinctDistancesFrom X p : ℝ) < c * Real.sqrt ((m ^ 2 : ℕ) : ℝ) at h
    rw [Nat.cast_pow, Real.sqrt_sq (by positivity)] at h
    have hsmall : distinctDistancesFrom X p < A * m := by
      exact_mod_cast h.trans (mul_lt_mul_of_pos_right hc (Nat.cast_pos.mpr hm))
    refine (radii_card X p).trans ((Nat.succ_le_of_lt hsmall).trans ?_)
    dsimp [B]
    nlinarith
  change 2 * (L * L) + 1 ≤ k at hk
  have htwo : 1 < K.card := by rw [hk']; nlinarith
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp htwo
  let T := cuts K X a b L
  have hbars (p : Plane) (hp : p ∈ K) : (barriers p (radii X p) L).card ≤ s * B + 1 := by
    apply (barriers_card ..).trans
    have h := Nat.div_le_div_right (c := L) (hD p hp)
    simpa [m, Nat.mul_assoc, hL] using Nat.add_le_add_right h 1
  have hsize : T.card ≤ k ^ 2 + (2 * (s * B) + 2) := by
    have hside : ((K ×ˢ K).image fun v => sideCut v.1 v.2).card ≤ k ^ 2 :=
      card_image_le.trans (by simp [hk', pow_two])
    exact (card_union_le ..).trans (Nat.add_le_add hside ((card_union_le ..).trans
      ((Nat.add_le_add (hbars a ha) (hbars b hb)).trans (by omega))))
  have hcross : 4 * T.card + 2 ≤ (8 * B + 1) * s := by
    dsimp [s] at hsize ⊢
    nlinarith only [hsize, Nat.zero_le N]
  have hhalf : 2 * ((4 * T.card + 2) * (m * B)) ≤ m ^ 2 := by
    calc 2 * ((4 * T.card + 2) * (m * B)) ≤ 2 * (((8 * B + 1) * s) * (m * B)) := by gcongr
         _ = m ^ 2 := by dsimp [m, L]; ring
  have h := count_inequality K X ha hb hab hL hD
  change K.card * X.card ≤ K.card * ((4 * T.card + 2) * (m * B)) + X.card * (L * L) at h
  rw [hk', hX] at h
  nlinarith only [h, Nat.mul_le_mul_left k hhalf, Nat.mul_le_mul_right (m ^ 2) hk,
    Nat.pow_pos hm (n := 2)]

end

/--
**Erdős Problem 652 is true.** For a finite set $X$ of points in the Euclidean plane and
$x \in X$, let $R_X(x)$ be the number of distinct distances from $x$ to the other points of
$X$. For $k \in \mathbb{N}$ let $\alpha_k$ be the infimum of the reals $c$ for which there is
$N$ such that for every $n \ge N$ some set $X$ of exactly $n$ points in the plane has at least
$k$ points $x$ with $R_X(x) < c\sqrt{n}$ (an empty set or a set unbounded below is given
infimum $0$). Then $\alpha_k \to \infty$ as $k \to \infty$.

Mathialagan proved that for $2 \le m \le n^{1/3}$, some point of an $m$-point set determines
$\Omega(\sqrt{mn})$ distances to an $n$-point set; with Elekes's circle-grid construction this
gives $\alpha_k = \Theta(\sqrt{k})$.

Source: S. Mathialagan, On bipartite distinct distances in the plane,
Electronic Journal of Combinatorics 28(4) (2021) P4.33, arXiv:1912.01883,
https://arxiv.org/abs/1912.01883. Moved from `OpenConjectures/Geometry/ErdosProblem652`.
-/
theorem conjecture_holds : conjecture := by
  apply Filter.tendsto_atTop_atTop.mpr
  intro b
  obtain ⟨A, hA⟩ := exists_nat_ge b
  let L := 2 * (A + 1) * (8 * (A + 1) + 1)
  refine ⟨2 * (L * L) + 1, fun k hk => ?_⟩
  exact hA.trans (le_csInf (admissible_nonempty k) fun c hc => many_pins_lower A k c hc hk)

end MathlibExt.Geometry.ErdosProblem652Wanted
