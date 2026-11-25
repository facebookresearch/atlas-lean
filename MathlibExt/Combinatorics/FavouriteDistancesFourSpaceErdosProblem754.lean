/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Set.Card
import Mathlib.Geometry.Euclidean.Sphere.SecondInter

/-!
# Favourite distances in four dimensions

The minimum number of points at a favourite distance in a finite set in four-space is at most
half the size of the set plus an absolute constant.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.FavouriteDistancesFourSpaceErdosProblem754Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #754, https://www.erdosproblems.com/754 (status PROVED
(LEAN)). UnsolvedMath record UM-30007014 (`EP-754`), dataset ulamai/UnsolvedMath v1.8.0.

Points lie in `EuclideanSpace ℝ (Fin 4)`; "`f` points equidistant from `x`" is `f` points of `A` at
one distance `r(x) > 0` from `x`. The bound is stated for every nonempty `A` and every `f` attained,
so it bounds the maximum `f(n)` (for empty `A` every `f` would qualify vacuously).
-/

/-- **Statement of Erdős Problem 754.** This is the statement that there is a real constant $C$
such that for every nonempty finite set $A$ of points of the Euclidean space $\mathbb{R}^4$ and
every natural number $f$, if for every $x \in A$ there is a real number $r > 0$ such that at least
$f$ points of $A$ lie at distance $r$ from $x$, then $f \le |A|/2 + C$. Equivalently,
$f(n) \le n/2 + O(1)$, where $f(n)$ is the largest $f$ such that some set $A$ of $n \ge 1$ points of
$\mathbb{R}^4$ has, for every $x \in A$, at least $f$ points of $A$ at one common distance
$r(x) > 0$ from $x$. -/
def favouriteDistanceCountHalfPlusConstant : Prop :=
  ∃ C : ℝ, ∀ (A : Finset (EuclideanSpace ℝ (Fin 4))) (f : ℕ), A.Nonempty →
    (∀ x ∈ A, ∃ r : ℝ, 0 < r ∧ f ≤ {y | y ∈ A ∧ dist x y = r}.ncard) →
      (f : ℝ) ≤ A.card / 2 + C

open AffineSubspace EuclideanGeometry Finset Module
open scoped BigOperators RealInnerProductSpace

private abbrev Point := EuclideanSpace ℝ (Fin 4)

private theorem not_collinear_of_dist_eq {c x y z : Point} {r : ℝ}
    (hx : dist c x = r) (hy : dist c y = r) (hz : dist c z = r)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ¬ Collinear ℝ ({x, y, z} : Set Point) := by
  intro h
  let s : Sphere Point := ⟨c, r⟩
  have hxs : x ∈ s := mem_sphere.mpr ((dist_comm x c).trans hx)
  have hys : y ∈ s := mem_sphere.mpr ((dist_comm y c).trans hy)
  have hzs : z ∈ s := mem_sphere.mpr ((dist_comm z c).trans hz)
  have hy' := (s.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair hxs
    (right_mem_affineSpan_pair ℝ x y)).mpr hys
  have hz' := (s.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair hxs
    (h.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hxy)).mpr hzs
  exact hyz ((hy'.resolve_left hxy.symm).trans (hz'.resolve_left hxz.symm).symm)

open Classical in
private theorem card_filter_line_le (B : Finset Point) {c : Point} {r : ℝ}
    (hB : ∀ x ∈ B, dist c x = r) (a b : Point) :
    (B.filter (· ∈ line[ℝ, a, b])).card ≤ 2 := by
  by_contra! h
  obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ := two_lt_card.mp h
  rw [mem_filter] at hx hy hz
  exact not_collinear_of_dist_eq (hB x hx.1) (hB y hy.1) (hB z hz.1) hxy hxz hyz
    (collinear_triple_of_mem_affineSpan_pair hx.2 hy.2 hz.2)

private theorem not_collinear_of_two_lt_card {B : Finset Point} {c : Point} {r : ℝ}
    (hB : ∀ x ∈ B, dist c x = r) (hcard : 2 < B.card) : ¬ Collinear ℝ (B : Set Point) := by
  obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ := two_lt_card.mp hcard
  exact fun h ↦ not_collinear_of_dist_eq (hB x hx) (hB y hy) (hB z hz) hxy hxz hyz
    (h.subset (by simpa [Set.insert_subset_iff] using ⟨hx, hy, hz⟩))

private theorem affineSpan_le_bisector {S : Set Point} {y z : Point}
    (h : ∀ x ∈ S, dist x y = dist x z) :
    affineSpan ℝ S ≤ perpBisector y z :=
  affineSpan_le.mpr fun x hx ↦ mem_perpBisector_iff_dist_eq.mpr (h x hx)

private theorem coplanar_of_common_distances {S T : Set Point} (hS : ¬ Collinear ℝ S)
    (h : ∀ x ∈ S, ∀ y ∈ T, ∀ z ∈ T, dist x y = dist x z) : Coplanar ℝ T := by
  have horth : vectorSpan ℝ T ≤ (vectorSpan ℝ S)ᗮ := by
    rw [vectorSpan_def, Submodule.span_le]
    rintro _ ⟨z, hz, y, hy, rfl⟩
    have hdir := direction_le (affineSpan_le_bisector fun x hx ↦ h x hx y hy z hz)
    rw [direction_affineSpan, direction_perpBisector] at hdir
    exact (Submodule.mem_orthogonal' _ _).mpr fun w hw ↦
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp (hdir hw)
  have hdim := (vectorSpan ℝ S).finrank_add_finrank_orthogonal
  rw [finrank_euclideanSpace_fin] at hdim
  rw [coplanar_iff_finrank_le_two]
  have hT := Submodule.finrank_mono horth
  rw [collinear_iff_finrank_le_one, not_le] at hS
  omega

private theorem affineSpan_eq_of_coplanar {X S : Finset Point} {c : Point} {r : ℝ}
    (hXS : X ⊆ S) (hX : 2 < X.card) (hS : Coplanar ℝ (S : Set Point))
    (hsphere : ∀ x ∈ S, dist c x = r) :
    affineSpan ℝ (X : Set Point) = affineSpan ℝ (S : Set Point) := by
  have hsub : (X : Set Point) ⊆ S := coe_subset.mpr hXS
  have hle := affineSpan_mono ℝ hsub
  have hnoncol := not_collinear_of_two_lt_card (fun x hx ↦ hsphere x (hXS hx)) hX
  rw [collinear_iff_finrank_le_one, not_le] at hnoncol
  have hdimX : 2 ≤ finrank ℝ (affineSpan ℝ (X : Set Point)).direction := by
    rw [direction_affineSpan]
    omega
  have hdimS : finrank ℝ (affineSpan ℝ (S : Set Point)).direction ≤ 2 := by
    rw [direction_affineSpan]
    exact hS.finrank_le_two
  have hdir := direction_le hle
  have heq : (affineSpan ℝ (X : Set Point)).direction =
      (affineSpan ℝ (S : Set Point)).direction := by
    apply Submodule.eq_of_le_of_finrank_eq hdir
    have hmono := Submodule.finrank_mono hdir
    omega
  obtain ⟨x, hx⟩ := card_pos.mp (by omega : 0 < X.card)
  exact (eq_iff_direction_eq_of_mem (mem_affineSpan ℝ (mem_coe.mpr hx))
    (mem_affineSpan ℝ (mem_coe.mpr (hXS hx)))).mpr heq

/-- Average the number of incident targets over the possible centres. -/
private theorem exists_large_neighborhood {α β : Type*}
    (R : α → β → Prop) [∀ x y, Decidable (R x y)]
    {A : Finset α} {B : Finset β} (hA : A.Nonempty) (p : ℝ)
    (h : ∀ y ∈ B, (A.card : ℝ) * p ≤ (A.bipartiteBelow R y).card) :
    ∃ x ∈ A, (B.card : ℝ) * p ≤ (B.bipartiteAbove R x).card := by
  by_contra! hbad
  have hlt := card_nsmul_lt_card_nsmul_of_le_of_lt' R hA h hbad
  rw [nsmul_eq_mul, nsmul_eq_mul, mul_left_comm] at hlt
  exact (lt_irrefl _) hlt

/-- Bound the incidence count by splitting the targets into two sets. -/
private theorem incidence_bound {α β : Type*} [DecidableEq β]
    (R : α → β → Prop) [∀ x y, Decidable (R x y)]
    {A : Finset α} {B J : Finset β} (hJ : J ⊆ B) {f m k : ℝ}
    (hf : ∀ x ∈ A, f ≤ (B.bipartiteAbove R x).card)
    (hm : ∀ y ∈ B \ J, ((A.bipartiteBelow R y).card : ℝ) ≤ m)
    (hk : ∀ y ∈ J, ((A.bipartiteBelow R y).card : ℝ) ≤ k) :
    (A.card : ℝ) * f ≤ ((B \ J).card : ℝ) * m + (J.card : ℝ) * k := by
  calc
    _ ≤ ∑ x ∈ A, ((B.bipartiteAbove R x).card : ℝ) := by
      simpa only [nsmul_eq_mul] using A.card_nsmul_le_sum _ _ hf
    _ = ∑ y ∈ B, ((A.bipartiteBelow R y).card : ℝ) := by
      norm_cast
      exact sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow R
    _ = (∑ y ∈ B \ J, ((A.bipartiteBelow R y).card : ℝ)) +
        ∑ y ∈ J, ((A.bipartiteBelow R y).card : ℝ) := (sum_sdiff hJ).symm
    _ ≤ _ := by
      simp only [← nsmul_eq_mul]
      exact add_le_add ((B \ J).sum_le_card_nsmul _ _ hm) (J.sum_le_card_nsmul _ _ hk)

private theorem card_filter_not_ge {α : Type*} (B : Finset α) (p : α → Prop) [DecidablePred p] :
    (B.card : ℝ) ≤ ((B.filter fun x ↦ ¬ p x).card : ℝ) + (B.filter p).card := by
  have h := card_filter_add_card_filter_not (s := B) p
  rw [add_comm] at h
  exact_mod_cast h.ge

/-- Find three noncollinear centres with a common neighbourhood of size at least `A.card / 16384`.
This neighbourhood is coplanar and lies on each centre's sphere. -/
private theorem exists_coplanar_subset {A : Finset Point} (hA : A.Nonempty)
    (r : Point → ℝ) (f : ℝ) (hn : 32 ≤ (A.card : ℝ)) (hf : (A.card : ℝ) / 2 ≤ f)
    (hdeg : ∀ x ∈ A, f ≤ (A.filter fun y ↦ dist x y = r x).card) :
    ∃ S ⊆ A, (A.card : ℝ) / 16384 ≤ S.card ∧ Coplanar ℝ (S : Set Point) ∧
      ∃ c ρ, ∀ y ∈ S, dist c y = ρ := by
  classical
  let R (x y : Point) := dist x y = r x
  let n : ℝ := A.card
  let onLine (p : Point × Point) := A.filter (· ∈ line[ℝ, p.1, p.2])
  obtain ⟨p, _, hmax⟩ := (A ×ˢ A).exists_max_image (fun p ↦ (onLine p).card) (hA.product hA)
  let m : ℝ := (onLine p).card
  let B := A.filter (· ∉ line[ℝ, p.1, p.2])
  let H := B.filter fun y ↦ m + n / 8 ≤ ((A.bipartiteBelow R y).card : ℝ)
  have hBcard : (B.card : ℝ) + m = n := by
    have h := card_filter_add_card_filter_not (s := A) (· ∈ line[ℝ, p.1, p.2])
    rw [add_comm] at h
    change (B.card : ℝ) + ((onLine p).card : ℝ) = (A.card : ℝ)
    exact_mod_cast h
  have hBdeg (x) (hx : x ∈ A) : f - 2 ≤ (B.bipartiteAbove R x).card := by
    have heq : B.bipartiteAbove R x =
        (A.bipartiteAbove R x).filter (· ∉ line[ℝ, p.1, p.2]) := by
      ext y
      simp only [B, mem_bipartiteAbove, mem_filter, and_right_comm]
    have hline := card_filter_line_le (A.bipartiteAbove R x)
      (fun y hy ↦ ((mem_bipartiteAbove R).mp hy).2) p.1 p.2
    have hline' : (((A.bipartiteAbove R x).filter (· ∈ line[ℝ, p.1, p.2])).card : ℝ) ≤ 2 := by
      exact_mod_cast hline
    have hsplit := card_filter_not_ge (A.bipartiteAbove R x) (· ∈ line[ℝ, p.1, p.2])
    rw [← heq] at hsplit
    have hd : f ≤ (A.bipartiteAbove R x).card := hdeg x hx
    linarith
  -- Outside the most populated line, enough targets have many more than `m` incoming edges.
  have hH : n / 16 ≤ (H.card : ℝ) := by
    have hcount := incidence_bound R (A := A) (B := B) (J := H) (filter_subset _ _)
      hBdeg (m := m + n / 8) (k := n)
      (fun y hy ↦ by
        have hy' := (mem_sdiff.mp hy).2
        simp only [H, mem_filter, (mem_sdiff.mp hy).1, true_and, not_le] at hy'
        exact hy'.le)
      (fun y _ ↦ by
        change ((A.filter (R · y)).card : ℝ) ≤ (A.card : ℝ)
        exact_mod_cast card_filter_le A (R · y))
    have hm : 0 ≤ m := Nat.cast_nonneg _
    have hn' : 0 < n := by linarith
    have hsub : ((B \ H).card : ℝ) ≤ B.card := by exact_mod_cast card_le_card sdiff_subset
    have hupper := mul_le_mul_of_nonneg_right hsub (by positivity : 0 ≤ m + n / 8)
    have hprod := mul_nonneg (show 0 ≤ n from hn'.le)
      (show 0 ≤ n / 16 - 2 by linarith)
    have hprod' := mul_nonneg (show 0 ≤ n from hn'.le)
      (show 0 ≤ f - n / 2 by linarith)
    have hBn := mul_nonneg (show 0 ≤ n from hn'.le) hm
    rw [show (B.card : ℝ) = n - m by linarith] at hupper
    have hlower : 7 * n ^ 2 / 16 ≤ n * (f - 2) := by
      nlinarith only [hprod, hprod']
    have hbound : (n - m) * (m + n / 8) ≤ 3 * n ^ 2 / 8 := by
      nlinarith only [sq_nonneg (m - n / 2), hBn]
    have hfinal : n * (n / 16) ≤ n * (H.card : ℝ) := by
      change n * (f - 2) ≤ _ at hcount
      nlinarith only [hlower, hupper.trans hbound, hcount]
    exact le_of_mul_le_mul_left hfinal hn'
  have hI {y} (hy : y ∈ H) : m + n / 8 ≤ ((A.bipartiteBelow R y).card : ℝ) :=
    (mem_filter.mp hy).2
  -- Choose the centres in turn, averaging over the targets retained at each step.
  obtain ⟨a, ha, haCount⟩ := exists_large_neighborhood R hA (1 / 8)
    (B := H) (fun y hy ↦ by
      have hy' := hI hy
      have hm : 0 ≤ m := Nat.cast_nonneg _
      change n * (1 / 8) ≤ _
      linarith)
  let H₁ := H.bipartiteAbove R a
  let R₂ (b y : Point) := R b y ∧ b ≠ a
  have hR₂ {y} (hy : y ∈ H₁) : n * (1 / 16) ≤ (A.bipartiteBelow R₂ y).card := by
    have hy' := (mem_bipartiteAbove R).mp hy
    have haI : a ∈ A.bipartiteBelow R y := (mem_bipartiteBelow R).mpr ⟨ha, hy'.2⟩
    have heq : A.bipartiteBelow R₂ y = (A.bipartiteBelow R y).erase a := by
      ext b
      simp only [R₂, mem_bipartiteBelow, mem_erase]
      tauto
    have hcard : ((A.bipartiteBelow R₂ y).card : ℝ) + 1 =
        ((A.bipartiteBelow R y).card : ℝ) := by
      exact_mod_cast heq ▸ card_erase_add_one haI
    have hm : 0 ≤ m := Nat.cast_nonneg _
    linarith [hI hy'.1]
  obtain ⟨b, hb, hbCount⟩ := exists_large_neighborhood R₂ hA (1 / 16)
    (B := H₁) (fun y hy ↦ hR₂ hy)
  let H₂ := H₁.bipartiteAbove R₂ b
  let R₃ (c y : Point) := R c y ∧ c ∉ line[ℝ, a, b]
  have hR₃ {y} (hy : y ∈ H₂) : n * (1 / 8) ≤ (A.bipartiteBelow R₃ y).card := by
    have hy' := ((mem_bipartiteAbove R).mp ((mem_bipartiteAbove R₂).mp hy).1).1
    have hsplit := card_filter_not_ge (A.bipartiteBelow R y) (· ∈ line[ℝ, a, b])
    have hline : (((A.bipartiteBelow R y).filter (· ∈ line[ℝ, a, b])).card : ℝ) ≤ m := by
      change _ ≤ ((onLine p).card : ℝ)
      exact_mod_cast (card_le_card (show
        (A.bipartiteBelow R y).filter (· ∈ line[ℝ, a, b]) ⊆ onLine (a, b) from
          fun x hx ↦ mem_filter.mpr ⟨((mem_bipartiteBelow R).mp (mem_filter.mp hx).1).1,
            (mem_filter.mp hx).2⟩)).trans (hmax (a, b) (mem_product.mpr ⟨ha, hb⟩))
    rw [show (A.bipartiteBelow R y).filter (· ∉ line[ℝ, a, b]) =
        A.bipartiteBelow R₃ y by
          ext x
          simp only [R₃, mem_bipartiteBelow, mem_filter, and_assoc]] at hsplit
    linarith [hI hy']
  obtain ⟨c, _, hcCount⟩ := exists_large_neighborhood R₃ hA (1 / 8)
    (B := H₂) (fun y hy ↦ hR₃ hy)
  let S := H₂.bipartiteAbove R₃ c
  have hS : n / 16384 ≤ (S.card : ℝ) := by
    change (H.card : ℝ) * (1 / 8) ≤ (H₁.card : ℝ) at haCount
    change (H₁.card : ℝ) * (1 / 16) ≤ (H₂.card : ℝ) at hbCount
    change (H₂.card : ℝ) * (1 / 8) ≤ (S.card : ℝ) at hcCount
    linarith
  have hmem {y} (hy : y ∈ S) : y ∈ A ∧ R a y ∧ R b y ∧ R c y ∧
      b ≠ a ∧ c ∉ line[ℝ, a, b] := by
    simp only [S, H₂, H₁, H, B, R₂, R₃, mem_bipartiteAbove, mem_filter] at hy
    tauto
  have hSpos : 0 < (S.card : ℝ) := by linarith
  obtain ⟨y₀, hy₀⟩ := card_pos.mp (by exact_mod_cast hSpos : 0 < S.card)
  have hnoncol : ¬ Collinear ℝ ({a, b, c} : Set Point) := by
    rcases hmem hy₀ with ⟨_, _, _, _, hba, hcLine⟩
    exact fun h ↦ hcLine (h.mem_affineSpan_of_mem_of_ne (by simp) (by simp)
      (by simp) hba.symm)
  refine ⟨S, fun y hy ↦ (hmem hy).1, hS, coplanar_of_common_distances hnoncol ?_, a, r a,
    fun y hy ↦ (hmem hy).2.1⟩
  intro x hx y hy z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact (hmem hy).2.1.trans (hmem hz).2.1.symm
  · exact (hmem hy).2.2.1.trans (hmem hz).2.2.1.symm
  · exact (hmem hy).2.2.2.1.trans (hmem hz).2.2.2.1.symm

/-- A large coplanar cospherical set gives a second such set whose size is within a constant of the
minimum degree. The two sets have at most one point in common. -/
private theorem exists_coplanar_subset_of_large {A S : Finset Point} (hA : A.Nonempty)
    (r : Point → ℝ) (f : ℝ) (hn : 1048576 ≤ (A.card : ℝ))
    (hdeg : ∀ x ∈ A, f ≤ (A.filter fun y ↦ dist x y = r x).card)
    (hf : (A.card : ℝ) / 2 ≤ f) (hSA : S ⊆ A) (hS : (A.card : ℝ) / 16384 ≤ S.card)
    (hplane : Coplanar ℝ (S : Set Point)) (hsphere : ∃ c ρ, ∀ x ∈ S, dist c x = ρ) :
    ∃ T ⊆ A, f ≤ (T.card : ℝ) + 65536 ∧ (S ∩ T).card ≤ 1 ∧ Coplanar ℝ (T : Set Point) ∧
      ∃ c ρ, ∀ x ∈ T, dist c x = ρ := by
  classical
  let R (x y : Point) := dist x y = r x
  rcases hsphere with ⟨c, ρ, hρ⟩
  obtain ⟨y, _, hyCount⟩ := exists_large_neighborhood (fun y x ↦ R x y) hA (1 / 2)
    (B := S) (fun x hx ↦ by
      have hd := hdeg x (hSA hx)
      change (A.card : ℝ) * (1 / 2) ≤ ((A.filter fun y ↦ dist x y = r x).card : ℝ)
      linarith)
  let X := S.bipartiteBelow R y
  have hX : (S.card : ℝ) * (1 / 2) ≤ X.card := hyCount
  have hXcard : 2 < X.card := by
    apply_mod_cast (show (2 : ℝ) < (X.card : ℝ) by linarith)
  have hXp : 0 < (X.card : ℝ) := by positivity
  have hXS : X ⊆ S := filter_subset _ _
  have hspan := affineSpan_eq_of_coplanar hXS hXcard hplane hρ
  have hxy {x} (hx : x ∈ X) : dist x y = r x := ((mem_bipartiteBelow R).mp hx).2
  let T := A.filter fun z ↦ ∀ x ∈ X, R x z
  have hT : T ⊆ A := filter_subset _ _
  have hdist {z} (hz : z ∈ T) {x} (hx : x ∈ X) : dist x z = r x := (mem_filter.mp hz).2 x hx
  -- Three centres on the circle span its plane, so their bisector constraint holds on all of X.
  have hsmall {z} (hz : z ∈ A \ T) : (X.bipartiteBelow R z).card ≤ 2 := by
    by_contra! hlarge
    let W := X.bipartiteBelow R z
    have hWS : W ⊆ S := (filter_subset _ _).trans hXS
    have hspan' := affineSpan_eq_of_coplanar hWS hlarge hplane hρ
    have hbis : affineSpan ℝ (W : Set Point) ≤ perpBisector y z :=
      affineSpan_le_bisector fun x hx ↦
        (hxy ((mem_bipartiteBelow R).mp hx).1).trans ((mem_bipartiteBelow R).mp hx).2.symm
    rw [hspan', ← hspan] at hbis
    exact (mem_sdiff.mp hz).2 (mem_filter.mpr ⟨(mem_sdiff.mp hz).1, fun x hx ↦
      (mem_perpBisector_iff_dist_eq.mp (hbis (mem_affineSpan ℝ hx))).symm.trans (hxy hx)⟩)
  have hlarge : f ≤ (T.card : ℝ) + 65536 := by
    have hcount := incidence_bound R (A := X) (B := A) (m := 2) (k := (X.card : ℝ)) hT
      (fun x hx ↦ hdeg x (hSA (hXS hx)))
      (fun z hz ↦ by exact_mod_cast hsmall hz)
      (fun z _ ↦ by exact_mod_cast card_filter_le X (R · z))
    have hsub : ((A \ T).card : ℝ) ≤ A.card := by exact_mod_cast card_le_card sdiff_subset
    have hbudget : (A.card : ℝ) * 2 ≤ (X.card : ℝ) * 65536 := by linarith
    have hmul : (X.card : ℝ) * (f - T.card) ≤ (X.card : ℝ) * 65536 := by
      linarith only [hbudget, hcount, hsub,
        mul_comm (X.card : ℝ) (T.card : ℝ)]
    linarith [le_of_mul_le_mul_left hmul hXp]
  have hoverlap : (S ∩ T).card ≤ 1 := by
    rw [card_le_one]
    intro u hu v hv
    have hu' := mem_inter.mp hu
    have hv' := mem_inter.mp hv
    apply left_mem_perpBisector.mp
    have hbis : affineSpan ℝ (X : Set Point) ≤ perpBisector u v :=
      affineSpan_le_bisector fun x hx ↦ (hdist hu'.2 hx).trans (hdist hv'.2 hx).symm
    rw [hspan] at hbis
    exact hbis (mem_affineSpan ℝ hu'.1)
  obtain ⟨x, hx⟩ := card_pos.mp (by omega : 0 < X.card)
  have hnoncol := not_collinear_of_two_lt_card (fun x hx ↦ hρ x (hXS hx)) hXcard
  exact ⟨T, hT, hlarge, hoverlap, coplanar_of_common_distances hnoncol
    (fun x hx y hy z hz ↦ (hdist hy hx).trans (hdist hz hx).symm), x, r x,
    fun y hy ↦ hdist hy hx⟩

/--
**Erdős Problem 754: favourite distances in $\mathbb{R}^4$.** There is a real constant $C$ such
that for every nonempty finite set $A$ of points of the Euclidean space $\mathbb{R}^4$ and every
natural number $f$, if for every $x \in A$ there is a real number $r > 0$ such that at least $f$
points of $A$ lie at distance $r$ from $x$, then $f \le |A|/2 + C$.

Swanepoel proved that for every finite $A \subseteq \mathbb{R}^4$ with $|A| = n$ and every choice
of distances $r(x) > 0$, the number of pairs $(x, y)$ of points of $A$ with $|x - y| = r(x)$ is at
most $n^2/2 + O(n)$, which gives this bound.

Source: T. F. Bloom, Erdős Problems, Problem #754, https://www.erdosproblems.com/754 (status PROVED
(LEAN)); resolution: K. J. Swanepoel, Favourite distances in high dimensions, Thirty Essays on
Geometric Graph Theory (2013), 499-519, abstract of arXiv:1108.4817: f_d(n) = max ∑_{x ∈ S} e_r(x,
S) = (1 - 1/⌊d/2⌋) n² + Θ(n) for even d (n²/2 + O(n) for d = 4); erdosproblems.com/754: proved by
Swanepoel (Avis, Erdős and Pach had n/2 + 2 ≤ f(n) ≤ (1 + o(1)) n/2),
https://arxiv.org/abs/1108.4817.
-/
theorem favouriteDistanceCountHalfPlusConstant_holds :
    favouriteDistanceCountHalfPlusConstant := by
  classical
  refine ⟨1048576, fun A f hA hf ↦ ?_⟩
  let r (x : Point) : ℝ := if hx : x ∈ A then (hf x hx).choose else 1
  have hdeg (x) (hx : x ∈ A) : (f : ℝ) ≤ (A.filter fun y ↦ dist x y = r x).card := by
    have hcard := (hf x hx).choose_spec.2
    have hr : r x = (hf x hx).choose := dite_eq_left hx
    have hset : ({y | y ∈ A ∧ dist x y = r x} : Set Point) =
        ((A.filter fun y ↦ dist x y = r x) : Set Point) := (coe_filter _ _).symm
    rw [← hr, hset, Set.ncard_coe_finset] at hcard
    exact_mod_cast hcard
  obtain ⟨x, hx⟩ := hA
  have hfn : (f : ℝ) ≤ A.card :=
    (hdeg x hx).trans (by exact_mod_cast card_filter_le A _)
  by_cases hn : 1048576 ≤ (A.card : ℝ)
  · by_cases hf' : (A.card : ℝ) / 2 ≤ f
    · obtain ⟨S, hSA, hS, hSplane, hSsphere⟩ :=
        exists_coplanar_subset ⟨x, hx⟩ r f (by linarith) hf' hdeg
      obtain ⟨T, hTA, hT, _, hTplane, hTsphere⟩ :=
        exists_coplanar_subset_of_large ⟨x, hx⟩ r f hn hdeg hf' hSA hS hSplane hSsphere
      have hTsize : (A.card : ℝ) / 16384 ≤ T.card := by linarith
      obtain ⟨U, hUA, hU, hTU, _, _⟩ :=
        exists_coplanar_subset_of_large ⟨x, hx⟩ r f hn hdeg hf' hTA hTsize hTplane hTsphere
      have hcard : (T.card : ℝ) + U.card ≤ (A.card : ℝ) + 1 := by
        exact_mod_cast (by
          have hsub := card_le_card (union_subset hTA hUA)
          have hsum := card_union_add_card_inter T U
          omega : T.card + U.card ≤ A.card + 1)
      linarith
    · linarith
  · linarith

end MathlibExt.Combinatorics.FavouriteDistancesFourSpaceErdosProblem754Wanted
