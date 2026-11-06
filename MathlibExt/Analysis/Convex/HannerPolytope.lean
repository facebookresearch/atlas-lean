/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Hanner polytopes
-/
module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.Join
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import MathlibExt.Geometry.Convex.CubeCovering

@[expose] public section

open Set

namespace MetaMathlibExt

/-- **Centered unit segment.** The centered unit segment is the closed unit ball
$\{x \in \mathbb{R}^1 : \|x\| \le 1\}$, that is, the segment $[-1, 1]$. It is the
one-dimensional leaf in the recursive definition of Hanner polytopes. -/
def hannerUnitSegment : Set (EuclideanSpace ℝ (Fin 1)) :=
  Metric.closedBall 0 1

/-- **$\ell_\infty$ sum of bodies.** For sets $K \subseteq \mathbb{R}^m$ and
$L \subseteq \mathbb{R}^n$, the $\ell_\infty$ sum of $K$ and $L$ is the set of points of
$\mathbb{R}^{m+n}$ whose first $m$ coordinates form a point of $K$ and whose last $n$
coordinates form a point of $L$; that is, the product $K \times L$ under the identification
$\mathbb{R}^{m+n} = \mathbb{R}^m \times \mathbb{R}^n$. -/
noncomputable def hannerInfinitySum {m n : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin m)))
    (L : Set (EuclideanSpace ℝ (Fin n))) :
    Set (EuclideanSpace ℝ (Fin (m + n))) :=
  EuclideanSpace.finAddEquivProd.symm.toLinearEquiv '' (K ×ˢ L)

/-- **$\ell_1$ sum of bodies.** For sets $K \subseteq \mathbb{R}^m$ and $L \subseteq \mathbb{R}^n$,
the $\ell_1$ sum of $K$ and $L$ is the convex hull in $\mathbb{R}^{m+n}$ of
$(K \times \{0\}) \cup (\{0\} \times L)$, where $\mathbb{R}^{m+n}$ is identified with
$\mathbb{R}^m \times \mathbb{R}^n$ by splitting off the first $m$ coordinates. -/
noncomputable def hannerOneSum {m n : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin m)))
    (L : Set (EuclideanSpace ℝ (Fin n))) :
    Set (EuclideanSpace ℝ (Fin (m + n))) :=
  EuclideanSpace.finAddEquivProd.symm.toLinearEquiv ''
    convexHull ℝ ((K ×ˢ ({0} : Set (EuclideanSpace ℝ (Fin n)))) ∪
      (({0} : Set (EuclideanSpace ℝ (Fin m))) ×ˢ L))

/-- **Hanner polytopes.** For $K \subseteq \mathbb{R}^m$ and $L \subseteq \mathbb{R}^n$, identify
$\mathbb{R}^{m+n}$ with $\mathbb{R}^m \times \mathbb{R}^n$ by splitting off the first $m$
coordinates; the $\ell_\infty$ sum of $K$ and $L$ is $K \times L$, and their $\ell_1$ sum is the
convex hull of $(K \times \{0\}) \cup (\{0\} \times L)$, both viewed as subsets of
$\mathbb{R}^{m+n}$. The Hanner polytopes are the smallest family of subsets of the Euclidean
spaces $\mathbb{R}^n$ such that: the unit segment $[-1, 1] \subseteq \mathbb{R}^1$ is a Hanner
polytope; if $K \subseteq \mathbb{R}^n$ is a Hanner polytope and
$e \colon \mathbb{R}^n \to \mathbb{R}^n$ is an invertible linear map, then $e(K)$ is a Hanner
polytope; and if $K \subseteq \mathbb{R}^m$ and $L \subseteq \mathbb{R}^n$ are Hanner polytopes
with $m, n > 0$, then their $\ell_\infty$ sum and their $\ell_1$ sum are Hanner polytopes. -/
inductive IsHannerPolytope : {n : ℕ} → Set (EuclideanSpace ℝ (Fin n)) → Prop
  | unitSegment : IsHannerPolytope hannerUnitSegment
  | linearImage {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
      (hK : IsHannerPolytope K)
      (e : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n)) :
      IsHannerPolytope (e '' K)
  | infinitySum {m n : ℕ} {K : Set (EuclideanSpace ℝ (Fin m))}
      {L : Set (EuclideanSpace ℝ (Fin n))}
      (hm : 0 < m) (hn : 0 < n)
      (hK : IsHannerPolytope K) (hL : IsHannerPolytope L) :
      IsHannerPolytope (hannerInfinitySum K L)
  | oneSum {m n : ℕ} {K : Set (EuclideanSpace ℝ (Fin m))}
      {L : Set (EuclideanSpace ℝ (Fin n))}
      (hm : 0 < m) (hn : 0 < n)
      (hK : IsHannerPolytope K) (hL : IsHannerPolytope L) :
      IsHannerPolytope (hannerOneSum K L)

/-- **Hanner cube.** For $n \in \mathbb{N}$, the Hanner cube $C_n \subseteq \mathbb{R}^{n+1}$ is
defined by recursion on $n$: $C_0$ is the centered unit segment $[-1, 1] \subseteq \mathbb{R}^1$,
and $C_{n+1} \subseteq \mathbb{R}^{n+2}$ is the $\ell_\infty$ sum of $C_n$ and the centered
unit segment. -/
noncomputable def hannerCube : (n : ℕ) → Set (EuclideanSpace ℝ (Fin (n + 1)))
  | 0 => hannerUnitSegment
  | n + 1 => hannerInfinitySum (hannerCube n) hannerUnitSegment

/-- **Hanner cross-polytope.** For $n \in \mathbb{N}$, the Hanner cross-polytope
$P_n \subseteq \mathbb{R}^{n+1}$ is defined by recursion on $n$: $P_0$ is the centered unit
segment $[-1, 1] \subseteq \mathbb{R}^1$, and $P_{n+1} \subseteq \mathbb{R}^{n+2}$ is the
$\ell_1$ sum of $P_n$ and the centered unit segment. -/
noncomputable def hannerCrossPolytope : (n : ℕ) → Set (EuclideanSpace ℝ (Fin (n + 1)))
  | 0 => hannerUnitSegment
  | n + 1 => hannerOneSum (hannerCrossPolytope n) hannerUnitSegment

/-- Every recursively constructed coordinate cube is a Hanner polytope. -/
theorem hannerCube_isHannerPolytope (n : ℕ) : IsHannerPolytope (hannerCube n) := by
  induction n with
  | zero => exact .unitSegment
  | succ n ih => exact .infinitySum (Nat.succ_pos n) Nat.zero_lt_one ih .unitSegment

/-- Every recursively constructed coordinate cross-polytope is a Hanner polytope. -/
theorem hannerCrossPolytope_isHannerPolytope (n : ℕ) :
    IsHannerPolytope (hannerCrossPolytope n) := by
  induction n with
  | zero => exact .unitSegment
  | succ n ih => exact .oneSum (Nat.succ_pos n) Nat.zero_lt_one ih .unitSegment

/-- **Membership in the Hanner unit segment.** A point $x \in \mathbb{R}^1$ lies in the Hanner
unit segment if and only if every coordinate $x_i$ of $x$ satisfies $|x_i| \le 1$. -/
theorem mem_hannerUnitSegment_iff (x : EuclideanSpace ℝ (Fin 1)) :
    x ∈ hannerUnitSegment ↔ ∀ i, |x i| ≤ 1 := by
  rw [hannerUnitSegment, Metric.mem_closedBall, dist_zero_right, PiLp.norm_eq_sum]
  · simp only [ENNReal.toReal_ofNat, Fintype.sum_unique, Real.norm_eq_abs]
    rw [← Real.sqrt_eq_rpow, Real.rpow_two, Real.sqrt_sq_eq_abs, abs_abs]
    constructor
    · intro h i
      simpa [Subsingleton.elim i (0 : Fin 1), Subsingleton.elim default (0 : Fin 1)] using h
    · intro h
      simpa [Subsingleton.elim default (0 : Fin 1)] using h 0
  · norm_num

/-- **Membership in the $\ell_\infty$ Hanner sum.** Let $K \subseteq \mathbb{R}^m$ and
$L \subseteq \mathbb{R}^n$. A point $x \in \mathbb{R}^{m+n}$ lies in the $\ell_\infty$ Hanner
sum of $K$ and $L$ if and only if $(x_1, \dots, x_m) \in K$ and
$(x_{m+1}, \dots, x_{m+n}) \in L$. -/
theorem mem_hannerInfinitySum_iff {m n : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin m))} {L : Set (EuclideanSpace ℝ (Fin n))}
    (x : EuclideanSpace ℝ (Fin (m + n))) :
    x ∈ hannerInfinitySum K L ↔
      (EuclideanSpace.finAddEquivProd x).1 ∈ K ∧
        (EuclideanSpace.finAddEquivProd x).2 ∈ L := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    simpa using hp
  · intro hx
    exact ⟨EuclideanSpace.finAddEquivProd x, hx,
      EuclideanSpace.finAddEquivProd.symm_apply_apply x⟩

/-- **The Hanner cube is the coordinate cube.** For every $n \in \mathbb{N}$, the Hanner cube
$C_n \subseteq \mathbb{R}^{n+1}$ equals the coordinate cube
$\{x \in \mathbb{R}^{n+1} : -1 \le x_i \le 1 \text{ for every } i\} = [-1, 1]^{n+1}$. -/
theorem hannerCube_eq_coordinateCube (n : ℕ) :
    hannerCube n = ConvexCovering.coordinateCube (n + 1) := by
  rw [ConvexCovering.coordinateCube_eq_absSet]
  induction n with
  | zero =>
      ext x
      exact mem_hannerUnitSegment_iff x
  | succ n ih =>
      ext x
      rw [hannerCube, mem_hannerInfinitySum_iff, ih, mem_hannerUnitSegment_iff]
      change ((∀ i : Fin (n + 1), |(EuclideanSpace.finAddEquivProd x).1 i| ≤ 1) ∧
        (∀ j : Fin 1, |(EuclideanSpace.finAddEquivProd x).2 j| ≤ 1)) ↔
          ∀ k : Fin (n + 1 + 1), |x k| ≤ 1
      constructor
      · rintro ⟨hl, hr⟩
        exact Fin.addCases (fun i => by simpa using hl i) (fun j => by simpa using hr j)
      · intro h
        exact ⟨fun i => by simpa using h (Fin.castAdd 1 i),
          fun j => by simpa using h (Fin.natAdd (n + 1) j)⟩

/-- **Hanner polytopes live in positive dimension.** If $K \subseteq \mathbb{R}^n$ is a Hanner
polytope, then $0 < n$. -/
theorem IsHannerPolytope.dimension_pos {n : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsHannerPolytope K) : 0 < n := by
  induction hK with
  | unitSegment => exact Nat.zero_lt_one
  | linearImage hK _ ih => exact ih
  | infinitySum hm _ _ _ _ _ => exact Nat.add_pos_left hm _
  | oneSum hm _ _ _ _ _ => exact Nat.add_pos_left hm _

/-- Negation commutes with the image of a real linear equivalence. -/
private theorem neg_image_linearEquiv {E F : Type*} [AddCommGroup E] [AddCommGroup F]
    [Module ℝ E] [Module ℝ F] (e : E ≃ₗ[ℝ] F) (K : Set E) :
    -(e '' K) = e '' (-K) := by
  rw [← Set.image_neg_eq_neg, ← Set.image_neg_eq_neg, Set.image_image, Set.image_image]
  congr 1
  funext x
  exact (e.map_neg x).symm

private theorem neg_mem_iff_of_neg_eq_self {E : Type*} [AddCommGroup E]
    {K : Set E} (hK : -K = K) {x : E} : -x ∈ K ↔ x ∈ K :=
  (Set.mem_neg (s := K) (a := x)).symm.trans (by rw [hK])

/-- **Hanner polytopes are centrally symmetric.** Every Hanner polytope $K$ is centrally
symmetric about the origin: $-K = K$. -/
theorem IsHannerPolytope.neg_eq_self {n : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsHannerPolytope K) : -K = K := by
  induction hK with
  | unitSegment =>
      ext x
      simp [hannerUnitSegment, Metric.mem_closedBall]
  | linearImage hK e ih =>
      rw [neg_image_linearEquiv, ih]
  | infinitySum hm hn hK hL ihK ihL =>
      rw [hannerInfinitySum, neg_image_linearEquiv, Set.neg_prod, ihK, ihL]
  | oneSum hm hn hK hL ihK ihL =>
      rw [hannerOneSum, neg_image_linearEquiv, ← convexHull_neg]
      congr 2
      ext x
      rcases x with ⟨x, y⟩
      simp only [Set.mem_neg, Set.mem_union, Set.mem_prod, Set.mem_singleton_iff]
      change ((-x ∈ _ ∧ -y = 0) ∨ (-x = 0 ∧ -y ∈ _)) ↔
        ((x ∈ _ ∧ y = 0) ∨ (x = 0 ∧ y ∈ _))
      rw [neg_mem_iff_of_neg_eq_self ihK, neg_mem_iff_of_neg_eq_self ihL]
      simp

/-- **Negation preserves membership in a Hanner polytope.** For every Hanner polytope
$K \subseteq \mathbb{R}^n$ and every $x \in \mathbb{R}^n$, $-x \in K$ if and only if $x \in K$. -/
theorem IsHannerPolytope.neg_mem_iff {n : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsHannerPolytope K)
    {x : EuclideanSpace ℝ (Fin n)} : -x ∈ K ↔ x ∈ K :=
  neg_mem_iff_of_neg_eq_self hK.neg_eq_self

/-- **Hanner polytopes are convex.** Every Hanner polytope $K \subseteq \mathbb{R}^n$ is
convex. -/
theorem IsHannerPolytope.convex {n : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsHannerPolytope K) : Convex ℝ K := by
  induction hK with
  | unitSegment => exact convex_closedBall 0 1
  | linearImage hK e ih => exact ih.linear_image e.toLinearMap
  | infinitySum hm hn hK hL ihK ihL =>
      exact (ihK.prod ihL).linear_image
        EuclideanSpace.finAddEquivProd.symm.toLinearEquiv.toLinearMap
  | oneSum hm hn hK hL ihK ihL =>
      exact (convex_convexHull ℝ _).linear_image
        EuclideanSpace.finAddEquivProd.symm.toLinearEquiv.toLinearMap

/-- **Hanner polytopes contain the origin.** The origin belongs to every Hanner polytope. -/
theorem IsHannerPolytope.zero_mem {n : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsHannerPolytope K) : 0 ∈ K := by
  induction hK with
  | unitSegment => simp [hannerUnitSegment]
  | linearImage hK e ih => exact ⟨0, ih, by simp⟩
  | infinitySum hm hn hK hL ihK ihL => exact ⟨(0, 0), ⟨ihK, ihL⟩, by simp⟩
  | oneSum hm hn hK hL ihK ihL =>
      refine ⟨(0, 0), subset_convexHull ℝ _ ?_, by simp⟩
      exact Or.inl ⟨ihK, rfl⟩

private theorem isCompact_convexJoin {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {K L : Set E} (hK : IsCompact K) (hL : IsCompact L) :
    IsCompact (convexJoin ℝ K L) := by
  let f : ℝ × (E × E) → E := fun p => AffineMap.lineMap p.2.1 p.2.2 p.1
  have hf : Continuous f := by fun_prop
  have hdomain : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ (K ×ˢ L)) :=
    isCompact_Icc.prod (hK.prod hL)
  have himage : f '' (Set.Icc (0 : ℝ) 1 ×ˢ (K ×ˢ L)) = convexJoin ℝ K L := by
    ext z
    constructor
    · rintro ⟨⟨t, a, b⟩, ⟨ht, ha, hb⟩, rfl⟩
      exact mem_convexJoin.mpr ⟨a, ha, b, hb, lineMap_mem_segment ℝ a b ht⟩
    · intro hz
      obtain ⟨a, ha, b, hb, hz⟩ := mem_convexJoin.mp hz
      rw [segment_eq_image_lineMap] at hz
      obtain ⟨t, ht, rfl⟩ := hz
      exact ⟨⟨t, a, b⟩, ⟨ht, ha, hb⟩, rfl⟩
  rw [← himage]
  exact hdomain.image hf

private theorem isCompact_hannerOneSum {m n : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin m))} {L : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact K) (hL : IsCompact L) (hKconvex : Convex ℝ K)
    (hLconvex : Convex ℝ L) (hK0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ K)
    (hL0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ L) : IsCompact (hannerOneSum K L) := by
  have hK0compact : IsCompact (K ×ˢ ({0} : Set (EuclideanSpace ℝ (Fin n)))) :=
    hK.prod isCompact_singleton
  have h0Lcompact : IsCompact (({0} : Set (EuclideanSpace ℝ (Fin m))) ×ˢ L) :=
    isCompact_singleton.prod hL
  have hK0convex : Convex ℝ (K ×ˢ ({0} : Set (EuclideanSpace ℝ (Fin n)))) :=
    hKconvex.prod (convex_singleton 0)
  have h0Lconvex : Convex ℝ (({0} : Set (EuclideanSpace ℝ (Fin m))) ×ˢ L) :=
    (convex_singleton 0).prod hLconvex
  have hK0ne : (K ×ˢ ({0} : Set (EuclideanSpace ℝ (Fin n)))).Nonempty :=
    ⟨(0, 0), hK0, rfl⟩
  have h0Lne : (({0} : Set (EuclideanSpace ℝ (Fin m))) ×ˢ L).Nonempty :=
    ⟨(0, 0), rfl, hL0⟩
  rw [hannerOneSum, hK0convex.convexHull_union h0Lconvex hK0ne h0Lne]
  exact (isCompact_convexJoin hK0compact h0Lcompact).image
    EuclideanSpace.finAddEquivProd.symm.continuous

/-- **Hanner polytopes are compact.** Every Hanner polytope is compact. -/
theorem IsHannerPolytope.isCompact {n : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsHannerPolytope K) : IsCompact K := by
  induction hK with
  | unitSegment => exact isCompact_closedBall 0 1
  | linearImage hK e ih => exact ih.image e.toContinuousLinearEquiv.continuous
  | infinitySum hm hn hK hL ihK ihL =>
      exact (ihK.prod ihL).image EuclideanSpace.finAddEquivProd.symm.continuous
  | oneSum hm hn hK hL ihK ihL =>
      exact isCompact_hannerOneSum ihK ihL hK.convex hL.convex hK.zero_mem hL.zero_mem

private theorem half_smul_prod_subset_convexHull_axes {E F : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (K : Set E) (L : Set F) :
    (fun p : E × F => (⅟2 : ℝ) • p) '' (K ×ˢ L) ⊆
      convexHull ℝ ((K ×ˢ ({0} : Set F)) ∪ (({0} : Set E) ×ˢ L)) := by
  intro z hz
  obtain ⟨p, hp, rfl⟩ := hz
  have hmid := segment_subset_convexHull
    (show (p.1, (0 : F)) ∈ (K ×ˢ ({0} : Set F)) ∪ (({0} : Set E) ×ˢ L) from
      Or.inl ⟨hp.1, rfl⟩)
    (show ((0 : E), p.2) ∈ (K ×ˢ ({0} : Set F)) ∪ (({0} : Set E) ×ˢ L) from
      Or.inr ⟨rfl, hp.2⟩)
    (midpoint_mem_segment (𝕜 := ℝ) ((p.1, (0 : F))) (((0 : E), p.2)))
  simpa [midpoint_eq_smul_add] using hmid

private theorem zero_mem_interior_linearEquiv_image {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (e : E ≃ₗ[ℝ] F) {K : Set E} (hK : (0 : E) ∈ interior K) :
    (0 : F) ∈ interior (e '' K) := by
  have hi : (0 : F) ∈ e.toContinuousLinearEquiv '' interior K :=
    ⟨0, hK, by simp⟩
  have := e.toContinuousLinearEquiv.isOpenMap.image_interior_subset K hi
  simpa using this

private theorem zero_mem_interior_hannerOneSum {m n : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin m))} {L : Set (EuclideanSpace ℝ (Fin n))}
    (hK : (0 : EuclideanSpace ℝ (Fin m)) ∈ interior K)
    (hL : (0 : EuclideanSpace ℝ (Fin n)) ∈ interior L) :
    (0 : EuclideanSpace ℝ (Fin (m + n))) ∈ interior (hannerOneSum K L) := by
  let half :
      (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) ≃ₜ
        (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) :=
    Homeomorph.smulOfNeZero (⅟2 : ℝ) (by norm_num)
  have hprod :
      ((0 : EuclideanSpace ℝ (Fin m)), (0 : EuclideanSpace ℝ (Fin n))) ∈
        interior (K ×ˢ L) := by
    rw [interior_prod_eq]
    exact ⟨hK, hL⟩
  have hhalf :
      ((0 : EuclideanSpace ℝ (Fin m)), (0 : EuclideanSpace ℝ (Fin n))) ∈
        interior (half '' (K ×ˢ L)) := by
    rw [← half.image_interior]
    exact ⟨(0, 0), hprod, by simp [half]⟩
  have hhull :
      ((0 : EuclideanSpace ℝ (Fin m)), (0 : EuclideanSpace ℝ (Fin n))) ∈
        interior (convexHull ℝ
          ((K ×ˢ ({0} : Set (EuclideanSpace ℝ (Fin n)))) ∪
            (({0} : Set (EuclideanSpace ℝ (Fin m))) ×ˢ L))) := by
    apply interior_mono (half_smul_prod_subset_convexHull_axes K L)
    simpa [half] using hhalf
  exact zero_mem_interior_linearEquiv_image
    EuclideanSpace.finAddEquivProd.symm.toLinearEquiv hhull

/-- The origin is an interior point of every Hanner polytope. -/
theorem IsHannerPolytope.zero_mem_interior {n : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsHannerPolytope K) : 0 ∈ interior K := by
  induction hK with
  | unitSegment => exact Metric.ball_subset_interior_closedBall (Metric.mem_ball_self zero_lt_one)
  | linearImage hK e ih => exact zero_mem_interior_linearEquiv_image e ih
  | infinitySum hm hn hK hL ihK ihL =>
      apply zero_mem_interior_linearEquiv_image
        EuclideanSpace.finAddEquivProd.symm.toLinearEquiv
      rw [interior_prod_eq]
      exact ⟨ihK, ihL⟩
  | oneSum hm hn hK hL ihK ihL =>
      exact zero_mem_interior_hannerOneSum ihK ihL

end MetaMathlibExt
