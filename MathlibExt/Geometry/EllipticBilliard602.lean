/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Geometry.Euclidean.Projection

/-!
# Elliptic billiard invariant $k_{602}$

We prove the constancy of the product of the focal pedal distances over all periodic orbits
with a fixed confocal elliptic caustic.
-/

@[expose] public section

namespace MathlibExt.Geometry.EllipticBilliard602Wanted

open scoped BigOperators

/-- **Elliptic billiard invariant $k_{602}$.** Write $|XY|$ for the distance between points $X$
and $Y$ of the Euclidean plane. For every natural number $N$, all points $O, f_1, f_2$ of the
plane and all reals $a, a_c$ with $O = \frac{1}{2}(f_1 + f_2)$, $|f_1 f_2| < a$,
$|f_1 f_2| < a_c$ and $a_c < a$, there is a real number $C$ with the following property. Let
$P_0, P_1, P_2, \dots$ be points of the plane such that $|P_i f_1| + |P_i f_2| = a$ and
$P_{i+N} = P_i$ for every $i$, and such that for every $i < N$ the points $P_i$ and $P_{i+1}$
are distinct and the line $P_i P_{i+1}$ contains exactly one point $X$ with
$|X f_1| + |X f_2| = a_c$. For $i < N$ let $Q_{1,i}$ and $Q_{2,i}$ be points of the line
$P_i P_{i+1}$ closest to $f_1$ and to $f_2$ respectively. Then

$$\prod_{i<N} |f_1 Q_{1,i}| \cdot \prod_{i<N} |f_2 Q_{2,i}| = C.$$

In words: the vertices lie on the ellipse with foci $f_1, f_2$ and major axis $a$, every side
is tangent to the confocal caustic with major axis $a_c$, and $Q_{j,i}$ is the foot of the
perpendicular from $f_j$ to the $i$-th side.

Source: [AMR-050-0031] Reznik, Garcia and Koiller, Eighty New Invariants of N-Periodics in the
Elliptic Billiard (2021), Table row $k_{602}$, arXiv:2004.12497. -/
def conjecture : Prop :=
  ∀ (N : ℕ) (O f₁ f₂ : EuclideanSpace ℝ (Fin 2)) (a ac : ℝ),
    O = ((1 / 2 : ℝ) • (f₁ + f₂)) →
    dist f₁ f₂ < a →
    dist f₁ f₂ < ac →
    ac < a →
    ∃ C : ℝ,
      ∀ (P : ℕ → EuclideanSpace ℝ (Fin 2)) (Q₁ Q₂ : Fin N → EuclideanSpace ℝ (Fin 2)),
        (∀ i, dist (P i) f₁ + dist (P i) f₂ = a) →
        (∀ i, P (i + N) = P i) →
        (∀ i : Fin N, P i.val ≠ P (i.val + 1)) →
        (∀ i : Fin N, ∃! X : EuclideanSpace ℝ (Fin 2),
          (∃ t : ℝ, X = P i.val + t • (P (i.val + 1) - P i.val)) ∧
            dist X f₁ + dist X f₂ = ac) →
        (∀ i : Fin N, (∃ t : ℝ, Q₁ i = P i.val + t • (P (i.val + 1) - P i.val)) ∧
          ∀ X : EuclideanSpace ℝ (Fin 2),
            (∃ t : ℝ, X = P i.val + t • (P (i.val + 1) - P i.val)) →
              dist f₁ (Q₁ i) ≤ dist f₁ X) →
        (∀ i : Fin N, (∃ t : ℝ, Q₂ i = P i.val + t • (P (i.val + 1) - P i.val)) ∧
          ∀ X : EuclideanSpace ℝ (Fin 2),
            (∃ t : ℝ, X = P i.val + t • (P (i.val + 1) - P i.val)) →
              dist f₂ (Q₂ i) ≤ dist f₂ X) →
        (∏ i : Fin N, dist f₁ (Q₁ i)) * (∏ i : Fin N, dist f₂ (Q₂ i)) = C

open AffineSubspace EuclideanGeometry
open scoped RealInnerProductSpace

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

/-- If a level of the focal-distance sum is attained only once on a line, it is the minimum.
A smaller value would give a second intersection farther along the line by continuity. -/
private theorem le_focalSum_of_unique_level {L : AffineSubspace ℝ Plane}
    {f₁ f₂ : Plane} {ac : ℝ} (hac : 0 ≤ ac)
    (h : ∃! x : Plane, x ∈ L ∧ dist x f₁ + dist x f₂ = ac)
    {y : Plane} (hy : y ∈ L) : ac ≤ dist y f₁ + dist y f₂ := by
  obtain ⟨x, ⟨hx, hxlevel⟩, huniq⟩ := h
  by_contra! hylt
  have hxy : x ≠ y := by rintro rfl; linarith
  have hd : 0 < dist x y := dist_pos.mpr hxy
  let T := 1 + (ac + dist x f₁ + 1) / dist x y
  have hT : 1 ≤ T := le_add_of_nonneg_right (by positivity)
  let F := fun t : ℝ =>
    dist (AffineMap.lineMap x y t) f₁ + dist (AffineMap.lineMap x y t) f₂
  have hF : Continuous F :=
    ((lipschitzWith_lineMap x y).continuous.dist continuous_const).add
      ((lipschitzWith_lineMap x y).continuous.dist continuous_const)
  have hFT : ac ≤ F T := by
    have hdist : dist (AffineMap.lineMap x y T) x = T * dist x y := by
      rw [dist_lineMap_left, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    have hmul : T * dist x y = dist x y + (ac + dist x f₁ + 1) := by
      dsimp [T]
      rw [add_mul, one_mul, div_mul_cancel₀ _ hd.ne']
    have htri := dist_triangle (AffineMap.lineMap x y T) f₁ x
    rw [hdist, hmul, dist_comm f₁ x] at htri
    dsimp [F]
    linarith [dist_nonneg (x := AffineMap.lineMap x y T) (y := f₂)]
  have hF1 : F 1 ≤ ac := by simpa [F] using hylt.le
  obtain ⟨t, ht, htlevel⟩ := intermediate_value_Icc hT hF.continuousOn ⟨hF1, hFT⟩
  have heq : AffineMap.lineMap x y t = x :=
    huniq _ ⟨AffineMap.lineMap_mem t hx hy, htlevel⟩
  have hdtx := dist_lineMap_left x y t
  rw [heq, dist_self, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.1])] at hdtx
  exact (mul_pos (by linarith [ht.1]) hd).ne' hdtx.symm

/-- The segment between two points with opposite normal displacements meets the line. -/
private theorem exists_on_line_between {L : AffineSubspace ℝ Plane} {q₁ q₂ n : Plane}
    (hq₁ : q₁ ∈ L) (hq₂ : q₂ ∈ L) {k : ℝ} (hk : 0 ≤ k) :
    ∃ x ∈ L, dist x (q₁ + n) + dist x (q₂ - k • n) = dist (q₁ + n) (q₂ - k • n) := by
  let t : ℝ := 1 / (1 + k)
  have hden : 0 < 1 + k := by linarith
  have ht : t ∈ Set.Icc 0 1 :=
    ⟨by positivity, (div_le_one hden).2 (by linarith)⟩
  have hcancel : 1 - t - t * k = 0 := by
    dsimp [t]
    field_simp; ring
  let x := AffineMap.lineMap (q₁ + n) (q₂ - k • n) t
  have hx : x = AffineMap.lineMap q₁ q₂ t := by
    simp only [x, AffineMap.lineMap_apply_module]
    calc
      (1 - t) • (q₁ + n) + t • (q₂ - k • n) =
          ((1 - t) • q₁ + t • q₂) + (1 - t - t * k) • n := by
        simp only [smul_add, smul_sub, smul_smul, sub_smul]
        abel
      _ = _ := by rw [hcancel, zero_smul, add_zero]
  refine ⟨x, hx ▸ AffineMap.lineMap_mem t hq₁ hq₂, ?_⟩
  rw [dist_comm x (q₁ + n)]
  exact Wbtw.dist_add_dist ⟨t, ht, rfl⟩

/-- On a line tangent to a nondegenerate focal ellipse, the product of the two focal distances
to the line equals the square of the semiminor axis. -/
private theorem focalDistanceProduct {u v f₁ f₂ Q₁ Q₂ : Plane} {ac : ℝ}
    (huv : u ≠ v) (hac : dist f₁ f₂ < ac)
    (htan : ∃! x : Plane, x ∈ line[ℝ, u, v] ∧ dist x f₁ + dist x f₂ = ac)
    (hQ₁ : Q₁ ∈ line[ℝ, u, v] ∧ ∀ x ∈ line[ℝ, u, v], dist f₁ Q₁ ≤ dist f₁ x)
    (hQ₂ : Q₂ ∈ line[ℝ, u, v] ∧ ∀ x ∈ line[ℝ, u, v], dist f₂ Q₂ ≤ dist f₂ x) :
    dist f₁ Q₁ * dist f₂ Q₂ = (ac ^ 2 - dist f₁ f₂ ^ 2) / 4 := by
  let L : AffineSubspace ℝ Plane := line[ℝ, u, v]
  have : Nonempty L := ⟨u, left_mem_affineSpan_pair ℝ u v⟩
  have hmin {x : Plane} (hx : x ∈ L) : ac ≤ dist x f₁ + dist x f₂ :=
    le_focalSum_of_unique_level (dist_nonneg.trans hac.le) htan hx
  -- The given closest points have the same distances as the orthogonal projections.
  let q₁ : Plane := orthogonalProjection L f₁
  let q₂ : Plane := orthogonalProjection L f₂
  have hproj {f Q : Plane} (hQ : Q ∈ L ∧ ∀ x ∈ L, dist f Q ≤ dist f x) :
      dist f Q = dist f (orthogonalProjection L f) := by
    refine (hQ.2 _ (orthogonalProjection_mem f)).antisymm ?_
    rw [dist_orthogonalProjection_eq_infDist]
    exact Metric.infDist_le_dist_of_mem hQ.1
  rw [hproj hQ₁, hproj hQ₂]
  let n := f₁ - q₁
  have hn : n ≠ 0 := by
    intro hzero
    have hf : f₁ ∈ L := (sub_eq_zero.mp hzero).symm ▸ orthogonalProjection_mem f₁
    have := hmin hf
    simp only [dist_self, zero_add] at this
    exact hac.not_ge this
  have hdir : L.direction = ℝ ∙ (v - u) := by
    change (line[ℝ, u, v]).direction = _
    simp only [direction_affineSpan, vectorSpan_pair_rev, vsub_eq_sub]
  have hnorth : n ∈ L.directionᗮ := vsub_orthogonalProjection_mem_direction_orthogonal L f₁
  have hnormal (f : Plane) : f - (orthogonalProjection L f : Plane) ∈ (ℝ ∙ (v - u))ᗮ := by
    rw [← hdir]
    exact vsub_orthogonalProjection_mem_direction_orthogonal L f
  have : Fact (Module.finrank ℝ Plane = 2) := ⟨finrank_euclideanSpace_fin⟩
  obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp
    (Submodule.mem_span_singleton_of_inner_eq_zero_of_inner_eq_zero
      (sub_ne_zero.mpr huv.symm) hn
      (Submodule.mem_orthogonal_singleton_iff_inner_right.mp (hnormal f₂))
      (Submodule.mem_orthogonal_singleton_iff_inner_right.mp (hnormal f₁)))
  change k • n = f₂ - q₂ at hk
  have hf₁ : q₁ + n = f₁ := by dsimp [n]; abel
  have hf₂ : q₂ + k • n = f₂ := by rw [hk]; abel
  have hq₁ : q₁ ∈ L := orthogonalProjection_mem _
  have hq₂ : q₂ ∈ L := orthogonalProjection_mem _
  -- The original focal segment cannot meet the line, since its distance sum is too small.
  have hkpos : 0 < k := by
    by_contra! hkneg
    obtain ⟨x, hx, hxeq⟩ := exists_on_line_between hq₁ hq₂ (n := n) (neg_nonneg.mpr hkneg)
    rw [hf₁, neg_smul, sub_neg_eq_add, hf₂] at hxeq
    exact hac.not_ge (hxeq ▸ hmin hx)
  have href : q₂ - k • n = reflection L f₂ := by
    rw [reflection_apply']
    change q₂ - k • n = q₂ - f₂ + q₂
    rw [hk]
    abel
  -- Reflecting the second focus gives an intersecting segment and realizes the minimum.
  have hbase : ac = dist f₁ (reflection L f₂) := by
    obtain ⟨x, hx, hxeq⟩ := exists_on_line_between hq₁ hq₂ (n := n) hkpos.le
    rw [hf₁, href, dist_reflection_eq_of_mem L hx] at hxeq
    refine (hxeq ▸ hmin hx).antisymm ?_
    obtain ⟨y, ⟨hy, hylevel⟩, _⟩ := htan
    calc
      dist f₁ (reflection L f₂) ≤ dist f₁ y + dist y (reflection L f₂) := dist_triangle ..
      _ = ac := by rw [dist_reflection_eq_of_mem L hy, dist_comm f₁ y, hylevel]
  -- Subtract the two squared lengths. Their tangential components are identical.
  let d := q₁ - q₂
  have hdorth : ⟪d, n⟫ = 0 :=
    Submodule.inner_right_of_mem_orthogonal (vsub_mem_direction hq₁ hq₂) hnorth
  have hsq (r : ℝ) : ‖d + r • n‖ ^ 2 = ‖d‖ ^ 2 + r ^ 2 * ‖n‖ ^ 2 := by
    simp [norm_add_sq_real d (r • n), real_inner_smul_right, hdorth, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs]
  have hdiff : f₁ - f₂ = d + (1 - k) • n := by
    rw [← hf₁, ← hf₂, sub_smul, one_smul]
    dsimp [d]
    abel
  have hdiffRef : f₁ - reflection L f₂ = d + (1 + k) • n := by
    rw [← hf₁, ← href, add_smul, one_smul]
    dsimp [d]
    abel
  have hprod : dist f₁ q₁ * dist f₂ q₂ = k * ‖n‖ ^ 2 := by
    rw [dist_eq_norm, dist_eq_norm, ← hk, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hkpos.le]
    change ‖n‖ * (k * ‖n‖) = k * ‖n‖ ^ 2
    ring
  change dist f₁ q₁ * dist f₂ q₂ = _
  rw [hprod, hbase, dist_eq_norm, hdiffRef, dist_eq_norm, hdiff, hsq, hsq]
  ring

/--
**Bialy–Tabachnikov: $k_{602}$ is invariant.** The elliptic billiard invariant $k_{602}$
conjecture holds. Write $|XY|$ for the distance between points $X$ and $Y$. For every natural
number $N$, all points $O, f_1, f_2$ of the Euclidean plane and all reals $a, a_c$ with
$O = \frac{1}{2}(f_1 + f_2)$, $|f_1 f_2| < a$, $|f_1 f_2| < a_c$ and $a_c < a$, there is a real
number $C$ with the following property. Let $P_0, P_1, P_2, \dots$ be points of the plane such
that $|P_i f_1| + |P_i f_2| = a$ and $P_{i+N} = P_i$ for every $i$, and such that for every
$i < N$ the points $P_i$ and $P_{i+1}$ are distinct and the line $P_i P_{i+1}$ contains exactly
one point $X$ with $|X f_1| + |X f_2| = a_c$. For $i < N$ let $Q_{1,i}$ and $Q_{2,i}$ be any
points of the line $P_i P_{i+1}$ closest to $f_1$ and to $f_2$ respectively. Then
$\prod_{i<N} |f_1 Q_{1,i}| \cdot \prod_{i<N} |f_2 Q_{2,i}| = C$.

Bialy and Tabachnikov (Lemma 4.2) show that for each side tangent to the confocal caustic with
semi-minor axis $b$ the two focal distances multiply to $b^2$, so the common value is $b^{2N}$.

Source: M. Bialy, S. Tabachnikov, Dan Reznik's identities and more,
European Journal of Mathematics (2020), arXiv:2001.08469, https://arxiv.org/abs/2001.08469.
Moved from `OpenConjectures/Geometry/EllipticBilliard602`.
-/
theorem conjecture_holds : conjecture := by
  intro N O f₁ f₂ a ac _ _ hac _
  refine ⟨((ac ^ 2 - dist f₁ f₂ ^ 2) / 4) ^ N, ?_⟩
  intro P Q₁ Q₂ _ _ hne htan hQ₁ hQ₂
  rw [← Finset.prod_mul_distrib]
  have hline (i : Fin N) (x : Plane) :
      (∃ t : ℝ, x = P i.val + t • (P (i.val + 1) - P i.val)) ↔
        x ∈ line[ℝ, P i.val, P (i.val + 1)] := by
    rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
    simp only [AffineMap.lineMap_apply_module', add_comm, eq_comm]
  calc
    (∏ i : Fin N, dist f₁ (Q₁ i) * dist f₂ (Q₂ i)) =
        ∏ _i : Fin N, (ac ^ 2 - dist f₁ f₂ ^ 2) / 4 := by
      apply Finset.prod_congr rfl
      intro i _
      exact focalDistanceProduct (hne i) hac
        (by simpa only [hline] using htan i)
        (by simpa only [hline] using hQ₁ i)
        (by simpa only [hline] using hQ₂ i)
    _ = _ := by simp [div_pow]

end MathlibExt.Geometry.EllipticBilliard602Wanted
