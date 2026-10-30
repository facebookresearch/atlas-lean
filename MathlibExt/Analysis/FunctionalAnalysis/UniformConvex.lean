/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Uniform
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Order.Compact

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Uniform convexity in finite dimensions, and minimizing sequences

A normed space is *uniformly convex* when the triangle inequality is strict
with a bound that depends only on how far apart the two unit vectors are,
and a *strictly convex* space when the inequality is strict for every pair of
distinct unit vectors. In general strict convexity does not imply uniform
convexity: a strictly convex renorming of a non-reflexive space (for
instance Day's norm on `c₀`) cannot be uniformly convex, since uniformly
convex spaces are reflexive by Milman–Pettis. In finite dimensions the unit
sphere is compact, so the worst case is attained and the implication holds.

This file proves:

* In a finite-dimensional real normed space, strict convexity implies
  uniform convexity, by maximizing `‖x + y‖` over the compact set of pairs
  of unit vectors at distance at least `ε`. Together with Mathlib's
  `UniformConvexSpace.toStrictConvexSpace` this gives, in finite dimensions,
  the equivalence between strict and uniform convexity.
* In a complete uniformly convex space, every minimizing sequence for the
  distance from a point to a closed convex set converges to a nearest
  point. This is the quantitative form of the nearest-point existence used
  in Hilbert-space projection arguments.
* The finite-dimensional corollary: in a finite-dimensional strictly convex
  space, every minimizing sequence for the distance to a nonempty closed
  convex set converges to the unique nearest point.

This is a companion to the orthogonal-projection material of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean`
(the projection proposition for Hilbert spaces). It is not one of the 72
v1 targets. It is distinct from the results already in base MathlibExt:
`MilmanPettis.lean` uses uniform convexity to prove reflexivity,
`BanachSaks.lean` and `BrowderKirk.lean` assume a `UniformConvexSpace`
instance, `BestApproximation.lean` (batch 101) proves that
finite-dimensional subspaces are proximinal and that best approximation
is unique in strictly convex spaces, but none of them proves that strict
convexity implies uniform convexity in finite dimensions, nor that
minimizing sequences converge in uniformly convex spaces. Pinned Mathlib has the
`UniformConvexSpace` and `StrictConvexSpace` classes with the Hilbert-space
instances, but no implication between them in finite dimensions.

## References

* J. A. Clarkson, *Transactions of the American Mathematical Society* **40**
  (1936), for uniform convexity.
* K. Goebel and W. A. Kirk, *Topics in Metric Fixed Point Theory*, Cambridge
  University Press, 1990, for minimizing sequences in uniformly convex spaces
  and the finite-dimensional compactness argument from strict to uniform
  convexity.

## Main declarations

* `uniformConvexSpace_of_finiteDimensional_strictConvexSpace` : strict
  convexity implies uniform convexity in finite dimensions.
* `strictConvexSpace_iff_uniformConvexSpace_of_finiteDimensional` : in
  finite dimensions, strict and uniform convexity are equivalent.
* `exists_tendsto_of_minimizingSequence` : a minimizing sequence for the
  distance to a closed convex set in a complete uniformly convex space
  converges to a nearest point.
* `exists_unique_nearestPoint_of_minimizingSequence_of_finiteDimensional` :
  the nearest point is unique, independently of any convergence property of
  a second nearest point.
* `exists_unique_tendsto_of_minimizingSequence_of_finiteDimensional` :
  the finite-dimensional strictly convex form, with uniqueness.
-/

@[expose] public section

open Filter Metric Set Topology

namespace MathlibExt.Analysis.FunctionalAnalysis.UniformConvex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- In a finite-dimensional real normed space, strict convexity implies
uniform convexity. The proof maximizes `‖x + y‖` over the compact set of
pairs of unit vectors at distance at least `ε`; strict convexity says the
maximum is `< 2`, and the gap is the required `δ`. -/
theorem uniformConvexSpace_of_finiteDimensional_strictConvexSpace
    [FiniteDimensional ℝ E] [StrictConvexSpace ℝ E] : UniformConvexSpace E := by
  refine ⟨?_⟩
  intro ε hε
  -- The compact set of pairs of unit vectors at distance at least `ε`.
  set S : Set (E × E) :=
    (sphere (0 : E) 1 ×ˢ sphere (0 : E) 1) ∩ {p | ε ≤ ‖p.1 - p.2‖} with hS
  have hScompact : IsCompact S := by
    refine (isCompact_sphere (0 : E) 1).prod (isCompact_sphere (0 : E) 1) |>.inter_right ?_
    exact isClosed_Ici.preimage ((continuous_fst.sub continuous_snd).norm)
  by_cases hSne : S.Nonempty
  · -- The maximum of `‖x + y‖` on `S` is attained and is `< 2`.
    obtain ⟨p, hp, hmax⟩ := hScompact.exists_isMaxOn hSne
      ((continuous_fst.add continuous_snd).norm.continuousOn)
    obtain ⟨⟨hpx, hpy⟩, hpε⟩ := hp
    rw [mem_sphere_zero_iff_norm] at hpx hpy
    have hpε' : ε ≤ ‖p.1 - p.2‖ := hpε
    have hxy : p.1 ≠ p.2 := by
      intro h
      rw [h, sub_self, norm_zero] at hpε'
      linarith
    have hnsr : ¬ SameRay ℝ p.1 p.2 :=
      fun h => hxy (h.eq_of_norm_eq (hpx.trans hpy.symm))
    have hlt : ‖p.1 + p.2‖ < 2 := by
      have h := norm_add_lt_of_not_sameRay hnsr
      rw [hpx, hpy] at h
      linarith
    refine ⟨2 - ‖p.1 + p.2‖, by linarith, fun x hx y hy hxy => ?_⟩
    have hmem : (x, y) ∈ S := ⟨⟨by rwa [mem_sphere_zero_iff_norm], by rwa [mem_sphere_zero_iff_norm]⟩,
      hxy⟩
    have hle := hmax hmem
    simp only at hle
    have : 2 - (2 - ‖p.1 + p.2‖) = ‖p.1 + p.2‖ := sub_sub_self 2 _
    rw [this]
    exact hle
  · -- If `S` is empty, the implication is vacuous.
    refine ⟨1, one_pos, fun x hx y hy hxy => ?_⟩
    have hmem : (x, y) ∈ S := ⟨⟨by rwa [mem_sphere_zero_iff_norm], by rwa [mem_sphere_zero_iff_norm]⟩,
      hxy⟩
    exact (hSne ⟨(x, y), hmem⟩).elim

/-- In finite dimensions, strict convexity and uniform convexity are
equivalent. -/
theorem strictConvexSpace_iff_uniformConvexSpace_of_finiteDimensional
    [FiniteDimensional ℝ E] :
    StrictConvexSpace ℝ E ↔ UniformConvexSpace E :=
  ⟨fun _ => uniformConvexSpace_of_finiteDimensional_strictConvexSpace,
    fun _ => inferInstance⟩

section MinimizingSequence

variable [CompleteSpace E] [UniformConvexSpace E]

/-- In a complete uniformly convex space, a minimizing sequence for the
distance from a point `x` to a closed convex set `K` converges to a point
of `K` attaining that distance. The argument is the usual one: if the
sequence were not Cauchy, two far-apart almost-minimizing terms would have
normalized displacements far apart on the unit sphere, and uniform
convexity would force their midpoint to beat the infimum, contradicting
convexity of `K`. -/
theorem exists_tendsto_of_minimizingSequence {K : Set E} (hKconv : Convex ℝ K)
    (hKclosed : IsClosed K) {x : E} (u : ℕ → E) (hu : ∀ n, u n ∈ K)
    (hmin : Tendsto (fun n => ‖u n - x‖) atTop (𝓝 (infDist x K))) :
    ∃ y ∈ K, ‖y - x‖ = infDist x K ∧ Tendsto u atTop (𝓝 y) := by
  set d := infDist x K with hd
  have hd0 : 0 ≤ d := infDist_nonneg
  rcases eq_or_lt_of_le hd0 with hd0' | hdpos
  · -- If `d = 0`, then `u n → x` and `x ∈ K` since `K` is closed.
    have hd' : d = 0 := hd0'.symm
    have hux : Tendsto u atTop (𝓝 x) := by
      have h0 : Tendsto (fun n => ‖u n - x‖) atTop (𝓝 0) := by
        rw [← hd']; exact hmin
      have h1 : Tendsto (fun n => u n - x) atTop (𝓝 0) :=
        tendsto_zero_iff_norm_tendsto_zero.2 h0
      exact tendsto_sub_nhds_zero_iff.1 h1
    refine ⟨x, hKclosed.mem_of_tendsto hux (Filter.Eventually.of_forall hu), ?_, hux⟩
    rw [hd', sub_self, norm_zero]
  · -- If `d > 0`, the sequence is Cauchy: otherwise two almost-minimizing
    -- terms are far apart, contradicting uniform convexity at their midpoint.
    have hcauchy : CauchySeq u := by
      by_contra hnc
      rw [Metric.cauchySeq_iff] at hnc
      push Not at hnc
      obtain ⟨ε₀, hε₀, hfar⟩ := hnc
      -- Uniform convexity at the normalized separation `ε₀ / (4 * d)`.
      have hεw : (0 : ℝ) < ε₀ / (4 * d) := div_pos hε₀ (by linarith)
      obtain ⟨δ, hδ, hδprop⟩ := UniformConvexSpace.uniform_convex (E := E) hεw
      -- Shrink `δ` so that `δ ≤ 1`; the uniform-convexity bound persists.
      set δ' := min δ 1 with hδ'def
      have hδ'pos : 0 < δ' := by
        rw [hδ'def]; exact lt_min hδ one_pos
      have hδ'le : δ' ≤ 1 := by
        rw [hδ'def]; exact min_le_right _ _
      have hδ'leδ : δ' ≤ δ := by
        rw [hδ'def]; exact min_le_left _ _
      have hδ'prop : ∀ ⦃a b : E⦄, ‖a‖ = 1 → ‖b‖ = 1 → ε₀ / (4 * d) ≤ ‖a - b‖ →
          ‖a + b‖ ≤ 2 - δ' := by
        intro a b ha hb hab
        exact (hδprop ha hb hab).trans (by linarith)
      -- Tolerance: close enough to `d` that the normalized vectors stay
      -- separated and the midpoint estimate beats `2 * d`.
      set c := min (ε₀ / 4) (d * δ' / 8) with hcdef
      have hδ'd : 0 < d * δ' := mul_pos hdpos hδ'pos
      have hcpos : 0 < c := by
        rw [hcdef]
        exact lt_min (by linarith) (by linarith)
      have hc1 : 2 * c ≤ ε₀ / 2 := by
        have h : c ≤ ε₀ / 4 := by rw [hcdef]; exact min_le_left _ _
        linarith
      have hc2 : 2 * c ≤ d * δ' / 4 := by
        have h : c ≤ d * δ' / 8 := by rw [hcdef]; exact min_le_right _ _
        linarith
      have hcd : c < d := by
        have h : c ≤ d * δ' / 8 := by rw [hcdef]; exact min_le_right _ _
        have h2 : d * δ' / 8 ≤ d / 8 := by
          rw [div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 8)]
          exact mul_le_of_le_one_right hd0 hδ'le
        linarith
      -- Eventually all terms are within `c` of the infimal distance.
      obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hmin) c hcpos
      -- Pick a far-apart pair at and after `N`.
      obtain ⟨m, hmN, n, hnN, hndist⟩ := hfar N
      set a := u m - x with hadef
      set b := u n - x with hbdef
      have ha_close : |‖a‖ - d| < c := by
        have h := hN m hmN
        rwa [Real.dist_eq, ← hadef] at h
      have hb_close : |‖b‖ - d| < c := by
        have h := hN n hnN
        rwa [Real.dist_eq, ← hbdef] at h
      have ha_pos : 0 < ‖a‖ := by
        have : d - c < ‖a‖ := by linarith [abs_lt.1 ha_close]
        linarith
      have ha_le : ‖a‖ < 2 * d := by
        have : ‖a‖ < d + c := by linarith [abs_lt.1 ha_close]
        linarith
      have hb_pos : 0 < ‖b‖ := by
        have : d - c < ‖b‖ := by linarith [abs_lt.1 hb_close]
        linarith
      -- The far-apart hypothesis, in norm form.
      have hab_dist : ε₀ ≤ ‖a - b‖ := by
        have h := hndist
        rw [dist_eq_norm] at h
        have : u m - u n = a - b := by rw [hadef, hbdef]; abel
        rwa [this] at h
      -- Normalized displacements.
      set wa := ‖a‖⁻¹ • a with hwadef
      set wb := ‖b‖⁻¹ • b with hwbdef
      have hwa : ‖wa‖ = 1 := by
        rw [hwadef, norm_smul_of_nonneg (inv_nonneg.2 (norm_nonneg _)),
          inv_mul_cancel₀ ha_pos.ne']
      have hwb : ‖wb‖ = 1 := by
        rw [hwbdef, norm_smul_of_nonneg (inv_nonneg.2 (norm_nonneg _)),
          inv_mul_cancel₀ hb_pos.ne']
      have hsmul_a : ‖a‖ • wa = a := by
        rw [hwadef, smul_inv_smul₀ ha_pos.ne']
      have hsmul_b : ‖b‖ • wb = b := by
        rw [hwbdef, smul_inv_smul₀ hb_pos.ne']
      -- `a - b` is controlled by the normalized difference.
      have hnorm_diff : ‖a - b‖ ≤ ‖a‖ * ‖wa - wb‖ + |‖a‖ - ‖b‖| := by
        have heq : a - b = ‖a‖ • (wa - wb) + (‖a‖ - ‖b‖) • wb := by
          rw [smul_sub, hsmul_a, sub_smul, hsmul_b]
          abel
        calc ‖a - b‖ = ‖‖a‖ • (wa - wb) + (‖a‖ - ‖b‖) • wb‖ := by rw [heq]
          _ ≤ ‖‖a‖ • (wa - wb)‖ + ‖(‖a‖ - ‖b‖) • wb‖ := norm_add_le _ _
          _ = ‖a‖ * ‖wa - wb‖ + |‖a‖ - ‖b‖| := by
            rw [norm_smul_of_nonneg (norm_nonneg _), norm_smul, Real.norm_eq_abs, hwb,
              mul_one]
      have hnorm_sub : |‖a‖ - ‖b‖| ≤ ε₀ / 2 := by
        have : |‖a‖ - ‖b‖| ≤ |‖a‖ - d| + |‖b‖ - d| := by
          calc |‖a‖ - ‖b‖| = |(‖a‖ - d) - (‖b‖ - d)| := by ring_nf
            _ ≤ |‖a‖ - d| + |‖b‖ - d| := abs_sub _ _
        linarith
      -- Hence the normalized displacements are separated.
      have hsep : ε₀ / (4 * d) ≤ ‖wa - wb‖ := by
        have h1 : ε₀ / 2 ≤ ‖a‖ * ‖wa - wb‖ := by linarith
        rw [div_le_iff₀ (by linarith : (0 : ℝ) < 4 * d)]
        have hnonneg : (0 : ℝ) ≤ (2 * d - ‖a‖) * ‖wa - wb‖ :=
          mul_nonneg (by linarith) (norm_nonneg _)
        nlinarith [h1, hnonneg]
      have hsum : ‖wa + wb‖ ≤ 2 - δ' := hδ'prop hwa hwb hsep
      -- The midpoint therefore beats `2 * d`, contradicting convexity.
      have hmid : ‖a + b‖ < 2 * d := by
        have heq : a + b = d • (wa + wb) + (‖a‖ - d) • wa + (‖b‖ - d) • wb := by
          symm
          rw [smul_add, sub_smul, sub_smul, hsmul_a, hsmul_b]
          abel
        calc ‖a + b‖
            = ‖d • (wa + wb) + (‖a‖ - d) • wa + (‖b‖ - d) • wb‖ := by rw [heq]
          _ ≤ ‖d • (wa + wb)‖ + ‖(‖a‖ - d) • wa‖ + ‖(‖b‖ - d) • wb‖ :=
              norm_add_le _ _ |>.trans (add_le_add_left (norm_add_le _ _) _)
          _ = d * ‖wa + wb‖ + |‖a‖ - d| * ‖wa‖ + |‖b‖ - d| * ‖wb‖ := by
              have e1 : ‖d • (wa + wb)‖ = d * ‖wa + wb‖ := norm_smul_of_nonneg hd0 _
              have e2 : ‖(‖a‖ - d) • wa‖ = |‖a‖ - d| := by
                rw [norm_smul, Real.norm_eq_abs, hwa, mul_one]
              have e3 : ‖(‖b‖ - d) • wb‖ = |‖b‖ - d| := by
                rw [norm_smul, Real.norm_eq_abs, hwb, mul_one]
              rw [e1, e2, e3, hwa, hwb, mul_one, mul_one]
          _ ≤ d * (2 - δ') + c + c := by
              have h1 : d * ‖wa + wb‖ ≤ d * (2 - δ') :=
                mul_le_mul_of_nonneg_left hsum hd0
              have h2 : |‖a‖ - d| * ‖wa‖ ≤ c := by
                rw [hwa, mul_one]; exact le_of_lt ha_close
              have h3 : |‖b‖ - d| * ‖wb‖ ≤ c := by
                rw [hwb, mul_one]; exact le_of_lt hb_close
              exact add_le_add (add_le_add h1 h2) h3
          _ < 2 * d := by
              have hrw : d * (2 - δ') = 2 * d - d * δ' := by ring
              have hpos : 0 < d * δ' := mul_pos hdpos hδ'pos
              linarith
      -- But the midpoint lies in `K`, so `‖a + b‖ ≥ 2 * d`.
      have hmidK : (1 / 2 : ℝ) • u m + (1 / 2 : ℝ) • u n ∈ K :=
        hKconv (hu m) (hu n) (by norm_num) (by norm_num) (by norm_num)
      have hmid_ge : 2 * d ≤ ‖a + b‖ := by
        have hle : d ≤ dist x ((1 / 2 : ℝ) • u m + (1 / 2 : ℝ) • u n) :=
          infDist_le_dist_of_mem hmidK
        have heq : (1 / 2 : ℝ) • u m + (1 / 2 : ℝ) • u n - x
            = (1 / 2 : ℝ) • (a + b) := by rw [hadef, hbdef]; module
        rw [dist_eq_norm, norm_sub_rev, heq, norm_smul,
          Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)] at hle
        linarith
      exact absurd (hmid.trans_le hmid_ge) (by linarith)
    obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hcauchy
    have hyK : y ∈ K := hKclosed.mem_of_tendsto hy (Filter.Eventually.of_forall hu)
    have hnorm : ‖y - x‖ = d := by
      have h1 : Tendsto (fun n => ‖u n - x‖) atTop (𝓝 ‖y - x‖) := by
        have h2 : Tendsto (fun n => u n - x) atTop (𝓝 (y - x)) := hy.sub_const x
        exact h2.norm
      exact tendsto_nhds_unique h1 hmin
    exact ⟨y, hyK, hnorm, hy⟩

end MinimizingSequence

/-- In a finite-dimensional strictly convex space, a minimizing sequence for
the distance to a closed convex set supplies a unique nearest point. The
uniqueness clause only assumes that a second point belongs to the set and
attains the distance; it does not assume that the minimizing sequence
converges to that point. -/
theorem exists_unique_nearestPoint_of_minimizingSequence_of_finiteDimensional
    [FiniteDimensional ℝ E] [StrictConvexSpace ℝ E] {K : Set E} (hKconv : Convex ℝ K)
    (hKclosed : IsClosed K) {x : E} (u : ℕ → E) (hu : ∀ n, u n ∈ K)
    (hmin : Tendsto (fun n => ‖u n - x‖) atTop (𝓝 (infDist x K))) :
    ∃! y, y ∈ K ∧ ‖y - x‖ = infDist x K := by
  have : UniformConvexSpace E :=
    uniformConvexSpace_of_finiteDimensional_strictConvexSpace
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨y, hyK, hynorm, _⟩ := exists_tendsto_of_minimizingSequence hKconv hKclosed u hu hmin
  refine ⟨y, ⟨hyK, hynorm⟩, ?_⟩
  intro z ⟨hzK, hznorm⟩
  -- Uniqueness via the midpoint: if `z` is another nearest point, the
  -- midpoint of `y` and `z` lies in `K` and is at least as far from `x`,
  -- so the triangle inequality is an equality, and strict convexity
  -- (from uniform convexity) forces `y = z`.
  by_cases hd0 : infDist x K = 0
  · have hyx : y = x := by
      have h : ‖y - x‖ = 0 := by rw [hynorm, hd0]
      exact sub_eq_zero.1 (norm_eq_zero.1 h)
    have hzx : z = x := by
      have h : ‖z - x‖ = 0 := by rw [hznorm, hd0]
      exact sub_eq_zero.1 (norm_eq_zero.1 h)
    rw [hyx, hzx]
  · have hdpos : 0 < infDist x K := lt_of_le_of_ne' infDist_nonneg hd0
    set a := y - x with hadef
    set b := z - x with hbdef
    have hmidK : (1 / 2 : ℝ) • y + (1 / 2 : ℝ) • z ∈ K :=
      hKconv hyK hzK (by norm_num) (by norm_num) (by norm_num)
    have hmid_ge : infDist x K ≤ ‖(1 / 2 : ℝ) • (a + b)‖ := by
      have hle : infDist x K ≤ dist x ((1 / 2 : ℝ) • y + (1 / 2 : ℝ) • z) :=
        infDist_le_dist_of_mem hmidK
      have heq : (1 / 2 : ℝ) • y + (1 / 2 : ℝ) • z - x
          = (1 / 2 : ℝ) • (a + b) := by rw [hadef, hbdef]; module
      rw [dist_eq_norm, norm_sub_rev, heq] at hle
      exact hle
    have hsum : ‖a + b‖ = ‖a‖ + ‖b‖ := by
      have h1 : ‖(1 / 2 : ℝ) • (a + b)‖ = (1 / 2) * ‖a + b‖ := by
        rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2)]
      have h2 : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le _ _
      linarith
    have hab : a = b :=
      eq_of_norm_eq_of_norm_add_eq (by rw [hynorm, hznorm]) hsum
    exact (sub_left_inj.1 hab).symm

/-- In a finite-dimensional strictly convex space, a minimizing sequence for
the distance to a closed convex set converges to the unique point of the
set attaining that distance. This preserves the original combined API as a
corollary of nearest-point uniqueness and minimizing-sequence convergence. -/
theorem exists_unique_tendsto_of_minimizingSequence_of_finiteDimensional
    [FiniteDimensional ℝ E] [StrictConvexSpace ℝ E] {K : Set E} (hKconv : Convex ℝ K)
    (hKclosed : IsClosed K) {x : E} (u : ℕ → E) (hu : ∀ n, u n ∈ K)
    (hmin : Tendsto (fun n => ‖u n - x‖) atTop (𝓝 (infDist x K))) :
    ∃! y, y ∈ K ∧ ‖y - x‖ = infDist x K ∧ Tendsto u atTop (𝓝 y) := by
  have : UniformConvexSpace E :=
    uniformConvexSpace_of_finiteDimensional_strictConvexSpace
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨y, hyK, hynorm, hy⟩ :=
    exists_tendsto_of_minimizingSequence hKconv hKclosed u hu hmin
  obtain ⟨_, _, huniq⟩ :=
    exists_unique_nearestPoint_of_minimizingSequence_of_finiteDimensional
      hKconv hKclosed u hu hmin
  refine ⟨y, ⟨hyK, hynorm, hy⟩, ?_⟩
  intro z hz
  exact (huniq z ⟨hz.1, hz.2.1⟩).trans (huniq y ⟨hyK, hynorm⟩).symm

end MathlibExt.Analysis.FunctionalAnalysis.UniformConvex
