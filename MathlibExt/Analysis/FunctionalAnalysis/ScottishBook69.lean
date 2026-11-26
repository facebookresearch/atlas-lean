/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-!
# Metric centers and Scottish Book Problem 69

This module defines iterated metric centers and refutes the Scottish Book Problem 69 claim
using the hyperbolic upper half-plane.

Source: S. Mazur and S. Ulam, Problem 69 of the Scottish Book; typescript Ad 69 records the
negative answer (S. Mazur, December 21, 1936).
-/

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook69Wanted

/-- **Iterated metric center sets.** Let $p, q$ be points of a pseudometric space $E$ with
distance $d$. The iterated metric center sets $R_n \subseteq E$ of $(p, q)$, for
$n \in \mathbb{N}$, are defined by $R_0 = \{x \in E : d(p, x) + d(x, q) = d(p, q)\}$ and
$R_{n+1} = \{r \in R_n : d(r, x) \le \operatorname{diam}(R_n) / 2 \text{ for all } x \in R_n\}$. -/
noncomputable def metricCenterSets (E : Type*) [PseudoMetricSpace E]
    (p q : E) : ℕ → Set E
  | 0 => {x | dist p x + dist x q = dist p q}
  | (n + 1) =>
    {r ∈ metricCenterSets E p q n |
      ∀ x ∈ metricCenterSets E p q n,
        dist r x ≤ Metric.diam (metricCenterSets E p q n) / 2}

/-- **Metric center of a pair of points.** Let $p, q, c$ be points of a pseudometric space $E$
and let $R_n$, for $n \in \mathbb{N}$, be the iterated metric center sets of $(p, q)$. We say
that $c$ is the metric center of $(p, q)$ when $c \in R_n$ for every $n$, and every point
$y \in E$ with $y \in R_n$ for every $n$ equals $c$. -/
def IsMetricCenter (E : Type*) [PseudoMetricSpace E] (p q c : E) : Prop :=
  (∀ n, c ∈ metricCenterSets E p q n) ∧
  ∀ y, (∀ n, y ∈ metricCenterSets E p q n) → y = c

/-- **Scottish Book Problem 69 claim.** The statement that every nonempty complete pseudometric
space $E$ with the following two properties is isometric to a real Banach space: (1) for all
$p, q \in E$ there is exactly one point $c \in E$ that is the metric center of $(p, q)$, and
(2) for all $p, q \in E$ there is exactly one point $x \in E$ such that $q$ is the metric
center of $(p, x)$. Here "isometric to a real Banach space" means that there are a complete
real normed space $F$ and an isometric bijection $E \to F$. This is the affirmative answer to
Problem 69 of S. Mazur and S. Ulam in the Scottish Book; the claim is false
(`mazurUlam69_refuted`).

The space is required to be nonempty: the empty space has properties (1) and (2) vacuously but
is not isometric to a Banach space. -/
def ScottishBookProblem69Claim : Prop :=
  ∀ (E : Type) [PseudoMetricSpace E] [CompleteSpace E] [Nonempty E],
    (∀ p q : E, ∃! c, IsMetricCenter E p q c) →
    (∀ p q : E, ∃! x, IsMetricCenter E p x q) →
    ∃ (F : Type) (_ : NormedAddCommGroup F) (_ : NormedSpace ℝ F)
      (_ : CompleteSpace F), Nonempty (E ≃ᵢ F)

private theorem centerSets_subset (E : Type*) [PseudoMetricSpace E] (p q : E) (n : ℕ) :
    metricCenterSets E p q n ⊆ metricCenterSets E p q 0 := by
  induction n with
  | zero => exact Set.Subset.rfl
  | succ n ih => exact fun _ hx => ih hx.1

private theorem centerSets_bounded (E : Type*) [PseudoMetricSpace E] (p q : E) (n : ℕ) :
    Bornology.IsBounded (metricCenterSets E p q n) := by
  apply Bornology.IsBounded.subset _ (centerSets_subset E p q n)
  apply Metric.isBounded_iff.mpr
  refine ⟨2 * dist p q, fun x hx y hy => ?_⟩
  change dist p x + dist x q = dist p q at hx
  change dist p y + dist y q = dist p q at hy
  have h := dist_triangle_left x y p
  have hx0 := dist_nonneg (x := x) (y := q)
  have hy0 := dist_nonneg (x := y) (y := q)
  linarith

private theorem centerSets_diam_le (E : Type*) [PseudoMetricSpace E] (p q : E) (n : ℕ) :
    Metric.diam (metricCenterSets E p q n) ≤ 2 * dist p q * (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero =>
    apply Metric.diam_le_of_forall_dist_le (by positivity)
    intro x hx y hy
    change dist p x + dist x q = dist p q at hx
    change dist p y + dist y q = dist p q at hy
    have h := dist_triangle_left x y p
    have hx0 := dist_nonneg (x := x) (y := q)
    have hy0 := dist_nonneg (x := y) (y := q)
    simp only [pow_zero, mul_one]
    linarith
  | succ n ih =>
    have h : Metric.diam (metricCenterSets E p q (n + 1)) ≤
        Metric.diam (metricCenterSets E p q n) / 2 :=
      Metric.diam_le_of_forall_dist_le (by positivity) fun x hx y hy => hx.2 y hy.1
    rw [pow_succ]
    linarith

private theorem centerSets_comm (E : Type*) [PseudoMetricSpace E] (p q : E) (n : ℕ) :
    metricCenterSets E p q n = metricCenterSets E q p n := by
  induction n with
  | zero => ext x; simp only [metricCenterSets, Set.mem_ofPred_eq, dist_comm, add_comm]
  | succ n ih => simp only [metricCenterSets, ih]

private theorem centerSets_image (E F : Type*) [PseudoMetricSpace E] [PseudoMetricSpace F]
    (e : E ≃ᵢ F) (p q : E) (n : ℕ) :
    e '' metricCenterSets E p q n = metricCenterSets F (e p) (e q) n := by
  induction n with
  | zero =>
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [metricCenterSets, Set.mem_ofPred_eq, e.dist_eq] using hx
    · intro hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      simpa only [metricCenterSets, Set.mem_ofPred_eq, ← e.dist_eq, e.apply_symm_apply] using hy
  | succ n ih =>
    have hd : Metric.diam (metricCenterSets F (e p) (e q) n) =
        Metric.diam (metricCenterSets E p q n) := by
      rw [← ih, e.isometry.diam_image]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨ih ▸ Set.mem_image_of_mem e hx.1, ?_⟩
      intro z hz
      rw [← ih] at hz
      rcases hz with ⟨z, hz, rfl⟩
      simpa only [e.dist_eq, hd] using hx.2 z hz
    · intro hy
      change y ∈ metricCenterSets F (e p) (e q) n ∧ _ at hy
      rw [← ih] at hy
      rcases hy.1 with ⟨x, hx, rfl⟩
      refine ⟨x, ⟨hx, ?_⟩, rfl⟩
      intro z hz
      have h := hy.2 (e z) (Set.mem_image_of_mem e hz)
      simpa only [e.dist_eq, e.isometry.diam_image] using h

private theorem centerSets_mem_map (E F : Type*) [PseudoMetricSpace E] [PseudoMetricSpace F]
    (e : E ≃ᵢ F) (p q x : E) (n : ℕ) :
    e x ∈ metricCenterSets F (e p) (e q) n ↔ x ∈ metricCenterSets E p q n := by
  rw [← centerSets_image E F e p q n]
  exact e.injective.mem_set_image

private theorem metricCenter_map (E F : Type*) [PseudoMetricSpace E] [PseudoMetricSpace F]
    (e : E ≃ᵢ F) (p q c : E) (hc : IsMetricCenter E p q c) :
    IsMetricCenter F (e p) (e q) (e c) := by
  refine ⟨fun n => (centerSets_mem_map E F e p q c n).mpr (hc.1 n), ?_⟩
  intro y hy
  have h : e.symm y = c := hc.2 (e.symm y) fun n =>
    (centerSets_mem_map E F e p q (e.symm y) n).mp (by simpa using hy n)
  simpa using congrArg e h

private theorem metricCenter_unique (E : Type*) [PseudoMetricSpace E] (p q c d : E)
    (hc : IsMetricCenter E p q c) (hd : IsMetricCenter E p q d) : c = d := hd.2 c hc.1

private theorem metricCenter_of_reflection (E : Type*) [MetricSpace E]
    (p q c : E) (e : E ≃ᵢ E) (hep : e p = q) (heq : e q = p)
    (hd : ∀ x, dist x (e x) = 2 * dist x c)
    (hc : dist p c + dist c q = dist p q) : IsMetricCenter E p q c := by
  have hinv : ∀ n x, e x ∈ metricCenterSets E p q n ↔ x ∈ metricCenterSets E p q n := by
    intro n x
    have h := centerSets_mem_map E E e p q x n
    simpa only [hep, heq, centerSets_comm E q p n] using h
  have hmem : ∀ n, c ∈ metricCenterSets E p q n := by
    intro n
    induction n with
    | zero => exact hc
    | succ n ih =>
      refine ⟨ih, fun x hx => ?_⟩
      have h := Metric.dist_le_diam_of_mem (centerSets_bounded E p q n)
        hx ((hinv n x).mpr hx)
      rw [hd x] at h
      rw [dist_comm c x]
      linarith
  refine ⟨hmem, fun y hy => ?_⟩
  apply dist_eq_zero.mp
  have hle : ∀ n, dist y c ≤ 2 * dist p q * (1 / 2 : ℝ) ^ n := fun n =>
    (Metric.dist_le_diam_of_mem (centerSets_bounded E p q n) (hy n) (hmem n)).trans
      (centerSets_diam_le E p q n)
  have ht : Filter.Tendsto (fun n : ℕ => 2 * dist p q * (1 / 2 : ℝ) ^ n)
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (2 * dist p q)
  exact le_antisymm (ge_of_tendsto' ht hle) dist_nonneg

private noncomputable def halfTurn : UpperHalfPlane ≃ᵢ UpperHalfPlane :=
  IsometryEquiv.constSMul (ModularGroup.S : Matrix.SpecialLinearGroup (Fin 2) ℝ)

private theorem halfTurn_coe (z : UpperHalfPlane) :
    (halfTurn z : ℂ) = -(z : ℂ)⁻¹ := by
  simp [halfTurn, UpperHalfPlane.coe_specialLinearGroup_apply, ModularGroup.coe_S,
    div_eq_mul_inv]

private theorem halfTurn_double (z : UpperHalfPlane) :
    dist z (halfTurn z) = 2 * dist z UpperHalfPlane.I := by
  apply Real.cosh_strictMonoOn.injOn dist_nonneg
    (by change 0 ≤ 2 * dist z UpperHalfPlane.I; positivity)
  rw [Real.cosh_two_mul, Real.sinh_sq, UpperHalfPlane.cosh_dist',
    UpperHalfPlane.cosh_dist']
  have hz : z.re ^ 2 + z.im ^ 2 ≠ 0 := by
    have h := z.im_pos
    nlinarith [sq_nonneg z.re]
  have hre : (halfTurn z).re = -z.re / (z.re ^ 2 + z.im ^ 2) := by
    change (halfTurn z : ℂ).re = _
    rw [halfTurn_coe]
    simp [Complex.inv_re, Complex.normSq_apply, UpperHalfPlane.coe_re,
      UpperHalfPlane.coe_im, pow_two, neg_div]
  have him : (halfTurn z).im = z.im / (z.re ^ 2 + z.im ^ 2) := by
    change (halfTurn z : ℂ).im = _
    rw [halfTurn_coe]
    simp [Complex.inv_im, Complex.normSq_apply, UpperHalfPlane.coe_re,
      UpperHalfPlane.coe_im, pow_two, neg_div]
  rw [hre, him]
  simp only [UpperHalfPlane.I_re, UpperHalfPlane.I_im]
  field_simp [hz, z.im_ne_zero]
  ring

private noncomputable def normalize (c : UpperHalfPlane) : UpperHalfPlane ≃ᵢ UpperHalfPlane where
  toFun z := c.re +ᵥ (⟨c.im, c.im_pos⟩ : {x : ℝ // 0 < x}) • z
  invFun z := (⟨c.im⁻¹, inv_pos.mpr c.im_pos⟩ : {x : ℝ // 0 < x}) • (-c.re +ᵥ z)
  left_inv z := by
    apply UpperHalfPlane.ext_re_im <;>
      simp [UpperHalfPlane.pos_real_re, UpperHalfPlane.pos_real_im, c.im_ne_zero]
  right_inv z := by
    apply UpperHalfPlane.ext_re_im <;>
      simp [UpperHalfPlane.pos_real_re, UpperHalfPlane.pos_real_im, c.im_ne_zero]
  isometry_toFun := (UpperHalfPlane.isometry_real_vadd c.re).comp
    (UpperHalfPlane.isometry_pos_mul ⟨c.im, c.im_pos⟩)

private theorem normalize_I (c : UpperHalfPlane) : normalize c UpperHalfPlane.I = c := by
  apply UpperHalfPlane.ext_re_im <;>
    simp [normalize, UpperHalfPlane.vadd_re, UpperHalfPlane.vadd_im,
      UpperHalfPlane.pos_real_re, UpperHalfPlane.pos_real_im]

private noncomputable def reflection (c : UpperHalfPlane) : UpperHalfPlane ≃ᵢ UpperHalfPlane :=
  ((normalize c).symm.trans halfTurn).trans (normalize c)

private theorem reflection_double (c z : UpperHalfPlane) :
    dist z (reflection c z) = 2 * dist z c := by
  calc
    dist z (reflection c z) =
        dist ((normalize c).symm z) (halfTurn ((normalize c).symm z)) := by
      simpa only [reflection, IsometryEquiv.trans_apply, IsometryEquiv.apply_symm_apply] using
        (normalize c).dist_eq ((normalize c).symm z) (halfTurn ((normalize c).symm z))
    _ = 2 * dist ((normalize c).symm z) UpperHalfPlane.I := halfTurn_double _
    _ = 2 * dist z c := by
      rw [← (normalize c).dist_eq ((normalize c).symm z) UpperHalfPlane.I,
        IsometryEquiv.apply_symm_apply, normalize_I]

private theorem reflection_coe (c z : UpperHalfPlane) :
    (reflection c z : ℂ) = (c.re : ℂ) - (c.im : ℂ) ^ 2 / ((z : ℂ) - c.re) := by
  change ((c.re : ℂ) + (c.im : ℂ) *
    (halfTurn ((normalize c).symm z) : ℂ)) = _
  rw [halfTurn_coe]
  change (c.re : ℂ) + (c.im : ℂ) *
    -((c.im⁻¹ : ℝ) * ((-c.re : ℝ) + (z : ℂ)))⁻¹ = _
  have hi : (c.im : ℂ) ≠ 0 := by exact_mod_cast c.im_ne_zero
  simp only [Complex.ofReal_inv, Complex.ofReal_neg, mul_inv_rev]
  field_simp
  ring

private theorem reflection_involutive (c : UpperHalfPlane) :
    Function.Involutive (reflection c) := by
  intro z
  apply UpperHalfPlane.coe_injective
  rw [reflection_coe, reflection_coe]
  have hi : (c.im : ℂ) ≠ 0 := by exact_mod_cast c.im_ne_zero
  have hz : (z : ℂ) - c.re ≠ 0 := by
    intro h
    have h' := congrArg Complex.im h
    simp only [Complex.sub_im, UpperHalfPlane.coe_im, Complex.ofReal_im,
      sub_zero, Complex.zero_im] at h'
    exact z.im_ne_zero h'
  field_simp
  ring

private theorem reflection_center (p c : UpperHalfPlane) :
    IsMetricCenter UpperHalfPlane p (reflection c p) c := by
  have hfix : reflection c c = c := by
    apply dist_eq_zero.mp
    simpa only [dist_self, mul_zero, dist_comm] using reflection_double c c
  apply metricCenter_of_reflection UpperHalfPlane p (reflection c p) c (reflection c) rfl
    (reflection_involutive c p) (reflection_double c)
  have heq : dist c (reflection c p) = dist p c := by
    simpa only [hfix, dist_comm] using (reflection c).dist_eq c p
  rw [heq, reflection_double]
  ring

private theorem exists_reflection (p q : UpperHalfPlane) :
    ∃ c, reflection c p = q := by
  let a : ℝ := (p.re * q.im + q.re * p.im) / (p.im + q.im)
  let B : ℝ := p.im * q.im * (1 + ((p.re - q.re) / (p.im + q.im)) ^ 2)
  have hB : 0 < B := by dsimp [B]; positivity
  let c : UpperHalfPlane := ⟨⟨a, Real.sqrt B⟩, Real.sqrt_pos.mpr hB⟩
  refine ⟨c, ?_⟩
  apply UpperHalfPlane.coe_injective
  rw [reflection_coe]
  change (a : ℂ) - (Real.sqrt B : ℂ) ^ 2 / ((p : ℂ) - a) = (q : ℂ)
  have hp : (p : ℂ) - a ≠ 0 := by
    intro h
    have h' := congrArg Complex.im h
    simp only [Complex.sub_im, UpperHalfPlane.coe_im, Complex.ofReal_im,
      sub_zero, Complex.zero_im] at h'
    exact p.im_ne_zero h'
  have hsq : (Real.sqrt B : ℂ) ^ 2 = (B : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hB.le]
  rw [hsq]
  field_simp
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, UpperHalfPlane.coe_re,
      UpperHalfPlane.coe_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
    dsimp [a, B]
    field_simp [ne_of_gt (add_pos p.im_pos q.im_pos)]
    ring
  · simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im, UpperHalfPlane.coe_re,
      UpperHalfPlane.coe_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
    dsimp [a]
    field_simp [ne_of_gt (add_pos p.im_pos q.im_pos)]
    ring

private theorem hyperbolic_centers (p q : UpperHalfPlane) :
    ∃! c, IsMetricCenter UpperHalfPlane p q c := by
  rcases exists_reflection p q with ⟨c, hc⟩
  refine ⟨c, hc ▸ reflection_center p c, fun d hd => ?_⟩
  exact metricCenter_unique UpperHalfPlane p q d c hd (hc ▸ reflection_center p c)

private theorem hyperbolic_endpoints (p q : UpperHalfPlane) :
    ∃! x, IsMetricCenter UpperHalfPlane p x q := by
  refine ⟨reflection q p, reflection_center p q, fun x hx => ?_⟩
  rcases exists_reflection p x with ⟨c, hc⟩
  have h : c = q := metricCenter_unique UpperHalfPlane p x c q
    (hc ▸ reflection_center p c) hx
  simpa only [h] using hc.symm

private theorem normed_center (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (p q : F) : IsMetricCenter F p q (midpoint ℝ p q) := by
  apply metricCenter_of_reflection F p q (midpoint ℝ p q)
    (AffineIsometryEquiv.pointReflection ℝ (midpoint ℝ p q)).toIsometryEquiv
  · exact AffineIsometryEquiv.pointReflection_midpoint_left p q
  · exact AffineIsometryEquiv.pointReflection_midpoint_right p q
  · intro x
    change dist x (AffineIsometryEquiv.pointReflection ℝ (midpoint ℝ p q) x) = _
    simpa only [dist_comm] using
      AffineIsometryEquiv.dist_pointReflection_self_real (midpoint ℝ p q) x
  · rw [dist_left_midpoint, dist_midpoint_right, Real.norm_two]
    ring

private theorem reflection_map (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : UpperHalfPlane ≃ᵢ F) (c p : UpperHalfPlane) :
    e (reflection c p) = AffineIsometryEquiv.pointReflection ℝ (e c) (e p) := by
  have h : midpoint ℝ (e p) (e (reflection c p)) = e c :=
    metricCenter_unique F (e p) (e (reflection c p)) _ _
      (normed_center F _ _)
      (metricCenter_map UpperHalfPlane F e p (reflection c p) c (reflection_center p c))
  rw [← h, AffineIsometryEquiv.pointReflection_midpoint_left]

private theorem affine_reflections_reverse (F : Type*) [NormedAddCommGroup F]
    [NormedSpace ℝ F] (p q r z : F) :
    AffineIsometryEquiv.pointReflection ℝ p
      (AffineIsometryEquiv.pointReflection ℝ q (AffineIsometryEquiv.pointReflection ℝ r z)) =
    AffineIsometryEquiv.pointReflection ℝ r
      (AffineIsometryEquiv.pointReflection ℝ q (AffineIsometryEquiv.pointReflection ℝ p z)) := by
  simp only [AffineIsometryEquiv.pointReflection_apply, vsub_eq_sub, vadd_eq_add]
  abel

private theorem hyperbolic_reflections_not_reverse :
    ∃ p q r z : UpperHalfPlane,
      reflection p (reflection q (reflection r z)) ≠
        reflection r (reflection q (reflection p z)) := by
  let p := UpperHalfPlane.I
  let q : UpperHalfPlane := ⟨⟨0, 2⟩, by norm_num⟩
  let r : UpperHalfPlane := ⟨⟨1, 1⟩, by norm_num⟩
  refine ⟨p, q, r, p, fun h => ?_⟩
  have h' := congrArg (fun z : UpperHalfPlane => (z : ℂ).re) h
  simp only [reflection_coe] at h'
  norm_num [p, q, r, Complex.div_re, Complex.div_im, Complex.normSq_apply,
    Complex.inv_re, Complex.inv_im] at h'

private theorem hyperbolic_not_normed (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] :
    IsEmpty (UpperHalfPlane ≃ᵢ F) := by
  refine ⟨fun e => ?_⟩
  rcases hyperbolic_reflections_not_reverse with ⟨p, q, r, z, h⟩
  apply h
  apply e.injective
  simp only [reflection_map]
  exact affine_reflections_reverse F (e p) (e q) (e r) (e z)


/--
**Mazur–Ulam Problem 69 refuted.** The Scottish Book Problem 69 claim is false: there is a
nonempty complete pseudometric space $E$ such that (1) for all $p, q \in E$ there is exactly one
point $c \in E$ that is the metric center of $(p, q)$, and (2) for all $p, q \in E$ there is
exactly one point $x \in E$ such that $q$ is the metric center of $(p, x)$, but there is no
complete real normed space $F$ with an isometric bijection $E \to F$.

Source: S. Mazur and
S. Ulam, Problem 69 of the Scottish Book; typescript Ad 69 records the
negative answer (S. Mazur, December 21, 1936).
-/
theorem mazurUlam69_refuted : ¬ ScottishBookProblem69Claim := by
  intro h
  rcases h UpperHalfPlane hyperbolic_centers hyperbolic_endpoints with
    ⟨F, hF, hℝ, _, ⟨e⟩⟩
  let _ := hF
  let _ := hℝ
  let _ := hyperbolic_not_normed F
  exact isEmptyElim e

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook69Wanted
