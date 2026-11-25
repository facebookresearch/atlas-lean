/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Mazur–Ulam's Problem 69 in the Scottish Book

The hyperbolic upper half-plane refutes the proposed metric characterization of real Banach
spaces. The iterated center sets reduce to the hyperbolic midpoint after one step.
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

open scoped UpperHalfPlane
open Real

noncomputable section

-- The displacement per unit of endpoint height determines both midpoint coordinates.
private def slope (p q : ℍ) : ℝ := (q.re - p.re) / (p.im + q.im)

private def hypMid (p q : ℍ) : ℍ :=
  ⟨⟨p.re + p.im * slope p q, √(p.im * q.im * (1 + slope p q ^ 2))⟩, by
    change 0 < √_
    positivity⟩

private lemma mid_re (p q : ℍ) : (hypMid p q).re = p.re + p.im * slope p q := rfl

private lemma mid_im_sq (p q : ℍ) :
    (hypMid p q).im ^ 2 = p.im * q.im * (1 + slope p q ^ 2) := by
  apply Real.sq_sqrt
  positivity

private lemma cosh_double (r : ℝ) : cosh (2 * r) = 2 * cosh r ^ 2 - 1 := by
  rw [cosh_two_mul, sinh_sq]
  ring

private lemma mid_weight (p q : ℍ) :
    2 * cosh (dist p q / 2) = (1 / p.im + 1 / q.im) * (hypMid p q).im := by
  apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
  calc
    (2 * cosh (dist p q / 2)) ^ 2 = 2 * (cosh (dist p q) + 1) := by
      have h := cosh_double (dist p q / 2)
      rw [show 2 * (dist p q / 2) = dist p q by ring] at h
      linarith
    _ = _ := by
      rw [UpperHalfPlane.cosh_dist', mul_pow, mid_im_sq, slope]
      field_simp [p.im_ne_zero, q.im_ne_zero, (add_pos p.im_pos q.im_pos).ne']
      ring

-- This identity recovers the distance to the midpoint anywhere on the metric segment.
private lemma cosh_mid_dist (p q z : ℍ) :
    (2 * cosh (dist p q / 2)) * cosh (dist (hypMid p q) z) =
      cosh (dist p z) + cosh (dist q z) := by
  rw [mid_weight, UpperHalfPlane.cosh_dist', UpperHalfPlane.cosh_dist',
    UpperHalfPlane.cosh_dist', mid_re, mid_im_sq, slope]
  field_simp [p.im_ne_zero, q.im_ne_zero, z.im_ne_zero, (hypMid p q).im_ne_zero,
    (add_pos p.im_pos q.im_pos).ne']
  ring

private lemma dist_mid_of_between (p q z : ℍ) (hz : dist p z + dist z q = dist p q) :
    dist (hypMid p q) z = |(dist p z - dist z q) / 2| := by
  apply cosh_strictMonoOn.injOn dist_nonneg (abs_nonneg _)
  rw [cosh_abs]
  apply mul_left_cancel₀ (show 2 * cosh (dist p q / 2) ≠ 0 by positivity)
  rw [cosh_mid_dist, ← hz, dist_comm q z]
  generalize dist p z = a, dist z q = b
  have ha : (a + b) / 2 + (a - b) / 2 = a := by ring
  have hb : (a + b) / 2 - (a - b) / 2 = b := by ring
  calc
    cosh a + cosh b = cosh ((a + b) / 2 + (a - b) / 2) +
        cosh ((a + b) / 2 - (a - b) / 2) := by rw [ha, hb]
    _ = _ := by rw [cosh_add, cosh_sub]; ring

private lemma mid_dist_left (p q : ℍ) : dist (hypMid p q) p = dist p q / 2 := by
  simpa [abs_div] using dist_mid_of_between p q p (by simp)

private lemma mid_dist_right (p q : ℍ) : dist (hypMid p q) q = dist p q / 2 := by
  simpa [abs_div] using dist_mid_of_between p q q (by simp)

private lemma eq_mid_of_half (p q z : ℍ)
    (hp : dist p z = dist p q / 2) (hq : dist z q = dist p q / 2) :
    z = hypMid p q := by
  have h := dist_mid_of_between p q z (by linarith)
  rw [hp, hq, sub_self, zero_div, abs_zero] at h
  exact (dist_eq_zero.mp h).symm

private lemma centerSets_one (p q : ℍ) :
    metricCenterSets ℍ p q 1 = {hypMid p q} := by
  let S := metricCenterSets ℍ p q 0
  have hp : p ∈ S := by simp [S, metricCenterSets]
  have hq : q ∈ S := by simp [S, metricCenterSets]
  have hball : S ⊆ Metric.closedBall (hypMid p q) (dist p q / 2) := by
    intro z hz
    change dist p z + dist z q = dist p q at hz
    rw [Metric.mem_closedBall, dist_comm, dist_mid_of_between p q z hz, abs_le]
    constructor <;> linarith [dist_nonneg (x := p) (y := z), dist_nonneg (x := z) (y := q)]
  have hd : Metric.diam S = dist p q := by
    refine le_antisymm ?_
      (Metric.dist_le_diam_of_mem (Metric.isBounded_closedBall.subset hball) hp hq)
    linarith [Metric.diam_le_of_subset_closedBall (by positivity) hball]
  ext z
  change (z ∈ S ∧ ∀ x ∈ S, dist z x ≤ Metric.diam S / 2) ↔ z = hypMid p q
  rw [hd]
  constructor
  · rintro ⟨hz, h⟩
    change dist p z + dist z q = dist p q at hz
    have hzp := h p hp
    rw [dist_comm] at hzp
    exact eq_mid_of_half p q z (by linarith [h q hq]) (by linarith [h q hq])
  · rintro rfl
    constructor
    · change dist p (hypMid p q) + dist (hypMid p q) q = dist p q
      rw [dist_comm, mid_dist_left, mid_dist_right]
      ring
    · intro x hx
      simpa only [dist_comm (hypMid p q) x] using Metric.mem_closedBall.mp (hball hx)

private lemma centerSets_succ (p q : ℍ) (n : ℕ) :
    metricCenterSets ℍ p q (n + 1) = {hypMid p q} := by
  induction n with
  | zero => exact centerSets_one p q
  | succ n ih => rw [metricCenterSets, ih]; simp

private lemma isCenter_iff (p q z : ℍ) : IsMetricCenter ℍ p q z ↔ z = hypMid p q := by
  have unique (y : ℍ) (hy : ∀ n, y ∈ metricCenterSets ℍ p q n) : y = hypMid p q := by
    simpa only [centerSets_one, Set.mem_singleton_iff] using hy 1
  refine ⟨fun h => unique z h.1, ?_⟩
  rintro rfl
  refine ⟨fun n => ?_, unique⟩
  cases n with
  | zero =>
    change dist p (hypMid p q) + dist (hypMid p q) q = dist p q
    rw [dist_comm, mid_dist_left, mid_dist_right]
    ring
  | succ n => rw [centerSets_succ]; exact Set.mem_singleton _

-- Fixing the first endpoint, solve the two midpoint coordinate equations for the other endpoint.
private def extendThrough (p q : ℍ) : ℍ :=
  let t := (q.re - p.re) / p.im
  let h := q.im ^ 2 / (p.im * (1 + t ^ 2))
  ⟨⟨q.re + h * t, h⟩, by change 0 < q.im ^ 2 / _; positivity⟩

private lemma extend_im (p q : ℍ) :
    (extendThrough p q).im = q.im ^ 2 / (p.im * (1 + ((q.re - p.re) / p.im) ^ 2)) := rfl

private lemma extend_re (p q : ℍ) :
    (extendThrough p q).re = q.re + (extendThrough p q).im * ((q.re - p.re) / p.im) := rfl

private lemma mid_extend (p q : ℍ) : hypMid p (extendThrough p q) = q := by
  have ht : slope p (extendThrough p q) = (q.re - p.re) / p.im := by
    rw [slope, extend_re]
    field_simp [p.im_ne_zero, (add_pos p.im_pos (extendThrough p q).im_pos).ne']
    ring
  apply UpperHalfPlane.ext_re_im
  · rw [mid_re, ht]
    field_simp [p.im_ne_zero]
    ring
  · apply (sq_eq_sq₀ (UpperHalfPlane.im_pos _).le q.im_pos.le).mp
    rw [mid_im_sq, ht, extend_im]
    field_simp

private lemma extend_mid (p x : ℍ) : extendThrough p (hypMid p x) = x := by
  have ht : ((hypMid p x).re - p.re) / p.im = slope p x := by
    rw [mid_re]
    field_simp [p.im_ne_zero]
    ring
  have hy : (extendThrough p (hypMid p x)).im = x.im := by
    rw [extend_im, ht, mid_im_sq]
    field_simp
  refine UpperHalfPlane.ext_re_im ?_ hy
  rw [extend_re, hy, ht, mid_re, slope]
  field_simp [(add_pos p.im_pos x.im_pos).ne']
  ring

private lemma map_mid {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : ℍ ≃ᵢ F) (p q : ℍ) : e (hypMid p q) = midpoint ℝ (e p) (e q) := by
  obtain ⟨z, hz⟩ := e.surjective (midpoint ℝ (e p) (e q))
  have hp : dist p z = dist p q / 2 := by
    rw [← e.dist_eq p z, hz, dist_left_midpoint, e.dist_eq]
    norm_num [div_eq_inv_mul]
  have hq : dist z q = dist p q / 2 := by
    rw [← e.dist_eq z q, hz, dist_midpoint_right, e.dist_eq]
    norm_num [div_eq_inv_mul]
  rwa [← eq_mid_of_half p q z hp hq]

-- In a real normed space, doubling rays from a fixed point doubles all distances.
private lemma double_dist {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : ℍ ≃ᵢ F) (p a b : ℍ) : dist (extendThrough p a) (extendThrough p b) = 2 * dist a b := by
  have ha := map_mid e p (extendThrough p a)
  have hb := map_mid e p (extendThrough p b)
  rw [mid_extend] at ha hb
  rw [← e.dist_eq a b, ha, hb, dist_eq_norm_vsub F (midpoint _ _ _) _,
    midpoint_vsub_midpoint_same_left,
    norm_smul, ← dist_eq_norm_vsub F, e.dist_eq, invOf_eq_inv, norm_inv]
  norm_num
  ring

private lemma no_isometry {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : ℍ ≃ᵢ F) : False := by
  let p : ℍ := ⟨⟨0, 1⟩, zero_lt_one⟩
  let a : ℍ := ⟨⟨1, 1⟩, zero_lt_one⟩
  let b : ℍ := ⟨⟨-1, 1⟩, zero_lt_one⟩
  -- Their extensions have coordinates (±3/2, 1/2), giving cosh values 19 and 17.
  have h := congrArg cosh (double_dist e p a b)
  rw [cosh_double, UpperHalfPlane.cosh_dist', UpperHalfPlane.cosh_dist'] at h
  norm_num [extendThrough, p, a, b] at h

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
  have hc (p q : ℍ) : ∃! z, IsMetricCenter ℍ p q z :=
    ⟨hypMid p q, (isCenter_iff ..).2 rfl, fun z => (isCenter_iff p q z).1⟩
  have he (p q : ℍ) : ∃! x, IsMetricCenter ℍ p x q := by
    refine ⟨extendThrough p q, (isCenter_iff ..).2 (mid_extend p q).symm, ?_⟩
    intro x hx
    rw [(isCenter_iff ..).1 hx, extend_mid]
  obtain ⟨F, _, _, _, ⟨e⟩⟩ := h ℍ hc he
  exact no_isometry e

end

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook69Wanted
