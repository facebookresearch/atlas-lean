/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Order.Filter.AtTopBot.Defs

import Mathlib.Algebra.Field.TransferInstance
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Topology.MetricSpace.Snowflaking

/-!
# Negative answer to Scottish Book Problem 15.1

The space of real sequences with summable square roots of their absolute values has a bounded
sphere in a complete translation-invariant metric, but admits no compatible Banach norm.
-/

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook15Point1Wanted

/-- **Spaces of type (F).** A real vector space $E$ with a topology is of type (F) when addition
$E \times E \to E$ and scalar multiplication $\mathbb{R} \times E \to E$ are continuous and there
is a metric $d$ on $E$ that is translation invariant, $d(x + z, y + z) = d(x, y)$ for all
$x, y, z \in E$, that induces the topology of $E$, and that is complete: every Cauchy sequence
for $d$ converges for $d$. -/
def IsTypeF (E : Type) [TopologicalSpace E] [AddCommGroup E] [Module ℝ E] : Prop :=
  ∃ d : E → E → ℝ, (∀ x y, 0 ≤ d x y) ∧ (∀ x y, d x y = 0 ↔ x = y) ∧
    (∀ x y, d x y = d y x) ∧ (∀ x y z, d x z ≤ d x y + d y z) ∧
    (∀ x y z, d (x + z) (y + z) = d x y) ∧
    (∀ U : Set E, IsOpen U ↔ ∀ x ∈ U, ∃ ε > 0, ∀ y, d y x < ε → y ∈ U) ∧
    (∀ x : ℕ → E, (∀ ε > 0, ∃ N, ∀ m n, m ≥ N → n ≥ N → d (x m) (x n) < ε) →
      ∃ y, ∀ ε > 0, ∃ N, ∀ n, n ≥ N → d (x n) y < ε) ∧
    Continuous (fun p : E × E => p.1 + p.2) ∧ Continuous fun p : ℝ × E => p.1 • p.2

/-- **Spheres in the ray sense.** Let $E$ be a real vector space. A set $K \subseteq E$ is a
sphere when $0 \notin K$ and for every $x \ne 0$ in $E$ there is exactly one real $t > 0$ with
$t x \in K$; that is, every open ray from the origin meets $K$ exactly once. -/
def IsSphere (E : Type) [AddCommGroup E] [Module ℝ E] (K : Set E) : Prop :=
  0 ∉ K ∧ ∀ x : E, x ≠ 0 → ∃! t : ℝ, 0 < t ∧ t • x ∈ K

/-- **Sequentially bounded sets.** Let $E$ be a real vector space with a topology. A set
$R \subseteq E$ is bounded when for every sequence $(x_n)$ of points of $R$ and every sequence
$(t_n)$ of real numbers with $t_n \to 0$, the sequence $(t_n x_n)$ tends to $0$ in $E$.

This is the definition of boundedness as printed in the statement of Scottish Book
Problem 15.1. -/
def IsBoundedSet (E : Type) [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (R : Set E) : Prop :=
  ∀ (x : ℕ → E) (t : ℕ → ℝ), (∀ n, x n ∈ R) →
    Filter.Tendsto t Filter.atTop (nhds 0) →
    Filter.Tendsto (fun n => t n • x n) Filter.atTop (nhds 0)

/-- **Spaces of type (B).** A real vector space $E$ with a topology is of type (B) when there is
a function $\|\cdot\| : E \to \mathbb{R}$ with $\|x\| \ge 0$, with $\|x\| = 0$ exactly when
$x = 0$, with $\|x + y\| \le \|x\| + \|y\|$ and with $\|a x\| = |a| \, \|x\|$ for all
$x, y \in E$ and $a \in \mathbb{R}$, such that a set $U \subseteq E$ is open exactly when every
$x \in U$ has an $\varepsilon > 0$ with $y \in U$ whenever $\|y - x\| < \varepsilon$, and such
that every Cauchy sequence for $\|\cdot\|$ converges in $E$ for $\|\cdot\|$. -/
def AdmitsBanachNorm (E : Type) [TopologicalSpace E] [AddCommGroup E] [Module ℝ E] : Prop :=
  ∃ normFn : E → ℝ, (∀ x, 0 ≤ normFn x) ∧ (∀ x, normFn x = 0 ↔ x = 0) ∧
    (∀ x y, normFn (x + y) ≤ normFn x + normFn y) ∧
    (∀ (a : ℝ) (x : E), normFn (a • x) = |a| * normFn x) ∧
    (∀ U : Set E, IsOpen U ↔ ∀ x ∈ U, ∃ ε > 0, ∀ y, normFn (y - x) < ε → y ∈ U) ∧
    (∀ x : ℕ → E, (∀ ε > 0, ∃ N, ∀ m n, m ≥ N → n ≥ N → normFn (x m - x n) < ε) →
      ∃ y, ∀ ε > 0, ∃ N, ∀ n, n ≥ N → normFn (x n - y) < ε)

/-- **Scottish Book Problem 15.1.** The claim of Mazur and Orlicz that every real vector space $E$
with a topology that is of type (F) and contains a bounded sphere is of type (B). -/
def ScottishBookProblem15Point1Claim : Prop :=
  ∀ (E : Type) [TopologicalSpace E] [AddCommGroup E] [Module ℝ E],
    IsTypeF E → (∃ K : Set E, IsSphere E K ∧ IsBoundedSet E K) → AdmitsBanachNorm E

open Metric Filter
open scoped Topology

noncomputable section

-- With the square-root absolute value on the coefficient field, ordinary ℓ¹ has exactly
-- the additive metric of the real sequence space ℓ^(1/2).
private abbrev Coeff := Snowflaking ℝ (1 / 2) (by norm_num) (by norm_num)

private local instance coeffNormedField : NormedField Coeff where
  toField := (Snowflaking.ofSnowflaking : Coeff ≃ ℝ).field
  toMetricSpace := inferInstance
  norm a := Real.sqrt |a.val|
  dist_eq a b := by
    change dist a.val b.val ^ (1 / 2 : ℝ) = Real.sqrt |(-a.val + b.val)|
    rw [← Real.sqrt_eq_rpow, Real.dist_eq, ← abs_neg (a.val - b.val)]
    simp [sub_eq_add_neg, add_comm]
  norm_mul a b := by
    change Real.sqrt |a.val * b.val| = _
    rw [abs_mul, Real.sqrt_mul (abs_nonneg _)]

private local instance coeffComplete : CompleteSpace Coeff :=
  (Snowflaking.uniformEquiv : Coeff ≃ᵤ ℝ).completeSpace_iff.2 inferInstance

private abbrev Seq := lp (fun _ : ℕ => Coeff) 1

private def toCoeff : ℝ →+* Coeff :=
  (Snowflaking.ofSnowflaking : Coeff ≃ ℝ).ringEquiv.symm.toRingHom

private local instance realModule : Module ℝ Seq := Module.compHom Seq toCoeff

private theorem gauge_smul (a : ℝ) (x : Seq) : ‖a • x‖ = Real.sqrt |a| * ‖x‖ :=
  norm_smul (toCoeff a) x

private theorem seq_typeF : IsTypeF Seq := by
  refine ⟨dist, fun _ _ => dist_nonneg, fun _ _ => dist_eq_zero, dist_comm, dist_triangle,
    dist_add_right, fun _ => Metric.isOpen_iff, ?_, continuous_add, ?_⟩
  · intro x hx
    have hc : CauchySeq x := by
      apply Metric.cauchySeq_iff.2
      intro ε hε
      obtain ⟨N, hN⟩ := hx ε hε
      exact ⟨N, fun m hm n hn => hN m n hm hn⟩
    obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hc
    exact ⟨y, Metric.tendsto_atTop.1 hy⟩
  · have h : Continuous toCoeff := Snowflaking.continuous_toSnowflaking
    exact (h.comp continuous_fst).smul continuous_snd

private theorem seq_sphere : IsSphere Seq {x : Seq | ‖x‖ = 1} := by
  refine ⟨by simp, fun x hx => ?_⟩
  have hpos := norm_pos_iff.mpr hx
  refine ⟨‖x‖⁻¹ ^ 2, ⟨by positivity, ?_⟩, ?_⟩
  · change ‖_ • x‖ = 1
    rw [gauge_smul, abs_of_nonneg (sq_nonneg _), Real.sqrt_sq (by positivity),
      inv_mul_cancel₀ hpos.ne']
  · rintro t ⟨ht, heq⟩
    change ‖t • x‖ = 1 at heq
    rw [gauge_smul, abs_of_pos ht] at heq
    have hroot : Real.sqrt t = ‖x‖⁻¹ := by
      simpa using (eq_div_iff hpos.ne').2 heq
    rw [← hroot, Real.sq_sqrt ht.le]

private theorem seq_bounded : IsBoundedSet Seq {x : Seq | ‖x‖ = 1} := by
  intro x t hx ht
  have h : Tendsto (fun n => Real.sqrt |t n|) atTop (𝓝 0) := by
    simpa using ht.abs.sqrt
  apply tendsto_zero_iff_norm_tendsto_zero.2
  simpa only [gauge_smul, show ∀ n, ‖x n‖ = 1 from hx, mul_one] using h

-- Disjoint unit coordinate vectors add exactly in the additive metric.
private def unitVector (i : ℕ) : Seq := lp.single 1 i 1

private theorem gauge_sum_unitVector (s : Finset ℕ) :
    ‖∑ i ∈ s, unitVector i‖ = s.card := by
  simpa [unitVector] using
    (lp.norm_sum_single (p := 1) (by simp) (fun _ : ℕ => (1 : Coeff)) s)

private theorem seq_not_normable : ¬ AdmitsBanachNorm Seq := by
  rintro ⟨N, _, hzero, hadd, hsmul, hopen, _⟩
  have hzero' := (hzero 0).2 rfl
  -- An N-ball inside the metric unit ball must itself contain a small metric ball.
  obtain ⟨r, hr, houter⟩ :=
    (hopen (ball (0 : Seq) 1)).1 isOpen_ball 0 (mem_ball_self zero_lt_one)
  have hopenN : IsOpen {x : Seq | N x < r / 2} := by
    apply (hopen _).2
    intro x hx
    change N x < r / 2 at hx
    refine ⟨r / 2 - N x, sub_pos.2 hx, fun y hy => ?_⟩
    change N y < r / 2
    have h := hadd (y - x) x
    rw [sub_add_cancel] at h
    linarith
  obtain ⟨η, hη, hinner⟩ := Metric.isOpen_iff.1 hopenN 0 (by
    change N 0 < r / 2
    rw [hzero']
    positivity)
  obtain ⟨k, hk⟩ := exists_nat_gt η⁻¹
  have hkpos : 0 < (k : ℝ) := (inv_pos.mpr hη).trans hk
  let q := (k : ℝ)⁻¹ ^ 2
  have hq : Real.sqrt |q| = (k : ℝ)⁻¹ := by
    rw [abs_of_nonneg (sq_nonneg _), Real.sqrt_sq (by positivity)]
  have hatom (i : ℕ) : N (q • unitVector i) ≤ r / 2 := by
    apply le_of_lt
    apply hinner
    rw [mem_ball_zero_iff, gauge_smul, hq]
    have hu : ‖unitVector i‖ = 1 := by simpa using gauge_sum_unitVector {i}
    rw [hu, mul_one]
    exact (inv_lt_comm₀ hkpos hη).2 hk
  -- Average k² of these small vectors. Its N-value is at most r/2, while its
  -- distance from zero is exactly one.
  let s := Finset.range (k ^ 2)
  let v := ∑ i ∈ s, q • unitVector i
  have hcard : (s.card : ℝ) = (k : ℝ) ^ 2 := by simp [s]
  have hNv : N v ≤ (k : ℝ) ^ 2 * (r / 2) := calc
    N v ≤ ∑ i ∈ s, N (q • unitVector i) :=
      Finset.le_sum_of_subadditive N hzero'.le hadd _ _
    _ ≤ ∑ _i ∈ s, r / 2 := Finset.sum_le_sum fun i _ => hatom i
    _ = _ := by simp [hcard]
  have hNsmall : N (q • v) < r := calc
    N (q • v) = q * N v := by rw [hsmul, abs_of_nonneg (sq_nonneg _)]
    _ ≤ q * ((k : ℝ) ^ 2 * (r / 2)) := by gcongr
    _ = r / 2 := by
      dsimp [q]
      field_simp
    _ < r := half_lt_self hr
  have hunit : ‖q • v‖ = 1 := by
    rw [show v = q • ∑ i ∈ s, unitVector i from (Finset.smul_sum ..).symm,
      gauge_smul, gauge_smul, hq, gauge_sum_unitVector, hcard]
    field_simp
  have hlt := houter (q • v) (by simpa using hNsmall)
  exact (mem_ball_zero_iff.mp hlt).ne hunit

/--
**Negative answer to Scottish Book Problem 15.1.** The Mazur–Orlicz claim of Problem 15.1 is
false: there is a real vector space $E$ with a topology that is of type (F) and contains a
bounded sphere, but is not of type (B).

Source: S. Mazur and
W. Orlicz, Problem 15.1 of the Scottish Book; the typescript itself records
the negative answer (Ad 15.1, Mazur, May 1 1937) with the spaces `ℓ ^ p` and
`L ^ p` for `0 < p < 1`, with quasi-norm given by the sum (respectively
integral) of `|·| ^ p`, as counterexamples: they are of type (F), possess a
bounded sphere, and are not normable, hence not of type (B).
-/
theorem boundedSphereFImpliesB_refuted : ¬ ScottishBookProblem15Point1Claim := by
  intro h
  exact seq_not_normable (h Seq seq_typeF ⟨_, seq_sphere, seq_bounded⟩)

end

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook15Point1Wanted
