/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.Stieltjes
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.Order.Compact
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Rat.Denumerable

/-!
# Helly's selection theorem

Every sequence of distribution functions on `ℝ` has a subsequence converging
pointwise to a monotone, right-continuous function at every continuity point
of the limit. The limit need not itself be a distribution function: mass may
escape to `±∞` (for example, the distribution functions of point masses at `n`
converge to `0`).

## Source

This formalizes the target "Theorem (Helly's selection theorem)"
(Lecture 12, Compactness section) of
`v1/Atlas/TheoryOfProbability/targets.yaml`: "Every sequence `F_n` of
distributions has a subsequence converging to a right continuous
nondecreasing `F` so that `lim F_{n(k)}(y) = F(y)` at all continuity points
of `F`." Its v1 formalization is
`v1/Atlas/TheoryOfProbability/code/HellySelection.lean` (`helly_selection`,
fully proved in v1).

## Main results

* `ProbabilityTheory.IsDistributionFunction`: a `StieltjesFunction ℝ` is a
  (cumulative) distribution function if it tends to `0` at `-∞` and to `1`
  at `+∞`; the bundle supplies monotonicity and right continuity.
* `ProbabilityTheory.helly_selection`: every sequence of distribution
  functions has a strictly monotone subsequence converging pointwise to a
  monotone, right-continuous function at every continuity point of the limit.

## Proof outline

Restrict the sequence to the rationals and extract a convergent subsequence
by compactness of `[0, 1]^ℚ` (a diagonal argument). The pointwise limit `g`
on `ℚ` is monotone and `[0, 1]`-valued; extend it to `ℝ` by the supremum `h`
of `g` over rationals below `x`, and take the right-limit regularisation `G`
of `h`. At a continuity point `x` of `G`, sandwich `F_{φ k} x` between its
values at rationals just below and just above `x`, where convergence is
known, and let the rationals close in on `x`.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace ProbabilityTheory

/-- **Distribution function.** A nondecreasing, right-continuous function
$F : \mathbb{R} \to \mathbb{R}$ (a Stieltjes function) is a (cumulative) distribution function if
$F(x) \to 0$ as $x \to -\infty$ and $F(x) \to 1$ as $x \to +\infty$.

These are exactly the distribution functions of probability measures on $\mathbb{R}$. -/
structure IsDistributionFunction (F : StieltjesFunction ℝ) : Prop where
  tendsto_atBot : Tendsto F atBot (𝓝 0)
  tendsto_atTop : Tendsto F atTop (𝓝 1)

/-- **Distribution functions are nonnegative.** If $F$ is a distribution function on
$\mathbb{R}$, then $0 \le F(x)$ for every $x \in \mathbb{R}$. -/
theorem IsDistributionFunction.nonneg {F : StieltjesFunction ℝ}
    (hF : IsDistributionFunction F) (x : ℝ) :
    0 ≤ F x :=
  le_of_tendsto hF.tendsto_atBot (eventually_atBot.mpr ⟨x, fun _ hy => F.mono hy⟩)

/-- **Distribution functions are at most one.** If $F$ is a distribution function on
$\mathbb{R}$, then $F(x) \le 1$ for every $x \in \mathbb{R}$. -/
theorem IsDistributionFunction.le_one {F : StieltjesFunction ℝ}
    (hF : IsDistributionFunction F) (x : ℝ) :
    F x ≤ 1 :=
  ge_of_tendsto hF.tendsto_atTop (eventually_atTop.mpr ⟨x, fun _ hy => F.mono hy⟩)

/-- **Distribution functions take values in the unit interval.** If $F$ is a distribution
function on $\mathbb{R}$, then $F(x) \in [0, 1]$ for every $x \in \mathbb{R}$. -/
theorem IsDistributionFunction.mem_Icc {F : StieltjesFunction ℝ}
    (hF : IsDistributionFunction F) (x : ℝ) :
    F x ∈ Icc (0 : ℝ) 1 :=
  ⟨hF.nonneg x, hF.le_one x⟩

/-- For a monotone, `[0, 1]`-valued function `g : ℚ → ℝ`, the supremum of `g` over
all rationals `r ≤ q` equals `g q`. This is the key bookkeeping step in the proof of
Helly's selection theorem, used to define the candidate limit on `ℝ` from values on `ℚ`. -/
private theorem sSup_image_rat_eq (g : ℚ → ℝ) (hg_mono : ∀ q₁ q₂ : ℚ, q₁ ≤ q₂ → g q₁ ≤ g q₂)
    (hg_bdd : ∀ q, 0 ≤ g q ∧ g q ≤ 1) (q : ℚ) :
    sSup (g '' { r : ℚ | (r : ℝ) ≤ ↑q }) = g q := by
  apply le_antisymm
  · apply csSup_le
    · exact ⟨g q, ⟨q, show (q : ℝ) ≤ ↑q from le_rfl, rfl⟩⟩
    · rintro _ ⟨r, (hr : (r : ℝ) ≤ ↑q), rfl⟩
      exact hg_mono r q (Rat.cast_le.mp hr)
  · exact le_csSup ⟨1, by rintro _ ⟨r, _, rfl⟩; exact (hg_bdd r).2⟩
      ⟨q, show (q : ℝ) ≤ ↑q from le_rfl, rfl⟩

/-- **Helly's selection theorem.** Let $(F_n)_{n \in \mathbb{N}}$ be a sequence of
distribution functions on $\mathbb{R}$. Then there are a strictly increasing map
$\varphi : \mathbb{N} \to \mathbb{N}$ and a nondecreasing, right-continuous function
$G : \mathbb{R} \to \mathbb{R}$ such that $F_{\varphi(k)}(x) \to G(x)$ as $k \to \infty$ at every
point $x \in \mathbb{R}$ at which $G$ is continuous.

The limit $G$ need not itself be a distribution function: it may lose mass to $\pm\infty$. -/
theorem helly_selection (F : ℕ → StieltjesFunction ℝ)
    (hF : ∀ n, IsDistributionFunction (F n)) :
    ∃ (φ : ℕ → ℕ) (G : StieltjesFunction ℝ),
      StrictMono φ ∧
      ∀ x, ContinuousAt (↑G) x → Tendsto (fun k => F (φ k) x) atTop (𝓝 (G x)) := by
  classical
  let v : ℕ → ℚ → Set.Icc (0 : ℝ) 1 :=
    fun n q => ⟨F n ↑q, (hF n).nonneg ↑q, (hF n).le_one ↑q⟩
  obtain ⟨a, φ, hφ_strict, hφ_conv⟩ := CompactSpace.tendsto_subseq v
  have hconv_rat : ∀ q : ℚ, Tendsto (fun k => F (φ k) (↑q)) atTop (𝓝 ↑(a q)) := by
    intro q
    have h1 : Tendsto (fun k => (v ∘ φ) k q) atTop (𝓝 (a q)) := tendsto_pi_nhds.mp hφ_conv q
    exact (continuous_subtype_val.tendsto _).comp h1
  let g : ℚ → ℝ := fun q => ↑(a q)
  have hg_mono : ∀ q₁ q₂ : ℚ, q₁ ≤ q₂ → g q₁ ≤ g q₂ := by
    intro p q hpq
    exact le_of_tendsto_of_tendsto (hconv_rat p) (hconv_rat q)
      (Eventually.of_forall fun k => (F (φ k)).mono (Rat.cast_le.mpr hpq))
  have hg_bdd : ∀ q, 0 ≤ g q ∧ g q ≤ 1 := fun q => (a q).2
  let h : ℝ → ℝ := fun x => sSup (g '' { q : ℚ | (q : ℝ) ≤ x })
  have hh_mono : Monotone h := by
    intro a b hab
    simp only [h]
    apply csSup_le_csSup
    · exact ⟨1, by rintro _ ⟨q, _, rfl⟩; exact (hg_bdd q).2⟩
    · obtain ⟨q, hq⟩ := exists_rat_lt a
      exact ⟨g q, ⟨q, le_of_lt hq, rfl⟩⟩
    · exact image_mono (fun q (hq : (q : ℝ) ≤ a) => le_trans hq hab)
  have hh_rat : ∀ q : ℚ, h (↑q) = g q := sSup_image_rat_eq g hg_mono hg_bdd
  let G := hh_mono.stieltjesFunction
  refine ⟨φ, G, hφ_strict, ?_⟩
  intro x hx_cont
  have hleft_eq : Function.leftLim h x = Function.rightLim h x := by
    have hlr := hh_mono.rightLim.continuousAt_iff_leftLim_eq_rightLim.mp hx_cont
    rw [leftLim_rightLim (hh_mono.tendsto_leftLim x)] at hlr
    rw [rightLim_rightLim (hh_mono.tendsto_rightLim x)] at hlr
    exact hlr
  have htend_left : Tendsto h (𝓝[<] x) (𝓝 (G x)) := by
    show Tendsto h (𝓝[<] x) (𝓝 (Function.rightLim h x))
    rw [← hleft_eq]; exact hh_mono.tendsto_leftLim x
  have htend_right : Tendsto h (𝓝[>] x) (𝓝 (G x)) :=
    hh_mono.tendsto_rightLim x
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := half_pos hε
  obtain ⟨r, hr_lt, hr_close⟩ : ∃ r : ℚ, (r : ℝ) < x ∧ G x - ε / 2 < h r := by
    have hev : ∀ᶠ y in 𝓝[<] x, dist (h y) (G x) < ε / 2 :=
      (Metric.tendsto_nhds.mp htend_left) (ε / 2) hε2
    rw [Filter.Eventually, mem_nhdsWithin] at hev
    obtain ⟨U, hU_open, hxU, hU_sub⟩ := hev
    obtain ⟨δ, hδ_pos, hδ_sub⟩ := Metric.isOpen_iff.mp hU_open x hxU
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (sub_lt_self x hδ_pos)
    refine ⟨r, hr2, ?_⟩
    have hr_mem : (r : ℝ) ∈ U ∩ Iio x :=
      ⟨hδ_sub (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith), hr2⟩
    have : dist (h ↑r) (G x) < ε / 2 := hU_sub hr_mem
    rw [Real.dist_eq, abs_lt] at this; linarith [this.1]
  obtain ⟨s, hs_lt, hs_close⟩ : ∃ s : ℚ, x < (s : ℝ) ∧ h s < G x + ε / 2 := by
    have hev : ∀ᶠ y in 𝓝[>] x, dist (h y) (G x) < ε / 2 :=
      (Metric.tendsto_nhds.mp htend_right) (ε / 2) hε2
    rw [Filter.Eventually, mem_nhdsWithin] at hev
    obtain ⟨V, hV_open, hxV, hV_sub⟩ := hev
    obtain ⟨δ, hδ_pos, hδ_sub⟩ := Metric.isOpen_iff.mp hV_open x hxV
    obtain ⟨s, hs1, hs2⟩ := exists_rat_btwn (show x < x + δ by linarith)
    refine ⟨s, hs1, ?_⟩
    have hs_mem : (s : ℝ) ∈ V ∩ Ioi x :=
      ⟨hδ_sub (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith), hs1⟩
    have : dist (h ↑s) (G x) < ε / 2 := hV_sub hs_mem
    rw [Real.dist_eq, abs_lt] at this; linarith [this.2]
  rw [hh_rat] at hr_close hs_close
  obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.mp (hconv_rat r)) (ε / 2) hε2
  obtain ⟨N₂, hN₂⟩ := (Metric.tendsto_atTop.mp (hconv_rat s)) (ε / 2) hε2
  refine ⟨max N₁ N₂, fun k hk => ?_⟩
  have hFr := hN₁ k (le_of_max_le_left hk)
  have hFs := hN₂ k (le_of_max_le_right hk)
  rw [Real.dist_eq, abs_lt] at hFr hFs
  have hle_r : F (φ k) ↑r ≤ F (φ k) x := (F (φ k)).mono (le_of_lt hr_lt)
  have hle_s : F (φ k) x ≤ F (φ k) ↑s := (F (φ k)).mono (le_of_lt hs_lt)
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end ProbabilityTheory
