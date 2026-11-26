/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import MathlibExt.Combinatorics.SimpleGraph.TreeMetric

import Mathlib.Tactic.Linarith
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Ring

/-!
# Tree-like metrics are totally split-decomposable

A canonical split decomposition of a finite metric satisfying the four-point condition has
zero residue. The proof shows that coherent residues inherit the four-point condition and that
a nonzero finite metric satisfying it has a coherent pendant split.

Sources: H.-J. Bandelt and A. W. M. Dress, "A canonical decomposition theory for metrics on a finite
set", Advances in Mathematics 92 (1992) 47–105, doi:10.1016/0001-8708(92)90061-O; statement read in
A. Dress, K. T. Huber and V. Moulton, "Metric spaces in pure and applied mathematics", Documenta
Mathematica, Extra Volume Quadratic Forms LSU (2001) 121–139, pp. 133–135; P. Buneman, "A note on
the metric properties of trees", Journal of Combinatorial Theory, Series B 17 (1974) 48–50.
-/

@[expose] public section

namespace WantedExt.Biology.ComputationalBiology.SplitDecompositionWanted

open MathlibExt.Biology.Phylogenetics.Buneman

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- `d` is a **metric** (pseudometric): zero diagonal, symmetric, triangle inequality. -/
def IsMetric (d : X → X → ℝ) : Prop :=
  (∀ x, d x x = 0) ∧ (∀ x y, d x y = d y x) ∧ ∀ x y z, d x z ≤ d x y + d y z

/-- The split metric `δ_A`: `1` across the split `A | X \ A`, `0` within each side. -/
def splitMetric (A : Finset X) (x y : X) : ℝ :=
  if (x ∈ A ∧ y ∉ A) ∨ (x ∉ A ∧ y ∈ A) then 1 else 0

/-- `d` is a **split metric**: `d = c · δ_A` for a proper nonempty `A` and `c > 0` (a metric with
exactly two zero-distance classes). -/
def IsSplitMetric (d : X → X → ℝ) : Prop :=
  ∃ A : Finset X, ∃ c : ℝ, A.Nonempty ∧ A ≠ Finset.univ ∧ 0 < c ∧
    ∀ x y, d x y = c * splitMetric A x y

/-- `f` **dominates** `d`: `d(x, y) ≤ f(x) + f(y)` for all `x, y`. -/
def Dominates (f : X → ℝ) (d : X → X → ℝ) : Prop :=
  ∀ x y, d x y ≤ f x + f y

/-- The family `ds` of `k` summands together with `r` is **coherent**: every function dominating
`∑ ds i + r` is a sum `∑ fs i + f₀` of functions dominating the respective summands. -/
def IsCoherent {k : ℕ} (ds : Fin k → X → X → ℝ) (r : X → X → ℝ) : Prop :=
  ∀ f : X → ℝ, Dominates f (fun x y => ∑ i, ds i x y + r x y) →
    ∃ (fs : Fin k → X → ℝ) (f₀ : X → ℝ), (∀ x, f x = ∑ i, fs i x + f₀ x) ∧
      (∀ i, Dominates (fs i) (ds i)) ∧ Dominates f₀ r

/-- `s + r` is a **coherent pair**: every function dominating `s + r` is `f₁ + f₂` with `f₁`
dominating `s` and `f₂` dominating `r`. -/
def IsCoherentPair (s r : X → X → ℝ) : Prop :=
  ∀ f : X → ℝ, Dominates f (fun x y => s x y + r x y) →
    ∃ f₁ f₂ : X → ℝ, (∀ x, f x = f₁ x + f₂ x) ∧ Dominates f₁ s ∧ Dominates f₂ r

/-- `d` is **split-prime**: it is not a coherent sum `s + r` of a split metric `s` and a metric
`r`. -/
def IsSplitPrime (d : X → X → ℝ) : Prop :=
  ¬ ∃ s r : X → X → ℝ, IsSplitMetric s ∧ IsMetric r ∧ IsCoherentPair s r ∧
    ∀ x y, d x y = s x y + r x y

/-- `(ds, r)` is a **canonical split decomposition** of `d`: the `ds i` are split metrics, `r` is a
split-prime metric, `d = ∑ ds i + r`, the decomposition is coherent, and the `ds i` are linearly
independent. -/
def IsCanonicalDecomp (d : X → X → ℝ) (k : ℕ) (ds : Fin k → X → X → ℝ) (r : X → X → ℝ) :
    Prop :=
  (∀ i, IsSplitMetric (ds i)) ∧ IsMetric r ∧ IsSplitPrime r ∧
    (∀ x y, d x y = ∑ i, ds i x y + r x y) ∧ IsCoherent ds r ∧
    ∀ c : Fin k → ℝ, (∀ x y, ∑ i, c i * ds i x y = 0) → ∀ i, c i = 0

private lemma metric_nonneg {Y : Type*} {d : Y → Y → ℝ} (hd : IsMetric d) (x y : Y) :
    0 ≤ d x y := by
  have h := hd.2.2 x y x
  rw [hd.1, hd.2.1 y x] at h
  linarith

private lemma metric_zero_class {Y : Type*} {d : Y → Y → ℝ} (hd : IsMetric d)
    {a x : Y} (hx : d a x = 0) (y : Y) : d x y = d a y := by
  have h₁ := hd.2.2 a x y
  have h₂ := hd.2.2 x a y
  rw [hx] at h₁
  rw [hd.2.1 x a, hx] at h₂
  linarith

private lemma coherent_tight {Y : Type*} {k : ℕ} {d r : Y → Y → ℝ}
    {ds : Fin k → Y → Y → ℝ} {f f₀ : Y → ℝ} {fs : Fin k → Y → ℝ}
    (hdecomp : ∀ x y, d x y = ∑ i, ds i x y + r x y)
    (hf : ∀ x, f x = ∑ i, fs i x + f₀ x) (hfs : ∀ i, Dominates (fs i) (ds i))
    (hr : Dominates f₀ r) {x y : Y} (hxy : d x y = f x + f y) :
    r x y = f₀ x + f₀ y := by
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hfs i x y)
  rw [Finset.sum_add_distrib] at hsum
  have he := hdecomp x y
  rw [hxy, hf x, hf y] at he
  have h := hr x y
  linarith

private lemma residue_fourPoint {Y : Type*} {d r : Y → Y → ℝ} (hd : IsMetric d)
    (htree : FourPointCondition d) {k : ℕ} {ds : Fin k → Y → Y → ℝ}
    (hdecomp : ∀ x y, d x y = ∑ i, ds i x y + r x y) (hcoh : IsCoherent ds r) :
    FourPointCondition r := by
  intro x y z t
  let a := (d x y + d x z - d y z) / 2
  let b := d x y - a
  let f := fun u => max (d x u - a) (d y u - b)
  have hab : a + b = d x y := by dsimp [b]; ring
  have ha : 0 ≤ a := by dsimp [a]; linarith [hd.2.2 y x z, hd.2.1 y x]
  have hb : 0 ≤ b := by dsimp [b, a]; linarith [hd.2.2 x y z]
  have hfx : f x = a := by
    dsimp [f]
    rw [hd.1 x, hd.2.1 y x, max_eq_right] <;> linarith
  have hfy : f y = b := by
    dsimp [f]
    rw [hd.1 y, max_eq_left]; linarith
  have hfz : f z = d x z - a := by
    dsimp [f, b, a]
    rw [max_eq_left]; linarith
  have hdom : Dominates f d := by
    intro u v
    have h₁ := le_max_left (d x u - a) (d y u - b)
    have h₂ := le_max_right (d x u - a) (d y u - b)
    have h₃ := le_max_left (d x v - a) (d y v - b)
    have h₄ := le_max_right (d x v - a) (d y v - b)
    rcases le_max_iff.mp (htree u v x y) with h | h
    · rw [hd.2.1 u x, hd.2.1 v y] at h
      dsimp [f]
      linarith
    · rw [hd.2.1 u y, hd.2.1 v x] at h
      dsimp [f]
      linarith
  obtain ⟨fs, f₀, hf, hfs, hr⟩ := hcoh f (fun u v => by
    change ∑ i, ds i u v + r u v ≤ f u + f v
    rw [← hdecomp]
    exact hdom u v)
  have hxz := coherent_tight hdecomp hf hfs hr (x := x) (y := z) (by rw [hfx, hfz]; ring)
  have hyz := coherent_tight hdecomp hf hfs hr (x := y) (y := z) (by
    rw [hfy, hfz]; dsimp [b, a]; ring)
  have hxy := hr x y
  have hzt := hr z t
  rcases le_total (d x t - a) (d y t - b) with h | h
  · have hyt := coherent_tight hdecomp hf hfs hr (x := y) (y := t) (by
      rw [hfy]; dsimp [f]; rw [max_eq_right h]; ring)
    apply le_trans (b := r x z + r y t) _ (le_max_left _ _)
    rw [hxz, hyt]
    linarith
  · have hxt := coherent_tight hdecomp hf hfs hr (x := x) (y := t) (by
      rw [hfx]; dsimp [f]; rw [max_eq_left h]; ring)
    apply le_trans (b := r x t + r y z) _ (le_max_right _ _)
    rw [hxt, hyz]
    linarith

private lemma pendant_split {Y : Type*} [DecidableEq Y]
    {d : Y → Y → ℝ} (hd : IsMetric d) (A : Finset Y) (hA : A.Nonempty)
    (hzero : ∀ x ∈ A, ∀ y ∈ A, d x y = 0) (c : ℝ) (hc : 0 ≤ c)
    (hgap : ∀ a ∈ A, ∀ y ∉ A, ∀ z ∉ A, 2 * c ≤ d a y + d a z - d y z) :
    IsMetric (fun x y => d x y - c * splitMetric A x y) ∧
      IsCoherentPair (fun x y => c * splitMetric A x y)
        (fun x y => d x y - c * splitMetric A x y) := by
  have hcross : ∀ a ∈ A, ∀ y ∉ A, c ≤ d a y := by
    intro a ha y hy
    have h := hgap a ha y hy y hy
    rw [hd.1] at h
    linarith
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · intro x
      simp [splitMetric, hd.1]
    · intro x y
      change d x y - c * splitMetric A x y = d y x - c * splitMetric A y x
      rw [hd.2.1 x y]
      by_cases hx : x ∈ A <;> by_cases hy : y ∈ A <;> simp [splitMetric, hx, hy]
    · intro x y z
      have htri := hd.2.2 x y z
      by_cases hx : x ∈ A <;> by_cases hy : y ∈ A <;> by_cases hz : z ∈ A <;>
        simp only [splitMetric, hx, hy, hz, not_true_eq_false, not_false_eq_true, and_self,
          and_true, and_false, or_self, or_false, false_or,
          ite_true, ite_false, mul_one, mul_zero, sub_zero]
      · exact htri
      · linarith
      · have h₁ := hcross x hx y hy
        have h₂ := hcross z hz y hy
        rw [hzero x hx z hz, hd.2.1 y z]
        linarith
      · linarith
      · linarith
      · have h := hgap y hy x hx z hz
        rw [hd.2.1 y x] at h
        linarith
      · linarith
      · exact htri
  · intro f hf
    have hdom : Dominates f d := by
      intro x y
      have h := hf x y
      dsimp at h
      linarith
    obtain ⟨a, ha, hmin⟩ := Finset.exists_min_image A f hA
    have hfpos : ∀ x, 0 ≤ f x := by
      intro x
      have h := hdom x x
      rw [hd.1] at h
      linarith
    let u := min (f a) c
    let v := c - u
    let f₁ := fun x => if x ∈ A then u else v
    have hu : 0 ≤ u := le_min (hfpos a) hc
    have hv : 0 ≤ v := sub_nonneg.mpr (min_le_right _ _)
    have huv : u + v = c := by dsimp [v]; ring
    have hule : ∀ x ∈ A, u ≤ f x := fun x hx => (min_le_left _ _).trans (hmin x hx)
    have hB : ∀ y ∉ A, ∀ z ∉ A, d y z ≤ f y + f z - 2 * v := by
      intro y hy z hz
      by_cases h : c ≤ f a
      · have hvzero : v = 0 := by dsimp [v, u]; rw [min_eq_right h]; ring
        simpa [hvzero] using hdom y z
      · have huval : u = f a := min_eq_left (le_of_not_ge h)
        have h₁ := hdom a y
        have h₂ := hdom a z
        have h₃ := hgap a ha y hy z hz
        dsimp [v]
        rw [huval]
        linarith
    refine ⟨f₁, fun x => f x - f₁ x, fun x => by ring, ?_, ?_⟩
    · intro x y
      by_cases hx : x ∈ A <;> by_cases hy : y ∈ A <;>
        simp [splitMetric, f₁, hx, hy] <;> linarith
    · intro x y
      by_cases hx : x ∈ A <;> by_cases hy : y ∈ A <;>
        simp only [splitMetric, f₁, hx, hy, not_true_eq_false, not_false_eq_true, and_self,
          and_true, and_false, or_self, or_false, false_or,
          ite_true, ite_false, mul_one, mul_zero, sub_zero]
      · rw [hzero x hx y hy]
        linarith [hule x hx, hule y hy]
      · have h := hdom x y
        dsimp [v]
        linarith
      · have h := hdom x y
        dsimp [v]
        linarith
      · linarith [hB x hx y hy]

private lemma splitPrime_fourPoint_zero {Y : Type*} [Fintype Y] [DecidableEq Y]
    {d : Y → Y → ℝ} (hd : IsMetric d) (htree : FourPointCondition d)
    (hprime : IsSplitPrime d) : ∀ x y, d x y = 0 := by
  classical
  intro x y
  by_contra hxy
  have hxypos : 0 < d x y := lt_of_le_of_ne (metric_nonneg hd x y) (Ne.symm hxy)
  obtain ⟨⟨a, b⟩, _, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun p : Y × Y => d p.1 p.2) ⟨(x, y), Finset.mem_univ _⟩
  have hM : ∀ u v, d u v ≤ d a b := fun u v => hmax (u, v) (Finset.mem_univ _)
  have hab : 0 < d a b := hxypos.trans_le (hM x y)
  let A := Finset.univ.filter fun u => d a u = 0
  let B := Finset.univ.filter fun u => d a u ≠ 0
  have hA : ∀ u, u ∈ A ↔ d a u = 0 := by intro u; simp [A]
  have hB : ∀ u, u ∈ B ↔ d a u ≠ 0 := by intro u; simp [B]
  have ha : a ∈ A := (hA a).mpr (hd.1 a)
  have hb : b ∈ B := (hB b).mpr hab.ne'
  obtain ⟨t, ht, hmin⟩ := Finset.exists_min_image B (d a) ⟨b, hb⟩
  have htpos : 0 < d a t :=
    lt_of_le_of_ne (metric_nonneg hd a t) (Ne.symm ((hB t).mp ht))
  let c := d a t / 2
  have hc : 0 < c := by dsimp [c]; linarith
  have hzero : ∀ u ∈ A, ∀ v ∈ A, d u v = 0 := by
    intro u hu v hv
    rw [metric_zero_class hd ((hA u).mp hu) v]
    exact (hA v).mp hv
  have hgap : ∀ e ∈ A, ∀ u ∉ A, ∀ v ∉ A, 2 * c ≤ d e u + d e v - d u v := by
    intro e he u hu v hv
    have h₁ := hmin u ((hB u).mpr (fun h => hu ((hA u).mpr h)))
    have h₂ := hmin v ((hB v).mpr (fun h => hv ((hA v).mpr h)))
    rw [metric_zero_class hd ((hA e).mp he) u,
      metric_zero_class hd ((hA e).mp he) v]
    dsimp [c]
    rcases le_max_iff.mp (htree a b u v) with h | h
    · linarith [hM b v]
    · linarith [hM b u]
  obtain ⟨hr, hcoh⟩ := pendant_split hd A ⟨a, ha⟩ hzero c hc.le hgap
  apply hprime
  refine ⟨fun u v => c * splitMetric A u v,
    fun u v => d u v - c * splitMetric A u v, ?_, hr, hcoh, fun u v => by ring⟩
  refine ⟨A, c, ⟨a, ha⟩, ?_, hc, fun _ _ => rfl⟩
  intro h
  have hbA : b ∈ A := h ▸ Finset.mem_univ b
  exact hab.ne' ((hA b).mp hbA)

/-- **Tree-like metrics are totally split-decomposable** (Bandelt and Dress 1992, via Dress, Huber
and Moulton 2001): for every metric `d` (zero diagonal, symmetric, triangle inequality) on a finite
set `X` satisfying the four-point condition, and every canonical split decomposition `(ds, r)` of
`d`, the split-prime residue `r` vanishes.

Source: Bandelt and Dress (1992), via Dress, Huber and Moulton (2001), p. 134. -/
public theorem canonicalDecomp_residue_eq_zero_of_treeLike (d : X → X → ℝ)
    (hd : IsMetric d) (htree : FourPointCondition d) (k : ℕ) (ds : Fin k → X → X → ℝ)
    (r : X → X → ℝ) (hcanon : IsCanonicalDecomp d k ds r) :
    ∀ x y, r x y = 0 := by
  exact splitPrime_fourPoint_zero hcanon.2.1
    (residue_fourPoint hd htree hcanon.2.2.2.1 hcanon.2.2.2.2.1) hcanon.2.2.1

end WantedExt.Biology.ComputationalBiology.SplitDecompositionWanted
