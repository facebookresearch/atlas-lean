/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Data.Rat.Cast.Order
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # The countably additive reading of Scottish Book Problem 169 -/

@[expose] public section

open Function MeasureTheory Set
open scoped ENNReal

namespace MathlibExt.MeasureTheory.ScottishBook169Wanted

/-- **Congruent plane sets.** Two sets $E$ and $F$ in the Euclidean plane $\mathbb{R}^2$ are
congruent when some isometry of the plane onto itself maps $E$ onto $F$. -/
def AreCongruent (E F : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∃ T : EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2), T '' E = F

/-- **Congruence-invariant set functions on the plane.** A function $\mu$ that assigns to every
subset of the Euclidean plane $\mathbb{R}^2$ a value in $[0, \infty]$ is congruence invariant when
$\mu(E) = \mu(F)$ for all congruent plane sets $E$ and $F$. -/
def IsCongruenceInvariant (μ : Set (EuclideanSpace ℝ (Fin 2)) → ENNReal) : Prop :=
  ∀ E F : Set (EuclideanSpace ℝ (Fin 2)), AreCongruent E F → μ E = μ F

/-- `μ` is countably additive on pairwise-disjoint families. This is the
countably-additive reading of "additive" in Problem 169; the typescript
does not say whether finite or countable additivity is meant. -/
def IsCountablyAdditive (μ : Set (EuclideanSpace ℝ (Fin 2)) → ENNReal) : Prop :=
  ∀ E : ℕ → Set (EuclideanSpace ℝ (Fin 2)),
    Pairwise (fun i j => Disjoint (E i) (E j)) → μ (⋃ i, E i) = ∑' i, μ (E i)

/-- The countably additive reading of Problem 169: there is a function
`μ`, defined for all plane sets, equal on congruent sets, countably
additive, extending Carathéodory's linear measure (the one-dimensional
Hausdorff measure on measurable sets), with values in `[0, +∞]`
(automatic for `ENNReal`). -/
def CountablyAdditiveCongruenceClaim : Prop :=
  ∃ μ : Set (EuclideanSpace ℝ (Fin 2)) → ENNReal,
    IsCongruenceInvariant μ ∧ IsCountablyAdditive μ ∧
    ∀ E : Set (EuclideanSpace ℝ (Fin 2)), MeasurableSet E →
      μ E = μH[1] E

private def RatShift := ↥(Icc (-1 : ℚ) 1)

private def translate (q : RatShift) (s : Set ℝ) : Set ℝ :=
  (fun x : ℝ => x + (q.val : ℝ)) '' s

private theorem exists_vitali_partition : ∃ V : Set ℝ,
    Pairwise (fun q₁ q₂ : RatShift => Disjoint (translate q₁ V) (translate q₂ V)) ∧
    Icc (0 : ℝ) 1 ⊆ ⋃ q : RatShift, translate q V ∧
    (⋃ q : RatShift, translate q V) ⊆ Icc (-1 : ℝ) 2 := by
  classical
  let I := ↥(Icc (0 : ℝ) 1)
  let s : Setoid I := {
    r := fun x y => ∃ q : ℚ, x.val - y.val = (q : ℝ)
    iseqv := {
      refl := fun x => ⟨0, by simp⟩
      symm := by
        rintro x y ⟨q, hq⟩
        exact ⟨-q, by rw [Rat.cast_neg, ← hq]; ring⟩
      trans := by
        rintro x y z ⟨q, hq⟩ ⟨r, hr⟩
        exact ⟨q + r, by rw [Rat.cast_add, ← hq, ← hr]; ring⟩ } }
  let rep (c : Quotient s) : ℝ := c.out.val
  let V := range rep
  have hsub : V ⊆ Icc (0 : ℝ) 1 := by
    rintro x ⟨c, rfl⟩
    exact c.out.property
  refine ⟨V, ?_, ?_, ?_⟩
  · intro q₁ q₂ hne
    refine disjoint_left.mpr ?_
    rintro x ⟨v₁, ⟨c₁, rfl⟩, rfl⟩ ⟨v₂, ⟨c₂, rfl⟩, h⟩
    have hr : s.r c₁.out c₂.out := by
      refine ⟨q₂.val - q₁.val, ?_⟩
      change rep c₁ - rep c₂ = _
      rw [Rat.cast_sub]
      linarith
    have hc : c₁ = c₂ := (Quotient.out_eq c₁).symm.trans
      ((Quotient.sound hr).trans (Quotient.out_eq c₂))
    rw [hc] at h
    exact hne (Subtype.ext (Rat.cast_injective (add_left_cancel h.symm)))
  · intro x hx
    let a : I := ⟨x, hx⟩
    let c : Quotient s := Quotient.mk s a
    have hrel : s.r a c.out := Quotient.exact (Quotient.out_eq c).symm
    obtain ⟨q, hq⟩ := hrel
    change x - rep c = (q : ℝ) at hq
    have hrep := hsub (mem_range_self c)
    have hlow : (-1 : ℝ) ≤ (q : ℝ) := by linarith [hx.1, hrep.2]
    have hhigh : (q : ℝ) ≤ 1 := by linarith [hx.2, hrep.1]
    exact mem_iUnion.mpr ⟨⟨q, by exact_mod_cast hlow, by exact_mod_cast hhigh⟩,
      rep c, mem_range_self c, by linarith⟩
  · intro x hx
    obtain ⟨q, v, hv, rfl⟩ := mem_iUnion.mp hx
    have hqlo : (-1 : ℝ) ≤ (q.val : ℝ) := by exact_mod_cast q.property.1
    have hqhi : (q.val : ℝ) ≤ (1 : ℝ) := by exact_mod_cast q.property.2
    exact ⟨by linarith [(hsub hv).1], by linarith [(hsub hv).2]⟩

private def CountablyAdditive {X : Type*} (m : Set X → ℝ≥0∞) : Prop :=
  ∀ t : ℕ → Set X, Pairwise (fun i j => Disjoint (t i) (t j)) → m (⋃ i, t i) = ∑' i, m (t i)

private theorem monotone_of_countablyAdditive {X : Type*} {m : Set X → ℝ≥0∞}
    (hadd : CountablyAdditive m) : Monotone m := by
  intro A B hAB
  let t : ℕ → Set X := fun n => if n = 0 then A else if n = 1 then B \ A else ∅
  have hpair : Pairwise (fun i j => Disjoint (t i) (t j)) := by
    intro i j hij
    by_cases hi : i = 0 <;> by_cases hj : j = 0 <;>
      by_cases hi' : i = 1 <;> by_cases hj' : j = 1 <;>
      simp_all [t, disjoint_sdiff_left, disjoint_sdiff_right]
  have hU : (⋃ i, t i) = B := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      by_cases h0 : i = 0
      · exact hAB (by simpa [t, h0] using hi)
      by_cases h1 : i = 1
      · exact (show x ∈ B \ A by simpa [t, h0, h1] using hi).1
      · simp [t, h0, h1] at hi
    · intro hx
      by_cases hA : x ∈ A
      · exact mem_iUnion.mpr ⟨0, by simpa [t] using hA⟩
      · exact mem_iUnion.mpr ⟨1, by simpa [t] using (show x ∈ B \ A from ⟨hx, hA⟩)⟩
  rw [← hU, hadd t hpair]
  simpa [t] using (le_tsum (fun i => m (t i)) 0)

private theorem no_real_extension (m : Set ℝ → ℝ≥0∞)
    (hadd : CountablyAdditive m)
    (htranslate : ∀ q : RatShift, ∀ s : Set ℝ, m (translate q s) = m s)
    (hunit : m (Icc 0 1) = 1) (hbig : m (Icc (-1) 2) = 3) : False := by
  classical
  obtain ⟨V, hdis, hcov, hup⟩ := exists_vitali_partition
  let : Infinite ↥(Ioo (-1 : ℚ) 1) := Ioo.infinite (by norm_num)
  let : Countable RatShift := inferInstanceAs (Countable ↥(Icc (-1 : ℚ) 1))
  let : Infinite RatShift := Infinite.of_injective
    (fun q : ↥(Ioo (-1 : ℚ) 1) => (⟨q.val, q.property.1.le, q.property.2.le⟩ : RatShift))
    (fun _ _ h => Subtype.ext (congrArg (fun q : RatShift => q.val) h))
  let e : ℕ ≃ RatShift := Classical.choice nonempty_equiv_of_countable
  let t (n : ℕ) := translate (e n) V
  have ht : Pairwise (fun i j => Disjoint (t i) (t j)) :=
    fun i j hij => hdis (fun h => hij (e.injective h))
  have hU : (⋃ n, t n) = ⋃ q : RatShift, translate q V := by
    ext x
    simp only [mem_iUnion, t]
    exact ⟨fun ⟨n, hn⟩ => ⟨e n, hn⟩, fun ⟨q, hq⟩ => ⟨e.symm q, by simpa using hq⟩⟩
  have hmono := monotone_of_countablyAdditive hadd
  have hlo := hmono hcov
  have hhi := hmono hup
  rw [hunit, ← hU, hadd t ht] at hlo
  rw [hbig, ← hU, hadd t ht] at hhi
  have hsum : (∑' n, m (t n)) = ∑' _ : ℕ, m V := tsum_congr (fun n => htranslate (e n) V)
  rw [hsum] at hlo hhi
  by_cases hz : m V = 0
  · simp [hz] at hlo
  · rw [ENNReal.tsum_const_eq_top_of_ne_zero hz] at hhi
    exact (by norm_num : ¬(⊤ : ℝ≥0∞) ≤ 3) hhi

/--
The countably additive reading is false in ZFC. Sketch: let
`V₀ ⊆ [0,1]` meet each `ℚ`-coset represented in `[0,1]` exactly once
(Vitali selector) and put `V = V₀ × {0}`. Enumerating `ℚ ∩ [-1,1]` as
`(qₙ)`, the translates `Tₙ = V + (qₙ, 0)` are pairwise disjoint, each
congruent to `V`, so all have the same mass `c = μ V`. Their union
contains the unit segment `[0,1] × {0}` and lies in `[-1,2] × {0}`,
of linear measures `1` and `3` respectively, so countable additivity
and monotonicity give `1 ≤ μ U ≤ 3`, while countable additivity also
gives `μ U = ∑'ₙ c`, which is `0` if `c = 0` and `+∞` if `c > 0`, a
contradiction. Hence no such `μ` exists. This refutes the countably
additive formalization only. The typescript says bare "additive"; the
finite-additivity reading is not asserted here.
Source: E. Szpilrajn, Problem 169 of the Scottish Book; typescript
PDF p.78, printed p.75. C. Carathéodory, *Über das lineare Mass von
Punktmengen*, Nachr. Ges. Wiss. Göttingen (1914), 404-426.
-/
theorem no_countably_additive_congruence_measure :
  ¬ CountablyAdditiveCongruenceClaim := by
  rintro ⟨μ, hcong, hadd, hB⟩
  let E := EuclideanSpace ℝ (Fin 2)
  have hnorm : ‖EuclideanSpace.single (0 : Fin 2) (1 : ℝ)‖ = 1 := by
    change ‖PiLp.single 2 (β := fun _ : Fin 2 => ℝ) 0 1‖ = 1
    rw [PiLp.norm_single, norm_one]
  let e : ℝ →ₗᵢ[ℝ] E := LinearIsometry.toSpanSingleton ℝ E hnorm
  let m (S : Set ℝ) : ℝ≥0∞ := μ (e '' S)
  apply no_real_extension m
  · intro t ht
    change μ (e '' (⋃ i, t i)) = ∑' i, μ (e '' t i)
    rw [image_iUnion]
    exact hadd _ (fun i j hij => disjoint_image_of_injective e.injective (ht hij))
  · intro q S
    change μ (e '' translate q S) = μ (e '' S)
    symm
    refine hcong _ _ ⟨IsometryEquiv.addRight (e (q.val : ℝ)), ?_⟩
    rw [translate, image_image, image_image]
    congr 1
    funext x
    exact (e.map_add x (q.val : ℝ)).symm
  · change μ (e '' Icc (0 : ℝ) 1) = 1
    rw [hB _ (isCompact_Icc.image e.continuous).measurableSet,
      e.isometry.hausdorffMeasure_image (Or.inl zero_le_one), hausdorffMeasure_real]
    simp
  · change μ (e '' Icc (-1 : ℝ) 2) = 3
    rw [hB _ (isCompact_Icc.image e.continuous).measurableSet,
      e.isometry.hausdorffMeasure_image (Or.inl zero_le_one), hausdorffMeasure_real,
      Real.volume_Icc]
    norm_num

end MathlibExt.MeasureTheory.ScottishBook169Wanted
