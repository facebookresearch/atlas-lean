/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Analysis.Convex.Extreme
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Basic optimal points of a standard-form polyhedron

A linear objective that attains its minimum on a standard-form polyhedron
`{z ≥ 0 | L z = c}` attains it at a basic point (`IsBasicPt`): a feasible
point where no nonzero direction in the kernel of `L` vanishes off the
support of `z`. A basic point is determined by its support, so there are
finitely many (`finite_basic`), and the minimum is attained at one of them
(`exists_basic_optimal`).

These results are stated for a general real module `E` and were moved here
from `Domains.Biology.Dynamics.FluxBalanceValue`, which uses them for the
flux balance dual.
-/

@[expose] public section

namespace MathlibExt.Analysis.Convex.LPBasic

/-! ### Basic optimal points of a standard-form polyhedron -/

section Basic

variable {ι E : Type*} [Finite ι] [AddCommGroup E] [Module ℝ E]

/-- `z` is a basic point for the linear map `L`: the only kernel direction of `L` that vanishes
wherever `z` vanishes is `0`.

Moved from `Domains.Biology.Dynamics.FluxBalanceValue`. -/
def IsBasicPt (L : (ι → ℝ) →ₗ[ℝ] E) (z : ι → ℝ) : Prop :=
  ∀ d : ι → ℝ, L d = 0 → (∀ i, z i = 0 → d i = 0) → d = 0

/-- A kernel direction supported in the support of `z ≥ 0` keeps `z ± ε d ≥ 0` for some
`ε > 0`. -/
private theorem exists_pos_nonneg_add_sub {z d : ι → ℝ} (hz : 0 ≤ z)
    (hd : ∀ i, z i = 0 → d i = 0) (hd0 : d ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ 0 ≤ z + ε • d ∧ 0 ≤ z - ε • d := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨j, hj⟩ : ∃ j, d j ≠ 0 := by
    by_contra h
    push Not at h
    exact hd0 (funext h)
  have hS : (Finset.univ.filter fun i => d i ≠ 0).Nonempty := ⟨j, by simp [hj]⟩
  obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_min_image _ (fun i => z i / |d i|) hS
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi₀ hmin
  have hzpos : ∀ i, d i ≠ 0 → 0 < z i := fun i hi =>
    lt_of_le_of_ne (hz i) (fun h => hi (hd i h.symm))
  refine ⟨z i₀ / |d i₀|, div_pos (hzpos i₀ hi₀) (abs_pos.2 hi₀), fun i => ?_, fun i => ?_⟩ <;>
  · simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    by_cases hi : d i = 0
    · simp only [hi, mul_zero, add_zero, sub_zero]; exact hz i
    · have h1 := hmin i hi
      have hdi := abs_pos.2 hi
      have h2 : z i₀ / |d i₀| * |d i| ≤ z i := by
        rwa [le_div_iff₀ hdi] at h1
      have h3 := neg_abs_le (d i)
      have h4 := le_abs_self (d i)
      have h5 : 0 ≤ z i₀ / |d i₀| := (div_pos (hzpos i₀ hi₀) (abs_pos.2 hi₀)).le
      nlinarith

/-- A linear objective that attains its minimum on `{z ≥ 0 | L z = c}` attains it at a basic
point.

Moved from `Domains.Biology.Dynamics.FluxBalanceValue`. -/
theorem exists_basic_optimal (L : (ι → ℝ) →ₗ[ℝ] E) (φ : (ι → ℝ) →ₗ[ℝ] ℝ) (c : E)
    {z : ι → ℝ} (hz : 0 ≤ z) (hLz : L z = c)
    (hopt : ∀ z' : ι → ℝ, 0 ≤ z' → L z' = c → φ z ≤ φ z') :
    ∃ z' : ι → ℝ, 0 ≤ z' ∧ L z' = c ∧ φ z' = φ z ∧ IsBasicPt L z' := by
  classical
  have := Fintype.ofFinite ι
  suffices H : ∀ k, ∀ z : ι → ℝ, (Finset.univ.filter fun i => z i ≠ 0).card = k → 0 ≤ z →
      L z = c → (∀ z' : ι → ℝ, 0 ≤ z' → L z' = c → φ z ≤ φ z') →
      ∃ z' : ι → ℝ, 0 ≤ z' ∧ L z' = c ∧ φ z' = φ z ∧ IsBasicPt L z' from
    H _ z rfl hz hLz hopt
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro z hk hz hLz hopt
  by_cases hbasic : IsBasicPt L z
  · exact ⟨z, hz, hLz, rfl, hbasic⟩
  simp only [IsBasicPt, not_forall] at hbasic
  obtain ⟨d, hLd, hdz, hd0⟩ := hbasic
  -- optimality forces `φ d = 0`
  obtain ⟨ε, hε, hp, hm⟩ := exists_pos_nonneg_add_sub hz hdz hd0
  have hφd : φ d = 0 := by
    have h1 := hopt _ hp (by rw [map_add, map_smul, hLd, smul_zero, add_zero, hLz])
    have h2 := hopt _ hm (by rw [map_sub, map_smul, hLd, smul_zero, sub_zero, hLz])
    rw [map_add, map_smul, smul_eq_mul] at h1
    rw [map_sub, map_smul, smul_eq_mul] at h2
    have h3 : 0 ≤ ε * φ d := by linarith
    have h4 : ε * φ d ≤ 0 := by linarith
    have := le_antisymm h4 h3
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hε.ne'
    · exact h
  -- choose a sign with a negative coordinate
  obtain ⟨e, hLe, hez, hφe, hneg⟩ : ∃ e : ι → ℝ, L e = 0 ∧ (∀ i, z i = 0 → e i = 0) ∧
      φ e = 0 ∧ ∃ i, e i < 0 := by
    by_cases h : ∃ i, d i < 0
    · exact ⟨d, hLd, hdz, hφd, h⟩
    · push Not at h
      obtain ⟨j, hj⟩ : ∃ j, d j ≠ 0 := by
        by_contra h'
        push Not at h'
        exact hd0 (funext h')
      refine ⟨-d, by rw [map_neg, hLd, neg_zero], fun i hi => by simp [hdz i hi],
        by rw [map_neg, hφd, neg_zero], j, ?_⟩
      simp only [Pi.neg_apply, neg_neg_iff_pos]
      exact lt_of_le_of_ne (h j) (Ne.symm hj)
  have hS : (Finset.univ.filter fun i => e i < 0).Nonempty := by
    obtain ⟨i, hi⟩ := hneg
    exact ⟨i, by simp [hi]⟩
  obtain ⟨i₁, hi₁, hmin⟩ := Finset.exists_min_image _ (fun i => z i / -e i) hS
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi₁ hmin
  set t := z i₁ / -e i₁ with ht
  have ht0 : 0 ≤ t := div_nonneg (hz i₁) (by linarith)
  set z' := z + t • e with hz'
  have hz'0 : 0 ≤ z' := by
    intro i
    simp only [hz', Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    by_cases hi : e i < 0
    · have h1 := hmin i hi
      have h2 : t * -e i ≤ z i := by
        rwa [le_div_iff₀ (by linarith)] at h1
      linarith
    · push Not at hi
      have h1 : 0 ≤ z i := hz i
      have h2 : 0 ≤ t * e i := mul_nonneg ht0 hi
      linarith
  have hLz' : L z' = c := by rw [hz', map_add, map_smul, hLe, smul_zero, add_zero, hLz]
  have hφz' : φ z' = φ z := by rw [hz', map_add, map_smul, hφe, smul_zero, add_zero]
  have hz'i₁ : z' i₁ = 0 := by
    have hne : e i₁ ≠ 0 := hi₁.ne
    simp only [hz', ht, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  have hsub : (Finset.univ.filter fun i => z' i ≠ 0) ⊂
      (Finset.univ.filter fun i => z i ≠ 0) := by
    refine Finset.ssubset_iff_of_subset (fun i hi => ?_) |>.2 ⟨i₁, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      intro hzi
      apply hi
      simp [hz', hzi, hez i hzi]
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro hzi
      exact (ne_of_lt hi₁) (hez i₁ hzi)
    · simp [hz'i₁]
  obtain ⟨w, hw0, hLw, hφw, hw⟩ := ih _ (hk ▸ Finset.card_lt_card hsub) z' rfl hz'0 hLz'
    (fun z'' h0 hL => hφz' ▸ hopt z'' h0 hL)
  exact ⟨w, hw0, hLw, hφw.trans hφz', hw⟩

/-- There are finitely many basic points of `{z ≥ 0 | L z = c}`.

Moved from `Domains.Biology.Dynamics.FluxBalanceValue`. -/
theorem finite_basic (L : (ι → ℝ) →ₗ[ℝ] E) (c : E) :
    {z : ι → ℝ | 0 ≤ z ∧ L z = c ∧ IsBasicPt L z}.Finite := by
  classical
  have := Fintype.ofFinite ι
  refine Set.Finite.of_finite_image
    (f := fun z : ι → ℝ => Finset.univ.filter fun i => z i = 0) (Set.toFinite _) ?_
  rintro z₁ ⟨-, hL₁, hb₁⟩ z₂ ⟨-, hL₂, -⟩ heq
  have heq' : ∀ i, z₁ i = 0 ↔ z₂ i = 0 := fun i => by
    have := congrArg (fun s : Finset ι => i ∈ s) heq
    simpa using this
  have := hb₁ (z₁ - z₂) (by rw [map_sub, hL₁, hL₂, sub_self]) (fun i hi => by
    simp [hi, (heq' i).1 hi])
  exact sub_eq_zero.1 this

/-- A feasible point of `{z ≥ 0 | L z = c}` is basic iff it is an extreme point of the
feasible set. -/
theorem isBasicPt_iff_mem_extremePoints (L : (ι → ℝ) →ₗ[ℝ] E) (c : E)
    {z : ι → ℝ} (hz : 0 ≤ z) (hLz : L z = c) :
    IsBasicPt L z ↔ z ∈ Set.extremePoints ℝ {w | 0 ≤ w ∧ L w = c} := by
  constructor
  · intro hbasic
    rw [mem_extremePoints_iff_left]
    refine ⟨⟨hz, hLz⟩, fun x₁ hx₁ x₂ hx₂ hzseg => ?_⟩
    obtain ⟨hx₁0, hL₁⟩ := hx₁
    obtain ⟨hx₂0, _hL₂⟩ := hx₂
    obtain ⟨a, b, ha, hb, _hab, hzcomb⟩ := hzseg
    have hLd : L (x₁ - z) = 0 := by rw [map_sub, hL₁, hLz, sub_self]
    have hsupp : ∀ i, z i = 0 → (x₁ - z) i = 0 := by
      intro i hzi
      have hfun := congrFun hzcomb i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hfun
      have hsum0 : a * x₁ i + b * x₂ i = 0 := hfun.trans hzi
      have h1nn : 0 ≤ a * x₁ i := mul_nonneg ha.le (hx₁0 i)
      have h2nn : 0 ≤ b * x₂ i := mul_nonneg hb.le (hx₂0 i)
      have h10 : a * x₁ i = 0 := ((add_eq_zero_iff_of_nonneg h1nn h2nn).1 hsum0).1
      have hx₁i : x₁ i = 0 := by
        rcases mul_eq_zero.1 h10 with h | h
        · exact absurd h ha.ne'
        · exact h
      simp [Pi.sub_apply, hx₁i, hzi]
    have hdz : x₁ - z = 0 := hbasic _ hLd hsupp
    exact sub_eq_zero.1 hdz
  · intro hext
    rw [mem_extremePoints_iff_left] at hext
    intro d hLd hsupp
    by_contra hd0
    obtain ⟨ε, hε, hp, hm⟩ := exists_pos_nonneg_add_sub hz hsupp hd0
    have hLp : L (z + ε • d) = c := by
      rw [map_add, map_smul, hLd, smul_zero, add_zero, hLz]
    have hLm : L (z - ε • d) = c := by
      rw [map_sub, map_smul, hLd, smul_zero, sub_zero, hLz]
    have : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
    have hzmem : z ∈ openSegment ℝ (z - ε • d) (z + ε • d) :=
      mem_openSegment_sub_add (𝕜 := ℝ) z (ε • d)
    have hx₁mem : (z - ε • d) ∈ {w | 0 ≤ w ∧ L w = c} := ⟨hm, hLm⟩
    have hx₂mem : (z + ε • d) ∈ {w | 0 ≤ w ∧ L w = c} := ⟨hp, hLp⟩
    have hEq : z - ε • d = z := hext.2 _ hx₁mem _ hx₂mem hzmem
    have hεd : ε • d = 0 := by
      have h3 := congrArg (fun w => z - w) hEq
      rwa [sub_sub_cancel, sub_self] at h3
    have hd : d = 0 := by
      funext i
      have hi := congrFun hεd i
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
      rcases mul_eq_zero.1 hi with h | h
      · exact absurd h hε.ne'
      · exact h
    exact hd0 hd

end Basic

end MathlibExt.Analysis.Convex.LPBasic
