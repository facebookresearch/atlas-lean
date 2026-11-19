/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Consumer.Shephard


@[expose] public section

open Filter Topology

/-! Leontief and linear utilities on `ℝ²₊`: Shephard's lemma in the `IsGLB` form gives the
gradient `(1, 1)` of `e(p) = p₀ + p₁`, and the uniqueness theorem shows that the kinked
expenditure function `min p₀ p₁` of linear utility is not differentiable at `(1, 1)`. -/

namespace MathlibExtTest.Economics.Consumer.Shephard

open _root_.Economics.Consumer

/-- Leontief utility (non-vacuous instance): with `u x = min (x 0) (x 1)`,
`p₀ = ![1, 2]`, `e p = p 0 + p 1` and Hicksian demand `h = ![1, 1]`, Shephard's
lemma gives `e' v = v 0 + v 1`. -/
theorem leontief_shephard :
    ∀ v : Fin 2 → ℝ,
      (ContinuousLinearMap.proj (R := ℝ) (ι := Fin 2) (φ := fun _ => ℝ) (0 : Fin 2)
        + ContinuousLinearMap.proj (R := ℝ) (ι := Fin 2) (φ := fun _ => ℝ) (1 : Fin 2)) v
        = v 0 + v 1 := by
  have hpos : ∀ᶠ p : Fin 2 → ℝ in 𝓝 ![1, 2], 0 < p 0 ∧ 0 < p 1 := by
    have e0 : IsOpen {p : Fin 2 → ℝ | 0 < p 0} := isOpen_Ioi.preimage (continuous_apply 0)
    have e1 : IsOpen {p : Fin 2 → ℝ | 0 < p 1} := isOpen_Ioi.preimage (continuous_apply 1)
    have hopen : IsOpen {p : Fin 2 → ℝ | 0 < p 0 ∧ 0 < p 1} := by
      rw [show {p : Fin 2 → ℝ | 0 < p 0 ∧ 0 < p 1}
          = {p : Fin 2 → ℝ | 0 < p 0} ∩ {p : Fin 2 → ℝ | 0 < p 1} from rfl]
      exact e0.inter e1
    have hmem : ![1, 2] ∈ {p : Fin 2 → ℝ | 0 < p 0 ∧ 0 < p 1} := by
      norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact hopen.mem_nhds hmem
  have he : ∀ᶠ p : Fin 2 → ℝ in 𝓝 ![1, 2],
      IsGLB ((fun x => p ⬝ᵥ x) '' {x | x ∈ {x : Fin 2 → ℝ | 0 ≤ x} ∧ (1:ℝ) ≤ min (x 0) (x 1)})
        (p 0 + p 1) := by
    filter_upwards [hpos] with p hp
    obtain ⟨hp0, hp1⟩ := hp
    have hmem : p 0 + p 1 ∈ (fun x => p ⬝ᵥ x) '' {x | x ∈ {x : Fin 2 → ℝ | 0 ≤ x} ∧ (1:ℝ) ≤ min (x 0) (x 1)} := by
      refine ⟨![1, 1], ⟨?_, ?_⟩, ?_⟩
      · show (0:Fin 2 → ℝ) ≤ ![1, 1]
        rw [Pi.le_def]
        intro i
        simp only [Pi.zero_apply]
        fin_cases i <;> norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]
      · show (1:ℝ) ≤ min (![1, 1] 0) (![1, 1] 1)
        norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]
      · show p ⬝ᵥ ![1, 1] = p 0 + p 1
        simp [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hlb : p 0 + p 1 ∈ lowerBounds ((fun x => p ⬝ᵥ x) '' {x | x ∈ {x : Fin 2 → ℝ | 0 ≤ x} ∧ (1:ℝ) ≤ min (x 0) (x 1)}) := by
      rw [mem_lowerBounds]
      intro y hy
      obtain ⟨x, ⟨_hxX, hxu⟩, rfl⟩ := hy
      show p 0 + p 1 ≤ p ⬝ᵥ x
      rw [le_min_iff] at hxu
      obtain ⟨hxu0, hxu1⟩ := hxu
      have hdot : p ⬝ᵥ x = p 0 * x 0 + p 1 * x 1 := by
        simp [dotProduct, Fin.sum_univ_two]
      rw [hdot]
      have g0 : p 0 * 1 ≤ p 0 * x 0 := mul_le_mul_of_nonneg_left hxu0 (le_of_lt hp0)
      have g1 : p 1 * 1 ≤ p 1 * x 1 := mul_le_mul_of_nonneg_left hxu1 (le_of_lt hp1)
      have hsum := add_le_add g0 g1
      simpa using hsum
    exact IsLeast.isGLB ⟨hmem, hlb⟩
  have hX : ![1, 1] ∈ ({x : Fin 2 → ℝ | 0 ≤ x} : Set (Fin 2 → ℝ)) := by
    show (0:Fin 2 → ℝ) ≤ ![1, 1]
    rw [Pi.le_def]
    intro i
    simp only [Pi.zero_apply]
    fin_cases i <;> norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hu : (1:ℝ) ≤ min (![1, 1] 0) (![1, 1] 1) := by
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hcost : (![1, 2] : Fin 2 → ℝ) ⬝ᵥ ![1, 1] = ![1, 2] 0 + ![1, 2] 1 := by
    norm_num [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hdiff : HasFDerivAt (fun p : Fin 2 → ℝ => p 0 + p 1)
      (ContinuousLinearMap.proj (R := ℝ) (ι := Fin 2) (φ := fun _ => ℝ) (0 : Fin 2)
        + ContinuousLinearMap.proj (R := ℝ) (ι := Fin 2) (φ := fun _ => ℝ) (1 : Fin 2)) ![1, 2] := by
    have h0 := (ContinuousLinearMap.proj (R := ℝ) (ι := Fin 2) (φ := fun _ => ℝ) (0 : Fin 2)).hasFDerivAt (x := ![1, 2])
    have h1 := (ContinuousLinearMap.proj (R := ℝ) (ι := Fin 2) (φ := fun _ => ℝ) (1 : Fin 2)).hasFDerivAt (x := ![1, 2])
    exact h0.add h1
  have hmain := hasFDerivAt_expenditure_eq_hicksianDemand
    (u := fun x : Fin 2 → ℝ => min (x 0) (x 1)) (X := {x : Fin 2 → ℝ | 0 ≤ x})
    (ubar := (1:ℝ)) (e := fun p : Fin 2 → ℝ => p 0 + p 1) (p₀ := ![1, 2]) (h := ![1, 1])
    he hX hu hcost hdiff
  intro v
  have hv := hmain v
  rw [hv]
  simp [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Kinked expenditure (the differentiability hypothesis matters): with linear
utility `u x = x 0 + x 1`, `p₀ = ![1, 1]` and `e p = min (p 0) (p 1)`, both
`![1, 0]` and `![0, 1]` are Hicksian demands at `p₀`, so `e` cannot be
differentiable at `p₀`. -/
theorem kinked_not_differentiable :
    ¬ DifferentiableAt ℝ (fun p : Fin 2 → ℝ => min (p 0) (p 1)) ![1, 1] := by
  have hpos : ∀ᶠ p : Fin 2 → ℝ in 𝓝 ![1, 1], 0 < p 0 ∧ 0 < p 1 := by
    have e0 : IsOpen {p : Fin 2 → ℝ | 0 < p 0} := isOpen_Ioi.preimage (continuous_apply 0)
    have e1 : IsOpen {p : Fin 2 → ℝ | 0 < p 1} := isOpen_Ioi.preimage (continuous_apply 1)
    have hopen : IsOpen {p : Fin 2 → ℝ | 0 < p 0 ∧ 0 < p 1} := by
      rw [show {p : Fin 2 → ℝ | 0 < p 0 ∧ 0 < p 1}
          = {p : Fin 2 → ℝ | 0 < p 0} ∩ {p : Fin 2 → ℝ | 0 < p 1} from rfl]
      exact e0.inter e1
    have hmem : ![1, 1] ∈ {p : Fin 2 → ℝ | 0 < p 0 ∧ 0 < p 1} := by
      norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact hopen.mem_nhds hmem
  have he : ∀ᶠ p : Fin 2 → ℝ in 𝓝 ![1, 1],
      IsGLB ((fun x => p ⬝ᵥ x) '' {x | x ∈ {x : Fin 2 → ℝ | 0 ≤ x} ∧ (1:ℝ) ≤ x 0 + x 1})
        (min (p 0) (p 1)) := by
    filter_upwards [hpos] with p hp
    obtain ⟨hp0, hp1⟩ := hp
    rcases le_total (p 0) (p 1) with hle | hle
    · rw [min_eq_left hle]
      have hmem : p 0 ∈ (fun x => p ⬝ᵥ x) '' {x | x ∈ {x : Fin 2 → ℝ | 0 ≤ x} ∧ (1:ℝ) ≤ x 0 + x 1} := by
        refine ⟨![1, 0], ⟨?_, ?_⟩, ?_⟩
        · show (0:Fin 2 → ℝ) ≤ ![1, 0]
          rw [Pi.le_def]
          intro i
          simp only [Pi.zero_apply]
          fin_cases i <;> norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]
        · show (1:ℝ) ≤ ![1, 0] 0 + ![1, 0] 1
          norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]
        · show p ⬝ᵥ ![1, 0] = p 0
          simp [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      have hlb : p 0 ∈ lowerBounds ((fun x => p ⬝ᵥ x) '' {x | x ∈ {x : Fin 2 → ℝ | 0 ≤ x} ∧ (1:ℝ) ≤ x 0 + x 1}) := by
        rw [mem_lowerBounds]
        intro y hy
        obtain ⟨x, ⟨hxX, hxu⟩, rfl⟩ := hy
        show p 0 ≤ p ⬝ᵥ x
        simp only [Pi.le_def, Pi.zero_apply] at hxX
        have hx1 : (0:ℝ) ≤ x 1 := hxX 1
        have hdot : p ⬝ᵥ x = p 0 * x 0 + p 1 * x 1 := by
          simp [dotProduct, Fin.sum_univ_two]
        rw [hdot]
        have h1 : p 0 * x 1 ≤ p 1 * x 1 := mul_le_mul_of_nonneg_right hle hx1
        have h2 : p 0 * 1 ≤ p 0 * (x 0 + x 1) := mul_le_mul_of_nonneg_left hxu (le_of_lt hp0)
        calc p 0 = p 0 * 1 := (mul_one _).symm
          _ ≤ p 0 * (x 0 + x 1) := h2
          _ = p 0 * x 0 + p 0 * x 1 := mul_add _ _ _
          _ ≤ p 0 * x 0 + p 1 * x 1 := add_le_add_right h1 _
      exact IsLeast.isGLB ⟨hmem, hlb⟩
    · rw [min_eq_right hle]
      have hmem : p 1 ∈ (fun x => p ⬝ᵥ x) '' {x | x ∈ {x : Fin 2 → ℝ | 0 ≤ x} ∧ (1:ℝ) ≤ x 0 + x 1} := by
        refine ⟨![0, 1], ⟨?_, ?_⟩, ?_⟩
        · show (0:Fin 2 → ℝ) ≤ ![0, 1]
          rw [Pi.le_def]
          intro i
          simp only [Pi.zero_apply]
          fin_cases i <;> norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]
        · show (1:ℝ) ≤ ![0, 1] 0 + ![0, 1] 1
          norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]
        · show p ⬝ᵥ ![0, 1] = p 1
          simp [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      have hlb : p 1 ∈ lowerBounds ((fun x => p ⬝ᵥ x) '' {x | x ∈ {x : Fin 2 → ℝ | 0 ≤ x} ∧ (1:ℝ) ≤ x 0 + x 1}) := by
        rw [mem_lowerBounds]
        intro y hy
        obtain ⟨x, ⟨hxX, hxu⟩, rfl⟩ := hy
        show p 1 ≤ p ⬝ᵥ x
        simp only [Pi.le_def, Pi.zero_apply] at hxX
        have hx0 : (0:ℝ) ≤ x 0 := hxX 0
        have hdot : p ⬝ᵥ x = p 0 * x 0 + p 1 * x 1 := by
          simp [dotProduct, Fin.sum_univ_two]
        rw [hdot]
        have h1 : p 1 * x 0 ≤ p 0 * x 0 := mul_le_mul_of_nonneg_right hle hx0
        have h2 : p 1 * 1 ≤ p 1 * (x 0 + x 1) := mul_le_mul_of_nonneg_left hxu (le_of_lt hp1)
        calc p 1 = p 1 * 1 := (mul_one _).symm
          _ ≤ p 1 * (x 0 + x 1) := h2
          _ = p 1 * x 0 + p 1 * x 1 := mul_add _ _ _
          _ ≤ p 0 * x 0 + p 1 * x 1 := add_le_add_left h1 _
      exact IsLeast.isGLB ⟨hmem, hlb⟩
  have h1X : ![1, 0] ∈ ({x : Fin 2 → ℝ | 0 ≤ x} : Set (Fin 2 → ℝ)) := by
    show (0:Fin 2 → ℝ) ≤ ![1, 0]
    rw [Pi.le_def]
    intro i
    simp only [Pi.zero_apply]
    fin_cases i <;> norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]
  have h1u : (1:ℝ) ≤ ![1, 0] 0 + ![1, 0] 1 := by
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]
  have h1cost : (![1, 1] : Fin 2 → ℝ) ⬝ᵥ ![1, 0] = min (![1, 1] 0) (![1, 1] 1) := by
    norm_num [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  have h2X : ![0, 1] ∈ ({x : Fin 2 → ℝ | 0 ≤ x} : Set (Fin 2 → ℝ)) := by
    show (0:Fin 2 → ℝ) ≤ ![0, 1]
    rw [Pi.le_def]
    intro i
    simp only [Pi.zero_apply]
    fin_cases i <;> norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]
  have h2u : (1:ℝ) ≤ ![0, 1] 0 + ![0, 1] 1 := by
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]
  have h2cost : (![1, 1] : Fin 2 → ℝ) ⬝ᵥ ![0, 1] = min (![1, 1] 0) (![1, 1] 1) := by
    norm_num [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  intro hdiff
  have he' := hdiff.hasFDerivAt
  have hcontra := hicksianDemand_unique_of_hasFDerivAt
    (u := fun x : Fin 2 → ℝ => x 0 + x 1) (X := {x : Fin 2 → ℝ | 0 ≤ x})
    (ubar := (1:ℝ)) (e := fun p : Fin 2 → ℝ => min (p 0) (p 1)) (p₀ := ![1, 1])
    (h := ![1, 0]) (k := ![0, 1]) he h1X h1u h1cost h2X h2u h2cost he'
  have h01 := congrFun hcontra (0 : Fin 2)
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one] at h01

end MathlibExtTest.Economics.Consumer.Shephard

/-! Leontief utility again, now through the `expenditure` definition: the expenditure function
equals `p₀ + p₁` near `(1, 2)` and its derivative is `v ↦ v₀ + v₁`. -/

namespace MathlibExtTest.Economics.Consumer.Shephard.Expenditure

open _root_.Economics.Consumer

/-- Nonnegative orthant in ℝ². -/
def X : Set (Fin 2 → ℝ) := {x | 0 ≤ x}

/-- Leontief utility. -/
def u : (Fin 2 → ℝ) → ℝ := fun x => min (x 0) (x 1)

theorem mem_X_iff {x : Fin 2 → ℝ} : x ∈ X ↔ ∀ i, 0 ≤ x i := by
  simp [X, Pi.le_def]

theorem dotProduct_expand (p y : Fin 2 → ℝ) :
    p ⬝ᵥ y = p 0 * y 0 + p 1 * y 1 := by
  simp [dotProduct, Fin.sum_univ_two]

theorem h_hicksian :
    IsHicksianDemand u X (![1, 2] : Fin 2 → ℝ) 1 (![1, 1] : Fin 2 → ℝ) := by
  have hXt : (![1, 1] : Fin 2 → ℝ) ∈ X := by
    rw [mem_X_iff]
    intro i
    fin_cases i <;> simp
  have hut : (1 : ℝ) ≤ u ![1, 1] := by
    show (1 : ℝ) ≤ min ((![1, 1] : Fin 2 → ℝ) 0) ((![1, 1] : Fin 2 → ℝ) 1)
    simp
  have hmint : ∀ y ∈ X, (1 : ℝ) ≤ u y →
      (![1, 2] : Fin 2 → ℝ) ⬝ᵥ ![1, 1] ≤ (![1, 2] : Fin 2 → ℝ) ⬝ᵥ y := by
    intro y _ hyu
    simp only [u] at hyu
    obtain ⟨hy0, hy1⟩ := le_min_iff.mp hyu
    have lhs : (![1, 2] : Fin 2 → ℝ) ⬝ᵥ ![1, 1] = 3 := by
      rw [dotProduct_expand]
      norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]
    have rhs : (![1, 2] : Fin 2 → ℝ) ⬝ᵥ y = y 0 + 2 * y 1 := by
      rw [dotProduct_expand]
      simp [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [lhs, rhs]
    linarith
  exact ⟨hXt, hut, hmint⟩

theorem hbdd_near : ∀ᶠ p in 𝓝 (![1, 2] : Fin 2 → ℝ),
    BddBelow ((fun x => p ⬝ᵥ x) '' {x | x ∈ X ∧ 1 ≤ u x}) := by
  have g0 : (1 / 2 : ℝ) < (![1, 2] : Fin 2 → ℝ) 0 := by
    have e0 : ((![1, 2] : Fin 2 → ℝ) 0) = 1 := by simp
    linarith
  have g1 : (1 / 2 : ℝ) < (![1, 2] : Fin 2 → ℝ) 1 := by
    have e1 : ((![1, 2] : Fin 2 → ℝ) 1) = 2 := by simp
    linarith
  have h0 : ∀ᶠ p : Fin 2 → ℝ in 𝓝 (![1, 2] : Fin 2 → ℝ), (1 / 2 : ℝ) < p 0 :=
    ((continuous_apply (0 : Fin 2)).tendsto _).eventually
      (eventually_gt_nhds g0)
  have h1 : ∀ᶠ p : Fin 2 → ℝ in 𝓝 (![1, 2] : Fin 2 → ℝ), (1 / 2 : ℝ) < p 1 :=
    ((continuous_apply (1 : Fin 2)).tendsto _).eventually
      (eventually_gt_nhds g1)
  filter_upwards [h0, h1] with p hp0 hp1
  refine ⟨0, ?_⟩
  intro c hc
  obtain ⟨y, ⟨yX, _⟩, rfl⟩ := hc
  rw [mem_X_iff] at yX
  simp only [dotProduct_expand]
  have t0 : (0 : ℝ) ≤ p 0 * y 0 := mul_nonneg (by linarith) (yX 0)
  have t1 : (0 : ℝ) ≤ p 1 * y 1 := mul_nonneg (by linarith) (yX 1)
  linarith

theorem expenditure_eq_near : ∀ᶠ p in 𝓝 (![1, 2] : Fin 2 → ℝ),
    expenditure u X p 1 = p 0 + p 1 := by
  have g0 : (1 / 2 : ℝ) < (![1, 2] : Fin 2 → ℝ) 0 := by
    have e0 : ((![1, 2] : Fin 2 → ℝ) 0) = 1 := by simp
    linarith
  have g1 : (1 / 2 : ℝ) < (![1, 2] : Fin 2 → ℝ) 1 := by
    have e1 : ((![1, 2] : Fin 2 → ℝ) 1) = 2 := by simp
    linarith
  have h0 : ∀ᶠ p : Fin 2 → ℝ in 𝓝 (![1, 2] : Fin 2 → ℝ), (1 / 2 : ℝ) < p 0 :=
    ((continuous_apply (0 : Fin 2)).tendsto _).eventually
      (eventually_gt_nhds g0)
  have h1 : ∀ᶠ p : Fin 2 → ℝ in 𝓝 (![1, 2] : Fin 2 → ℝ), (1 / 2 : ℝ) < p 1 :=
    ((continuous_apply (1 : Fin 2)).tendsto _).eventually
      (eventually_gt_nhds g1)
  filter_upwards [h0, h1] with p hp0 hp1
  have hp0' : (0 : ℝ) < p 0 := by linarith
  have hp1' : (0 : ℝ) < p 1 := by linarith
  have hleast : IsLeast ((fun x => p ⬝ᵥ x) '' {x | x ∈ X ∧ 1 ≤ u x})
      (p 0 + p 1) := by
    constructor
    · refine ⟨(![1, 1] : Fin 2 → ℝ), ⟨?_, ?_⟩, ?_⟩
      · rw [mem_X_iff]
        intro i
        fin_cases i <;> simp
      · show (1 : ℝ) ≤ min ((![1, 1] : Fin 2 → ℝ) 0) ((![1, 1] : Fin 2 → ℝ) 1)
        simp
      · simp only [dotProduct_expand]
        simp
    · intro c hc
      obtain ⟨y, ⟨_, yu⟩, rfl⟩ := hc
      simp only [u] at yu
      obtain ⟨hy0, hy1⟩ := le_min_iff.mp yu
      simp only [dotProduct_expand]
      have g0' : p 0 * 1 ≤ p 0 * y 0 :=
        mul_le_mul_of_nonneg_left hy0 (le_of_lt hp0')
      have g1' : p 1 * 1 ≤ p 1 * y 1 :=
        mul_le_mul_of_nonneg_left hy1 (le_of_lt hp1')
      have hsum := add_le_add g0' g1'
      simpa using hsum
  exact hleast.csInf_eq

theorem hdiff_test : HasFDerivAt (fun p : Fin 2 → ℝ => expenditure u X p 1)
    (((ContinuousLinearMap.proj (0 : Fin 2)) : (Fin 2 → ℝ) →L[ℝ] ℝ) +
      ((ContinuousLinearMap.proj (1 : Fin 2)) : (Fin 2 → ℝ) →L[ℝ] ℝ))
    (![1, 2] : Fin 2 → ℝ) := by
  have hbase : HasFDerivAt (fun p : Fin 2 → ℝ => p 0 + p 1)
      (((ContinuousLinearMap.proj (0 : Fin 2)) : (Fin 2 → ℝ) →L[ℝ] ℝ) +
        ((ContinuousLinearMap.proj (1 : Fin 2)) : (Fin 2 → ℝ) →L[ℝ] ℝ))
      (![1, 2] : Fin 2 → ℝ) := by
    have ha := ((ContinuousLinearMap.proj (0 : Fin 2)) :
      (Fin 2 → ℝ) →L[ℝ] ℝ).hasFDerivAt (x := (![1, 2] : Fin 2 → ℝ))
    have hb := ((ContinuousLinearMap.proj (1 : Fin 2)) :
      (Fin 2 → ℝ) →L[ℝ] ℝ).hasFDerivAt (x := (![1, 2] : Fin 2 → ℝ))
    have hadd := ha.add hb
    exact hadd
  exact hbase.congr_of_eventuallyEq expenditure_eq_near

theorem shephard_conclusion : ∀ v : Fin 2 → ℝ,
    ((((ContinuousLinearMap.proj (0 : Fin 2)) : (Fin 2 → ℝ) →L[ℝ] ℝ) +
      ((ContinuousLinearMap.proj (1 : Fin 2)) : (Fin 2 → ℝ) →L[ℝ] ℝ))) v
      = v 0 + v 1 := by
  intro v
  have h := hasFDerivAt_expenditure_eq_of_isHicksianDemand
    hbdd_near h_hicksian hdiff_test v
  rw [h]
  rw [dotProduct_expand]
  simp

-- The canonical homogeneity API applies directly through the consumer spelling.
example (p : Fin 2 → ℝ) (ubar : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    expenditure u X (t • p) ubar =
      t * MathlibExt.Economics.ExpenditureFunction.expenditure u X p ubar := by
  exact MathlibExt.Economics.ExpenditureFunction.expenditure_smul u X p ubar ht

end MathlibExtTest.Economics.Consumer.Shephard.Expenditure

/-! The same Leontief example through the canonical gradient form: the derivative of the
expenditure function at `(1, 2)` is `Real.dotL (1, 1)`. -/

namespace MathlibExtTest.Economics.Consumer.Shephard.DotL

open _root_.Economics.Consumer

example : fderiv ℝ (fun p : Fin 2 → ℝ => expenditure (fun x => min (x 0) (x 1)) {x | 0 ≤ x} p 1) ![1, 2] = Real.dotL ![1, 1] := by
  have hpos0 : ∀ᶠ p : Fin 2 → ℝ in 𝓝 ![1, 2], 0 < p 0 := by
    have h1 : ∀ᶠ y : ℝ in 𝓝 ((![1, 2] : Fin 2 → ℝ) 0), 0 < y := by
      have heq : ((![1, 2] : Fin 2 → ℝ) 0) = 1 := by simp
      rw [heq]
      exact eventually_gt_nhds (by norm_num)
    have hcont : Filter.Tendsto (fun p : Fin 2 → ℝ => p 0) (𝓝 ![1, 2]) (𝓝 ((![1, 2] : Fin 2 → ℝ) 0)) :=
      (continuous_apply 0).continuousAt
    exact hcont.eventually h1
  have hpos1 : ∀ᶠ p : Fin 2 → ℝ in 𝓝 ![1, 2], 0 < p 1 := by
    have h1 : ∀ᶠ y : ℝ in 𝓝 ((![1, 2] : Fin 2 → ℝ) 1), 0 < y := by
      have heq : ((![1, 2] : Fin 2 → ℝ) 1) = 2 := by simp
      rw [heq]
      exact eventually_gt_nhds (by norm_num)
    have hcont : Filter.Tendsto (fun p : Fin 2 → ℝ => p 1) (𝓝 ![1, 2]) (𝓝 ((![1, 2] : Fin 2 → ℝ) 1)) :=
      (continuous_apply 1).continuousAt
    exact hcont.eventually h1
  have hbdd : ∀ᶠ p : Fin 2 → ℝ in 𝓝 ![1, 2],
      BddBelow ((fun x => p ⬝ᵥ x) '' {x | x ∈ ({x | 0 ≤ x} : Set (Fin 2 → ℝ)) ∧ 1 ≤ min (x 0) (x 1)}) := by
    filter_upwards [hpos0, hpos1] with p hp0 hp1
    use 0
    intro c hc
    obtain ⟨x, ⟨hxX, hux⟩, rfl⟩ := hc
    simp only [dotProduct, Fin.sum_univ_two]
    have hx0 : 0 ≤ x 0 := hxX 0
    have hx1 : 0 ≤ x 1 := hxX 1
    have h0 : 0 ≤ p 0 * x 0 := mul_nonneg hp0.le hx0
    have h1 : 0 ≤ p 1 * x 1 := mul_nonneg hp1.le hx1
    linarith
  have hh : IsHicksianDemand (fun x : Fin 2 → ℝ => min (x 0) (x 1)) {x | 0 ≤ x} ![1, 2] 1 ![1, 1] := by
    constructor
    · show (0 : Fin 2 → ℝ) ≤ ![1, 1]
      intro i
      fin_cases i <;> simp
    · constructor
      · show (1 : ℝ) ≤ min ((![1, 1] : Fin 2 → ℝ) 0) ((![1, 1] : Fin 2 → ℝ) 1)
        simp
      · intro y hyX huy
        have ⟨hy0, hy1⟩ := le_min_iff.mp huy
        have hlhs : ((![1, 2] : Fin 2 → ℝ) ⬝ᵥ ![1, 1]) = 3 := by
          simp [dotProduct, Fin.sum_univ_two]
          norm_num
        have hrhs : ((![1, 2] : Fin 2 → ℝ) ⬝ᵥ y) = y 0 + 2 * y 1 := by
          simp [dotProduct, Fin.sum_univ_two]
        rw [hlhs, hrhs]
        linarith
  have hexp : ∀ᶠ p : Fin 2 → ℝ in 𝓝 ![1, 2],
      expenditure (fun x => min (x 0) (x 1)) {x | 0 ≤ x} p 1 = p 0 + p 1 := by
    filter_upwards [hpos0, hpos1, hbdd] with p hp0 hp1 hbb
    unfold expenditure
    have hleast : IsLeast ((fun x => p ⬝ᵥ x) '' {x | x ∈ ({x | 0 ≤ x} : Set (Fin 2 → ℝ)) ∧ 1 ≤ min (x 0) (x 1)}) (p 0 + p 1) := by
      constructor
      · have hmemX : (![1, 1] : Fin 2 → ℝ) ∈ ({x | 0 ≤ x} : Set (Fin 2 → ℝ)) := by
          show (0 : Fin 2 → ℝ) ≤ ![1, 1]
          intro i
          fin_cases i <;> simp
        have hmemU : (1 : ℝ) ≤ min ((![1, 1] : Fin 2 → ℝ) 0) ((![1, 1] : Fin 2 → ℝ) 1) := by simp
        have hcost : p ⬝ᵥ ![1, 1] = p 0 + p 1 := by
          simp [dotProduct, Fin.sum_univ_two]
        exact ⟨![1, 1], ⟨hmemX, hmemU⟩, hcost⟩
      · intro b hb
        obtain ⟨y, ⟨hyX, huy⟩, rfl⟩ := hb
        have ⟨hy0, hy1⟩ := le_min_iff.mp huy
        simp only [dotProduct, Fin.sum_univ_two]
        have h0 : p 0 * 1 ≤ p 0 * y 0 := mul_le_mul_of_nonneg_left hy0 hp0.le
        have h1 : p 1 * 1 ≤ p 1 * y 1 := mul_le_mul_of_nonneg_left hy1 hp1.le
        simp only [mul_one] at h0 h1
        linarith
    exact hleast.csInf_eq
  have hlin : HasFDerivAt (fun p : Fin 2 → ℝ => p ⬝ᵥ (![1, 1] : Fin 2 → ℝ)) (Real.dotL ![1, 1]) ![1, 2] :=
    Real.hasFDerivAt_dotProduct _ _
  have heq : (fun p : Fin 2 → ℝ => expenditure (fun x => min (x 0) (x 1)) {x | 0 ≤ x} p 1) =ᶠ[𝓝 ![1, 2]]
      (fun p : Fin 2 → ℝ => p ⬝ᵥ (![1, 1] : Fin 2 → ℝ)) := by
    filter_upwards [hexp] with p hp
    rw [hp]
    simp [dotProduct, Fin.sum_univ_two]
  have hdiff_explicit : HasFDerivAt (fun p : Fin 2 → ℝ => expenditure (fun x => min (x 0) (x 1)) {x | 0 ≤ x} p 1) (Real.dotL ![1, 1]) ![1, 2] :=
    hlin.congr_of_eventuallyEq heq
  have hdiff : HasFDerivAt (fun p : Fin 2 → ℝ => expenditure (fun x => min (x 0) (x 1)) {x | 0 ≤ x} p 1)
      (fderiv ℝ (fun p : Fin 2 → ℝ => expenditure (fun x => min (x 0) (x 1)) {x | 0 ≤ x} p 1) ![1, 2]) ![1, 2] :=
    hdiff_explicit.differentiableAt.hasFDerivAt
  exact hasFDerivAt_expenditure_eq_dotL_of_isHicksianDemand hbdd hh hdiff

end MathlibExtTest.Economics.Consumer.Shephard.DotL
