/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Four-point comparison for curvature bounded below

This file defines model-plane trigonometry, model angles, and the four-point
comparison condition for Alexandrov geometry following AKP.

## Main definitions
* `modelDiameter`: diameter of the model plane.
* `modelCos` and `modelSin`: the functions `cs` and `sn`.
* `ModelTriangleDefined`: a model triangle with given sides exists.
* `modelAngle`: model angle opposite a side via the cosine law.
* `ModelAngleDefined` and `comparisonAngle`: model angle of a triple.
* `FourPointComparison`: the `Alex` comparison for a quadruple.
* `IsAlex`: the `Alex` curvature bound for a metric space.

## Main results
* Values of `modelDiameter`, `modelCos`, and `modelSin`.
* `modelAngle` lies in `[0, π]` and is symmetric in adjacent sides.
* `comparisonAngle` and `ModelAngleDefined` are symmetric.
* `IsAlex` pulls back along isometries and to subsets; subsingletons qualify.

## References
* S. Alexander, V. Kapovitch, and A. Petrunin, Alexandrov geometry:
  foundations, AMS GSM 236, 2024; arXiv:1903.08539v6, `model.tex`,
  `euclid.tex`, and `defs-CBB.tex`.
-/

@[expose] public section

universe u v

namespace AlexandrovGeometry

/-- Diameter of the model plane of curvature `κ`: infinite for `κ ≤ 0` and
`π / √κ` for `κ > 0`. -/
noncomputable def modelDiameter (κ : ℝ) : ENNReal :=
  if κ ≤ 0 then ⊤ else ENNReal.ofReal (Real.pi / √κ)

/-- AKP's `cs`: cosine in the model plane of curvature `κ`. -/
noncomputable def modelCos (κ t : ℝ) : ℝ :=
  if 0 < κ then Real.cos (√κ * t)
  else if κ = 0 then 1
  else Real.cosh (√(-κ) * t)

/-- AKP's `sn`: sine in the model plane of curvature `κ`. -/
noncomputable def modelSin (κ t : ℝ) : ℝ :=
  if 0 < κ then Real.sin (√κ * t) / √κ
  else if κ = 0 then t
  else Real.sinh (√(-κ) * t) / √(-κ)

/-- A model triangle with sides `a, b, c` exists: triangle inequalities plus,
for `κ > 0`, perimeter below `2 * π / √κ`. -/
def ModelTriangleDefined (κ a b c : ℝ) : Prop :=
  a ≤ b + c ∧ b ≤ a + c ∧ c ≤ a + b ∧ (0 < κ → a + b + c < 2 * Real.pi / √κ)

/-- Model angle opposite `a` with adjacent sides `b, c` via the cosine law;
meaningful where the triangle is defined and `b, c > 0`. -/
noncomputable def modelAngle (κ a b c : ℝ) : ℝ :=
  if κ = 0 then Real.arccos ((b ^ 2 + c ^ 2 - a ^ 2) / (2 * b * c))
  else Real.arccos ((modelCos κ a - modelCos κ b * modelCos κ c) /
    (κ * modelSin κ b * modelSin κ c))

/-- The triple model angle at `p` is defined: the model triangle exists and
both sides at `p` are positive. -/
def ModelAngleDefined {X : Type u} [MetricSpace X] (κ : ℝ)
    (p x y : X) : Prop :=
  ModelTriangleDefined κ (dist x y) (dist p x) (dist p y) ∧
    0 < dist p x ∧ 0 < dist p y

/-- AKP's model angle of the triple `p, x, y` at `p`. -/
noncomputable def comparisonAngle {X : Type u} [MetricSpace X] (κ : ℝ)
    (p x y : X) : ℝ :=
  modelAngle κ (dist x y) (dist p x) (dist p y)

/-- AKP's `Alex κ` comparison: the three comparison angles at `p` sum to at
most `2 * π` when all are defined. -/
def FourPointComparison {X : Type u} [MetricSpace X] (κ : ℝ)
    (p x₁ x₂ x₃ : X) : Prop :=
  (ModelAngleDefined κ p x₁ x₂ ∧ ModelAngleDefined κ p x₂ x₃ ∧
    ModelAngleDefined κ p x₃ x₁) →
    comparisonAngle κ p x₁ x₂ + comparisonAngle κ p x₂ x₃ +
      comparisonAngle κ p x₃ x₁ ≤ 2 * Real.pi

/-- A space is `Alex κ` if every quadruple meets the comparison. For complete
length spaces this is curvature `≥ κ`; no diameter bound for `κ > 0`, so the
real line is `Alex 1`. -/
def IsAlex (κ : ℝ) (X : Type u) [MetricSpace X] : Prop :=
  ∀ p x₁ x₂ x₃ : X, FourPointComparison κ p x₁ x₂ x₃

/-- Model diameter for `κ ≤ 0` is infinite. -/
theorem modelDiameter_of_nonpos {κ : ℝ} (h : κ ≤ 0) : modelDiameter κ = ⊤ := by
  unfold modelDiameter
  simp only [h, ite_true]

/-- Model diameter for `κ > 0` is `π / √κ`. -/
theorem modelDiameter_of_pos {κ : ℝ} (h : 0 < κ) :
    modelDiameter κ = ENNReal.ofReal (Real.pi / √κ) := by
  unfold modelDiameter
  have hn : ¬ κ ≤ 0 := not_le.mpr h
  simp only [hn, ite_false]

/-- `cs` for `κ > 0` is `cos` of the scaled argument. -/
theorem modelCos_of_pos {κ : ℝ} (hκ : 0 < κ) (t : ℝ) : modelCos κ t = Real.cos (√κ * t) := by
  unfold modelCos
  simp only [hκ, ite_true]

/-- `cs` for `κ < 0` is `cosh` of the scaled argument. -/
theorem modelCos_of_neg {κ : ℝ} (hκ : κ < 0) (t : ℝ) : modelCos κ t = Real.cosh (√(-κ) * t) := by
  unfold modelCos
  have hpos : ¬ 0 < κ := fun h => absurd (lt_trans hκ h) (lt_irrefl κ)
  have h0 : κ ≠ 0 := ne_of_lt hκ
  simp only [hpos, h0, ite_false]

/-- `sn` for `κ > 0` is `sin` of the scaled argument. -/
theorem modelSin_of_pos {κ : ℝ} (hκ : 0 < κ) (t : ℝ) : modelSin κ t = Real.sin (√κ * t) / √κ := by
  unfold modelSin
  simp only [hκ, ite_true]

/-- `sn` for `κ < 0` is `sinh` of the scaled argument. -/
theorem modelSin_of_neg {κ : ℝ} (hκ : κ < 0) (t : ℝ) :
    modelSin κ t = Real.sinh (√(-κ) * t) / √(-κ) := by
  unfold modelSin
  have hpos : ¬ 0 < κ := fun h => absurd (lt_trans hκ h) (lt_irrefl κ)
  have h0 : κ ≠ 0 := ne_of_lt hκ
  simp only [hpos, h0, ite_false]

/-- `cs` for `κ = 0` is constantly `1`. -/
theorem modelCos_zero_left (t : ℝ) : modelCos 0 t = 1 := by
  unfold modelCos
  simp only [lt_irrefl, ite_false, ite_true]

/-- `sn` for `κ = 0` is the identity. -/
theorem modelSin_zero_left (t : ℝ) : modelSin 0 t = t := by
  unfold modelSin
  simp only [lt_irrefl, ite_false, ite_true]

/-- `cs` at `0` equals `1` for every `κ`. -/
theorem modelCos_zero_right (κ : ℝ) : modelCos κ 0 = 1 := by
  by_cases hpos : 0 < κ
  · rw [modelCos_of_pos hpos 0, mul_zero, Real.cos_zero]
  · by_cases h0 : κ = 0
    · rw [h0]
      exact modelCos_zero_left 0
    · have hneg : κ < 0 := lt_of_le_of_ne (not_lt.mp hpos) h0
      rw [modelCos_of_neg hneg 0, mul_zero, Real.cosh_zero]

/-- `sn` at `0` equals `0` for every `κ`. -/
theorem modelSin_zero_right (κ : ℝ) : modelSin κ 0 = 0 := by
  by_cases hpos : 0 < κ
  · rw [modelSin_of_pos hpos 0, mul_zero, Real.sin_zero, zero_div]
  · by_cases h0 : κ = 0
    · rw [h0]
      exact modelSin_zero_left 0
    · have hneg : κ < 0 := lt_of_le_of_ne (not_lt.mp hpos) h0
      rw [modelSin_of_neg hneg 0, mul_zero, Real.sinh_zero, zero_div]

/-- Model angle for `κ = 0`: the Euclidean cosine law. -/
theorem modelAngle_zero_left (a b c : ℝ) :
    modelAngle 0 a b c = Real.arccos ((b ^ 2 + c ^ 2 - a ^ 2) / (2 * b * c)) := by
  unfold modelAngle
  rw [ite_eq_left rfl]

/-- Model angle for `κ ≠ 0`: the `κ` cosine law. -/
theorem modelAngle_of_ne_zero {κ : ℝ} (hκ : κ ≠ 0) (a b c : ℝ) :
    modelAngle κ a b c = Real.arccos ((modelCos κ a - modelCos κ b * modelCos κ c) /
      (κ * modelSin κ b * modelSin κ c)) := by
  unfold modelAngle
  simp only [hκ, ite_false]

/-- Model angles are nonnegative. -/
theorem modelAngle_nonneg (κ a b c : ℝ) : 0 ≤ modelAngle κ a b c := by
  by_cases h0 : κ = 0
  · rw [h0, modelAngle_zero_left]
    exact Real.arccos_nonneg _
  · rw [modelAngle_of_ne_zero h0]
    exact Real.arccos_nonneg _

/-- Model angles are at most `π`. -/
theorem modelAngle_le_pi (κ a b c : ℝ) : modelAngle κ a b c ≤ Real.pi := by
  by_cases h0 : κ = 0
  · rw [h0, modelAngle_zero_left]
    exact Real.arccos_le_pi _
  · rw [modelAngle_of_ne_zero h0]
    exact Real.arccos_le_pi _

/-- The model angle is symmetric in the two adjacent sides. -/
theorem modelAngle_comm (κ a b c : ℝ) :
    modelAngle κ a b c = modelAngle κ a c b := by
  by_cases h0 : κ = 0
  · rw [h0, modelAngle_zero_left, modelAngle_zero_left]
    have hnum : b ^ 2 + c ^ 2 - a ^ 2 = c ^ 2 + b ^ 2 - a ^ 2 := by
      rw [add_comm (b ^ 2) (c ^ 2)]
    have hden : 2 * b * c = 2 * c * b := by
      rw [mul_assoc, mul_comm b c, ← mul_assoc]
    rw [hnum, hden]
  · rw [modelAngle_of_ne_zero h0, modelAngle_of_ne_zero h0]
    have hnum : modelCos κ a - modelCos κ b * modelCos κ c =
        modelCos κ a - modelCos κ c * modelCos κ b := by
      rw [mul_comm (modelCos κ b) (modelCos κ c)]
    have hden : κ * modelSin κ b * modelSin κ c =
        κ * modelSin κ c * modelSin κ b := by
      rw [mul_assoc, mul_comm (modelSin κ b) (modelSin κ c), ← mul_assoc]
    rw [hnum, hden]

/-- The comparison angle is symmetric in the two points. -/
theorem comparisonAngle_comm {X : Type u} [MetricSpace X] (κ : ℝ) (p x y : X) :
    comparisonAngle κ p x y = comparisonAngle κ p y x := by
  unfold comparisonAngle
  have hdist : dist x y = dist y x := dist_comm x y
  have hcomm : modelAngle κ (dist y x) (dist p x) (dist p y) =
      modelAngle κ (dist y x) (dist p y) (dist p x) :=
    modelAngle_comm κ (dist y x) (dist p x) (dist p y)
  rw [hdist, hcomm]

/-- Definedness of the comparison angle is symmetric in the points. -/
theorem modelAngleDefined_comm {X : Type u} [MetricSpace X] (κ : ℝ)
    (p x y : X) :
    ModelAngleDefined κ p x y ↔ ModelAngleDefined κ p y x := by
  unfold ModelAngleDefined ModelTriangleDefined
  have hdist : dist x y = dist y x := dist_comm x y
  rw [hdist]
  constructor
  · intro h
    have h1 : dist y x ≤ dist p x + dist p y := h.1.1
    have h2 : dist p x ≤ dist y x + dist p y := h.1.2.1
    have h3 : dist p y ≤ dist y x + dist p x := h.1.2.2.1
    have h4 : 0 < κ → dist y x + dist p x + dist p y < 2 * Real.pi / √κ :=
      h.1.2.2.2
    have h5 : 0 < dist p x := h.2.1
    have h6 : 0 < dist p y := h.2.2
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · simpa only [add_comm (dist p x) (dist p y)] using h1
    · exact h3
    · exact h2
    · intro hpos
      have hper : dist y x + dist p x + dist p y =
          dist y x + dist p y + dist p x := by
        rw [add_assoc, add_comm (dist p x) (dist p y), ← add_assoc]
      have hlt : dist y x + dist p x + dist p y < 2 * Real.pi / √κ := h4 hpos
      rw [hper] at hlt
      exact hlt
    · exact h6
    · exact h5
  · intro h
    have h1 : dist y x ≤ dist p y + dist p x := h.1.1
    have h2 : dist p y ≤ dist y x + dist p x := h.1.2.1
    have h3 : dist p x ≤ dist y x + dist p y := h.1.2.2.1
    have h4 : 0 < κ → dist y x + dist p y + dist p x < 2 * Real.pi / √κ :=
      h.1.2.2.2
    have h5 : 0 < dist p y := h.2.1
    have h6 : 0 < dist p x := h.2.2
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · simpa only [add_comm (dist p y) (dist p x)] using h1
    · exact h3
    · exact h2
    · intro hpos
      have hper : dist y x + dist p y + dist p x =
          dist y x + dist p x + dist p y := by
        rw [add_assoc, add_comm (dist p y) (dist p x), ← add_assoc]
      have hlt : dist y x + dist p y + dist p x < 2 * Real.pi / √κ := h4 hpos
      rw [hper] at hlt
      exact hlt
    · exact h6
    · exact h5

namespace IsAlex

/-- `IsAlex` pulls back along an isometry. -/
theorem of_isometry {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    {κ : ℝ} (hY : IsAlex κ Y) {f : X → Y} (hf : Isometry f) :
    IsAlex κ X := by
  intro p x₁ x₂ x₃ hdef
  have h1 : ModelAngleDefined κ (f p) (f x₁) (f x₂) := by
    have horig : ModelAngleDefined κ p x₁ x₂ := hdef.1
    unfold ModelAngleDefined ModelTriangleDefined at horig ⊢
    simpa only [hf.dist_eq] using horig
  have h2 : ModelAngleDefined κ (f p) (f x₂) (f x₃) := by
    have horig : ModelAngleDefined κ p x₂ x₃ := hdef.2.1
    unfold ModelAngleDefined ModelTriangleDefined at horig ⊢
    simpa only [hf.dist_eq] using horig
  have h3 : ModelAngleDefined κ (f p) (f x₃) (f x₁) := by
    have horig : ModelAngleDefined κ p x₃ x₁ := hdef.2.2
    unfold ModelAngleDefined ModelTriangleDefined at horig ⊢
    simpa only [hf.dist_eq] using horig
  have hdef' : ModelAngleDefined κ (f p) (f x₁) (f x₂) ∧
      ModelAngleDefined κ (f p) (f x₂) (f x₃) ∧
      ModelAngleDefined κ (f p) (f x₃) (f x₁) := ⟨h1, h2, h3⟩
  have hle : comparisonAngle κ (f p) (f x₁) (f x₂) +
      comparisonAngle κ (f p) (f x₂) (f x₃) +
      comparisonAngle κ (f p) (f x₃) (f x₁) ≤ 2 * Real.pi :=
    hY (f p) (f x₁) (f x₂) (f x₃) hdef'
  have c1 : comparisonAngle κ (f p) (f x₁) (f x₂) =
      comparisonAngle κ p x₁ x₂ := by
    unfold comparisonAngle
    simp only [hf.dist_eq]
  have c2 : comparisonAngle κ (f p) (f x₂) (f x₃) =
      comparisonAngle κ p x₂ x₃ := by
    unfold comparisonAngle
    simp only [hf.dist_eq]
  have c3 : comparisonAngle κ (f p) (f x₃) (f x₁) =
      comparisonAngle κ p x₃ x₁ := by
    unfold comparisonAngle
    simp only [hf.dist_eq]
  rw [c1, c2, c3] at hle
  exact hle

/-- Every subset of an `Alex κ` space is `Alex κ`. -/
theorem subtype {X : Type u} [MetricSpace X] {κ : ℝ} (hX : IsAlex κ X)
    (s : Set X) : IsAlex κ s :=
  of_isometry hX isometry_subtype_coe

/-- Every subsingleton metric space is `Alex κ`. -/
theorem of_subsingleton (X : Type u) [MetricSpace X] [Subsingleton X]
    {κ : ℝ} : IsAlex κ X := by
  intro p x₁ _ _ hdef
  have heq : p = x₁ := Subsingleton.elim p x₁
  have hdist : dist p x₁ = 0 := by rw [heq, dist_self]
  have hpos : 0 < dist p x₁ := by
    unfold ModelAngleDefined at hdef
    exact hdef.1.2.1
  rw [hdist] at hpos
  exact absurd hpos (lt_irrefl 0)

end IsAlex

end AlexandrovGeometry
