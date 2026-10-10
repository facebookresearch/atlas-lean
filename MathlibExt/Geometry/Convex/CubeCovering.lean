/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.Convex.Covering
public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
import Mathlib.Topology.Constructions
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The actual cube covering obstruction and an eight-translate cover

Source: Arman, Bondarenko and Prymak, arXiv:2404.00547v1, introduction.
The `2^n` vertices cannot share a translate of the cube's interior. In dimension
three, the eight centers with coordinates `±1/2` give an actual matching cover.
-/

@[expose] public section

namespace ConvexCovering

/-- The coordinate cube in the actual Euclidean space. -/
def coordinateCube (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ i, x i ∈ Set.Icc (-1 : ℝ) 1}

/-- An affine cube is the image under a genuinely invertible affine map. -/
def IsAffineCube {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ e : EuclideanSpace ℝ (Fin n) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
    K = e '' coordinateCube n

/-- Interior membership is strict in every coordinate. -/
theorem coordinateCube_interior_iff {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    x ∈ interior (coordinateCube n) ↔ ∀ i, -1 < x i ∧ x i < 1 := by
  have hcube : coordinateCube n = (PiLp.homeomorph 2 (fun _ : Fin n ↦ ℝ)) ⁻¹'
      Set.univ.pi (fun _ : Fin n ↦ Set.Icc (-1 : ℝ) 1) := by
    ext z
    simp only [coordinateCube, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_pi,
      Set.mem_univ, forall_true_left]
    rfl
  rw [hcube, ← IsOpenMap.preimage_interior_eq_interior_preimage
    (PiLp.homeomorph 2 (fun _ : Fin n ↦ ℝ)).isOpenMap
    (PiLp.homeomorph 2 (fun _ : Fin n ↦ ℝ)).continuous]
  rw [interior_pi_set Set.finite_univ]
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left,
    interior_Icc, Set.mem_Ioo]
  rfl

/-- The cube is compact, convex and has nonempty ambient interior. -/
theorem coordinateCube_isConvexBody (n : ℕ) : IsConvexBody (coordinateCube n) := by
  refine ⟨?_, ?_, 0, ?_⟩
  · have hcube : coordinateCube n = (PiLp.homeomorph 2 (fun _ : Fin n ↦ ℝ)) ⁻¹'
        {x : Fin n → ℝ | ∀ i, x i ∈ Set.Icc (-1 : ℝ) 1} := rfl
    rw [hcube]
    apply (PiLp.homeomorph 2 (fun _ : Fin n ↦ ℝ)).isCompact_preimage.mpr
    exact isCompact_pi_infinite (fun _ : Fin n ↦
      (isCompact_Icc : IsCompact (Set.Icc (-1 : ℝ) 1)))
  · intro x hx y hy a b ha hb hab i
    change a * x i + b * y i ∈ Set.Icc (-1 : ℝ) 1
    exact convex_Icc (-1 : ℝ) 1 (hx i) (hy i) ha hb hab
  · rw [coordinateCube_interior_iff]
    intro i
    change -1 < (0 : ℝ) ∧ (0 : ℝ) < 1
    norm_num

/-- Reflection about the origin preserves the cube. -/
theorem coordinateCube_isCentrallySymmetric (n : ℕ) :
    IsCentrallySymmetric (coordinateCube n) := by
  refine ⟨0, ?_⟩
  intro x
  simp only [zero_add, zero_sub]
  change (∀ i, -1 ≤ x i ∧ x i ≤ 1) ↔ (∀ i, -1 ≤ -x i ∧ -x i ≤ 1)
  constructor <;> intro hx i <;> have hi := hx i <;> constructor <;> linarith

private def cubeVertex {n : ℕ} (b : Fin n → Bool) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i ↦ if b i then (1 : ℝ) else -1)

private theorem cubeVertex_unique {n : ℕ} (v : EuclideanSpace ℝ (Fin n))
    (a b : Fin n → Bool)
    (ha : cubeVertex a ∈ (fun z ↦ v + z) '' interior (coordinateCube n))
    (hb : cubeVertex b ∈ (fun z ↦ v + z) '' interior (coordinateCube n)) : a = b := by
  rcases ha with ⟨x, hx, hxa⟩
  rcases hb with ⟨y, hy, hyb⟩
  funext i
  have hxi := (coordinateCube_interior_iff x).mp hx i
  have hyi := (coordinateCube_interior_iff y).mp hy i
  have hax := congrArg (fun z : EuclideanSpace ℝ (Fin n) ↦ z i) hxa
  have hby := congrArg (fun z : EuclideanSpace ℝ (Fin n) ↦ z i) hyb
  change v i + x i = (if a i then 1 else -1) at hax
  change v i + y i = (if b i then 1 else -1) at hby
  cases hai : a i <;> cases hbi : b i
  · rfl
  · simp only [hai, hbi, Bool.false_eq_true, ↓reduceIte] at hax hby
    linarith
  · simp only [hai, hbi, Bool.false_eq_true, ↓reduceIte] at hax hby
    linarith
  · rfl

/-- An actual interior-translate cover of the cube requires at least `2^n` members. -/
theorem coordinateCube_coveringCount_ge_two_pow {n q : ℕ}
    (h : CoveredByInteriorTranslates (coordinateCube n) q) : 2 ^ n ≤ q := by
  classical
  rcases h with ⟨v, hv⟩
  have hc : ∀ b : Fin n → Bool, ∃ j,
      cubeVertex b ∈ (fun z ↦ v j + z) '' interior (coordinateCube n) := by
    intro b
    apply Set.mem_iUnion.mp
    apply hv
    intro i
    change -1 ≤ (if b i then (1 : ℝ) else -1) ∧
      (if b i then (1 : ℝ) else -1) ≤ 1
    cases b i <;> norm_num
  choose f hf using hc
  have hinj : Function.Injective f := by
    intro a b hab
    apply cubeVertex_unique (v (f a)) a b (hf a)
    simpa only [hab] using hf b
  simpa using Fintype.card_le_of_injective f hinj

/-- The actual cube obstructs every universal interior-translate bound. -/
theorem uniformInteriorTranslateBound_ge_two_pow {n q : ℕ}
    (h : UniformInteriorTranslateBound n q) : 2 ^ n ≤ q :=
  coordinateCube_coveringCount_ge_two_pow
    (h (coordinateCube n) (coordinateCube_isConvexBody n))

/-- The classical three-dimensional lower-bound row. -/
theorem cubeLowerBound (q : ℕ) (h : UniformInteriorTranslateBound 3 q) : 8 ≤ q := by
  simpa using uniformInteriorTranslateBound_ge_two_pow h

/-- The centrally symmetric class has the same actual cube obstruction. -/
theorem symmetricInteriorTranslateBound_ge_two_pow {n q : ℕ}
    (h : UniformSymmetricInteriorTranslateBound n q) : 2 ^ n ≤ q :=
  coordinateCube_coveringCount_ge_two_pow (h (coordinateCube n)
    (coordinateCube_isConvexBody n) (coordinateCube_isCentrallySymmetric n))

/-- Eight actual translates of the interior cover the three-dimensional cube. -/
theorem coordinateCube_three_coveredByInteriorTranslates :
    CoveredByInteriorTranslates (coordinateCube 3) 8 := by
  classical
  let e : (Fin 3 → Bool) ≃ Fin 8 := Fintype.equivOfCardEq (by norm_num)
  let center (b : Fin 3 → Bool) : EuclideanSpace ℝ (Fin 3) :=
    WithLp.toLp 2 (fun i ↦ if b i then (1 / 2 : ℝ) else -(1 / 2))
  refine ⟨fun j ↦ center (e.symm j), ?_⟩
  intro x hx
  let b : Fin 3 → Bool := fun i ↦ decide (0 ≤ x i)
  apply Set.mem_iUnion.mpr
  refine ⟨e b, x - center b, ?_, ?_⟩
  · rw [coordinateCube_interior_iff]
    intro i
    have hi := hx i
    change -1 < x i - (if b i then (1 / 2 : ℝ) else -(1 / 2)) ∧
      x i - (if b i then (1 / 2 : ℝ) else -(1 / 2)) < 1
    dsimp [b]
    by_cases h : 0 ≤ x i
    · simp only [h, decide_true, ↓reduceIte]
      constructor <;> linarith [hi.1, hi.2]
    · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
      constructor <;> linarith [hi.1, hi.2]
  · simp only [Equiv.symm_apply_apply]
    exact add_sub_cancel _ _

/-- The matching cover and vertex obstruction give an actual least count of eight. -/
theorem coordinateCube_three_least_coveringCount :
    IsLeast {q : ℕ | CoveredByInteriorTranslates (coordinateCube 3) q} 8 := by
  refine ⟨coordinateCube_three_coveredByInteriorTranslates, ?_⟩
  intro q hq
  simpa using coordinateCube_coveringCount_ge_two_pow hq

/-- The generic covering-number data evaluates to eight for the actual cube. -/
theorem coordinateCube_three_translateCoveringNumber :
    translateCoveringNumber (coordinateCube 3) (interior (coordinateCube 3)) =
      (8 : WithTop ℕ) :=
  translateCoveringNumber_eq_of_isLeast _ _ coordinateCube_three_least_coveringCount

end ConvexCovering
