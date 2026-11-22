/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import MathlibExt.Analysis.ODE.Nagumo

open Set

-- The criterion interoperates with Mathlib's positive tangent cone.
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → E) (hf : LocallyLipschitz f)
    (s : Set E) (hs : IsClosed s) :
    (∀ x ∈ s, f x ∈ posTangentConeAt s x) ↔
      ∀ T : ℝ, 0 < T → ∀ u : ℝ → E,
        (∀ t ∈ Icc 0 T, HasDerivWithinAt u (f (u t)) (Icc 0 T) t) →
        u 0 ∈ s → ∀ t ∈ Icc 0 T, u t ∈ s :=
  Nagumo.invariant_iff_mem_posTangentConeAt f hf s hs

-- An existing Mathlib convex-segment lemma supplies the tangency hypothesis.
example {a b : ℝ} {u : ℝ → ℝ}
    (hu : ∀ t ∈ Icc a b, HasDerivWithinAt u 1 (Icc a b) t)
    (hu₀ : 0 ≤ u a) : ∀ t ∈ Icc a b, 0 ≤ u t := by
  apply Nagumo.mapsTo_of_mem_posTangentConeAt
    (LipschitzWith.const (1 : ℝ)).locallyLipschitz isClosed_Ici _ hu hu₀
  intro x hx
  apply mem_posTangentConeAt_of_segment_subset
  exact (convex_Ici (0 : ℝ)).segment_subset hx (by
    change 0 ≤ x + 1
    linarith [show 0 ≤ x from hx])

-- The bridge itself does not require finite dimension or a closed set.
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} {x v : E} (hx : x ∈ s) (hv : Nagumo.IsContingent s x v) :
    v ∈ posTangentConeAt s x :=
  (Nagumo.isContingent_iff_mem_posTangentConeAt hx).mp hv

-- Isolated points retain their zero tangent direction.
example (x : Fin 0 → ℝ) : Nagumo.IsContingent {x} x 0 :=
  (Nagumo.isContingent_iff_mem_posTangentConeAt (mem_singleton x)).mpr
    (zero_mem_tangentConeAt (subset_closure (mem_singleton x)))

-- The exact general criterion is available for a closed, not necessarily convex set.
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → E) (hf : LocallyLipschitz f)
    (s : Set E) (hs : IsClosed s) :
    (∀ x ∈ s, Nagumo.IsContingent s x (f x)) ↔
      ∀ T : ℝ, 0 < T → ∀ u : ℝ → E,
        (∀ t ∈ Icc 0 T, HasDerivWithinAt u (f (u t)) (Icc 0 T) t) →
        u 0 ∈ s → ∀ t ∈ Icc 0 T, u t ∈ s :=
  Nagumo.invariant_iff_contingent f hf s hs

-- An unbounded, disconnected closed set: neither compactness nor convexity
-- is required of the invariant region.
private def twoRays : Set ℝ := Iic (-1) ∪ Ici 1

private theorem twoRays_tangent (x : ℝ) (hx : x ∈ twoRays) :
    Nagumo.IsContingent twoRays x x := by
  intro ε hε δ hδ
  let h := δ / 2
  have hh : 0 < h := half_pos hδ
  refine ⟨h, hh, half_lt_self hδ, x + h * x, ?_, ?_⟩
  · rcases hx with hx | hx
    · left
      change x + h * x ≤ -1
      change x ≤ -1 at hx
      nlinarith
    · right
      change 1 ≤ x + h * x
      change 1 ≤ x at hx
      nlinarith
  · have he : x + h * x - x - h • x = 0 := by simp
    rw [he, norm_zero]
    positivity

example {T : ℝ} {u : ℝ → ℝ}
    (hu : ∀ t ∈ Icc 0 T, HasDerivWithinAt u (u t) (Icc 0 T) t)
    (hu₀ : u 0 = -2) : ∀ t ∈ Icc 0 T, u t ≤ -1 ∨ 1 ≤ u t := by
  exact Nagumo.mapsTo_of_contingent LipschitzWith.id.locallyLipschitz
    (isClosed_Iic.union isClosed_Ici) twoRays_tangent hu (by
      change u 0 ∈ twoRays
      rw [hu₀]
      left
      norm_num)

-- Positive-time tangency detects an outward vector at the endpoint.
private theorem outward_not_contingent :
    ¬ Nagumo.IsContingent (Ici (0 : ℝ)) 0 (-1) := by
  intro ht
  obtain ⟨h, hh, _, y, hy, he⟩ := ht (1 / 2) (by norm_num) 1 (by norm_num)
  change 0 ≤ y at hy
  have he' : |y + h| ≤ (1 / 2 : ℝ) * h := by
    simpa [Real.norm_eq_abs] using he
  rw [abs_of_nonneg (by linarith [hy] : 0 ≤ y + h)] at he'
  linarith

example : (-1 : ℝ) ∉ posTangentConeAt (Ici 0) 0 := fun h =>
  outward_not_contingent
    ((Nagumo.isContingent_iff_mem_posTangentConeAt
      (show (0 : ℝ) ∈ Ici 0 from le_rfl)).mpr h)

-- The field x'=x² is only locally Lipschitz. The theorem asserts invariance
-- on the supplied finite interval, not global existence past blow-up.
example {b : ℝ} {u : ℝ → ℝ}
    (hu : ∀ t ∈ Icc (-2) b, HasDerivWithinAt u ((u t) ^ 2) (Icc (-2) b) t)
    (hu₀ : u (-2) = 1) : ∀ t ∈ Icc (-2) b, 0 ≤ u t := by
  have hf : ContDiff ℝ 1 (fun x : ℝ => x ^ 2) := by fun_prop
  apply Nagumo.mapsTo_of_contingent hf.locallyLipschitz isClosed_Ici _ hu
    (show u (-2) ∈ Ici 0 by rw [hu₀]; norm_num)
  intro x hx ε hε δ hδ
  refine ⟨δ / 2, half_pos hδ, half_lt_self hδ, x + (δ / 2) * x ^ 2, ?_, ?_⟩
  · change 0 ≤ x + (δ / 2) * x ^ 2
    exact add_nonneg hx (mul_nonneg (half_pos hδ).le (sq_nonneg x))
  · have he : x + δ / 2 * x ^ 2 - x - (δ / 2) • x ^ 2 = 0 := by simp
    rw [he, norm_zero]
    positivity

-- Empty sets and zero-dimensional state spaces retain their expected behavior.
example : ∀ x ∈ (∅ : Set (Fin 0 → ℝ)),
    Nagumo.IsContingent ∅ x (0 : Fin 0 → ℝ) := by simp

example (x : Fin 0 → ℝ) : Nagumo.IsContingent {x} x 0 := by
  intro ε hε δ hδ
  refine ⟨δ / 2, half_pos hδ, half_lt_self hδ, x, rfl, ?_⟩
  simp only [sub_self, smul_zero, norm_zero]
  positivity

-- Instantiate the full criterion in dimension zero, including an empty region.
example (T : ℝ) (hT : 0 < T) (u : ℝ → Fin 0 → ℝ)
    (hu : ∀ t ∈ Icc 0 T, HasDerivWithinAt u 0 (Icc 0 T) t)
    (hu₀ : u 0 ∈ (∅ : Set (Fin 0 → ℝ))) :
    ∀ t ∈ Icc 0 T, u t ∈ (∅ : Set (Fin 0 → ℝ)) :=
  (Nagumo.invariant_iff_contingent (fun _ => 0)
    (LipschitzWith.const _).locallyLipschitz ∅ isClosed_empty).mp
      (by simp) T hT u hu hu₀

#print axioms Nagumo.invariant_iff_contingent
#print axioms Nagumo.isContingent_iff_mem_posTangentConeAt
#print axioms Nagumo.invariant_iff_mem_posTangentConeAt
