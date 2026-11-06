/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
-/

/-
Adapted from `anthropics/fermats-last-theorem` at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`:
* `Theorems/Thm_MeasureTheory_exists_isLocallyConstant_integral_subgroup_mul_eq_one.lean`
* `P2M/Sol/S_MeasureTheory_exists_isLocallyConstant_integral_subgroup_mul_eq_one.lean`
Source: https://github.com/anthropics/fermats-last-theorem
The proof-extraction framework is removed, and the compact neighborhood is
constructed with Mathlib's pointwise-set API instead of a finite coset cover.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
The upstream NOTICE also credits Mathlib:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in their file headers.
Released under the Apache License, Version 2.0.
-/

module

public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Locally constant normalized subgroup cutoffs

A topological group with a compact open subgroup admits a nonnegative,
locally constant, compactly supported function whose integral over each
translate of a closed commutative subgroup is one on the saturation of a
prescribed compact set. This is a locally constant Bruhat function, not a
section of the quotient map.

The normalization applies to the left action `t * x`. Neither the ambient
group nor its compact open subgroup is required to be commutative.
-/

public section

open Set
open scoped Pointwise

namespace MeasureTheory

private theorem isLocallyConstant_of_right_invariant
    {G Y : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
    (K : Subgroup G) (hK : IsOpen (K : Set G)) (f : G → Y)
    (hf : ∀ y, ∀ k ∈ K, f (y * k) = f y) : IsLocallyConstant f := by
  refine (IsLocallyConstant.iff_exists_open f).2 fun y =>
    ⟨(fun z => y⁻¹ * z) ⁻¹' (K : Set G),
      hK.preimage (continuous_const_mul y⁻¹), ?_, ?_⟩
  · change y⁻¹ * y ∈ K
    rw [inv_mul_cancel]
    exact K.one_mem
  · intro z hz
    simpa only [mul_inv_cancel_left] using hf y (y⁻¹ * z) hz

/-- **Existence of a locally constant normalized subgroup cutoff.**
A compact set in a topological group with a compact open subgroup has a
nonnegative locally constant cutoff whose integral over every left
`T`-orbit meeting that set is one, for a closed commutative subgroup `T`.
The same compactly supported function works simultaneously on all of
`T * Ω`. The Haar measure need not have any prescribed normalization. -/
theorem exists_isLocallyConstant_integral_subgroup_mul_eq_one
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K : Subgroup G) (hK : IsCompact (K : Set G))
    (hK' : IsOpen (K : Set G))
    (T : Subgroup G) (hT : IsClosed (T : Set G))
    (hcomm : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s)
    [MeasurableSpace T] [BorelSpace T] (τ : Measure T) [τ.IsHaarMeasure]
    (Ω : Set G) (hΩ : IsCompact Ω) :
    ∃ w : G → ℝ, (∀ x, 0 ≤ w x) ∧ IsLocallyConstant w ∧
      HasCompactSupport w ∧ ∀ x : G,
      (∃ t ∈ T, ∃ d ∈ Ω, x = t * d) → ∫ t : T, w (t * x) ∂τ = 1 := by
  let C : Set G := Ω * (K : Set G)
  have hCc : IsCompact C := hΩ.mul hK
  have hCo : IsOpen C := hK'.mul_left
  have hCcl : IsClosed C := (K.isClosed_of_isOpen hK').mul_left_of_isCompact hΩ
  have hΩC : Ω ⊆ C := fun x hx => ⟨x, hx, 1, K.one_mem, mul_one x⟩
  have hCK : ∀ y ∈ C, ∀ k ∈ K, y * k ∈ C := by
    rintro _ ⟨z, hz, l, hl, rfl⟩ k hk
    exact ⟨z, hz, l * k, K.mul_mem hl hk, (mul_assoc z l k).symm⟩
  have hCiff : ∀ y, ∀ k ∈ K, (y * k ∈ C ↔ y ∈ C) := by
    intro y k hk
    refine ⟨fun h => ?_, fun h => hCK y h k hk⟩
    simpa only [mul_inv_cancel_right] using hCK (y * k) h k⁻¹ (K.inv_mem hk)
  let A : G → Set T := fun y => (fun t : T => (t : G) * y) ⁻¹' C
  have hAo : ∀ y, IsOpen (A y) :=
    fun y => hCo.preimage ((continuous_mul_const y).comp continuous_subtype_val)
  have hAc : ∀ y, IsCompact (A y) := by
    intro y
    exact hT.isClosedEmbedding_subtypeVal.isCompact_preimage
      ((Homeomorph.mulRight y).isCompact_preimage.2 hCc)
  have hAtop : ∀ y, τ (A y) ≠ ⊤ :=
    fun y => ((hAc y).measure_lt_top (μ := τ)).ne
  have hAne : ∀ y ∈ C, τ (A y) ≠ 0 := by
    intro y hy
    refine ((hAo y).measure_pos τ ⟨1, ?_⟩).ne'
    change ((1 : T) : G) * y ∈ C
    simpa only [OneMemClass.coe_one, one_mul] using hy
  have hAK : ∀ y, ∀ k ∈ K, A (y * k) = A y := by
    intro y k hk
    ext t
    change (t : G) * (y * k) ∈ C ↔ (t : G) * y ∈ C
    rw [← mul_assoc]
    exact hCiff _ k hk
  have hAT : ∀ (s : T) (y : G), τ (A ((s : G) * y)) = τ (A y) := by
    intro s y
    have h : A ((s : G) * y) = (fun t : T => s * t) ⁻¹' A y := by
      ext t
      change (t : G) * ((s : G) * y) ∈ C ↔ ((s * t : T) : G) * y ∈ C
      rw [Subgroup.coe_mul, ← mul_assoc, hcomm s s.2 t t.2]
    rw [h]
    exact measure_preimage_mul τ s (A y)
  let φ : G → ℝ := fun y => τ.real (A y)
  have hφpos : ∀ y ∈ C, 0 < φ y := by
    intro y hy
    exact ENNReal.toReal_pos (hAne y hy) (hAtop y)
  have hφK : ∀ y, ∀ k ∈ K, φ (y * k) = φ y := by
    intro y k hk
    change (τ (A (y * k))).toReal = (τ (A y)).toReal
    rw [hAK y k hk]
  have hφT : ∀ (s : T) (y : G), φ ((s : G) * y) = φ y := by
    intro s y
    change (τ (A ((s : G) * y))).toReal = (τ (A y)).toReal
    rw [hAT s y]
  have hwK : ∀ y, ∀ k ∈ K,
      C.indicator (fun z => (φ z)⁻¹) (y * k) =
        C.indicator (fun z => (φ z)⁻¹) y := by
    intro y k hk
    by_cases hy : y ∈ C
    · rw [indicator_of_mem hy, indicator_of_mem ((hCiff y k hk).2 hy),
        hφK y k hk]
    · rw [indicator_of_notMem hy,
        indicator_of_notMem (fun h => hy ((hCiff y k hk).1 h))]
  refine ⟨C.indicator fun z => (φ z)⁻¹, ?_,
    isLocallyConstant_of_right_invariant K hK' _ hwK,
    HasCompactSupport.intro' hCc hCcl fun y hy => indicator_of_notMem hy _, ?_⟩
  · intro x
    exact indicator_nonneg (fun z _ => inv_nonneg.2 ENNReal.toReal_nonneg) x
  · rintro x ⟨t₀, ht₀, d, hd, rfl⟩
    have hind : (fun t : T =>
        C.indicator (fun z => (φ z)⁻¹) ((t : G) * (t₀ * d))) =
        (A (t₀ * d)).indicator fun _ => (φ d)⁻¹ := by
      funext t
      by_cases h : (t : G) * (t₀ * d) ∈ C
      · have hA : t ∈ A (t₀ * d) := h
        have hts : (t : G) * (t₀ * d) =
            ((t * ⟨t₀, ht₀⟩ : T) : G) * d := (mul_assoc _ _ _).symm
        rw [indicator_of_mem h, indicator_of_mem hA, hts, hφT]
      · have hA : t ∉ A (t₀ * d) := h
        rw [indicator_of_notMem h, indicator_of_notMem hA]
    have h2 : τ.real (A (t₀ * d)) = φ d := hφT ⟨t₀, ht₀⟩ d
    rw [hind, integral_indicator_const _ (hAo (t₀ * d)).measurableSet,
      smul_eq_mul, h2]
    exact mul_inv_cancel₀ (hφpos d (hΩC hd)).ne'

end MeasureTheory
