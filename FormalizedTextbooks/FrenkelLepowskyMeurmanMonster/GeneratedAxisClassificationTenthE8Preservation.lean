/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7SliceSpan

/-! Actual E7 projector-preserving Leech isometries preserve the enclosing physical E8 section. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

private def realProjection (x : Fin 24 → ℝ) : Fin 24 → ℝ :=
  generatedTenthE7ProjectionInteger.map (Int.castRingHom ℝ) *ᵥ x

private theorem projection_cast (u : Fin 24 → ℤ) :
    realProjection (fun i => (u i : ℝ)) =
      (fun i => ((generatedTenthE7ProjectionInteger *ᵥ u) i : ℝ)) := by
  ext i
  simp only [realProjection, Matrix.mulVec, dotProduct, Matrix.map_apply]
  push_cast
  rfl

private theorem integral_action_cast (e : leechIsomSubgroup) (u : leechIntegral) :
    e.val (fun i => (u.val i : ℝ)) =
      (fun i => ((leechIntegralAction e u).val i : ℝ)) := by
  have hsqrt : Real.sqrt 8 ≠ 0 := by positivity
  have he (v : Fin 24 → ℤ) : (Real.sqrt 8 : ℝ) • leechCoordinateEmbedding v =
      (fun i => (v i : ℝ)) := by
    ext i
    change Real.sqrt 8 * ((v i : ℝ) / Real.sqrt 8) = (v i : ℝ)
    exact mul_div_cancel₀ _ hsqrt
  rw [← he u.val, map_smul, ← leechIntegralAction_embedding, he]

private theorem cast_pairing (u : Fin 24 → ℤ) :
    stdPairingFun (fun i => (u i : ℝ)) (fun i => (u i : ℝ)) =
      (leechSquareSum u : ℝ) := by
  simp only [stdPairingFun, leechSquareSum, Int.cast_sum, pow_two, Int.cast_mul]

private theorem slice_action (e : leechIsomSubgroup)
    (he : ∀ x, e.val (realProjection x) = realProjection (e.val x))
    (u : Fin 24 → ℤ) (hu : u ∈ generatedTenthE7SliceIntegral) :
    (leechIntegralAction e ⟨u, hu.1⟩).val ∈ generatedTenthE7SliceIntegral := by
  let v := leechIntegralAction e ⟨u, hu.1⟩
  refine ⟨v.property, (leechIntegralAction_squareSum e ⟨u, hu.1⟩).trans hu.2.1, ?_⟩
  have hh := e.property.1 (realProjection (fun i => (u i : ℝ)))
    (realProjection (fun i => (u i : ℝ)))
  rw [he, integral_action_cast e ⟨u, hu.1⟩, projection_cast, projection_cast, cast_pairing,
    cast_pairing] at hh
  have hn : leechSquareSum (generatedTenthE7ProjectionInteger *ᵥ v.val) =
      leechSquareSum (generatedTenthE7ProjectionInteger *ᵥ u) := by exact_mod_cast hh
  exact hn.trans hu.2.2

private theorem section_action (e : leechIsomSubgroup)
    (he : ∀ x, e.val (realProjection x) = realProjection (e.val x))
    (x : Fin 24 → ℝ) (hx : x ∈ generatedTenthE8CoordinateSection) :
    e.val x ∈ generatedTenthE8CoordinateSection := by
  rw [← generatedTenth_e7_slice_span_eq] at hx ⊢
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨u, hu, rfl⟩ := hx
      rw [integral_action_cast e ⟨u, hu.1⟩]
      exact Submodule.subset_span ⟨_, slice_action e he u hu, rfl⟩
  | zero => rw [map_zero]; exact generatedTenthE7SliceSpan.zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact generatedTenthE7SliceSpan.add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact generatedTenthE7SliceSpan.smul_mem a hx

/-- An actual Leech isometry commuting with the complete E7 projector preserves
the actual E8 section. -/
theorem generatedTenth_e8_preserved_of_e7_projection (e : leechIsomSubgroup)
    (he : ∀ x : Fin 24 → ℝ,
      e.val (generatedTenthE7ProjectionInteger.map (Int.castRingHom ℝ) *ᵥ x) =
        generatedTenthE7ProjectionInteger.map (Int.castRingHom ℝ) *ᵥ e.val x)
    (x : Fin 24 → ℝ) :
    x ∈ generatedTenthE8CoordinateSection ↔ e.val x ∈ generatedTenthE8CoordinateSection := by
  constructor
  · exact section_action e he x
  · intro hx
    have hinv : ∀ y, e.val.symm (realProjection y) =
        realProjection (e.val.symm y) := by
      intro y
      apply e.val.injective
      have he' : ∀ z, e.val (realProjection z) = realProjection (e.val z) := he
      rw [e.val.apply_symm_apply, he', e.val.apply_symm_apply]
    have h := section_action e⁻¹ hinv (e.val x) hx
    change e.val.symm (e.val x) ∈ generatedTenthE8CoordinateSection at h
    rw [e.val.symm_apply_apply] at h
    exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
