/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Definitions
public import Mathlib.Algebra.Group.AddChar
/-! The binary character-coset Fourier identity used by octad triality.

A symmetric binary form identifies a self-annihilating subspace's coset
character with its normalized Fourier transform. Character orthogonality
uses Mathlib's AddChar.sum_eq_ite, without enumerating pairs of vectors.
The ambient Fourier theorem requires the self-annihilator and cardinality
hypotheses explicitly. Instantiating them for three physical octad sign
spaces is a separate source-coordinate calculation.
Source: finite Fourier character orthogonality and Seysen's octad triality. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def binarySubspaceCharacter {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2)
    (L : Submodule (ZMod 2) V) (w : V) : AddChar L ℝ where
  toFun l := qSign (B l.val w)
  map_zero_eq_one' := by simp only [ZeroMemClass.coe_zero, map_zero, LinearMap.zero_apply,
    qSign_zero]
  map_add_eq_mul' l m := by
    simp only [Submodule.coe_add, map_add, LinearMap.add_apply, qSign_add]

lemma binarySubspaceCharacter_eq_zero_iff {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2)
    (L : Submodule (ZMod 2) V) (w : V) :
    binarySubspaceCharacter B L w = 0 ↔ ∀ l : L, B l.val w = 0 := by
  constructor
  · intro h l
    have hl := congrArg (fun χ : AddChar L ℝ => χ l) h
    change qSign (B l.val w) = 1 at hl
    exact (qSign_eq_one_iff _).mp hl
  · intro h
    apply AddChar.ext
    intro l
    change qSign (B l.val w) = 1
    rw [h l, qSign_zero]

lemma binarySubspace_character_sum {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2)
    (L : Submodule (ZMod 2) V) [Fintype L]
    (hL : ∀ w : V, (∀ l : L, B l.val w = 0) ↔ w ∈ L) (w : V) :
    (∑ l : L, qSign (B l.val w)) = if w ∈ L then (Fintype.card L : ℝ) else 0 := by
  classical
  have h := AddChar.sum_eq_ite (binarySubspaceCharacter B L w)
  change (∑ l : L, qSign (B l.val w)) =
    if binarySubspaceCharacter B L w = 0 then (Fintype.card L : ℝ) else 0 at h
  simpa only [binarySubspaceCharacter_eq_zero_iff, hL] using h

lemma lagrangianFourier_coset_sum {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2)
    (hs : ∀ x y, B x y = B y x) (L : Submodule (ZMod 2) V) [Fintype L]
    (hL : ∀ w : V, (∀ l : L, B l.val w = 0) ↔ w ∈ L)
    (t w : V) (ht : B t t = 0) :
    (∑ l : L, qSign (B t (t + l.val)) * qSign (B (t + l.val) w)) =
      qSign (B t w) * (if t + w ∈ L then (Fintype.card L : ℝ) else 0) := by
  classical
  have hphase (l : L) : B t (t + l.val) + B (t + l.val) w =
      B t w + B l.val (t + w) := by
    simp only [map_add, LinearMap.add_apply, ht]
    rw [hs t l.val]
    ring
  simp_rw [← qSign_add, hphase, qSign_add]
  rw [← Finset.mul_sum, binarySubspace_character_sum B L hL]

/-- The normalized character sum over the actual translate of a self-annihilating subspace. -/
theorem lagrangianFourier_coset {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2)
    (hs : ∀ x y, B x y = B y x) (L : Submodule (ZMod 2) V) [Fintype L]
    (hL : ∀ w : V, (∀ l : L, B l.val w = 0) ↔ w ∈ L)
    (t w : V) (ht : B t t = 0) :
    (∑ l : L, qSign (B t (t + l.val)) * qSign (B (t + l.val) w)) /
        (Fintype.card L : ℝ) =
      if t + w ∈ L then qSign (B t w) else 0 := by
  classical
  rw [lagrangianFourier_coset_sum B hs L hL t w ht]
  have hn : (Fintype.card L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  by_cases h : t + w ∈ L
  · simp only [h, ite_true]
    exact mul_div_cancel_right₀ _ hn
  · simp only [h, ite_false, mul_zero, zero_div]

private lemma binaryModule_add_self {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (v : V) : v + v = 0 := by
  rw [← one_smul (ZMod 2) v, ← add_smul,
    show (1 : ZMod 2) + 1 = 0 by decide, zero_smul]

lemma binaryCoset_indicator_sum {V : Type*} [AddCommGroup V] [Fintype V]
    [Module (ZMod 2) V] (L : Submodule (ZMod 2) V) [Fintype L] (t : V) (f : V → ℝ) :
    (∑ v : V, if t + v ∈ L then f v else 0) = ∑ l : L, f (t + l.val) := by
  classical
  let e : L → V := fun l => t + l.val
  have he : Function.Injective e := by
    intro l m h
    exact Subtype.ext (add_left_cancel h)
  symm
  apply Fintype.sum_of_injective e he
  · intro v hv
    have hnot : t + v ∉ L := by
      intro hm
      apply hv
      refine ⟨⟨t + v, hm⟩, ?_⟩
      change t + (t + v) = v
      rw [← add_assoc, binaryModule_add_self, zero_add]
    simp only [hnot, ite_false]
  · intro l
    have hm : t + e l ∈ L := by
      change t + (t + l.val) ∈ L
      rw [← add_assoc, binaryModule_add_self, zero_add]
      exact l.property
    simp only [hm, ite_true]
    rfl

/-- The complete ambient normalized Fourier identity for a binary coset character. -/
theorem lagrangianFourier_indicator {V : Type*} [AddCommGroup V] [Fintype V]
    [Module (ZMod 2) V] (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2)
    (hs : ∀ x y, B x y = B y x) (L : Submodule (ZMod 2) V) [Fintype L]
    (hL : ∀ w : V, (∀ l : L, B l.val w = 0) ↔ w ∈ L)
    (hcard : (Fintype.card L : ℝ) = Real.sqrt (Fintype.card V : ℝ))
    (t w : V) (ht : B t t = 0) :
    (∑ v : V, (if t + v ∈ L then qSign (B t v) else 0) * qSign (B v w)) /
        Real.sqrt (Fintype.card V : ℝ) =
      if t + w ∈ L then qSign (B t w) else 0 := by
  have hterm (v : V) :
      (if t + v ∈ L then qSign (B t v) else 0) * qSign (B v w) =
        if t + v ∈ L then qSign (B t v) * qSign (B v w) else 0 := by
    split_ifs <;> simp
  simp_rw [hterm]
  rw [binaryCoset_indicator_sum L t, ← hcard]
  exact lagrangianFourier_coset B hs L hL t w ht
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
