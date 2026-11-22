/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.Euclidean.DiscreteGroups
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic

/-!
# Tests for discrete subgroups of the Euclidean plane

The point group preserves the translation lattice (trivial and whole-group
cases), conjugation of a translation is translation by the transported
vector, and the classification of discrete additive subgroups of the plane
applies to the trivial subgroup, to cyclic subgroups, and to arbitrary
discrete subgroups. The source separation criterion and classification bridge
are exercised on trivial and nontrivial cyclic plane-translation groups.
-/

@[expose] public section

namespace MathlibExtTest.Geometry.Euclidean.DiscreteGroups

-- `_root_` disambiguates from this file's own `...Euclidean.DiscreteGroups` namespace.
open _root_.DiscreteGroups

/-- Conjugating a translation by the identity isometry does nothing. -/
example (v : E2) :
    (1 : M₂) * (AffineIsometryEquiv.constVAdd ℝ E2 v) * (1 : M₂)⁻¹ =
      AffineIsometryEquiv.constVAdd ℝ E2 v := by
  simp

/-- The point group of the trivial isometry group preserves its (trivial)
translation lattice, at the identity linear part and the zero vector. -/
example : (LinearIsometryEquiv.refl ℝ E2) (0 : E2) ∈
    translationLattice (⊥ : Subgroup M₂) :=
  point_group_preserves_lattice ⊥ (LinearIsometryEquiv.refl ℝ E2)
    ⟨1, Subgroup.mem_bot.mpr rfl, by rfl⟩ 0
    (by
      show (AffineIsometryEquiv.constVAdd ℝ E2 (0 : E2) : M₂) ∈ (⊥ : Subgroup M₂)
      rw [show (AffineIsometryEquiv.constVAdd ℝ E2 (0 : E2) : M₂) = 1 from by
        ext x; simp]
      exact Subgroup.mem_bot.mpr rfl)

/-- The point group of the whole isometry group preserves its (whole)
translation lattice, at an arbitrary linear part and vector. -/
example (A : E2 ≃ₗᵢ[ℝ] E2) (v : E2) :
    A v ∈ translationLattice (⊤ : Subgroup M₂) :=
  point_group_preserves_lattice ⊤ A
    ⟨A.toAffineIsometryEquiv, Subgroup.mem_top _,
      by simp [linearPart, LinearIsometryEquiv.toAffineIsometryEquiv_linearIsometryEquiv]⟩
    v (by
      show (AffineIsometryEquiv.constVAdd ℝ E2 v : M₂) ∈ (⊤ : Subgroup M₂)
      exact Subgroup.mem_top _)

/-- The classification applies to the trivial additive subgroup. -/
example :
    (⊥ : AddSubgroup E2) = ⊥ ∨
    (∃ α : E2, α ≠ 0 ∧ (⊥ : AddSubgroup E2) = AddSubgroup.zmultiples α) ∨
    (∃ a b : E2, LinearIndependent ℝ ![a, b] ∧
      (⊥ : AddSubgroup E2) = AddSubgroup.zmultiples a ⊔ AddSubgroup.zmultiples b) :=
  discrete_subgroup_R2_classification ⊥

/-- The classification applies to every cyclic additive subgroup. -/
example (α : E2) :
    AddSubgroup.zmultiples α = ⊥ ∨
    (∃ β : E2, β ≠ 0 ∧ AddSubgroup.zmultiples α = AddSubgroup.zmultiples β) ∨
    (∃ a b : E2, LinearIndependent ℝ ![a, b] ∧
      AddSubgroup.zmultiples α = AddSubgroup.zmultiples a ⊔ AddSubgroup.zmultiples b) :=
  discrete_subgroup_R2_classification (AddSubgroup.zmultiples α)

/-- The classification applies to every discrete additive subgroup. -/
example (G : AddSubgroup E2) [DiscreteTopology G] :
    G = ⊥ ∨
    (∃ α : E2, α ≠ 0 ∧ G = AddSubgroup.zmultiples α) ∨
    (∃ a b : E2, LinearIndependent ℝ ![a, b] ∧
      G = AddSubgroup.zmultiples a ⊔ AddSubgroup.zmultiples b) :=
  discrete_subgroup_R2_classification G

/-- A rank-two lattice satisfies the third alternative of the classification. -/
example (a b : E2) (h : LinearIndependent ℝ ![a, b])
    (G : AddSubgroup E2) (hG : G = AddSubgroup.zmultiples a ⊔ AddSubgroup.zmultiples b)
    [DiscreteTopology G] :
    G = ⊥ ∨
    (∃ α : E2, α ≠ 0 ∧ G = AddSubgroup.zmultiples α) ∨
    (∃ a' b' : E2, LinearIndependent ℝ ![a', b'] ∧
      G = AddSubgroup.zmultiples a' ⊔ AddSubgroup.zmultiples b') :=
  Or.inr (Or.inr ⟨a, b, h, hG⟩)

example (G : Subgroup M₂) {v w : E2}
    (hv : v ∈ translationLattice G) (hw : w ∈ translationLattice G) :
    v + w ∈ translationLattice G :=
  (translationLatticeSubgroup G).add_mem hv hw

example (G : Subgroup M₂) {v : E2} (hv : v ∈ translationLattice G) :
    -v ∈ translationLattice G := (translationLatticeSubgroup G).neg_mem hv

example (G : Subgroup M₂) : (0 : E2) ∈ translationLattice G :=
  (translationLatticeSubgroup G).zero_mem

/-- The trivial plane-isometry group meets the source criterion. -/
private theorem isDiscrete_bot : IsDiscrete (⊥ : Subgroup M₂) := by
  refine ⟨1, zero_lt_one, ?_, ?_⟩
  · intro f hf hpure hne
    exact False.elim (hne (Subgroup.mem_bot.mp hf))
  · intro f hf hne
    rw [Subgroup.mem_bot.mp hf] at hne
    exact False.elim (hne rfl)

private noncomputable def cyclicTranslationGroup (v : E2) : Subgroup M₂ :=
  (AddSubgroup.zmultiples v).toSubgroup.map translationHom

private theorem translationLatticeSubgroup_cyclicTranslationGroup (v : E2) :
    translationLatticeSubgroup (cyclicTranslationGroup v) = AddSubgroup.zmultiples v := by
  ext w
  change translationHom (Multiplicative.ofAdd w) ∈
      (AddSubgroup.zmultiples v).toSubgroup.map translationHom ↔
    Multiplicative.ofAdd w ∈ (AddSubgroup.zmultiples v).toSubgroup
  exact Subgroup.mem_map_iff_mem translationHom_injective

private theorem isDiscrete_cyclicTranslationGroup (v : E2) (hv : v ≠ 0) :
    IsDiscrete (cyclicTranslationGroup v) := by
  refine ⟨‖v‖, norm_pos_iff.mpr hv, ?_, ?_⟩
  · intro f hf hpure hne
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hf
    have hw' : Multiplicative.toAdd w ∈ AddSubgroup.zmultiples v := hw
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hw'
    have hn0 : n ≠ 0 := by
      intro h0
      apply hne
      apply AffineIsometryEquiv.ext
      intro x
      change Multiplicative.toAdd w + x = x
      have hw0 : Multiplicative.toAdd w = 0 := by simpa [h0] using hn.symm
      rw [hw0, zero_add]
    have hnabs : (1 : ℝ) ≤ ‖(n : ℝ)‖ := by
      rw [Real.norm_eq_abs]
      exact_mod_cast Int.one_le_abs hn0
    calc ‖v‖ = 1 * ‖v‖ := (one_mul _).symm
      _ ≤ ‖(n : ℝ)‖ * ‖v‖ := mul_le_mul_of_nonneg_right hnabs (norm_nonneg _)
      _ = ‖n • v‖ := (norm_zsmul ℝ n v).symm
      _ = ‖translationHom w 0‖ := by rw [hn]; simp [translationHom]
  · intro f hf hne
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hf
    exact False.elim (hne (by ext x; rfl))

private theorem cyclicTranslationGroup_ne_bot (v : E2) (hv : v ≠ 0) :
    cyclicTranslationGroup v ≠ ⊥ := by
  intro hbot
  have hv' : Multiplicative.ofAdd v ∈ (AddSubgroup.zmultiples v).toSubgroup := by
    change v ∈ AddSubgroup.zmultiples v
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨1, by simp⟩
  have hmem := Subgroup.mem_map_of_mem translationHom hv'
  have hid : translationHom (Multiplicative.ofAdd v) = 1 := by
    apply Subgroup.mem_bot.mp
    rw [← hbot]
    exact hmem
  have hzero := congrArg (fun f : M₂ => f 0) hid
  exact hv (by simpa [translationHom] using hzero)

example (v : E2) (hv : v ≠ 0) :
    DiscreteTopology (translationLatticeSubgroup (cyclicTranslationGroup v)) :=
  translationLatticeSubgroup_discreteTopology _ (isDiscrete_cyclicTranslationGroup v hv)

/-- The claimed corollary is callable for the trivial plane-isometry group. -/
example : translationLatticeSubgroup (⊥ : Subgroup M₂) = ⊥ ∨
    (∃ α : E2, α ≠ 0 ∧ translationLatticeSubgroup (⊥ : Subgroup M₂) =
      AddSubgroup.zmultiples α) ∨
    (∃ a b : E2, LinearIndependent ℝ ![a, b] ∧
      translationLatticeSubgroup (⊥ : Subgroup M₂) =
        AddSubgroup.zmultiples a ⊔ AddSubgroup.zmultiples b) :=
  translation_lattice_classification ⊥ isDiscrete_bot

/-- It is also callable for a nontrivial cyclic plane-translation group. -/
example (v : E2) (hv : v ≠ 0) : translationLatticeSubgroup (cyclicTranslationGroup v) = ⊥ ∨
    (∃ α : E2, α ≠ 0 ∧ translationLatticeSubgroup (cyclicTranslationGroup v) =
      AddSubgroup.zmultiples α) ∨
    (∃ a b : E2, LinearIndependent ℝ ![a, b] ∧
      translationLatticeSubgroup (cyclicTranslationGroup v) =
        AddSubgroup.zmultiples a ⊔ AddSubgroup.zmultiples b) :=
  translation_lattice_classification _ (isDiscrete_cyclicTranslationGroup v hv)

#print axioms isDiscrete_bot
#print axioms translationLatticeSubgroup_cyclicTranslationGroup
#print axioms isDiscrete_cyclicTranslationGroup
#print axioms cyclicTranslationGroup_ne_bot

end MathlibExtTest.Geometry.Euclidean.DiscreteGroups
