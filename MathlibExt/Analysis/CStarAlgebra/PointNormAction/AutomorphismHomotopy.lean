/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.Homotopy

import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Topology.Path
import Mathlib.Tactic.NormNum

/-!
# Point-norm homotopies through C-star automorphisms

This file packages paths whose intermediate maps are complex star-algebra
automorphisms.  Only forward point-norm continuity is stored: continuity of
the inverse orbits follows from isometry.  The resulting path has a canonical
forgetful map to the weaker homomorphism-valued point-norm homotopy.
-/

@[expose] public section

open scoped CStarAlgebra

noncomputable section

universe uA uB

/-- A point-norm continuous path through complex star-algebra automorphisms. -/
structure AutomorphismHomotopy
    {A : Type uA} [NonUnitalCStarAlgebra A]
    (α β : A ≃⋆ₐ[ℂ] A) where
  /-- The automorphism at one point of the unit interval. -/
  aut : unitInterval → A ≃⋆ₐ[ℂ] A
  /-- Every coefficient varies continuously along the path. -/
  continuous_apply : ∀ a : A, Continuous fun t ↦ aut t a
  /-- The path starts at `α`. -/
  zero : aut 0 = α
  /-- The path ends at `β`. -/
  one : aut 1 = β

namespace AutomorphismHomotopy

variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable {α β γ : A ≃⋆ₐ[ℂ] A}

/-- Automorphism homotopies are determined by their path of automorphisms. -/
@[ext]
theorem ext {h k : AutomorphismHomotopy α β} (haut : h.aut = k.aut) : h = k := by
  cases h
  cases k
  cases haut
  rfl

@[simp]
theorem aut_zero (h : AutomorphismHomotopy α β) : h.aut 0 = α :=
  h.zero

@[simp]
theorem aut_one (h : AutomorphismHomotopy α β) : h.aut 1 = β :=
  h.one

/-- Forward point-norm continuity forces continuity of every inverse orbit. -/
theorem continuous_symm_apply (h : AutomorphismHomotopy α β) (a : A) :
    Continuous fun t ↦ (h.aut t).symm a := by
  rw [continuous_iff_continuousAt]
  intro t₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  let b : A := (h.aut t₀).symm a
  filter_upwards [
      (Metric.tendsto_nhds.mp (h.continuous_apply b).continuousAt) ε hε] with t ht
  calc
    dist ((h.aut t).symm a) ((h.aut t₀).symm a) =
        dist (h.aut t ((h.aut t).symm a))
          (h.aut t ((h.aut t₀).symm a)) :=
      ((StarAlgEquiv.isometry (h.aut t)).dist_eq _ _).symm
    _ = dist a (h.aut t b) := by simp [b]
    _ < ε := by simpa [b, dist_comm] using ht

/-- The constant automorphism homotopy. -/
def refl (α : A ≃⋆ₐ[ℂ] A) : AutomorphismHomotopy α α where
  aut := fun _ ↦ α
  continuous_apply := fun _ ↦ continuous_const
  zero := rfl
  one := rfl

/-- Reverse the interval parameter of an automorphism homotopy. -/
def symm (h : AutomorphismHomotopy α β) : AutomorphismHomotopy β α where
  aut := fun t ↦ h.aut (unitInterval.symmHomeomorph t)
  continuous_apply := fun a ↦
    (h.continuous_apply a).comp unitInterval.symmHomeomorph.continuous
  zero := by simp [h.one]
  one := by simp [h.zero]

/-- Invert every automorphism along a homotopy without reversing time. -/
def inverse (h : AutomorphismHomotopy α β) :
    AutomorphismHomotopy α.symm β.symm where
  aut := fun t ↦ (h.aut t).symm
  continuous_apply := h.continuous_symm_apply
  zero := by rw [h.zero]
  one := by rw [h.one]

/-- Postcompose every member of an automorphism homotopy by a fixed
automorphism. -/
def compLeft (h : AutomorphismHomotopy α β) (δ : A ≃⋆ₐ[ℂ] A) :
    AutomorphismHomotopy (δ * α) (δ * β) where
  aut := fun t ↦ δ * h.aut t
  continuous_apply := fun a ↦ by
    change Continuous fun t ↦ δ (h.aut t a)
    exact (map_continuous δ.toNonUnitalStarAlgHom).comp (h.continuous_apply a)
  zero := by rw [h.zero]
  one := by rw [h.one]

/-- Precompose every member of an automorphism homotopy by a fixed
automorphism. -/
def compRight (h : AutomorphismHomotopy α β) (δ : A ≃⋆ₐ[ℂ] A) :
    AutomorphismHomotopy (α * δ) (β * δ) where
  aut := fun t ↦ h.aut t * δ
  continuous_apply := fun a ↦ by
    change Continuous fun t ↦ h.aut t (δ a)
    exact h.continuous_apply (δ a)
  zero := by rw [h.zero]
  one := by rw [h.one]

/-- Concatenate two automorphism homotopies, following the first on
`[0, 1/2]` and the second on `[1/2, 1]`. -/
noncomputable def trans
    (h : AutomorphismHomotopy α β) (k : AutomorphismHomotopy β γ) :
    AutomorphismHomotopy α γ := by
  let hPath (a : A) : Path (α a) (β a) :=
    { toContinuousMap := ⟨fun t ↦ h.aut t a, h.continuous_apply a⟩
      source' := by
        change h.aut 0 a = α a
        rw [h.zero]
      target' := by
        change h.aut 1 a = β a
        rw [h.one] }
  let kPath (a : A) : Path (β a) (γ a) :=
    { toContinuousMap := ⟨fun t ↦ k.aut t a, k.continuous_apply a⟩
      source' := by
        change k.aut 0 a = β a
        rw [k.zero]
      target' := by
        change k.aut 1 a = γ a
        rw [k.one] }
  let pathAut : unitInterval → A ≃⋆ₐ[ℂ] A := fun t ↦
    if ht : (t : ℝ) ≤ 1 / 2 then
      h.aut ⟨2 * (t : ℝ),
        (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩
    else
      k.aut ⟨2 * (t : ℝ) - 1,
        unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩
  have pathAut_apply (t : unitInterval) (a : A) :
      pathAut t a =
        ((hPath a).trans (kPath a)) t := by
    rw [Path.trans_apply]
    dsimp only [pathAut]
    split_ifs <;> rfl
  exact
    { aut := pathAut
      continuous_apply := fun a ↦ by
        rw [show (fun t ↦ pathAut t a) =
            fun t ↦ ((hPath a).trans (kPath a)) t by
          funext t
          exact pathAut_apply t a]
        exact ((hPath a).trans (kPath a)).continuous
      zero := by
        apply StarAlgEquiv.ext
        intro a
        rw [pathAut_apply]
        exact Path.source _
      one := by
        apply StarAlgEquiv.ext
        intro a
        rw [pathAut_apply]
        exact Path.target _ }

@[simp]
theorem refl_aut (α : A ≃⋆ₐ[ℂ] A) (t : unitInterval) :
    (refl α).aut t = α :=
  rfl

@[simp]
theorem symm_aut_apply (h : AutomorphismHomotopy α β)
    (t : unitInterval) (a : A) :
    h.symm.aut t a = h.aut (unitInterval.symmHomeomorph t) a :=
  rfl

@[simp]
theorem inverse_aut_apply (h : AutomorphismHomotopy α β)
    (t : unitInterval) (a : A) :
    h.inverse.aut t a = (h.aut t).symm a :=
  rfl

@[simp]
theorem compLeft_aut_apply (h : AutomorphismHomotopy α β)
    (δ : A ≃⋆ₐ[ℂ] A) (t : unitInterval) (a : A) :
    (h.compLeft δ).aut t a = δ (h.aut t a) :=
  rfl

@[simp]
theorem compRight_aut_apply (h : AutomorphismHomotopy α β)
    (δ : A ≃⋆ₐ[ℂ] A) (t : unitInterval) (a : A) :
    (h.compRight δ).aut t a = h.aut t (δ a) :=
  rfl

/-- On the left half of the interval, concatenation is the first path with
the parameter doubled. -/
theorem trans_apply_of_le_half (h : AutomorphismHomotopy α β)
    (k : AutomorphismHomotopy β γ) (t : unitInterval)
    (ht : (t : ℝ) ≤ 1 / 2) (a : A) :
    (h.trans k).aut t a =
      h.aut ⟨2 * (t : ℝ),
        (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩ a := by
  have ht' : (t : ℝ) ≤ (2 : ℝ)⁻¹ := by
    simpa only [one_div] using ht
  simp [trans, ht']

/-- On the strict right half of the interval, concatenation is the second
path with parameter `2t - 1`. -/
theorem trans_apply_of_half_lt (h : AutomorphismHomotopy α β)
    (k : AutomorphismHomotopy β γ) (t : unitInterval)
    (ht : 1 / 2 < (t : ℝ)) (a : A) :
    (h.trans k).aut t a =
      k.aut ⟨2 * (t : ℝ) - 1,
        unitInterval.two_mul_sub_one_mem_iff.2 ⟨ht.le, t.2.2⟩⟩ a := by
  have ht' : ¬(t : ℝ) ≤ (2 : ℝ)⁻¹ := by
    apply not_le.mpr
    simpa only [one_div] using ht
  simp [trans, ht']

@[simp]
theorem trans_aut_zero (h : AutomorphismHomotopy α β)
    (k : AutomorphismHomotopy β γ) : (h.trans k).aut 0 = α :=
  (h.trans k).zero

@[simp]
theorem trans_aut_one (h : AutomorphismHomotopy α β)
    (k : AutomorphismHomotopy β γ) : (h.trans k).aut 1 = γ :=
  (h.trans k).one

/-- The concatenated homotopy has the common endpoint at time `1/2`. -/
theorem trans_aut_half (h : AutomorphismHomotopy α β)
    (k : AutomorphismHomotopy β γ) :
    (h.trans k).aut
        ⟨(1 : ℝ) / 2, by constructor <;> norm_num⟩ = β := by
  apply StarAlgEquiv.ext
  intro a
  simp [trans, h.one]

/-- The proposition that two automorphisms are joined by a point-norm
automorphism homotopy. -/
def AutomorphismHomotopic (α β : A ≃⋆ₐ[ℂ] A) : Prop :=
  Nonempty (AutomorphismHomotopy α β)

/-- Point-norm automorphism homotopy is an equivalence relation. -/
theorem automorphismHomotopic_equivalence (A : Type uA)
    [NonUnitalCStarAlgebra A] :
    Equivalence (AutomorphismHomotopic :
      (A ≃⋆ₐ[ℂ] A) → (A ≃⋆ₐ[ℂ] A) → Prop) := by
  refine ⟨fun δ ↦ ⟨refl δ⟩, ?_, ?_⟩
  · rintro δ ε ⟨h⟩
    exact ⟨h.symm⟩
  · rintro δ ε ζ ⟨h⟩ ⟨k⟩
    exact ⟨h.trans k⟩

/-! ## Forgetful map to homomorphism-valued homotopy -/

/-- An automorphism homotopy as one nonunital star-algebra homomorphism into
the algebra of continuous paths. -/
def toHomotopyMap (h : AutomorphismHomotopy α β) :
    A →⋆ₙₐ[ℂ] C(unitInterval, A) where
  toFun a := ⟨fun t ↦ h.aut t a, h.continuous_apply a⟩
  map_zero' := by ext; simp
  map_add' a b := by ext t; exact map_add (h.aut t) a b
  map_mul' a b := by ext t; exact map_mul (h.aut t) a b
  map_smul' z a := by ext t; exact map_smul (h.aut t) z a
  map_star' a := by ext t; exact map_star (h.aut t) a

@[simp]
theorem toHomotopyMap_apply (h : AutomorphismHomotopy α β)
    (a : A) (t : unitInterval) : h.toHomotopyMap a t = h.aut t a :=
  rfl

/-- Forgetting invertibility gives a point-norm homotopy of nonunital
star-algebra homomorphisms with the same endpoint orientation. -/
theorem toHomotopic (h : AutomorphismHomotopy α β) :
    NonUnitalStarAlgHom.Homotopic
      α.toNonUnitalStarAlgHom β.toNonUnitalStarAlgHom := by
  refine ⟨h.toHomotopyMap, ?_, ?_⟩
  · intro a
    change h.aut 0 a = α a
    rw [h.zero]
  · intro a
    change h.aut 1 a = β a
    rw [h.one]

/-- Postcomposition preserves the homomorphism homotopy underlying an
automorphism homotopy. -/
theorem toHomotopic_postcomp (h : AutomorphismHomotopy α β)
    {B : Type uB} [NonUnitalCStarAlgebra B]
    (δ : A →⋆ₙₐ[ℂ] B) :
    (δ.comp α.toNonUnitalStarAlgHom).Homotopic
      (δ.comp β.toNonUnitalStarAlgHom) :=
  h.toHomotopic.postcomp δ

/-- Precomposition preserves the homomorphism homotopy underlying an
automorphism homotopy. -/
theorem toHomotopic_precomp (h : AutomorphismHomotopy α β)
    {B : Type uB} [NonUnitalCStarAlgebra B]
    (δ : B →⋆ₙₐ[ℂ] A) :
    (α.toNonUnitalStarAlgHom.comp δ).Homotopic
      (β.toNonUnitalStarAlgHom.comp δ) :=
  h.toHomotopic.precomp δ

/-- Left composition of an automorphism path has the correspondingly
postcomposed homomorphism-homotopy endpoints. -/
theorem compLeft_toHomotopic (h : AutomorphismHomotopy α β)
    (δ : A ≃⋆ₐ[ℂ] A) :
    NonUnitalStarAlgHom.Homotopic
      (δ * α).toNonUnitalStarAlgHom (δ * β).toNonUnitalStarAlgHom :=
  (h.compLeft δ).toHomotopic

/-- Right composition of an automorphism path has the correspondingly
precomposed homomorphism-homotopy endpoints. -/
theorem compRight_toHomotopic (h : AutomorphismHomotopy α β)
    (δ : A ≃⋆ₐ[ℂ] A) :
    NonUnitalStarAlgHom.Homotopic
      (α * δ).toNonUnitalStarAlgHom (β * δ).toNonUnitalStarAlgHom :=
  (h.compRight δ).toHomotopic

/-- Reversing an automorphism homotopy reverses its underlying homomorphism
homotopy. -/
theorem toHomotopic_symm (h : AutomorphismHomotopy α β) :
    NonUnitalStarAlgHom.Homotopic
      β.toNonUnitalStarAlgHom α.toNonUnitalStarAlgHom :=
  h.toHomotopic.symm

/-- Concatenating automorphism homotopies concatenates their underlying
homomorphism homotopies. -/
theorem toHomotopic_trans (h : AutomorphismHomotopy α β)
    (k : AutomorphismHomotopy β γ) :
    NonUnitalStarAlgHom.Homotopic
      α.toNonUnitalStarAlgHom γ.toNonUnitalStarAlgHom :=
  h.toHomotopic.trans k.toHomotopic

end AutomorphismHomotopy
