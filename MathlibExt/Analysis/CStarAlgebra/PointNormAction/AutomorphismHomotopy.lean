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
# Point-norm homotopies of C-star automorphisms

For a nonunital complex C-star algebra A, a homotopy from α to β is a path t ↦ hₜ of
star-algebra automorphisms on [0,1] such that t ↦ hₜ(a) is norm-continuous for every a ∈ A,
with h₀ = α and h₁ = β. Isometry implies continuity of the inverse orbits. Reversal, inversion
and concatenation preserve this condition, and a path determines a star homomorphism A →
C([0,1],A).
-/

@[expose] public section

open scoped CStarAlgebra

noncomputable section

universe uA uB

/-- **Point-norm automorphism homotopy.**

For a nonunital complex C-star algebra A and automorphisms α, β, this structure records a path
hₜ ∈ Aut(A), continuous in norm on each coefficient a, with endpoints α and β.
-/
structure AutomorphismHomotopy
    {A : Type uA} [NonUnitalCStarAlgebra A]
    (α β : A ≃⋆ₐ[ℂ] A) where
  /-- **Automorphism path.**

The map t ↦ hₜ from [0,1] to complex star-algebra automorphisms of A.
-/
  aut : unitInterval → A ≃⋆ₐ[ℂ] A
  /-- **Point-norm continuity.**

For every a ∈ A, the function t ↦ hₜ(a) is continuous in the C-star norm.
-/
  continuous_apply : ∀ a : A, Continuous fun t ↦ aut t a
  /-- **Initial automorphism.**

The automorphism path satisfies h₀ = α.
-/
  zero : aut 0 = α
  /-- **Final automorphism.**

The automorphism path satisfies h₁ = β.
-/
  one : aut 1 = β

namespace AutomorphismHomotopy

variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable {α β γ : A ≃⋆ₐ[ℂ] A}

/-- **Equality of automorphism homotopies.**

Two point-norm homotopies from α to β are equal when their paths of automorphisms are equal.
-/
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

/-- **Continuity of inverse automorphism orbits.**

For a point-norm homotopy h and a ∈ A, the function t ↦ hₜ⁻¹(a) is norm-continuous. No
separate continuity condition on inverse orbits is required.
-/
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

/-- **Constant automorphism homotopy.**

The constant path hₜ = α is a point-norm automorphism homotopy from α to itself.
-/
def refl (α : A ≃⋆ₐ[ℂ] A) : AutomorphismHomotopy α α where
  aut := fun _ ↦ α
  continuous_apply := fun _ ↦ continuous_const
  zero := rfl
  one := rfl

/-- **Reversal of an automorphism homotopy.**

A homotopy h from α to β gives the homotopy t ↦ h₁₋ₜ from β to α.
-/
def symm (h : AutomorphismHomotopy α β) : AutomorphismHomotopy β α where
  aut := fun t ↦ h.aut (unitInterval.symmHomeomorph t)
  continuous_apply := fun a ↦
    (h.continuous_apply a).comp unitInterval.symmHomeomorph.continuous
  zero := by simp [h.one]
  one := by simp [h.zero]

/-- **Pointwise inversion of an automorphism homotopy.**

The path t ↦ hₜ⁻¹ is a point-norm homotopy from α⁻¹ to β⁻¹; the interval parameter is
unchanged.
-/
def inverse (h : AutomorphismHomotopy α β) :
    AutomorphismHomotopy α.symm β.symm where
  aut := fun t ↦ (h.aut t).symm
  continuous_apply := h.continuous_symm_apply
  zero := by rw [h.zero]
  one := by rw [h.one]

/-- **Postcomposition of an automorphism homotopy.**

For an automorphism δ of A, the path t ↦ δ ∘ hₜ joins δ ∘ α to δ ∘ β and is point-norm
continuous.
-/
def compLeft (h : AutomorphismHomotopy α β) (δ : A ≃⋆ₐ[ℂ] A) :
    AutomorphismHomotopy (δ * α) (δ * β) where
  aut := fun t ↦ δ * h.aut t
  continuous_apply := fun a ↦ by
    change Continuous fun t ↦ δ (h.aut t a)
    exact (map_continuous δ.toNonUnitalStarAlgHom).comp (h.continuous_apply a)
  zero := by rw [h.zero]
  one := by rw [h.one]

/-- **Precomposition of an automorphism homotopy.**

For an automorphism δ of A, the path t ↦ hₜ ∘ δ joins α ∘ δ to β ∘ δ and is point-norm
continuous.
-/
def compRight (h : AutomorphismHomotopy α β) (δ : A ≃⋆ₐ[ℂ] A) :
    AutomorphismHomotopy (α * δ) (β * δ) where
  aut := fun t ↦ h.aut t * δ
  continuous_apply := fun a ↦ by
    change Continuous fun t ↦ h.aut t (δ a)
    exact h.continuous_apply (δ a)
  zero := by rw [h.zero]
  one := by rw [h.one]

/-- **Concatenation of automorphism homotopies.**

A homotopy h from α to β and k from β to γ give a homotopy from α to γ: use h₂ₜ for t ≤ 1/2
and k₂ₜ₋₁ for t > 1/2.
-/
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

/-- **Concatenation on the first half interval.**

For t ≤ 1/2 and a ∈ A, the concatenated path satisfies (h.trans k)ₜ(a) = h₂ₜ(a).
-/
theorem trans_apply_of_le_half (h : AutomorphismHomotopy α β)
    (k : AutomorphismHomotopy β γ) (t : unitInterval)
    (ht : (t : ℝ) ≤ 1 / 2) (a : A) :
    (h.trans k).aut t a =
      h.aut ⟨2 * (t : ℝ),
        (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩ a := by
  have ht' : (t : ℝ) ≤ (2 : ℝ)⁻¹ := by
    simpa only [one_div] using ht
  simp [trans, ht']

/-- **Concatenation on the second half interval.**

For t > 1/2 and a ∈ A, the concatenated path satisfies (h.trans k)ₜ(a) = k₂ₜ₋₁(a).
-/
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

/-- **The midpoint of a concatenated homotopy.**

At t = 1/2, the concatenation of h : α → β and k : β → γ equals the common endpoint β.
-/
theorem trans_aut_half (h : AutomorphismHomotopy α β)
    (k : AutomorphismHomotopy β γ) :
    (h.trans k).aut
        ⟨(1 : ℝ) / 2, by constructor <;> norm_num⟩ = β := by
  apply StarAlgEquiv.ext
  intro a
  simp [trans, h.one]

/-- **Homotopic C-star automorphisms.**

Automorphisms α and β are homotopic when there exists a point-norm continuous automorphism
path from α to β.
-/
def AutomorphismHomotopic (α β : A ≃⋆ₐ[ℂ] A) : Prop :=
  Nonempty (AutomorphismHomotopy α β)

/-- **Automorphism homotopy is an equivalence relation.**

For every nonunital complex C-star algebra A, point-norm homotopy of star-algebra
automorphisms is reflexive, symmetric and transitive.
-/
theorem automorphismHomotopic_equivalence (A : Type uA)
    [NonUnitalCStarAlgebra A] :
    Equivalence (AutomorphismHomotopic :
      (A ≃⋆ₐ[ℂ] A) → (A ≃⋆ₐ[ℂ] A) → Prop) := by
  refine ⟨fun δ ↦ ⟨refl δ⟩, ?_, ?_⟩
  · rintro δ ε ⟨h⟩
    exact ⟨h.symm⟩
  · rintro δ ε ζ ⟨h⟩ ⟨k⟩
    exact ⟨h.trans k⟩

/-!
## Continuous-path algebra from an automorphism homotopy

An automorphism path h yields the homomorphism a ↦ (t ↦ hₜ(a)) into C([0,1],A), and hence a
homotopy of its endpoint star homomorphisms.
-/

/-- **Star homomorphism into the continuous-path algebra.**

A point-norm automorphism homotopy h determines the nonunital complex star homomorphism A →
C([0,1],A), a ↦ (t ↦ hₜ(a)).
-/
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

/-- **Underlying homotopy of star homomorphisms.**

An automorphism homotopy from α to β is a point-norm homotopy between the nonunital star
homomorphisms underlying α and β.
-/
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

/-- **Postcomposition preserves the underlying homotopy.**

If h joins automorphisms α and β of A and δ : A → B is a nonunital complex star homomorphism,
then δ ∘ α and δ ∘ β are homotopic.
-/
theorem toHomotopic_postcomp (h : AutomorphismHomotopy α β)
    {B : Type uB} [NonUnitalCStarAlgebra B]
    (δ : A →⋆ₙₐ[ℂ] B) :
    (δ.comp α.toNonUnitalStarAlgHom).Homotopic
      (δ.comp β.toNonUnitalStarAlgHom) :=
  h.toHomotopic.postcomp δ

/-- **Precomposition preserves the underlying homotopy.**

If h joins automorphisms α and β of A and δ : B → A is a nonunital complex star homomorphism,
then α ∘ δ and β ∘ δ are homotopic.
-/
theorem toHomotopic_precomp (h : AutomorphismHomotopy α β)
    {B : Type uB} [NonUnitalCStarAlgebra B]
    (δ : B →⋆ₙₐ[ℂ] A) :
    (α.toNonUnitalStarAlgHom.comp δ).Homotopic
      (β.toNonUnitalStarAlgHom.comp δ) :=
  h.toHomotopic.precomp δ

/-- **Underlying homotopy after left composition.**

For an automorphism δ of A, left composition of h gives a homotopy between the star
homomorphisms underlying δ ∘ α and δ ∘ β.
-/
theorem compLeft_toHomotopic (h : AutomorphismHomotopy α β)
    (δ : A ≃⋆ₐ[ℂ] A) :
    NonUnitalStarAlgHom.Homotopic
      (δ * α).toNonUnitalStarAlgHom (δ * β).toNonUnitalStarAlgHom :=
  (h.compLeft δ).toHomotopic

/-- **Underlying homotopy after right composition.**

For an automorphism δ of A, right composition of h gives a homotopy between the star
homomorphisms underlying α ∘ δ and β ∘ δ.
-/
theorem compRight_toHomotopic (h : AutomorphismHomotopy α β)
    (δ : A ≃⋆ₐ[ℂ] A) :
    NonUnitalStarAlgHom.Homotopic
      (α * δ).toNonUnitalStarAlgHom (β * δ).toNonUnitalStarAlgHom :=
  (h.compRight δ).toHomotopic

/-- **Underlying homotopy after path reversal.**

Reversing an automorphism homotopy from α to β gives a homotopy of star homomorphisms from β
to α.
-/
theorem toHomotopic_symm (h : AutomorphismHomotopy α β) :
    NonUnitalStarAlgHom.Homotopic
      β.toNonUnitalStarAlgHom α.toNonUnitalStarAlgHom :=
  h.toHomotopic.symm

/-- **Underlying homotopy after concatenation.**

Homotopies from α to β and from β to γ give a point-norm homotopy between the star
homomorphisms underlying α and γ.
-/
theorem toHomotopic_trans (h : AutomorphismHomotopy α β)
    (k : AutomorphismHomotopy β γ) :
    NonUnitalStarAlgHom.Homotopic
      α.toNonUnitalStarAlgHom γ.toNonUnitalStarAlgHom :=
  h.toHomotopic.trans k.toHomotopic

end AutomorphismHomotopy
