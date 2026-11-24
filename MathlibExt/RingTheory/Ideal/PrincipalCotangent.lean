/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Tactic.Ring

/-!
# The conormal generator of a regular principal equation

For a regular equation `g`, the actual quotient-ideal conormal module
`(g)/(g)^2` is the free rank-one module over the actual quotient by `(g)`.
The isomorphism sends one to the class of the original equation.
-/

@[expose] public section
noncomputable section
universe u
namespace Ideal
variable (B : Type u) [CommRing B] (g : B)
local notation "𝓘" => Ideal.span (Set.singleton g)

/-- The class of the original principal equation in its actual conormal module. -/
def principalCotangentGenerator : (𝓘).Cotangent :=
  (𝓘).toCotangent ⟨g, Ideal.subset_span (Set.mem_singleton g)⟩

/-- Multiplication by the original conormal generator over the actual quotient. -/
def principalCotangentMap : (B ⧸ 𝓘) →ₗ[B ⧸ 𝓘] (𝓘).Cotangent :=
  LinearMap.toSpanSingleton (B ⧸ 𝓘) (𝓘).Cotangent (principalCotangentGenerator B g)

/-- The original principal conormal map is scalar multiplication by its
actual defining-equation class. -/
theorem principalCotangentMap_apply (c : B ⧸ 𝓘) :
    principalCotangentMap B g c = c • principalCotangentGenerator B g := rfl

/-- A quotient scalar acts on the equation class by the original product. -/
theorem principalCotangentMap_mk (b : B) :
    principalCotangentMap B g (Ideal.Quotient.mk 𝓘 b) =
      (𝓘).toCotangent (b • (⟨g, Ideal.subset_span (Set.mem_singleton g)⟩ : 𝓘)) := by
  change (algebraMap B (B ⧸ 𝓘) b) •
      (𝓘).toCotangent ⟨g, Ideal.subset_span (Set.mem_singleton g)⟩ = _
  exact (IsScalarTower.algebraMap_smul (B ⧸ 𝓘) b _).trans
    ((𝓘).toCotangent.map_smul b _).symm

/-- The actual equation class generates the conormal module of every
principal ideal, without a regularity or basis hypothesis. -/
theorem principalCotangentMap_surjective : Function.Surjective (principalCotangentMap B g) := by
  intro x
  obtain ⟨a, rfl⟩ := (𝓘).toCotangent_surjective x
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp a.property
  refine ⟨Ideal.Quotient.mk 𝓘 b, (principalCotangentMap_mk B g b).trans ?_⟩
  apply congrArg (𝓘).toCotangent
  apply Subtype.ext
  change b * g = a
  exact (mul_comm b g).trans hb.symm

/-- Regularity of the original equation makes its quotient scalar
coefficient unique in the conormal module. -/
theorem principalCotangentMap_injective (hg : g ∈ nonZeroDivisors B) :
    Function.Injective (principalCotangentMap B g) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hb : b * g ∈ (𝓘) ^ 2 :=
    ((𝓘).toCotangent_eq_zero _).mp ((principalCotangentMap_mk B g b).symm.trans hx)
  have hpow : (𝓘) ^ 2 = Ideal.span (Set.singleton (g ^ 2)) :=
    Ideal.span_singleton_pow g 2
  have hb' : b * g ∈ Ideal.span (Set.singleton (g ^ 2)) := hpow ▸ hb
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hb'
  have hprod : (b - g * c) * g = 0 := by
    calc
      (b - g * c) * g = b * g - g ^ 2 * c := by ring
      _ = 0 := sub_eq_zero.mpr hc
  have hbc : b = g * c := sub_eq_zero.mp
    ((mul_right_mem_nonZeroDivisors_eq_zero_iff hg).mp hprod)
  exact (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.mem_span_singleton.mpr ⟨c, hbc⟩)

/-- The actual conormal module of a regular principal equation is its
actual quotient ring, with one mapped to the original equation class. -/
def principalCotangentEquiv (hg : g ∈ nonZeroDivisors B) :
    (B ⧸ 𝓘) ≃ₗ[B ⧸ 𝓘] (𝓘).Cotangent :=
  LinearEquiv.ofBijective (principalCotangentMap B g)
    ⟨principalCotangentMap_injective B g hg, principalCotangentMap_surjective B g⟩

/-- The principal conormal isomorphism retains the original defining equation. -/
theorem principalCotangentEquiv_one (hg : g ∈ nonZeroDivisors B) :
    principalCotangentEquiv B g hg 1 = principalCotangentGenerator B g := by
  change (1 : B ⧸ 𝓘) • principalCotangentGenerator B g = _
  exact one_smul _ _

end Ideal
