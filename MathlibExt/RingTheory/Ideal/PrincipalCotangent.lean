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
# Conormal coordinates for a regular principal equation

Let `B` be a commutative ring, `g : B`, and `I = (g)`. The class `[g]` generates the conormal
module `I/I²` over `B/I`, giving a surjective map `B/I → I/I²`, `c ↦ c • [g]`.

If multiplication by `g` is injective on `B` (`g ∈ nonZeroDivisors B`), this map is a
`B/I`-linear equivalence. It sends `1` to `[g]`.

Reference: Atiyah and Macdonald, *Introduction to Commutative Algebra*, Chapter 2.
-/

@[expose] public section
noncomputable section
universe u
namespace Ideal
variable (B : Type u) [CommRing B] (g : B)
local notation "𝓘" => Ideal.span (Set.singleton g)

/-- For a commutative ring `B` and `g : B`, let `I = Ideal.span {g}`. The principal conormal
generator is `I.toCotangent g`, the class `[g]` of the defining element in `I.Cotangent =
I/I²`. -/
def principalCotangentGenerator : (𝓘).Cotangent :=
  (𝓘).toCotangent ⟨g, Ideal.subset_span (Set.mem_singleton g)⟩

/-- For a commutative ring `B`, `g : B`, and `I = (g)`, this is the `B/I`-linear map `B/I → I/I²`
given by `c ↦ c • [g]`, where `[g] = principalCotangentGenerator B g`. -/
def principalCotangentMap : (B ⧸ 𝓘) →ₗ[B ⧸ 𝓘] (𝓘).Cotangent :=
  LinearMap.toSpanSingleton (B ⧸ 𝓘) (𝓘).Cotangent (principalCotangentGenerator B g)

/-- For a commutative ring `B`, `g : B`, `I = (g)`, and `c : B/I`, `principalCotangentMap B g c =
c • principalCotangentGenerator B g`. Its value is scalar multiplication of the equation class
`[g]` by `c`. -/
theorem principalCotangentMap_apply (c : B ⧸ 𝓘) :
    principalCotangentMap B g c = c • principalCotangentGenerator B g := rfl

/-- For a commutative ring `B` and `g,b : B`, let `I = (g)`. Then `principalCotangentMap B g (b
mod I)` is the class of `b*g` in `I/I²`, namely `I.toCotangent (b • g)` with `g` viewed as an
element of `I`. -/
theorem principalCotangentMap_mk (b : B) :
    principalCotangentMap B g (Ideal.Quotient.mk 𝓘 b) =
      (𝓘).toCotangent (b • (⟨g, Ideal.subset_span (Set.mem_singleton g)⟩ : 𝓘)) := by
  change (algebraMap B (B ⧸ 𝓘) b) •
      (𝓘).toCotangent ⟨g, Ideal.subset_span (Set.mem_singleton g)⟩ = _
  exact (IsScalarTower.algebraMap_smul (B ⧸ 𝓘) b _).trans
    ((𝓘).toCotangent.map_smul b _).symm

/-- For every commutative ring `B` and `g : B`, with `I = (g)`, the map `principalCotangentMap B g
: B/I → I/I²` is surjective. Every conormal class is a quotient-ring scalar multiple of `[g]`. -/
theorem principalCotangentMap_surjective : Function.Surjective (principalCotangentMap B g) := by
  intro x
  obtain ⟨a, rfl⟩ := (𝓘).toCotangent_surjective x
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp a.property
  refine ⟨Ideal.Quotient.mk 𝓘 b, (principalCotangentMap_mk B g b).trans ?_⟩
  apply congrArg (𝓘).toCotangent
  apply Subtype.ext
  change b * g = a
  exact (mul_comm b g).trans hb.symm

/-- Let `B` be a commutative ring and `g : B` satisfy `g ∈ nonZeroDivisors B`, so multiplication
by `g` is injective on `B`. For `I = (g)`, the map `principalCotangentMap B g : B/I → I/I²`,
`c ↦ c • [g]`, is injective. -/
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

/-- Let `B` be a commutative ring, `g : B` a non-zero-divisor, and `I = (g)`. Multiplication by
the conormal class `[g]` is the `B/I`-linear equivalence `principalCotangentEquiv B g hg : B/I
≃ₗ[B/I] I/I²`, with `c ↦ c • [g]`. -/
def principalCotangentEquiv (hg : g ∈ nonZeroDivisors B) :
    (B ⧸ 𝓘) ≃ₗ[B ⧸ 𝓘] (𝓘).Cotangent :=
  LinearEquiv.ofBijective (principalCotangentMap B g)
    ⟨principalCotangentMap_injective B g hg, principalCotangentMap_surjective B g⟩

/-- For a commutative ring `B` and a non-zero-divisor `g : B`, let `I = (g)`. The conormal
equivalence satisfies `principalCotangentEquiv B g hg 1 = principalCotangentGenerator B g`, so
the unit of `B/I` maps to the equation class `[g]` in `I/I²`. -/
theorem principalCotangentEquiv_one (hg : g ∈ nonZeroDivisors B) :
    principalCotangentEquiv B g hg 1 = principalCotangentGenerator B g := by
  change (1 : B ⧸ 𝓘) • principalCotangentGenerator B g = _
  exact one_smul _ _

end Ideal
