/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual central sign section splits the original source determinant kernel. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3CentralSplitProofs

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- A central section multiplies with the actual kernel as a group homomorphism. -/
def y322CentralSectionProductHom {G A : Type*} [Group G] [Group A]
    (f : G →* A) (s : A →* G) (hc : ∀ u x, s u * x = x * s u) : f.ker × A →* G where
  toFun x := x.1.val * s x.2
  map_one' := by simp
  map_mul' x y := by
    change (x.1.val * y.1.val) * s (x.2 * y.2) =
      (x.1.val * s x.2) * (y.1.val * s y.2)
    rw [map_mul]
    calc
      _ = x.1.val * (y.1.val * s x.2) * s y.2 := by simp only [mul_assoc]
      _ = x.1.val * (s x.2 * y.1.val) * s y.2 := by rw [hc]
      _ = _ := by simp only [mul_assoc]

/-- The original homomorphism recovers the second component of a central section product. -/
theorem y322CentralSectionProductHom_projection {G A : Type*} [Group G] [Group A]
    (f : G →* A) (s : A →* G) (hc : ∀ u x, s u * x = x * s u)
    (hs : ∀ u, f (s u) = u) (x : f.ker × A) :
    f (y322CentralSectionProductHom f s hc x) = x.2 := by
  change f (x.1.val * s x.2) = x.2
  rw [map_mul, hs, x.1.property, one_mul]

/-- A genuine right-inverse section makes its central kernel product map injective. -/
theorem y322CentralSectionProductHom_injective {G A : Type*} [Group G] [Group A]
    (f : G →* A) (s : A →* G) (hc : ∀ u x, s u * x = x * s u)
    (hs : ∀ u, f (s u) = u) : Function.Injective (y322CentralSectionProductHom f s hc) := by
  intro x y hxy
  have hp := congrArg f hxy
  rw [y322CentralSectionProductHom_projection f s hc hs,
    y322CentralSectionProductHom_projection f s hc hs] at hp
  apply Prod.ext
  · apply Subtype.ext
    change x.1.val * s x.2 = y.1.val * s y.2 at hxy
    rw [hp] at hxy
    exact mul_right_cancel hxy
  · exact hp

/-- Every group element has an explicit kernel component relative to a right-inverse section. -/
theorem y322CentralSectionProductHom_surjective {G A : Type*} [Group G] [Group A]
    (f : G →* A) (s : A →* G) (hc : ∀ u x, s u * x = x * s u)
    (hs : ∀ u, f (s u) = u) : Function.Surjective (y322CentralSectionProductHom f s hc) := by
  intro x
  have hk : x * (s (f x))⁻¹ ∈ f.ker := by
    change f (x * (s (f x))⁻¹) = 1
    rw [map_mul, map_inv, hs, mul_inv_cancel]
  refine ⟨(⟨x * (s (f x))⁻¹, hk⟩, f x), ?_⟩
  change (x * (s (f x))⁻¹) * s (f x) = x
  simp only [mul_assoc, inv_mul_cancel, mul_one]

/-- A genuine central section identifies a group with its actual kernel product. -/
noncomputable def y322CentralSectionProductEquiv {G A : Type*} [Group G] [Group A]
    (f : G →* A) (s : A →* G) (hc : ∀ u x, s u * x = x * s u)
    (hs : ∀ u, f (s u) = u) : f.ker × A ≃* G :=
  MulEquiv.ofBijective (y322CentralSectionProductHom f s hc)
    ⟨y322CentralSectionProductHom_injective f s hc hs,
      y322CentralSectionProductHom_surjective f s hc hs⟩

/-- Faithful actual matrices identify the source as its determinant kernel times the sign group. -/
noncomputable def y322SignProductEquivOfInjective
    (hi : Function.Injective y322Orthogonal3Hom) :
    y322Orthogonal3Sign.ker × (ZMod 3)ˣ ≃* Y322Presentation :=
  y322CentralSectionProductEquiv y322Orthogonal3Sign y322SignSection
    (y322SignSection_commute_of_injective hi) y322SignSection_right_inverse

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
