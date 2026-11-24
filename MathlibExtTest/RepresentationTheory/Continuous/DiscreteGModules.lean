/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.RepresentationTheory.Continuous.DiscreteGModules
import Mathlib.Topology.Instances.Int

/-!
# Discrete continuous modules and their invariants

The abelian structures are inferred with independent universes. Two concrete
discrete modules over discrete groups distinguish the invariants functor from
both the identity and the zero functor: the trivial `ℤ` has every integer as an
invariant, while the sign module of `ℤˣ` on `ℤ` has none but zero. Degree-zero
derived invariants recover the invariants for a left exact functor, and higher
ones vanish on injectives.
-/

noncomputable section

open CategoryTheory Limits DiscreteGModules
open scoped DiscreteGModules

namespace MathlibExtTest.DiscreteGModules

/-! ## Inferred structure -/

section Instances

variable (G : Type) [Group G] [TopologicalSpace G]

example : Abelian (ContinuousGModule.{0, 0} G) := inferInstance
example : Abelian (ContinuousModule.{0, 0, 0} ℚ G) := inferInstance
example : Abelian (ContinuousModule.{0, 0, 1} ℤ G) := inferInstance
example (G' : Type 1) [Group G'] [TopologicalSpace G'] :
    Abelian (ContinuousModule.{0, 1, 0} ℤ G') := inferInstance
example : Abelian (ContAction (ModuleCat.{0} ℤ) G) := inferInstance
example : (invariantsFunctor.{0, 0} G).Additive := inferInstance
example : ObjectProperty.IsClosedUnderSubobjects
    (Action.IsContinuous (V := ModuleCat.{0} ℤ) (G := G)) := inferInstance
example : ObjectProperty.IsClosedUnderQuotients
    (Action.IsContinuous (V := ModuleCat.{0} ℤ) (G := G)) := inferInstance
example : ObjectProperty.IsClosedUnderFiniteProducts
    (ContAction.IsDiscrete (V := ModuleCat.{0} ℤ) (G := G)) := inferInstance
example : ObjectProperty.ContainsZero
    (ContAction.IsDiscrete (V := ModuleCat.{0} ℤ) (G := G)) := inferInstance

example {Z : Type} [TopologicalSpace Z] (g : Z → Bool) (h : Continuous (Bool.toNat ∘ g)) :
    Continuous g :=
  continuous_of_comp_injective_discrete Bool.toNat
    (fun a b hab => by cases a <;> cases b <;> simp_all) h

end Instances

/-! ## Concrete discrete modules -/

section Concrete

variable (G : Type) [Group G] [TopologicalSpace G] [DiscreteTopology G]

/-- `ℤ` with the trivial action. -/
def trivialModule : ContinuousGModule.{0, 0} G :=
  ⟨⟨Action.trivial G (ModuleCat.of ℤ ℤ), ⟨continuous_of_discreteTopology⟩⟩, ⟨rfl⟩⟩

/-- Every integer is invariant under the trivial action. -/
def trivialInvariant (n : ℤ) : (invariantsFunctor G).obj (trivialModule G) :=
  ⟨n, fun _ => rfl⟩

example : trivialInvariant G 1 ≠ 0 := by
  intro h
  exact one_ne_zero (α := ℤ) (congrArg Subtype.val h)

/-- `ℤ` with the sign action of `ℤˣ`. -/
def signModule : ContinuousGModule.{0, 0} ℤˣ :=
  ⟨⟨(Rep.RepToAction ℤ ℤˣ).obj (Rep.of (Representation.ofDistribMulAction ℤ ℤˣ ℤ)),
    ⟨continuous_of_discreteTopology⟩⟩, ⟨rfl⟩⟩

/-- The sign module has no nonzero invariants. -/
example (x : (invariantsFunctor ℤˣ).obj signModule) : x = 0 := by
  obtain ⟨v, hv⟩ := x
  have key : ∀ w : ℤ, (-1 : ℤ) * w = w → w = 0 := fun w hw => by omega
  exact Subtype.ext (key v (hv (-1)))

end Concrete

/-! ## Derived invariants -/

section Derived

variable (G : Type) [Group G] [TopologicalSpace G] [EnoughInjectives (ContinuousGModule.{0, 0} G)]

example (n : ℕ) : derivedCohomology G n = (invariantsFunctor G).rightDerived n := rfl

example (I : ContinuousGModule.{0, 0} G) [Injective I] (n : ℕ) :
    IsZero ((derivedCohomology G (n + 1)).obj I) :=
  (invariantsFunctor G).isZero_rightDerived_obj_injective_succ n I

example [PreservesFiniteLimits (invariantsFunctor G)] :
    derivedCohomology G 0 ≅ invariantsFunctor G :=
  (invariantsFunctor G).rightDerivedZeroIsoSelf

end Derived

end MathlibExtTest.DiscreteGModules
