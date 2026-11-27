/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.RingTheory.TensorProduct.IsBaseChangeRightExact
public import Mathlib.Algebra.FiveLemma

/-!
# Right-exact tensor-base-change comparison

Let R,S be commutative rings with R→S an algebra map. In a commuting diagram from the base
change of a right-exact R-module row U→V→W→0 to a right-exact S-module row U′→V′→W′→0,
isomorphisms on the first two terms make the third comparison bijective.
-/

@[expose] public section
set_option autoImplicit false

open scoped TensorProduct

namespace LinearMap

variable {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
  {U V W U' V' W' : Type*}
  [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
  [AddCommGroup U'] [AddCommGroup V'] [AddCommGroup W']
  [Module R U] [Module R V] [Module R W]
  [Module S U'] [Module S V'] [Module S W']

/-- **Bijectivity of the third map in a right-exact base-change diagram.**

Let R,S be commutative rings with R→S, exact rows U→ᵃV→ᑫW→0 and U′→ᵃ′V′→ᑫ′W′→0, and both q,q′
surjective. Suppose eU:S⊗_RU≃U′, eV:S⊗_RV≃V′ and v:S⊗_RW→W′ satisfy eV∘(id⊗a)=a′∘eU and
v∘(id⊗q)=q′∘eV. Then v is bijective.
-/
theorem baseChange_rightExact_bijective
    (a : U →ₗ[R] V) (q : V →ₗ[R] W) (a' : U' →ₗ[S] V') (q' : V' →ₗ[S] W')
    (v : S ⊗[R] W →ₗ[S] W') (eU : S ⊗[R] U ≃ₗ[S] U') (eV : S ⊗[R] V ≃ₗ[S] V')
    (h₁ : eV.toLinearMap.comp (a.baseChange S) = a'.comp eU.toLinearMap)
    (h₂ : v.comp (q.baseChange S) = q'.comp eV.toLinearMap)
    (hA : Function.Exact a q) (hq : Function.Surjective q)
    (hB : Function.Exact a' q') (hq' : Function.Surjective q') : Function.Bijective v := by
  have hTensor : Function.Exact (a.baseChange S) (q.baseChange S) := by
    simpa only [LinearMap.baseChange_eq_lTensor] using _root_.lTensor_exact S hA hq
  exact LinearMap.bijective_of_surjective_of_bijective_of_right_exact
    (a.baseChange S) (q.baseChange S) a' q' eU.toLinearMap eV.toLinearMap v
    h₁.symm h₂.symm hTensor hB eU.surjective eV.bijective
    (q.baseChange_surjective S hq) hq'

end LinearMap
