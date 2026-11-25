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
# Right-exact base-change diagrams in tensor coordinates

The right-exact four lemma applies to tensor-base-change maps, with the
first two comparison equivalences and both commuting squares specified.
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

/-- Two actual tensor comparison equivalences identify the third map in
a commuting right-exact diagram. -/
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
