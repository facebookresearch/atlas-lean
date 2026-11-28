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
# Bijectivity in a right-exact base-change diagram

Let S be a commutative R-algebra and U→V→W→0, U′→V′→W′→0 right-exact module sequences over R,S.
Suppose the first two vertical comparisons are S-linear equivalences S⊗_R U≅U′ and S⊗_R V≅V′,
and the third is an S-linear map v:S⊗_R W→W′.

If both squares commute, v is bijective. The tensor source row is right exact without requiring
S to be flat. The result retains both specified comparison equivalences, both exactness
hypotheses and both surjective row endpoints.
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

/-- Let R,S be commutative rings with S an R-algebra. Let a:U→V,q:V→W be R-linear and
a′:U′→V′,q′:V′→W′ S-linear, with im(a)=ker(q), im(a′)=ker(q′) and q,q′ surjective. Given
S-linear equivalences e_U:S⊗_R U≅U′, e_V:S⊗_R V≅V′ and v:S⊗_R W→W′, assume e_V∘(S⊗a)=a′∘e_U and
v∘(S⊗q)=q′∘e_V. Then v is bijective. The modules have their declared carrier universes, and no
flatness hypothesis is imposed on S. -/
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
