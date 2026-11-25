/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.RingHom.IterateTelescoping

/-! # Consumers for the twisted telescoping formula -/

namespace RingHomIterateTelescopingTest

/-- The exact source statement, with no added hypothesis. -/
public theorem exactSource (R : Type*) [CommRing R] (s : R →+* R) (ℓ : ℕ)
    (hs : ∀ r : R, (⇑s)^[ℓ] r = r) (x lam u : R) (h : s x = lam * x + u) :
    (1 - ∏ i ∈ Finset.range ℓ, (⇑s)^[i] lam) * x =
      ∑ j ∈ Finset.range ℓ, (∏ i ∈ Finset.Ico (j + 1) ℓ, (⇑s)^[i] lam) * (⇑s)^[j] u :=
  RingHom.one_sub_prod_iterate_mul_eq_sum_prod_iterate_mul_iterate_of_apply_eq_mul_add
    R s ℓ hs x lam u h

/-- Boundary at `ℓ = 0`: both sides vanish for any `x`. -/
public example (R : Type*) [CommRing R] (s : R →+* R) (x lam u : R)
    (_h : s x = lam * x + u) :
    (1 - ∏ i ∈ Finset.range 0, (⇑s)^[i] lam) * x =
      ∑ j ∈ Finset.range 0, (∏ i ∈ Finset.Ico (j + 1) 0, (⇑s)^[i] lam) * (⇑s)^[j] u := by
  simp

/-- With `s = id` and `ℓ = 1` the formula reduces to `(1 - lam) * x = u`. -/
public example (R : Type*) [CommRing R] (x lam u : R) (h : x = lam * x + u) :
    (1 - lam) * x = u := by
  have := RingHom.one_sub_prod_iterate_mul_eq_sum_prod_iterate_mul_iterate_of_apply_eq_mul_add
    R (RingHom.id R) 1 (fun r => by simp) x lam u (by simpa using h)
  simpa using this

end RingHomIterateTelescopingTest
