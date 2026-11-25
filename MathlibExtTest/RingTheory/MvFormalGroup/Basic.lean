/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.MvFormalGroup.Basic

/-!
# Tests for the basic multivariate formal group law API

Base change and `n`-series of the additive formal group law, computed from the definitions.
-/

@[expose] public section

namespace MvFormalGroupBasicTest

open MvPowerSeries MvFormalGroup

variable {g : ℕ} {R S : Type*} [CommRing R] [CommRing S]

/-- Base change of the additive formal group law is the additive formal group law. -/
theorem map_addMv (f : R →+* S) : (addMv g R).map f = addMv g S := by
  apply MvFormalGroup.ext
  funext i
  change MvPowerSeries.map f (X (Sum.inl i) + X (Sum.inr i)) =
    (X (Sum.inl i) + X (Sum.inr i) : MvPowerSeries (Fin g ⊕ Fin g) S)
  rw [map_add, map_X, map_X]

/-- The `n`-series of the additive formal group law is `n • X`. -/
theorem nthSeries_addMv (n : ℕ) (i : Fin g) :
    (addMv g R).nthSeries n i = n • (X i : MvPowerSeries (Fin g) R) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [nthSeries_succ]
    change subst (Sum.elim ((addMv g R).nthSeries n) fun j => X j)
        (X (Sum.inl i) + X (Sum.inr i)) = _
    rw [subst_X_add_X (by
      rintro (j | j)
      exacts [constantCoeff_nthSeries _ n j, constantCoeff_X j])]
    simp only [Sum.elim_inl, Sum.elim_inr, ih, succ_nsmul]

/-- The doubled variable `2 • X` is not the `1`-series of the additive law. -/
example : (addMv 1 ℤ).nthSeries 1 0 ≠ 2 • (X 0 : MvPowerSeries (Fin 1) ℤ) := by
  rw [nthSeries_addMv, one_smul, two_nsmul]
  intro h
  have := congrArg (coeff (Finsupp.single 0 1)) h
  simp [coeff_X] at this

end MvFormalGroupBasicTest
