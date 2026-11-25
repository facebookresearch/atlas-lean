/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.RingTheory.Length

/-!
# Finite-length Euler characteristics of Tor

This file packages explicit data asserting that the Tor modules of two
modules have finite length below a chosen cutoff and vanish from that cutoff
onward.  Their Euler characteristic is the finite alternating integer sum of
the guarded natural-number lengths.

The value is independent of the chosen valid cutoff.  All finiteness and
eventual-vanishing information remains explicit input data; no such facts are
inferred from properties of the ring or modules.

## Main declarations

* `CategoryTheory.FiniteTorData`
* `CategoryTheory.torEulerCharacteristic`
* `CategoryTheory.torEulerCharacteristic_eq_of_data`
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory.Limits

universe u

namespace CategoryTheory

variable (R : Type u) [CommRing R]

/-- Explicit finite-length and eventual-vanishing data for the Tor modules
of `M` and `N`.  The cutoff is allowed to be zero. -/
structure FiniteTorData (M N : ModuleCat.{u} R) where
  /-- The first degree from which all Tor modules vanish. -/
  cutoff : ℕ
  /-- Every Tor module strictly below the cutoff has finite length. -/
  length_ne_top : ∀ j < cutoff,
    Module.length R (((Tor (ModuleCat.{u} R) j).obj M).obj N) ≠ ⊤
  /-- Every Tor module at or above the cutoff is zero. -/
  vanishes : ∀ j, cutoff ≤ j →
    IsZero (((Tor (ModuleCat.{u} R) j).obj M).obj N)

/-- The alternating integer sum of Tor lengths below the supplied cutoff. -/
noncomputable def torEulerCharacteristic
    {M N : ModuleCat.{u} R} (h : FiniteTorData R M N) : ℤ :=
  ∑ j ∈ Finset.range h.cutoff,
    (-1 : ℤ) ^ j *
      (Module.length R (((Tor (ModuleCat.{u} R) j).obj M).obj N)).toNat

/-- Any two explicit finite-length/eventual-vanishing data values for the
same pair of modules give the same alternating Tor Euler characteristic. -/
theorem torEulerCharacteristic_eq_of_data
    {M N : ModuleCat.{u} R} (h h' : FiniteTorData R M N) :
    torEulerCharacteristic R h = torEulerCharacteristic R h' := by
  wlog hle : h.cutoff ≤ h'.cutoff generalizing h h'
  · exact (this h' h (le_of_not_ge hle)).symm
  unfold torEulerCharacteristic
  apply Finset.sum_subset (Finset.range_mono hle)
  intro j _ hj
  have hjge : h.cutoff ≤ j := by
    simpa only [Finset.mem_range, not_lt] using hj
  have hzero := h.vanishes j hjge
  have hlength :
      Module.length R (((Tor (ModuleCat.{u} R) j).obj M).obj N) = 0 := by
    rw [Module.length_eq_zero_iff]
    exact ModuleCat.isZero_iff_subsingleton.mp hzero
  rw [hlength]
  simp

end CategoryTheory
