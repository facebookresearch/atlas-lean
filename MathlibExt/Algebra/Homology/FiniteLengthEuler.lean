/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.RingTheory.Length

/-!
# Euler characteristics from finite-length homology

For a nonnegative chain complex of modules, explicit data consisting of
finite homology lengths below a cutoff and vanishing at and above the cutoff
defines an integer Euler characteristic.  The value is independent of the
chosen valid cutoff and invariant under chain-complex isomorphism.

All finiteness and eventual-vanishing statements remain explicit inputs.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace HomologicalComplex

variable (R : Type u) [CommRing R]

/-- Explicit finite-length and eventual-vanishing data for the homology of a
nonnegative chain complex. -/
structure FiniteLengthHomologyData
    (K : ChainComplex (ModuleCat.{v} R) ℕ) where
  /-- First degree from which homology vanishes. -/
  cutoff : ℕ
  /-- Homology below the cutoff has finite length. -/
  length_ne_top : ∀ j < cutoff,
    Module.length R (K.homology j) ≠ ⊤
  /-- Homology at and above the cutoff vanishes. -/
  vanishes : ∀ j, cutoff ≤ j → IsZero (K.homology j)

/-- Alternating integer sum of the guarded homology lengths. -/
noncomputable def finiteLengthEulerCharacteristic
    {K : ChainComplex (ModuleCat.{v} R) ℕ}
    (h : FiniteLengthHomologyData R K) : ℤ :=
  ∑ j ∈ Finset.range h.cutoff,
    (-1 : ℤ) ^ j * (Module.length R (K.homology j)).toNat

/-- The Euler characteristic is independent of the chosen valid cutoff and
finiteness data. -/
theorem finiteLengthEulerCharacteristic_eq_of_data
    {K : ChainComplex (ModuleCat.{v} R) ℕ}
    (h h' : FiniteLengthHomologyData R K) :
    finiteLengthEulerCharacteristic R h =
      finiteLengthEulerCharacteristic R h' := by
  wlog hle : h.cutoff ≤ h'.cutoff generalizing h h'
  · exact (this h' h (le_of_not_ge hle)).symm
  unfold finiteLengthEulerCharacteristic
  apply Finset.sum_subset (Finset.range_mono hle)
  intro j _ hj
  have hjge : h.cutoff ≤ j := by
    simpa only [Finset.mem_range, not_lt] using hj
  have hzero := h.vanishes j hjge
  have hlength : Module.length R (K.homology j) = 0 := by
    rw [Module.length_eq_zero_iff]
    exact ModuleCat.isZero_iff_subsingleton.mp hzero
  rw [hlength]
  simp

/-- Transport finite-length homology data through an isomorphism of chain
complexes. -/
noncomputable def FiniteLengthHomologyData.mapIso
    {K L : ChainComplex (ModuleCat.{v} R) ℕ}
    (h : FiniteLengthHomologyData R K) (e : K ≅ L) :
    FiniteLengthHomologyData R L where
  cutoff := h.cutoff
  length_ne_top j hj := by
    let eH := HomologicalComplex.homologyMapIso e j
    rw [← eH.toLinearEquiv.length_eq]
    exact h.length_ne_top j hj
  vanishes j hj := by
    let eH := HomologicalComplex.homologyMapIso e j
    exact IsZero.of_iso (h.vanishes j hj) eH.symm

/-- Transport through a chain-complex isomorphism preserves the Euler
characteristic. -/
theorem finiteLengthEulerCharacteristic_mapIso
    {K L : ChainComplex (ModuleCat.{v} R) ℕ}
    (h : FiniteLengthHomologyData R K) (e : K ≅ L) :
    finiteLengthEulerCharacteristic R h =
      finiteLengthEulerCharacteristic R (h.mapIso R e) := by
  unfold finiteLengthEulerCharacteristic
  apply Finset.sum_congr rfl
  intro j hj
  let eH := HomologicalComplex.homologyMapIso e j
  rw [eH.toLinearEquiv.length_eq]

end HomologicalComplex
