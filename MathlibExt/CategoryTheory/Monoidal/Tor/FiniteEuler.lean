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

Let R be a commutative ring and M,N modules in ModuleCat.{u} R. FiniteTorData specifies a
cutoff c, finite R-module length for Tor_j(M,N) when j<c, and vanishing for j≥c. The cutoff
may be zero and is not required to be minimal.

The Tor Euler characteristic is the integer sum Σ_{j<c}(-1)^j length_R(Tor_j(M,N)). Its value
is independent of the chosen valid finite-length and vanishing data. Existence of such data is
an explicit hypothesis.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory.Limits

universe u

namespace CategoryTheory

variable (R : Type u) [CommRing R]

/-- Let R : Type u be a commutative ring and M,N ∈ ModuleCat.{u} R. FiniteTorData consists of a
cutoff c∈ℕ, finite Module.length R of Tor_j(M,N) for every j<c, and IsZero of Tor_j(M,N) for
every j≥c. The data allow c=0 and do not assert its minimality. -/
structure FiniteTorData (M N : ModuleCat.{u} R) where
  /-- For a pair of modules M,N over a commutative ring R, the cutoff in FiniteTorData is a natural
number c such that the supplied vanishing condition applies for every j≥c. It is a chosen
valid threshold, not necessarily the least one. -/
  cutoff : ℕ
  /-- For FiniteTorData of M,N over a commutative ring R with cutoff c, every Tor_j(M,N) for j<c
satisfies Module.length R(Tor_j(M,N))≠⊤. This makes its natural-number length finite before it
is used in the Euler sum. -/
  length_ne_top : ∀ j < cutoff,
    Module.length R (((Tor (ModuleCat.{u} R) j).obj M).obj N) ≠ ⊤
  /-- Let R be a commutative ring and h be FiniteTorData for M,N with cutoff c. The vanishing field
asserts IsZero(Tor_j(M,N)) for every j with c≤j. -/
  vanishes : ∀ j, cutoff ≤ j →
    IsZero (((Tor (ModuleCat.{u} R) j).obj M).obj N)

/-- For a commutative ring R, M,N ∈ ModuleCat.{u} R, and h : FiniteTorData R M N, define
χ_Tor(h)=Σ_{j∈range(h.cutoff)}(-1)^j·(length_R Tor_j(M,N)).toNat in ℤ. Finiteness below the
cutoff makes these guarded natural lengths valid, and an empty cutoff gives the empty sum. -/
noncomputable def torEulerCharacteristic
    {M N : ModuleCat.{u} R} (h : FiniteTorData R M N) : ℤ :=
  ∑ j ∈ Finset.range h.cutoff,
    (-1 : ℤ) ^ j *
      (Module.length R (((Tor (ModuleCat.{u} R) j).obj M).obj N)).toNat

/-- Let R be a commutative ring, M,N ∈ ModuleCat.{u} R, and h,h′ two FiniteTorData values for the
same pair. Then χ_Tor(h)=χ_Tor(h′). Any extra degrees below the larger cutoff have zero Tor by
the other vanishing condition and hence contribute length zero. -/
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
