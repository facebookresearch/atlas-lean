/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


















































































import Mathlib
import Code.Lattice.DartOrbit
import Code.Lattice.BalancePreservingContraction
import Code.Walls.jc3_earfootprint

open SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice














def jc4_FootprintFree (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    (i : ℕ) : Prop :=
  jc3_AvoidsEarFootprint r ((dartNext K)^[i] a.1)












theorem jc4_iterate_period_eq (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    (dartNext K)^[dartOrbitPeriod K a] a.1 = a.1 := by
  have := dartOrbitPeriod_iterate K a
  have hv := congrArg Subtype.val this
  rwa [dartNextSub_iterate_val] at hv







theorem jc4_firstReturn_exists_of_some_free (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    (j : ℕ) (hj : jc4_FootprintFree K a r j) :
    ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i := by
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · 
    refine ⟨dartOrbitPeriod K a, dartOrbitPeriod_pos K hK a, ?_⟩
    unfold jc4_FootprintFree at hj ⊢
    rw [jc4_iterate_period_eq K a]
    subst hj0
    simpa using hj
  · 
    exact ⟨j, hjpos, hj⟩












noncomputable def jc4_firstReturnK (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2)
    (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i) : ℕ :=
  open Classical in Nat.find hex


theorem jc4_firstReturnK_pos (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2) (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i) :
    1 ≤ jc4_firstReturnK K a r hex := by
  classical
  exact (Nat.find_spec hex).1



theorem jc4_firstReturnK_free (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2) (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i) :
    jc4_FootprintFree K a r (jc4_firstReturnK K a r hex) := by
  classical
  exact (Nat.find_spec hex).2



theorem jc4_firstReturnK_avoidsEarFootprint (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i) :
    jc3_AvoidsEarFootprint r ((dartNext K)^[jc4_firstReturnK K a r hex] a.1) :=
  jc4_firstReturnK_free K a r hex











theorem jc4_firstReturnK_lt_touching (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i)
    (k : ℕ) (hk1 : 1 ≤ k) (hk : k < jc4_firstReturnK K a r hex) :
    ¬ jc4_FootprintFree K a r k := by
  classical
  intro hfree
  exact Nat.find_min hex hk ⟨hk1, hfree⟩
















theorem jc4_firstReturnK_maximalInitialBlock (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i)
    (ha0 : ¬ jc4_FootprintFree K a r 0) :
    1 ≤ jc4_firstReturnK K a r hex ∧
      jc4_FootprintFree K a r (jc4_firstReturnK K a r hex) ∧
      (∀ k, k < jc4_firstReturnK K a r hex → ¬ jc4_FootprintFree K a r k) := by
  refine ⟨jc4_firstReturnK_pos K a r hex, jc4_firstReturnK_free K a r hex, ?_⟩
  intro k hk
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · 
    subst hk0
    exact ha0
  · 
    exact jc4_firstReturnK_lt_touching K a r hex k hkpos hk










theorem jc4_firstReturnK_le_of_witness (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i)
    (j : ℕ) (hj1 : 1 ≤ j) (hj : jc4_FootprintFree K a r j) :
    jc4_firstReturnK K a r hex ≤ j := by
  classical
  exact Nat.find_le ⟨hj1, hj⟩





theorem jc4_firstReturnK_le_period_of_free (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i)
    (ha0 : jc4_FootprintFree K a r 0) :
    jc4_firstReturnK K a r hex ≤ dartOrbitPeriod K a := by
  apply jc4_firstReturnK_le_of_witness K a r hex _ (dartOrbitPeriod_pos K hK a)
  unfold jc4_FootprintFree at ha0 ⊢
  rw [jc4_iterate_period_eq K a]
  simpa using ha0





















theorem jc4_firstReturnK_remains_free_of_initialBlock (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i)
    (hinit : ∀ i, i < dartOrbitPeriod K a → ¬ jc4_FootprintFree K a r i →
      ∀ k, k ≤ i → ¬ jc4_FootprintFree K a r k)
    (i : ℕ) (hmi : jc4_firstReturnK K a r hex ≤ i) (hip : i < dartOrbitPeriod K a) :
    jc4_FootprintFree K a r i := by
  by_contra hfree
  
  
  have := hinit i hip hfree (jc4_firstReturnK K a r hex) hmi
  exact this (jc4_firstReturnK_free K a r hex)



















theorem jc4_firstReturnK_of_witness (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    (j : ℕ) (hj : jc4_FootprintFree K a r j)
    (ha0 : ¬ jc4_FootprintFree K a r 0) :
    ∃ m : ℕ, 1 ≤ m ∧ jc4_FootprintFree K a r m ∧
      (∀ k, k < m → ¬ jc4_FootprintFree K a r k) := by
  have hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i :=
    jc4_firstReturn_exists_of_some_free K hK a r j hj
  obtain ⟨h1, h2, h3⟩ := jc4_firstReturnK_maximalInitialBlock K a r hex ha0
  exact ⟨jc4_firstReturnK K a r hex, h1, h2, h3⟩











theorem jc4_firstReturnK_nonvacuous (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    (j : ℕ) (hj : jc4_FootprintFree K a r j) :
    ∃ (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i), 1 ≤ jc4_firstReturnK K a r hex :=
  ⟨jc4_firstReturn_exists_of_some_free K hK a r j hj,
    jc4_firstReturnK_pos K a r _⟩








































end Walls

end StatMech
