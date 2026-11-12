/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






























































































import Mathlib
import Code.Walls.jc4_firstreturnK
import Code.Walls.jc4_tailnotprobed
import Code.Lattice.DartOrbit
import Code.Lattice.JordanSingleCycle

open SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice






















theorem jc5_firstReturn_isLeastFree (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i) :
    1 ≤ jc4_firstReturnK K a r hex ∧
      jc4_FootprintFree K a r (jc4_firstReturnK K a r hex) ∧
      (∀ k, 1 ≤ k → jc4_FootprintFree K a r k → jc4_firstReturnK K a r hex ≤ k) :=
  ⟨jc4_firstReturnK_pos K a r hex, jc4_firstReturnK_free K a r hex,
    fun k hk1 hkf => jc4_firstReturnK_le_of_witness K a r hex k hk1 hkf⟩













theorem jc5_firstReturn_touching_lt (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i)
    (ha0 : ¬ jc4_FootprintFree K a r 0)
    (k : ℕ) (hk : k < jc4_firstReturnK K a r hex) :
    ¬ jc4_FootprintFree K a r k :=
  (jc4_firstReturnK_maximalInitialBlock K a r hex ha0).2.2 k hk


























theorem jc5_firstReturn (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i)
    (ha0 : ¬ jc4_FootprintFree K a r 0) :
    (1 ≤ jc4_firstReturnK K a r hex ∧
        jc4_FootprintFree K a r (jc4_firstReturnK K a r hex) ∧
        (∀ k, 1 ≤ k → jc4_FootprintFree K a r k → jc4_firstReturnK K a r hex ≤ k)) ∧
      (∀ k, k < jc4_firstReturnK K a r hex → ¬ jc4_FootprintFree K a r k) :=
  ⟨jc5_firstReturn_isLeastFree K a r hex,
    (jc4_firstReturnK_maximalInitialBlock K a r hex ha0).2.2⟩
















theorem jc5_firstReturn_within_cycle (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i)
    (ha0 : jc4_FootprintFree K a r 0) :
    jc4_firstReturnK K a r hex ≤ dartOrbitPeriod K a :=
  jc4_firstReturnK_le_period_of_free K hK a r hex ha0








theorem jc5_firstReturn_unique (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i)
    (n : ℕ) (hn1 : 1 ≤ n) (hnfree : jc4_FootprintFree K a r n)
    (hnleast : ∀ k, 1 ≤ k → jc4_FootprintFree K a r k → n ≤ k) :
    n = jc4_firstReturnK K a r hex := by
  obtain ⟨hm1, hmfree, hmleast⟩ := jc5_firstReturn_isLeastFree K a r hex
  exact le_antisymm (hnleast _ hm1 hmfree) (hmleast _ hn1 hnfree)



























theorem jc5_firstReturn_of_witness (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    (j : ℕ) (hj : jc4_FootprintFree K a r j)
    (ha0 : ¬ jc4_FootprintFree K a r 0) :
    ∃ m : ℕ,
      (1 ≤ m ∧ jc4_FootprintFree K a r m ∧
        (∀ k, 1 ≤ k → jc4_FootprintFree K a r k → m ≤ k)) ∧
      (∀ k, k < m → ¬ jc4_FootprintFree K a r k) := by
  have hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i :=
    jc4_firstReturn_exists_of_some_free K hK a r j hj
  exact ⟨jc4_firstReturnK K a r hex, jc5_firstReturn K a r hex ha0⟩











theorem jc5_firstReturn_isLeastFree_of_witness (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    (j : ℕ) (hj : jc4_FootprintFree K a r j) :
    ∃ (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i),
      1 ≤ jc4_firstReturnK K a r hex ∧
        jc4_FootprintFree K a r (jc4_firstReturnK K a r hex) ∧
        (∀ k, 1 ≤ k → jc4_FootprintFree K a r k → jc4_firstReturnK K a r hex ≤ k) :=
  ⟨jc4_firstReturn_exists_of_some_free K hK a r j hj,
    jc5_firstReturn_isLeastFree K a r _⟩





theorem jc5_firstReturn_nonvacuous (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    (j : ℕ) (hj : jc4_FootprintFree K a r j)
    (ha0 : ¬ jc4_FootprintFree K a r 0) :
    ∃ m : ℕ, 1 ≤ m ∧ jc4_FootprintFree K a r m ∧
      (∀ k, k < m → ¬ jc4_FootprintFree K a r k) := by
  obtain ⟨m, ⟨hm1, hmfree, _⟩, hmblock⟩ := jc5_firstReturn_of_witness K hK a r j hj ha0
  exact ⟨m, hm1, hmfree, hmblock⟩

















theorem jc5_firstReturn_tailStart_free (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i) :
    jc3_AvoidsEarFootprint r ((dartNext K)^[jc4_firstReturnK K a r hex + 0] a.1) := by
  simpa using jc4_firstReturnK_free K a r hex













































end Walls

end StatMech
