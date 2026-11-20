/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















































import Mathlib
import Code.Universality.HexLattice
import Code.Universality.HexInfraDisplacement

namespace StatMech.Universality

open HexWalk List
open scoped BigOperators Real










theorem hexInfra_headAccum_append (h : ℤ) (s t : List ℤ) :
    hexInfra_headAccum h (s ++ t) = hexInfra_headAccum (hexInfra_headAccum h s) t := by
  induction s generalizing h with
  | nil => simp
  | cons u s ih => rw [List.cons_append, hexInfra_headAccum_cons, hexInfra_headAccum_cons, ih]





theorem hexInfra_stepReSum_append (h : ℤ) (s t : List ℤ) :
    hexInfra_stepReSum h (s ++ t)
      = hexInfra_stepReSum h s + hexInfra_stepReSum (hexInfra_headAccum h s) t := by
  induction s generalizing h with
  | nil => simp
  | cons u s ih =>
    rw [List.cons_append, hexInfra_stepReSum_cons, hexInfra_stepReSum_cons,
      hexInfra_headAccum_cons, ih]
    ring





theorem hexInfra_stepReSum_take_drop (h0 : ℤ) (ts : List ℤ) (cp : ℕ) :
    hexInfra_stepReSum h0 ts
      = hexInfra_stepReSum h0 (ts.take cp)
        + hexInfra_stepReSum (hexInfra_headAccum h0 (ts.take cp)) (ts.drop cp) := by
  conv_lhs => rw [← List.take_append_drop cp ts]
  rw [hexInfra_stepReSum_append]













theorem hexInfra_prefix_reachesWidth (a : ℂ) (h0 : ℤ) (T : ℕ) (ts : List ℤ) (cp : ℕ)
    (hdisp : (T : ℝ)
      ≤ hexInfra_stepReSum h0 (ts.take cp)
        + (HexWalk.halfStep (hexInfra_headAccum h0 (ts.take cp))).re) :
    hexWall3_ReachesWidth a h0 T (ts.take cp) :=
  hexInfra_reachesWidth_of_last_re a h0 T (ts.take cp) hdisp






theorem hexInfra_suffix_displacement_eq (h0 : ℤ) (ts : List ℤ) (cp : ℕ) :
    hexInfra_stepReSum (hexInfra_headAccum h0 (ts.take cp)) (ts.drop cp)
      = hexInfra_stepReSum h0 ts - hexInfra_stepReSum h0 (ts.take cp) := by
  rw [hexInfra_stepReSum_take_drop h0 ts cp]; ring









theorem hexInfra_cut_displacement_witness (h0 : ℤ) :
    hexInfra_stepReSum h0 [(-1 : ℤ), 1]
      = hexInfra_stepReSum h0 ([(-1 : ℤ), 1].take 1)
        + hexInfra_stepReSum (hexInfra_headAccum h0 ([(-1 : ℤ), 1].take 1))
            ([(-1 : ℤ), 1].drop 1) :=
  hexInfra_stepReSum_take_drop h0 [(-1 : ℤ), 1] 1

end StatMech.Universality
