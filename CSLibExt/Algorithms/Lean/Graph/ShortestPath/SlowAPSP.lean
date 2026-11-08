/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.ShortestPath.Extend
public import CSLibExt.Algorithms.Lean.Matrix.Assignments
public import CSLibExt.Algorithms.Lean.Graph.ShortestPath.MatrixPower
public import Mathlib.Analysis.Asymptotics.Theta

import Batteries.Data.Vector.Lemmas
import Cslib.Algorithms.Lean.TimeM
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.Group.Int
import all CSLibExt.Algorithms.Lean.Graph.ShortestPath.FloydWarshall.Internal.Simplify
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Slow all-pairs shortest paths

CLRS, fourth edition, Section 23.1, printed pages 651-652, SLOW-APSP:
copy the supplied identity table, perform n-1 saved min-plus extensions,
initialize every temporary cell to infinity, then copy the completed cells.

The executor is total on arbitrary saved inputs. Bounded-path and all-path
semantics separately require source diagonal/identity hypotheses, and the latter
requires no negative cycle. Each actual copy/fill assignment is charged once;
canonical matrixAccumulate supplies its same-run scalar addition/minimum counts.

The proved Theta statement concerns these three selected event coordinates.
Physical allocation, machine-word/bit costs, predecessor reconstruction and
generic weight refinements remain separate obligations.

Retained source was authored by Codex at Adam's explicit selection, reusing
canonical CSLib TimeM/Vector and the existing matrix accumulator/path predicates.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Matrix

/-- A bound of at least n-1 edges suffices when no negative cycle exists. -/
private theorem edgeBounded_distance {n r : Nat}
    (weight : Matrix (Fin n) (Fin n) (WithTop Int))
    (hr : n - 1 ≤ r) (hNoCycle : FloydWarshall.NoNegativeCycle weight)
    {i j : Fin n} {distance : WithTop Int}
    (hbound : FloydWarshall.IsEdgeBoundedShortestPathWeight weight r i j distance) :
    FloydWarshall.IsStageShortestPathWeight weight n i j distance := by
  constructor
  · intro path hpath _
    obtain ⟨simplified, hsimplified, hnodup, hweight, _⟩ :=
      FloydWarshall.Internal.exists_nodup_weight_le_of_noNegativeCycle
        weight hNoCycle hpath
    have hlength : simplified.length ≤ n := by
      simpa only [Fintype.card_fin] using hnodup.length_le_card
    have hedges : simplified.length - 1 ≤ r :=
      (Nat.sub_le_sub_right hlength 1).trans hr
    exact (hbound.1 simplified hsimplified hedges).trans hweight
  · rcases hbound.2 with htop | ⟨path, hpath, _, hweight⟩
    · exact Or.inl htop
    · right
      refine ⟨path, hpath, ?_, hweight⟩
      intro vertex _
      exact vertex.isLt

end Cslib.Algorithms.Lean.Matrix

namespace Cslib.Algorithms.Lean.Matrix

open Cslib.Algorithms.Lean
open Filter

private abbrev Weight := MinTropical (WithTop Int)
private abbrev Cost := Nat × (Nat × Nat)
private abbrev Table (n : Nat) :=
  _root_.Vector (_root_.Vector Weight n) n

private def asMatrix {n : Nat} (A : Table n) : Matrix (Fin n) (Fin n) Weight :=
  Matrix.of fun i j => (A.get i).get j

@[no_expose] private def injectAccumulator {n : Nat}
    (A B C : Table n) : TimeM Cost (Table n) :=
  let actual := Matrix.matrixAccumulate A B C
  ⟨actual.ret, (0, actual.time)⟩

private theorem injectAccumulator_ret {n : Nat} (A B C : Table n) :
    (injectAccumulator A B C).ret = (Matrix.matrixAccumulate A B C).ret := by
  rfl

private theorem injectAccumulator_time {n : Nat} (A B C : Table n) :
    (injectAccumulator A B C).time =
      (0, (Matrix.matrixAccumulate A B C).time) := by
  rfl

@[no_expose] def phase {n : Nat} (W L : Table n) :
    TimeM Cost (Table n) := do
  let M ← fillCells n
  let completed ← injectAccumulator L W M
  copyCells completed

theorem phase_ret {n : Nat} (W L : Table n) :
    asMatrix (phase W L).ret = asMatrix L * asMatrix W := by
  simp only [phase, TimeM.ret_bind, fillCells_ret, injectAccumulator_ret,
    copyCells_ret]
  have hz : Matrix.of (fun (_i _j : Fin n) => (0 : Weight)) = 0 := rfl
  simpa [asMatrix, Vector.get_eq_getElem, hz] using
    Matrix.matrixAccumulate_ret L W
      (Vector.replicate n (Vector.replicate n 0))

theorem phase_time {n : Nat} (W L : Table n) :
    (phase W L).time = (2 * n ^ 2, (n ^ 3, n ^ 3)) := by
  simp only [phase, TimeM.time_bind, fillCells_ret, fillCells_time,
    injectAccumulator_time, Matrix.matrixAccumulate_time, copyCells_time]
  simp [two_mul]

@[no_expose] def runPhases {n : Nat} (W : Table n) :
    Nat → Table n → TimeM Cost (Table n)
  | 0, L => pure L
  | r + 1, L => do
      let previous ← runPhases W r L
      phase W previous

theorem runPhases_ret {n : Nat} (W : Table n) (r : Nat) (L : Table n) :
    asMatrix (runPhases W r L).ret = asMatrix L * asMatrix W ^ r := by
  induction r with
  | zero => simp [runPhases]
  | succ r ih =>
      simp only [runPhases, TimeM.ret_bind]
      rw [phase_ret, ih]
      simp [Matrix.mul_assoc, pow_succ]

theorem runPhases_time {n : Nat} (W : Table n) (r : Nat) (L : Table n) :
    (runPhases W r L).time =
      (2 * r * n ^ 2, (r * n ^ 3, r * n ^ 3)) := by
  induction r with
  | zero =>
      simp [runPhases]
      rfl
  | succ r ih =>
      simp only [runPhases, TimeM.time_bind, ih, phase_time]
      simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc]

@[expose] public section

/-- Execute CLRS SLOW-APSP with explicit copy/fill assignment charges.
Accumulator vector updates in `matrixAccumulate` are outside these assignment charges. -/
@[no_expose] public def slowAPSP {n : Nat}
    (W L0 : _root_.Vector (_root_.Vector (MinTropical (WithTop Int)) n) n) :
    TimeM (Nat × (Nat × Nat))
      (_root_.Vector (_root_.Vector (MinTropical (WithTop Int)) n) n) := do
  let saved ← copyCells L0
  runPhases W (n - 1) saved

/-- The saved matrix after all phases is `L0 * W^(n-1)`. -/
public theorem slowAPSP_ret {n : Nat}
    (W L0 : _root_.Vector
      (_root_.Vector (MinTropical (WithTop Int)) n) n) :
    Matrix.of (fun i j => ((slowAPSP W L0).ret.get i).get j) =
      Matrix.of (fun i j => (L0.get i).get j) *
        Matrix.of (fun i j => (W.get i).get j) ^ (n - 1) := by
  change asMatrix (slowAPSP W L0).ret =
    asMatrix L0 * asMatrix W ^ (n - 1)
  simp only [slowAPSP, TimeM.ret_bind]
  rw [runPhases_ret, copyCells_ret]

/-- The source identity initialization gives the minimum over at most `n-1` edges. -/
public theorem slowAPSP_edgeBounded {n : Nat}
    (W L0 : _root_.Vector (_root_.Vector (MinTropical (WithTop Int)) n) n)
    (hdiag : ∀ i : Fin n, MinTropical.untrop ((W.get i).get i) = 0)
    (hinit : ∀ i j : Fin n,
      MinTropical.untrop ((L0.get i).get j) = if i = j then 0 else ⊤)
    (i j : Fin n) :
    FloydWarshall.IsEdgeBoundedShortestPathWeight
      (Matrix.of fun x y => MinTropical.untrop ((W.get x).get y))
      (n - 1) i j
      (MinTropical.untrop (((slowAPSP W L0).ret.get i).get j)) := by
  have hid : Matrix.of (fun x y => (L0.get x).get y) =
      (1 : Matrix (Fin n) (Fin n) (MinTropical (WithTop Int))) := by
    ext x y
    apply MinTropical.injective_untrop
    change MinTropical.untrop ((L0.get x).get y) =
      MinTropical.untrop ((1 : Matrix (Fin n) (Fin n) (MinTropical (WithTop Int))) x y)
    rw [hinit]
    by_cases hxy : x = y
    · simp [Matrix.one_apply, hxy]
    · simp [hxy]
  have hpower := matrix_pow_edgeBounded
    (Matrix.of fun x y => (W.get x).get y) hdiag (n - 1) i j
  have hentry := congrArg (fun M => MinTropical.untrop (M i j)) (slowAPSP_ret W L0)
  rw [hid, one_mul] at hentry
  exact hentry.symm ▸ hpower

/-- Without a negative cycle, the same executed table is minimal over all paths. -/
public theorem slowAPSP_distance_spec {n : Nat}
    (W L0 : _root_.Vector (_root_.Vector (MinTropical (WithTop Int)) n) n)
    (hdiag : ∀ i : Fin n, MinTropical.untrop ((W.get i).get i) = 0)
    (hinit : ∀ i j : Fin n,
      MinTropical.untrop ((L0.get i).get j) = if i = j then 0 else ⊤)
    (hNoCycle : FloydWarshall.NoNegativeCycle
      (Matrix.of fun x y => MinTropical.untrop ((W.get x).get y)))
    (i j : Fin n) :
    FloydWarshall.IsStageShortestPathWeight
      (Matrix.of fun x y => MinTropical.untrop ((W.get x).get y))
      n i j
      (MinTropical.untrop (((slowAPSP W L0).ret.get i).get j)) := by
  exact edgeBounded_distance _ le_rfl hNoCycle
    (slowAPSP_edgeBounded W L0 hdiag hinit i j)

/-- Exact copy/fill assignment, scalar-addition, and scalar-minimum counts.
The first coordinate excludes the accumulator vector updates in `matrixAccumulate`. -/
public theorem slowAPSP_time {n : Nat}
    (W L0 : _root_.Vector
      (_root_.Vector (MinTropical (WithTop Int)) n) n) :
    (slowAPSP W L0).time =
      (n ^ 2 + 2 * (n - 1) * n ^ 2,
        ((n - 1) * n ^ 3, (n - 1) * n ^ 3)) := by
  simp [slowAPSP, copyCells_ret, copyCells_time, runPhases_time]

private theorem totalTime_cast {n : Nat} (W L0 : Table n) (hn : 1 ≤ n) :
    ((slowAPSP W L0).time.1 + (slowAPSP W L0).time.2.1 +
        (slowAPSP W L0).time.2.2 : ℝ) =
      2 * (n : ℝ) ^ 4 - (n : ℝ) ^ 2 := by
  simp only [slowAPSP_time]
  push_cast [Nat.cast_sub hn]
  ring

/-- The sum of the three actual executed cost coordinates is `Θ(n^4)`. -/
public theorem slowAPSP_time_isTheta
    (W L0 : (n : Nat) →
      _root_.Vector
        (_root_.Vector (MinTropical (WithTop Int)) n) n) :
    Asymptotics.IsTheta Filter.atTop
      (fun n => ((slowAPSP (W n) (L0 n)).time.1 +
        (slowAPSP (W n) (L0 n)).time.2.1 +
        (slowAPSP (W n) (L0 n)).time.2.2 : ℝ))
      (fun n => (n : ℝ) ^ 4) := by
  constructor
  · apply Asymptotics.IsBigO.of_bound 5
    filter_upwards [Filter.eventually_ge_atTop (2 : Nat)] with n hn
    have hn1 : 1 ≤ n := by omega
    rw [totalTime_cast (W n) (L0 n) hn1]
    have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hsq : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
    have hsqOne : 1 ≤ (n : ℝ) ^ 2 := by nlinarith
    have hquartic : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 4 := by
      nlinarith [mul_nonneg hsq (sub_nonneg.mpr hsqOne)]
    have htotal : 0 ≤ 2 * (n : ℝ) ^ 4 - (n : ℝ) ^ 2 := by
      nlinarith
    simp only [Real.norm_eq_abs, abs_of_nonneg htotal,
      abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) ^ 4)]
    nlinarith [hsq, (show 0 ≤ (n : ℝ) ^ 4 by positivity)]
  · apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [Filter.eventually_ge_atTop (2 : Nat)] with n hn
    have hn1 : 1 ≤ n := by omega
    rw [totalTime_cast (W n) (L0 n) hn1]
    have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hsq : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
    have hsqOne : 1 ≤ (n : ℝ) ^ 2 := by nlinarith
    have hquartic : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 4 := by
      nlinarith [mul_nonneg hsq (sub_nonneg.mpr hsqOne)]
    have htotal : 0 ≤ 2 * (n : ℝ) ^ 4 - (n : ℝ) ^ 2 := by
      nlinarith
    simp only [one_mul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) ^ 4),
      abs_of_nonneg htotal]
    nlinarith

end

end Cslib.Algorithms.Lean.Matrix
