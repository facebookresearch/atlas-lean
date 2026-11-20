/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FK.PeriodicPlanarGraph

open Set SimpleGraph

namespace StatMech
namespace FK
namespace PeriodicPlanar

open Lattice



private theorem triangular_reachable_axis_le
    (x : Site 2) (j : Fin 2) (a : Int) (n : Nat) :
    triangularGraph.Reachable (Function.update x j a)
      (Function.update x j (a + n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      refine ih.trans (SimpleGraph.Adj.reachable ?_)
      rw [triangularGraph_adj]
      fin_cases j
      · refine ⟨0, Or.inl ?_⟩
        ext k
        fin_cases k <;> simp [triangularStep]
      · refine ⟨1, Or.inl ?_⟩
        ext k
        fin_cases k <;> simp [triangularStep]


private theorem triangular_reachable_axis
    (x : Site 2) (j : Fin 2) (a b : Int) :
    triangularGraph.Reachable (Function.update x j a)
      (Function.update x j b) := by
  rcases le_total a b with hab | hab
  · obtain ⟨n, rfl⟩ := Int.le.dest hab
    exact triangular_reachable_axis_le x j a n
  · obtain ⟨n, rfl⟩ := Int.le.dest hab
    exact (triangular_reachable_axis_le x j b n).symm


theorem triangularGraph_connected : triangularGraph.Connected := by
  rw [SimpleGraph.connected_iff]
  refine ⟨?_, ⟨0⟩⟩
  intro x y
  have h0 : triangularGraph.Reachable x (Function.update x 0 (y 0)) := by
    have h := triangular_reachable_axis x 0 (x 0) (y 0)
    rwa [Function.update_eq_self] at h
  set z := Function.update x 0 (y 0) with hz
  have h1 : triangularGraph.Reachable z (Function.update z 1 (y 1)) := by
    have h := triangular_reachable_axis z 1 (z 1) (y 1)
    rwa [Function.update_eq_self] at h
  have hzy : Function.update z 1 (y 1) = y := by
    funext i
    fin_cases i <;> simp [hz]
  rw [hzy] at h1
  exact h0.trans h1


theorem triangular_adj_sub_mem_box_one
    {x y : Site 2} (hxy : triangularGraph.Adj x y) :
    y - x ∈ box 2 1 := by
  rw [triangularGraph_adj] at hxy
  obtain ⟨i, h | h⟩ := hxy
  · rw [h]
    intro j
    fin_cases i <;> fin_cases j <;> norm_num [triangularStep]
  · have hyx : y - x = -triangularStep i := by
      rw [← h]
      abel
    rw [hyx]
    intro j
    fin_cases i <;> fin_cases j <;> norm_num [triangularStep]



theorem triangular_walk_sub_mem_box
    {x y : Site 2} (w : triangularGraph.Walk x y) :
    y - x ∈ box 2 w.length := by
  induction w with
  | nil =>
      intro j
      simp
  | @cons x y z hxy w ih =>
      have hstep := triangular_adj_sub_mem_box_one hxy
      intro j
      have hsum : z j - x j = (z j - y j) + (y j - x j) := by omega
      simp only [Pi.sub_apply]
      rw [hsum]
      calc
        ((z j - y j) + (y j - x j)).natAbs ≤
            (z j - y j).natAbs + (y j - x j).natAbs :=
          Int.natAbs_add_le _ _
        _ ≤ w.length + 1 := Nat.add_le_add (ih j) (hstep j)
        _ = (Walk.cons hxy w).length := by simp [Nat.add_comm]


theorem triangular_sub_mem_box_dist (x y : Site 2) :
    y - x ∈ box 2 (triangularGraph.dist x y) := by
  obtain ⟨w, hw⟩ := triangularGraph_connected.exists_walk_length_eq_dist x y
  simpa [hw] using triangular_walk_sub_mem_box w


private theorem exists_triangular_axis_walk_le
    (x : Site 2) (j : Fin 2) (a : Int) (n : Nat) :
    ∃ w : triangularGraph.Walk (Function.update x j a)
        (Function.update x j (a + n)), w.length = n := by
  induction n with
  | zero =>
      have hzero : Function.update x j (a + (0 : Nat)) =
          Function.update x j a := by simp
      rw [hzero]
      exact ⟨Walk.nil, rfl⟩
  | succ n ih =>
      obtain ⟨w, hw⟩ := ih
      have hadj : triangularGraph.Adj (Function.update x j (a + n))
          (Function.update x j (a + (n + 1))) := by
        rw [triangularGraph_adj]
        fin_cases j
        · refine ⟨0, Or.inl ?_⟩
          ext k
          fin_cases k <;> simp [triangularStep]
        · refine ⟨1, Or.inl ?_⟩
          ext k
          fin_cases k <;> simp [triangularStep]
      refine ⟨w.concat hadj, ?_⟩
      simp [hw]



private theorem exists_triangular_axis_walk
    (x : Site 2) (j : Fin 2) (a b : Int) :
    ∃ w : triangularGraph.Walk (Function.update x j a)
        (Function.update x j b), w.length = (b - a).natAbs := by
  rcases le_total a b with hab | hab
  · obtain ⟨n, rfl⟩ := Int.le.dest hab
    obtain ⟨w, hw⟩ := exists_triangular_axis_walk_le x j a n
    refine ⟨w, ?_⟩
    simpa using hw
  · obtain ⟨n, rfl⟩ := Int.le.dest hab
    obtain ⟨w, hw⟩ := exists_triangular_axis_walk_le x j b n
    refine ⟨w.reverse, ?_⟩
    simpa using hw


private theorem exists_triangular_axis_walk_from
    (x : Site 2) (j : Fin 2) (b : Int) :
    ∃ w : triangularGraph.Walk x (Function.update x j b),
      w.length = (b - x j).natAbs := by
  have h := exists_triangular_axis_walk x j (x j) b
  have hstart : Function.update x j (x j) = x := Function.update_eq_self _ _
  rw [hstart] at h
  exact h


private theorem exists_triangular_coordinate_walk (x y : Site 2) :
    ∃ w : triangularGraph.Walk x y,
      w.length = (y 0 - x 0).natAbs + (y 1 - x 1).natAbs := by
  obtain ⟨w0, hw0⟩ := exists_triangular_axis_walk_from x 0 (y 0)
  let z := Function.update x 0 (y 0)
  change triangularGraph.Walk x z at w0
  obtain ⟨w1, hw1⟩ := exists_triangular_axis_walk_from z 1 (y 1)
  have hwalk : ∃ w : triangularGraph.Walk x (Function.update z 1 (y 1)),
      w.length = (y 0 - x 0).natAbs + (y 1 - x 1).natAbs := by
    refine ⟨w0.append w1, ?_⟩
    rw [Walk.length_append, hw0, hw1]
    simp [z]
  have hend : Function.update z 1 (y 1) = y := by
    funext i
    fin_cases i <;> simp [z]
  rw [hend] at hwalk
  exact hwalk



theorem triangular_dist_le_coordinate_sum (x y : Site 2) :
    triangularGraph.dist x y ≤
      (y 0 - x 0).natAbs + (y 1 - x 1).natAbs := by
  obtain ⟨w, hw⟩ := exists_triangular_coordinate_walk x y
  exact (SimpleGraph.dist_le w).trans_eq hw



theorem triangular_dist_le_two_mul_of_sub_mem_box
    {x y : Site 2} {n : Nat} (hxy : y - x ∈ box 2 n) :
    triangularGraph.dist x y ≤ 2 * n := by
  have h0 := hxy 0
  have h1 := hxy 1
  simp only [Pi.sub_apply] at h0 h1
  have hdist := triangular_dist_le_coordinate_sum x y
  omega


private def triHexLiftEntry (i : Fin 3) : Fin 3 :=
  ![2, 2, 1] i


private def triHexLiftExit (i : Fin 3) : Fin 3 :=
  ![1, 0, 0] i

private theorem triangularStep_eq_hexagonalStep_sub (i : Fin 3) :
    triangularStep i =
      hexagonalStep (triHexLiftEntry i) -
        hexagonalStep (triHexLiftExit i) := by
  fin_cases i <;> decide



private theorem exists_hexagonal_walk_of_triangular_step
    {x y : Site 2} (i : Fin 3) (h : y - x = triangularStep i) :
    ∃ w : hexagonalGraph.Walk (x, false) (y, false), w.length = 2 := by
  let m := x + hexagonalStep (triHexLiftEntry i)
  have hxm : hexagonalGraph.Adj (x, false) (m, true) := by
    rw [hexagonalGraph_adj]
    exact Or.inl ⟨rfl, rfl, triHexLiftEntry i, by simp [m]⟩
  have hmy : hexagonalGraph.Adj (m, true) (y, false) := by
    rw [hexagonalGraph_adj]
    refine Or.inr ⟨rfl, rfl, triHexLiftExit i, ?_⟩
    calc
      m - y = hexagonalStep (triHexLiftEntry i) - (y - x) := by
        simp only [m]
        abel
      _ = hexagonalStep (triHexLiftExit i) := by
        rw [h, triangularStep_eq_hexagonalStep_sub]
        abel
  exact ⟨Walk.cons hxm (Walk.cons hmy Walk.nil), by simp⟩


private theorem exists_hexagonal_walk_of_triangular_adj
    {x y : Site 2} (hxy : triangularGraph.Adj x y) :
    ∃ w : hexagonalGraph.Walk (x, false) (y, false), w.length = 2 := by
  rw [triangularGraph_adj] at hxy
  obtain ⟨i, h | h⟩ := hxy
  · exact exists_hexagonal_walk_of_triangular_step i h
  · obtain ⟨w, hw⟩ := exists_hexagonal_walk_of_triangular_step i h
    exact ⟨w.reverse, by simpa using hw⟩


private theorem exists_hexagonal_walk_of_triangular_walk
    {x y : Site 2} (w : triangularGraph.Walk x y) :
    ∃ W : hexagonalGraph.Walk (x, false) (y, false),
      W.length = 2 * w.length := by
  induction w with
  | nil => exact ⟨Walk.nil, by simp⟩
  | @cons x y z hxy w ih =>
      obtain ⟨e, he⟩ := exists_hexagonal_walk_of_triangular_adj hxy
      obtain ⟨W, hW⟩ := ih
      refine ⟨e.append W, ?_⟩
      rw [Walk.length_append, he, hW, Walk.length_cons]
      omega


def hexToTriAnchor (u : HexVertex) : Site 2 :=
  if u.2 then u.1 - hexagonalStep 0 else u.1


private theorem exists_hexagonal_walk_to_anchor (u : HexVertex) :
    ∃ w : hexagonalGraph.Walk u (hexToTriAnchor u, false),
      w.length ≤ 1 := by
  rcases u with ⟨x, b⟩
  cases b with
  | false =>
      exact ⟨Walk.nil, by simp [hexToTriAnchor]⟩
  | true =>
      have h : hexagonalGraph.Adj (x, true)
          (hexToTriAnchor (x, true), false) := by
        rw [hexagonalGraph_adj]
        refine Or.inr ⟨rfl, rfl, 0, ?_⟩
        simp [hexToTriAnchor]
      exact ⟨Walk.cons h Walk.nil, by simp⟩


theorem hexagonalGraph_connected : hexagonalGraph.Connected := by
  rw [SimpleGraph.connected_iff]
  refine ⟨?_, ⟨(0, false)⟩⟩
  intro u v
  obtain ⟨wu, _⟩ := exists_hexagonal_walk_to_anchor u
  obtain ⟨wv, _⟩ := exists_hexagonal_walk_to_anchor v
  obtain ⟨wt⟩ := triangularGraph_connected.preconnected
    (hexToTriAnchor u) (hexToTriAnchor v)
  obtain ⟨wh, _⟩ := exists_hexagonal_walk_of_triangular_walk wt
  exact ⟨wu.append (wh.append wv.reverse)⟩



theorem hexagonal_dist_le_two_mul_triangular_anchor_dist_add_two
    (u v : HexVertex) :
    hexagonalGraph.dist u v ≤
      2 * triangularGraph.dist (hexToTriAnchor u) (hexToTriAnchor v) + 2 := by
  obtain ⟨wu, hwu⟩ := exists_hexagonal_walk_to_anchor u
  obtain ⟨wv, hwv⟩ := exists_hexagonal_walk_to_anchor v
  obtain ⟨wt, hwt⟩ := triangularGraph_connected.exists_walk_length_eq_dist
    (hexToTriAnchor u) (hexToTriAnchor v)
  obtain ⟨wh, hwh⟩ := exists_hexagonal_walk_of_triangular_walk wt
  have hlen : (wu.append (wh.append wv.reverse)).length ≤
      2 * triangularGraph.dist (hexToTriAnchor u) (hexToTriAnchor v) + 2 := by
    simp only [Walk.length_append, Walk.length_reverse]
    rw [hwh, hwt]
    omega
  exact (SimpleGraph.dist_le (wu.append (wh.append wv.reverse))).trans hlen


theorem half_hexagonal_dist_le_triangular_anchor_dist_add_one
    (u v : HexVertex) :
    (1 / 2 : Real) * (hexagonalGraph.dist u v : Real) ≤
      (triangularGraph.dist (hexToTriAnchor u) (hexToTriAnchor v) : Real) + 1 := by
  have h := hexagonal_dist_le_two_mul_triangular_anchor_dist_add_two u v
  have h' : (hexagonalGraph.dist u v : Real) ≤
      2 * (triangularGraph.dist (hexToTriAnchor u) (hexToTriAnchor v) : Real) + 2 := by
    exact_mod_cast h
  linarith



theorem hexagonal_dist_le_four_mul_add_two_of_anchor_sub_mem_box
    {u v : HexVertex} {n : Nat}
    (huv : hexToTriAnchor v - hexToTriAnchor u ∈ box 2 n) :
    hexagonalGraph.dist u v ≤ 4 * n + 2 := by
  have htri := triangular_dist_le_two_mul_of_sub_mem_box huv
  have hhex := hexagonal_dist_le_two_mul_triangular_anchor_dist_add_two u v
  omega

end PeriodicPlanar
end FK
end StatMech
