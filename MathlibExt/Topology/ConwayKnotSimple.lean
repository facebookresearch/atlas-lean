/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/KnotTheory/Piccirillo.lean` (leanprover/lean-eval at commit
38361be884302c7edce1908c4aef8296eb2cb27e), manifest
`manifests/problems/conway_knot_not_smoothly_slice.toml` (revision 1).
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison (benchmark submitter).
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).

The adapted portion is the statement of `conwayKnot_isSimple`, moved from
`WantedExt/Topology/PiccirilloWanted.lean` with its name and docstring intact.
lean-eval ships no `NOTICE` file.
-/
module

public import MathlibExt.Topology.ConwayKnotShared
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.LinearAlgebra.AffineSpace.Ordered
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Simplicity of the Conway knot polyline

The periodic parametrization of the Conway knot is injective on one half-open period.
The proof checks the exact vertex coordinates and separates pairs of half-open edges
by linear projections.
-/

namespace MathlibExt.Topology.PiccirilloWanted.KnotTheory
open MathlibExt.Topology.ConwayKnotShared.KnotTheory
open AffineMap

private abbrev IntPoint := ℤ × ℤ × ℤ

-- The Conway polyline's vertices, with each coordinate multiplied by four.
private def vertices : List IntPoint :=
  [(4, 0, 0),
    -- Pass from strand position 1.
    (8, 0, -4), (8, 4, -5), (4, 4, -7), (4, 0, -8),
    (4, 0, -12), (8, 0, -16), (8, 4, -17), (12, 4, -19),
    (12, 0, -20), (12, 0, -24), (12, 4, -25), (16, 4, -27),
    (16, 0, -28), (16, 0, -32), (16, 0, -36), (12, 0, -40),
    (12, 4, -41), (16, 4, -43), (16, 0, -44), (16, 400, -44),
    (16, 400, 0), (16, 0, 0),
    -- Pass from strand position 4.
    (16, 0, -4), (16, 0, -8), (16, 0, -12), (16, 0, -16),
    (16, 0, -20), (16, 0, -24), (12, 0, -28), (12, 4, -29),
    (8, 4, -31), (8, 0, -32), (12, 0, -36), (12, 4, -37),
    (16, 4, -39), (16, 0, -40), (12, 0, -44), (12, 400, -44),
    (12, 400, 0), (12, 0, 0),
    -- Pass from strand position 3.
    (12, 0, -4), (12, 0, -8), (8, 0, -12), (8, 4, -13),
    (4, 4, -15), (4, 0, -16), (4, 0, -20), (8, 0, -24),
    (8, 0, -28), (12, 0, -32), (12, 4, -33), (8, 4, -35),
    (8, 0, -36), (8, 0, -40), (8, 0, -44), (8, 400, -44),
    (8, 400, 0), (8, 0, 0),
    -- Pass from strand position 2.
    (8, 4, -1), (4, 4, -3), (4, 0, -4), (8, 0, -8),
    (8, 4, -9), (12, 4, -11), (12, 0, -12), (12, 0, -16),
    (8, 0, -20), (8, 4, -21), (4, 4, -23), (4, 0, -24),
    (4, 0, -28), (4, 0, -32), (4, 0, -36), (4, 0, -40),
    (4, 0, -44), (4, 400, -44), (4, 400, 0)]

private noncomputable def toR3 (p : IntPoint) : R3 :=
  BraidClosure.mkR3 ((p.1 : ℝ) / 4) ((p.2.1 : ℝ) / 4) ((p.2.2 : ℝ) / 4)

-- Unfold the four passes of the braid closure before normalizing the coordinates.
set_option maxRecDepth 4096 in
private theorem vertices_eq : conwayKnot.vertices = vertices.map toR3 := by
  norm_num [conwayKnot, braidClosure, conwayBraidWord, BraidClosure.iterate, BraidClosure.onePass,
    BraidClosure.applyWord, BraidClosure.applyCrossing, vertices, toR3]

private def dot (n p : IntPoint) : ℤ :=
  n.1 * p.1 + n.2.1 * p.2.1 + n.2.2 * p.2.2

-- The three coordinate projections suffice except at the join of edges 57 and 58,
-- where the linear functional `y + 4*z` separates the edges.
private def directions : List IntPoint := [(1, 0, 0), (0, 1, 0), (0, 0, 1), (0, 1, 4)]

-- The projected half-open edge from `a` to `b` lies strictly below the one from `c` to `d`.
-- At a common bound, one of the intervals must omit that bound at its final endpoint.
private def before (a b c d : ℤ) : Bool :=
  decide (max a b < min c d ∨ max a b = min c d ∧ (a < b ∨ d < c))

private abbrev Edge := Fin vertices.length

private def finish (i : Edge) : Edge :=
  ⟨(i.val + 1) % vertices.length, Nat.mod_lt _ (by decide)⟩

private def edgeOK (i j : Edge) : Bool :=
  let a := vertices[i.val]
  let b := vertices[(finish i).val]
  let c := vertices[j.val]
  let d := vertices[(finish j).val]
  if i = j then
    directions.any fun n => decide (dot n a ≠ dot n b)
  else
    directions.any fun n =>
      before (dot n a) (dot n b) (dot n c) (dot n d) ||
      before (dot n c) (dot n d) (dot n a) (dot n b)

-- Check the finite table by reduction in the kernel.
set_option maxRecDepth 4096 in
private theorem edges_checked :
    (List.finRange vertices.length).all
        (fun i => (List.finRange vertices.length).all (edgeOK i)) = true := by
  decide +kernel

private theorem edgeOK_eq_true (i j : Edge) : edgeOK i j = true :=
  List.all_eq_true.mp (List.all_eq_true.mp edges_checked i (List.mem_finRange i))
    j (List.mem_finRange j)

private def project (n : IntPoint) (v : R3) : ℝ :=
  4 * ((n.1 : ℝ) * v 0 + (n.2.1 : ℝ) * v 1 + (n.2.2 : ℝ) * v 2)

private theorem project_toR3 (n p : IntPoint) : project n (toR3 p) = (dot n p : ℝ) := by
  simp [project, toR3, BraidClosure.mkR3, dot, PiLp.toLp_apply]
  ring

private theorem project_lineMap (n : IntPoint) (a b : R3) (t : ℝ) :
    project n (lineMap a b t) = lineMap (project n a) (project n b) t := by
  simp only [project, lineMap_apply_module, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

private theorem lineMap_lt_of_before {a b c d : ℤ} {u v : ℝ}
    (hu : u ∈ Set.Ico (0 : ℝ) 1) (hv : v ∈ Set.Ico (0 : ℝ) 1)
    (h : before a b c d = true) :
    lineMap (a : ℝ) (b : ℝ) u < lineMap (c : ℝ) (d : ℝ) v := by
  have upper : lineMap (a : ℝ) (b : ℝ) u ≤ (↑(max a b) : ℝ) := calc
      lineMap (a : ℝ) (b : ℝ) u ≤ lineMap (↑(max a b) : ℝ) (↑(max a b) : ℝ) u :=
        lineMap_mono_endpoints (by exact_mod_cast le_max_left a b)
          (by exact_mod_cast le_max_right a b) hu.1 hu.2.le
      _ = _ := lineMap_same_apply _ _
  have lower : (↑(min c d) : ℝ) ≤ lineMap (c : ℝ) (d : ℝ) v := calc
      (↑(min c d) : ℝ) = lineMap (↑(min c d) : ℝ) (↑(min c d) : ℝ) v :=
        (lineMap_same_apply _ _).symm
      _ ≤ _ := lineMap_mono_endpoints (by exact_mod_cast min_le_left c d)
        (by exact_mod_cast min_le_right c d) hv.1 hv.2.le
  rcases of_decide_eq_true h with hgap | ⟨htouch, hab | hdc⟩
  · exact upper.trans_lt ((Int.cast_lt.mpr hgap).trans_le lower)
  · have hlt := (lineMap_lt_right_iff_lt (E := ℝ) hu.2).mpr (Int.cast_lt.mpr hab)
    rw [max_eq_right hab.le] at htouch
    exact hlt.trans_le ((Int.cast_inj.mpr htouch : (b : ℝ) = ↑(min c d)).le.trans lower)
  · have hlt := (right_lt_lineMap_iff_lt (E := ℝ) hv.2).mpr (Int.cast_lt.mpr hdc)
    rw [min_eq_right hdc.le] at htouch
    exact (upper.trans (Int.cast_inj.mpr htouch : (↑(max a b) : ℝ) = (d : ℝ)).le).trans_lt hlt

private theorem edge_parameters_eq {i j : Edge} {u v : ℝ}
    (hu : u ∈ Set.Ico (0 : ℝ) 1) (hv : v ∈ Set.Ico (0 : ℝ) 1)
    (h : lineMap (toR3 vertices[i.val]) (toR3 vertices[(finish i).val]) u =
      lineMap (toR3 vertices[j.val]) (toR3 vertices[(finish j).val]) v) :
    i = j ∧ u = v := by
  have checked := edgeOK_eq_true i j
  by_cases hij : i = j
  · subst j
    simp only [edgeOK] at checked
    obtain ⟨n, _, hn⟩ := List.any_eq_true.mp checked
    have hne : toR3 vertices[i.val] ≠ toR3 vertices[(finish i).val] := by
      intro he
      have hp := congrArg (project n) he
      simp only [project_toR3, Int.cast_inj] at hp
      exact of_decide_eq_true hn hp
    exact ⟨rfl, lineMap_injective ℝ hne h⟩
  · simp only [edgeOK, ite_eq_right hij] at checked
    obtain ⟨n, _, hn⟩ := List.any_eq_true.mp checked
    have hp := congrArg (project n) h
    simp only [project_lineMap, project_toR3] at hp
    rcases Bool.or_eq_true_iff.mp hn with hbefore | hbefore
    · exact ((lineMap_lt_of_before hu hv hbefore).ne hp).elim
    · exact ((lineMap_lt_of_before hv hu hbefore).ne hp.symm).elim

private theorem plCurve_eq_lineMap {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) (vertices.length : ℝ)) :
    ∃ i : Edge, ∃ u ∈ Set.Ico (0 : ℝ) 1, t = (i.val : ℝ) + u ∧
      plCurve conwayKnot.vertices t =
        lineMap (toR3 vertices[i.val]) (toR3 vertices[(finish i).val]) u := by
  have hn : 0 < (vertices.length : ℝ) := ht.1.trans_lt ht.2
  have hn' : vertices.length ≠ 0 := by exact_mod_cast hn.ne'
  have hquot : Int.floor (t / (vertices.length : ℝ)) = 0 :=
    Int.floor_eq_zero_iff.mpr ⟨div_nonneg ht.1 hn.le, (div_lt_one hn).mpr ht.2⟩
  let k := (Int.floor t).toNat
  have hkcast : (k : ℝ) = (Int.floor t : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (Int.floor_nonneg.mpr ht.1)]
  have hkt : (k : ℝ) ≤ t := hkcast.le.trans (Int.floor_le t)
  have hk : k < vertices.length := by exact_mod_cast hkt.trans_lt ht.2
  refine ⟨⟨k, hk⟩, t - k, ⟨sub_nonneg.mpr hkt, ?_⟩, by simp, ?_⟩
  · rw [sub_lt_iff_lt_add, hkcast, add_comm]
    exact Int.lt_floor_add_one t
  · simp only [vertices_eq, plCurve, List.length_map, dite_eq_right hn', hquot, Int.cast_zero,
      mul_zero, sub_zero, lineMap_apply_module, List.getElem_map, finish, Nat.mod_eq_of_lt hk, k]

/-- **The Conway knot polyline is a simple closed curve.** Let $K$ be the Conway knot $11n34$,
realized as a closed polyline in $\mathbb{R}^3$ (the braid closure of a 4-strand braid word for
it), and let $N$ be its number of vertices. The periodic piecewise-linear parametrization of $K$,
which traverses each edge in unit time, is injective on the interval $[0, N)$.

Equivalently, the vertices of $K$ are distinct, non-adjacent edges are disjoint, and adjacent
edges meet only at their shared vertex.

Source: https://arxiv.org/abs/1808.02923 Via leanprover/lean-eval@38361be, problem
`conway_knot_not_smoothly_slice`. -/
public theorem conwayKnot_isSimple : conwayKnot.IsSimple := by
  intro s t hs ht heq
  rw [vertices_eq, List.length_map] at hs ht
  obtain ⟨i, u, hu, hs, hi⟩ := plCurve_eq_lineMap hs
  obtain ⟨j, v, hv, ht, hj⟩ := plCurve_eq_lineMap ht
  obtain ⟨rfl, rfl⟩ := edge_parameters_eq hu hv (hi.symm.trans (heq.trans hj))
  exact hs.trans ht.symm

end MathlibExt.Topology.PiccirilloWanted.KnotTheory
