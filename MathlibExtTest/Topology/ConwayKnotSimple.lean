/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.ConwayKnotSimple
import Mathlib.Tactic.NormNum

namespace ConwayKnotSimpleTest

open MathlibExt.Topology.ConwayKnotShared.KnotTheory
open MathlibExt.Topology.PiccirilloWanted.KnotTheory

example : Set.InjOn (plCurve conwayKnot.vertices)
    (Set.Ico 0 (conwayKnot.vertices.length : ℝ)) := by
  intro s hs t ht h
  exact conwayKnot_isSimple s t hs ht h

-- A point in the interior of the closing edge cannot coincide with the initial vertex.
set_option maxRecDepth 4096 in
example : plCurve conwayKnot.vertices (155 / 2) ≠ plCurve conwayKnot.vertices 0 := by
  have hlen : conwayKnot.vertices.length = 78 := by rfl
  have hlast : (155 / 2 : ℝ) ∈ Set.Ico 0 (conwayKnot.vertices.length : ℝ) := by
    norm_num [hlen]
  have hfirst : (0 : ℝ) ∈ Set.Ico 0 (conwayKnot.vertices.length : ℝ) := by
    norm_num [hlen]
  intro h
  have heq := conwayKnot_isSimple (155 / 2) 0 hlast hfirst h
  norm_num at heq

end ConwayKnotSimpleTest
