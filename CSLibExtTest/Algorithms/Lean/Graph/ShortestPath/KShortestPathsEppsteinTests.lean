/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.ShortestPath.KShortestPathsEppstein

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.KShortestPathsEppsteinTests

open Cslib.Algorithms.Lean.KShortestPathsEppstein

#check eppDelta
#check DiWalk
#check DiWalk.length
#check DiWalk.sidetracks
#check listSidetrackSum
#check lemma1_delta_nonneg
#check lemma1_delta_tree
#check lemma1_all_nonneg
#check lemma2_telescoping
#check lemma2_sidetrack
#check lemma2_path_length
#check sidetrackSum_eq_listSum
#check lemma3_core
#check lemma3_prefpath_le
#check PPath
#check PPath.weight
#check PPath.sidetrackList
#check IsBFSTrace
#check lemma5_decode
#check lemma5_encode
#check lemma6_weight_mono
#check lemma7_parent_weight
#check thm1_bfs_enumeration
#check thm2_all_dests

-- `δ` unfolds to its defining arithmetic expression.
example (len : Fin 2 → Fin 2 → ℝ) (dist : Fin 2 → ℝ) (u v : Fin 2) :
    eppDelta len dist u v = len u v + dist v - dist u := rfl

-- Lemma 1 applies on a concrete triangle inequality witness.
example (len : Fin 2 → Fin 2 → ℝ) (dist : Fin 2 → ℝ)
    (G : Digraph (Fin 2)) (u v : Fin 2) (hadj : G.Adj u v)
    (htri : dist u ≤ len u v + dist v) :
    0 ≤ eppDelta len dist u v :=
  lemma1_delta_nonneg len dist hadj htri

-- Lemma 2 telescopes on the empty walk.
example (len : Fin 2 → Fin 2 → ℝ) (dist : Fin 2 → ℝ)
    (G : Digraph (Fin 2)) (u : Fin 2) :
    (DiWalk.nil u : DiWalk G u u).length len
      = dist u - dist u + (DiWalk.nil u : DiWalk G u u).deltaSum len dist :=
  lemma2_telescoping len dist (DiWalk.nil u)

-- Lemma 6 applies to a single sidestep extension.
example (len : Fin 2 → Fin 2 → ℝ) (dist : Fin 2 → ℝ)
    {G T : Digraph (Fin 2)} {s a : Fin 2} (q : PPath G T s a) (e : Fin 2 × Fin 2)
    (tw : DiWalk T a e.1) (hadj : G.Adj e.1 e.2) (hside : ¬ T.Adj e.1 e.2)
    (hδ : 0 ≤ eppDelta len dist e.1 e.2) :
    q.weight len dist ≤ (PPath.sidestep e q tw hadj hside).weight len dist :=
  lemma6_weight_mono len dist q e tw hadj hside hδ

end Cslib.Algorithms.Lean.KShortestPathsEppsteinTests
