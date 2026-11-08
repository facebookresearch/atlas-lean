/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Stefan Trandafir
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Moore
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Girth

@[expose] public section

open SimpleGraph

namespace MathlibExtTest.Combinatorics.SimpleGraph.Moore

open MetaMathlibExt

-- Combinatorics 19: Is Moore graph

abbrev K3 : SimpleGraph (Fin 3) := ⊤

def K3tri : K3.Walk (0 : Fin 3) 0 :=
  Walk.cons ((top_adj (0 : Fin 3) 1).mpr (by decide))
    (Walk.cons ((top_adj (1 : Fin 3) 2).mpr (by decide))
      (Walk.cons ((top_adj (2 : Fin 3) 0).mpr (by decide)) Walk.nil))

theorem K3tri_isCycle : K3tri.IsCycle := by
  rw [Walk.isCycle_def]
  refine ⟨?_, ?_, ?_⟩
  · rw [Walk.isTrail_def]
    decide
  · intro h
    have hl := congrArg Walk.length h
    simp [K3tri] at hl
  · decide

theorem K3_girth : K3.girth = 3 := by
  have hle : K3.girth ≤ 3 := by
    have h := girth_le_length K3tri_isCycle
    have hlen : K3tri.length = 3 := rfl
    rwa [hlen] at h
  have hnacyc : ¬ K3.IsAcyclic := fun hac => hac K3tri K3tri_isCycle
  have hge := three_le_girth hnacyc
  omega

example : IsMooreGraph K3 1 := by
  refine ⟨diam_top, ?_⟩
  rw [K3_girth]

end MathlibExtTest.Combinatorics.SimpleGraph.Moore

end
