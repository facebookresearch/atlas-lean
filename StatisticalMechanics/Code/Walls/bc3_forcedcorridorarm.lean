/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











































































import Mathlib
import Code.Walls.bc2_core
import Code.Walls.bc2_forcemono
import Code.Walls.bc2_forcedpathconn
import Code.Percolation.HrouteDisjointPaths
import Code.Percolation.HrouteHighDim

open Set
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths

namespace StatMech

namespace Walls

variable {d : ℕ}



















theorem bc3_corridorArm_chain (j : Fin d) (L : ℕ) (G : Finset (Sym2 (Site d)))
    (hsub : hrHD_corridorEdges j (L + 1) ⊆ G) :
    Relation.ReflTransGen (CorridorStep G) (hrHD_rayPt j 1) (hrHD_rayPt j ((L : ℤ) + 1)) :=
  bc2_corridorChain_in_union j L G hsub


















theorem bc3_corridorArm_infinite (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L : ℕ)
    (G : Finset (Sym2 (Site d)))
    (hinf : (cluster d (removeSite 0 ω) (hrHD_rayPt j ((L : ℤ) + 1))).Infinite) :
    (cluster d (removeSite 0 (forceOpenFinset G ω)) (hrHD_rayPt j ((L : ℤ) + 1))).Infinite :=
  bc2_clusterInfinite_force_mono_origin ω G hinf


















def bc3_ForcedCorridorArm (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L : ℕ)
    (G : Finset (Sym2 (Site d))) : Prop :=
  Relation.ReflTransGen (CorridorStep G) (hrHD_rayPt j 1) (hrHD_rayPt j ((L : ℤ) + 1)) ∧
    (cluster d (removeSite 0 (forceOpenFinset G ω)) (hrHD_rayPt j ((L : ℤ) + 1))).Infinite
















theorem bc3_forcedCorridorArm (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L : ℕ)
    (G : Finset (Sym2 (Site d))) (hsub : hrHD_corridorEdges j (L + 1) ⊆ G)
    (hinf : (cluster d (removeSite 0 ω) (hrHD_rayPt j ((L : ℤ) + 1))).Infinite) :
    bc3_ForcedCorridorArm ω j L G :=
  ⟨bc3_corridorArm_chain j L G hsub, bc3_corridorArm_infinite ω j L G hinf⟩



















theorem bc3_three_corridorArms (ω : ConfigSpace (Sym2 (Site d)))
    (j₁ j₂ j₃ : Fin d) (L₁ L₂ L₃ : ℕ)
    (hi1 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₁ ((L₁ : ℤ) + 1))).Infinite)
    (hi2 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₂ ((L₂ : ℤ) + 1))).Infinite)
    (hi3 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₃ ((L₃ : ℤ) + 1))).Infinite) :
    bc3_ForcedCorridorArm ω j₁ L₁
        (hrHD_corridorEdges j₁ (L₁ + 1) ∪ hrHD_corridorEdges j₂ (L₂ + 1) ∪
          hrHD_corridorEdges j₃ (L₃ + 1)) ∧
      bc3_ForcedCorridorArm ω j₂ L₂
        (hrHD_corridorEdges j₁ (L₁ + 1) ∪ hrHD_corridorEdges j₂ (L₂ + 1) ∪
          hrHD_corridorEdges j₃ (L₃ + 1)) ∧
      bc3_ForcedCorridorArm ω j₃ L₃
        (hrHD_corridorEdges j₁ (L₁ + 1) ∪ hrHD_corridorEdges j₂ (L₂ + 1) ∪
          hrHD_corridorEdges j₃ (L₃ + 1)) := by
  set G : Finset (Sym2 (Site d)) :=
    hrHD_corridorEdges j₁ (L₁ + 1) ∪ hrHD_corridorEdges j₂ (L₂ + 1) ∪
      hrHD_corridorEdges j₃ (L₃ + 1) with hGdef
  have hs1 : hrHD_corridorEdges j₁ (L₁ + 1) ⊆ G := by
    rw [hGdef]; exact (Finset.subset_union_left).trans Finset.subset_union_left
  have hs2 : hrHD_corridorEdges j₂ (L₂ + 1) ⊆ G := by
    rw [hGdef]; exact (Finset.subset_union_right).trans Finset.subset_union_left
  have hs3 : hrHD_corridorEdges j₃ (L₃ + 1) ⊆ G := by rw [hGdef]; exact Finset.subset_union_right
  exact ⟨bc3_forcedCorridorArm ω j₁ L₁ G hs1 hi1,
    bc3_forcedCorridorArm ω j₂ L₂ G hs2 hi2,
    bc3_forcedCorridorArm ω j₃ L₃ G hs3 hi3⟩













theorem bc3_corridorArm_self (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L : ℕ)
    (hinf : (cluster d (removeSite 0 ω) (hrHD_rayPt j ((L : ℤ) + 1))).Infinite) :
    bc3_ForcedCorridorArm ω j L (hrHD_corridorEdges j (L + 1)) :=
  bc3_forcedCorridorArm ω j L (hrHD_corridorEdges j (L + 1)) (Finset.Subset.refl _) hinf




theorem bc3_forcedCorridorArm_ne (j : Fin d) (L : ℕ) (hL : 1 ≤ L) :
    (hrHD_rayPt j ((L : ℤ) + 1) : Site d) ≠ hrHD_rayPt j 1 :=
  bc2_farEnd_ne_mouth j L hL

end Walls

end StatMech
