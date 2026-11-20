/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/























































import Mathlib
import Code.Walls.bc6edgedichotomy

open Set
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation

namespace StatMech

namespace Walls

variable {d : ℕ}
















theorem bc7_offBox_rho_edge_agree_iff {N : ℕ} {G : Finset (Sym2 (Site d))}
    {ω : ConfigSpace (Sym2 (Site d))} {e : Sym2 (Site d)}
    (hG : e ∉ G) (hbox : e ∉ boxEdges d N) :
    removeSite 0 (bc6_closeBoxExcept N G ω) e = removeSite 0 ω e := by
  by_cases h0 : (0 : Site d) ∈ e
  · 
    rw [removeSite_apply_of_mem h0, removeSite_apply_of_mem h0]
  · 
    rw [removeSite_apply_of_notMem h0, removeSite_apply_of_notMem h0,
      bc6_closeBoxExcept_of_outside hG hbox]





















theorem bc7_offBox_rho_edge_agree {N : ℕ} {G : Finset (Sym2 (Site d))}
    {ω : ConfigSpace (Sym2 (Site d))} {u v : Site d}
    (hopen : IsOpenEdge d (removeSite 0 (bc6_closeBoxExcept N G ω)) u v)
    (hG : s(u, v) ∉ G) (hbox : s(u, v) ∉ boxEdges d N) :
    IsOpenEdge d (removeSite 0 ω) u v := by
  obtain ⟨hadj, hval⟩ := hopen
  exact ⟨hadj, by rwa [bc7_offBox_rho_edge_agree_iff hG hbox] at hval⟩











theorem bc7_offBox_rho_edge_agree' {N : ℕ} {G : Finset (Sym2 (Site d))}
    {ω : ConfigSpace (Sym2 (Site d))} {u v : Site d}
    (hopen : IsOpenEdge d (removeSite 0 ω) u v)
    (hG : s(u, v) ∉ G) (hbox : s(u, v) ∉ boxEdges d N) :
    IsOpenEdge d (removeSite 0 (bc6_closeBoxExcept N G ω)) u v := by
  obtain ⟨hadj, hval⟩ := hopen
  exact ⟨hadj, by rwa [bc7_offBox_rho_edge_agree_iff hG hbox]⟩











theorem bc7_offBox_rho_edge_agree_and_originFree {N : ℕ} {G : Finset (Sym2 (Site d))}
    {ω : ConfigSpace (Sym2 (Site d))} {u v : Site d}
    (hopen : IsOpenEdge d (removeSite 0 (bc6_closeBoxExcept N G ω)) u v)
    (hG : s(u, v) ∉ G) (hbox : s(u, v) ∉ boxEdges d N) :
    (0 : Site d) ∉ s(u, v) ∧ IsOpenEdge d (removeSite 0 ω) u v :=
  ⟨bc6_origin_notMem ω N G hopen.2, bc7_offBox_rho_edge_agree hopen hG hbox⟩

end Walls

end StatMech
