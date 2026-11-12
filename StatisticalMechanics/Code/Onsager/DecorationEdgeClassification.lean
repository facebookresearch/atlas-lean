/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.DecorationFormalSupport








namespace StatMech.Onsager

open Finset SimpleGraph StatMech.Ising

theorem ons_decGraph_edge_external_or_chain
    (L : ℕ) [Fact (2 < L)] (edge : ons_DecEdge L)
    (hedge : edge ∈ (ons_decGraph L).edgeFinset) :
    (∃ d : ons_Dart L, edge = s(d, ons_dartRev L d)) ∨
      ∃ (site : ZMod L × ZMod L) (i : Fin 3),
        edge = ons_decChainEdge site i := by
  induction edge using Sym2.inductionOn with
  | _ d e =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hedge
      change ons_decAdj L d e at hedge
      rcases hedge with hrev | hint
      · left
        exact ⟨d, congrArg (fun x ↦ s(d, x)) hrev⟩
      · right
        rcases d with ⟨site, i⟩
        rcases e with ⟨site', j⟩
        rcases hint with ⟨hsite, hij⟩
        change site = site' at hsite
        change i.val + 1 = j.val ∨ j.val + 1 = i.val at hij
        subst site'
        fin_cases i
        · fin_cases j
          · norm_num at hij
          · exact ⟨site, 0, rfl⟩
          · norm_num at hij
          · norm_num at hij
        · fin_cases j
          · refine ⟨site, 0, ?_⟩
            exact Sym2.eq_swap
          · norm_num at hij
          · exact ⟨site, 1, rfl⟩
          · norm_num at hij
        · fin_cases j
          · norm_num at hij
          · refine ⟨site, 1, ?_⟩
            exact Sym2.eq_swap
          · norm_num at hij
          · exact ⟨site, 2, rfl⟩
        · fin_cases j
          · norm_num at hij
          · norm_num at hij
          · refine ⟨site, 2, ?_⟩
            exact Sym2.eq_swap
          · norm_num at hij

theorem ons_decGraph_edge_isExternal_or_chain
    (L : ℕ) [Fact (2 < L)] (edge : ons_DecEdge L)
    (hedge : edge ∈ (ons_decGraph L).edgeFinset) :
    ons_decIsExternal edge ∨
      ∃ (site : ZMod L × ZMod L) (i : Fin 3),
        edge = ons_decChainEdge site i := by
  rcases ons_decGraph_edge_external_or_chain L edge hedge with
    ⟨d, hd⟩ | hchain
  · exact Or.inl ⟨d, hd⟩
  · exact Or.inr hchain

end StatMech.Onsager
