/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicSquareWiredEuler
import Code.FK.EdgeConfigZ
import Code.FrontierB.BoxGraphPath









open Finset SimpleGraph

namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierB
  StatMech.FrontierD

noncomputable section

private theorem boundaryCliqueGraph_reachable_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (bdry : V -> Prop) [DecidablePred bdry] (x y : V) :
    (boundaryCliqueGraph bdry).Reachable x y <->
      x = y ∨ (bdry x ∧ bdry y) := by
  constructor
  · rintro ⟨p⟩
    induction p with
    | nil => exact Or.inl rfl
    | @cons u v w huv p ih =>
        have huv' := (boundaryCliqueGraph_adj bdry u v).1 huv
        rcases ih with rfl | ⟨hv, hw⟩
        · exact Or.inr ⟨huv'.2.1, huv'.2.2⟩
        · exact Or.inr ⟨huv'.2.1, hw⟩
  · rintro (rfl | ⟨hx, hy⟩)
    · exact SimpleGraph.Reachable.refl _
    · by_cases hxy : x = y
      · subst y
        exact SimpleGraph.Reachable.refl _
      · exact ((boundaryCliqueGraph_adj bdry x y).2
          ⟨hxy, hx, hy⟩).reachable

private noncomputable def boundaryCliqueComponentEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (bdry : V -> Prop) [DecidablePred bdry]
    (v0 : V) (hv0 : bdry v0) :
    Option {x : V // ¬ bdry x} ≃
      (boundaryCliqueGraph bdry).ConnectedComponent := by
  let f : Option {x : V // ¬ bdry x} ->
      (boundaryCliqueGraph bdry).ConnectedComponent
    | none => (boundaryCliqueGraph bdry).connectedComponentMk v0
    | some x => (boundaryCliqueGraph bdry).connectedComponentMk x.1
  apply Equiv.ofBijective f
  constructor
  · intro a b hab
    cases a with
    | none =>
        cases b with
        | none => rfl
        | some y =>
            exfalso
            have hreach := ConnectedComponent.eq.mp hab
            have hclass := (boundaryCliqueGraph_reachable_iff
              bdry v0 y.1).1 hreach
            rcases hclass with h | h
            · exact y.2 (h ▸ hv0)
            · exact y.2 h.2
    | some x =>
        cases b with
        | none =>
            exfalso
            have hreach := ConnectedComponent.eq.mp hab
            have hclass := (boundaryCliqueGraph_reachable_iff
              bdry x.1 v0).1 hreach
            rcases hclass with h | h
            · exact x.2 (h.symm ▸ hv0)
            · exact x.2 h.1
        | some y =>
            have hreach := ConnectedComponent.eq.mp hab
            have hclass := (boundaryCliqueGraph_reachable_iff
              bdry x.1 y.1).1 hreach
            have hxy : x.1 = y.1 := by
              rcases hclass with h | h
              · exact h
              · exact False.elim (x.2 h.1)
            exact congrArg some (Subtype.ext hxy)
  · intro C
    by_cases hC : bdry C.out
    · refine ⟨none, ?_⟩
      rw [← C.out_eq]
      apply ConnectedComponent.sound
      exact (boundaryCliqueGraph_reachable_iff bdry v0 C.out).2
        (Or.inr ⟨hv0, hC⟩)
    · refine ⟨some ⟨C.out, hC⟩, ?_⟩
      exact C.out_eq

private theorem card_boundaryCliqueGraph_components
    {V : Type*} [Fintype V] [DecidableEq V]
    (bdry : V -> Prop) [DecidablePred bdry]
    (v0 : V) (hv0 : bdry v0) :
    Nat.card (boundaryCliqueGraph bdry).ConnectedComponent =
      Fintype.card {x : V // ¬ bdry x} + 1 := by
  rw [← Nat.card_congr (boundaryCliqueComponentEquiv bdry v0 hv0)]
  simp

private noncomputable def fkIsingSquareWiredArcEquivIcc
    (n : Nat) :
    {x : (fkSquareBoxPlanar n).V // fkIsingSquareWiredArc n x} ≃
      {z : Int // z ∈ Finset.Icc (-(n : Int)) (n : Int)} where
  toFun x := ⟨x.1.1 1, by
    rw [Finset.mem_Icc]
    exact fkIsingSquareVertex_coordinate_bounds n x.1 1⟩
  invFun z := ⟨⟨![-(n : Int), z.1], by
    intro i
    fin_cases i
    · simp
    · have hz := z.2
      rw [Finset.mem_Icc] at hz
      have habs : |z.1| ≤ (n : Int) := abs_le.mpr hz
      rw [Int.abs_eq_natAbs] at habs
      exact_mod_cast habs⟩, rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    fin_cases i
    · exact x.2.symm
    · rfl
  right_inv z := by
    apply Subtype.ext
    rfl

theorem fkIsingSquareWiredArc_card (n : Nat) :
    Nat.card
      {x : (fkSquareBoxPlanar n).V // fkIsingSquareWiredArc n x} =
      2 * n + 1 := by
  rw [Nat.card_congr (fkIsingSquareWiredArcEquivIcc n),
    Nat.card_eq_fintype_card, Fintype.card_coe, Int.card_Icc]
  omega

theorem fkIsingSquareWired_empty_clusterCount
    (n : Nat) (hn : 0 < n) :
    numClustersBC (fkSquareBoxPlanar n).G
        (fkIsingSquareWiredDobrushinDomain n hn).wiring
        (FK.edgeSetConfig ∅) =
      (2 * n + 1) ^ 2 - 2 * n := by
  classical
  have hopen : openSub (fkSquareBoxPlanar n).G (FK.edgeSetConfig ∅) = ⊥ := by
    ext x y
    simp [FK.edgeSetConfig]
  unfold FKIsingDobrushinDomain.wiring
  rw [fkIsingSquareWiredDobrushinDomain]
  unfold numClustersBC
  rw [hopen, bot_sup_eq]
  change Nat.card
      (boundaryCliqueGraph (fkIsingSquareWiredArc n)).ConnectedComponent = _
  rw [card_boundaryCliqueGraph_components
    (fkIsingSquareWiredArc n) (fkIsingSquareMarkedA n)
    (fkIsingSquareMarkedA_mem_wiredArc n)]
  have hArc : Fintype.card
      {x : (fkSquareBoxPlanar n).V // fkIsingSquareWiredArc n x} =
        2 * n + 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact fkIsingSquareWiredArc_card n
  have hV : Fintype.card (fkSquareBoxPlanar n).V =
      (2 * n + 1) ^ 2 := by
    change Fintype.card (StatMech.FK.boxVerts 2 n) = _
    exact StatMech.FK.ecz_boxVerts_card 2 n
  rw [Fintype.card_subtype_compl, hArc, hV]
  have hle : 2 * n + 1 ≤ (2 * n + 1) ^ 2 := by nlinarith
  omega

theorem fkIsingSquareWired_full_clusterCount
    (n : Nat) (hn : 0 < n) :
    numClustersBC (fkSquareBoxPlanar n).G
        (fkIsingSquareWiredDobrushinDomain n hn).wiring
        (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset) = 1 := by
  have hopen : openSub (fkSquareBoxPlanar n).G
      (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset) =
        (fkSquareBoxPlanar n).G := by
    ext x y
    simp only [openSub_adj, FK.edgeSetConfig_apply,
      SimpleGraph.mem_edgeFinset]
    tauto
  unfold numClustersBC
  rw [hopen]
  apply card_components_eq_one_of_connected
  apply SimpleGraph.Connected.mono
    (show (fkSquareBoxPlanar n).G ≤
      (fkSquareBoxPlanar n).G ⊔
        (fkIsingSquareWiredDobrushinDomain n hn).wiring from le_sup_left)
  letI : Nonempty (fkSquareBoxPlanar n).V :=
    ⟨⟨fun _ => 0, by intro i; simp⟩⟩
  exact ⟨boxGraph_preconnected 2 n⟩

theorem fkIsingSquareWired_full_openCount
    (n : Nat) :
    openCount (fkSquareBoxPlanar n).G
        (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset) =
      2 * ((2 * n) * (2 * n + 1)) := by
  unfold openCount
  rw [show (fkSquareBoxPlanar n).G.edgeFinset.filter
      (fun f => FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset f = true) =
      (fkSquareBoxPlanar n).G.edgeFinset by
    ext f
    simp only [Finset.mem_filter, FK.edgeSetConfig_apply]
    tauto]
  change (StatMech.FK.boxGraph 2 n).edgeFinset.card = _
  rw [StatMech.FK.EdgeCount.boxGraph_edgeCard 2 n (by omega)]
  ring

theorem fkIsingSquareWired_empty_openCount
    (n : Nat) :
    openCount (fkSquareBoxPlanar n).G (FK.edgeSetConfig ∅) = 0 := by
  unfold openCount
  simp [FK.edgeSetConfig]



theorem fkIsingSquareWiredEulerDefect_empty_formula
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareWiredEulerDefect n hn (FK.edgeSetConfig ∅) =
      2 * ((2 * n + 1) ^ 2 - 2 * n) -
        Nat.card (fkIsingSquareWiredCompletedLoopGraph n hn
          (FK.edgeSetConfig ∅)).ConnectedComponent := by
  unfold fkIsingSquareWiredEulerDefect
  rw [fkIsingSquareWired_empty_clusterCount,
    fkIsingSquareWired_empty_openCount]
  simp only [Nat.cast_zero, add_zero]
  have hle : 2 * n ≤ (2 * n + 1) ^ 2 := by nlinarith
  rw [Nat.cast_sub hle]
  push_cast
  rfl




theorem fkIsingSquareWiredEulerDefect_full_formula
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareWiredEulerDefect n hn
        (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset) =
      2 * ((2 * n + 1) ^ 2 - 2 * n) -
        Nat.card (fkIsingSquareWiredCompletedLoopGraph n hn
          (FK.edgeSetConfig
            (fkSquareBoxPlanar n).G.edgeFinset)).ConnectedComponent := by
  unfold fkIsingSquareWiredEulerDefect
  rw [fkIsingSquareWired_full_clusterCount,
    fkIsingSquareWired_full_openCount]
  push_cast
  ring




theorem fkIsingSquareWiredEulerDefect_empty_full_iff_componentCount
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareWiredEulerDefect n hn
          (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset) =
        fkIsingSquareWiredEulerDefect n hn (FK.edgeSetConfig ∅) ↔
      Nat.card (fkIsingSquareWiredCompletedLoopGraph n hn
          (FK.edgeSetConfig
            (fkSquareBoxPlanar n).G.edgeFinset)).ConnectedComponent =
        Nat.card (fkIsingSquareWiredCompletedLoopGraph n hn
          (FK.edgeSetConfig ∅)).ConnectedComponent := by
  rw [fkIsingSquareWiredEulerDefect_full_formula,
    fkIsingSquareWiredEulerDefect_empty_formula]
  constructor
  · intro h
    have hcast :
        (Nat.card (fkIsingSquareWiredCompletedLoopGraph n hn
            (FK.edgeSetConfig
              (fkSquareBoxPlanar n).G.edgeFinset)).ConnectedComponent : Int) =
          Nat.card (fkIsingSquareWiredCompletedLoopGraph n hn
            (FK.edgeSetConfig ∅)).ConnectedComponent := by
      omega
    exact_mod_cast hcast
  · intro h
    rw [h]

end

end StatMech.Universality
