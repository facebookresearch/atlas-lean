/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectCutSquareEmbedding










open MeasureTheory SimpleGraph StatMech.Lattice

namespace StatMech.FrontierD

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]


def FKFiniteConnectionEvent (source target : V) :
    Set (ConfigSpace (Sym2 V)) :=
  {omega | (FK.openSub G omega).Reachable source target}

theorem fkFiniteConnectionEvent_isIncreasing (source target : V) :
    IsIncreasing (FKFiniteConnectionEvent G source target) := by
  intro omega omega' hle hreach
  exact hreach.mono (FK.openSub_mono G hle)



theorem fkFiniteConnection_reachable_box
    (N : Nat) (iota : V -> FK.boxVerts 2 N)
    (hadj : FK.ocd_AdjMatch G (FK.boxGraph 2 N) iota)
    (rho : ConfigSpace (Sym2 (FK.boxVerts 2 N))) {x y : V}
    (hreach : (FK.openSub G (FK.ocd_innerRestrict iota rho)).Reachable x y) :
    (FK.openSub (FK.boxGraph 2 N) rho).Reachable (iota x) (iota y) := by
  let f : FK.openSub G (FK.ocd_innerRestrict iota rho) →g
      FK.openSub (FK.boxGraph 2 N) rho :=
    { toFun := iota
      map_rel' := fun {u v} huv => by
        refine ⟨(hadj u v).mp huv.1, ?_⟩
        simpa [FK.ocd_innerRestrict, FK.ocd_innerEdge_mk] using huv.2 }
  exact hreach.map f



theorem fkFiniteConnection_cylinder_subset_boxConnEvent
    (N : Nat) (iota : V -> FK.boxVerts 2 N)
    (hadj : FK.ocd_AdjMatch G (FK.boxGraph 2 N) iota)
    (source target : V) :
    FK.boxRestrict 2 N ⁻¹'
        (FK.ocd_innerRestrict iota ⁻¹'
          FKFiniteConnectionEvent G source target) ⊆
      FK.boxConnEvent 2 N (iota source) (iota target) := by
  intro omega hreach
  exact fkFiniteConnection_reachable_box G N iota hadj
    (FK.boxRestrict 2 N omega) hreach




theorem fkFiniteConnection_freeMass_le_boxConn
    (N : Nat) (iota : V -> FK.boxVerts 2 N)
    (hiota : Function.Injective iota)
    (hadj : FK.ocd_AdjMatch G (FK.boxGraph 2 N) iota)
    (source target : V) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q) :
    (∑ omega,
        (FKFiniteConnectionEvent G source target).indicator
            (fun _ => (1 : Real)) omega *
          FK.fkProb G p q omega) <=
      (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site 2)))).real
          (FK.boxConnEvent 2 N (iota source) (iota target)) := by
  let A := FKFiniteConnectionEvent G source target
  let B := FK.ocd_innerRestrict iota ⁻¹' A
  let C := FK.boxRestrict 2 N ⁻¹' B
  let mu : Measure (ConfigSpace (Sym2 (Site 2))) :=
    FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq)
  have hA : IsIncreasing A :=
    fkFiniteConnectionEvent_isIncreasing G source target
  have hB : IsIncreasing B := by
    intro rho rho' hrho hmem
    apply hA _ hmem
    intro e
    exact hrho _
  have hfinite := FK.ocd_free_inner_le_outer_fkProb
    G (FK.boxGraph 2 N) iota hiota hadj hp hp1 hq hA
  have hinfinite := freeBoxEvent_le_freeInfinite N hp hp1 hq hB
  have hdomain :
      (∑ omega,
          A.indicator (fun _ => (1 : Real)) omega *
            FK.fkProb G p q omega) <= mu.real C := by
    exact hfinite.trans (by simpa [B, C, mu] using hinfinite)
  have hsubset : C ⊆
      FK.boxConnEvent 2 N (iota source) (iota target) := by
    simpa [A, B, C] using
      (fkFiniteConnection_cylinder_subset_boxConnEvent
        G N iota hadj source target)
  exact hdomain.trans (measureReal_mono hsubset)

end

end StatMech.FrontierD
