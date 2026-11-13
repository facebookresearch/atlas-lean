/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.BeffaraDC.PlanarFKDuality
import Code.FK.InfiniteVolume

open Finset SimpleGraph

namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC

noncomputable section



def fkSquareBoxPlanar (n : Nat) : PlanarZ2Subgraph where
  V := FK.boxVerts 2 n
  finV := inferInstance
  decV := inferInstance
  G := FK.boxGraph 2 n
  emb := Function.Embedding.subtype _
  isSub := by
    intro x y hxy
    exact hxy

@[simp] theorem fkSquareBoxPlanar_graph (n : Nat) :
    (fkSquareBoxPlanar n).G = FK.boxGraph 2 n := rfl

@[simp] theorem fkSquareBoxPlanar_emb (n : Nat) (x : FK.boxVerts 2 n) :
    (fkSquareBoxPlanar n).emb x = (x : Site 2) := rfl


theorem fkSquareBox_fkWeight_duality (n : Nat)
    (omega : ConfigSpace (Sym2 (FK.boxVerts 2 n)))
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    FK.fkWeight (FK.boxGraph 2 n) p q omega *
        q ^ ((FK.boxGraph 2 n).edgeFinset.card + 1) =
      (p / (1 - dualParam p q)) ^ (FK.boxGraph 2 n).edgeFinset.card *
        q ^ Nat.card (FK.boxVerts 2 n) *
          pfdDualWeight (fkSquareBoxPlanar n) (dualParam p q) q
            (FK.openSub (FK.boxGraph 2 n) omega) := by
  exact pfd_fkWeight_duality (fkSquareBoxPlanar n) omega hp hp1 hq


theorem fkSquareBox_fkProb_duality (n : Nat)
    (omega : ConfigSpace (Sym2 (FK.boxVerts 2 n)))
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    FK.fkProb (FK.boxGraph 2 n) p q omega =
      pfdDualProb (fkSquareBoxPlanar n) (dualParam p q) q omega := by
  exact pfd_fkProb_duality (fkSquareBoxPlanar n) omega hp hp1 hq



theorem fkSquareBox_fkProb_selfDual (n : Nat)
    (omega : ConfigSpace (Sym2 (FK.boxVerts 2 n)))
    {q : Real} (hq : 0 < q) :
    FK.fkProb (FK.boxGraph 2 n) (selfDualPoint q) q omega =
      pfdDualProb (fkSquareBoxPlanar n) (selfDualPoint q) q omega := by
  have hp := selfDualPoint_mem_Ioo hq
  simpa [selfDualPoint_is_fixed hq] using
    fkSquareBox_fkProb_duality n omega hp.1 hp.2 hq

end

end StatMech.FrontierD
