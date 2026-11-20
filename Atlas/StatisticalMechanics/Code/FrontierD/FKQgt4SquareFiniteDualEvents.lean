/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.FrontierD.FKQgt4SquareFiniteDuality

open Finset SimpleGraph

namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC

noncomputable section



noncomputable def fkSquareBoxFaithfulDualPMF (n : Nat)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    PMF (ConfigSpace (Sym2 (FK.boxVerts 2 n))) :=
  PMF.ofFintype
    (fun omega => ENNReal.ofReal
      (pfdDualProb (fkSquareBoxPlanar n) (dualParam p q) q omega)) <| by
    rw [← ENNReal.ofReal_sum_of_nonneg]
    · rw [show (∑ omega : ConfigSpace (Sym2 (FK.boxVerts 2 n)),
          pfdDualProb (fkSquareBoxPlanar n) (dualParam p q) q omega) = 1 by
          calc
            _ = ∑ omega : ConfigSpace (Sym2 (FK.boxVerts 2 n)),
                FK.fkProb (FK.boxGraph 2 n) p q omega := by
              apply Finset.sum_congr rfl
              intro omega _
              exact (fkSquareBox_fkProb_duality n omega hp hp1 hq).symm
            _ = 1 := FK.fkProb_sum_eq_one (FK.boxGraph 2 n) hp hp1 hq]
      simp
    · intro omega _
      rw [← fkSquareBox_fkProb_duality n omega hp hp1 hq]
      exact FK.fkProb_nonneg (FK.boxGraph 2 n) hp hp1 hq omega

@[simp] theorem fkSquareBoxFaithfulDualPMF_apply (n : Nat)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (omega : ConfigSpace (Sym2 (FK.boxVerts 2 n))) :
    fkSquareBoxFaithfulDualPMF n hp hp1 hq omega =
      ENNReal.ofReal
        (pfdDualProb (fkSquareBoxPlanar n) (dualParam p q) q omega) :=
  PMF.ofFintype_apply _ _



theorem fkSquareBox_fkPMF_eq_faithfulDualPMF (n : Nat)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    FK.fkPMF (FK.boxGraph 2 n) hp hp1 hq =
      fkSquareBoxFaithfulDualPMF n hp hp1 hq := by
  ext omega
  rw [FK.fkPMF_apply, fkSquareBoxFaithfulDualPMF_apply,
    fkSquareBox_fkProb_duality n omega hp hp1 hq]



noncomputable def fkSquareBoxFaithfulDualEventProb (n : Nat)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (A : Set (ConfigSpace (Sym2 (FK.boxVerts 2 n)))) : ENNReal :=
  (fkSquareBoxFaithfulDualPMF n hp hp1 hq).toMeasure A


theorem fkSquareBox_eventProb_duality (n : Nat)
    (A : Set (ConfigSpace (Sym2 (FK.boxVerts 2 n))))
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    (FK.fkPMF (FK.boxGraph 2 n) hp hp1 hq).toMeasure A =
      fkSquareBoxFaithfulDualEventProb n hp hp1 hq A := by
  unfold fkSquareBoxFaithfulDualEventProb
  rw [fkSquareBox_fkPMF_eq_faithfulDualPMF n hp hp1 hq]


theorem fkSquareBox_eventProb_selfDual (n : Nat)
    (A : Set (ConfigSpace (Sym2 (FK.boxVerts 2 n))))
    {q : Real} (hq : 0 < q) :
    (FK.fkPMF (FK.boxGraph 2 n)
      (selfDualPoint_mem_Ioo hq).1 (selfDualPoint_mem_Ioo hq).2 hq).toMeasure A =
      fkSquareBoxFaithfulDualEventProb n
        (selfDualPoint_mem_Ioo hq).1 (selfDualPoint_mem_Ioo hq).2 hq A := by
  exact fkSquareBox_eventProb_duality n A
    (selfDualPoint_mem_Ioo hq).1 (selfDualPoint_mem_Ioo hq).2 hq

end

end StatMech.FrontierD
