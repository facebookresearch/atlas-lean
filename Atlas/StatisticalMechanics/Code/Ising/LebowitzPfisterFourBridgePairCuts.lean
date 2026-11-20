/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterFourBridgeMiddleRank
import Code.Ising.LebowitzPfisterAgreementMarginalLogSupermodular



open Finset

namespace StatMech.Ising

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]



theorem fourBridgeAgreementMarginal_complementaryPair_sum_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall v, 0 <= hf v)
    {w x y z : V}
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    let M := fourBridgeMarkedSet w x y z
    ghsiAgreementMarginalProb G J hf M {w, x} *
          ghsiAgreementMarginalProb G J hf M {y, z} +
        ghsiAgreementMarginalProb G J hf M {w, y} *
          ghsiAgreementMarginalProb G J hf M {x, z} +
        ghsiAgreementMarginalProb G J hf M {w, z} *
          ghsiAgreementMarginalProb G J hf M {x, y} <=
      3 * ghsiAgreementMarginalProb G J hf M ∅ *
        ghsiAgreementMarginalProb G J hf M M := by
  classical
  dsimp only
  let M := fourBridgeMarkedSet w x y z
  let mu := ghsiAgreementMarginalProb G J hf M
  have hcut (P Q : Finset V) (hP : P ⊆ M) (hQ : Q ⊆ M) :
      mu P * mu Q <= mu (P ∩ Q) * mu (P ∪ Q) :=
    ghsiAgreementMarginalProb_logSupermodular G J hf hJ hhf hP hQ
  have hPwx : ({w, x} : Finset V) ⊆ M := by
    intro v hv
    simp only [mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl <;> simp [M, fourBridgeMarkedSet]
  have hPwy : ({w, y} : Finset V) ⊆ M := by
    intro v hv
    simp only [mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl <;> simp [M, fourBridgeMarkedSet]
  have hPwz : ({w, z} : Finset V) ⊆ M := by
    intro v hv
    simp only [mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl <;> simp [M, fourBridgeMarkedSet]
  have hPxy : ({x, y} : Finset V) ⊆ M := by
    intro v hv
    simp only [mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl <;> simp [M, fourBridgeMarkedSet]
  have hPxz : ({x, z} : Finset V) ⊆ M := by
    intro v hv
    simp only [mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl <;> simp [M, fourBridgeMarkedSet]
  have hPyz : ({y, z} : Finset V) ⊆ M := by
    intro v hv
    simp only [mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl <;> simp [M, fourBridgeMarkedSet]
  have h1 := hcut {w, x} {y, z} hPwx hPyz
  have h2 := hcut {w, y} {x, z} hPwy hPxz
  have h3 := hcut {w, z} {x, y} hPwz hPxy
  have hi1 : ({w, x} : Finset V) ∩ {y, z} = ∅ := by
    ext v
    simp [hwx, hwy, hwz, hxy, hxz, hyz, hwx.symm, hwy.symm,
      hwz.symm, hxy.symm, hxz.symm, hyz.symm]
  have hi2 : ({w, y} : Finset V) ∩ {x, z} = ∅ := by
    ext v
    simp [hwx, hwy, hwz, hxy, hxz, hyz, hwx.symm, hwy.symm,
      hwz.symm, hxy.symm, hxz.symm, hyz.symm]
  have hi3 : ({w, z} : Finset V) ∩ {x, y} = ∅ := by
    ext v
    simp [hwx, hwy, hwz, hxy, hxz, hyz, hwx.symm, hwy.symm,
      hwz.symm, hxy.symm, hxz.symm, hyz.symm]
  have hu1 : ({w, x} : Finset V) ∪ {y, z} = M := by
    ext v
    simp [M, fourBridgeMarkedSet, or_assoc, or_left_comm, or_comm]
  have hu2 : ({w, y} : Finset V) ∪ {x, z} = M := by
    ext v
    simp [M, fourBridgeMarkedSet, or_assoc, or_left_comm, or_comm]
  have hu3 : ({w, z} : Finset V) ∪ {x, y} = M := by
    ext v
    simp [M, fourBridgeMarkedSet, or_assoc, or_left_comm, or_comm]
  rw [hi1, hu1] at h1
  rw [hi2, hu2] at h2
  rw [hi3, hu3] at h3
  dsimp only [mu] at h1 h2 h3 ⊢
  nlinarith



theorem fourBridgeAgreementMarginal_complementaryPair_sum_le_rank
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall v, 0 <= hf v)
    {w x y z : V}
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    let M := fourBridgeMarkedSet w x y z
    let p := fourBridgeRankMass
      (fourBridgeOneCoeff G J hf w x y z)
      (fourBridgeTwoCoeff G J hf w x y z)
      (fourBridgeThreeCoeff G J hf w x y z)
      (fourBridgeFourCoeff G J hf w x y z)
    ghsiAgreementMarginalProb G J hf M {w, x} *
          ghsiAgreementMarginalProb G J hf M {y, z} +
        ghsiAgreementMarginalProb G J hf M {w, y} *
          ghsiAgreementMarginalProb G J hf M {x, z} +
        ghsiAgreementMarginalProb G J hf M {w, z} *
          ghsiAgreementMarginalProb G J hf M {x, y} <=
      3 * p 0 * p 4 := by
  dsimp only
  let M := fourBridgeMarkedSet w x y z
  have h := fourBridgeAgreementMarginal_complementaryPair_sum_le
    G J hf hJ hhf hwx hwy hwz hxy hxz hyz
  have hzero : ghsiAgreementMarginalProb G J hf M ∅ =
      fourBridgeRankMass
        (fourBridgeOneCoeff G J hf w x y z)
        (fourBridgeTwoCoeff G J hf w x y z)
        (fourBridgeThreeCoeff G J hf w x y z)
        (fourBridgeFourCoeff G J hf w x y z) 0 := by
    rw [<- fourBridgeAgreementSpinMass_neg_four_eq_marginal_empty,
      fourBridgeAgreementSpinMass_neg_four_eq_rankMass_zero]
  have hfour : ghsiAgreementMarginalProb G J hf M M =
      fourBridgeRankMass
        (fourBridgeOneCoeff G J hf w x y z)
        (fourBridgeTwoCoeff G J hf w x y z)
        (fourBridgeThreeCoeff G J hf w x y z)
        (fourBridgeFourCoeff G J hf w x y z) 4 := by
    rw [<- fourBridgeAgreementSpinMass_four_eq_marginal_full,
      fourBridgeAgreementSpinMass_four_eq_rankMass_four]
  simpa only [M, hzero, hfour] using h

end

end StatMech.Ising
