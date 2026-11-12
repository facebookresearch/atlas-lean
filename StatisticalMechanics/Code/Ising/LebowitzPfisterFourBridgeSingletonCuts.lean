/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterFourBridgePairCuts



open Finset

namespace StatMech.Ising

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem fourBridgeRankMass_zero_eq_marginal_empty
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (w x y z : V) :
    fourBridgeRankMass
        (fourBridgeOneCoeff G J hf w x y z)
        (fourBridgeTwoCoeff G J hf w x y z)
        (fourBridgeThreeCoeff G J hf w x y z)
        (fourBridgeFourCoeff G J hf w x y z) 0 =
      ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z) ∅ := by
  rw [← fourBridgeAgreementSpinMass_neg_four_eq_rankMass_zero,
    fourBridgeAgreementSpinMass_neg_four_eq_marginal_empty]


theorem fourBridgeRankMass_four_eq_marginal_full
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (w x y z : V) :
    fourBridgeRankMass
        (fourBridgeOneCoeff G J hf w x y z)
        (fourBridgeTwoCoeff G J hf w x y z)
        (fourBridgeThreeCoeff G J hf w x y z)
        (fourBridgeFourCoeff G J hf w x y z) 4 =
      ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z)
        (fourBridgeMarkedSet w x y z) := by
  rw [← fourBridgeAgreementSpinMass_four_eq_rankMass_four,
    fourBridgeAgreementSpinMass_four_eq_marginal_full]


theorem ghsiAgreementMarginalProb_le_one
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (M P : Finset V) :
    ghsiAgreementMarginalProb G J hf M P <= 1 := by
  classical
  rw [← ghsiAgreementProb_sum_eq_one G J hf]
  unfold ghsiAgreementMarginalProb
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun q _ _ => ghsiAgreementProb_nonneg G J hf q)



theorem fourBridgeRankMass_one_eq_marginal_singletons
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    {w x y z : V}
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    fourBridgeRankMass
        (fourBridgeOneCoeff G J hf w x y z)
        (fourBridgeTwoCoeff G J hf w x y z)
        (fourBridgeThreeCoeff G J hf w x y z)
        (fourBridgeFourCoeff G J hf w x y z) 1 =
      ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z) {w} +
      ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z) {x} +
      ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z) {y} +
      ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z) {z} := by
  rw [← fourBridgeAgreementSpinMass_neg_two_eq_rankMass_one]
  exact fourBridgeAgreementSpinMass_neg_two_eq_marginal_singletons
    G J hf hwx hwy hwz hxy hxz hyz



theorem fourBridgeRankMass_three_eq_marginal_cosingletons
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    {w x y z : V}
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    fourBridgeRankMass
        (fourBridgeOneCoeff G J hf w x y z)
        (fourBridgeTwoCoeff G J hf w x y z)
        (fourBridgeThreeCoeff G J hf w x y z)
        (fourBridgeFourCoeff G J hf w x y z) 3 =
      ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z)
          (fourBridgeMarkedSet w x y z \ {w}) +
      ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z)
          (fourBridgeMarkedSet w x y z \ {x}) +
      ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z)
          (fourBridgeMarkedSet w x y z \ {y}) +
      ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z)
          (fourBridgeMarkedSet w x y z \ {z}) := by
  rw [← fourBridgeAgreementSpinMass_two_eq_rankMass_three]
  exact fourBridgeAgreementSpinMass_two_eq_marginal_cosingletons
    G J hf hwx hwy hwz hxy hxz hyz




theorem fourBridgeAgreementMarginal_singletonPair_sum_le_rank
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall v, 0 <= hf v)
    {w x y z : V}
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    let M := fourBridgeMarkedSet w x y z
    let mu := ghsiAgreementMarginalProb G J hf M
    let p := fourBridgeRankMass
      (fourBridgeOneCoeff G J hf w x y z)
      (fourBridgeTwoCoeff G J hf w x y z)
      (fourBridgeThreeCoeff G J hf w x y z)
      (fourBridgeFourCoeff G J hf w x y z)
    mu {w} * mu {x} + mu {w} * mu {y} + mu {w} * mu {z} +
        mu {x} * mu {y} + mu {x} * mu {z} + mu {y} * mu {z} <=
      mu ∅ * p 2 := by
  classical
  dsimp only
  let M := fourBridgeMarkedSet w x y z
  let mu := ghsiAgreementMarginalProb G J hf M
  have hsingle (u : V) (hu : u ∈ M) : ({u} : Finset V) ⊆ M :=
    singleton_subset_iff.mpr hu
  have hcut (u v : V) (hu : u ∈ M) (hv : v ∈ M) :
      mu {u} * mu {v} <= mu ({u} ∩ {v}) * mu ({u} ∪ {v}) :=
    ghsiAgreementMarginalProb_logSupermodular G J hf hJ hhf
      (hsingle u hu) (hsingle v hv)
  have hwM : w ∈ M := by simp [M, fourBridgeMarkedSet]
  have hxM : x ∈ M := by simp [M, fourBridgeMarkedSet]
  have hyM : y ∈ M := by simp [M, fourBridgeMarkedSet]
  have hzM : z ∈ M := by simp [M, fourBridgeMarkedSet]
  have hwxCut : mu {w} * mu {x} <= mu ∅ * mu {w, x} := by
    simpa [hwx] using hcut w x hwM hxM
  have hwyCut : mu {w} * mu {y} <= mu ∅ * mu {w, y} := by
    simpa [hwy] using hcut w y hwM hyM
  have hwzCut : mu {w} * mu {z} <= mu ∅ * mu {w, z} := by
    simpa [hwz] using hcut w z hwM hzM
  have hxyCut : mu {x} * mu {y} <= mu ∅ * mu {x, y} := by
    simpa [hxy] using hcut x y hxM hyM
  have hxzCut : mu {x} * mu {z} <= mu ∅ * mu {x, z} := by
    simpa [hxz] using hcut x z hxM hzM
  have hyzCut : mu {y} * mu {z} <= mu ∅ * mu {y, z} := by
    simpa [hyz] using hcut y z hyM hzM
  have hrank := fourBridgeRankMass_two_eq_marginal_pairs
    G J hf hwx hwy hwz hxy hxz hyz
  rw [hrank]
  dsimp only [mu, M] at hwxCut hwyCut hwzCut hxyCut hxzCut hyzCut
  nlinarith


theorem fourBridgeRankMass_one_sq_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall v, 0 <= hf v)
    {w x y z : V}
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    let p := fourBridgeRankMass
      (fourBridgeOneCoeff G J hf w x y z)
      (fourBridgeTwoCoeff G J hf w x y z)
      (fourBridgeThreeCoeff G J hf w x y z)
      (fourBridgeFourCoeff G J hf w x y z)
    p 1 ^ 2 <= p 1 + 2 * p 0 * p 2 := by
  classical
  dsimp only
  let M := fourBridgeMarkedSet w x y z
  let mu := ghsiAgreementMarginalProb G J hf M
  have hcut := fourBridgeAgreementMarginal_singletonPair_sum_le_rank
    G J hf hJ hhf hwx hwy hwz hxy hxz hyz
  have hw0 := ghsiAgreementMarginalProb_nonneg G J hf M {w}
  have hx0 := ghsiAgreementMarginalProb_nonneg G J hf M {x}
  have hy0 := ghsiAgreementMarginalProb_nonneg G J hf M {y}
  have hz0 := ghsiAgreementMarginalProb_nonneg G J hf M {z}
  have hw1 := ghsiAgreementMarginalProb_le_one G J hf M {w}
  have hx1 := ghsiAgreementMarginalProb_le_one G J hf M {x}
  have hy1 := ghsiAgreementMarginalProb_le_one G J hf M {y}
  have hz1 := ghsiAgreementMarginalProb_le_one G J hf M {z}
  rw [fourBridgeRankMass_one_eq_marginal_singletons
      G J hf hwx hwy hwz hxy hxz hyz,
    fourBridgeRankMass_zero_eq_marginal_empty]
  dsimp only [mu, M] at hcut hw0 hx0 hy0 hz0 hw1 hx1 hy1 hz1
  nlinarith [mul_nonneg hw0 (sub_nonneg.mpr hw1),
    mul_nonneg hx0 (sub_nonneg.mpr hx1),
    mul_nonneg hy0 (sub_nonneg.mpr hy1),
    mul_nonneg hz0 (sub_nonneg.mpr hz1)]


set_option maxHeartbeats 2000000 in


theorem fourBridgeAgreementMarginal_cosingletonPair_sum_le_rank
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall v, 0 <= hf v)
    {w x y z : V}
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    let M := fourBridgeMarkedSet w x y z
    let mu := ghsiAgreementMarginalProb G J hf M
    let p := fourBridgeRankMass
      (fourBridgeOneCoeff G J hf w x y z)
      (fourBridgeTwoCoeff G J hf w x y z)
      (fourBridgeThreeCoeff G J hf w x y z)
      (fourBridgeFourCoeff G J hf w x y z)
    mu (M \ {w}) * mu (M \ {x}) +
        mu (M \ {w}) * mu (M \ {y}) +
        mu (M \ {w}) * mu (M \ {z}) +
        mu (M \ {x}) * mu (M \ {y}) +
        mu (M \ {x}) * mu (M \ {z}) +
        mu (M \ {y}) * mu (M \ {z}) <=
      p 2 * mu M := by
  classical
  dsimp only
  let M := fourBridgeMarkedSet w x y z
  let mu := ghsiAgreementMarginalProb G J hf M
  have hcut (u v : V) :
      mu (M \ {u}) * mu (M \ {v}) <=
        mu ((M \ {u}) ∩ (M \ {v})) *
          mu ((M \ {u}) ∪ (M \ {v})) :=
    ghsiAgreementMarginalProb_logSupermodular G J hf hJ hhf
      sdiff_subset sdiff_subset
  have hwM : w ∈ M := by simp [M, fourBridgeMarkedSet]
  have hxM : x ∈ M := by simp [M, fourBridgeMarkedSet]
  have hyM : y ∈ M := by simp [M, fourBridgeMarkedSet]
  have hzM : z ∈ M := by simp [M, fourBridgeMarkedSet]
  have hinter (u v : V) :
      (M \ {u}) ∩ (M \ {v}) = M \ {u, v} := by
    ext a
    simp [and_assoc, and_left_comm, and_comm]
  have hunion (u v : V) (hu : u ∈ M) (hv : v ∈ M) (huv : u ≠ v) :
      (M \ {u}) ∪ (M \ {v}) = M := by
    ext a
    simp only [mem_union, mem_sdiff, mem_singleton]
    constructor
    · rintro (h | h)
      · exact h.1
      · exact h.1
    · intro ha
      by_cases hau : a = u
      · right
        exact ⟨ha, hau ▸ huv⟩
      · left
        exact ⟨ha, hau⟩
  have hpair_wx : M \ {w, x} = {y, z} := by
    ext a
    simp [M, fourBridgeMarkedSet, hwx, hwy, hwz, hxy, hxz, hyz,
      hwx.symm, hwy.symm, hwz.symm, hxy.symm, hxz.symm, hyz.symm] <;> aesop
  have hpair_wy : M \ {w, y} = {x, z} := by
    ext a
    simp [M, fourBridgeMarkedSet, hwx, hwy, hwz, hxy, hxz, hyz,
      hwx.symm, hwy.symm, hwz.symm, hxy.symm, hxz.symm, hyz.symm] <;> aesop
  have hpair_wz : M \ {w, z} = {x, y} := by
    ext a
    simp [M, fourBridgeMarkedSet, hwx, hwy, hwz, hxy, hxz, hyz,
      hwx.symm, hwy.symm, hwz.symm, hxy.symm, hxz.symm, hyz.symm] <;> aesop
  have hpair_xy : M \ {x, y} = {w, z} := by
    ext a
    simp [M, fourBridgeMarkedSet, hwx, hwy, hwz, hxy, hxz, hyz,
      hwx.symm, hwy.symm, hwz.symm, hxy.symm, hxz.symm, hyz.symm] <;> aesop
  have hpair_xz : M \ {x, z} = {w, y} := by
    ext a
    simp [M, fourBridgeMarkedSet, hwx, hwy, hwz, hxy, hxz, hyz,
      hwx.symm, hwy.symm, hwz.symm, hxy.symm, hxz.symm, hyz.symm] <;> aesop
  have hpair_yz : M \ {y, z} = {w, x} := by
    ext a
    simp [M, fourBridgeMarkedSet, hwx, hwy, hwz, hxy, hxz, hyz,
      hwx.symm, hwy.symm, hwz.symm, hxy.symm, hxz.symm, hyz.symm] <;> aesop
  have hwxCut := hcut w x
  have hwyCut := hcut w y
  have hwzCut := hcut w z
  have hxyCut := hcut x y
  have hxzCut := hcut x z
  have hyzCut := hcut y z
  rw [hinter, hunion w x hwM hxM hwx, hpair_wx] at hwxCut
  rw [hinter, hunion w y hwM hyM hwy, hpair_wy] at hwyCut
  rw [hinter, hunion w z hwM hzM hwz, hpair_wz] at hwzCut
  rw [hinter, hunion x y hxM hyM hxy, hpair_xy] at hxyCut
  rw [hinter, hunion x z hxM hzM hxz, hpair_xz] at hxzCut
  rw [hinter, hunion y z hyM hzM hyz, hpair_yz] at hyzCut
  have hrank := fourBridgeRankMass_two_eq_marginal_pairs
    G J hf hwx hwy hwz hxy hxz hyz
  rw [hrank]
  dsimp only [mu, M] at hwxCut hwyCut hwzCut hxyCut hxzCut hyzCut
  nlinarith


theorem fourBridgeRankMass_three_sq_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall v, 0 <= hf v)
    {w x y z : V}
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    let p := fourBridgeRankMass
      (fourBridgeOneCoeff G J hf w x y z)
      (fourBridgeTwoCoeff G J hf w x y z)
      (fourBridgeThreeCoeff G J hf w x y z)
      (fourBridgeFourCoeff G J hf w x y z)
    p 3 ^ 2 <= p 3 + 2 * p 2 * p 4 := by
  classical
  dsimp only
  let M := fourBridgeMarkedSet w x y z
  let mu := ghsiAgreementMarginalProb G J hf M
  let sw := M \ {w}
  let sx := M \ {x}
  let sy := M \ {y}
  let sz := M \ {z}
  have hcut := fourBridgeAgreementMarginal_cosingletonPair_sum_le_rank
    G J hf hJ hhf hwx hwy hwz hxy hxz hyz
  have hw0 := ghsiAgreementMarginalProb_nonneg G J hf M sw
  have hx0 := ghsiAgreementMarginalProb_nonneg G J hf M sx
  have hy0 := ghsiAgreementMarginalProb_nonneg G J hf M sy
  have hz0 := ghsiAgreementMarginalProb_nonneg G J hf M sz
  have hw1 := ghsiAgreementMarginalProb_le_one G J hf M sw
  have hx1 := ghsiAgreementMarginalProb_le_one G J hf M sx
  have hy1 := ghsiAgreementMarginalProb_le_one G J hf M sy
  have hz1 := ghsiAgreementMarginalProb_le_one G J hf M sz
  rw [fourBridgeRankMass_three_eq_marginal_cosingletons
      G J hf hwx hwy hwz hxy hxz hyz,
    fourBridgeRankMass_four_eq_marginal_full]
  dsimp only [mu, M, sw, sx, sy, sz] at hcut hw0 hx0 hy0 hz0
  dsimp only [mu, M, sw, sx, sy, sz] at hw1 hx1 hy1 hz1
  nlinarith [mul_nonneg hw0 (sub_nonneg.mpr hw1),
    mul_nonneg hx0 (sub_nonneg.mpr hx1),
    mul_nonneg hy0 (sub_nonneg.mpr hy1),
    mul_nonneg hz0 (sub_nonneg.mpr hz1)]




theorem fourBridgeAgreementMarginal_nestedSingletonPair_sum_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall v, 0 <= hf v)
    {w x y z : V} :
    let M := fourBridgeMarkedSet w x y z
    let mu := ghsiAgreementMarginalProb G J hf M
    (mu {w} + mu {x}) * mu (M \ {w, x}) +
        (mu {w} + mu {y}) * mu (M \ {w, y}) +
        (mu {w} + mu {z}) * mu (M \ {w, z}) +
        (mu {x} + mu {y}) * mu (M \ {x, y}) +
        (mu {x} + mu {z}) * mu (M \ {x, z}) +
        (mu {y} + mu {z}) * mu (M \ {y, z}) <=
      mu {w, x} * (mu (M \ {w}) + mu (M \ {x})) +
        mu {w, y} * (mu (M \ {w}) + mu (M \ {y})) +
        mu {w, z} * (mu (M \ {w}) + mu (M \ {z})) +
        mu {x, y} * (mu (M \ {x}) + mu (M \ {y})) +
        mu {x, z} * (mu (M \ {x}) + mu (M \ {z})) +
        mu {y, z} * (mu (M \ {y}) + mu (M \ {z})) := by
  classical
  dsimp only
  let M := fourBridgeMarkedSet w x y z
  let mu := ghsiAgreementMarginalProb G J hf M
  have hwM : w ∈ M := by simp [M, fourBridgeMarkedSet]
  have hxM : x ∈ M := by simp [M, fourBridgeMarkedSet]
  have hyM : y ∈ M := by simp [M, fourBridgeMarkedSet]
  have hzM : z ∈ M := by simp [M, fourBridgeMarkedSet]
  have hflag (u v : V) (hu : u ∈ M) (hv : v ∈ M) :
      mu {u} * mu (M \ {u, v}) <=
        mu {u, v} * mu (M \ {u}) := by
    apply ghsiAgreementMarginalProb_compl_ratio_mono G J hf hJ hhf
    · simp
    · intro a ha
      simp only [mem_insert, mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact hu
      · exact hv
  have hwx := hflag w x hwM hxM
  have hxw := hflag x w hxM hwM
  have hwy := hflag w y hwM hyM
  have hyw := hflag y w hyM hwM
  have hwz := hflag w z hwM hzM
  have hzw := hflag z w hzM hwM
  have hxy := hflag x y hxM hyM
  have hyx := hflag y x hyM hxM
  have hxz := hflag x z hxM hzM
  have hzx := hflag z x hzM hxM
  have hyz := hflag y z hyM hzM
  have hzy := hflag z y hzM hyM
  dsimp only [mu, M] at hwx hxw hwy hyw hwz hzw hxy hyx hxz hzx hyz hzy
  simp only [Finset.pair_comm x w] at hxw
  simp only [Finset.pair_comm y w] at hyw
  simp only [Finset.pair_comm z w] at hzw
  simp only [Finset.pair_comm y x] at hyx
  simp only [Finset.pair_comm z x] at hzx
  simp only [Finset.pair_comm z y] at hzy
  nlinarith


set_option maxHeartbeats 2000000 in



theorem fourBridgeAgreementMarginal_intersectingPair_sum_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall v, 0 <= hf v)
    {w x y z : V}
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    let M := fourBridgeMarkedSet w x y z
    let mu := ghsiAgreementMarginalProb G J hf M
    mu {w, x} * mu {w, y} + mu {x, w} * mu {x, y} +
        mu {y, w} * mu {y, x} +
        mu {w, x} * mu {w, z} + mu {x, w} * mu {x, z} +
        mu {z, w} * mu {z, x} +
        mu {w, y} * mu {w, z} + mu {y, w} * mu {y, z} +
        mu {z, w} * mu {z, y} +
        mu {x, y} * mu {x, z} + mu {y, x} * mu {y, z} +
        mu {z, x} * mu {z, y} <=
      mu {w} * mu {w, x, y} + mu {x} * mu {x, w, y} +
        mu {y} * mu {y, w, x} +
        mu {w} * mu {w, x, z} + mu {x} * mu {x, w, z} +
        mu {z} * mu {z, w, x} +
        mu {w} * mu {w, y, z} + mu {y} * mu {y, w, z} +
        mu {z} * mu {z, w, y} +
        mu {x} * mu {x, y, z} + mu {y} * mu {y, x, z} +
        mu {z} * mu {z, x, y} := by
  classical
  dsimp only
  let M := fourBridgeMarkedSet w x y z
  let mu := ghsiAgreementMarginalProb G J hf M
  have hpair (u v : V) (hu : u ∈ M) (hv : v ∈ M) :
      ({u, v} : Finset V) ⊆ M := by
    intro a ha
    simp only [mem_insert, mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact hu
    · exact hv
  have hwM : w ∈ M := by simp [M, fourBridgeMarkedSet]
  have hxM : x ∈ M := by simp [M, fourBridgeMarkedSet]
  have hyM : y ∈ M := by simp [M, fourBridgeMarkedSet]
  have hzM : z ∈ M := by simp [M, fourBridgeMarkedSet]
  have hcut (a b c : V) (ha : a ∈ M) (hb : b ∈ M) (hc : c ∈ M)
      (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
      mu {a, b} * mu {a, c} <= mu {a} * mu {a, b, c} := by
    have h := ghsiAgreementMarginalProb_logSupermodular
      G J hf hJ hhf (hpair a b ha hb) (hpair a c ha hc)
    simpa [hab, hac, hbc, hab.symm, hac.symm, hbc.symm,
      or_assoc, or_left_comm, or_comm] using h
  have hwxy := hcut w x y hwM hxM hyM hwx hwy hxy
  have hxwy := hcut x w y hxM hwM hyM hwx.symm hxy hwy
  have hywx := hcut y w x hyM hwM hxM hwy.symm hxy.symm hwx
  have hwxz := hcut w x z hwM hxM hzM hwx hwz hxz
  have hxwz := hcut x w z hxM hwM hzM hwx.symm hxz hwz
  have hzwx := hcut z w x hzM hwM hxM hwz.symm hxz.symm hwx
  have hwyz := hcut w y z hwM hyM hzM hwy hwz hyz
  have hywz := hcut y w z hyM hwM hzM hwy.symm hyz hwz
  have hzwy := hcut z w y hzM hwM hyM hwz.symm hyz.symm hwy
  have hxyz := hcut x y z hxM hyM hzM hxy hxz hyz
  have hyxz := hcut y x z hyM hxM hzM hxy.symm hyz hxz
  have hzyx := hcut z x y hzM hxM hyM hxz.symm hyz.symm hxy
  dsimp only [mu, M] at hwxy hxwy hywx hwxz hxwz hzwx
  dsimp only [mu, M] at hwyz hywz hzwy hxyz hyxz hzyx
  nlinarith

end

end StatMech.Ising
