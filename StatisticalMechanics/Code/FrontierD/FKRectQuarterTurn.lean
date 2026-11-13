/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectDevelopedSquareReflection
import Code.FrontierD.FKRectTorusCrossingEvents



open Set SimpleGraph StatMech.Lattice

namespace StatMech.FrontierD

noncomputable section



def fkRectQuarterTurnTorus (R : FKRectTorus) (hheight : 4 < R.height) :
    FKRectTorus where
  width := R.height / 2
  height := 2 * R.width
  width_gt_two := by
    have hH := Nat.two_mul_div_two_of_even R.height_even
    omega
  height_gt_two := by
    have hW := R.width_gt_two
    omega
  height_even := even_two_mul R.width

@[simp] theorem fkRectQuarterTurnTorus_width
    (R : FKRectTorus) (hheight : 4 < R.height) :
    (fkRectQuarterTurnTorus R hheight).width = R.height / 2 := rfl

@[simp] theorem fkRectQuarterTurnTorus_height
    (R : FKRectTorus) (hheight : 4 < R.height) :
    (fkRectQuarterTurnTorus R hheight).height = 2 * R.width := rfl

private theorem fkRectHeight_two_mul_div_two (R : FKRectTorus) :
    2 * (R.height / 2) = R.height := by
  exact Nat.two_mul_div_two_of_even R.height_even



def fkRectQuarterTurnVertex (R : FKRectTorus) (hheight : 4 < R.height)
    (v : R.Vertex) : (fkRectQuarterTurnTorus R hheight).Vertex :=
  (⟨v.2.val / 2, by
      have hH := fkRectHeight_two_mul_div_two R
      simp only [fkRectQuarterTurnTorus]
      omega⟩,
   ⟨2 * v.1.val + v.2.val % 2, by
      simp only [fkRectQuarterTurnTorus]
      omega⟩)


def fkRectQuarterTurnVertexInv (R : FKRectTorus) (hheight : 4 < R.height)
    (v : (fkRectQuarterTurnTorus R hheight).Vertex) : R.Vertex :=
  (⟨v.2.val / 2, by
      simp only [fkRectQuarterTurnTorus] at v ⊢
      omega⟩,
   ⟨2 * v.1.val + v.2.val % 2, by
      have hH := fkRectHeight_two_mul_div_two R
      simp only [fkRectQuarterTurnTorus] at v ⊢
      omega⟩)

@[simp] theorem fkRectQuarterTurnVertex_fst_val
    (R : FKRectTorus) (hheight : 4 < R.height) (v : R.Vertex) :
    (fkRectQuarterTurnVertex R hheight v).1.val = v.2.val / 2 := rfl

@[simp] theorem fkRectQuarterTurnVertex_snd_val
    (R : FKRectTorus) (hheight : 4 < R.height) (v : R.Vertex) :
    (fkRectQuarterTurnVertex R hheight v).2.val =
      2 * v.1.val + v.2.val % 2 := rfl

theorem fkRectQuarterTurnVertexInv_left
    (R : FKRectTorus) (hheight : 4 < R.height) (v : R.Vertex) :
    fkRectQuarterTurnVertexInv R hheight
        (fkRectQuarterTurnVertex R hheight v) = v := by
  apply Prod.ext <;> apply Fin.ext <;>
    simp [fkRectQuarterTurnVertexInv, fkRectQuarterTurnVertex] <;> omega

theorem fkRectQuarterTurnVertexInv_right
    (R : FKRectTorus) (hheight : 4 < R.height)
    (v : (fkRectQuarterTurnTorus R hheight).Vertex) :
    fkRectQuarterTurnVertex R hheight
        (fkRectQuarterTurnVertexInv R hheight v) = v := by
  apply Prod.ext <;> apply Fin.ext <;>
    simp [fkRectQuarterTurnVertexInv, fkRectQuarterTurnVertex] <;> omega


def fkRectQuarterTurnVertexEquiv (R : FKRectTorus)
    (hheight : 4 < R.height) :
    R.Vertex ≃ (fkRectQuarterTurnTorus R hheight).Vertex where
  toFun := fkRectQuarterTurnVertex R hheight
  invFun := fkRectQuarterTurnVertexInv R hheight
  left_inv := fkRectQuarterTurnVertexInv_left R hheight
  right_inv := fkRectQuarterTurnVertexInv_right R hheight

@[simp] theorem fkRectQuarterTurnVertexEquiv_apply
    (R : FKRectTorus) (hheight : 4 < R.height) (v : R.Vertex) :
    fkRectQuarterTurnVertexEquiv R hheight v =
      fkRectQuarterTurnVertex R hheight v := rfl

private def fkRectParityBit (n : Nat) : Bool := decide (n % 2 = 1)

@[simp] private theorem fkRectParityBit_zero : fkRectParityBit 0 = false := by
  rfl

@[simp] private theorem fkRectParityBit_two_mul (n : Nat) :
    fkRectParityBit (2 * n) = false := by
  simp [fkRectParityBit]

@[simp] private theorem fkRectParityBit_two_mul_add_one (n : Nat) :
    fkRectParityBit (2 * n + 1) = true := by
  simp [fkRectParityBit]

private theorem fkRectParityBit_toNat (n : Nat) :
    (fkRectParityBit n).toNat = n % 2 := by
  have hn := Nat.mod_lt n (by norm_num : 0 < 2)
  interval_cases h : n % 2 <;> simp [fkRectParityBit, h]



def fkRectQuarterTurnEdge (R : FKRectTorus) (hheight : 4 < R.height)
    (a : R.EdgeIndex) : (fkRectQuarterTurnTorus R hheight).EdgeIndex :=
  (fkRectParityBit a.2.2.val,
    (⟨a.2.2.val / 2, by
        have hH := fkRectHeight_two_mul_div_two R
        simp only [fkRectQuarterTurnTorus]
        omega⟩,
     ⟨2 * a.2.1.val + a.1.toNat, by
        simp only [fkRectQuarterTurnTorus]
        cases a.1 <;> simp <;> omega⟩))


def fkRectQuarterTurnEdgeInv (R : FKRectTorus) (hheight : 4 < R.height)
    (a : (fkRectQuarterTurnTorus R hheight).EdgeIndex) : R.EdgeIndex :=
  (fkRectParityBit a.2.2.val,
    (⟨a.2.2.val / 2, by
        simp only [fkRectQuarterTurnTorus] at a ⊢
        omega⟩,
     ⟨2 * a.2.1.val + a.1.toNat, by
        have hH := fkRectHeight_two_mul_div_two R
        simp only [fkRectQuarterTurnTorus] at a ⊢
        cases a.1 <;> simp <;> omega⟩))

theorem fkRectQuarterTurnEdgeInv_left
    (R : FKRectTorus) (hheight : 4 < R.height) (a : R.EdgeIndex) :
    fkRectQuarterTurnEdgeInv R hheight
        (fkRectQuarterTurnEdge R hheight a) = a := by
  rcases a with ⟨b, x, y⟩
  cases b <;> apply Prod.ext
  · simp [fkRectQuarterTurnEdgeInv, fkRectQuarterTurnEdge,
      fkRectParityBit]
  · apply Prod.ext <;> apply Fin.ext <;>
      simp [fkRectQuarterTurnEdgeInv, fkRectQuarterTurnEdge,
        fkRectParityBit_toNat] <;> omega
  · simp [fkRectQuarterTurnEdgeInv, fkRectQuarterTurnEdge,
      fkRectParityBit]
  · apply Prod.ext <;> apply Fin.ext <;>
      simp [fkRectQuarterTurnEdgeInv, fkRectQuarterTurnEdge,
        fkRectParityBit_toNat] <;> omega

theorem fkRectQuarterTurnEdgeInv_right
    (R : FKRectTorus) (hheight : 4 < R.height)
    (a : (fkRectQuarterTurnTorus R hheight).EdgeIndex) :
    fkRectQuarterTurnEdge R hheight
        (fkRectQuarterTurnEdgeInv R hheight a) = a := by
  rcases a with ⟨b, x, y⟩
  cases b <;> apply Prod.ext
  · simp [fkRectQuarterTurnEdgeInv, fkRectQuarterTurnEdge,
      fkRectParityBit]
  · apply Prod.ext <;> apply Fin.ext <;>
      simp [fkRectQuarterTurnEdgeInv, fkRectQuarterTurnEdge,
        fkRectParityBit_toNat] <;> omega
  · simp [fkRectQuarterTurnEdgeInv, fkRectQuarterTurnEdge,
      fkRectParityBit]
  · apply Prod.ext <;> apply Fin.ext <;>
      simp [fkRectQuarterTurnEdgeInv, fkRectQuarterTurnEdge,
        fkRectParityBit_toNat] <;> omega


def fkRectQuarterTurnEdgeEquiv (R : FKRectTorus)
    (hheight : 4 < R.height) :
    R.EdgeIndex ≃ (fkRectQuarterTurnTorus R hheight).EdgeIndex where
  toFun := fkRectQuarterTurnEdge R hheight
  invFun := fkRectQuarterTurnEdgeInv R hheight
  left_inv := fkRectQuarterTurnEdgeInv_left R hheight
  right_inv := fkRectQuarterTurnEdgeInv_right R hheight

@[simp] theorem fkRectQuarterTurnEdgeEquiv_apply
    (R : FKRectTorus) (hheight : 4 < R.height) (a : R.EdgeIndex) :
    fkRectQuarterTurnEdgeEquiv R hheight a =
      fkRectQuarterTurnEdge R hheight a := rfl


theorem fkRectTorusIndexedEdge_quarterTurn
    (R : FKRectTorus) (hheight : 4 < R.height) (a : R.EdgeIndex) :
    fkRectTorusIndexedEdge (fkRectQuarterTurnTorus R hheight)
        (fkRectQuarterTurnEdgeEquiv R hheight a) =
      Sym2.map (fkRectQuarterTurnVertexEquiv R hheight)
        (fkRectTorusIndexedEdge R a) := by
  have hH := fkRectHeight_two_mul_div_two R
  have hW := R.width_gt_two
  rcases a with ⟨b, x, y⟩
  cases b <;> by_cases hy : Even y.val
  · obtain ⟨k, hk⟩ := hy
    have hyeven : Even y.val := ⟨k, hk⟩
    have hymod : y.val % 2 = 0 := by omega
    simp only [fkRectQuarterTurnEdgeEquiv_apply, fkRectQuarterTurnEdge,
      fkRectParityBit, hymod, Nat.reduceEqDiff, decide_false,
      Bool.false_eq_true, if_false, even_two_mul, if_true,
      fkRectTorusIndexedEdge, fkRectQuarterTurnVertexEquiv_apply,
      fkRectQuarterTurnVertex, Bool.toNat_false, Nat.add_zero, hyeven,
      Sym2.map_mk]
    apply Sym2.eq_iff.mpr
    left
    constructor <;> apply Prod.ext <;> apply Fin.ext
    all_goals
      by_cases hx0 : x.val = 0 <;>
        by_cases hy0 : y.val = 0 <;>
        by_cases hyhalf0 : y.val / 2 = 0 <;>
        simp [fkRectCyclicPred_val, hx0, hy0, hyhalf0,
          fkRectQuarterTurnTorus] <;> omega
  · have hymodlt := Nat.mod_lt y.val (by norm_num : 0 < 2)
    have hymod : y.val % 2 = 1 := by
      by_contra h
      apply hy
      rw [Nat.even_iff]
      omega
    simp only [fkRectQuarterTurnEdgeEquiv_apply, fkRectQuarterTurnEdge,
      fkRectParityBit, hymod, decide_true, if_true,
      fkRectTorusIndexedEdge, Bool.false_eq_true, if_false, hy,
      fkRectQuarterTurnVertexEquiv_apply, fkRectQuarterTurnVertex,
      Bool.toNat_false, Nat.add_zero, even_two_mul, Sym2.map_mk]
    apply Sym2.eq_iff.mpr
    right
    constructor <;> apply Prod.ext <;> apply Fin.ext
    all_goals
      by_cases hx0 : x.val = 0 <;>
        by_cases hy0 : y.val = 0 <;>
        by_cases hyhalf0 : y.val / 2 = 0 <;>
        simp [fkRectCyclicPred_val, hx0, hy0, hyhalf0,
          fkRectQuarterTurnTorus] <;> omega
  · obtain ⟨k, hk⟩ := hy
    have hyeven : Even y.val := ⟨k, hk⟩
    have hymod : y.val % 2 = 0 := by omega
    simp only [fkRectQuarterTurnEdgeEquiv_apply, fkRectQuarterTurnEdge,
      fkRectParityBit, hymod, Nat.reduceEqDiff, decide_false,
      Bool.true_eq_false, if_true, Nat.reduceAdd, Nat.not_even_one,
      if_false, fkRectTorusIndexedEdge, fkRectQuarterTurnVertexEquiv_apply,
      fkRectQuarterTurnVertex, Bool.toNat_true, hyeven, even_two_mul,
      Nat.even_add_one, Sym2.map_mk]
    apply Sym2.eq_iff.mpr
    right
    constructor <;> apply Prod.ext <;> apply Fin.ext
    all_goals
      by_cases hx0 : x.val = 0 <;>
        by_cases hy0 : y.val = 0 <;>
        by_cases hyhalf0 : y.val / 2 = 0 <;>
        simp [fkRectCyclicPred_val, hx0, hy0, hyhalf0,
          fkRectQuarterTurnTorus] <;> omega
  · have hymodlt := Nat.mod_lt y.val (by norm_num : 0 < 2)
    have hymod : y.val % 2 = 1 := by
      by_contra h
      apply hy
      rw [Nat.even_iff]
      omega
    simp only [fkRectQuarterTurnEdgeEquiv_apply, fkRectQuarterTurnEdge,
      fkRectParityBit, hymod, decide_true, if_true,
      fkRectTorusIndexedEdge, Nat.reduceAdd, Nat.not_even_one,
      if_false, fkRectQuarterTurnVertexEquiv_apply,
      fkRectQuarterTurnVertex, Bool.toNat_true, hy, even_two_mul,
      Nat.even_add_one, Sym2.map_mk]
    apply Sym2.eq_iff.mpr
    left
    constructor <;> apply Prod.ext <;> apply Fin.ext
    all_goals
      by_cases hx0 : x.val = 0 <;>
        by_cases hy0 : y.val = 0 <;>
        by_cases hyhalf0 : y.val / 2 = 0 <;>
        simp [fkRectCyclicPred_val, hx0, hy0, hyhalf0,
          fkRectQuarterTurnTorus] <;> omega


theorem fkRectTorusGraph_adj_quarterTurn
    (R : FKRectTorus) (hheight : 4 < R.height) (x y : R.Vertex) :
    (fkRectTorusGraph (fkRectQuarterTurnTorus R hheight)).Adj
        (fkRectQuarterTurnVertexEquiv R hheight x)
        (fkRectQuarterTurnVertexEquiv R hheight y) ↔
      (fkRectTorusGraph R).Adj x y := by
  constructor
  · rintro ⟨a, ha⟩
    let b := (fkRectQuarterTurnEdgeEquiv R hheight).symm a
    refine ⟨b, ?_⟩
    have hturn := fkRectTorusIndexedEdge_quarterTurn R hheight b
    rw [(fkRectQuarterTurnEdgeEquiv R hheight).apply_symm_apply a,
      ha] at hturn
    apply Sym2.map.injective
      (fkRectQuarterTurnVertexEquiv R hheight).injective
    simpa only [Sym2.map_mk] using hturn.symm
  · rintro ⟨a, ha⟩
    refine ⟨fkRectQuarterTurnEdgeEquiv R hheight a, ?_⟩
    rw [fkRectTorusIndexedEdge_quarterTurn, ha, Sym2.map_mk]


def fkRectQuarterTurnConfigurationEquiv
    (R : FKRectTorus) (hheight : 4 < R.height) :
    R.Configuration ≃ (fkRectQuarterTurnTorus R hheight).Configuration :=
  Equiv.arrowCongr (fkRectQuarterTurnEdgeEquiv R hheight)
    (Equiv.refl Bool)

@[simp] theorem fkRectQuarterTurnConfigurationEquiv_apply
    (R : FKRectTorus) (hheight : 4 < R.height)
    (omega : R.Configuration)
    (a : (fkRectQuarterTurnTorus R hheight).EdgeIndex) :
    fkRectQuarterTurnConfigurationEquiv R hheight omega a =
      omega ((fkRectQuarterTurnEdgeEquiv R hheight).symm a) := rfl


theorem fkRectOpenGraph_quarterTurn_adj
    (R : FKRectTorus) (hheight : 4 < R.height)
    (omega : R.Configuration) (x y : R.Vertex) :
    (fkRectOpenGraph (fkRectQuarterTurnTorus R hheight)
      (fkRectQuarterTurnConfigurationEquiv R hheight omega)).Adj
        (fkRectQuarterTurnVertexEquiv R hheight x)
        (fkRectQuarterTurnVertexEquiv R hheight y) ↔
      (fkRectOpenGraph R omega).Adj x y := by
  constructor
  · rintro ⟨a, haopen, ha⟩
    let b := (fkRectQuarterTurnEdgeEquiv R hheight).symm a
    refine ⟨b, ?_, ?_⟩
    · exact haopen
    · have hturn := fkRectTorusIndexedEdge_quarterTurn R hheight b
      rw [(fkRectQuarterTurnEdgeEquiv R hheight).apply_symm_apply a,
        ha] at hturn
      apply Sym2.map.injective
        (fkRectQuarterTurnVertexEquiv R hheight).injective
      simpa only [Sym2.map_mk] using hturn.symm
  · rintro ⟨a, haopen, ha⟩
    refine ⟨fkRectQuarterTurnEdgeEquiv R hheight a, ?_, ?_⟩
    · change omega ((fkRectQuarterTurnEdgeEquiv R hheight).symm
          (fkRectQuarterTurnEdgeEquiv R hheight a)) = true
      rw [(fkRectQuarterTurnEdgeEquiv R hheight).symm_apply_apply]
      exact haopen
    · rw [fkRectTorusIndexedEdge_quarterTurn, ha, Sym2.map_mk]


def fkRectOpenGraphQuarterTurnIso
    (R : FKRectTorus) (hheight : 4 < R.height)
    (omega : R.Configuration) :
    fkRectOpenGraph R omega ≃g
      fkRectOpenGraph (fkRectQuarterTurnTorus R hheight)
        (fkRectQuarterTurnConfigurationEquiv R hheight omega) where
  toEquiv := fkRectQuarterTurnVertexEquiv R hheight
  map_rel_iff' := by
    intro x y
    exact fkRectOpenGraph_quarterTurn_adj R hheight omega x y


theorem fkRectOpenEdgeCount_quarterTurn
    (R : FKRectTorus) (hheight : 4 < R.height)
    (omega : R.Configuration) :
    fkRectOpenEdgeCount (fkRectQuarterTurnTorus R hheight)
        (fkRectQuarterTurnConfigurationEquiv R hheight omega) =
      fkRectOpenEdgeCount R omega := by
  unfold fkRectOpenEdgeCount
  let E := fkRectQuarterTurnEdgeEquiv R hheight
  apply Finset.card_bij (fun a _ => E.symm a)
  · intro a ha
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using ha
  · intro a ha b hb hab
    exact E.symm.injective hab
  · intro b hb
    refine ⟨E b, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      change omega (E.symm (E b)) = true
      rwa [E.symm_apply_apply]
    · exact E.symm_apply_apply b


theorem fkRectNumClusters_quarterTurn
    (R : FKRectTorus) (hheight : 4 < R.height)
    (omega : R.Configuration) :
    fkRectNumClusters (fkRectQuarterTurnTorus R hheight)
        (fkRectQuarterTurnConfigurationEquiv R hheight omega) =
      fkRectNumClusters R omega := by
  unfold fkRectNumClusters
  exact (Fintype.card_congr
    (fkRectOpenGraphQuarterTurnIso R hheight omega).connectedComponentEquiv).symm


theorem fkRectCriticalReducedWeight_quarterTurn
    (R : FKRectTorus) (hheight : 4 < R.height) (q : Real)
    (omega : R.Configuration) :
    fkRectCriticalReducedWeight (fkRectQuarterTurnTorus R hheight) q
        (fkRectQuarterTurnConfigurationEquiv R hheight omega) =
      fkRectCriticalReducedWeight R q omega := by
  unfold fkRectCriticalReducedWeight
  rw [fkRectOpenEdgeCount_quarterTurn, fkRectNumClusters_quarterTurn]


theorem fkRectCriticalReducedZ_quarterTurn
    (R : FKRectTorus) (hheight : 4 < R.height) (q : Real) :
    fkRectCriticalReducedZ (fkRectQuarterTurnTorus R hheight) q =
      fkRectCriticalReducedZ R q := by
  unfold fkRectCriticalReducedZ
  rw [← Equiv.sum_comp (fkRectQuarterTurnConfigurationEquiv R hheight)
    (fkRectCriticalReducedWeight (fkRectQuarterTurnTorus R hheight) q)]
  apply Finset.sum_congr rfl
  intro omega homega
  exact fkRectCriticalReducedWeight_quarterTurn R hheight q omega


theorem fkRectCriticalRandomClusterProb_quarterTurn
    (R : FKRectTorus) (hheight : 4 < R.height) (q : Real)
    (omega : R.Configuration) :
    fkRectCriticalRandomClusterProb (fkRectQuarterTurnTorus R hheight) q
        (fkRectQuarterTurnConfigurationEquiv R hheight omega) =
      fkRectCriticalRandomClusterProb R q omega := by
  unfold fkRectCriticalRandomClusterProb
  rw [fkRectCriticalReducedWeight_quarterTurn,
    fkRectCriticalReducedZ_quarterTurn]



theorem fkRectCriticalEventMass_quarterTurn
    (R : FKRectTorus) (hheight : 4 < R.height) (q : Real)
    (A : Set (fkRectQuarterTurnTorus R hheight).Configuration) :
    fkRectCriticalEventMass (fkRectQuarterTurnTorus R hheight) q A =
      fkRectCriticalEventMass R q
        ((fkRectQuarterTurnConfigurationEquiv R hheight) ⁻¹' A) := by
  classical
  let C := fkRectQuarterTurnConfigurationEquiv R hheight
  unfold fkRectCriticalEventMass
  rw [← Equiv.sum_comp C (fun eta =>
    A.indicator (fun eta => fkRectCriticalRandomClusterProb
      (fkRectQuarterTurnTorus R hheight) q eta) eta)]
  apply Finset.sum_congr rfl
  intro omega _
  have hprob : fkRectCriticalRandomClusterProb
      (fkRectQuarterTurnTorus R hheight) q (C omega) =
        fkRectCriticalRandomClusterProb R q omega :=
    fkRectCriticalRandomClusterProb_quarterTurn R hheight q omega
  by_cases hA : C omega ∈ A
  · rw [Set.indicator_of_mem hA,
      Set.indicator_of_mem (show omega ∈ C ⁻¹' A from hA), hprob]
  · rw [Set.indicator_of_notMem hA,
      Set.indicator_of_notMem
        (show omega ∉ C ⁻¹' A from hA)]



theorem fkRectCriticalEventMass_quarterTurn_image
    (R : FKRectTorus) (hheight : 4 < R.height) (q : Real)
    (A : Set R.Configuration) :
    fkRectCriticalEventMass (fkRectQuarterTurnTorus R hheight) q
        (fkRectQuarterTurnConfigurationEquiv R hheight '' A) =
      fkRectCriticalEventMass R q A := by
  rw [fkRectCriticalEventMass_quarterTurn]
  congr 1
  ext omega
  simp


def fkRectQuarterTurnSet (R : FKRectTorus) (hheight : 4 < R.height)
    (S : Set R.Vertex) :
    Set (fkRectQuarterTurnTorus R hheight).Vertex :=
  fkRectQuarterTurnVertexEquiv R hheight '' S



def fkRectQuarterTurnSetEquiv (R : FKRectTorus)
    (hheight : 4 < R.height) (S : Set R.Vertex) :
    S ≃ fkRectQuarterTurnSet R hheight S where
  toFun v := ⟨fkRectQuarterTurnVertexEquiv R hheight v.1,
    ⟨v.1, v.2, rfl⟩⟩
  invFun v := ⟨(fkRectQuarterTurnVertexEquiv R hheight).symm v.1, by
    rcases v.2 with ⟨w, hw, hturn⟩
    rw [← hturn]
    rw [Equiv.symm_apply_apply]
    exact hw⟩
  left_inv v := by
    apply Subtype.ext
    exact (fkRectQuarterTurnVertexEquiv R hheight).symm_apply_apply v.1
  right_inv v := by
    apply Subtype.ext
    exact (fkRectQuarterTurnVertexEquiv R hheight).apply_symm_apply v.1


def fkRectOpenGraphQuarterTurnInduceIso
    (R : FKRectTorus) (hheight : 4 < R.height)
    (omega : R.Configuration) (S : Set R.Vertex) :
    (fkRectOpenGraph R omega).induce S ≃g
      (fkRectOpenGraph (fkRectQuarterTurnTorus R hheight)
        (fkRectQuarterTurnConfigurationEquiv R hheight omega)).induce
          (fkRectQuarterTurnSet R hheight S) where
  toEquiv := fkRectQuarterTurnSetEquiv R hheight S
  map_rel_iff' := by
    intro x y
    exact fkRectOpenGraph_quarterTurn_adj R hheight omega x.1 y.1


theorem fkRectConnectedWithin_quarterTurn_iff
    (R : FKRectTorus) (hheight : 4 < R.height)
    (omega : R.Configuration) (S : Set R.Vertex) (x y : S) :
    FKRectConnectedWithin (fkRectQuarterTurnTorus R hheight)
        (fkRectQuarterTurnConfigurationEquiv R hheight omega)
        (fkRectQuarterTurnSet R hheight S)
        (fkRectQuarterTurnSetEquiv R hheight S x)
        (fkRectQuarterTurnSetEquiv R hheight S y) ↔
      FKRectConnectedWithin R omega S x y := by
  exact (fkRectOpenGraphQuarterTurnInduceIso
    R hheight omega S).reachable_iff



theorem fkRectCritical_connectedWithinMass_quarterTurn
    (R : FKRectTorus) (hheight : 4 < R.height) (q : Real)
    (S : Set R.Vertex) (x y : S) :
    fkRectCriticalEventMass (fkRectQuarterTurnTorus R hheight) q
        {omega | FKRectConnectedWithin
          (fkRectQuarterTurnTorus R hheight) omega
          (fkRectQuarterTurnSet R hheight S)
          (fkRectQuarterTurnSetEquiv R hheight S x)
          (fkRectQuarterTurnSetEquiv R hheight S y)} =
      fkRectCriticalEventMass R q
        {omega | FKRectConnectedWithin R omega S x y} := by
  classical
  let C := fkRectQuarterTurnConfigurationEquiv R hheight
  let A : Set R.Configuration :=
    {omega | FKRectConnectedWithin R omega S x y}
  let B : Set (fkRectQuarterTurnTorus R hheight).Configuration :=
    {omega | FKRectConnectedWithin
      (fkRectQuarterTurnTorus R hheight) omega
      (fkRectQuarterTurnSet R hheight S)
      (fkRectQuarterTurnSetEquiv R hheight S x)
      (fkRectQuarterTurnSetEquiv R hheight S y)}
  unfold fkRectCriticalEventMass
  rw [← Equiv.sum_comp C (fun eta =>
    B.indicator (fun eta => fkRectCriticalRandomClusterProb
      (fkRectQuarterTurnTorus R hheight) q eta) eta)]
  apply Finset.sum_congr rfl
  intro omega _
  have hmem : C omega ∈ B ↔ omega ∈ A :=
    fkRectConnectedWithin_quarterTurn_iff
      R hheight omega S x y
  have hprob : fkRectCriticalRandomClusterProb
      (fkRectQuarterTurnTorus R hheight) q (C omega) =
        fkRectCriticalRandomClusterProb R q omega :=
    fkRectCriticalRandomClusterProb_quarterTurn
      R hheight q omega
  by_cases hA : omega ∈ A
  · rw [Set.indicator_of_mem hA,
      Set.indicator_of_mem (hmem.mpr hA), hprob]
  · rw [Set.indicator_of_notMem hA,
      Set.indicator_of_notMem (fun hB => hA (hmem.mp hB))]

end

end StatMech.FrontierD
