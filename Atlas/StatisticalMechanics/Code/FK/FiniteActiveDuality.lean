/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.TriHexFKFiniteWiredWeights
import Code.BeffaraDC.Duality









open Finset SimpleGraph
open scoped BigOperators

namespace StatMech.FK

open Lattice

noncomputable section

variable {V W : Type*} [Fintype V] [Fintype W]
  [DecidableEq V] [DecidableEq W]
  (G : SimpleGraph V) (H : SimpleGraph W)
  [DecidableRel G.Adj] [DecidableRel H.Adj]


def activeDualConfig (edgeDual : G.edgeSet ≃ H.edgeSet) :
    ConfigSpace G.edgeSet ≃ ConfigSpace H.edgeSet where
  toFun omega e := !(omega (edgeDual.symm e))
  invFun eta e := !(eta (edgeDual e))
  left_inv omega := by
    funext e
    simp
  right_inv eta := by
    funext e
    simp

@[simp] theorem activeDualConfig_apply
    (edgeDual : G.edgeSet ≃ H.edgeSet)
    (omega : ConfigSpace G.edgeSet) (e : H.edgeSet) :
    activeDualConfig G H edgeDual omega e =
      !(omega (edgeDual.symm e)) := rfl

@[simp] theorem activeDualConfig_symm_apply
    (edgeDual : G.edgeSet ≃ H.edgeSet)
    (eta : ConfigSpace H.edgeSet) (e : G.edgeSet) :
    (activeDualConfig G H edgeDual).symm eta e =
      !(eta (edgeDual e)) := rfl


def activeOpenCount (omega : ConfigSpace G.edgeSet) : Nat :=
  Fintype.card {e : G.edgeSet // omega e = true}

private def edgeFinsetEdgeSetEquiv : G.edgeFinset ≃ G.edgeSet where
  toFun e := ⟨e.1, by
    simpa only [SimpleGraph.mem_edgeFinset] using e.2⟩
  invFun e := ⟨e.1, by
    simpa only [SimpleGraph.mem_edgeFinset] using e.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem openCount_extendActive_eq_activeOpenCount
    (omega : ConfigSpace G.edgeSet) :
    openCount G (extendActive G omega) = activeOpenCount G omega := by
  let E : {e : G.edgeFinset // extendActive G omega e.1 = true} ≃
      {e : G.edgeSet // omega e = true} :=
    Equiv.subtypeEquiv (edgeFinsetEdgeSetEquiv G) (fun e => by
      simpa [edgeFinsetEdgeSetEquiv] using
        extendActive_apply G omega (edgeFinsetEdgeSetEquiv G e))
  have hcard := Fintype.card_congr E
  unfold openCount activeOpenCount
  rw [← hcard, Fintype.card_subtype]
  rw [show (Finset.univ : Finset G.edgeFinset) =
      G.edgeFinset.attach by ext; simp]
  have hf := congrArg Finset.card
    (Finset.filter_attach
      (fun e : Sym2 V => extendActive G omega e = true) G.edgeFinset)
  simpa using hf.symm


theorem activeOpenCount_dualConfig
    (edgeDual : G.edgeSet ≃ H.edgeSet)
    (omega : ConfigSpace G.edgeSet) :
    activeOpenCount H (activeDualConfig G H edgeDual omega) =
      Fintype.card G.edgeSet - activeOpenCount G omega := by
  unfold activeOpenCount
  rw [← Fintype.card_subtype_compl (fun e : G.edgeSet => omega e = true)]
  let E : {e : G.edgeSet // ¬ omega e = true} ≃
      {f : H.edgeSet // activeDualConfig G H edgeDual omega f = true} :=
    Equiv.subtypeEquiv edgeDual (fun e => by simp)
  have hcard := Fintype.card_congr E
  exact hcard.symm

theorem activeWeight_eq_count (p q : Real)
    (omega : ConfigSpace G.edgeSet) :
    activeWeight G (fun _ => p) q omega =
      BeffaraDC.edgeProductCount p (Fintype.card G.edgeSet)
          (activeOpenCount G omega) *
        q ^ numClusters G (extendActive G omega) := by
  unfold activeWeight fkWeightW
  change edgeProduct G p (extendActive G omega) * _ = _
  rw [BeffaraDC.dlt_edgeProduct_eq_count,
    openCount_extendActive_eq_activeOpenCount]
  rw [SimpleGraph.edgeFinset_card]

theorem wiredActiveWeight_eq_count
    (boundary : W → Prop) [DecidablePred boundary]
    (p q : Real) (eta : ConfigSpace H.edgeSet) :
    PeriodicPlanar.wiredActiveWeight H boundary p q eta =
      BeffaraDC.edgeProductCount p (Fintype.card H.edgeSet)
          (activeOpenCount H eta) *
        q ^ numClustersWired H boundary (extendActive H eta) := by
  unfold PeriodicPlanar.wiredActiveWeight wiredFkWeight
  rw [BeffaraDC.dlt_edgeProduct_eq_count,
    openCount_extendActive_eq_activeOpenCount]
  rw [SimpleGraph.edgeFinset_card]



def ActiveFreeWiredEulerIdentity
    (boundary : W → Prop) [DecidablePred boundary]
    (edgeDual : G.edgeSet ≃ H.edgeSet) : Prop :=
  ∀ omega : ConfigSpace G.edgeSet,
    Fintype.card V +
        numClustersWired H boundary
          (extendActive H (activeDualConfig G H edgeDual omega)) =
      activeOpenCount G omega +
        numClusters G (extendActive G omega) + 1



theorem active_free_wired_weight_duality
    (boundary : W → Prop) [DecidablePred boundary]
    (edgeDual : G.edgeSet ≃ H.edgeSet)
    (hEuler : ActiveFreeWiredEulerIdentity G H boundary edgeDual)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (omega : ConfigSpace G.edgeSet) :
    activeWeight G (fun _ => p) q omega *
        q ^ (Fintype.card G.edgeSet + 1) =
      (p / (1 - BeffaraDC.dualParam p q)) ^
          Fintype.card G.edgeSet * q ^ Fintype.card V *
        PeriodicPlanar.wiredActiveWeight H boundary
          (BeffaraDC.dualParam p q) q
          (activeDualConfig G H edgeDual omega) := by
  let m := Fintype.card G.edgeSet
  let o := activeOpenCount G omega
  let k := numClusters G (extendActive G omega)
  let eta := activeDualConfig G H edgeDual omega
  let kd := numClustersWired H boundary (extendActive H eta)
  let v := Fintype.card V
  have hom : o ≤ m := Fintype.card_subtype_le _
  have hedge := BeffaraDC.dlt_edgeProduct_duality hp hp1 hq m o hom
  have hedgeCard : Fintype.card H.edgeSet = m := by
    simpa only [m] using (Fintype.card_congr edgeDual).symm
  have hopenDual : activeOpenCount H eta = m - o := by
    dsimp only [eta, m, o]
    exact activeOpenCount_dualConfig G H edgeDual omega
  have heuler : v + kd = o + k + 1 := hEuler omega
  have hpow : q ^ o * q ^ k * q = q ^ v * q ^ kd := by
    calc
      q ^ o * q ^ k * q = q ^ (o + k + 1) := by
        rw [← pow_add, ← pow_succ]
      _ = q ^ (v + kd) := congrArg (q ^ ·) heuler.symm
      _ = q ^ v * q ^ kd := pow_add q v kd
  rw [activeWeight_eq_count G p q omega,
    wiredActiveWeight_eq_count H boundary
      (BeffaraDC.dualParam p q) q eta]
  rw [hedgeCard, hopenDual]
  change BeffaraDC.edgeProductCount p m o * q ^ k * q ^ (m + 1) =
    (p / (1 - BeffaraDC.dualParam p q)) ^ m * q ^ v *
      (BeffaraDC.edgeProductCount (BeffaraDC.dualParam p q) m (m - o) *
        q ^ kd)
  calc
    BeffaraDC.edgeProductCount p m o * q ^ k * q ^ (m + 1) =
        (BeffaraDC.edgeProductCount p m o * q ^ m) *
          (q ^ k * q) := by
      rw [pow_succ]
      ring
    _ = ((p / (1 - BeffaraDC.dualParam p q)) ^ m * q ^ o *
          BeffaraDC.edgeProductCount (BeffaraDC.dualParam p q) m (m - o)) *
          (q ^ k * q) := by
      rw [hedge]
    _ = (p / (1 - BeffaraDC.dualParam p q)) ^ m *
          BeffaraDC.edgeProductCount (BeffaraDC.dualParam p q) m (m - o) *
          (q ^ o * q ^ k * q) := by ring
    _ = (p / (1 - BeffaraDC.dualParam p q)) ^ m * q ^ v *
          (BeffaraDC.edgeProductCount (BeffaraDC.dualParam p q) m (m - o) *
            q ^ kd) := by
      rw [hpow]
      ring



theorem active_free_wired_prob_duality
    (boundary : W → Prop) [DecidablePred boundary]
    (edgeDual : G.edgeSet ≃ H.edgeSet)
    (hEuler : ActiveFreeWiredEulerIdentity G H boundary edgeDual)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (omega : ConfigSpace G.edgeSet) :
    activeProb G (fun _ => p) q omega =
      PeriodicPlanar.wiredActiveWeight H boundary
          (BeffaraDC.dualParam p q) q
          (activeDualConfig G H edgeDual omega) /
        PeriodicPlanar.wiredActiveZ H boundary
          (BeffaraDC.dualParam p q) q := by
  let A : Real := q ^ (Fintype.card G.edgeSet + 1)
  let B : Real :=
    (p / (1 - BeffaraDC.dualParam p q)) ^ Fintype.card G.edgeSet *
      q ^ Fintype.card V
  have hA : 0 < A := by
    dsimp only [A]
    positivity
  have hpDual := BeffaraDC.dualParam_mem_Ioo hp hp1 hq
  have hB : 0 < B := by
    dsimp only [B]
    exact mul_pos (pow_pos (div_pos hp (sub_pos.mpr hpDual.2)) _)
      (pow_pos hq _)
  have hpoint :
      activeWeight G (fun _ => p) q omega * A =
        B * PeriodicPlanar.wiredActiveWeight H boundary
          (BeffaraDC.dualParam p q) q
          (activeDualConfig G H edgeDual omega) := by
    exact active_free_wired_weight_duality G H boundary edgeDual hEuler
      hp hp1 hq omega
  have hsum :
      activeZ G (fun _ => p) q * A =
        B * PeriodicPlanar.wiredActiveZ H boundary
          (BeffaraDC.dualParam p q) q := by
    calc
      activeZ G (fun _ => p) q * A =
          ∑ omega : ConfigSpace G.edgeSet,
            activeWeight G (fun _ => p) q omega * A := by
        unfold activeZ
        rw [Finset.sum_mul]
      _ = ∑ omega : ConfigSpace G.edgeSet,
          B * PeriodicPlanar.wiredActiveWeight H boundary
            (BeffaraDC.dualParam p q) q
            (activeDualConfig G H edgeDual omega) := by
        apply Finset.sum_congr rfl
        intro eta _
        exact active_free_wired_weight_duality G H boundary edgeDual hEuler
          hp hp1 hq eta
      _ = B * ∑ eta : ConfigSpace H.edgeSet,
          PeriodicPlanar.wiredActiveWeight H boundary
            (BeffaraDC.dualParam p q) q eta := by
        rw [← Finset.mul_sum]
        congr 1
        exact Equiv.sum_comp (activeDualConfig G H edgeDual)
          (fun eta => PeriodicPlanar.wiredActiveWeight H boundary
            (BeffaraDC.dualParam p q) q eta)
      _ = B * PeriodicPlanar.wiredActiveZ H boundary
          (BeffaraDC.dualParam p q) q := by
        rfl
  have hZfree : 0 < activeZ G (fun _ => p) q :=
    activeZ_pos G (fun _ => hp) (fun _ => hp1) hq
  have hZwired : 0 < PeriodicPlanar.wiredActiveZ H boundary
      (BeffaraDC.dualParam p q) q := by
    unfold PeriodicPlanar.wiredActiveZ
    exact Finset.sum_pos
      (fun eta _ => wiredFkWeight_pos H boundary hpDual.1 hpDual.2 hq
        (extendActive H eta))
      Finset.univ_nonempty
  have hw : activeWeight G (fun _ => p) q omega =
      (B / A) * PeriodicPlanar.wiredActiveWeight H boundary
        (BeffaraDC.dualParam p q) q
        (activeDualConfig G H edgeDual omega) := by
    calc
      activeWeight G (fun _ => p) q omega =
          (B * PeriodicPlanar.wiredActiveWeight H boundary
            (BeffaraDC.dualParam p q) q
            (activeDualConfig G H edgeDual omega)) / A :=
        (eq_div_iff hA.ne').2 hpoint
      _ = (B / A) * PeriodicPlanar.wiredActiveWeight H boundary
          (BeffaraDC.dualParam p q) q
          (activeDualConfig G H edgeDual omega) := by ring
  have hZ : activeZ G (fun _ => p) q =
      (B / A) * PeriodicPlanar.wiredActiveZ H boundary
        (BeffaraDC.dualParam p q) q := by
    calc
      activeZ G (fun _ => p) q =
          (B * PeriodicPlanar.wiredActiveZ H boundary
            (BeffaraDC.dualParam p q) q) / A :=
        (eq_div_iff hA.ne').2 hsum
      _ = (B / A) * PeriodicPlanar.wiredActiveZ H boundary
          (BeffaraDC.dualParam p q) q := by ring
  unfold activeProb
  rw [hw, hZ]
  field_simp [hA.ne', hB.ne', hZfree.ne', hZwired.ne']

end

end StatMech.FK
