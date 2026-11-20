/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKLoopSixVertexLocalCorrespondence
import Code.FrontierD.SixVertexRectangleTorusCut












open Finset Matrix

namespace StatMech.FrontierD

noncomputable section


abbrev SixVertexLocalIncomingPattern := Fin 4 -> Bool

def sixVertexLocalIncomingCount
    (p : SixVertexLocalIncomingPattern) : Nat :=
  ∑ i, (p i).toNat

def SixVertexLocalIncomingPattern.Ice
    (p : SixVertexLocalIncomingPattern) : Prop :=
  sixVertexLocalIncomingCount p = 2


def SixVertexLocalIncomingPattern.IsCType
    (p : SixVertexLocalIncomingPattern) : Prop :=
  (p 0).toNat + (p 1).toNat = 0 \/
    (p 0).toNat + (p 1).toNat = 2

instance (p : SixVertexLocalIncomingPattern) :
    Decidable p.Ice := by
  unfold SixVertexLocalIncomingPattern.Ice
  exact inferInstance

instance (p : SixVertexLocalIncomingPattern) :
    Decidable p.IsCType := by
  unfold SixVertexLocalIncomingPattern.IsCType
  exact inferInstance

def sixVertexLocalCTypeCount
    (p q : SixVertexLocalIncomingPattern) : Nat :=
  (if p.IsCType then 1 else 0) + (if q.IsCType then 1 else 0)


def sixVertexLocalSwapTwo
    (p q : SixVertexLocalIncomingPattern) (d e : Fin 4) :
    SixVertexLocalIncomingPattern × SixVertexLocalIncomingPattern :=
  (fun i => if i = d \/ i = e then q i else p i,
    fun i => if i = d \/ i = e then p i else q i)




theorem exists_sixVertexLocalSwapTwo_of_disagreement
    (p q : SixVertexLocalIncomingPattern) (d : Fin 4)
    (hp : p.Ice) (hq : q.Ice) (hd : p d ≠ q d)
    (hnotCC : Not (p.IsCType /\ q.IsCType)) :
    exists e : Fin 4,
      e ≠ d /\ p e ≠ q e /\
      (sixVertexLocalSwapTwo p q d e).1.Ice /\
      (sixVertexLocalSwapTwo p q d e).2.Ice /\
      sixVertexLocalCTypeCount p q <=
        sixVertexLocalCTypeCount
          (sixVertexLocalSwapTwo p q d e).1
          (sixVertexLocalSwapTwo p q d e).2 := by
  decide +revert




theorem sixVertexLocal_all_disagree_of_ice_cType
    (p q : SixVertexLocalIncomingPattern) (d : Fin 4)
    (hp : p.Ice) (hq : q.Ice)
    (hpc : p.IsCType) (hqc : q.IsCType) (hd : p d ≠ q d) :
    forall i : Fin 4, p i ≠ q i := by
  decide +revert


noncomputable def sixVertexLocalPatternWeight
    (c : Real) (p : SixVertexLocalIncomingPattern) : Real :=
  if p.Ice then if p.IsCType then c else 1 else 0

theorem sixVertexLocalPatternWeight_eq_pow
    (c : Real) (p : SixVertexLocalIncomingPattern) (hp : p.Ice) :
    sixVertexLocalPatternWeight c p =
      c ^ (if p.IsCType then 1 else 0) := by
  unfold sixVertexLocalPatternWeight
  rw [if_pos hp]
  by_cases hpc : p.IsCType <;> simp [hpc]



theorem exists_sixVertexLocalSwapTwo_weight_product_le
    {c : Real} (hc : 1 <= c)
    (p q : SixVertexLocalIncomingPattern) (d : Fin 4)
    (hp : p.Ice) (hq : q.Ice) (hd : p d ≠ q d)
    (hnotCC : Not (p.IsCType /\ q.IsCType)) :
    exists e : Fin 4,
      e ≠ d /\ p e ≠ q e /\
      (sixVertexLocalSwapTwo p q d e).1.Ice /\
      (sixVertexLocalSwapTwo p q d e).2.Ice /\
      sixVertexLocalPatternWeight c p * sixVertexLocalPatternWeight c q <=
        sixVertexLocalPatternWeight c
            (sixVertexLocalSwapTwo p q d e).1 *
          sixVertexLocalPatternWeight c
            (sixVertexLocalSwapTwo p q d e).2 := by
  obtain ⟨e, hed, heq, hp', hq', hcount⟩ :=
    exists_sixVertexLocalSwapTwo_of_disagreement p q d hp hq hd hnotCC
  refine ⟨e, hed, heq, hp', hq', ?_⟩
  rw [sixVertexLocalPatternWeight_eq_pow c p hp,
    sixVertexLocalPatternWeight_eq_pow c q hq,
    sixVertexLocalPatternWeight_eq_pow c _ hp',
    sixVertexLocalPatternWeight_eq_pow c _ hq', ← pow_add, ← pow_add]
  exact pow_le_pow_right₀ hc hcount


def sixVertexLocalIncomingPattern
    (omega : SixVertexArrows T) (v : T.Vertex) :
    SixVertexLocalIncomingPattern :=
  ![fkLoopWestIncoming omega v, fkLoopEastIncoming omega v,
    fkLoopSouthIncoming omega v, fkLoopNorthIncoming omega v]

theorem sixVertexLocalIncomingPattern_count
    (omega : SixVertexArrows T) (v : T.Vertex) :
    sixVertexLocalIncomingCount (sixVertexLocalIncomingPattern omega v) =
      omega.incomingCount v := by
  simp [sixVertexLocalIncomingCount, Fin.sum_univ_four,
    sixVertexLocalIncomingPattern,
    SixVertexArrows.incomingCount, fkLoopWestIncoming,
    fkLoopEastIncoming, fkLoopSouthIncoming, fkLoopNorthIncoming]

theorem sixVertexLocalIncomingPattern_ice
    (omega : SixVertexArrows T) (homega : omega.IceRule)
    (v : T.Vertex) :
    (sixVertexLocalIncomingPattern omega v).Ice := by
  rw [SixVertexLocalIncomingPattern.Ice,
    sixVertexLocalIncomingPattern_count]
  exact homega v

theorem sixVertexLocalIncomingPattern_isCType_iff
    (omega : SixVertexArrows T) (v : T.Vertex) :
    (sixVertexLocalIncomingPattern omega v).IsCType <->
      omega.IsCType v := by
  rfl

theorem sixVertexLocalPatternWeight_eq_localWeight
    (c : Real) (omega : SixVertexArrows T) (v : T.Vertex) :
    sixVertexLocalPatternWeight c
        (sixVertexLocalIncomingPattern omega v) =
      omega.localWeight c v := by
  classical
  simp [sixVertexLocalPatternWeight, SixVertexLocalIncomingPattern.Ice,
    SixVertexLocalIncomingPattern.IsCType, SixVertexArrows.localWeight,
    sixVertexLocalIncomingCount, Fin.sum_univ_four,
    sixVertexLocalIncomingPattern, SixVertexArrows.incomingCount,
    SixVertexArrows.IsCType, fkLoopWestIncoming, fkLoopEastIncoming,
    fkLoopSouthIncoming, fkLoopNorthIncoming]




def sixVertexRectangleLocalIncomingPattern
    (omega : SixVertexRectangleArrows N M) (v : Fin N × Fin M) :
    SixVertexLocalIncomingPattern :=
  ![omega.horizontal (v.1.castSucc, v.2),
    !omega.horizontal (v.1.succ, v.2),
    omega.vertical (v.1, v.2.castSucc),
    !omega.vertical (v.1, v.2.succ)]

theorem sixVertexRectangleLocalIncomingPattern_count
    (omega : SixVertexRectangleArrows N M) (v : Fin N × Fin M) :
    sixVertexLocalIncomingCount
        (sixVertexRectangleLocalIncomingPattern omega v) =
      omega.incomingCount v := by
  simp [sixVertexLocalIncomingCount, Fin.sum_univ_four,
    sixVertexRectangleLocalIncomingPattern,
    SixVertexRectangleArrows.incomingCount]

theorem sixVertexRectangleLocalIncomingPattern_ice
    (omega : SixVertexRectangleArrows N M) (homega : omega.IceRule)
    (v : Fin N × Fin M) :
    (sixVertexRectangleLocalIncomingPattern omega v).Ice := by
  rw [SixVertexLocalIncomingPattern.Ice,
    sixVertexRectangleLocalIncomingPattern_count]
  exact homega v

theorem sixVertexRectangleLocalIncomingPattern_isCType_iff
    (omega : SixVertexRectangleArrows N M) (v : Fin N × Fin M) :
    (sixVertexRectangleLocalIncomingPattern omega v).IsCType <->
      omega.IsCType v := by
  rfl

theorem sixVertexRectangleLocalPatternWeight_eq_localWeight
    (c : Real) (omega : SixVertexRectangleArrows N M)
    (v : Fin N × Fin M) :
    sixVertexLocalPatternWeight c
        (sixVertexRectangleLocalIncomingPattern omega v) =
      omega.localWeight c v := by
  classical
  simp [sixVertexLocalPatternWeight, SixVertexLocalIncomingPattern.Ice,
    SixVertexLocalIncomingPattern.IsCType,
    sixVertexLocalIncomingCount, Fin.sum_univ_four,
    sixVertexRectangleLocalIncomingPattern,
    SixVertexRectangleArrows.localWeight,
    SixVertexRectangleArrows.incomingCount,
    SixVertexRectangleArrows.IsCType]



def sixVertexRectangleSwitchFirst
    (mask omega eta : SixVertexRectangleArrows N M) :
    SixVertexRectangleArrows N M where
  horizontal e := if mask.horizontal e then eta.horizontal e
    else omega.horizontal e
  vertical e := if mask.vertical e then eta.vertical e
    else omega.vertical e


def sixVertexRectangleSwitchSecond
    (mask omega eta : SixVertexRectangleArrows N M) :
    SixVertexRectangleArrows N M where
  horizontal e := if mask.horizontal e then omega.horizontal e
    else eta.horizontal e
  vertical e := if mask.vertical e then omega.vertical e
    else eta.vertical e


def sixVertexRectangleLocalSwitchMask
    (mask : SixVertexRectangleArrows N M) (v : Fin N × Fin M) :
    SixVertexLocalIncomingPattern :=
  ![mask.horizontal (v.1.castSucc, v.2),
    mask.horizontal (v.1.succ, v.2),
    mask.vertical (v.1, v.2.castSucc),
    mask.vertical (v.1, v.2.succ)]


def sixVertexLocalSwapMask
    (p q mask : SixVertexLocalIncomingPattern) :
    SixVertexLocalIncomingPattern × SixVertexLocalIncomingPattern :=
  (fun i => if mask i then q i else p i,
    fun i => if mask i then p i else q i)


def sixVertexLocalSwitchMaskCount
    (mask : SixVertexLocalIncomingPattern) : Nat :=
  ∑ i, (mask i).toNat





theorem exists_sixVertexLocalSwapMask_of_disagreement
    (p q : SixVertexLocalIncomingPattern) (d : Fin 4)
    (hp : p.Ice) (hq : q.Ice) (hd : p d ≠ q d) :
    exists mask : SixVertexLocalIncomingPattern,
      mask d = true /\
      (forall i, mask i = true -> p i ≠ q i) /\
      (sixVertexLocalSwapMask p q mask).1.Ice /\
      (sixVertexLocalSwapMask p q mask).2.Ice /\
      sixVertexLocalCTypeCount p q <=
        sixVertexLocalCTypeCount
          (sixVertexLocalSwapMask p q mask).1
          (sixVertexLocalSwapMask p q mask).2 /\
      (sixVertexLocalSwitchMaskCount mask = 2 \/
        sixVertexLocalSwitchMaskCount mask = 4) := by
  decide +revert

theorem sixVertexRectangleLocalIncomingPattern_pairSwitch
    (mask omega eta : SixVertexRectangleArrows N M)
    (v : Fin N × Fin M) :
    (sixVertexRectangleLocalIncomingPattern
        (sixVertexRectangleSwitchFirst mask omega eta) v,
      sixVertexRectangleLocalIncomingPattern
        (sixVertexRectangleSwitchSecond mask omega eta) v) =
      sixVertexLocalSwapMask
        (sixVertexRectangleLocalIncomingPattern omega v)
        (sixVertexRectangleLocalIncomingPattern eta v)
        (sixVertexRectangleLocalSwitchMask mask v) := by
  apply Prod.ext <;> funext i <;> fin_cases i <;>
    simp [sixVertexRectangleLocalIncomingPattern,
      sixVertexRectangleSwitchFirst, sixVertexRectangleSwitchSecond,
      sixVertexRectangleLocalSwitchMask, sixVertexLocalSwapMask] <;>
    split <;> simp_all

theorem sixVertexLocalSwapMask_eq_swapTwo
    (p q mask : SixVertexLocalIncomingPattern) (d e : Fin 4)
    (hmask : forall i, mask i = decide (i = d \/ i = e)) :
    sixVertexLocalSwapMask p q mask = sixVertexLocalSwapTwo p q d e := by
  apply Prod.ext <;> funext i <;>
    simp [sixVertexLocalSwapMask, sixVertexLocalSwapTwo, hmask i]



theorem sixVertexRectanglePairSwitch_weight_product_le
    {c : Real} (hc : 0 <= c)
    (mask omega eta : SixVertexRectangleArrows N M)
    (hlocal : forall v,
      omega.localWeight c v * eta.localWeight c v <=
        (sixVertexRectangleSwitchFirst mask omega eta).localWeight c v *
          (sixVertexRectangleSwitchSecond mask omega eta).localWeight c v) :
    omega.weight c * eta.weight c <=
      (sixVertexRectangleSwitchFirst mask omega eta).weight c *
        (sixVertexRectangleSwitchSecond mask omega eta).weight c := by
  simp only [SixVertexRectangleArrows.weight, <- Finset.prod_mul_distrib]
  exact Finset.prod_le_prod
    (fun v _ => mul_nonneg
      (SixVertexRectangleArrows.localWeight_nonneg hc omega v)
      (SixVertexRectangleArrows.localWeight_nonneg hc eta v))
      (fun v _ => hlocal v)





def sixVertexTorusSwitchFirst
    (mask omega eta : SixVertexArrows T) : SixVertexArrows T where
  horizontal e := if mask.horizontal e then eta.horizontal e
    else omega.horizontal e
  vertical e := if mask.vertical e then eta.vertical e
    else omega.vertical e


def sixVertexTorusSwitchSecond
    (mask omega eta : SixVertexArrows T) : SixVertexArrows T where
  horizontal e := if mask.horizontal e then omega.horizontal e
    else eta.horizontal e
  vertical e := if mask.vertical e then omega.vertical e
    else eta.vertical e


def sixVertexTorusLocalSwitchMask
    (mask : SixVertexArrows T) (v : T.Vertex) :
    SixVertexLocalIncomingPattern :=
  ![mask.horizontal (SixVertexArrows.cyclicPred T.width_pos v.1, v.2),
    mask.horizontal v,
    mask.vertical (v.1, SixVertexArrows.cyclicPred T.height_pos v.2),
    mask.vertical v]

theorem sixVertexTorusLocalIncomingPattern_pairSwitch
    (mask omega eta : SixVertexArrows T) (v : T.Vertex) :
    (sixVertexLocalIncomingPattern
        (sixVertexTorusSwitchFirst mask omega eta) v,
      sixVertexLocalIncomingPattern
        (sixVertexTorusSwitchSecond mask omega eta) v) =
      sixVertexLocalSwapMask
        (sixVertexLocalIncomingPattern omega v)
        (sixVertexLocalIncomingPattern eta v)
        (sixVertexTorusLocalSwitchMask mask v) := by
  apply Prod.ext <;> funext i <;> fin_cases i <;>
    simp [sixVertexLocalIncomingPattern, sixVertexTorusSwitchFirst,
      sixVertexTorusSwitchSecond, sixVertexTorusLocalSwitchMask,
      sixVertexLocalSwapMask, fkLoopWestIncoming, fkLoopEastIncoming,
      fkLoopSouthIncoming, fkLoopNorthIncoming] <;> split <;> simp_all

end

end StatMech.FrontierD
