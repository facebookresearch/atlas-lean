/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.MonoBC









open scoped BigOperators
open SimpleGraph

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace StatMech.FK

noncomputable section

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]



def indexedOpenGraph (ends : E -> Sym2 V) (omega : E -> Bool) :
    SimpleGraph V :=
  SimpleGraph.fromEdgeSet {e | exists i, ends i = e /\ omega i = true}

theorem indexedOpenGraph_inf_le
    (ends : E -> Sym2 V) (a b : E -> Bool) :
    indexedOpenGraph ends (a ⊓ b) <=
      indexedOpenGraph ends a ⊓ indexedOpenGraph ends b := by
  intro x y hxy
  rw [SimpleGraph.inf_adj]
  simp only [indexedOpenGraph, SimpleGraph.fromEdgeSet_adj,
    Set.mem_setOf_eq] at hxy ⊢
  obtain ⟨⟨i, hi, hab⟩, hne⟩ := hxy
  have hab' : a i = true ∧ b i = true := by simpa using hab
  have ha : a i = true := hab'.1
  have hb : b i = true := hab'.2
  exact ⟨⟨⟨i, hi, ha⟩, hne⟩, ⟨⟨i, hi, hb⟩, hne⟩⟩

theorem indexedOpenGraph_sup
    (ends : E -> Sym2 V) (a b : E -> Bool) :
    indexedOpenGraph ends (a ⊔ b) =
      indexedOpenGraph ends a ⊔ indexedOpenGraph ends b := by
  ext x y
  simp only [indexedOpenGraph, SimpleGraph.fromEdgeSet_adj,
    Set.mem_setOf_eq, SimpleGraph.sup_adj]
  constructor
  · rintro ⟨⟨i, hi, hab⟩, hne⟩
    have hor : a i = true ∨ b i = true := by
      simpa using hab
    rcases hor with ha | hb
    · exact Or.inl ⟨⟨i, hi, ha⟩, hne⟩
    · exact Or.inr ⟨⟨i, hi, hb⟩, hne⟩
  · rintro (⟨⟨i, hi, ha⟩, hne⟩ | ⟨⟨i, hi, hb⟩, hne⟩)
    · exact ⟨⟨i, hi, by simp [ha]⟩, hne⟩
    · exact ⟨⟨i, hi, by simp [hb]⟩, hne⟩


def indexedEdgeProduct (p : Real) (omega : E -> Bool) : Real :=
  ∏ e, if omega e then p else 1 - p

theorem indexedEdgeProduct_pos {p : Real} (hp : 0 < p) (hp1 : p < 1)
    (omega : E -> Bool) :
    0 < indexedEdgeProduct p omega := by
  apply Finset.prod_pos
  intro e _
  split
  · exact hp
  · linarith

theorem indexedEdgeProduct_logModular
    (p : Real) (a b : E -> Bool) :
    indexedEdgeProduct p a * indexedEdgeProduct p b =
      indexedEdgeProduct p (a ⊓ b) * indexedEdgeProduct p (a ⊔ b) := by
  unfold indexedEdgeProduct
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e _
  rw [Pi.inf_apply, Pi.sup_apply]
  cases a e <;> cases b e <;> simp
  all_goals ring


theorem card_connectedComponent_antitone
    {G H : SimpleGraph V} (hGH : G <= H) :
    Nat.card H.ConnectedComponent <= Nat.card G.ConnectedComponent := by
  classical
  letI : DecidableRel H.Adj := Classical.decRel _
  have h := card_connectedComponent_marginal hGH H
  rw [sup_eq_right.mpr hGH, sup_idem] at h
  omega



def indexedNumClustersBC (ends : E -> Sym2 V)
    (C : SimpleGraph V) [DecidableRel C.Adj] (omega : E -> Bool) : Nat :=
  Nat.card (indexedOpenGraph ends omega ⊔ C).ConnectedComponent

theorem indexedMixed_supermodular_bc
    (ends : E -> Sym2 V)
    (C C' : SimpleGraph V) [DecidableRel C.Adj] [DecidableRel C'.Adj]
    (hCC' : C <= C') (a b : E -> Bool) :
    indexedNumClustersBC ends C a + indexedNumClustersBC ends C' b <=
      indexedNumClustersBC ends C (a ⊓ b) +
        indexedNumClustersBC ends C' (a ⊔ b) := by
  classical
  let A := indexedOpenGraph ends a
  let B := indexedOpenGraph ends b
  let I := indexedOpenGraph ends (a ⊓ b)
  let U := indexedOpenGraph ends (a ⊔ b)
  have hI : I <= A ⊓ B := indexedOpenGraph_inf_le ends a b
  have hU : U = A ⊔ B := indexedOpenGraph_sup ends a b
  have hPQ : (A ⊓ B) ⊔ C <= A ⊔ C :=
    sup_le_sup_right inf_le_left C
  have hmarg := card_connectedComponent_marginal hPQ (B ⊔ C')
  have hCC'' : C ⊔ C' = C' := sup_eq_right.mpr hCC'
  have hBAB : (A ⊓ B) ⊔ B = B := by
    rw [inf_comm, sup_comm, sup_inf_self]
  have e1 : (A ⊓ B) ⊔ C ⊔ (B ⊔ C') = B ⊔ C' := by
    calc
      (A ⊓ B) ⊔ C ⊔ (B ⊔ C') =
          ((A ⊓ B) ⊔ B) ⊔ (C ⊔ C') := by ac_rfl
      _ = B ⊔ C' := by rw [hBAB, hCC'']
  have e2 : A ⊔ C ⊔ (B ⊔ C') = A ⊔ B ⊔ C' := by
    calc
      A ⊔ C ⊔ (B ⊔ C') = (A ⊔ B) ⊔ (C ⊔ C') := by ac_rfl
      _ = A ⊔ B ⊔ C' := by rw [hCC'']
  rw [e1, e2] at hmarg
  have hmeet : Nat.card ((A ⊓ B) ⊔ C).ConnectedComponent <=
      Nat.card (I ⊔ C).ConnectedComponent :=
    card_connectedComponent_antitone (sup_le_sup_right hI C)
  unfold indexedNumClustersBC
  change Nat.card (A ⊔ C).ConnectedComponent +
      Nat.card (B ⊔ C').ConnectedComponent <=
    Nat.card (I ⊔ C).ConnectedComponent +
      Nat.card (U ⊔ C').ConnectedComponent
  rw [hU]
  omega

def indexedBcWeight (ends : E -> Sym2 V)
    (C : SimpleGraph V) [DecidableRel C.Adj]
    (p q : Real) (omega : E -> Bool) : Real :=
  indexedEdgeProduct p omega * q ^ indexedNumClustersBC ends C omega

theorem indexedBcWeight_pos
    (ends : E -> Sym2 V) (C : SimpleGraph V) [DecidableRel C.Adj]
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (omega : E -> Bool) :
    0 < indexedBcWeight ends C p q omega :=
  mul_pos (indexedEdgeProduct_pos hp hp1 omega) (pow_pos hq _)

def indexedBcZ (ends : E -> Sym2 V)
    (C : SimpleGraph V) [DecidableRel C.Adj] (p q : Real) : Real :=
  ∑ omega : E -> Bool, indexedBcWeight ends C p q omega

theorem indexedBcZ_pos
    (ends : E -> Sym2 V) (C : SimpleGraph V) [DecidableRel C.Adj]
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    0 < indexedBcZ ends C p q :=
  Finset.sum_pos
    (fun omega _ => indexedBcWeight_pos ends C hp hp1 hq omega)
    Finset.univ_nonempty

def indexedBcProb (ends : E -> Sym2 V)
    (C : SimpleGraph V) [DecidableRel C.Adj]
    (p q : Real) (omega : E -> Bool) : Real :=
  indexedBcWeight ends C p q omega / indexedBcZ ends C p q

theorem indexedBcProb_nonneg
    (ends : E -> Sym2 V) (C : SimpleGraph V) [DecidableRel C.Adj]
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (omega : E -> Bool) :
    0 <= indexedBcProb ends C p q omega :=
  div_nonneg (indexedBcWeight_pos ends C hp hp1 hq omega).le
    (indexedBcZ_pos ends C hp hp1 hq).le

theorem indexedBcProb_sum_eq_one
    (ends : E -> Sym2 V) (C : SimpleGraph V) [DecidableRel C.Adj]
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ∑ omega : E -> Bool, indexedBcProb ends C p q omega = 1 := by
  unfold indexedBcProb indexedBcZ
  rw [← Finset.sum_div]
  exact div_self (indexedBcZ_pos ends C hp hp1 hq).ne'

theorem indexedBcWeight_cross
    (ends : E -> Sym2 V)
    (C C' : SimpleGraph V) [DecidableRel C.Adj] [DecidableRel C'.Adj]
    (hCC' : C <= C') {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (a b : E -> Bool) :
    indexedBcWeight ends C p q a * indexedBcWeight ends C' p q b <=
      indexedBcWeight ends C p q (a ⊓ b) *
        indexedBcWeight ends C' p q (a ⊔ b) := by
  have hcluster :
      q ^ indexedNumClustersBC ends C a *
          q ^ indexedNumClustersBC ends C' b <=
        q ^ indexedNumClustersBC ends C (a ⊓ b) *
          q ^ indexedNumClustersBC ends C' (a ⊔ b) := by
    rw [← pow_add, ← pow_add]
    exact pow_le_pow_right₀ hq
      (indexedMixed_supermodular_bc ends C C' hCC' a b)
  have hedge := indexedEdgeProduct_logModular p a b
  have hedge0 : 0 <= indexedEdgeProduct p (a ⊓ b) *
      indexedEdgeProduct p (a ⊔ b) :=
    mul_nonneg (indexedEdgeProduct_pos hp hp1 _).le
      (indexedEdgeProduct_pos hp hp1 _).le
  unfold indexedBcWeight
  rw [show indexedEdgeProduct p a * q ^ indexedNumClustersBC ends C a *
        (indexedEdgeProduct p b * q ^ indexedNumClustersBC ends C' b) =
      (indexedEdgeProduct p a * indexedEdgeProduct p b) *
        (q ^ indexedNumClustersBC ends C a *
          q ^ indexedNumClustersBC ends C' b) by ring]
  rw [show indexedEdgeProduct p (a ⊓ b) *
        q ^ indexedNumClustersBC ends C (a ⊓ b) *
        (indexedEdgeProduct p (a ⊔ b) *
          q ^ indexedNumClustersBC ends C' (a ⊔ b)) =
      (indexedEdgeProduct p (a ⊓ b) * indexedEdgeProduct p (a ⊔ b)) *
        (q ^ indexedNumClustersBC ends C (a ⊓ b) *
          q ^ indexedNumClustersBC ends C' (a ⊔ b)) by ring]
  rw [hedge]
  exact mul_le_mul_of_nonneg_left hcluster hedge0

theorem indexedBcProb_cross
    (ends : E -> Sym2 V)
    (C C' : SimpleGraph V) [DecidableRel C.Adj] [DecidableRel C'.Adj]
    (hCC' : C <= C') {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (a b : E -> Bool) :
    indexedBcProb ends C p q a * indexedBcProb ends C' p q b <=
      indexedBcProb ends C p q (a ⊓ b) *
        indexedBcProb ends C' p q (a ⊔ b) := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  have hZ : 0 < indexedBcZ ends C p q := indexedBcZ_pos ends C hp hp1 hq0
  have hZ' : 0 < indexedBcZ ends C' p q :=
    indexedBcZ_pos ends C' hp hp1 hq0
  unfold indexedBcProb
  rw [div_mul_div_comm, div_mul_div_comm,
    div_le_div_iff_of_pos_right (mul_pos hZ hZ')]
  exact indexedBcWeight_cross ends C C' hCC' hp hp1 hq a b

def indexedBcEventMass (ends : E -> Sym2 V)
    (C : SimpleGraph V) [DecidableRel C.Adj]
    (p q : Real) (A : Set (E -> Bool)) : Real :=
  ∑ omega, A.indicator (fun _ => (1 : Real)) omega *
    indexedBcProb ends C p q omega

theorem indexedBcEventMass_mono_bc
    (ends : E -> Sym2 V)
    (C C' : SimpleGraph V) [DecidableRel C.Adj] [DecidableRel C'.Adj]
    (hCC' : C <= C') {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    {A : Set (E -> Bool)} (hA : IsIncreasing A) :
    indexedBcEventMass ends C p q A <=
      indexedBcEventMass ends C' p q A := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  unfold indexedBcEventMass
  apply holley_dominates
  · exact indexedBcProb_nonneg ends C hp hp1 hq0
  · exact indexedBcProb_nonneg ends C' hp hp1 hq0
  · rw [indexedBcProb_sum_eq_one ends C hp hp1 hq0,
      indexedBcProb_sum_eq_one ends C' hp hp1 hq0]
  · exact indexedBcProb_cross ends C C' hCC' hp hp1 hq
  · exact hA

end

end StatMech.FK
