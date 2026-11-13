/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


























































import Mathlib
import Code.FK.RandomCluster
import Code.FK.FKG
import Code.FK.Comparison
import Code.FK.Limits
import Code.Lattice.BoundaryConditions
import Code.Inequalities.FKG
import Code.Foundations.StochasticDomination

open scoped BigOperators
open SimpleGraph

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]











noncomputable def numClustersBC (C : SimpleGraph V) [DecidableRel C.Adj]
    (ω : ConfigSpace (Sym2 V)) : ℕ :=
  Nat.card (openSub G ω ⊔ C).ConnectedComponent



theorem numClustersBC_bot (ω : ConfigSpace (Sym2 V)) :
    numClustersBC G (⊥ : SimpleGraph V) ω = numClusters G ω := by
  rw [numClustersBC, sup_bot_eq, numClusters, Nat.card_eq_fintype_card]

variable (bdry : V → Prop) [DecidablePred bdry]



theorem numClustersBC_boundaryClique (ω : ConfigSpace (Sym2 V)) :
    numClustersBC G (StatMech.Lattice.boundaryCliqueGraph bdry) ω
      = StatMech.Lattice.numClustersWired G bdry ω := by
  rw [numClustersBC, StatMech.Lattice.numClustersWired, StatMech.Lattice.wiredGraph,
    openSub_eq_openGraph]


















theorem mixed_supermodular_bc (C C' : SimpleGraph V) [DecidableRel C.Adj]
    [DecidableRel C'.Adj] (hCC' : C ≤ C') (a b : ConfigSpace (Sym2 V)) :
    numClustersBC G C a + numClustersBC G C' b
      ≤ numClustersBC G C (a ⊓ b) + numClustersBC G C' (a ⊔ b) := by
  classical
  
  have hinf : openSub G (a ⊓ b) = openSub G a ⊓ openSub G b := by
    ext i j; rw [SimpleGraph.inf_adj]; exact openSub_inf_adj G a b i j
  have hsup : openSub G (a ⊔ b) = openSub G a ⊔ openSub G b := by
    ext i j; rw [SimpleGraph.sup_adj]; exact openSub_sup_adj G a b i j
  
  rw [numClustersBC, numClustersBC, numClustersBC, numClustersBC, hinf, hsup]
  set A := openSub G a with hA
  set B := openSub G b with hB
  
  have hPQ : (A ⊓ B) ⊔ C ≤ A ⊔ C := sup_le_sup_right inf_le_left C
  have hmarg := card_connectedComponent_marginal hPQ (B ⊔ C')
  have hCC'' : C ⊔ C' = C' := sup_eq_right.mpr hCC'
  
  have hBAB : (A ⊓ B) ⊔ B = B := by rw [inf_comm, sup_comm, sup_inf_self]
  have e1 : (A ⊓ B) ⊔ C ⊔ (B ⊔ C') = B ⊔ C' := by
    calc (A ⊓ B) ⊔ C ⊔ (B ⊔ C')
        = ((A ⊓ B) ⊔ B) ⊔ (C ⊔ C') := by ac_rfl
      _ = B ⊔ C' := by rw [hBAB, hCC'']
  have e2 : A ⊔ C ⊔ (B ⊔ C') = A ⊔ B ⊔ C' := by
    calc A ⊔ C ⊔ (B ⊔ C')
        = (A ⊔ B) ⊔ (C ⊔ C') := by ac_rfl
      _ = A ⊔ B ⊔ C' := by rw [hCC'']
  rw [e1, e2] at hmarg
  
  omega






variable (C : SimpleGraph V) [DecidableRel C.Adj]



noncomputable def bcWeight (p q : ℝ) (ω : ConfigSpace (Sym2 V)) : ℝ :=
  edgeProduct G p ω * q ^ numClustersBC G C ω

theorem bcWeight_pos {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (ω : ConfigSpace (Sym2 V)) : 0 < bcWeight G C p q ω :=
  mul_pos (edgeProduct_pos G hp hp1 ω) (pow_pos hq _)

theorem bcWeight_nonneg {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (ω : ConfigSpace (Sym2 V)) : 0 ≤ bcWeight G C p q ω :=
  (bcWeight_pos G C hp hp1 hq ω).le



noncomputable def bcZ (p q : ℝ) : ℝ :=
  ∑ ω : ConfigSpace (Sym2 V), bcWeight G C p q ω

theorem bcZ_pos {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    0 < bcZ G C p q :=
  Finset.sum_pos (fun ω _ => bcWeight_pos G C hp hp1 hq ω) Finset.univ_nonempty

theorem bcZ_ne_zero {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    bcZ G C p q ≠ 0 :=
  (bcZ_pos G C hp hp1 hq).ne'



noncomputable def bcProb (p q : ℝ) (ω : ConfigSpace (Sym2 V)) : ℝ :=
  bcWeight G C p q ω / bcZ G C p q

theorem bcProb_nonneg {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (ω : ConfigSpace (Sym2 V)) : 0 ≤ bcProb G C p q ω :=
  div_nonneg (bcWeight_nonneg G C hp hp1 hq ω) (bcZ_pos G C hp hp1 hq).le

theorem bcProb_sum_eq_one {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ∑ ω : ConfigSpace (Sym2 V), bcProb G C p q ω = 1 := by
  unfold bcProb
  rw [← Finset.sum_div]
  exact div_self (bcZ_ne_zero G C hp hp1 hq)







theorem bcWeight_cross (C' : SimpleGraph V) [DecidableRel C'.Adj] (hCC' : C ≤ C')
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) (a b : ConfigSpace (Sym2 V)) :
    bcWeight G C p q a * bcWeight G C' p q b
      ≤ bcWeight G C p q (a ⊓ b) * bcWeight G C' p q (a ⊔ b) := by
  have hcluster :
      q ^ numClustersBC G C a * q ^ numClustersBC G C' b
        ≤ q ^ numClustersBC G C (a ⊓ b) * q ^ numClustersBC G C' (a ⊔ b) := by
    rw [← pow_add, ← pow_add]
    exact pow_le_pow_right₀ hq (mixed_supermodular_bc G C C' hCC' a b)
  have hedge := edgeProduct_logModular G p a b
  have hpow_nonneg : (0 : ℝ) ≤ edgeProduct G p (a ⊓ b) * edgeProduct G p (a ⊔ b) :=
    mul_nonneg (edgeProduct_pos G hp hp1 _).le (edgeProduct_pos G hp hp1 _).le
  have hLHS : bcWeight G C p q a * bcWeight G C' p q b
      = (edgeProduct G p a * edgeProduct G p b)
          * (q ^ numClustersBC G C a * q ^ numClustersBC G C' b) := by
    unfold bcWeight; ring
  have hRHS : bcWeight G C p q (a ⊓ b) * bcWeight G C' p q (a ⊔ b)
      = (edgeProduct G p (a ⊔ b) * edgeProduct G p (a ⊓ b))
          * (q ^ numClustersBC G C (a ⊓ b) * q ^ numClustersBC G C' (a ⊔ b)) := by
    unfold bcWeight; ring
  rw [hLHS, hRHS, hedge]
  have hcomm : edgeProduct G p (a ⊔ b) * edgeProduct G p (a ⊓ b)
      = edgeProduct G p (a ⊓ b) * edgeProduct G p (a ⊔ b) := by ring
  rw [hcomm]
  exact mul_le_mul_of_nonneg_left hcluster hpow_nonneg






theorem bcProb_cross (C' : SimpleGraph V) [DecidableRel C'.Adj] (hCC' : C ≤ C')
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) (a b : ConfigSpace (Sym2 V)) :
    bcProb G C p q a * bcProb G C' p q b
      ≤ bcProb G C p q (a ⊓ b) * bcProb G C' p q (a ⊔ b) := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  have hZ1 : 0 < bcZ G C p q := bcZ_pos G C hp hp1 hq0
  have hZ2 : 0 < bcZ G C' p q := bcZ_pos G C' hp hp1 hq0
  unfold bcProb
  rw [div_mul_div_comm, div_mul_div_comm,
    div_le_div_iff_of_pos_right (mul_pos hZ1 hZ2)]
  exact bcWeight_cross G C C' hCC' hp hp1 hq a b





theorem bcProb_FKGLatticeCondition {p q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 1 ≤ q) : FKGLatticeCondition (fun ω => bcProb G C p q ω) := by
  intro a b
  simpa only [mul_comm] using bcProb_cross G C C le_rfl hp hp1 hq a b



theorem bcProb_positively_associated {p q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 1 ≤ q) {f g : ConfigSpace (Sym2 V) → ℝ} (hf : Monotone f)
    (hg : Monotone g) :
    (∑ ω, bcProb G C p q ω * f ω) * (∑ ω, bcProb G C p q ω * g ω)
      ≤ ∑ ω, bcProb G C p q ω * (f ω * g ω) := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  exact fkg_inequality
    (fun ω => bcProb_nonneg G C hp hp1 hq0 ω)
    (bcProb_sum_eq_one G C hp hp1 hq0)
    (bcProb_FKGLatticeCondition G C hp hp1 hq) hf hg



theorem bcProb_positively_associated_events {p q : ℝ} (hp : 0 < p)
    (hp1 : p < 1) (hq : 1 ≤ q) {A B : Set (ConfigSpace (Sym2 V))}
    (hA : IsIncreasing A) (hB : IsIncreasing B) :
    (∑ ω, bcProb G C p q ω * A.indicator (fun _ => (1 : ℝ)) ω)
        * (∑ ω, bcProb G C p q ω * B.indicator (fun _ => (1 : ℝ)) ω)
      ≤ ∑ ω, bcProb G C p q ω * (A ∩ B).indicator (fun _ => (1 : ℝ)) ω := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  exact fkg_inequality_events
    (fun ω => bcProb_nonneg G C hp hp1 hq0 ω)
    (bcProb_sum_eq_one G C hp hp1 hq0)
    (bcProb_FKGLatticeCondition G C hp hp1 hq) hA hB



















theorem bcProb_mono_bc (C' : SimpleGraph V) [DecidableRel C'.Adj] (hCC' : C ≤ C')
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (Sym2 V))} (hA : IsIncreasing A) :
    (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G C p q ω)
      ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G C' p q ω := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  refine holley_dominates ?_ ?_ ?_ ?_ hA
  · exact fun ω => bcProb_nonneg G C hp hp1 hq0 ω
  · exact fun ω => bcProb_nonneg G C' hp hp1 hq0 ω
  · rw [bcProb_sum_eq_one G C hp hp1 hq0, bcProb_sum_eq_one G C' hp hp1 hq0]
  · exact fun a b => bcProb_cross G C C' hCC' hp hp1 hq a b

end FK

end StatMech
