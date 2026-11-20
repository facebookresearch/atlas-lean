/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.EdgeMarginal



open SimpleGraph

namespace StatMech.FrontierD

open StatMech.FK

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]



theorem numClustersBC_le_sup_edge_add_one
    (C : SimpleGraph V) [DecidableRel C.Adj]
    (x y : V) (omega : ConfigSpace (Sym2 V)) :
    FK.numClustersBC G C omega <=
      FK.numClustersBC G (C ⊔ SimpleGraph.edge x y) omega + 1 := by
  classical
  unfold FK.numClustersBC
  have h := FK.card_connectedComponent_le_sup_edge
    (FK.openSub G omega ⊔ C) x y
  convert h using 1 <;> ac_rfl



theorem bcEventMass_sup_edge_le_q_mul
    (C : SimpleGraph V) [DecidableRel C.Adj]
    (x y : V) {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (A : Set (ConfigSpace (Sym2 V))) :
    FK.bcEventMass G (C ⊔ SimpleGraph.edge x y) p q A <=
      q * FK.bcEventMass G C p q A := by
  classical
  simpa using FK.bcEventMass_le_qpow G C (C ⊔ SimpleGraph.edge x y)
    (show C <= C ⊔ SimpleGraph.edge x y from le_sup_left)
    hp hp1 hq 1
    (fun omega => numClustersBC_le_sup_edge_add_one G C x y omega)
    (A := A) (fun omega => by
      by_cases homega : omega ∈ A <;> simp [homega])



theorem bcEventMass_add_compl
    (C : SimpleGraph V) [DecidableRel C.Adj]
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (A : Set (ConfigSpace (Sym2 V))) :
    FK.bcEventMass G C p q A + FK.bcEventMass G C p q Aᶜ = 1 := by
  classical
  unfold FK.bcEventMass
  rw [← Finset.sum_add_distrib]
  calc
    (∑ omega : ConfigSpace (Sym2 V),
        (A.indicator (fun _ => (1 : Real)) omega * FK.bcProb G C p q omega +
          (Aᶜ).indicator (fun _ => (1 : Real)) omega * FK.bcProb G C p q omega)) =
        ∑ omega : ConfigSpace (Sym2 V), FK.bcProb G C p q omega := by
      apply Finset.sum_congr rfl
      intro omega _
      by_cases homega : omega ∈ A <;> simp [homega]
    _ = 1 := FK.bcProb_sum_eq_one G C hp hp1 hq




theorem bcEventMass_compl_le_of_equiv
    (C C' : SimpleGraph V) [DecidableRel C.Adj] [DecidableRel C'.Adj]
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (A : Set (ConfigSpace (Sym2 V)))
    (D : ConfigSpace (Sym2 V) ≃ ConfigSpace (Sym2 V))
    (hfailure : ∀ omega, omega ∉ A → D omega ∈ A)
    (hprob : ∀ omega, FK.bcProb G C p q omega <=
      FK.bcProb G C' p q (D omega)) :
    FK.bcEventMass G C p q Aᶜ <= FK.bcEventMass G C' p q A := by
  classical
  unfold FK.bcEventMass
  rw [← Equiv.sum_comp D (fun eta : ConfigSpace (Sym2 V) =>
    A.indicator (fun _ => (1 : Real)) eta * FK.bcProb G C' p q eta)]
  apply Finset.sum_le_sum
  intro omega _
  by_cases homega : omega ∈ A
  · rw [Set.indicator_of_notMem (by simpa using homega)]
    simp only [zero_mul]
    exact mul_nonneg (by
      by_cases hdual : D omega ∈ A <;> simp [hdual])
      (FK.bcProb_nonneg G C' hp hp1 hq (D omega))
  · rw [Set.indicator_of_mem (by simpa using homega),
      Set.indicator_of_mem (hfailure omega homega)]
    simpa using hprob omega




theorem bcEventMass_ge_one_div_one_add_q_of_compl_le_sup_edge
    (C : SimpleGraph V) [DecidableRel C.Adj]
    (x y : V) {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (A : Set (ConfigSpace (Sym2 V)))
    (hdual : FK.bcEventMass G C p q Aᶜ <=
      FK.bcEventMass G (C ⊔ SimpleGraph.edge x y) p q A) :
    1 / (1 + q) <= FK.bcEventMass G C p q A := by
  classical
  let separate := FK.bcEventMass G C p q A
  let merged := FK.bcEventMass G (C ⊔ SimpleGraph.edge x y) p q A
  have hpartition := bcEventMass_add_compl G C hp hp1
    (zero_lt_one.trans_le hq) A
  have hcompl : 1 - separate <= merged := by
    dsimp [separate, merged]
    linarith
  have hmerge : merged <= q * separate := by
    exact bcEventMass_sup_edge_le_q_mul G C x y hp hp1 hq A
  have hden : 0 < 1 + q := by linarith
  rw [div_le_iff₀ hden]
  nlinarith [hcompl.trans hmerge]




theorem bcEventMass_ge_one_div_one_add_mul_of_compl_le_mul_sup_edge
    (C : SimpleGraph V) [DecidableRel C.Adj]
    (x y : V) {p q distortion : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (hdistortion : 0 <= distortion)
    (A : Set (ConfigSpace (Sym2 V)))
    (hdual : FK.bcEventMass G C p q Aᶜ <=
      distortion *
        FK.bcEventMass G (C ⊔ SimpleGraph.edge x y) p q A) :
    1 / (1 + distortion * q) <= FK.bcEventMass G C p q A := by
  classical
  let separate := FK.bcEventMass G C p q A
  let merged := FK.bcEventMass G (C ⊔ SimpleGraph.edge x y) p q A
  have hpartition := bcEventMass_add_compl G C hp hp1
    (zero_lt_one.trans_le hq) A
  have hcompl : 1 - separate <= distortion * merged := by
    dsimp [separate, merged]
    linarith
  have hmerge : distortion * merged <=
      distortion * (q * separate) := by
    exact mul_le_mul_of_nonneg_left
      (bcEventMass_sup_edge_le_q_mul G C x y hp hp1 hq A)
      hdistortion
  have hden : 0 < 1 + distortion * q := by
    have hq0 : 0 <= q := zero_le_one.trans hq
    nlinarith [mul_nonneg hdistortion hq0]
  rw [div_le_iff₀ hden]
  nlinarith [hcompl.trans hmerge]



theorem bcEventMass_ge_one_div_one_add_q_of_dual_equiv
    (C : SimpleGraph V) [DecidableRel C.Adj]
    (x y : V) {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (A : Set (ConfigSpace (Sym2 V)))
    (D : ConfigSpace (Sym2 V) ≃ ConfigSpace (Sym2 V))
    (hfailure : ∀ omega, omega ∉ A → D omega ∈ A)
    (hprob : ∀ omega, FK.bcProb G C p q omega <=
      FK.bcProb G (C ⊔ SimpleGraph.edge x y) p q (D omega)) :
    1 / (1 + q) <= FK.bcEventMass G C p q A := by
  classical
  apply bcEventMass_ge_one_div_one_add_q_of_compl_le_sup_edge
    G C x y hp hp1 hq A
  exact bcEventMass_compl_le_of_equiv G C
    (C ⊔ SimpleGraph.edge x y) hp hp1 (zero_lt_one.trans_le hq)
    A D hfailure hprob




theorem one_div_one_add_q_le_of_compl_le_merged
    {q separate merged : Real} (hq : 1 <= q)
    (hcompl : 1 - separate <= merged)
    (hmerge : merged <= q * separate) :
    1 / (1 + q) <= separate := by
  have hden : 0 < 1 + q := by linarith
  rw [div_le_iff₀ hden]
  nlinarith [hcompl.trans hmerge]


theorem one_div_one_add_mul_le_of_compl_le_mul_merged
    {q distortion separate merged : Real} (hq : 1 <= q)
    (hdistortion : 0 <= distortion)
    (hcompl : 1 - separate <= distortion * merged)
    (hmerge : merged <= q * separate) :
    1 / (1 + distortion * q) <= separate := by
  have hq0 : 0 <= q := zero_le_one.trans hq
  have hdistortedMerge : distortion * merged <=
      distortion * (q * separate) :=
    mul_le_mul_of_nonneg_left hmerge hdistortion
  have hden : 0 < 1 + distortion * q := by
    nlinarith [mul_nonneg hdistortion hq0]
  rw [div_le_iff₀ hden]
  nlinarith [hcompl.trans hdistortedMerge]

end

end StatMech.FrontierD
