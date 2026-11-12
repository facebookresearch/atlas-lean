/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/































import Mathlib
import Code.Foundations.ConfigSpace

open scoped BigOperators

namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]





def openSub (ω : ConfigSpace (Sym2 V)) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ ω s(x, y) = true
  symm := by
    intro x y h
    refine ⟨h.1.symm, ?_⟩
    rw [Sym2.eq_swap]; exact h.2
  loopless := ⟨fun x h => h.1.ne rfl⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp]
theorem openSub_adj (ω : ConfigSpace (Sym2 V)) (x y : V) :
    (openSub G ω).Adj x y ↔ G.Adj x y ∧ ω s(x, y) = true :=
  Iff.rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in


theorem openSub_le (ω : ConfigSpace (Sym2 V)) : openSub G ω ≤ G := fun _ _ h => h.1



instance instDecidableRelOpenSubAdj (ω : ConfigSpace (Sym2 V)) :
    DecidableRel (openSub G ω).Adj := by
  intro x y
  change Decidable (G.Adj x y ∧ ω s(x, y) = true)
  infer_instance





def numClusters (ω : ConfigSpace (Sym2 V)) : ℕ :=
  Fintype.card (openSub G ω).ConnectedComponent




def edgeProduct (p : ℝ) (ω : ConfigSpace (Sym2 V)) : ℝ :=
  ∏ e ∈ G.edgeFinset, (if ω e then p else 1 - p)

omit [DecidableEq V] in


theorem edgeProduct_pos {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (ω : ConfigSpace (Sym2 V)) :
    0 < edgeProduct G p ω := by
  unfold edgeProduct
  apply Finset.prod_pos
  intro e _
  split
  · exact hp
  · linarith



def fkWeight (p q : ℝ) (ω : ConfigSpace (Sym2 V)) : ℝ :=
  edgeProduct G p ω * q ^ numClusters G ω



theorem fkWeight_pos {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (ω : ConfigSpace (Sym2 V)) : 0 < fkWeight G p q ω :=
  mul_pos (edgeProduct_pos G hp hp1 ω) (pow_pos hq _)


theorem fkWeight_nonneg {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (ω : ConfigSpace (Sym2 V)) : 0 ≤ fkWeight G p q ω :=
  (fkWeight_pos G hp hp1 hq ω).le



def fkZ (p q : ℝ) : ℝ :=
  ∑ ω : ConfigSpace (Sym2 V), fkWeight G p q ω



theorem fkZ_pos {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) : 0 < fkZ G p q :=
  Finset.sum_pos (fun ω _ => fkWeight_pos G hp hp1 hq ω) Finset.univ_nonempty

theorem fkZ_ne_zero {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) : fkZ G p q ≠ 0 :=
  (fkZ_pos G hp hp1 hq).ne'


noncomputable def fkProb (p q : ℝ) (ω : ConfigSpace (Sym2 V)) : ℝ :=
  fkWeight G p q ω / fkZ G p q


theorem fkProb_nonneg {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (ω : ConfigSpace (Sym2 V)) : 0 ≤ fkProb G p q ω :=
  div_nonneg (fkWeight_nonneg G hp hp1 hq ω) (fkZ_pos G hp hp1 hq).le


theorem fkProb_pos {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (ω : ConfigSpace (Sym2 V)) : 0 < fkProb G p q ω :=
  div_pos (fkWeight_pos G hp hp1 hq ω) (fkZ_pos G hp hp1 hq)


theorem fkProb_sum_eq_one {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ∑ ω : ConfigSpace (Sym2 V), fkProb G p q ω = 1 := by
  unfold fkProb
  rw [← Finset.sum_div]
  exact div_self (fkZ_ne_zero G hp hp1 hq)




noncomputable def fkPMF {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    PMF (ConfigSpace (Sym2 V)) :=
  PMF.ofFintype (fun ω => ENNReal.ofReal (fkProb G p q ω)) <| by
    rw [← ENNReal.ofReal_sum_of_nonneg fun ω _ => fkProb_nonneg G hp hp1 hq ω,
      fkProb_sum_eq_one G hp hp1 hq]
    simp

@[simp]
theorem fkPMF_apply {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (ω : ConfigSpace (Sym2 V)) :
    fkPMF G hp hp1 hq ω = ENNReal.ofReal (fkProb G p q ω) :=
  PMF.ofFintype_apply _ _




theorem fkWeight_one (p : ℝ) (ω : ConfigSpace (Sym2 V)) :
    fkWeight G p 1 ω = edgeProduct G p ω := by
  unfold fkWeight
  rw [one_pow, mul_one]



theorem fkZ_one (p : ℝ) : fkZ G p 1 = ∑ ω : ConfigSpace (Sym2 V), edgeProduct G p ω := by
  unfold fkZ
  exact Finset.sum_congr rfl fun ω _ => fkWeight_one G p ω

end FK

end StatMech
