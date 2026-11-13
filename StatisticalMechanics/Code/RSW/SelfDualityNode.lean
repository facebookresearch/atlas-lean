/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




















































import Mathlib
import Code.Foundations.ConfigSpace
import Code.FK.RandomCluster
import Code.BeffaraDC.SelfDualValue
import Code.Universality.G3PercDualityFull

open scoped BigOperators ENNReal NNReal
open MeasureTheory

namespace StatMech

namespace RSW














def rsd_dualCoupling (p pStar q : ℝ) : Prop :=
    p * pStar / ((1 - p) * (1 - pStar)) = q




theorem rsd_dualParam_coupling {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    rsd_dualCoupling p (BeffaraDC.dualParam p q) q := by
  unfold rsd_dualCoupling
  
  
  have h := BeffaraDC.dualParam_product_eq hp hp1 hq
  rw [mul_comm p (BeffaraDC.dualParam p q),
    mul_comm (1 - p) (1 - BeffaraDC.dualParam p q)]
  exact h


noncomputable def rsd_selfDualPoint (q : ℝ) : ℝ := Real.sqrt q / (1 + Real.sqrt q)

theorem rsd_selfDualPoint_eq (q : ℝ) :
    rsd_selfDualPoint q = BeffaraDC.selfDualPoint q := rfl


theorem rsd_selfDualPoint_mem_Ioo {q : ℝ} (hq : 0 < q) :
    rsd_selfDualPoint q ∈ Set.Ioo (0 : ℝ) 1 :=
  BeffaraDC.selfDualPoint_mem_Ioo hq




theorem rsd_selfDual_coupling {q : ℝ} (hq : 0 < q) :
    rsd_dualCoupling (rsd_selfDualPoint q) (rsd_selfDualPoint q) q := by
  
  
  have hmem := BeffaraDC.selfDualPoint_mem_Ioo hq
  have hfix : BeffaraDC.dualParam (BeffaraDC.selfDualPoint q) q
      = BeffaraDC.selfDualPoint q := BeffaraDC.selfDualPoint_is_fixed hq
  have h := rsd_dualParam_coupling hmem.1 hmem.2 hq
  show rsd_dualCoupling (BeffaraDC.selfDualPoint q) (BeffaraDC.selfDualPoint q) q
  rwa [hfix] at h





theorem rsd_selfDual_iff {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    BeffaraDC.dualParam p q = p ↔ p = rsd_selfDualPoint q := by
  constructor
  · intro h; exact BeffaraDC.selfDualPoint_unique hp hp1 hq h
  · intro h; subst h; exact BeffaraDC.selfDualPoint_is_fixed hq









inductive rsd_BC : Type
  | wired : rsd_BC
  | free : rsd_BC
deriving DecidableEq



def rsd_dualBC : rsd_BC → rsd_BC
  | .wired => .free
  | .free => .wired

@[simp] theorem rsd_dualBC_wired : rsd_dualBC .wired = .free := rfl
@[simp] theorem rsd_dualBC_free : rsd_dualBC .free = .wired := rfl


@[simp] theorem rsd_dualBC_dualBC (bc : rsd_BC) : rsd_dualBC (rsd_dualBC bc) = bc := by
  cases bc <;> rfl










variable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]





def rsd_edgeCompl (ω : ConfigSpace (Sym2 V)) : ConfigSpace (Sym2 V) := fun e => !(ω e)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in

@[simp] theorem rsd_edgeCompl_invol (ω : ConfigSpace (Sym2 V)) :
    rsd_edgeCompl (rsd_edgeCompl ω) = ω := by
  funext e; simp [rsd_edgeCompl]



def rsd_edgeComplEquiv : ConfigSpace (Sym2 V) ≃ ConfigSpace (Sym2 V) where
  toFun := rsd_edgeCompl (V := V)
  invFun := rsd_edgeCompl (V := V)
  left_inv := rsd_edgeCompl_invol
  right_inv := rsd_edgeCompl_invol

omit [DecidableEq V] in




theorem rsd_edgeProduct_compl (p : ℝ) (ω : ConfigSpace (Sym2 V)) :
    FK.edgeProduct G p (rsd_edgeCompl ω) = FK.edgeProduct G (1 - p) ω := by
  unfold FK.edgeProduct rsd_edgeCompl
  apply Finset.prod_congr rfl
  intro e _
  cases ω e <;> simp





theorem rsd_fkZ_q1_dual (p : ℝ) : FK.fkZ G p 1 = FK.fkZ G (1 - p) 1 := by
  rw [FK.fkZ_one, FK.fkZ_one,
    ← Equiv.sum_comp (rsd_edgeComplEquiv (V := V)) (fun ω => FK.edgeProduct G p ω)]
  apply Finset.sum_congr rfl
  intro ω _
  exact rsd_edgeProduct_compl G p ω










theorem rsd_fkProb_q1_dual (p : ℝ) (ω : ConfigSpace (Sym2 V)) :
    FK.fkProb G p 1 (rsd_edgeCompl ω) = FK.fkProb G (1 - p) 1 ω := by
  unfold FK.fkProb
  rw [FK.fkWeight_one, FK.fkWeight_one, rsd_edgeProduct_compl, rsd_fkZ_q1_dual]










theorem rsd_fkLaw_q1_dual (p : ℝ) (A : Finset (ConfigSpace (Sym2 V))) :
    ∑ ω ∈ A.map (rsd_edgeComplEquiv (V := V)).toEmbedding, FK.fkProb G p 1 ω
      = ∑ ω ∈ A, FK.fkProb G (1 - p) 1 ω := by
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro ω _
  exact rsd_fkProb_q1_dual G p ω







theorem rsd_fkSelfDual_half (ω : ConfigSpace (Sym2 V)) :
    FK.fkProb G (1 / 2) 1 (rsd_edgeCompl ω) = FK.fkProb G (1 / 2) 1 ω := by
  rw [rsd_fkProb_q1_dual]; norm_num






theorem rsd_fkLaw_selfDual_half (A : Finset (ConfigSpace (Sym2 V))) :
    ∑ ω ∈ A.map (rsd_edgeComplEquiv (V := V)).toEmbedding, FK.fkProb G (1 / 2) 1 ω
      = ∑ ω ∈ A, FK.fkProb G (1 / 2) 1 ω := by
  have h := rsd_fkLaw_q1_dual G (1 / 2 : ℝ) A
  rwa [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at h



theorem rsd_selfDualPoint_one : rsd_selfDualPoint 1 = 1 / 2 := by
  unfold rsd_selfDualPoint
  rw [Real.sqrt_one]; norm_num




















theorem rsd_planarDual_law (p : ℝ≥0) (hp : p ≤ 1) :
    Measure.map Lattice.dualConfig (bernoulliProductMeasure p hp)
      = bernoulliProductMeasure (1 - p) tsub_le_self :=
  Universality.map_dualConfig p hp











theorem rsd_planarDual_selfDual_half :
    Measure.map Lattice.dualConfig
        (bernoulliProductMeasure (2⁻¹ : ℝ≥0) Universality.half_le_one)
      = bernoulliProductMeasure (2⁻¹ : ℝ≥0) Universality.half_le_one :=
  Universality.bernoulliProductMeasure_selfDual_half




theorem rsd_planarDual_invol (p : ℝ≥0) (hp : p ≤ 1) :
    Measure.map Lattice.dualConfig
        (Measure.map Lattice.dualConfig (bernoulliProductMeasure p hp))
      = bernoulliProductMeasure p hp :=
  Universality.map_dualConfig_dualConfig p hp



























end RSW

end StatMech
