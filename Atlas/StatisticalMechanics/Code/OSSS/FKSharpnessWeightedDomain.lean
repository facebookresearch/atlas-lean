/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.OSSS.FKSharpnessWeightedPeriodic
import Code.FK.MonoBC

open scoped BigOperators Classical
open Finset Set

set_option linter.unusedSectionVars false

namespace StatMech
namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (C : SimpleGraph V) [DecidableRel C.Adj]


noncomputable def bcWeightW (pf : Sym2 V -> Real) (q : Real)
    (omega : ConfigSpace (Sym2 V)) : Real :=
  edgeProductW G pf omega * q ^ numClustersBC G C omega


noncomputable def bcZW (pf : Sym2 V -> Real) (q : Real) : Real :=
  ∑ omega, bcWeightW G C pf q omega


noncomputable def bcProbW (pf : Sym2 V -> Real) (q : Real)
    (omega : ConfigSpace (Sym2 V)) : Real :=
  bcWeightW G C pf q omega / bcZW G C pf q

theorem bcWeightW_pos {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 0 < q) (omega : ConfigSpace (Sym2 V)) :
    0 < bcWeightW G C pf q omega := by
  exact mul_pos (edgeProductW_pos G hpf hpf1 omega) (pow_pos hq _)

theorem bcWeightW_nonneg {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 0 < q) (omega : ConfigSpace (Sym2 V)) :
    0 <= bcWeightW G C pf q omega :=
  (bcWeightW_pos G C hpf hpf1 hq omega).le

theorem bcZW_pos {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 0 < q) : 0 < bcZW G C pf q := by
  unfold bcZW
  exact Finset.sum_pos (fun omega _ => bcWeightW_pos G C hpf hpf1 hq omega)
    Finset.univ_nonempty

theorem bcProbW_nonneg {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 0 < q) (omega : ConfigSpace (Sym2 V)) :
    0 <= bcProbW G C pf q omega := by
  exact div_nonneg (bcWeightW_nonneg G C hpf hpf1 hq omega)
    (bcZW_pos G C hpf hpf1 hq).le

theorem bcProbW_sum_eq_one {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 0 < q) :
    ∑ omega, bcProbW G C pf q omega = 1 := by
  unfold bcProbW bcZW
  rw [← Finset.sum_div]
  exact div_self (bcZW_pos G C hpf hpf1 hq).ne'



theorem bcWeightW_cross_bc (C' : SimpleGraph V) [DecidableRel C'.Adj]
    (hCC' : C <= C') {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 1 <= q) (a b : ConfigSpace (Sym2 V)) :
    bcWeightW G C pf q a * bcWeightW G C' pf q b <=
      bcWeightW G C pf q (a ⊓ b) * bcWeightW G C' pf q (a ⊔ b) := by
  have hcluster :
      q ^ numClustersBC G C a * q ^ numClustersBC G C' b <=
        q ^ numClustersBC G C (a ⊓ b) *
          q ^ numClustersBC G C' (a ⊔ b) := by
    rw [← pow_add, ← pow_add]
    exact pow_le_pow_right₀ hq (mixed_supermodular_bc G C C' hCC' a b)
  have hedge := edgeProductW_logModular G pf a b
  have hedge0 : 0 <=
      edgeProductW G pf (a ⊓ b) * edgeProductW G pf (a ⊔ b) :=
    mul_nonneg (edgeProductW_pos G hpf hpf1 _).le
      (edgeProductW_pos G hpf hpf1 _).le
  unfold bcWeightW
  calc
    (edgeProductW G pf a * q ^ numClustersBC G C a) *
          (edgeProductW G pf b * q ^ numClustersBC G C' b) =
        (edgeProductW G pf a * edgeProductW G pf b) *
          (q ^ numClustersBC G C a * q ^ numClustersBC G C' b) := by ring
    _ = (edgeProductW G pf (a ⊓ b) * edgeProductW G pf (a ⊔ b)) *
          (q ^ numClustersBC G C a * q ^ numClustersBC G C' b) := by
        rw [hedge]
        ring
    _ <= (edgeProductW G pf (a ⊓ b) * edgeProductW G pf (a ⊔ b)) *
          (q ^ numClustersBC G C (a ⊓ b) *
            q ^ numClustersBC G C' (a ⊔ b)) :=
        mul_le_mul_of_nonneg_left hcluster hedge0
    _ = (edgeProductW G pf (a ⊓ b) *
          q ^ numClustersBC G C (a ⊓ b)) *
        (edgeProductW G pf (a ⊔ b) *
          q ^ numClustersBC G C' (a ⊔ b)) := by ring

theorem bcProbW_cross_bc (C' : SimpleGraph V) [DecidableRel C'.Adj]
    (hCC' : C <= C') {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 1 <= q) (a b : ConfigSpace (Sym2 V)) :
    bcProbW G C pf q a * bcProbW G C' pf q b <=
      bcProbW G C pf q (a ⊓ b) * bcProbW G C' pf q (a ⊔ b) := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hZ : 0 < bcZW G C pf q := bcZW_pos G C hpf hpf1 hq0
  have hZ' : 0 < bcZW G C' pf q := bcZW_pos G C' hpf hpf1 hq0
  unfold bcProbW
  rw [div_mul_div_comm, div_mul_div_comm,
    div_le_div_iff_of_pos_right (mul_pos hZ hZ')]
  exact bcWeightW_cross_bc G C C' hCC' hpf hpf1 hq a b


theorem bcProbW_mono_bc (C' : SimpleGraph V) [DecidableRel C'.Adj]
    (hCC' : C <= C') {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 1 <= q)
    {A : Set (ConfigSpace (Sym2 V))} (hA : IsIncreasing A) :
    (∑ omega, A.indicator (fun _ => (1 : Real)) omega *
        bcProbW G C pf q omega) <=
      ∑ omega, A.indicator (fun _ => (1 : Real)) omega *
        bcProbW G C' pf q omega := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  refine holley_dominates ?_ ?_ ?_ ?_ hA
  · exact fun omega => bcProbW_nonneg G C hpf hpf1 hq0 omega
  · exact fun omega => bcProbW_nonneg G C' hpf hpf1 hq0 omega
  · rw [bcProbW_sum_eq_one G C hpf hpf1 hq0,
      bcProbW_sum_eq_one G C' hpf hpf1 hq0]
  · exact fun a b => bcProbW_cross_bc G C C' hCC' hpf hpf1 hq a b





noncomputable def inducedBcZW (pf : Sym2 V -> Real) (q : Real)
    (F : Finset (Sym2 V)) (psi : ConfigSpace (Sym2 V)) : Real :=
  ∑ rho ∈ condFibre F psi, bcWeightW G C pf q rho

theorem inducedBcZW_pos {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 0 < q) (F : Finset (Sym2 V))
    (psi : ConfigSpace (Sym2 V)) : 0 < inducedBcZW G C pf q F psi := by
  unfold inducedBcZW
  exact Finset.sum_pos (fun rho _ => bcWeightW_pos G C hpf hpf1 hq rho)
    ⟨psi, self_mem_condFibre F psi⟩



noncomputable def condBcProbW (pf : Sym2 V -> Real) (q : Real)
    (F : Finset (Sym2 V)) (psi omega : ConfigSpace (Sym2 V)) : Real :=
  if AgreesOff F psi omega then
    bcWeightW G C pf q omega / inducedBcZW G C pf q F psi
  else 0

theorem condBcProbW_nonneg {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 0 < q) (F : Finset (Sym2 V))
    (psi : ConfigSpace (Sym2 V)) :
    (0 : ConfigSpace (Sym2 V) -> Real) <= condBcProbW G C pf q F psi := by
  intro omega
  unfold condBcProbW
  split
  · exact div_nonneg (bcWeightW_nonneg G C hpf hpf1 hq omega)
      (inducedBcZW_pos G C hpf hpf1 hq F psi).le
  · rfl

theorem condBcProbW_sum_eq_one {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 0 < q) (F : Finset (Sym2 V))
    (psi : ConfigSpace (Sym2 V)) :
    ∑ omega, condBcProbW G C pf q F psi omega = 1 := by
  unfold condBcProbW
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, ← Finset.sum_div]
  exact div_self (inducedBcZW_pos G C hpf hpf1 hq F psi).ne'

theorem condBcProbW_cross_bc (C' : SimpleGraph V) [DecidableRel C'.Adj]
    (hCC' : C <= C') {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 1 <= q) (F : Finset (Sym2 V))
    (psi a b : ConfigSpace (Sym2 V)) :
    condBcProbW G C pf q F psi a * condBcProbW G C' pf q F psi b <=
      condBcProbW G C pf q F psi (a ⊓ b) *
        condBcProbW G C' pf q F psi (a ⊔ b) := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hright : 0 <=
      condBcProbW G C pf q F psi (a ⊓ b) *
        condBcProbW G C' pf q F psi (a ⊔ b) :=
    mul_nonneg (condBcProbW_nonneg G C hpf hpf1 hq0 F psi _)
      (condBcProbW_nonneg G C' hpf hpf1 hq0 F psi _)
  unfold condBcProbW
  by_cases ha : AgreesOff F psi a
  · by_cases hb : AgreesOff F psi b
    · rw [if_pos ha, if_pos hb, if_pos (agreesOff_inf ha hb),
        if_pos (agreesOff_sup ha hb), div_mul_div_comm, div_mul_div_comm,
        div_le_div_iff_of_pos_right
          (mul_pos (inducedBcZW_pos G C hpf hpf1 hq0 F psi)
            (inducedBcZW_pos G C' hpf hpf1 hq0 F psi))]
      exact bcWeightW_cross_bc G C C' hCC' hpf hpf1 hq a b
    · rw [if_neg hb, mul_zero]
      simpa only [condBcProbW] using hright
  · rw [if_neg ha, zero_mul]
    simpa only [condBcProbW] using hright



theorem condBcProbW_mono_bc (C' : SimpleGraph V) [DecidableRel C'.Adj]
    (hCC' : C <= C') {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 1 <= q) (F : Finset (Sym2 V))
    (psi : ConfigSpace (Sym2 V))
    {A : Set (ConfigSpace (Sym2 V))} (hA : IsIncreasing A) :
    (∑ omega, A.indicator (fun _ => (1 : Real)) omega *
        condBcProbW G C pf q F psi omega) <=
      ∑ omega, A.indicator (fun _ => (1 : Real)) omega *
        condBcProbW G C' pf q F psi omega := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  refine holley_dominates ?_ ?_ ?_ ?_ hA
  · exact condBcProbW_nonneg G C hpf hpf1 hq0 F psi
  · exact condBcProbW_nonneg G C' hpf hpf1 hq0 F psi
  · rw [condBcProbW_sum_eq_one G C hpf hpf1 hq0 F psi,
      condBcProbW_sum_eq_one G C' hpf hpf1 hq0 F psi]
  · exact fun a b =>
      condBcProbW_cross_bc G C C' hCC' hpf hpf1 hq F psi a b



theorem activeBCProb_mono_bc (C' : SimpleGraph V) [DecidableRel C'.Adj]
    (hCC' : C <= C') {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 1 <= q)
    {A : Set (ConfigSpace G.edgeSet)} (hA : IsIncreasing A) :
    (∑ omega, A.indicator (fun _ => (1 : Real)) omega *
        activeBCProb G C pf q omega) <=
      ∑ omega, A.indicator (fun _ => (1 : Real)) omega *
        activeBCProb G C' pf q omega := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  refine holley_dominates ?_ ?_ ?_ ?_ hA
  · exact fun omega => (activeBCProb_pos G C hpf hpf1 hq0 omega).le
  · exact fun omega => (activeBCProb_pos G C' hpf hpf1 hq0 omega).le
  · rw [activeBCProb_sum_eq_one G C hpf hpf1 hq0,
      activeBCProb_sum_eq_one G C' hpf hpf1 hq0]
  · intro a b
    have hcluster :
        q ^ numClustersBC G C (extendActive G a) *
            q ^ numClustersBC G C' (extendActive G b) <=
          q ^ numClustersBC G C (extendActive G (a ⊓ b)) *
            q ^ numClustersBC G C' (extendActive G (a ⊔ b)) := by
      rw [extendActive_inf, extendActive_sup, ← pow_add, ← pow_add]
      exact pow_le_pow_right₀ hq
        (mixed_supermodular_bc G C C' hCC' (extendActive G a) (extendActive G b))
    have hedge := edgeProductW_logModular G pf
      (extendActive G a) (extendActive G b)
    have hedge' : edgeProductW G pf (extendActive G a) *
        edgeProductW G pf (extendActive G b) =
          edgeProductW G pf (extendActive G (a ⊓ b)) *
            edgeProductW G pf (extendActive G (a ⊔ b)) := by
      rw [hedge, extendActive_inf, extendActive_sup]
      ring
    have hedge0 : 0 <= edgeProductW G pf (extendActive G (a ⊓ b)) *
        edgeProductW G pf (extendActive G (a ⊔ b)) :=
      mul_nonneg (edgeProductW_pos G hpf hpf1 _).le
        (edgeProductW_pos G hpf hpf1 _).le
    have hweight : activeBCWeight G C pf q a * activeBCWeight G C' pf q b <=
        activeBCWeight G C pf q (a ⊓ b) * activeBCWeight G C' pf q (a ⊔ b) := by
      unfold activeBCWeight
      calc
        (edgeProductW G pf (extendActive G a) *
              q ^ numClustersBC G C (extendActive G a)) *
            (edgeProductW G pf (extendActive G b) *
              q ^ numClustersBC G C' (extendActive G b)) =
          (edgeProductW G pf (extendActive G a) *
              edgeProductW G pf (extendActive G b)) *
            (q ^ numClustersBC G C (extendActive G a) *
              q ^ numClustersBC G C' (extendActive G b)) := by ring
        _ = (edgeProductW G pf (extendActive G (a ⊓ b)) *
              edgeProductW G pf (extendActive G (a ⊔ b))) *
            (q ^ numClustersBC G C (extendActive G a) *
              q ^ numClustersBC G C' (extendActive G b)) := by
            rw [hedge']
        _ <= (edgeProductW G pf (extendActive G (a ⊓ b)) *
              edgeProductW G pf (extendActive G (a ⊔ b))) *
            (q ^ numClustersBC G C (extendActive G (a ⊓ b)) *
              q ^ numClustersBC G C' (extendActive G (a ⊔ b))) :=
            mul_le_mul_of_nonneg_left hcluster hedge0
        _ = (edgeProductW G pf (extendActive G (a ⊓ b)) *
              q ^ numClustersBC G C (extendActive G (a ⊓ b))) *
            (edgeProductW G pf (extendActive G (a ⊔ b)) *
              q ^ numClustersBC G C' (extendActive G (a ⊔ b))) := by ring
    have hZ : 0 < activeBCZ G C pf q := activeBCZ_pos G C hpf hpf1 hq0
    have hZ' : 0 < activeBCZ G C' pf q := activeBCZ_pos G C' hpf hpf1 hq0
    unfold activeBCProb
    rw [div_mul_div_comm, div_mul_div_comm,
      div_le_div_iff_of_pos_right (mul_pos hZ hZ')]
    exact hweight



theorem bcWeightW_eq_of_edges (pf : Sym2 V -> Real) (q : Real)
    (omega eta : ConfigSpace (Sym2 V))
    (h : forall e, e ∈ G.edgeFinset -> omega e = eta e) :
    bcWeightW G C pf q omega = bcWeightW G C pf q eta := by
  unfold bcWeightW
  rw [numClustersBC_eq_of_edges G C omega eta h]
  congr 1
  unfold edgeProductW
  exact Finset.prod_congr rfl (fun e he => by rw [h e he])

theorem bcWeightW_activeSplitEquiv_symm (pf : Sym2 V -> Real) (q : Real)
    (eta : ConfigSpace G.edgeSet)
    (xi : ConfigSpace {e : Sym2 V // e ∉ G.edgeSet}) :
    bcWeightW G C pf q ((activeSplitEquiv G).symm (eta, xi)) =
      activeBCWeight G C pf q eta := by
  apply bcWeightW_eq_of_edges G C
  intro e he
  have heSet : e ∈ G.edgeSet := by
    rwa [← SimpleGraph.mem_edgeFinset]
  rw [show ((activeSplitEquiv G).symm (eta, xi)) e = eta ⟨e, heSet⟩ by
    simp [activeSplitEquiv, Equiv.piEquivPiSubtypeProd_symm_apply, heSet]]
  exact (extendActive_apply G eta ⟨e, heSet⟩).symm

theorem activeBCZW_factorization (pf : Sym2 V -> Real) (q : Real) :
    bcZW G C pf q = 2 ^ ecz_NE G * activeBCZ G C pf q := by
  rw [bcZW, ← Equiv.sum_comp (activeSplitEquiv G).symm
    (fun omega => bcWeightW G C pf q omega), Fintype.sum_prod_type]
  have key : forall eta : ConfigSpace G.edgeSet,
      (∑ xi : ConfigSpace {e : Sym2 V // e ∉ G.edgeSet},
        bcWeightW G C pf q ((activeSplitEquiv G).symm (eta, xi))) =
      2 ^ ecz_NE G * activeBCWeight G C pf q eta := by
    intro eta
    rw [Finset.sum_congr rfl (fun xi _ =>
      bcWeightW_activeSplitEquiv_symm G C pf q eta xi)]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      card_inactive_config G]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun eta _ => key eta), ← Finset.mul_sum]
  rfl

theorem activeBCNumerW_factorization (pf : Sym2 V -> Real) (q : Real)
    (f : ConfigSpace G.edgeSet -> Real) :
    (∑ omega : ConfigSpace (Sym2 V),
      f (restrictActive G omega) * bcWeightW G C pf q omega) =
      2 ^ ecz_NE G * activeBCNumer G C pf q f := by
  rw [← Equiv.sum_comp (activeSplitEquiv G).symm
    (fun omega => f (restrictActive G omega) * bcWeightW G C pf q omega),
    Fintype.sum_prod_type]
  have key : forall eta : ConfigSpace G.edgeSet,
      (∑ xi : ConfigSpace {e : Sym2 V // e ∉ G.edgeSet},
        f (restrictActive G ((activeSplitEquiv G).symm (eta, xi))) *
          bcWeightW G C pf q ((activeSplitEquiv G).symm (eta, xi))) =
      2 ^ ecz_NE G * (f eta * activeBCWeight G C pf q eta) := by
    intro eta
    rw [Finset.sum_congr rfl (fun xi _ => by
      rw [restrictActive_activeSplitEquiv_symm,
        bcWeightW_activeSplitEquiv_symm G C pf q eta xi])]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      card_inactive_config G]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun eta _ => key eta), ← Finset.mul_sum]
  rfl


theorem activeBCMean_eq_bcProbW_lift {pf : Sym2 V -> Real}
    (hpf : forall e, 0 < pf e) (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 0 < q) (f : ConfigSpace G.edgeSet -> Real) :
    activeBCMean G C pf q f =
      ∑ omega : ConfigSpace (Sym2 V),
        f (restrictActive G omega) * bcProbW G C pf q omega := by
  have htwo : (2 : Real) ^ ecz_NE G ≠ 0 := by positivity
  have hZactive : activeBCZ G C pf q ≠ 0 :=
    (activeBCZ_pos G C hpf hpf1 hq).ne'
  rw [activeBCMean_eq_div]
  unfold bcProbW
  rw [show (fun omega : ConfigSpace (Sym2 V) =>
      f (restrictActive G omega) *
        (bcWeightW G C pf q omega / bcZW G C pf q)) =
      (fun omega =>
        (f (restrictActive G omega) * bcWeightW G C pf q omega) /
          bcZW G C pf q) by funext omega; ring]
  rw [← Finset.sum_div, activeBCNumerW_factorization G C,
    activeBCZW_factorization G C]
  field_simp



variable {Vin Vout : Type*} [Fintype Vin] [Fintype Vout]
variable [DecidableEq Vin] [DecidableEq Vout]
variable (Gin : SimpleGraph Vin) [DecidableRel Gin.Adj]
variable (Gout : SimpleGraph Vout) [DecidableRel Gout.Adj]
variable (iota : Vin -> Vout)
variable (bdryOut : Vout -> Prop) [DecidablePred bdryOut]



def ocd_ParamCompatible (pfIn : Sym2 Vin -> Real)
    (pfOut : Sym2 Vout -> Real) : Prop :=
  forall e, pfIn e = pfOut (ocd_innerEdge iota e)


noncomputable def ocd_psiEdgeFactorW (pfOut : Sym2 Vout -> Real)
    (psi : ConfigSpace (Sym2 Vout)) : Real :=
  ∏ e ∈ Gout.edgeFinset.filter
      (fun e => e ∉ Set.range (ocd_innerEdge iota)),
    if psi e then pfOut e else 1 - pfOut e

theorem ocd_psiEdgeFactorW_pos {pfOut : Sym2 Vout -> Real}
    (hpf : forall e, 0 < pfOut e) (hpf1 : forall e, pfOut e < 1)
    (psi : ConfigSpace (Sym2 Vout)) :
    0 < ocd_psiEdgeFactorW Gout iota pfOut psi := by
  unfold ocd_psiEdgeFactorW
  apply Finset.prod_pos
  intro e he
  split
  · exact hpf e
  · linarith [hpf1 e]



theorem ocd_edgeProductW_psiExt (hiota : Function.Injective iota)
    (hadjm : ocd_AdjMatch Gin Gout iota)
    {pfIn : Sym2 Vin -> Real} {pfOut : Sym2 Vout -> Real}
    (hparam : ocd_ParamCompatible iota pfIn pfOut)
    (psi : ConfigSpace (Sym2 Vout)) (omega : ConfigSpace (Sym2 Vin)) :
    edgeProductW Gout pfOut (ocd_psiExt iota psi omega) =
      edgeProductW Gin pfIn omega *
        ocd_psiEdgeFactorW Gout iota pfOut psi := by
  classical
  unfold edgeProductW ocd_psiEdgeFactorW
  rw [← Finset.prod_filter_mul_prod_filter_not Gout.edgeFinset
    (fun e => e ∈ Set.range (ocd_innerEdge iota))]
  congr 1
  · rw [← ocd_innerEdge_image_edgeFinset hiota hadjm,
      Finset.prod_image
        (fun a _ b _ h => ocd_innerEdge_injective iota hiota h)]
    refine Finset.prod_congr rfl (fun e he => ?_)
    rw [ocd_psiExt_innerEdge hiota, ← hparam e]
  · refine Finset.prod_congr rfl (fun e he => ?_)
    rw [Finset.mem_filter] at he
    rw [ocd_psiExt_eq_psi_of_not_range psi omega he.2]


noncomputable def ocd_psiShiftW (pfOut : Sym2 Vout -> Real)
    (psi : ConfigSpace (Sym2 Vout)) (q : Real) : Real :=
  ocd_psiEdgeFactorW Gout iota pfOut psi *
    q ^ ocd_outsideShift Gout iota bdryOut psi

theorem ocd_psiShiftW_pos {pfOut : Sym2 Vout -> Real}
    (hpf : forall e, 0 < pfOut e) (hpf1 : forall e, pfOut e < 1)
    {q : Real} (hq : 0 < q) (psi : ConfigSpace (Sym2 Vout)) :
    0 < ocd_psiShiftW Gout iota bdryOut pfOut psi q := by
  exact mul_pos (ocd_psiEdgeFactorW_pos Gout iota hpf hpf1 psi)
    (pow_pos hq _)


theorem ocd_bcWeightW_psiExt (hiota : Function.Injective iota)
    (hadjm : ocd_AdjMatch Gin Gout iota)
    {pfIn : Sym2 Vin -> Real} {pfOut : Sym2 Vout -> Real}
    (hparam : ocd_ParamCompatible iota pfIn pfOut)
    (psi : ConfigSpace (Sym2 Vout)) (omega : ConfigSpace (Sym2 Vin))
    (q : Real) :
    bcWeightW Gout (Lattice.boundaryCliqueGraph bdryOut) pfOut q
        (ocd_psiExt iota psi omega) =
      bcWeightW Gin (ocd_inducedWiring Gout iota bdryOut psi) pfIn q omega *
        ocd_psiShiftW Gout iota bdryOut pfOut psi q := by
  rw [bcWeightW, ocd_numClustersBC_psiExt hiota hadjm,
    ocd_edgeProductW_psiExt Gin Gout iota hiota hadjm hparam,
    bcWeightW, ocd_psiShiftW, pow_add]
  ring



theorem ocd_inducedBcZW_psi (hiota : Function.Injective iota)
    (hadjm : ocd_AdjMatch Gin Gout iota)
    {pfIn : Sym2 Vin -> Real} {pfOut : Sym2 Vout -> Real}
    (hparam : ocd_ParamCompatible iota pfIn pfOut)
    (psi : ConfigSpace (Sym2 Vout)) (q : Real) :
    inducedBcZW Gout (Lattice.boundaryCliqueGraph bdryOut) pfOut q
        (ocd_innerEdgeFinset (Vin := Vin) iota) psi =
      bcZW Gin (ocd_inducedWiring Gout iota bdryOut psi) pfIn q *
        ocd_psiShiftW Gout iota bdryOut pfOut psi q := by
  rw [inducedBcZW, ocd_condFibre_eq_image_psiExt hiota,
    Finset.sum_image (fun a _ b _ h => by
      have hab := congrArg (ocd_innerRestrict iota) h
      rwa [ocd_innerRestrict_psiExt hiota,
        ocd_innerRestrict_psiExt hiota] at hab),
    bcZW, Finset.sum_mul]
  exact Finset.sum_congr rfl
    (fun omega _ => ocd_bcWeightW_psiExt Gin Gout iota bdryOut
      hiota hadjm hparam psi omega q)


theorem ocd_condBcProbW_psiExt_eq_bcProbW
    (hiota : Function.Injective iota)
    (hadjm : ocd_AdjMatch Gin Gout iota)
    {pfIn : Sym2 Vin -> Real} {pfOut : Sym2 Vout -> Real}
    (hparam : ocd_ParamCompatible iota pfIn pfOut)
    (hpfOut : forall e, 0 < pfOut e)
    (hpfOut1 : forall e, pfOut e < 1) {q : Real} (hq : 0 < q)
    (psi : ConfigSpace (Sym2 Vout)) (omega : ConfigSpace (Sym2 Vin)) :
    condBcProbW Gout (Lattice.boundaryCliqueGraph bdryOut) pfOut q
        (ocd_innerEdgeFinset (Vin := Vin) iota) psi
        (ocd_psiExt iota psi omega) =
      bcProbW Gin (ocd_inducedWiring Gout iota bdryOut psi) pfIn q omega := by
  rw [condBcProbW, if_pos (ocd_agreesOff_psiExt psi omega),
    ocd_bcWeightW_psiExt Gin Gout iota bdryOut hiota hadjm hparam,
    ocd_inducedBcZW_psi Gin Gout iota bdryOut hiota hadjm hparam,
    bcProbW,
    mul_div_mul_right _ _
      (ocd_psiShiftW_pos Gout iota bdryOut hpfOut hpfOut1 hq psi).ne']


theorem ocd_condBcProbW_psiExt_sum_eq_inducedBox
    (hiota : Function.Injective iota)
    (hadjm : ocd_AdjMatch Gin Gout iota)
    {pfIn : Sym2 Vin -> Real} {pfOut : Sym2 Vout -> Real}
    (hparam : ocd_ParamCompatible iota pfIn pfOut)
    (hpfOut : forall e, 0 < pfOut e)
    (hpfOut1 : forall e, pfOut e < 1) {q : Real} (hq : 0 < q)
    (psi : ConfigSpace (Sym2 Vout))
    (B : Set (ConfigSpace (Sym2 Vout))) :
    (∑ rho, B.indicator (fun _ => (1 : Real)) rho *
        condBcProbW Gout (Lattice.boundaryCliqueGraph bdryOut) pfOut q
          (ocd_innerEdgeFinset (Vin := Vin) iota) psi rho) =
      ∑ omega : ConfigSpace (Sym2 Vin),
        (ocd_psiExt iota psi ⁻¹' B).indicator (fun _ => (1 : Real)) omega *
          bcProbW Gin (ocd_inducedWiring Gout iota bdryOut psi)
            pfIn q omega := by
  classical
  have hsupp : forall rho, rho ∉
      condFibre (ocd_innerEdgeFinset (Vin := Vin) iota) psi ->
      B.indicator (fun _ => (1 : Real)) rho *
        condBcProbW Gout (Lattice.boundaryCliqueGraph bdryOut) pfOut q
          (ocd_innerEdgeFinset (Vin := Vin) iota) psi rho = 0 := by
    intro rho hrho
    rw [mem_condFibre] at hrho
    unfold condBcProbW
    rw [if_neg hrho, mul_zero]
  rw [← Finset.sum_subset
    (Finset.subset_univ
      (condFibre (ocd_innerEdgeFinset (Vin := Vin) iota) psi))
    (fun rho _ hrho => hsupp rho hrho)]
  rw [ocd_condFibre_eq_image_psiExt hiota]
  rw [Finset.sum_image (fun a _ b _ hab => by
    have h := congrArg (ocd_innerRestrict iota) hab
    rwa [ocd_innerRestrict_psiExt hiota,
      ocd_innerRestrict_psiExt hiota] at h)]
  apply Finset.sum_congr rfl
  intro omega homega
  rw [ocd_condBcProbW_psiExt_eq_bcProbW Gin Gout iota bdryOut
    hiota hadjm hparam hpfOut hpfOut1 hq psi omega]
  by_cases hB : ocd_psiExt iota psi omega ∈ B
  · rw [Set.indicator_of_mem hB,
      Set.indicator_of_mem (Set.mem_preimage.mpr hB)]
  · rw [Set.indicator_of_notMem hB,
      Set.indicator_of_notMem (fun h => hB (Set.mem_preimage.mp h))]


theorem ocd_condBcProbW_psiExt_dominated
    (hiota : Function.Injective iota)
    (hadjm : ocd_AdjMatch Gin Gout iota)
    (bdryIn : Vin -> Prop) [DecidablePred bdryIn]
    {pfIn : Sym2 Vin -> Real} {pfOut : Sym2 Vout -> Real}
    (hparam : ocd_ParamCompatible iota pfIn pfOut)
    (hpfIn : forall e, 0 < pfIn e) (hpfIn1 : forall e, pfIn e < 1)
    (hpfOut : forall e, 0 < pfOut e)
    (hpfOut1 : forall e, pfOut e < 1)
    {q : Real} (hq : 1 <= q) (psi : ConfigSpace (Sym2 Vout))
    (hwire : ocd_inducedWiring Gout iota bdryOut psi <=
      Lattice.boundaryCliqueGraph bdryIn)
    {A : Set (ConfigSpace (Sym2 Vin))} (hA : IsIncreasing A) :
    (∑ rho, (ocd_innerRestrict iota ⁻¹' A).indicator
          (fun _ => (1 : Real)) rho *
        condBcProbW Gout (Lattice.boundaryCliqueGraph bdryOut) pfOut q
          (ocd_innerEdgeFinset (Vin := Vin) iota) psi rho) <=
      ∑ omega, A.indicator (fun _ => (1 : Real)) omega *
        bcProbW Gin (Lattice.boundaryCliqueGraph bdryIn) pfIn q omega := by
  rw [ocd_condBcProbW_psiExt_sum_eq_inducedBox Gin Gout iota bdryOut
    hiota hadjm hparam hpfOut hpfOut1 (zero_lt_one.trans_le hq) psi]
  have hpre : ocd_psiExt iota psi ⁻¹'
      (ocd_innerRestrict iota ⁻¹' A) = A := by
    ext omega
    simp only [Set.mem_preimage, ocd_innerRestrict_psiExt hiota]
  rw [hpre]
  exact bcProbW_mono_bc Gin
    (ocd_inducedWiring Gout iota bdryOut psi)
    (Lattice.boundaryCliqueGraph bdryIn) hwire hpfIn hpfIn1 hq hA



theorem ocd_free_le_condBcProbW_innerRestrict
    (hiota : Function.Injective iota)
    (hadjm : ocd_AdjMatch Gin Gout iota)
    {pfIn : Sym2 Vin -> Real} {pfOut : Sym2 Vout -> Real}
    (hparam : ocd_ParamCompatible iota pfIn pfOut)
    (hpfIn : forall e, 0 < pfIn e) (hpfIn1 : forall e, pfIn e < 1)
    (hpfOut : forall e, 0 < pfOut e)
    (hpfOut1 : forall e, pfOut e < 1)
    {q : Real} (hq : 1 <= q) (psi : ConfigSpace (Sym2 Vout))
    {A : Set (ConfigSpace (Sym2 Vin))} (hA : IsIncreasing A) :
    (∑ omega, A.indicator (fun _ => (1 : Real)) omega *
        bcProbW Gin ⊥ pfIn q omega) <=
      ∑ rho, (ocd_innerRestrict iota ⁻¹' A).indicator
          (fun _ => (1 : Real)) rho *
        condBcProbW Gout (Lattice.boundaryCliqueGraph bdryOut) pfOut q
          (ocd_innerEdgeFinset (Vin := Vin) iota) psi rho := by
  rw [ocd_condBcProbW_psiExt_sum_eq_inducedBox Gin Gout iota bdryOut
    hiota hadjm hparam hpfOut hpfOut1 (zero_lt_one.trans_le hq) psi]
  have hpre : ocd_psiExt iota psi ⁻¹'
      (ocd_innerRestrict iota ⁻¹' A) = A := by
    ext omega
    simp only [Set.mem_preimage, ocd_innerRestrict_psiExt hiota]
  rw [hpre]
  exact bcProbW_mono_bc Gin (⊥ : SimpleGraph Vin)
    (ocd_inducedWiring Gout iota bdryOut psi)
    (bot_le : (⊥ : SimpleGraph Vin) <=
      ocd_inducedWiring Gout iota bdryOut psi)
    hpfIn hpfIn1 hq hA



theorem bcProbW_eq_fibreMass_mul_condBcProbW
    {pf : Sym2 V -> Real} (hpf : forall e, 0 < pf e)
    (hpf1 : forall e, pf e < 1) {q : Real} (hq : 0 < q)
    (F : Finset (Sym2 V)) (omega : ConfigSpace (Sym2 V)) :
    bcProbW G C pf q omega =
      (∑ rho ∈ condFibre F omega, bcProbW G C pf q rho) *
        condBcProbW G C pf q F omega omega := by
  unfold condBcProbW
  rw [if_pos (agreesOff_self F omega)]
  unfold bcProbW inducedBcZW bcZW
  have hZ : 0 < ∑ eta, bcWeightW G C pf q eta :=
    bcZW_pos G C hpf hpf1 hq
  have hI : 0 < ∑ rho ∈ condFibre F omega,
      bcWeightW G C pf q rho := by
    exact Finset.sum_pos
      (fun rho _ => bcWeightW_pos G C hpf hpf1 hq rho)
      ⟨omega, self_mem_condFibre F omega⟩
  rw [show (∑ rho ∈ condFibre F omega,
      bcWeightW G C pf q rho / ∑ eta, bcWeightW G C pf q eta) =
      (∑ rho ∈ condFibre F omega, bcWeightW G C pf q rho) /
        (∑ eta, bcWeightW G C pf q eta) by rw [Finset.sum_div]]
  field_simp


theorem ocd_bcProbW_decompose (hiota : Function.Injective iota)
    {pfOut : Sym2 Vout -> Real}
    (hpfOut : forall e, 0 < pfOut e)
    (hpfOut1 : forall e, pfOut e < 1) {q : Real} (hq : 0 < q)
    (B : Set (ConfigSpace (Sym2 Vout))) :
    (∑ rho, B.indicator (fun _ => (1 : Real)) rho *
        bcProbW Gout (Lattice.boundaryCliqueGraph bdryOut) pfOut q rho) =
      ∑ psi ∈ Finset.univ.filter
          (fun psi => ocd_outProj iota psi = psi),
        (∑ sigma ∈ condFibre
            (ocd_innerEdgeFinset (Vin := Vin) iota) psi,
          bcProbW Gout (Lattice.boundaryCliqueGraph bdryOut) pfOut q sigma) *
        (∑ rho, B.indicator (fun _ => (1 : Real)) rho *
          condBcProbW Gout (Lattice.boundaryCliqueGraph bdryOut) pfOut q
            (ocd_innerEdgeFinset (Vin := Vin) iota) psi rho) := by
  classical
  let F := ocd_innerEdgeFinset (Vin := Vin) iota
  rw [← Finset.sum_fiberwise_of_maps_to
    (g := ocd_outProj iota)
    (t := Finset.univ.filter (fun psi => ocd_outProj iota psi = psi))
    (fun rho _ => Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ocd_outProj_idem hiota rho⟩)]
  apply Finset.sum_congr rfl
  intro psi hpsi
  rw [Finset.mem_filter] at hpsi
  rw [ocd_filter_outProj_eq_condFibre hiota psi hpsi.2]
  have hsupp : (∑ rho, B.indicator (fun _ => (1 : Real)) rho *
      condBcProbW Gout (Lattice.boundaryCliqueGraph bdryOut) pfOut q F psi rho) =
      ∑ rho ∈ condFibre F psi,
        B.indicator (fun _ => (1 : Real)) rho *
          condBcProbW Gout (Lattice.boundaryCliqueGraph bdryOut)
            pfOut q F psi rho := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro rho hrho hnot
    rw [mem_condFibre] at hnot
    unfold condBcProbW
    rw [if_neg hnot, mul_zero]
  rw [hsupp, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rho hrho
  rw [mem_condFibre] at hrho
  have hfibre : condFibre F rho = condFibre F psi := by
    ext sigma
    rw [mem_condFibre, mem_condFibre,
      agreesOff_congr (agreesOff_symm hrho)]
  have hcond : condBcProbW Gout
      (Lattice.boundaryCliqueGraph bdryOut) pfOut q F rho rho =
      condBcProbW Gout (Lattice.boundaryCliqueGraph bdryOut)
        pfOut q F psi rho := by
    unfold condBcProbW inducedBcZW
    rw [if_pos (agreesOff_self F rho), if_pos hrho, hfibre]
  have hfac := bcProbW_eq_fibreMass_mul_condBcProbW Gout
    (Lattice.boundaryCliqueGraph bdryOut) hpfOut hpfOut1 hq F rho
  rw [hfibre, hcond] at hfac
  rw [hfac]
  ring



theorem ocd_sum_fibreMassW_eq_one
    (hiota : Function.Injective iota)
    {pfOut : Sym2 Vout -> Real}
    (hpfOut : forall e, 0 < pfOut e)
    (hpfOut1 : forall e, pfOut e < 1)
    {q : Real} (hq : 0 < q) :
    (∑ psi ∈ Finset.univ.filter
        (fun psi => ocd_outProj iota psi = psi),
      ∑ sigma ∈ condFibre
          (ocd_innerEdgeFinset (Vin := Vin) iota) psi,
        bcProbW Gout (Lattice.boundaryCliqueGraph bdryOut)
          pfOut q sigma) = 1 := by
  rw [show (∑ psi ∈ Finset.univ.filter
      (fun psi => ocd_outProj iota psi = psi),
    ∑ sigma ∈ condFibre
        (ocd_innerEdgeFinset (Vin := Vin) iota) psi,
      bcProbW Gout (Lattice.boundaryCliqueGraph bdryOut) pfOut q sigma) =
    ∑ psi ∈ Finset.univ.filter
      (fun psi => ocd_outProj iota psi = psi),
    ∑ sigma ∈ Finset.univ.filter
        (fun rho => ocd_outProj iota rho = psi),
      bcProbW Gout (Lattice.boundaryCliqueGraph bdryOut) pfOut q sigma by
    apply Finset.sum_congr rfl
    intro psi hpsi
    rw [Finset.mem_filter] at hpsi
    rw [ocd_filter_outProj_eq_condFibre hiota psi hpsi.2]]
  rw [Finset.sum_fiberwise_of_maps_to
    (fun rho _ => Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ocd_outProj_idem hiota rho⟩)]
  exact bcProbW_sum_eq_one Gout
    (Lattice.boundaryCliqueGraph bdryOut) hpfOut hpfOut1 hq




theorem ocd_free_inner_dominated_bcProbW
    (hiota : Function.Injective iota)
    (hadjm : ocd_AdjMatch Gin Gout iota)
    {pfIn : Sym2 Vin -> Real} {pfOut : Sym2 Vout -> Real}
    (hparam : ocd_ParamCompatible iota pfIn pfOut)
    (hpfIn : forall e, 0 < pfIn e) (hpfIn1 : forall e, pfIn e < 1)
    (hpfOut : forall e, 0 < pfOut e)
    (hpfOut1 : forall e, pfOut e < 1)
    {q : Real} (hq : 1 <= q)
    {A : Set (ConfigSpace (Sym2 Vin))} (hA : IsIncreasing A) :
    (∑ omega, A.indicator (fun _ => (1 : Real)) omega *
        bcProbW Gin ⊥ pfIn q omega) <=
      ∑ rho, (ocd_innerRestrict iota ⁻¹' A).indicator
          (fun _ => (1 : Real)) rho *
        bcProbW Gout (Lattice.boundaryCliqueGraph bdryOut)
          pfOut q rho := by
  let c := ∑ omega, A.indicator (fun _ => (1 : Real)) omega *
    bcProbW Gin ⊥ pfIn q omega
  rw [ocd_bcProbW_decompose Gout iota bdryOut hiota hpfOut hpfOut1
    (zero_lt_one.trans_le hq) (ocd_innerRestrict iota ⁻¹' A)]
  calc
    c = (∑ psi ∈ Finset.univ.filter
          (fun psi => ocd_outProj iota psi = psi),
        ∑ sigma ∈ condFibre
            (ocd_innerEdgeFinset (Vin := Vin) iota) psi,
          bcProbW Gout (Lattice.boundaryCliqueGraph bdryOut)
            pfOut q sigma) * c := by
      rw [ocd_sum_fibreMassW_eq_one Gout iota bdryOut hiota
        hpfOut hpfOut1 (zero_lt_one.trans_le hq), one_mul]
    _ = ∑ psi ∈ Finset.univ.filter
          (fun psi => ocd_outProj iota psi = psi),
        (∑ sigma ∈ condFibre
            (ocd_innerEdgeFinset (Vin := Vin) iota) psi,
          bcProbW Gout (Lattice.boundaryCliqueGraph bdryOut)
            pfOut q sigma) * c := by
      rw [Finset.sum_mul]
    _ <= ∑ psi ∈ Finset.univ.filter
          (fun psi => ocd_outProj iota psi = psi),
        (∑ sigma ∈ condFibre
            (ocd_innerEdgeFinset (Vin := Vin) iota) psi,
          bcProbW Gout (Lattice.boundaryCliqueGraph bdryOut)
            pfOut q sigma) *
          (∑ rho, (ocd_innerRestrict iota ⁻¹' A).indicator
              (fun _ => (1 : Real)) rho *
            condBcProbW Gout (Lattice.boundaryCliqueGraph bdryOut)
              pfOut q (ocd_innerEdgeFinset (Vin := Vin) iota) psi rho) := by
      apply Finset.sum_le_sum
      intro psi _
      apply mul_le_mul_of_nonneg_left
      · exact ocd_free_le_condBcProbW_innerRestrict
          Gin Gout iota bdryOut hiota hadjm hparam
          hpfIn hpfIn1 hpfOut hpfOut1 hq psi hA
      · exact Finset.sum_nonneg (fun sigma _ =>
          bcProbW_nonneg Gout (Lattice.boundaryCliqueGraph bdryOut)
            hpfOut hpfOut1 (zero_lt_one.trans_le hq) sigma)


theorem ocd_wired_inner_dominated_bcProbW
    (hiota : Function.Injective iota)
    (hadjm : ocd_AdjMatch Gin Gout iota)
    (bdryIn : Vin -> Prop) [DecidablePred bdryIn]
    {pfIn : Sym2 Vin -> Real} {pfOut : Sym2 Vout -> Real}
    (hparam : ocd_ParamCompatible iota pfIn pfOut)
    (hpfIn : forall e, 0 < pfIn e) (hpfIn1 : forall e, pfIn e < 1)
    (hpfOut : forall e, 0 < pfOut e)
    (hpfOut1 : forall e, pfOut e < 1)
    {q : Real} (hq : 1 <= q)
    (hwire : forall psi : ConfigSpace (Sym2 Vout),
      ocd_inducedWiring Gout iota bdryOut psi <=
        Lattice.boundaryCliqueGraph bdryIn)
    {A : Set (ConfigSpace (Sym2 Vin))} (hA : IsIncreasing A) :
    (∑ rho, (ocd_innerRestrict iota ⁻¹' A).indicator
          (fun _ => (1 : Real)) rho *
        bcProbW Gout (Lattice.boundaryCliqueGraph bdryOut) pfOut q rho) <=
      ∑ omega, A.indicator (fun _ => (1 : Real)) omega *
        bcProbW Gin (Lattice.boundaryCliqueGraph bdryIn) pfIn q omega := by
  let c := ∑ omega, A.indicator (fun _ => (1 : Real)) omega *
    bcProbW Gin (Lattice.boundaryCliqueGraph bdryIn) pfIn q omega
  rw [ocd_bcProbW_decompose Gout iota bdryOut hiota hpfOut hpfOut1
    (zero_lt_one.trans_le hq) (ocd_innerRestrict iota ⁻¹' A)]
  calc
    _ <= ∑ psi ∈ Finset.univ.filter
          (fun psi => ocd_outProj iota psi = psi),
        (∑ sigma ∈ condFibre
            (ocd_innerEdgeFinset (Vin := Vin) iota) psi,
          bcProbW Gout (Lattice.boundaryCliqueGraph bdryOut) pfOut q sigma) * c := by
      apply Finset.sum_le_sum
      intro psi hpsi
      apply mul_le_mul_of_nonneg_left
      · exact ocd_condBcProbW_psiExt_dominated Gin Gout iota bdryOut
          hiota hadjm bdryIn hparam hpfIn hpfIn1 hpfOut hpfOut1 hq
          psi (hwire psi) hA
      · exact Finset.sum_nonneg (fun sigma hsigma =>
          bcProbW_nonneg Gout (Lattice.boundaryCliqueGraph bdryOut)
            hpfOut hpfOut1 (zero_lt_one.trans_le hq) sigma)
    _ = (∑ psi ∈ Finset.univ.filter
          (fun psi => ocd_outProj iota psi = psi),
        ∑ sigma ∈ condFibre
            (ocd_innerEdgeFinset (Vin := Vin) iota) psi,
          bcProbW Gout (Lattice.boundaryCliqueGraph bdryOut) pfOut q sigma) * c := by
      rw [Finset.sum_mul]
    _ = c := by
      rw [show (∑ psi ∈ Finset.univ.filter
          (fun psi => ocd_outProj iota psi = psi),
        ∑ sigma ∈ condFibre
            (ocd_innerEdgeFinset (Vin := Vin) iota) psi,
          bcProbW Gout (Lattice.boundaryCliqueGraph bdryOut) pfOut q sigma) = 1 by
        rw [show (∑ psi ∈ Finset.univ.filter
            (fun psi => ocd_outProj iota psi = psi),
          ∑ sigma ∈ condFibre
              (ocd_innerEdgeFinset (Vin := Vin) iota) psi,
            bcProbW Gout (Lattice.boundaryCliqueGraph bdryOut) pfOut q sigma) =
          ∑ psi ∈ Finset.univ.filter
            (fun psi => ocd_outProj iota psi = psi),
          ∑ sigma ∈ Finset.univ.filter
              (fun rho => ocd_outProj iota rho = psi),
            bcProbW Gout (Lattice.boundaryCliqueGraph bdryOut) pfOut q sigma by
          apply Finset.sum_congr rfl
          intro psi hpsi
          rw [Finset.mem_filter] at hpsi
          rw [ocd_filter_outProj_eq_condFibre hiota psi hpsi.2]]
        rw [Finset.sum_fiberwise_of_maps_to
          (fun rho _ => Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, ocd_outProj_idem hiota rho⟩)]
        exact bcProbW_sum_eq_one Gout
          (Lattice.boundaryCliqueGraph bdryOut) hpfOut hpfOut1
            (zero_lt_one.trans_le hq), one_mul]


theorem ocd_latticeWired_inner_dominatedW
    {d : Nat} {Sin Sout : Set (Lattice.Site d)}
    [Fintype Sin] [Fintype Sout]
    (iota : {y : Lattice.Site d // y ∈ Sin} ->
      {y : Lattice.Site d // y ∈ Sout})
    (hiotaVal : forall x, (iota x : Lattice.Site d) = (x : Lattice.Site d))
    (hiota : Function.Injective iota)
    (bdryOut : {y : Lattice.Site d // y ∈ Sout} -> Prop)
    [DecidablePred bdryOut]
    (bdryIn : {y : Lattice.Site d // y ∈ Sin} -> Prop)
    [DecidablePred bdryIn]
    (hmargin : forall x : {y : Lattice.Site d // y ∈ Sin},
      ¬ bdryOut (iota x))
    (hbdryIn : forall (x : {y : Lattice.Site d // y ∈ Sin})
      (z : Lattice.Site d), Lattice.NearestNeighbour d (x : Lattice.Site d) z ->
        z ∉ Sin -> bdryIn x)
    {pfIn : Sym2 {y : Lattice.Site d // y ∈ Sin} -> Real}
    {pfOut : Sym2 {y : Lattice.Site d // y ∈ Sout} -> Real}
    (hparam : ocd_ParamCompatible iota pfIn pfOut)
    (hpfIn : forall e, 0 < pfIn e) (hpfIn1 : forall e, pfIn e < 1)
    (hpfOut : forall e, 0 < pfOut e)
    (hpfOut1 : forall e, pfOut e < 1)
    {q : Real} (hq : 1 <= q)
    {A : Set (ConfigSpace (Sym2 {y : Lattice.Site d // y ∈ Sin}))}
    (hA : IsIncreasing A) :
    (∑ rho, (ocd_innerRestrict iota ⁻¹' A).indicator
          (fun _ => (1 : Real)) rho *
        bcProbW (SimpleGraph.comap Subtype.val (Lattice.hypercubicLattice d))
          (Lattice.boundaryCliqueGraph bdryOut) pfOut q rho) <=
      ∑ omega, A.indicator (fun _ => (1 : Real)) omega *
        bcProbW (SimpleGraph.comap Subtype.val (Lattice.hypercubicLattice d))
          (Lattice.boundaryCliqueGraph bdryIn) pfIn q omega := by
  let Gin : SimpleGraph {y : Lattice.Site d // y ∈ Sin} :=
    SimpleGraph.comap Subtype.val (Lattice.hypercubicLattice d)
  let Gout : SimpleGraph {y : Lattice.Site d // y ∈ Sout} :=
    SimpleGraph.comap Subtype.val (Lattice.hypercubicLattice d)
  have hadjm : ocd_AdjMatch Gin Gout iota :=
    ocd_latticeAdjMatch iota hiotaVal
  have hwire := fun psi => ocd_latticeInducedWiring_le
    iota hiotaVal hiota bdryOut bdryIn hmargin hbdryIn psi
  exact ocd_wired_inner_dominated_bcProbW Gin Gout iota bdryOut hiota
    hadjm bdryIn hparam hpfIn hpfIn1 hpfOut hpfOut1 hq hwire hA

end FK
end StatMech

namespace StatMech
namespace OSSS
namespace FKSharpnessWeightedDomain

open Lattice FK
open WiredBoxOffCentre FKSharpnessWeightedPeriodic





theorem weighted_transShellEvent_domain_dominated
    (d R k : Nat) (x : Site d)
    (J : Sym2 (Site d) -> Real) (hJ : forall e, 0 < J e)
    (hsub : fvs_transBox d (2 * k) x ⊆ box d R)
    (hmargin : forall y : fvs_transBoxVerts d (2 * k) x,
      ¬ boxBoundary d R (flc_incl hsub y))
    (hk : 1 <= k) (beta q : Real) (hbeta : 0 < beta) (hq : 1 <= q) :
    (∑ rho,
      (ocd_innerRestrict (flc_incl hsub) ⁻¹' transShellEvent d k x).indicator
          (fun _ => (1 : Real)) rho *
        bcProbW (boxGraph d R) (Lattice.boundaryCliqueGraph (boxBoundary d R))
          (FK.betaParams (boxCoupling J R) beta) q rho) <=
      ∑ eta,
        (transShellEvent d k x).indicator (fun _ => (1 : Real)) eta *
          bcProbW (fvs_transBoxGraph d (2 * k) x)
            (Lattice.boundaryCliqueGraph
              (fvs_transBoxBoundary d (2 * k) x))
            (FK.betaParams (transBoxCoupling J (2 * k) x) beta) q eta := by
  let pfIn := FK.betaParams (transBoxCoupling J (2 * k) x) beta
  let pfOut := FK.betaParams (boxCoupling J R) beta
  have hparam : ocd_ParamCompatible (flc_incl hsub) pfIn pfOut := by
    intro e
    unfold pfIn pfOut FK.betaParams transBoxCoupling boxCoupling
    congr 3
    simp [ocd_innerEdge, Sym2.map_map, flc_incl_val]
  have hpfIn : forall e, 0 < pfIn e :=
    FK.betaParams_pos (fun e => hJ (Sym2.map Subtype.val e)) hbeta
  have hpfIn1 : forall e, pfIn e < 1 :=
    FK.betaParams_lt_one _ beta
  have hpfOut : forall e, 0 < pfOut e :=
    FK.betaParams_pos (fun e => hJ (Sym2.map Subtype.val e)) hbeta
  have hpfOut1 : forall e, pfOut e < 1 :=
    FK.betaParams_lt_one _ beta
  have hdom := ocd_latticeWired_inner_dominatedW
    (Sin := fvs_transBox d (2 * k) x) (Sout := box d R)
    (flc_incl hsub) (flc_incl_val hsub) (flc_incl_injective hsub)
    (boxBoundary d R) (fvs_transBoxBoundary d (2 * k) x)
    hmargin (flc_hbdryIn_transBox (show 1 <= 2 * k by omega) x)
    hparam hpfIn hpfIn1 hpfOut hpfOut1 hq
    (A := transShellEvent d k x) (transShellEvent_increasing d k x)
  simpa [pfIn, pfOut] using hdom

end FKSharpnessWeightedDomain
end OSSS
end StatMech
