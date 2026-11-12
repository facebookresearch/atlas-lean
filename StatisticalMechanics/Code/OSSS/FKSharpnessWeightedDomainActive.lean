/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.OSSS.FKSharpnessWeightedDomain









open Finset Set SimpleGraph

namespace StatMech.FK

noncomputable section

variable {Vin Vout : Type*} [Fintype Vin] [Fintype Vout]
variable [DecidableEq Vin] [DecidableEq Vout]
variable (Gin : SimpleGraph Vin) [DecidableRel Gin.Adj]
variable (Gout : SimpleGraph Vout) [DecidableRel Gout.Adj]
variable (iota : Vin -> Vout)



def ocd_innerRestrictActive
    (hadjm : ocd_AdjMatch Gin Gout iota)
    (rho : ConfigSpace Gout.edgeSet) : ConfigSpace Gin.edgeSet :=
  fun e => rho ⟨ocd_innerEdge iota e.1, by
    have he : e.1 ∈ Gin.edgeSet := e.2
    rw [← e.1.out_eq] at he ⊢
    rw [ocd_innerEdge_mk, SimpleGraph.mem_edgeSet, ← hadjm]
    simpa only [SimpleGraph.mem_edgeSet] using he⟩

@[simp] theorem ocd_innerRestrictActive_restrictActive
    (hadjm : ocd_AdjMatch Gin Gout iota)
    (rho : ConfigSpace (Sym2 Vout)) :
    ocd_innerRestrictActive Gin Gout iota hadjm (restrictActive Gout rho) =
      restrictActive Gin (ocd_innerRestrict iota rho) := by
  rfl



theorem ocd_free_inner_dominated_activeBCMean
    (bdryOut : Vout -> Prop) [DecidablePred bdryOut]
    (hiota : Function.Injective iota)
    (hadjm : ocd_AdjMatch Gin Gout iota)
    {pfIn : Sym2 Vin -> Real} {pfOut : Sym2 Vout -> Real}
    (hparam : ocd_ParamCompatible iota pfIn pfOut)
    (hpfIn : forall e, 0 < pfIn e) (hpfIn1 : forall e, pfIn e < 1)
    (hpfOut : forall e, 0 < pfOut e)
    (hpfOut1 : forall e, pfOut e < 1)
    {q : Real} (hq : 1 <= q)
    {A : Set (ConfigSpace Gin.edgeSet)} (hA : IsIncreasing A) :
    activeBCMean Gin ⊥ pfIn q (A.indicator fun _ => (1 : Real)) <=
      activeBCMean Gout
        (StatMech.Lattice.boundaryCliqueGraph bdryOut) pfOut q
        (fun rho => A.indicator (fun _ => (1 : Real))
          (ocd_innerRestrictActive Gin Gout iota hadjm rho)) := by
  let Afull : Set (ConfigSpace (Sym2 Vin)) := restrictActive Gin ⁻¹' A
  have hAfull : IsIncreasing Afull := by
    intro omega eta homega hmem
    exact hA (fun e => homega e.1) hmem
  have hdom := ocd_free_inner_dominated_bcProbW Gin Gout iota bdryOut
    hiota hadjm hparam hpfIn hpfIn1 hpfOut hpfOut1 hq hAfull
  rw [activeBCMean_eq_bcProbW_lift Gout
      (StatMech.Lattice.boundaryCliqueGraph bdryOut)
      hpfOut hpfOut1 (zero_lt_one.trans_le hq),
    activeBCMean_eq_bcProbW_lift Gin ⊥
      hpfIn hpfIn1 (zero_lt_one.trans_le hq)]
  simpa only [Afull, Set.mem_preimage, Set.indicator_apply,
    ocd_innerRestrictActive_restrictActive] using hdom



theorem ocd_wired_inner_dominated_activeBCMean
    (bdryOut : Vout -> Prop) [DecidablePred bdryOut]
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
        StatMech.Lattice.boundaryCliqueGraph bdryIn)
    {A : Set (ConfigSpace Gin.edgeSet)} (hA : IsIncreasing A) :
    activeBCMean Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut)
        pfOut q
        (fun rho => A.indicator (fun _ => (1 : Real))
          (ocd_innerRestrictActive Gin Gout iota hadjm rho)) <=
      activeBCMean Gin (StatMech.Lattice.boundaryCliqueGraph bdryIn)
        pfIn q (A.indicator fun _ => (1 : Real)) := by
  let Afull : Set (ConfigSpace (Sym2 Vin)) := restrictActive Gin ⁻¹' A
  have hAfull : IsIncreasing Afull := by
    intro omega eta homega hmem
    exact hA (fun e => homega e.1) hmem
  have hdom := ocd_wired_inner_dominated_bcProbW Gin Gout iota bdryOut
    hiota hadjm bdryIn hparam hpfIn hpfIn1 hpfOut hpfOut1 hq hwire hAfull
  rw [activeBCMean_eq_bcProbW_lift Gout
      (StatMech.Lattice.boundaryCliqueGraph bdryOut)
      hpfOut hpfOut1 (zero_lt_one.trans_le hq),
    activeBCMean_eq_bcProbW_lift Gin
      (StatMech.Lattice.boundaryCliqueGraph bdryIn)
      hpfIn hpfIn1 (zero_lt_one.trans_le hq)]
  simpa only [Afull, Set.mem_preimage, Set.indicator_apply,
    ocd_innerRestrictActive_restrictActive] using hdom

end

end StatMech.FK
