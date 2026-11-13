/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.SixVertexBetheZeroPhase

open Finset

namespace StatMech.FrontierD

noncomputable section



theorem sixVertexBethePhase_ne_one_of_mem_Ioo_of_ne_zero
    {p : Real} (hp : p ∈ Set.Ioo (-Real.pi) Real.pi) (hne : p ≠ 0) :
    sixVertexBethePhase p ≠ 1 := by
  intro hphase
  have hphase0 : sixVertexBethePhase p = sixVertexBethePhase 0 := by
    simpa [sixVertexBethePhase] using hphase
  exact hne (sixVertexBethePhase_injective_on_Ioo hp
    ⟨neg_lt_zero.mpr Real.pi_pos, Real.pi_pos⟩ hphase0)



theorem sixVertexFixedChargeBetheRoots_phase_ne_one_of_odd_charge_of_ne
    {c : Real} (hc : 2 < c) {r : Nat} (hr : Odd r) (k : Nat)
    {j : Fin (sixVertexFixedChargeBetheParticleCount r k)}
    (hj : j ≠ sixVertexFixedChargeBetheCentralIndex r k) :
    sixVertexBethePhase (sixVertexFixedChargeBetheRoots hc r k j) ≠ 1 := by
  apply sixVertexBethePhase_ne_one_of_mem_Ioo_of_ne_zero
    ((sixVertexFixedChargeBetheRoots_mem_open hc r k).2.2 j)
  intro hjzero
  have hcentral :=
    sixVertexFixedChargeBetheRoots_central_eq_zero_of_odd_charge hc hr k
  exact hj ((sixVertexFixedChargeBetheRoots_mem_open hc r k).1.injective
    (hjzero.trans hcentral.symm))

end

end StatMech.FrontierD
