/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Code.FrontierD.FiniteTwoBranchWeightedTransport
import Code.FrontierD.SixVertexMarkedPairTotalCMonotone









open Finset Matrix Polynomial

namespace StatMech.FrontierD

noncomputable section

local instance physicalPairedBranchDecidableProp (p : Prop) : Decidable p :=
  Classical.propDecidable p

abbrev SixVertexConfigurationPhysicalSource
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) :=
  SixVertexMarkedSectorConfiguration T
      ⟨middle.val - 1, by omega⟩ ×
    SixVertexMarkedSectorConfiguration T
      ⟨middle.val + 1, by omega⟩

abbrev SixVertexConfigurationPhysicalTarget
    (T : EvenTorus) (middle : Fin (T.width + 1)) :=
  SixVertexMarkedSectorConfiguration T middle ×
    SixVertexMarkedSectorConfiguration T middle

def sixVertexConfigurationPairTotalCPhysical
    {T : EvenTorus} {left right : Fin (T.width + 1)}
    (pair : SixVertexMarkedSectorConfiguration T left ×
      SixVertexMarkedSectorConfiguration T right) : Nat :=
  sixVertexTorusCTypeCount pair.1.1 + sixVertexTorusCTypeCount pair.2.1

theorem SixVertexArrows.weight_eq_pow_cTypeCount
    {T : EvenTorus} (omega : SixVertexArrows T) (homega : omega.IceRule)
    (c : Real) :
    omega.weight c = c ^ sixVertexTorusCTypeCount omega := by
  have heval := eval_sixVertexTorusMarkedWeight (c - 2) omega
  have hc : 2 + (c - 2) = c := by ring
  rw [hc] at heval
  rw [← heval, sixVertexTorusMarkedWeight_eq_pow omega homega]
  simp

theorem sum_pow_sixVertexMarkedSectorConfiguration_eq_trace
    (T : EvenTorus) (sector : Fin (T.width + 1)) (c : Real) :
    (∑ omega : SixVertexMarkedSectorConfiguration T sector,
      c ^ sixVertexTorusCTypeCount omega.1) =
      Matrix.trace
        (sixVertexSectorTransfer T.width sector.val c ^ T.height) := by
  calc
    (∑ omega : SixVertexMarkedSectorConfiguration T sector,
        c ^ sixVertexTorusCTypeCount omega.1) =
        ∑ omega : SixVertexMarkedSectorConfiguration T sector,
          omega.1.weight c := by
      apply Finset.sum_congr rfl
      intro omega _
      exact (omega.1.weight_eq_pow_cTypeCount omega.2.1 c).symm
    _ = eval (c - 2)
        (sixVertexMarkedSectorConfigurationPolynomial T sector) := by
      unfold sixVertexMarkedSectorConfigurationPolynomial
      change (∑ omega : SixVertexMarkedSectorConfiguration T sector,
        omega.1.weight c) =
          (evalRingHom (c - 2))
            (∑ omega : SixVertexMarkedSectorConfiguration T sector,
              sixVertexTorusMarkedWeight omega.1)
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro omega _
      have heval := eval_sixVertexTorusMarkedWeight (c - 2) omega.1
      have hc : 2 + (c - 2) = c := by ring
      rw [hc] at heval
      exact heval.symm
    _ = eval (c - 2)
        (sixVertexShiftedSectorTracePolynomial
          T.width T.height sector.val) := by
      rw [sixVertexMarkedSectorConfigurationPolynomial_eq_trace]
    _ = Matrix.trace
        (sixVertexSectorTransfer T.width sector.val c ^ T.height) := by
      rw [eval_sixVertexShiftedSectorTracePolynomial]
      congr 3
      ring

theorem sum_pow_configurationPairTotalC_eq_trace_mul_trace
    (T : EvenTorus) (left right : Fin (T.width + 1)) (c : Real) :
    (∑ pair : SixVertexMarkedSectorConfiguration T left ×
        SixVertexMarkedSectorConfiguration T right,
      c ^ sixVertexConfigurationPairTotalCPhysical pair) =
      Matrix.trace (sixVertexSectorTransfer T.width left.val c ^ T.height) *
        Matrix.trace (sixVertexSectorTransfer T.width right.val c ^ T.height) := by
  rw [← sum_pow_sixVertexMarkedSectorConfiguration_eq_trace,
    ← sum_pow_sixVertexMarkedSectorConfiguration_eq_trace]
  simp only [sixVertexConfigurationPairTotalCPhysical, pow_add]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [Fintype.sum_prod_type]



structure SixVertexConfigurationPhysicalPairedBranchEmbeddings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) where
  branch : Bool ->
    SixVertexConfigurationPhysicalSource T middle hmiddle_pos hmiddle_lt ↪
      SixVertexConfigurationPhysicalTarget T middle
  distinct : forall source, branch false source ≠ branch true source
  aggregateTotalC : forall source,
    2 * sixVertexConfigurationPairTotalCPhysical source <=
      sixVertexConfigurationPairTotalCPhysical (branch false source) +
        sixVertexConfigurationPairTotalCPhysical (branch true source)



theorem sixVertexSectorTrace_logConcave_of_physicalPairedBranches
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    {c : Real} (hc : 1 <= c)
    (embeddings : SixVertexConfigurationPhysicalPairedBranchEmbeddings
      T middle hmiddle_pos hmiddle_lt) :
    Matrix.trace
          (sixVertexSectorTransfer T.width (middle.val - 1) c ^ T.height) *
        Matrix.trace
          (sixVertexSectorTransfer T.width (middle.val + 1) c ^ T.height) <=
      Matrix.trace
          (sixVertexSectorTransfer T.width middle.val c ^ T.height) ^ 2 := by
  have hmass := fintype_sum_le_of_twoBranchWeight
    (fun choice source => embeddings.branch choice source)
    (fun choice => (embeddings.branch choice).injective)
    (fun source => c ^ sixVertexConfigurationPairTotalCPhysical source)
    (fun target => c ^ sixVertexConfigurationPairTotalCPhysical target)
    (fun target => pow_nonneg (by linarith) _)
    (fun source => two_mul_pow_le_pow_add_pow_of_twice_le_add hc
      (embeddings.aggregateTotalC source))
  rw [sum_pow_configurationPairTotalC_eq_trace_mul_trace,
    sum_pow_configurationPairTotalC_eq_trace_mul_trace] at hmass
  simpa [pow_two] using hmass

end

end StatMech.FrontierD
