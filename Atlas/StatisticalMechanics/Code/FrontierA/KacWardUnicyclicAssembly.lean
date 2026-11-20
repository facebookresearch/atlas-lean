/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/















import Code.FrontierA.KacWardCycleAssembly

open scoped BigOperators

namespace StatMech.FrontierA

open Matrix





theorem kw_det_one_sub_blockTriangular
    {D Block : Type*} [Fintype D] [DecidableEq D]
    [Fintype Block] [DecidableEq Block] [LinearOrder Block]
    (transition : Matrix D D ℂ) (block : D -> Block)
    (htriangular : transition.BlockTriangular block) :
    (1 - transition).det =
      ∏ k : Block, (1 - transition.toSquareBlock block k).det := by
  have honeSub : (1 - transition).BlockTriangular block :=
    Matrix.blockTriangular_one.sub htriangular
  rw [honeSub.det_fintype]
  apply Finset.prod_congr rfl
  intro k _
  congr 1
  ext i j
  simp only [Matrix.sub_apply, Matrix.toSquareBlock_def, Matrix.of_apply]
  by_cases hij : i = j
  · subst j
    simp
  · have hval : (i : D) ≠ (j : D) := fun h => hij (Subtype.ext h)
    simp [hij, hval]




noncomputable def kwAcyclicCycleExtension
    {Incoming Core Outgoing : Type*}
    [Fintype Incoming] [DecidableEq Incoming]
    [Fintype Core] [DecidableEq Core]
    [Fintype Outgoing] [DecidableEq Outgoing]
    (incoming : Matrix Incoming Incoming ℂ)
    (incomingToRest : Matrix Incoming (Core ⊕ Outgoing) ℂ)
    (core : Matrix Core Core ℂ)
    (coreToOutgoing : Matrix Core Outgoing ℂ)
    (outgoing : Matrix Outgoing Outgoing ℂ) :
    Matrix (Incoming ⊕ (Core ⊕ Outgoing))
      (Incoming ⊕ (Core ⊕ Outgoing)) ℂ :=
  Matrix.fromBlocks incoming incomingToRest 0
    (Matrix.fromBlocks core coreToOutgoing 0 outgoing)



theorem kw_one_sub_acyclicCycleExtension
    {Incoming Core Outgoing : Type*}
    [Fintype Incoming] [DecidableEq Incoming]
    [Fintype Core] [DecidableEq Core]
    [Fintype Outgoing] [DecidableEq Outgoing]
    (incoming : Matrix Incoming Incoming ℂ)
    (incomingToRest : Matrix Incoming (Core ⊕ Outgoing) ℂ)
    (core : Matrix Core Core ℂ)
    (coreToOutgoing : Matrix Core Outgoing ℂ)
    (outgoing : Matrix Outgoing Outgoing ℂ) :
    1 - kwAcyclicCycleExtension incoming incomingToRest core
        coreToOutgoing outgoing =
      Matrix.fromBlocks (1 - incoming) (-incomingToRest) 0
        (Matrix.fromBlocks (1 - core) (-coreToOutgoing) 0 (1 - outgoing)) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp [kwAcyclicCycleExtension, Matrix.one_apply]
  · simp [kwAcyclicCycleExtension]
  · simp [kwAcyclicCycleExtension]
  · rcases i with i | i <;> rcases j with j | j <;>
      simp [kwAcyclicCycleExtension, Matrix.one_apply]



theorem kw_det_acyclicCycleExtension
    {Incoming Core Outgoing : Type*}
    [Fintype Incoming] [DecidableEq Incoming]
    [Fintype Core] [DecidableEq Core]
    [Fintype Outgoing] [DecidableEq Outgoing]
    (incoming : Matrix Incoming Incoming ℂ)
    (incomingToRest : Matrix Incoming (Core ⊕ Outgoing) ℂ)
    (core : Matrix Core Core ℂ)
    (coreToOutgoing : Matrix Core Outgoing ℂ)
    (outgoing : Matrix Outgoing Outgoing ℂ)
    (hIncoming : IsNilpotent incoming)
    (hOutgoing : IsNilpotent outgoing) :
    (1 - kwAcyclicCycleExtension incoming incomingToRest core
        coreToOutgoing outgoing).det = (1 - core).det := by
  rw [kw_one_sub_acyclicCycleExtension, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_fromBlocks_zero₂₁,
    det_one_sub_eq_one_of_isNilpotent incoming hIncoming,
    det_one_sub_eq_one_of_isNilpotent outgoing hOutgoing]
  ring




theorem kacWard_acyclic_extension_of_phase_sign
    {Incoming Outgoing E : Type*}
    [Fintype Incoming] [DecidableEq Incoming]
    [Fintype Outgoing] [DecidableEq Outgoing]
    [Fintype E] [DecidableEq E] [Nonempty E]
    (incoming : Matrix Incoming Incoming ℂ)
    (incomingToRest : Matrix Incoming ((E × Bool) ⊕ Outgoing) ℂ)
    (outgoing : Matrix Outgoing Outgoing ℂ)
    (coreToOutgoing : Matrix (E × Bool) Outgoing ℂ)
    (sigma : Equiv.Perm E) (edgeWeight : E -> ℂ)
    (phase : Bool -> E -> ℂ)
    (hIncoming : IsNilpotent incoming)
    (hOutgoing : IsNilpotent outgoing)
    (hcycle : sigma.IsCycle) (hfree : ∀ i, sigma i ≠ i)
    (hphase : ∀ b, ∏ i, phase b i = -1) :
    (1 - kwAcyclicCycleExtension incoming incomingToRest
        (kwTwoOrientationCycleTransition sigma
          (fun b i => edgeWeight i * phase b i))
        coreToOutgoing outgoing).det =
      (kwAbstractCycleEvenPolynomial edgeWeight) ^ 2 := by
  rw [kw_det_acyclicCycleExtension incoming incomingToRest _
    coreToOutgoing outgoing hIncoming hOutgoing]
  exact kacWard_abstract_cycle_of_phase_sign sigma edgeWeight phase
    hcycle hfree hphase




theorem kacWard_rectilinear_acyclic_extension
    {Incoming Outgoing : Type*}
    [Fintype Incoming] [DecidableEq Incoming]
    [Fintype Outgoing] [DecidableEq Outgoing]
    {n : ℕ} [NeZero n]
    (incoming : Matrix Incoming Incoming ℂ)
    (incomingToRest : Matrix Incoming ((Fin n × Bool) ⊕ Outgoing) ℂ)
    (outgoing : Matrix Outgoing Outgoing ℂ)
    (coreToOutgoing : Matrix (Fin n × Bool) Outgoing ℂ)
    (hIncoming : IsNilpotent incoming)
    (hOutgoing : IsNilpotent outgoing)
    (omega : ℂ) (homega : omega ≠ 0) (hI : omega ^ 2 = Complex.I)
    (d : Fin n -> Fin 4)
    (hclosed : ∑ i, StatMech.Onsager.BaseCase.stepOf (d i) = 0)
    (hsimple : Function.Injective (StatMech.Onsager.BaseCase.pos d))
    (hn : 3 ≤ n) (hnu : ∀ i, d (i + 1) ≠ d i + 2)
    (edgeWeight : Fin n -> ℂ) :
    (1 - kwAcyclicCycleExtension incoming incomingToRest
        (kwTwoOrientationCycleTransition (finRotate n)
          (fun _ i => edgeWeight i *
            StatMech.Onsager.ons_turnW omega (d i) (d (i + 1))))
        coreToOutgoing outgoing).det =
      (kwAbstractCycleEvenPolynomial edgeWeight) ^ 2 := by
  apply kacWard_acyclic_extension_of_phase_sign
      incoming incomingToRest outgoing coreToOutgoing
      (finRotate n) edgeWeight
      (fun _ i => StatMech.Onsager.ons_turnW omega (d i) (d (i + 1)))
      hIncoming hOutgoing
  · exact isCycle_finRotate_of_le (by omega)
  · exact kw_finRotate_free (by omega)
  · intro _
    exact StatMech.Onsager.GeneralUmlaufsatz.turnWeightProduct_eq_neg_one
      omega homega hI d hclosed hsimple hn hnu

end StatMech.FrontierA
