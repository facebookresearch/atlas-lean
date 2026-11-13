/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsoradialKacWardRibbonIdentification
import Code.FrontierA.SimpleGraphCellularRibbonEmbedding





namespace StatMech.FrontierA

open Finset
open scoped BigOperators



theorem isoradial_dualCos_mul_criticalMu_inv
    (theta : Real) (htheta : 0 < theta)
    (htheta' : theta < Real.pi / 2) :
    (Real.cos (Real.pi / 2 - theta) : Complex) *
        (isoradialCriticalMu theta)⁻¹ =
      -Complex.I * (Real.cos theta : Complex) := by
  have hthetaPi : theta < Real.pi :=
    lt_trans htheta' (by nlinarith [Real.pi_pos])
  have hsin : Real.sin theta ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi htheta hthetaPi)
  have hedgeReal :
      Real.sin theta * (Real.tan theta)⁻¹ = Real.cos theta := by
    rw [Real.tan_eq_sin_div_cos, inv_div]
    field_simp
  have hedgeComplex :
      (Real.sin theta : Complex) * (Real.tan theta : Complex)⁻¹ =
        (Real.cos theta : Complex) := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, hedgeReal]
  rw [Real.cos_pi_div_two_sub, isoradialCriticalMu,
    mul_inv_rev, Complex.inv_I]
  calc
    (Real.sin theta : Complex) *
        ((Real.tan theta : Complex)⁻¹ * -Complex.I) =
      ((Real.sin theta : Complex) *
        (Real.tan theta : Complex)⁻¹) * -Complex.I := by ring
    _ = (Real.cos theta : Complex) * -Complex.I := by
      rw [hedgeComplex]
    _ = -Complex.I * (Real.cos theta : Complex) := by ring

variable {E : Type*} [Fintype E] [DecidableEq E]

omit [DecidableEq E] in

theorem prod_isoradial_dualCos_mul_criticalMu_inv
    (theta : E -> Real) (htheta : forall edge, 0 < theta edge)
    (htheta' : forall edge, theta edge < Real.pi / 2) :
    (∏ edge : E,
        (Real.cos (Real.pi / 2 - theta edge) : Complex)) *
        (∏ edge : E, isoradialCriticalMu (theta edge))⁻¹ =
      (-Complex.I) ^ Fintype.card E *
        ∏ edge : E, (Real.cos (theta edge) : Complex) := by
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  calc
    (∏ edge : E,
        (Real.cos (Real.pi / 2 - theta edge) : Complex) *
          (isoradialCriticalMu (theta edge))⁻¹) =
      ∏ edge : E,
        (-Complex.I) * (Real.cos (theta edge) : Complex) := by
      apply Finset.prod_congr rfl
      intro edge _
      exact isoradial_dualCos_mul_criticalMu_inv
        (theta edge) (htheta edge) (htheta' edge)
    _ = (-Complex.I) ^ Fintype.card E *
        ∏ edge : E, (Real.cos (theta edge) : Complex) := by
      rw [Finset.prod_mul_distrib]
      simp


noncomputable def kwIsoradialDualityNormalization
    (Vertex : Type*) [Fintype Vertex] (theta : E -> Real) : Complex :=
  (2 : Complex) ^ Fintype.card Vertex *
    ∏ edge : E, (1 + (Real.cos (theta edge) : Complex))

omit [DecidableEq E] in


theorem kwIsoradialDualityNormalization_mul_prefactor
    {Vertex : Type*} [Fintype Vertex]
    (theta : E -> Real) (exceptional : Vertex -> Bool)
    (htheta : forall edge, 0 < theta edge)
    (htheta' : forall edge, theta edge < Real.pi / 2) :
    kwIsoradialDualityNormalization Vertex theta *
        criticalKacWardRibbonPrefactor theta exceptional =
      (-1 : Complex) ^ Fintype.card Vertex *
        (2 : Complex) ^ Fintype.card E *
        (∏ vertex : Vertex, coneQuarterPhase exceptional vertex) *
        ∏ edge : E, (Real.cos (theta edge) : Complex) := by
  have htwo : (2 : Complex) ^ Fintype.card Vertex ≠ 0 := by norm_num
  have hedge (edge : E) :
      (1 + Real.cos (theta edge) : Complex) ≠ 0 := by
    have hcos : 0 < Real.cos (theta edge) :=
      Real.cos_pos_of_mem_Ioo
        ⟨by nlinarith [Real.pi_pos, htheta edge], htheta' edge⟩
    have hreal : 1 + Real.cos (theta edge) ≠ 0 :=
      ne_of_gt (by linarith)
    exact_mod_cast hreal
  have hproducts :
      (∏ edge : E, (1 + (Real.cos (theta edge) : Complex))) *
          kwLaplacianEdgePrefactor theta =
        ∏ edge : E, (Real.cos (theta edge) : Complex) := by
    unfold kwLaplacianEdgePrefactor
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro edge _
    rw [Complex.ofReal_add, Complex.ofReal_one]
    rw [div_eq_mul_inv]
    calc
      (1 + (Real.cos (theta edge) : Complex)) *
          ((Real.cos (theta edge) : Complex) *
            (1 + (Real.cos (theta edge) : Complex))⁻¹) =
        (Real.cos (theta edge) : Complex) *
          ((1 + (Real.cos (theta edge) : Complex)) *
            (1 + (Real.cos (theta edge) : Complex))⁻¹) := by ring
      _ = (Real.cos (theta edge) : Complex) := by
        rw [mul_inv_cancel₀ (hedge edge), mul_one]
  unfold kwIsoradialDualityNormalization
    criticalKacWardRibbonPrefactor kwEulerPowerPrefactor
  rw [← hproducts]
  field_simp



theorem prod_coneQuarterPhase
    (Vertex : Type*) [Fintype Vertex]
    (exceptional : Vertex -> Bool) :
    (∏ vertex : Vertex, coneQuarterPhase exceptional vertex) =
      Complex.I ^ Fintype.card Vertex *
        (-1 : Complex) ^ coneExceptionCount exceptional := by
  classical
  have hlocal (vertex : Vertex) :
      coneQuarterPhase exceptional vertex =
        Complex.I * if exceptional vertex then (-1 : Complex) else 1 := by
    cases h : exceptional vertex <;>
      simp [coneQuarterPhase, h]
  calc
    (∏ vertex : Vertex, coneQuarterPhase exceptional vertex) =
        ∏ vertex : Vertex,
          Complex.I * if exceptional vertex then (-1 : Complex) else 1 := by
      apply Finset.prod_congr rfl
      intro vertex _
      exact hlocal vertex
    _ = (∏ _vertex : Vertex, Complex.I) *
        ∏ vertex : Vertex,
          if exceptional vertex then (-1 : Complex) else 1 := by
      rw [Finset.prod_mul_distrib]
    _ = Complex.I ^ Fintype.card Vertex *
        (-1 : Complex) ^ coneExceptionCount exceptional := by
      rw [coneExceptionCount, Finset.prod_ite]
      simp




theorem coneExceptionCount_mod_two_eq_sum
    (Vertex : Type*) [Fintype Vertex]
    (exceptional : Vertex -> Bool) (coneIndex : Vertex -> Nat)
    (hexceptional : forall vertex,
      exceptional vertex = true ↔ coneIndex vertex % 2 = 1) :
    coneExceptionCount exceptional % 2 =
      (∑ vertex : Vertex, coneIndex vertex) % 2 := by
  classical
  have hterm (vertex : Vertex) :
      (if exceptional vertex then 1 else 0) = coneIndex vertex % 2 := by
    cases h : exceptional vertex
    · have hv := hexceptional vertex
      simp [h] at hv
      have hlt := Nat.mod_lt (coneIndex vertex) (by omega : 0 < 2)
      simp
      omega
    · have hv := (hexceptional vertex).mp h
      simp [hv]
  have hcount : coneExceptionCount exceptional =
      ∑ vertex : Vertex, if exceptional vertex then 1 else 0 := by
    simp [coneExceptionCount]
  rw [hcount]
  simp_rw [hterm]
  exact Nat.ModEq.sum fun vertex _ => Nat.mod_modEq (coneIndex vertex) 2



structure KacWardSubgraphCoefficientIdentification
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (coefficient : Finset E -> Complex) (kacWard : Matrix Q Q Complex)
    (weight : E -> Complex) (prefactor : Complex) where
  permutationEdgeSet : Equiv.Perm Q -> Finset E
  coefficientFiber : forall F : Finset E,
    (∑ sigma : finiteMapFiber permutationEdgeSet F,
        matrixDetPermutationTerm (1 - kacWard) sigma.1) =
      prefactor * (coefficient F * ∏ edge ∈ F, weight edge)




structure RibbonDualBoundaryIdentification
    {Dprimal Ddual : Type*}
    [Fintype Dprimal] [DecidableEq Dprimal]
    [Fintype Ddual] [DecidableEq Ddual]
    (primalRibbon : RibbonPermutationSystem E Dprimal)
    (dualRibbon : RibbonPermutationSystem E Ddual) where
  boundaryEquiv : forall F : Finset E,
    Fin (dualRibbon.boundaryComponents F) ≃
      Fin (primalRibbon.boundaryComponents Fᶜ)

namespace RibbonPermutationSystem



noncomputable def dualRibbonSystem
    {D : Type*} [Fintype D] [DecidableEq D]
    (R : RibbonPermutationSystem E D) : RibbonPermutationSystem E D where
  rotation := R.boundaryPerm Finset.univ
  edgeFlip := R.edgeFlip
  edgeFlip_isSwap := R.edgeFlip_isSwap
  edgeFlip_commute := R.edgeFlip_commute

omit [Fintype E] [DecidableEq E] in
theorem edgeFlip_mul_self
    {D : Type*} [Fintype D] [DecidableEq D]
    (R : RibbonPermutationSystem E D) (edge : E) :
    R.edgeFlip edge * R.edgeFlip edge = 1 := by
  obtain ⟨a, b, hab, hswap⟩ := R.edgeFlip_isSwap edge
  rw [hswap]
  exact Equiv.swap_mul_self a b

omit [Fintype E] [DecidableEq E] in
theorem partialEdgeFlip_mul_self
    {D : Type*} [Fintype D] [DecidableEq D]
    (R : RibbonPermutationSystem E D) (F : Finset E) :
    R.partialEdgeFlip F * R.partialEdgeFlip F = 1 := by
  classical
  induction F using Finset.induction_on with
  | empty => simp [partialEdgeFlip]
  | @insert edge F hedge ih =>
      rw [R.partialEdgeFlip_insert F edge (by simpa using hedge)]
      have hcomm : Commute (R.edgeFlip edge) (R.partialEdgeFlip F) := by
        unfold partialEdgeFlip
        apply Finset.noncommProd_commute
        intro other hother
        exact R.edgeFlip_commute edge other fun h =>
          hedge (h ▸ hother)
      rw [hcomm.symm.mul_mul_mul_comm, R.edgeFlip_mul_self edge, ih, mul_one]

theorem partialEdgeFlip_univ_mul
    {D : Type*} [Fintype D] [DecidableEq D]
    (R : RibbonPermutationSystem E D) (F : Finset E) :
    R.partialEdgeFlip Finset.univ * R.partialEdgeFlip F =
      R.partialEdgeFlip Fᶜ := by
  have hdisjoint : Disjoint Fᶜ F := disjoint_compl_left_iff.mpr le_rfl
  have hunion : Fᶜ ∪ F = (Finset.univ : Finset E) := by
    ext edge
    by_cases hedge : edge ∈ F <;> simp [hedge]
  have hsplit : R.partialEdgeFlip Finset.univ =
      R.partialEdgeFlip Fᶜ * R.partialEdgeFlip F := by
    unfold partialEdgeFlip
    rw [← hunion]
    exact Finset.noncommProd_union_of_disjoint hdisjoint R.edgeFlip
      (fun edge _ other _ hne => R.edgeFlip_commute edge other hne)
  rw [hsplit, mul_assoc, R.partialEdgeFlip_mul_self F, mul_one]



theorem dualRibbonSystem_boundaryPerm
    {D : Type*} [Fintype D] [DecidableEq D]
    (R : RibbonPermutationSystem E D) (F : Finset E) :
    R.dualRibbonSystem.boundaryPerm F = R.boundaryPerm Fᶜ := by
  change (R.rotation * R.partialEdgeFlip Finset.univ) *
      R.partialEdgeFlip F = R.rotation * R.partialEdgeFlip Fᶜ
  rw [mul_assoc, R.partialEdgeFlip_univ_mul F]

theorem dualRibbonSystem_boundaryComponents
    {D : Type*} [Fintype D] [DecidableEq D]
    (R : RibbonPermutationSystem E D) (F : Finset E) :
    R.dualRibbonSystem.boundaryComponents F =
      R.boundaryComponents Fᶜ := by
  unfold boundaryComponents
  rw [R.dualRibbonSystem_boundaryPerm F]


noncomputable def dualBoundaryIdentification
    {D : Type*} [Fintype D] [DecidableEq D]
    (R : RibbonPermutationSystem E D) :
    RibbonDualBoundaryIdentification R R.dualRibbonSystem where
  boundaryEquiv F :=
    finCongr (R.dualRibbonSystem_boundaryComponents F)


noncomputable def dualBoundaryCharacter
    {D : Type*} [Fintype D] [DecidableEq D]
    (R : RibbonPermutationSystem E D)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (F : Finset E) (boundary : Fin (R.dualRibbonSystem.boundaryComponents F)) :
    Complex :=
  (character Fᶜ (R.dualBoundaryIdentification.boundaryEquiv F boundary))⁻¹

@[simp]
theorem dualBoundaryCharacter_reverse
    {D : Type*} [Fintype D] [DecidableEq D]
    (R : RibbonPermutationSystem E D)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (F : Finset E) (boundary : Fin (R.dualRibbonSystem.boundaryComponents F)) :
    R.dualBoundaryCharacter character F boundary =
      (character Fᶜ
        (R.dualBoundaryIdentification.boundaryEquiv F boundary))⁻¹ := rfl

end RibbonPermutationSystem



theorem ribbonBoundaryCharacterCoefficient_dual
    {Dprimal Ddual : Type*}
    [Fintype Dprimal] [DecidableEq Dprimal]
    [Fintype Ddual] [DecidableEq Ddual]
    (primalRibbon : RibbonPermutationSystem E Dprimal)
    (dualRibbon : RibbonPermutationSystem E Ddual)
    (identification : RibbonDualBoundaryIdentification
      primalRibbon dualRibbon)
    (primalCharacter : forall F : Finset E,
      Fin (primalRibbon.boundaryComponents F) -> Complex)
    (dualCharacter : forall F : Finset E,
      Fin (dualRibbon.boundaryComponents F) -> Complex)
    (character_reverse : forall (F : Finset E)
      (boundary : Fin (dualRibbon.boundaryComponents F)),
      dualCharacter F boundary =
        (primalCharacter Fᶜ (identification.boundaryEquiv F boundary))⁻¹)
    (F : Finset E) :
    ribbonBoundaryCharacterCoefficient dualRibbon dualCharacter F =
      dualRibbonBoundaryCharacterCoefficient primalRibbon primalCharacter F := by
  unfold ribbonBoundaryCharacterCoefficient
    dualRibbonBoundaryCharacterCoefficient
  apply Fintype.prod_equiv (identification.boundaryEquiv F)
  intro boundary
  rw [character_reverse]



theorem dualBoundaryCharacterCoefficient_eq
    {D : Type*} [Fintype D] [DecidableEq D]
    (R : RibbonPermutationSystem E D)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (F : Finset E) :
    ribbonBoundaryCharacterCoefficient R.dualRibbonSystem
        (R.dualBoundaryCharacter character) F =
      dualRibbonBoundaryCharacterCoefficient R character F :=
  ribbonBoundaryCharacterCoefficient_dual R R.dualRibbonSystem
    R.dualBoundaryIdentification character
    (R.dualBoundaryCharacter character)
    (R.dualBoundaryCharacter_reverse character) F

namespace CriticalKacWardRibbonCoefficientIdentification




def toSubgraphCoefficientIdentification
    {D V Q : Type*}
    [Fintype D] [DecidableEq D]
    [Fintype V]
    [Fintype Q] [DecidableEq Q]
    (R : RibbonPermutationSystem E D)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (kacWard : Matrix Q Q Complex) (theta : E -> Real)
    (exceptional : V -> Bool)
    (I : CriticalKacWardRibbonCoefficientIdentification
      R character kacWard theta exceptional) :
    KacWardSubgraphCoefficientIdentification
      (ribbonBoundaryCharacterCoefficient R character) kacWard
      (fun edge => isoradialCriticalMu (theta edge))
      (criticalKacWardRibbonPrefactor theta exceptional) where
  permutationEdgeSet := I.permutationEdgeSet
  coefficientFiber := I.coefficientFiber




def toDualSubgraphCoefficientIdentification
    {Ddual Dprimal Vdual Qdual : Type*}
    [Fintype Ddual] [DecidableEq Ddual]
    [Fintype Dprimal] [DecidableEq Dprimal]
    [Fintype Vdual]
    [Fintype Qdual] [DecidableEq Qdual]
    (dualRibbon : RibbonPermutationSystem E Ddual)
    (dualCharacter : forall F : Finset E,
      Fin (dualRibbon.boundaryComponents F) -> Complex)
    (dualKacWard : Matrix Qdual Qdual Complex)
    (dualTheta : E -> Real) (dualExceptional : Vdual -> Bool)
    (I : CriticalKacWardRibbonCoefficientIdentification
      dualRibbon dualCharacter dualKacWard dualTheta dualExceptional)
    (primalRibbon : RibbonPermutationSystem E Dprimal)
    (primalCharacter : forall F : Finset E,
      Fin (primalRibbon.boundaryComponents F) -> Complex)
    (boundaryCoefficient_eq : forall F : Finset E,
      ribbonBoundaryCharacterCoefficient dualRibbon dualCharacter F =
        dualRibbonBoundaryCharacterCoefficient
          primalRibbon primalCharacter F) :
    KacWardSubgraphCoefficientIdentification
      (dualRibbonBoundaryCharacterCoefficient
        primalRibbon primalCharacter) dualKacWard
      (fun edge => isoradialCriticalMu (dualTheta edge))
      (criticalKacWardRibbonPrefactor dualTheta dualExceptional) where
  permutationEdgeSet := I.permutationEdgeSet
  coefficientFiber := by
    intro F
    rw [← boundaryCoefficient_eq F]
    exact I.coefficientFiber F

end CriticalKacWardRibbonCoefficientIdentification

namespace KacWardSubgraphCoefficientIdentification



theorem expansion
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (coefficient : Finset E -> Complex) (kacWard : Matrix Q Q Complex)
    (weight : E -> Complex) (prefactor : Complex)
    (I : KacWardSubgraphCoefficientIdentification
      coefficient kacWard weight prefactor) :
    (1 - kacWard).det =
      prefactor * kwDualSubgraphSum coefficient weight := by
  rw [matrix_det_eq_sum_permutationTerm]
  calc
    (∑ sigma : Equiv.Perm Q,
        matrixDetPermutationTerm (1 - kacWard) sigma) =
      ∑ F : Finset E,
        ∑ sigma : finiteMapFiber I.permutationEdgeSet F,
          matrixDetPermutationTerm (1 - kacWard) sigma.1 :=
      (Fintype.sum_fiberwise I.permutationEdgeSet
        (matrixDetPermutationTerm (1 - kacWard))).symm
    _ = prefactor * kwDualSubgraphSum coefficient weight := by
      unfold kwDualSubgraphSum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro F _
      rw [I.coefficientFiber F]

end KacWardSubgraphCoefficientIdentification



structure IsoradialDualConePhaseBalance
    (PrimalVertex DualVertex : Type*)
    [Fintype PrimalVertex] [Fintype DualVertex]
    {Dart : Type*} [Fintype Dart] [DecidableEq Dart]
    (R : RibbonPermutationSystem E Dart) (C : CellularRibbonDualData R)
    (primalExceptional : PrimalVertex -> Bool)
    (dualExceptional : DualVertex -> Bool) where
  dualVertexCount_eq : C.dualVertexCount = Fintype.card DualVertex
  phaseBalance :
    (∏ vertex : DualVertex, coneQuarterPhase dualExceptional vertex) *
        (-Complex.I) ^ Fintype.card E =
      (-1 : Complex) ^ Fintype.card PrimalVertex *
        ∏ vertex : PrimalVertex,
          coneQuarterPhase primalExceptional vertex





structure IsoradialDualGaussBonnetParity
    (PrimalVertex DualVertex : Type*)
    [Fintype PrimalVertex] [Fintype DualVertex]
    {Dart : Type*} [Fintype Dart] [DecidableEq Dart]
    (R : RibbonPermutationSystem E Dart) (C : CellularRibbonDualData R)
    (primalExceptional : PrimalVertex -> Bool)
    (dualExceptional : DualVertex -> Bool) where
  primalVertexCount_eq : C.primalVertexCount = Fintype.card PrimalVertex
  dualVertexCount_eq : C.dualVertexCount = Fintype.card DualVertex
  exceptionParity :
    (coneExceptionCount primalExceptional +
      coneExceptionCount dualExceptional + 1) % 2 = C.genus % 2




structure IsoradialOddConeGaussBonnetData
    (PrimalVertex DualVertex : Type*)
    [Fintype PrimalVertex] [Fintype DualVertex]
    {Dart : Type*} [Fintype Dart] [DecidableEq Dart]
    (R : RibbonPermutationSystem E Dart) (C : CellularRibbonDualData R)
    (primalExceptional : PrimalVertex -> Bool)
    (dualExceptional : DualVertex -> Bool) where
  primalVertexCount_eq : C.primalVertexCount = Fintype.card PrimalVertex
  dualVertexCount_eq : C.dualVertexCount = Fintype.card DualVertex
  primalConeIndex : PrimalVertex -> Nat
  dualConeIndex : DualVertex -> Nat
  primalExceptional_iff : forall vertex,
    primalExceptional vertex = true ↔ primalConeIndex vertex % 2 = 1
  dualExceptional_iff : forall vertex,
    dualExceptional vertex = true ↔ dualConeIndex vertex % 2 = 1
  coneIndexGaussBonnet :
    (∑ vertex : PrimalVertex, primalConeIndex vertex) +
      (∑ vertex : DualVertex, dualConeIndex vertex) + 1 = C.genus

namespace IsoradialOddConeGaussBonnetData

omit [DecidableEq E] in


theorem toGaussBonnetParity
    {PrimalVertex DualVertex Dart : Type*}
    [Fintype PrimalVertex] [Fintype DualVertex]
    [Fintype Dart] [DecidableEq Dart]
    (R : RibbonPermutationSystem E Dart) (C : CellularRibbonDualData R)
    (primalExceptional : PrimalVertex -> Bool)
    (dualExceptional : DualVertex -> Bool)
    (data : IsoradialOddConeGaussBonnetData
      PrimalVertex DualVertex R C primalExceptional dualExceptional) :
    IsoradialDualGaussBonnetParity
      PrimalVertex DualVertex R C primalExceptional dualExceptional := by
  refine
    { primalVertexCount_eq := data.primalVertexCount_eq
      dualVertexCount_eq := data.dualVertexCount_eq
      exceptionParity := ?_ }
  have hprimal := coneExceptionCount_mod_two_eq_sum
    PrimalVertex primalExceptional data.primalConeIndex
      data.primalExceptional_iff
  have hdual := coneExceptionCount_mod_two_eq_sum
    DualVertex dualExceptional data.dualConeIndex data.dualExceptional_iff
  have hgaussBonnet := data.coneIndexGaussBonnet
  omega

end IsoradialOddConeGaussBonnetData

namespace IsoradialDualGaussBonnetParity

omit [DecidableEq E] in


theorem conePhaseBalance
    {PrimalVertex DualVertex Dart : Type*}
    [Fintype PrimalVertex] [Fintype DualVertex]
    [Fintype Dart] [DecidableEq Dart]
    (R : RibbonPermutationSystem E Dart) (C : CellularRibbonDualData R)
    (primalExceptional : PrimalVertex -> Bool)
    (dualExceptional : DualVertex -> Bool)
    (gaussBonnet : IsoradialDualGaussBonnetParity
      PrimalVertex DualVertex R C primalExceptional dualExceptional) :
    IsoradialDualConePhaseBalance
      PrimalVertex DualVertex R C primalExceptional dualExceptional := by
  classical
  refine
    { dualVertexCount_eq := gaussBonnet.dualVertexCount_eq
      phaseBalance := ?_ }
  rw [prod_coneQuarterPhase DualVertex dualExceptional,
    prod_coneQuarterPhase PrimalVertex primalExceptional]
  have heuler := C.cellularEuler
  rw [gaussBonnet.primalVertexCount_eq,
    gaussBonnet.dualVertexCount_eq] at heuler
  have hparity := gaussBonnet.exceptionParity
  have hmod :
      (Fintype.card DualVertex +
          2 * coneExceptionCount dualExceptional +
          3 * Fintype.card E) % 4 =
        (2 * Fintype.card PrimalVertex +
          (Fintype.card PrimalVertex +
            2 * coneExceptionCount primalExceptional)) % 4 := by
    omega
  have hneg : (-1 : Complex) = Complex.I ^ 2 := by
    norm_num [Complex.I_mul_I]
  have hnegI : -Complex.I = Complex.I ^ 3 := by
    norm_num [Complex.I_mul_I]
  rw [hneg, hnegI]
  simp only [← pow_mul, ← pow_add]
  exact pow_eq_pow_of_modEq hmod (by norm_num [Complex.I_mul_I])

end IsoradialDualGaussBonnetParity



theorem normalized_isoradialKacWard_duality
    {PrimalVertex DualVertex Dart Q Qstar : Type*}
    [Fintype PrimalVertex] [Fintype DualVertex]
    [Fintype Dart] [DecidableEq Dart]
    [Fintype Q] [DecidableEq Q] [Fintype Qstar] [DecidableEq Qstar]
    (R : RibbonPermutationSystem E Dart) (C : CellularRibbonDualData R)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (hcharacter : forall (F : Finset E)
      (boundary : Fin (R.boundaryComponents F)), character F boundary ≠ 0)
    (htotal : forall F : Finset E, ∏ boundary, character F boundary = 1)
    (theta : E -> Real)
    (htheta : forall edge, 0 < theta edge)
    (htheta' : forall edge, theta edge < Real.pi / 2)
    (primalExceptional : PrimalVertex -> Bool)
    (dualExceptional : DualVertex -> Bool)
    (primalKacWard : Matrix Q Q Complex)
    (dualKacWard : Matrix Qstar Qstar Complex)
    (primalExpansion : KacWardSubgraphCoefficientIdentification
      (ribbonBoundaryCharacterCoefficient R character) primalKacWard
      (fun edge => isoradialCriticalMu (theta edge))
      (criticalKacWardRibbonPrefactor theta primalExceptional))
    (dualExpansion : KacWardSubgraphCoefficientIdentification
      (dualRibbonBoundaryCharacterCoefficient R character) dualKacWard
      (fun edge => isoradialCriticalMu (Real.pi / 2 - theta edge))
      (criticalKacWardRibbonPrefactor
        (fun edge => Real.pi / 2 - theta edge) dualExceptional))
    (cone : IsoradialDualConePhaseBalance
      PrimalVertex DualVertex R C primalExceptional dualExceptional) :
    kwIsoradialDualityNormalization DualVertex
        (fun edge => Real.pi / 2 - theta edge) *
        (1 - dualKacWard).det =
      kwIsoradialDualityNormalization PrimalVertex theta *
        (1 - primalKacWard).det := by
  have hdualPos (edge : E) : 0 < Real.pi / 2 - theta edge := by
    linarith [htheta' edge]
  have hdualLt (edge : E) :
      Real.pi / 2 - theta edge < Real.pi / 2 := by
    linarith [htheta edge]
  rw [dualExpansion.expansion, primalExpansion.expansion]
  rw [cellularRibbon_isoradialCritical_subgraphSum_duality
    R C character hcharacter htotal theta htheta htheta']
  rw [← mul_assoc
      (kwIsoradialDualityNormalization DualVertex
        (fun edge => Real.pi / 2 - theta edge))
      (criticalKacWardRibbonPrefactor
        (fun edge => Real.pi / 2 - theta edge) dualExceptional)]
  rw [← mul_assoc
      (kwIsoradialDualityNormalization PrimalVertex theta)
      (criticalKacWardRibbonPrefactor theta primalExceptional)]
  rw [kwIsoradialDualityNormalization_mul_prefactor
      (fun edge => Real.pi / 2 - theta edge) dualExceptional
      hdualPos hdualLt,
    kwIsoradialDualityNormalization_mul_prefactor
      theta primalExceptional htheta htheta']
  rw [cone.dualVertexCount_eq]
  have hedgeProduct := prod_isoradial_dualCos_mul_criticalMu_inv
    theta htheta htheta'
  have hsign :
      (-1 : Complex) ^ Fintype.card DualVertex *
          (-1 : Complex) ^ Fintype.card DualVertex = 1 := by
    rw [← mul_pow]
    norm_num
  let signDual : Complex := (-1 : Complex) ^ Fintype.card DualVertex
  let signPrimal : Complex := (-1 : Complex) ^ Fintype.card PrimalVertex
  let twoEdges : Complex := (2 : Complex) ^ Fintype.card E
  let phaseDual : Complex :=
    ∏ vertex : DualVertex, coneQuarterPhase dualExceptional vertex
  let phasePrimal : Complex :=
    ∏ vertex : PrimalVertex, coneQuarterPhase primalExceptional vertex
  let cosDual : Complex :=
    ∏ edge : E, (Real.cos (Real.pi / 2 - theta edge) : Complex)
  let cosPrimal : Complex :=
    ∏ edge : E, (Real.cos (theta edge) : Complex)
  let muInv : Complex :=
    (∏ edge : E, isoradialCriticalMu (theta edge))⁻¹
  let subgraphSum : Complex :=
    kwDualSubgraphSum
      (ribbonBoundaryCharacterCoefficient R character)
      (fun edge => isoradialCriticalMu (theta edge))
  change ((signDual * twoEdges * phaseDual) * cosDual) *
      (signDual * (muInv * subgraphSum)) =
    ((signPrimal * twoEdges * phasePrimal) * cosPrimal) * subgraphSum
  have hsign' : signDual * signDual = 1 := hsign
  have hedgeProduct' :
      cosDual * muInv = (-Complex.I) ^ Fintype.card E * cosPrimal :=
    hedgeProduct
  have hphase :
      phaseDual * (-Complex.I) ^ Fintype.card E =
        signPrimal * phasePrimal := cone.phaseBalance
  calc
    ((signDual * twoEdges * phaseDual) * cosDual) *
        (signDual * (muInv * subgraphSum)) =
      (signDual * signDual) * twoEdges * phaseDual *
        (cosDual * muInv) * subgraphSum := by ring
    _ = twoEdges *
        (phaseDual * (-Complex.I) ^ Fintype.card E) *
        cosPrimal * subgraphSum := by
      rw [hsign', one_mul, hedgeProduct']
      ring
    _ = ((signPrimal * twoEdges * phasePrimal) * cosPrimal) *
        subgraphSum := by
      rw [hphase]
      ring



theorem normalized_isoradialKacWard_duality_of_gaussBonnet
    {PrimalVertex DualVertex Dart Q Qstar : Type*}
    [Fintype PrimalVertex] [Fintype DualVertex]
    [Fintype Dart] [DecidableEq Dart]
    [Fintype Q] [DecidableEq Q] [Fintype Qstar] [DecidableEq Qstar]
    (R : RibbonPermutationSystem E Dart) (C : CellularRibbonDualData R)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (hcharacter : forall (F : Finset E)
      (boundary : Fin (R.boundaryComponents F)), character F boundary ≠ 0)
    (htotal : forall F : Finset E, ∏ boundary, character F boundary = 1)
    (theta : E -> Real)
    (htheta : forall edge, 0 < theta edge)
    (htheta' : forall edge, theta edge < Real.pi / 2)
    (primalExceptional : PrimalVertex -> Bool)
    (dualExceptional : DualVertex -> Bool)
    (primalKacWard : Matrix Q Q Complex)
    (dualKacWard : Matrix Qstar Qstar Complex)
    (primalExpansion : KacWardSubgraphCoefficientIdentification
      (ribbonBoundaryCharacterCoefficient R character) primalKacWard
      (fun edge => isoradialCriticalMu (theta edge))
      (criticalKacWardRibbonPrefactor theta primalExceptional))
    (dualExpansion : KacWardSubgraphCoefficientIdentification
      (dualRibbonBoundaryCharacterCoefficient R character) dualKacWard
      (fun edge => isoradialCriticalMu (Real.pi / 2 - theta edge))
      (criticalKacWardRibbonPrefactor
        (fun edge => Real.pi / 2 - theta edge) dualExceptional))
    (gaussBonnet : IsoradialDualGaussBonnetParity
      PrimalVertex DualVertex R C primalExceptional dualExceptional) :
    kwIsoradialDualityNormalization DualVertex
        (fun edge => Real.pi / 2 - theta edge) *
        (1 - dualKacWard).det =
      kwIsoradialDualityNormalization PrimalVertex theta *
        (1 - primalKacWard).det :=
  normalized_isoradialKacWard_duality R C character hcharacter htotal
    theta htheta htheta' primalExceptional dualExceptional
    primalKacWard dualKacWard primalExpansion dualExpansion
    (gaussBonnet.conePhaseBalance R C
      primalExceptional dualExceptional)






theorem normalized_isoradialKacWard_duality_of_ribbonCoefficients
    {PrimalVertex DualVertex Dart DualDart Q Qstar : Type*}
    [Fintype PrimalVertex] [Fintype DualVertex]
    [Fintype Dart] [DecidableEq Dart]
    [Fintype DualDart] [DecidableEq DualDart]
    [Fintype Q] [DecidableEq Q] [Fintype Qstar] [DecidableEq Qstar]
    (R : RibbonPermutationSystem E Dart) (C : CellularRibbonDualData R)
    (Rdual : RibbonPermutationSystem E DualDart)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (dualCharacter : forall F : Finset E,
      Fin (Rdual.boundaryComponents F) -> Complex)
    (hcharacter : forall (F : Finset E)
      (boundary : Fin (R.boundaryComponents F)), character F boundary ≠ 0)
    (htotal : forall F : Finset E, ∏ boundary, character F boundary = 1)
    (boundaryIdentification : RibbonDualBoundaryIdentification R Rdual)
    (dualCharacter_reverse : forall (F : Finset E)
      (boundary : Fin (Rdual.boundaryComponents F)),
      dualCharacter F boundary =
        (character Fᶜ
          (boundaryIdentification.boundaryEquiv F boundary))⁻¹)
    (theta : E -> Real)
    (htheta : forall edge, 0 < theta edge)
    (htheta' : forall edge, theta edge < Real.pi / 2)
    (primalExceptional : PrimalVertex -> Bool)
    (dualExceptional : DualVertex -> Bool)
    (primalKacWard : Matrix Q Q Complex)
    (dualKacWard : Matrix Qstar Qstar Complex)
    (primalCoefficient : CriticalKacWardRibbonCoefficientIdentification
      R character primalKacWard theta primalExceptional)
    (dualCoefficient : CriticalKacWardRibbonCoefficientIdentification
      Rdual dualCharacter dualKacWard
      (fun edge => Real.pi / 2 - theta edge) dualExceptional)
    (gaussBonnet : IsoradialDualGaussBonnetParity
      PrimalVertex DualVertex R C primalExceptional dualExceptional) :
    kwIsoradialDualityNormalization DualVertex
        (fun edge => Real.pi / 2 - theta edge) *
        (1 - dualKacWard).det =
      kwIsoradialDualityNormalization PrimalVertex theta *
        (1 - primalKacWard).det :=
  normalized_isoradialKacWard_duality_of_gaussBonnet
    R C character hcharacter htotal theta htheta htheta'
    primalExceptional dualExceptional primalKacWard dualKacWard
    (primalCoefficient.toSubgraphCoefficientIdentification
      R character primalKacWard theta primalExceptional)
    (dualCoefficient.toDualSubgraphCoefficientIdentification
      Rdual dualCharacter dualKacWard
      (fun edge => Real.pi / 2 - theta edge) dualExceptional
      R character (ribbonBoundaryCharacterCoefficient_dual
        R Rdual boundaryIdentification character dualCharacter
        dualCharacter_reverse))
    gaussBonnet




theorem normalized_isoradialKacWard_duality_of_canonicalDualRibbon
    {PrimalVertex DualVertex Dart Q Qstar : Type*}
    [Fintype PrimalVertex] [Fintype DualVertex]
    [Fintype Dart] [DecidableEq Dart]
    [Fintype Q] [DecidableEq Q] [Fintype Qstar] [DecidableEq Qstar]
    (R : RibbonPermutationSystem E Dart) (C : CellularRibbonDualData R)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (hcharacter : forall (F : Finset E)
      (boundary : Fin (R.boundaryComponents F)), character F boundary ≠ 0)
    (htotal : forall F : Finset E, ∏ boundary, character F boundary = 1)
    (theta : E -> Real)
    (htheta : forall edge, 0 < theta edge)
    (htheta' : forall edge, theta edge < Real.pi / 2)
    (primalExceptional : PrimalVertex -> Bool)
    (dualExceptional : DualVertex -> Bool)
    (primalKacWard : Matrix Q Q Complex)
    (dualKacWard : Matrix Qstar Qstar Complex)
    (primalCoefficient : CriticalKacWardRibbonCoefficientIdentification
      R character primalKacWard theta primalExceptional)
    (dualCoefficient : CriticalKacWardRibbonCoefficientIdentification
      R.dualRibbonSystem (R.dualBoundaryCharacter character) dualKacWard
      (fun edge => Real.pi / 2 - theta edge) dualExceptional)
    (oddConeGaussBonnet : IsoradialOddConeGaussBonnetData
      PrimalVertex DualVertex R C primalExceptional dualExceptional) :
    kwIsoradialDualityNormalization DualVertex
        (fun edge => Real.pi / 2 - theta edge) *
        (1 - dualKacWard).det =
      kwIsoradialDualityNormalization PrimalVertex theta *
        (1 - primalKacWard).det :=
  normalized_isoradialKacWard_duality_of_ribbonCoefficients
    R C R.dualRibbonSystem character (R.dualBoundaryCharacter character)
    hcharacter htotal R.dualBoundaryIdentification
    (R.dualBoundaryCharacter_reverse character) theta htheta htheta'
    primalExceptional dualExceptional primalKacWard dualKacWard
    primalCoefficient dualCoefficient
    (oddConeGaussBonnet.toGaussBonnetParity
      R C primalExceptional dualExceptional)






structure CriticalIsoradialDualityCertificate
    (PrimalVertex DualVertex Dart Q Qstar : Type*)
    [Fintype PrimalVertex] [Fintype DualVertex]
    [Fintype Dart] [DecidableEq Dart]
    [Fintype Q] [DecidableEq Q] [Fintype Qstar] [DecidableEq Qstar]
    (R : RibbonPermutationSystem E Dart) (C : CellularRibbonDualData R)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (theta : E -> Real)
    (primalExceptional : PrimalVertex -> Bool)
    (dualExceptional : DualVertex -> Bool)
    (primalKacWard : Matrix Q Q Complex)
    (dualKacWard : Matrix Qstar Qstar Complex) where
  theta_pos : forall edge, 0 < theta edge
  theta_lt : forall edge, theta edge < Real.pi / 2
  character_ne : forall (F : Finset E)
    (boundary : Fin (R.boundaryComponents F)), character F boundary ≠ 0
  character_total : forall F : Finset E,
    ∏ boundary, character F boundary = 1
  primalCoefficient : CriticalKacWardRibbonCoefficientIdentification
    R character primalKacWard theta primalExceptional
  dualCoefficient : CriticalKacWardRibbonCoefficientIdentification
    R.dualRibbonSystem (R.dualBoundaryCharacter character) dualKacWard
      (fun edge => Real.pi / 2 - theta edge) dualExceptional
  oddConeGaussBonnet : IsoradialOddConeGaussBonnetData
    PrimalVertex DualVertex R C primalExceptional dualExceptional



theorem CriticalIsoradialDualityCertificate.normalized_det_eq
    {PrimalVertex DualVertex Dart Q Qstar : Type*}
    [Fintype PrimalVertex] [Fintype DualVertex]
    [Fintype Dart] [DecidableEq Dart]
    [Fintype Q] [DecidableEq Q] [Fintype Qstar] [DecidableEq Qstar]
    (R : RibbonPermutationSystem E Dart) (C : CellularRibbonDualData R)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (theta : E -> Real)
    (primalExceptional : PrimalVertex -> Bool)
    (dualExceptional : DualVertex -> Bool)
    (primalKacWard : Matrix Q Q Complex)
    (dualKacWard : Matrix Qstar Qstar Complex)
    (certificate : CriticalIsoradialDualityCertificate
      PrimalVertex DualVertex Dart Q Qstar R C
      character theta primalExceptional dualExceptional
      primalKacWard dualKacWard) :
    kwIsoradialDualityNormalization DualVertex
        (fun edge => Real.pi / 2 - theta edge) *
        (1 - dualKacWard).det =
      kwIsoradialDualityNormalization PrimalVertex theta *
        (1 - primalKacWard).det :=
  normalized_isoradialKacWard_duality_of_canonicalDualRibbon
    R C character certificate.character_ne certificate.character_total
    theta certificate.theta_pos certificate.theta_lt
    primalExceptional dualExceptional
    primalKacWard dualKacWard certificate.primalCoefficient
    certificate.dualCoefficient
    certificate.oddConeGaussBonnet

namespace FiniteCellularGraphEmbedding





theorem normalized_isoradialKacWard_duality
    {V DualVertex Q Qstar : Type*}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype DualVertex]
    [Fintype Q] [DecidableEq Q] [Fintype Qstar] [DecidableEq Qstar]
    (embedding : FiniteCellularGraphEmbedding G)
    (dualVertexCount_eq : embedding.faceCount = Fintype.card DualVertex)
    (character : forall F : Finset (finiteGraphEdge G),
      Fin (embedding.ribbonSystem.boundaryComponents F) -> Complex)
    (hcharacter : forall (F : Finset (finiteGraphEdge G))
      (boundary : Fin (embedding.ribbonSystem.boundaryComponents F)),
        character F boundary ≠ 0)
    (htotal : forall F : Finset (finiteGraphEdge G),
      ∏ boundary, character F boundary = 1)
    (theta : finiteGraphEdge G -> Real)
    (htheta : forall edge, 0 < theta edge)
    (htheta' : forall edge, theta edge < Real.pi / 2)
    (primalExceptional : V -> Bool)
    (dualExceptional : DualVertex -> Bool)
    (primalConeIndex : V -> Nat)
    (dualConeIndex : DualVertex -> Nat)
    (primalExceptional_iff : forall vertex,
      primalExceptional vertex = true ↔ primalConeIndex vertex % 2 = 1)
    (dualExceptional_iff : forall vertex,
      dualExceptional vertex = true ↔ dualConeIndex vertex % 2 = 1)
    (coneIndexGaussBonnet :
      (∑ vertex : V, primalConeIndex vertex) +
        (∑ vertex : DualVertex, dualConeIndex vertex) + 1 =
          embedding.genus)
    (primalKacWard : Matrix Q Q Complex)
    (dualKacWard : Matrix Qstar Qstar Complex)
    (primalExpansion : CriticalKacWardRibbonCoefficientIdentification
      embedding.ribbonSystem character primalKacWard theta
      primalExceptional)
    (dualExpansion : CriticalKacWardRibbonCoefficientIdentification
      embedding.ribbonSystem.dualRibbonSystem
      (embedding.ribbonSystem.dualBoundaryCharacter character) dualKacWard
      (fun edge => Real.pi / 2 - theta edge)
      dualExceptional) :
    kwIsoradialDualityNormalization DualVertex
        (fun edge => Real.pi / 2 - theta edge) *
        (1 - dualKacWard).det =
      kwIsoradialDualityNormalization V theta *
        (1 - primalKacWard).det := by
  let oddConeGaussBonnet : IsoradialOddConeGaussBonnetData
      V DualVertex embedding.ribbonSystem embedding.cellularDualData
      primalExceptional dualExceptional :=
    { primalVertexCount_eq := rfl
      dualVertexCount_eq := dualVertexCount_eq
      primalConeIndex := primalConeIndex
      dualConeIndex := dualConeIndex
      primalExceptional_iff := primalExceptional_iff
      dualExceptional_iff := dualExceptional_iff
      coneIndexGaussBonnet := coneIndexGaussBonnet }
  exact normalized_isoradialKacWard_duality_of_canonicalDualRibbon
    embedding.ribbonSystem embedding.cellularDualData character
    hcharacter htotal theta htheta htheta' primalExceptional dualExceptional
    primalKacWard dualKacWard primalExpansion dualExpansion
    oddConeGaussBonnet

end FiniteCellularGraphEmbedding

end StatMech.FrontierA
