/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsoradialRibbonBoundaryParity










namespace StatMech.FrontierA

open Finset Equiv
open scoped BigOperators symmDiff

variable {D E K : Type*} [Fintype D] [DecidableEq D]
  [Fintype E] [DecidableEq E]




structure CellularRibbonDualData (R : RibbonPermutationSystem E D) where
  primalVertexCount : Nat
  dualVertexCount : Nat
  genus : Nat
  rotationCycles_eq_primalVertexCount :
    permCycleCount R.rotation = primalVertexCount
  cellularEuler :
    primalVertexCount + dualVertexCount + 2 * genus =
      Fintype.card E + 2

namespace CellularRibbonDualData

variable {R : RibbonPermutationSystem E D}

omit [DecidableEq E] in


theorem eulerBaseParity (C : CellularRibbonDualData R) :
    (Fintype.card E + permCycleCount R.rotation) % 2 =
      C.dualVertexCount % 2 := by
  rw [C.rotationCycles_eq_primalVertexCount]
  have h := C.cellularEuler
  omega



theorem boundaryParity (C : CellularRibbonDualData R) :
    forall F : Finset E,
      (Fᶜ.card + R.boundaryComponents F) % 2 =
        C.dualVertexCount % 2 :=
  R.boundaryParity_eq_dualVertexCount C.dualVertexCount C.eulerBaseParity

end CellularRibbonDualData



noncomputable def ribbonBoundaryCharacterCoefficient
    [Field K] (R : RibbonPermutationSystem E D)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> K) (F : Finset E) : K :=
  ∏ b : Fin (R.boundaryComponents F), (1 - character F b)



noncomputable def dualRibbonBoundaryCharacterCoefficient
    [Field K] (R : RibbonPermutationSystem E D)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> K) (Fstar : Finset E) : K :=
  ∏ b : Fin (R.boundaryComponents Fstarᶜ),
    (1 - (character Fstarᶜ b)⁻¹)



theorem dualRibbonBoundaryCharacterCoefficient_compl
    [Field K] (R : RibbonPermutationSystem E D)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> K)
    (hcharacter : forall (F : Finset E)
      (b : Fin (R.boundaryComponents F)), character F b ≠ 0)
    (htotal : forall F : Finset E, ∏ b, character F b = 1)
    (F : Finset E) :
    dualRibbonBoundaryCharacterCoefficient R character Fᶜ =
      (-1 : K) ^ R.boundaryComponents F *
        ribbonBoundaryCharacterCoefficient R character F := by
  have h := prod_one_sub_inv_of_prod_eq_one
    (B := (Finset.univ : Finset (Fin (R.boundaryComponents F))))
    (character F) (fun b _ => hcharacter F b) (htotal F)
  rw [dualRibbonBoundaryCharacterCoefficient, compl_compl,
    ribbonBoundaryCharacterCoefficient]
  simpa using h




theorem cellularRibbon_kwDualSubgraphSum_complement_duality
    [Field K] (R : RibbonPermutationSystem E D)
    (C : CellularRibbonDualData R)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> K)
    (hcharacter : forall (F : Finset E)
      (b : Fin (R.boundaryComponents F)), character F b ≠ 0)
    (htotal : forall F : Finset E, ∏ b, character F b = 1)
    (weight : E -> K) (hweight : forall e, weight e ≠ 0) :
    kwDualSubgraphSum
        (dualRibbonBoundaryCharacterCoefficient R character)
        (fun e => -(weight e)⁻¹) =
      (-1 : K) ^ C.dualVertexCount *
        ((∏ e : E, weight e)⁻¹ *
          kwDualSubgraphSum
            (ribbonBoundaryCharacterCoefficient R character) weight) := by
  apply kwDualSubgraphSum_complement_duality_of_boundaryParity
    (ribbonBoundaryCharacterCoefficient R character)
    (dualRibbonBoundaryCharacterCoefficient R character)
    weight hweight R.boundaryComponents C.dualVertexCount
  · exact dualRibbonBoundaryCharacterCoefficient_compl R character
      hcharacter htotal
  · exact C.boundaryParity



theorem cellularRibbon_isoradialCritical_subgraphSum_duality
    (R : RibbonPermutationSystem E D)
    (C : CellularRibbonDualData R)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (hcharacter : forall (F : Finset E)
      (b : Fin (R.boundaryComponents F)), character F b ≠ 0)
    (htotal : forall F : Finset E, ∏ b, character F b = 1)
    (theta : E -> Real)
    (htheta : forall e, 0 < theta e)
    (htheta' : forall e, theta e < Real.pi / 2) :
    kwDualSubgraphSum
        (dualRibbonBoundaryCharacterCoefficient R character)
        (fun e => isoradialCriticalMu (Real.pi / 2 - theta e)) =
      (-1 : Complex) ^ C.dualVertexCount *
        ((∏ e : E, isoradialCriticalMu (theta e))⁻¹ *
          kwDualSubgraphSum
            (ribbonBoundaryCharacterCoefficient R character)
            (fun e => isoradialCriticalMu (theta e))) := by
  have hweight : forall e, isoradialCriticalMu (theta e) ≠ 0 :=
    fun e => isoradialCriticalMu_ne_zero (htheta e) (htheta' e)
  simpa only [isoradialCriticalMu_dual] using
    cellularRibbon_kwDualSubgraphSum_complement_duality
    R C character hcharacter htotal
      (fun e => isoradialCriticalMu (theta e)) hweight

end StatMech.FrontierA
