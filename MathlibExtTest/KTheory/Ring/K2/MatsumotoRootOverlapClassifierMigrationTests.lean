/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.KTheory.Ring.K2.MatsumotoTitsBruhatWeylCommutation

/-!
# Tests for the Matsumoto root-overlap classifier migration

These tests exercise the preserved historical surface after its proofs are
routed through `adjacentOverlapClass`, and keep the canonical Weyl--Weyl and
Fin-3 endpoints visible through the historical importing module.
-/

@[expose] public section

noncomputable section

open Matrix.GeneralLinearGroup
open MatsumotoBruhatOppositeWeylTransport
open MatsumotoTitsMonomialExtension
open MatsumotoTitsWeylLift
open PermutationBilinearCocycle

universe u

namespace MatsumotoTitsBruhatFiber

variable {F : Type u} [Field F] {n : ℕ}
variable {i j k l : Fin n} (hij : i ⋖ j) (hkl : k ⋖ l)

example (M : MonomialBase Fˣ (Fin n)) :
    PosOverlapLR M hij hkl ↔ PosOverlapRL M hij hkl :=
  posOverlapLR_iff_posOverlapRL M

example (M : MonomialBase Fˣ (Fin n)) :
    NegOverlapLR M hij hkl ↔ NegOverlapRL M hij hkl :=
  negOverlapLR_iff_negOverlapRL M

example (M : MonomialBase Fˣ (Fin n))
    (hPos : PosOverlapRL M hij hkl) :
    ¬ (rightMulWeylBase M hkl).right.symm i <
      (rightMulWeylBase M hkl).right.symm j :=
  leftOrder_rightMul_of_posOverlapRL M hPos

example (M : MonomialBase Fˣ (Fin n))
    (hNeg : NegOverlapLR M hij hkl) :
    (leftMulWeylBase M hij).right k <
      (leftMulWeylBase M hij).right l :=
  rightOrder_leftMul_of_negOverlapLR M hNeg

example (M : MonomialBase Fˣ (Fin n))
    (hNotPos : ¬ PosOverlapLR M hij hkl)
    (hNotNeg : ¬ NegOverlapLR M hij hkl) :
    (M.right k < M.right l) ↔
      (leftMulWeylBase M hij).right k <
        (leftMulWeylBase M hij).right l :=
  rightOrder_leftMul_preserved_iff M hNotPos hNotNeg

example (s : Matrix.SpecialLinearGroup (Fin n) F) :
    leftWeylMultiplier hij (rightWeylSLPerm hkl s) *
        hmTitsSection (bruhatMiddle s) * rightWeylMultiplier hkl s =
      leftWeylMultiplier hij s * hmTitsSection (bruhatMiddle s) *
        rightWeylMultiplier hkl (leftWeylSLPerm hij s) :=
  weyl_weyl_HMTits_identity_canonical hij hkl s

example (F : Type u) [Field F] (a : Fˣ) :
    projHom F 3
        (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) (by decide) a *
          weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ) *
          weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ)) =
      projHom F 3
        (weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ) *
          weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ) *
          weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) (by decide) a) :=
  fin3_weylHMTits_cycle_proj F a

#check fin3_weylHMTits_cycle
#check fin3_weylHMTits_cycle_conj
#check fin3_hTits_cycle_conj
#check fin3_weyl01_conj_hTits01
#check MatsumotoBruhatOppositeWeylTransport.instDecPosOverlapLR
#check MatsumotoBruhatOppositeWeylTransport.instDecNegOverlapLR
#check MatsumotoBruhatOppositeWeylTransport.instDecPosOverlapRL
#check MatsumotoBruhatOppositeWeylTransport.instDecNegOverlapRL

end MatsumotoTitsBruhatFiber

end
