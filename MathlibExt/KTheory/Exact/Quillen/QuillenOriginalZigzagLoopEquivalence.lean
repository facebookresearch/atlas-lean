/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Quillen.QuillenOriginalZigzagBasedInverse
public import MathlibExt.Topology.Homotopy.WeaklyPointedLoopHomotopyEquiv

/-!
# Both original Q/S loop legs retain their exact roots and full inverse families

Actual original352 based inverse data retain both exact forward realization
maps. Current227 loops those genuine equivalences using the EXACT original
weak-leg point paths. Their forward maps are the original loop legs and both
full inverse families are returned. No caller triangle/inverse/CW outcome.
-/

public section

noncomputable section

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open scoped Topology

universe u v

namespace AlgebraicKTheory

variable (C : Type u) [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- The standard Waldhausen structure on the original exact category `C`. -/
local instance originalZigzagLoopEquivWaldhausen : WaldhausenCategory C :=
  ExactCategory.waldhausenCategory C

/-- The Q-side loop equivalence uses the EXACT original Q-leg root and
SAME original forward map, retaining both complete227 inverse families. -/
def quillenOriginalQZigzagLoopEquiv :
    ContinuousMap.HomotopyEquiv (quillenStageGridDiagonalKSpace C) (NQKSpace C) :=
  (quillenOriginalQZigzagHomotopyEquiv C).weaklyPointedLoopHomotopyEquiv
    (quillenStageGridDiagonalReal.basepoint C)
    ((quillenStageGridToNQWeaklyPointed (C := C)).rootPath.cast
      (congrArg (fun f => f (quillenStageGridDiagonalReal.basepoint C))
        (quillenOriginalQZigzagHomotopyEquiv_toFun C)) rfl)

/-- The Stage-side loop equivalence uses the EXACT original composed leg
root and SAME forward map; both complete inverse families are retained. -/
def quillenOriginalStageZigzagLoopEquiv :
    ContinuousMap.HomotopyEquiv (quillenStageGridDiagonalKSpace C) (stageWeakDiagonalKSpace C) :=
  (quillenOriginalStageZigzagHomotopyEquiv C).weaklyPointedLoopHomotopyEquiv
    (quillenStageGridDiagonalReal.basepoint C)
    ((quillenStageGridToStageWeaklyPointed (C := C)).rootPath.cast
      (congrArg (fun f => f (quillenStageGridDiagonalReal.basepoint C))
        (quillenOriginalStageZigzagHomotopyEquiv_toFun C)) rfl)

private theorem originalWeakLegEqFromValues
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (f g : ContinuousMap.WeaklyPointed x y) (h : f.hom = g.hom)
    (hp : ∀ t, f.rootPath.toContinuousMap.toFun t = g.rootPath.toContinuousMap.toFun t) : f = g := by
  rcases f with ⟨f, p⟩
  rcases g with ⟨g, q⟩
  cases h
  have hP : p = q := by apply Path.ext; funext t; exact hp t
  cases hP
  rfl

private theorem originalQZigzagForwardLoopComputed :
    (quillenOriginalQZigzagLoopEquiv C).toFun = quillenStageGridToNQLoopMap (C := C) := by
  let E := quillenOriginalQZigzagHomotopyEquiv C
  let W := quillenStageGridToNQWeaklyPointed (C := C)
  let h := quillenOriginalQZigzagHomotopyEquiv_toFun C
  let p := W.rootPath.cast (congrArg (fun f => f (quillenStageGridDiagonalReal.basepoint C)) h) rfl
  have hW : (⟨E.toFun, p⟩ : ContinuousMap.WeaklyPointed
      (quillenStageGridDiagonalReal.basepoint C) (NQReal.basepoint C)) = W :=
    originalWeakLegEqFromValues _ _ h (fun _ => rfl)
  exact (ContinuousMap.HomotopyEquiv.weaklyPointedLoopHomotopyEquiv_toFun E
    (quillenStageGridDiagonalReal.basepoint C) p).trans
      (congrArg ContinuousMap.WeaklyPointed.loopMap hW)

/-- WHOLE Q-side forward map is EXACT original weakly pointed loop leg. -/
theorem quillenOriginalQZigzagLoopEquiv_toFun :
    (quillenOriginalQZigzagLoopEquiv C).toFun = quillenStageGridToNQLoopMap (C := C) :=
  originalQZigzagForwardLoopComputed C

private theorem originalStageZigzagForwardLoopComputed :
    (quillenOriginalStageZigzagLoopEquiv C).toFun = quillenStageGridToStageLoopMap (C := C) := by
  let E := quillenOriginalStageZigzagHomotopyEquiv C
  let W := quillenStageGridToStageWeaklyPointed (C := C)
  let h := quillenOriginalStageZigzagHomotopyEquiv_toFun C
  let p := W.rootPath.cast (congrArg (fun f => f (quillenStageGridDiagonalReal.basepoint C)) h) rfl
  have hW : (⟨E.toFun, p⟩ : ContinuousMap.WeaklyPointed
      (quillenStageGridDiagonalReal.basepoint C) (stageWeakDiagonalReal.basepoint C)) = W :=
    originalWeakLegEqFromValues _ _ h (fun _ => rfl)
  exact (ContinuousMap.HomotopyEquiv.weaklyPointedLoopHomotopyEquiv_toFun E
    (quillenStageGridDiagonalReal.basepoint C) p).trans
      (congrArg ContinuousMap.WeaklyPointed.loopMap hW)

/-- WHOLE Stage-side forward map is EXACT original weakly pointed composed loop leg. -/
theorem quillenOriginalStageZigzagLoopEquiv_toFun :
    (quillenOriginalStageZigzagLoopEquiv C).toFun = quillenStageGridToStageLoopMap (C := C) :=
  originalStageZigzagForwardLoopComputed C

/-- BOTH original full Q-loop inverse families are returned for the SAME
selected inverse and EXACT original forward loop map. -/
theorem quillenOriginalQZigzagLoopEquiv_both_inverse_families :
    Nonempty (ContinuousMap.Homotopy
      ((quillenOriginalQZigzagLoopEquiv C).invFun.comp (quillenStageGridToNQLoopMap (C := C)))
      (ContinuousMap.id (quillenStageGridDiagonalKSpace C))) ∧
    Nonempty (ContinuousMap.Homotopy
      ((quillenStageGridToNQLoopMap (C := C)).comp (quillenOriginalQZigzagLoopEquiv C).invFun)
      (ContinuousMap.id (NQKSpace C))) := by
  let E := quillenOriginalQZigzagLoopEquiv C
  have h := quillenOriginalQZigzagLoopEquiv_toFun C
  exact ⟨Nonempty.map (fun H => H.cast (congrArg (fun f => E.invFun.comp f) h) rfl) E.left_inv,
    Nonempty.map (fun H => H.cast (congrArg (fun f => f.comp E.invFun) h) rfl) E.right_inv⟩

/-- BOTH original full Stage-loop inverse families are returned for the
SAME selected inverse and EXACT original composed forward loop map. -/
theorem quillenOriginalStageZigzagLoopEquiv_both_inverse_families :
    Nonempty (ContinuousMap.Homotopy
      ((quillenOriginalStageZigzagLoopEquiv C).invFun.comp (quillenStageGridToStageLoopMap (C := C)))
      (ContinuousMap.id (quillenStageGridDiagonalKSpace C))) ∧
    Nonempty (ContinuousMap.Homotopy
      ((quillenStageGridToStageLoopMap (C := C)).comp (quillenOriginalStageZigzagLoopEquiv C).invFun)
      (ContinuousMap.id (stageWeakDiagonalKSpace C))) := by
  let E := quillenOriginalStageZigzagLoopEquiv C
  have h := quillenOriginalStageZigzagLoopEquiv_toFun C
  exact ⟨Nonempty.map (fun H => H.cast (congrArg (fun f => E.invFun.comp f) h) rfl) E.left_inv,
    Nonempty.map (fun H => H.cast (congrArg (fun f => f.comp E.invFun) h) rfl) E.right_inv⟩

end AlgebraicKTheory

end

public section

noncomputable section

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open scoped Topology

universe u v

namespace AlgebraicKTheory

variable (C : Type u) [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
attribute [local instance] originalZigzagLoopEquivWaldhausen

private theorem originalQZigzagLoopInverseValueComputed :
    (quillenOriginalQZigzagLoopEquiv C).invFun =
      ((quillenOriginalQZigzagHomotopyEquiv C).weaklyPointedLoopHomotopyEquiv
        (quillenStageGridDiagonalReal.basepoint C)
        ((quillenStageGridToNQWeaklyPointed (C := C)).rootPath.cast
          (congrArg (fun f => f (quillenStageGridDiagonalReal.basepoint C))
            (quillenOriginalQZigzagHomotopyEquiv_toFun C)) rfl)).invFun := rfl

/-- The actual corrected Q inverse is exactly the original protected loop
inverse with its SAME original weak-leg root and complete inverse families. -/
theorem quillenOriginalQZigzagLoopEquiv_invFun :
    (quillenOriginalQZigzagLoopEquiv C).invFun =
      ((quillenOriginalQZigzagHomotopyEquiv C).weaklyPointedLoopHomotopyEquiv
        (quillenStageGridDiagonalReal.basepoint C)
        ((quillenStageGridToNQWeaklyPointed (C := C)).rootPath.cast
          (congrArg (fun f => f (quillenStageGridDiagonalReal.basepoint C))
            (quillenOriginalQZigzagHomotopyEquiv_toFun C)) rfl)).invFun :=
  originalQZigzagLoopInverseValueComputed C

end AlgebraicKTheory

end
