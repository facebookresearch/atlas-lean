/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Quillen.KSpaceFunctorCoherence
public import MathlibExt.Topology.Homotopy.LoopMapUnitTraceNormalization

/-!
# The original exact-functor NatIso unit path

The actual canonical NatIso homotopy and its original chosen root-family
homotopy specialize the whole loop-map unit comparison. Public original
map values derive both endpoint casts on the original NQ carriers.
-/

public section

noncomputable section

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open scoped ZeroObject ContinuousMap

universe uC vC uD vD

namespace AlgebraicKTheory

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]

/-- The actual canonical functor unit image is the original whole unit
loop of its same chosen root, through the original mapped-loop values. -/
theorem NQKSpaceFunctorMap_unit_eq_rootUnitLoopFamily
    (F : C ⥤ D) [F.Additive] [F.IsExact] :
    NQKSpaceFunctorMap F (Path.refl (NQReal.basepoint C)) =
      ContinuousMap.rootUnitLoopFamily
        (fun p : Path ((NQRealFunctorWeaklyPointed F).hom (NQReal.basepoint C))
          (NQReal.basepoint D) => p) continuous_eval
            (NQRealFunctorWeaklyPointed F).rootPath := by
  let f := NQRealFunctorWeaklyPointed F
  let e : NQKSpace C := Path.refl (NQReal.basepoint C)
  have hMap : NQKSpaceFunctorMap F e = f.loopMap e :=
    (NQKSpaceFunctorMap_apply F e).trans
      (ContinuousMap.WeaklyPointed.loopMap_apply f e).symm
  exact hMap.trans (ContinuousMap.WeaklyPointed.loopMapUnit_eq_rootUnitLoopFamily
    f.hom f.rootPath)

/-- The actual original NatIso unit Path, including its SAME original
chosen root homotopy, compares with the two original root contractions.
Both NQ endpoint casts are computed from the actual canonical unit images. -/
theorem NQKSpaceFunctorNatIsoUnitPath_homotopic_rootUnits (F G : C ⥤ D)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] (e : F ≅ G) :
    (NQKSpaceFunctorNatIsoUnitPath F G e).Homotopic
      ((((ContinuousMap.rootUnitContraction
        (fun p : Path ((NQRealFunctorWeaklyPointed F).hom (NQReal.basepoint C))
          (NQReal.basepoint D) => p) continuous_eval).evalAt
            (NQRealFunctorWeaklyPointed F).rootPath).trans
              ((ContinuousMap.rootUnitContraction
                (fun p : Path ((NQRealFunctorWeaklyPointed G).hom (NQReal.basepoint C))
                  (NQReal.basepoint D) => p) continuous_eval).evalAt
                    (NQRealFunctorWeaklyPointed G).rootPath).symm).cast
                      (NQKSpaceFunctorMap_unit_eq_rootUnitLoopFamily F)
                      (NQKSpaceFunctorMap_unit_eq_rootUnitLoopFamily G)) := by
  let x := NQReal.basepoint C
  let f := NQRealFunctorWeaklyPointed F
  let g := NQRealFunctorWeaklyPointed G
  let H := NQRealFunctorNatIsoHomotopy F G e
  let Hp := (NQRealFunctorNatIso_rootPath_homotopic F G e).some
  let L := ContinuousMap.WeaklyPointed.loopMapHomotopyOfMap f g H Hp
  let eC : NQKSpace C := Path.refl x
  let T := L.evalAt eC
  have hF : NQKSpaceFunctorMap F eC = f.loopMap eC :=
    (NQKSpaceFunctorMap_apply F eC).trans
      (ContinuousMap.WeaklyPointed.loopMap_apply f eC).symm
  have hG : NQKSpaceFunctorMap G eC = g.loopMap eC :=
    (NQKSpaceFunctorMap_apply G eC).trans
      (ContinuousMap.WeaklyPointed.loopMap_apply g eC).symm
  have hActual : NQKSpaceFunctorNatIsoUnitPath F G e = T.cast hF hG := by
    apply Path.ext
    funext t
    apply Path.ext
    funext s
    change ((NQKSpaceFunctorNatIsoUnitPath F G e).toContinuousMap.toFun t :
        unitInterval → NQReal D) s =
      (L.toContinuousMap.toFun (t, eC) : unitInterval → NQReal D) s
    have hWhole := NQKSpaceFunctorNatIsoHomotopy_loopMap_value F G e t eC
    exact (NQKSpaceFunctorNatIsoUnitPath_apply F G e t s).trans
      (congrArg (fun gamma : NQKSpace D => (gamma : unitInterval → NQReal D) s) hWhole)
  obtain ⟨K⟩ := ContinuousMap.WeaklyPointed.loopMapHomotopyOfMap_unitTrace_homotopic
    f g H Hp
  refine ⟨(K.pathCast hF hG).cast hActual.symm ?_⟩
  apply Path.ext
  funext t
  rfl

end AlgebraicKTheory

end
