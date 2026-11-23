/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Quillen.UniverseLift
public import MathlibExt.AlgebraicTopology.SimplicialSet.CGWHRealization
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationUniverseLift
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizationHausdorff
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.CWComplex
public import MathlibExt.Topology.CWComplex.UniverseLift
public import MathlibExt.Topology.Category.CGWH.Basic

/-!
# The actual native Quillen realization with independent compact probes

The CGWH object has exactly the original lifted realization carrier and
topology. Its independent probe data are transported from the realization
of the same lifted Quillen simplicial set. The marked point is the original
lifted zero vertex. The raw loop space receives no CGWH assertion.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits ZeroObject Topology TopologicalSpace
open scoped Simplicial

universe uR uM uObj uHom uNative uProbe

namespace AlgebraicKTheory.QuillenUniverseLift

variable (R : Type uR) [Ring R]

private abbrev probeQuillenSSet :=
  NQ (liftedCategory.{uR, uM, uObj, uHom} R)

private abbrev probeQuillenLiftedSSet :=
  SSet.uliftFunctor.{uNative,
    max (max (max uR uM + 1) uObj) (max (max uR uM) uHom)}.obj
      (probeQuillenSSet.{uR, uM, uObj, uHom} R)

/-- The fixed lifted Quillen simplicial realization carries genuine
compact-Hausdorff probe data in the independent probe universe. -/
public abbrev nativeQuillenProbeRealization :
    CGWH.{uProbe,
      max (max (max (max uR uM + 1) uObj) (max (max uR uM) uHom)) uNative} :=
  SSet.toCGWH.{uProbe,
    max (max (max (max uR uM + 1) uObj) (max (max uR uM) uHom)) uNative}.obj
      (SSet.uliftFunctor.{uNative,
        max (max (max uR uM + 1) uObj) (max (max uR uM) uHom)}.obj
          (NQ (liftedCategory.{uR, uM, uObj, uHom} R)))

/-- The actual realization comparison ends at the literal original native
carrier, with its unchanged topology. -/
public abbrev nativeQuillenProbeRealizationIso :
    (nativeQuillenProbeRealization.{uR, uM, uObj, uHom, uNative, uProbe} R).toTop ≅
      TopCat.of (nativeRealization.{uR, uM, uObj, uHom, uNative} R) :=
  SSet.realizationToTopIso.{uProbe,
      max (max (max (max uR uM + 1) uObj) (max (max uR uM) uHom)) uNative}.app
      (SSet.uliftFunctor.{uNative,
        max (max (max uR uM + 1) uObj) (max (max uR uM) uHom)}.obj
          (NQ (liftedCategory.{uR, uM, uObj, uHom} R))) ≪≫
    SSet.toTopULiftIso.{
      max (max (max uR uM + 1) uObj) (max (max uR uM) uHom), uNative}.app
        (NQ (liftedCategory.{uR, uM, uObj, uHom} R))

/-- The comparison is a homeomorphism of the actual original carriers. -/
public def nativeQuillenProbeRealizationHomeomorph :
    (nativeQuillenProbeRealization.{uR, uM, uObj, uHom, uNative, uProbe} R) ≃ₜ
      nativeRealization.{uR, uM, uObj, uHom, uNative} R :=
  TopCat.homeoOfIso
    (nativeQuillenProbeRealizationIso.{uR, uM, uObj, uHom, uNative, uProbe} R)

/-- The forward comparison uses the original two public realization maps. -/
public theorem nativeQuillenProbeRealizationIso_hom_recipe :
    (nativeQuillenProbeRealizationIso.{uR, uM, uObj, uHom, uNative, uProbe} R).hom =
      (SSet.realizationToTopIso.{uProbe,
        max (max (max (max uR uM + 1) uObj) (max (max uR uM) uHom)) uNative}.app
          (SSet.uliftFunctor.{uNative,
            max (max (max uR uM + 1) uObj) (max (max uR uM) uHom)}.obj
              (NQ (liftedCategory.{uR, uM, uObj, uHom} R)))).hom ≫
        (SSet.toTopULiftIso.{
          max (max (max uR uM + 1) uObj) (max (max uR uM) uHom), uNative}.app
            (NQ (liftedCategory.{uR, uM, uObj, uHom} R))).hom := rfl

/-- The inverse comparison retains the same two public realization inverses. -/
public theorem nativeQuillenProbeRealizationIso_inv_recipe :
    (nativeQuillenProbeRealizationIso.{uR, uM, uObj, uHom, uNative, uProbe} R).inv =
      (SSet.toTopULiftIso.{
        max (max (max uR uM + 1) uObj) (max (max uR uM) uHom), uNative}.app
          (NQ (liftedCategory.{uR, uM, uObj, uHom} R))).inv ≫
        (SSet.realizationToTopIso.{uProbe,
          max (max (max (max uR uM + 1) uObj) (max (max uR uM) uHom)) uNative}.app
            (SSet.uliftFunctor.{uNative,
              max (max (max uR uM + 1) uObj) (max (max uR uM) uHom)}.obj
                (NQ (liftedCategory.{uR, uM, uObj, uHom} R)))).inv := rfl

/-- Compact generation is derived with the actual independently sized
probe data, and transported to the unchanged native topology. -/
public theorem nativeQuillenRealization_uCompactlyGeneratedSpace :
    UCompactlyGeneratedSpace.{uProbe}
      (nativeRealization.{uR, uM, uObj, uHom, uNative} R) := by
  let M := nativeQuillenProbeRealization.{uR, uM, uObj, uHom, uNative, uProbe} R
  let h := nativeQuillenProbeRealizationHomeomorph.{uR, uM, uObj, uHom, uNative, uProbe} R
  let _ : UCompactlyGeneratedSpace.{uProbe} M := inferInstance
  exact uCompactlyGeneratedSpace_of_coinduced h.continuous_toFun h.coinduced_eq.symm

/-- Hausdorffness belongs to the original lifted Quillen realization. -/
public theorem nativeQuillenRealization_t2Space :
    T2Space (nativeRealization.{uR, uM, uObj, uHom, uNative} R) := by
  let C := liftedCategory.{uR, uM, uObj, uHom} R
  let _ : T2Space (NQReal C) := SSet.realization_t2Space (NQ C)
  change T2Space (ULift.{uNative} (NQReal C))
  infer_instance

/-- The original Quillen realization's actual CW cells lift to the same
native carrier. No CW model is an input. -/
public noncomputable def nativeQuillenRealizationClassicalCW :
    Topology.CWComplex
      (Set.univ : Set (nativeRealization.{uR, uM, uObj, uHom, uNative} R)) := by
  let C := liftedCategory.{uR, uM, uObj, uHom} R
  let _ : Topology.CWComplex (Set.univ : Set (NQReal C)) :=
    SSet.instCWComplexToTop (NQ C)
  exact Topology.CWComplex.uliftCWComplex.{
    max (max (max uR uM + 1) uObj) (max (max uR uM) uHom), uNative} (NQReal C)

/-- The actual native Quillen realization, bundled using the independently
derived compact probes. Its underlying space and topology are unchanged. -/
public abbrev nativeQuillenRealizationBundle :
    CGWH.{uProbe,
      max (max (max (max uR uM + 1) uObj) (max (max uR uM) uHom)) uNative} := by
  let X := nativeRealization.{uR, uM, uObj, uHom, uNative} R
  let _ : UCompactlyGeneratedSpace.{uProbe} X :=
    nativeQuillenRealization_uCompactlyGeneratedSpace.{uR, uM, uObj, uHom, uNative, uProbe} R
  let _ : T2Space X := nativeQuillenRealization_t2Space.{uR, uM, uObj, uHom, uNative} R
  let _ : UWeakHausdorffSpace.{uProbe} X := uWeakHausdorffSpaceOfT2 X
  exact CGWH.of X

/-- The underlying TopCat is literally the original native realization. -/
public theorem nativeQuillenRealizationBundle_toTop :
    (nativeQuillenRealizationBundle.{uR, uM, uObj, uHom, uNative, uProbe} R).toTop =
      TopCat.of (nativeRealization.{uR, uM, uObj, uHom, uNative} R) := rfl

/-- The bundle keeps the exact original lifted zero vertex. -/
public abbrev nativeQuillenRealizationBundlePoint :
    nativeQuillenRealizationBundle.{uR, uM, uObj, uHom, uNative, uProbe} R :=
  nativeBasepoint.{uR, uM, uObj, uHom, uNative} R

/-- The bundled point is the same literal native zero vertex. -/
public theorem nativeQuillenRealizationBundlePoint_eq :
    nativeQuillenRealizationBundlePoint.{uR, uM, uObj, uHom, uNative, uProbe} R =
      nativeBasepoint.{uR, uM, uObj, uHom, uNative} R := rfl

/-- The bundle's raw loops are the original raw native loop space. -/
public theorem nativeQuillenRealizationBundle_rawLoopSpace_eq :
    LoopSpace
        (nativeQuillenRealizationBundle.{uR, uM, uObj, uHom, uNative, uProbe} R).toTop
        (nativeQuillenRealizationBundlePoint.{uR, uM, uObj, uHom, uNative, uProbe} R) =
      nativeRawLoopSpace.{uR, uM, uObj, uHom, uNative} R := rfl

/-- The bundle's constant loop is the original raw native constant loop. -/
public theorem nativeQuillenRealizationBundle_constantLoop_eq (R : Type uR) [Ring R] :
    Path.refl
        (nativeQuillenRealizationBundlePoint.{uR, uM, uObj, uHom, uNative, uProbe} R) =
      nativeConstantLoop.{uR, uM, uObj, uHom, uNative} R := by
  let p := nativeConstantLoop.{uR, uM, uObj, uHom, uNative} R
  let z := OriginalQZeroComparison.zeroQVertex
    (C := liftedCategory.{uR, uM, uObj, uHom} R)
  have hDown (t : unitInterval) : (p t).down = z := by
    have hc := congrArg
      (fun q : originalLoops.{uR, uM, uObj, uHom} R => q t)
      (rawNativeCarrierDown_constant.{uR, uM, uObj, uHom, uNative} R)
    exact (rawNativeCarrierDown_apply.{uR, uM, uObj, uHom, uNative} R p t).symm.trans hc
  have hBase : (nativeBasepoint.{uR, uM, uObj, uHom, uNative} R).down = z :=
    (congrArg ULift.down p.source.symm).trans (hDown 0)
  change Path.refl (nativeBasepoint.{uR, uM, uObj, uHom, uNative} R) = p
  apply Path.ext
  funext t
  apply ULift.ext
  exact hBase.trans (hDown t).symm

/-- The bundled native realization retains its derived Hausdorff topology. -/
public theorem nativeQuillenRealizationBundle_t2Space :
    T2Space (nativeQuillenRealizationBundle.{uR, uM, uObj, uHom, uNative, uProbe} R) := by
  let _ : T2Space (nativeRealization.{uR, uM, uObj, uHom, uNative} R) :=
    nativeQuillenRealization_t2Space.{uR, uM, uObj, uHom, uNative} R
  let e := eqToIso
    (nativeQuillenRealizationBundle_toTop.{uR, uM, uObj, uHom, uNative, uProbe} R)
  exact (TopCat.homeoOfIso e).symm.t2Space

/-- The bundled native realization has the same actual lifted CW structure. -/
public noncomputable def nativeQuillenRealizationBundleClassicalCW :
    Topology.CWComplex (Set.univ : Set
      (nativeQuillenRealizationBundle.{uR, uM, uObj, uHom, uNative, uProbe} R)) := by
  change Topology.CWComplex
    (Set.univ : Set (nativeRealization.{uR, uM, uObj, uHom, uNative} R))
  exact nativeQuillenRealizationClassicalCW.{uR, uM, uObj, uHom, uNative} R

end AlgebraicKTheory.QuillenUniverseLift

end
