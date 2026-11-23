/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.SourceConnectorLoopHomotopy
public import MathlibExt.Topology.Homotopy.RootUnitTraceComparison
public import MathlibExt.Topology.Homotopy.LoopMapUnitTraceNormalization
public import MathlibExt.Topology.Homotopy.LoopMapCompositionUnitTrace

/-!
# EXACT original081 and original201 unit paths

Both actual units evaluate the SAME original root path on the SAME three-piece
interval word and its original affine contraction. Every pair of unit/loop
times is recovered explicitly. The actual unit paths are equal; no chosen
unit is substituted, no π1 action or root outcome is assumed.
-/

public section

noncomputable section

open unitInterval
open scoped Topology

universe u v

namespace ContinuousMap

private theorem original081Clock_eq201 (s : I) :
    (((Path.id : Path (0 : I) (1 : I)).symm.trans
      ((Path.refl (0 : I)).trans (Path.id : Path (0 : I) (1 : I)))) s) = rootUnitClock s := by
  apply Subtype.ext
  rw [rootUnitClock_coe]
  simp only [Path.trans_apply, Path.symm_apply, Path.refl_apply, Path.id_apply]
  split_ifs <;> rfl

namespace WeaklyPointed

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {x : X} {y : Y}

/-- Every original081 unit and loop time is the EXACT original201 root
contraction value, preserving the actual original root and interval clocks. -/
theorem originalLoopOwnUnit_value201 (F : WeaklyPointed x y) (t s : I) :
    (loopUnitRootPath F).toContinuousMap.toFun t s =
      rootUnitContraction (fun p : Path (F.hom x) y => p) continuous_eval
        (t, F.rootPath) s := by
  have h081 := loopUnitRootPath_value F t s
  have hClock := HomotopyRel.sourceLoopUnitTemplateContraction_apply t s
  have h201 := rootUnitContraction_apply
    (fun p : Path (F.hom x) y => p) continuous_eval t F.rootPath s
  exact h081.trans ((congrArg F.rootPath hClock).trans
    ((congrArg (fun c => F.rootPath (Set.Icc.convexComb c 1 t))
      (original081Clock_eq201 s)).trans h201.symm))

private theorem originalLoopOwnUnitEq201Computed (F : WeaklyPointed x y) :
    loopUnitRootPath F =
      ((rootUnitContraction (fun p : Path (F.hom x) y => p) continuous_eval).evalAt F.rootPath).cast
        (loopMapUnit_eq_rootUnitLoopFamily F.hom F.rootPath) rfl := by
  apply Path.ext
  funext t
  apply Path.ext
  funext s
  exact originalLoopOwnUnit_value201 F t s

/-- EXACT equality of original081 and original201 designated units, from
all-time values. Both original choices/families are retained, not replaced. -/
theorem originalLoopOwnUnit_eq201 (F : WeaklyPointed x y) :
    loopUnitRootPath F =
      ((rootUnitContraction (fun p : Path (F.hom x) y => p) continuous_eval).evalAt F.rootPath).cast
        (loopMapUnit_eq_rootUnitLoopFamily F.hom F.rootPath) rfl :=
  originalLoopOwnUnitEq201Computed F

/-- The ACTUAL original full map-homotopy unit trace is compatible with
BOTH EXACT original081 units, via their proved all-time201 equality. -/
theorem originalLoopMapHomotopy_OWNunit (f g : WeaklyPointed x y)
    (H : Homotopy f.hom g.hom)
    (Hp : f.rootPath.Homotopy ((H.evalAt x).trans g.rootPath)) :
    (((loopMapHomotopyOfMap f g H Hp).evalAt (Path.refl x)).trans
      (loopUnitRootPath g)).Homotopic (loopUnitRootPath f) := by
  have h := loopMapHomotopyOfMap_unitTrace_homotopic f g H Hp
  let U := loopUnitRootPath f
  let V := loopUnitRootPath g
  let Uf := (rootUnitContraction (fun p : Path (f.hom x) y => p) continuous_eval).evalAt f.rootPath
  let Ug := (rootUnitContraction (fun p : Path (g.hom x) y => p) continuous_eval).evalAt g.rootPath
  have hValue : (Uf.trans Ug.symm).cast
      (loopMapUnit_eq_rootUnitLoopFamily f.hom f.rootPath)
      (loopMapUnit_eq_rootUnitLoopFamily g.hom g.rootPath) = U.trans V.symm := by
    apply Path.ext
    funext t
    have hU := originalLoopOwnUnit_eq201 f
    have hV := originalLoopOwnUnit_eq201 g
    dsimp only [U, V]
    rw [hU, hV]
    rfl
  obtain ⟨K⟩ := h
  have hTrace : ((loopMapHomotopyOfMap f g H Hp).evalAt (Path.refl x)).Homotopic
      (U.trans V.symm) := ⟨K.cast rfl hValue⟩
  exact (hTrace.hcomp (Path.Homotopic.refl V)).trans
    ((Path.Homotopic.trans_assoc U V.symm V).trans
      (((Path.Homotopic.refl U).hcomp (Path.Homotopic.symm_trans V)).trans
        (Path.Homotopic.trans_refl U)))

end WeaklyPointed

end ContinuousMap

end
