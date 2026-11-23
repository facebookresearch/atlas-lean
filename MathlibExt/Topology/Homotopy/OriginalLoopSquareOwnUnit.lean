/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.OriginalLoopOwnUnitCalibration

/-!
# Actual original whole loop-square unit telescope

The two original composition traces and the middle original root-map trace
use the SAME designated081 units. Original relative path algebra telescopes
those actual full pieces without supplying a square-unit outcome.
-/

public section

noncomputable section

open scoped Topology

universe uX uY

namespace ContinuousMap

private theorem originalEvalTrans {X : Type uX} {Y : Type uY}
    [TopologicalSpace X] [TopologicalSpace Y] {f g h : C(X, Y)}
    (H : Homotopy f g) (K : Homotopy g h) (x : X) :
    (H.trans K).evalAt x = (H.evalAt x).trans (K.evalAt x) := by
  apply Path.ext
  funext t
  exact (Homotopy.trans_apply H K (t, x)).trans
    (Path.trans_apply (H.evalAt x) (K.evalAt x) t).symm

private theorem originalEvalSymm {X : Type uX} {Y : Type uY}
    [TopologicalSpace X] [TopologicalSpace Y] {f g : C(X, Y)}
    (H : Homotopy f g) (x : X) : H.symm.evalAt x = (H.evalAt x).symm := by
  apply Path.ext
  funext t
  rfl

/-- Genuine actual full three-piece square unit telescope. Exact callers
supply the internally derived original composition/root traces, not an
endpoint unit outcome. All original family clocks are retained. -/
theorem originalThreePieceLoopSquare_OWNunit
    {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
    {f a b g : C(X, Y)} (x : X) (y : Y)
    (H₁ : Homotopy a f) (H₂ : Homotopy a b) (H₃ : Homotopy b g)
    (Uf : Path (f x) y) (Ua : Path (a x) y)
    (Ub : Path (b x) y) (Ug : Path (g x) y)
    (h₁ : (H₁.evalAt x).Homotopic (Ua.trans Uf.symm))
    (h₂ : (H₂.evalAt x).Homotopic (Ua.trans Ub.symm))
    (h₃ : (H₃.evalAt x).Homotopic (Ub.trans Ug.symm)) :
    (((H₁.symm.trans (H₂.trans H₃)).evalAt x).trans Ug).Homotopic Uf := by
  let A := H₁.evalAt x
  let B := H₂.evalAt x
  let C := H₃.evalAt x
  have hFirst : A.symm.Homotopic (Uf.trans Ua.symm) := by
    obtain ⟨K⟩ := h₁
    refine ⟨K.symm₂.cast rfl ?_⟩
    simpa only [Path.symm_symm] using (Path.trans_symm Ua Uf.symm)
  have hInnerCancel : (Ub.symm.trans (Ub.trans Ug.symm)).Homotopic Ug.symm :=
    (Path.Homotopic.trans_assoc Ub.symm Ub Ug.symm).symm.trans
      (((Path.Homotopic.symm_trans Ub).hcomp (Path.Homotopic.refl Ug.symm)).trans
        (Path.Homotopic.refl_trans Ug.symm))
  have hInner : (B.trans C).Homotopic (Ua.trans Ug.symm) :=
    (h₂.hcomp h₃).trans
      ((Path.Homotopic.trans_assoc Ua Ub.symm (Ub.trans Ug.symm)).trans
        ((Path.Homotopic.refl Ua).hcomp hInnerCancel))
  have hOuterCancel : (Ua.symm.trans (Ua.trans Ug.symm)).Homotopic Ug.symm :=
    (Path.Homotopic.trans_assoc Ua.symm Ua Ug.symm).symm.trans
      (((Path.Homotopic.symm_trans Ua).hcomp (Path.Homotopic.refl Ug.symm)).trans
        (Path.Homotopic.refl_trans Ug.symm))
  have hTrace : (A.symm.trans (B.trans C)).Homotopic (Uf.trans Ug.symm) :=
    (hFirst.hcomp hInner).trans
      ((Path.Homotopic.trans_assoc Uf Ua.symm (Ua.trans Ug.symm)).trans
        ((Path.Homotopic.refl Uf).hcomp hOuterCancel))
  have hTotal := (hTrace.hcomp (Path.Homotopic.refl Ug)).trans
    ((Path.Homotopic.trans_assoc Uf Ug.symm Ug).trans
      (((Path.Homotopic.refl Uf).hcomp (Path.Homotopic.symm_trans Ug)).trans
        (Path.Homotopic.trans_refl Uf)))
  have hValue : (H₁.symm.trans (H₂.trans H₃)).evalAt x = A.symm.trans (B.trans C) :=
    (originalEvalTrans H₁.symm (H₂.trans H₃) x).trans
      (congrArg₂ Path.trans (originalEvalSymm H₁ x) (originalEvalTrans H₂ H₃ x))
  obtain ⟨K⟩ := hTotal
  exact ⟨K.cast (congrArg (fun P => P.trans Ug) hValue).symm rfl⟩

end ContinuousMap

end
