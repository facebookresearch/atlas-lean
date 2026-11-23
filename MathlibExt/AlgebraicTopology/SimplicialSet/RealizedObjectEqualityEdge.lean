/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizedCompStruct
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

/-!
# Realized edges for actual object equalities

An equality of category objects gives its original `eqToHom` edge. Appending
that edge changes only the endpoint view of the original path, up to an
endpoint-fixed path homotopy. The result follows from the actual degenerate
identity edge and the realized composition structure.
-/

noncomputable section

open CategoryTheory
open scoped Simplicial

universe u v

namespace SSet

/-- Appending the realized object-equality edge retains the whole original
path, with only its actual terminal vertex equality transported. -/
public theorem appendRealizedEqToHom {D : Type u} [Category.{v} D]
    {x y : D} {a : SSet.toTop.obj (nerve D)}
    (p : _root_.Path a (SSet.realizedVertex (X := nerve D)
      ((nerveEquiv (C := D)).symm x))) (h : x = y) :
    (p.trans (TopCat.pathEquiv (SSet.realizedEdgePath
      (nerve.edgeMk (C := D) (x := x) (y := y) (eqToHom h))))).Homotopic
      (p.cast rfl (congrArg (fun z : D => SSet.realizedVertex (X := nerve D)
        ((nerveEquiv (C := D)).symm z)) h).symm) := by
  cases h
  have hId : (TopCat.pathEquiv (SSet.realizedEdgePath
      (nerve.edgeMk (C := D) (x := x) (y := x) (𝟙 x)))).Homotopic
      (_root_.Path.refl (SSet.realizedVertex (X := nerve D)
        ((nerveEquiv (C := D)).symm x))) := by
    simpa only [nerve.edgeMk_id] using
      SSet.realizedEdgePath_id_homotopic (X := nerve D)
        ((nerveEquiv (C := D)).symm x)
  have hRefl :
      (p.trans (_root_.Path.refl (SSet.realizedVertex (X := nerve D)
        ((nerveEquiv (C := D)).symm x)))).Homotopic p :=
    ⟨_root_.Path.Homotopy.transRefl p⟩
  have hc := ((_root_.Path.Homotopic.refl p).hcomp hId).trans hRefl
  obtain ⟨H⟩ := hc
  have hp :
      p.trans (TopCat.pathEquiv (SSet.realizedEdgePath
        (nerve.edgeMk (C := D) (x := x) (y := x) (𝟙 x)))) =
      p.trans (TopCat.pathEquiv (SSet.realizedEdgePath
        (nerve.edgeMk (C := D) (x := x) (y := x) (eqToHom (rfl : x = x))))) :=
    congrArg (fun k : x ⟶ x => p.trans (TopCat.pathEquiv
      (SSet.realizedEdgePath (nerve.edgeMk (C := D) (x := x) (y := x) k))))
        (eqToHom_refl x (rfl : x = x)).symm
  have hq : p = p.cast rfl
      (congrArg (fun z : D => SSet.realizedVertex (X := nerve D)
        ((nerveEquiv (C := D)).symm z)) (rfl : x = x)).symm := by
    apply _root_.Path.ext
    funext t
    rfl
  exact ⟨_root_.Path.Homotopy.cast H hp hq⟩

/-- Realizing postcomposition by the actual object-equality morphism is
homotopic to the original realized edge with the same vertex cast. -/
public theorem realizedCompEqToHom {D : Type u} [Category.{v} D]
    {x y z : D} (f : x ⟶ y) (h : y = z) :
    (TopCat.pathEquiv (SSet.realizedEdgePath
      (nerve.edgeMk (C := D) (x := x) (y := z) (f ≫ eqToHom h)))).Homotopic
      ((TopCat.pathEquiv (SSet.realizedEdgePath
        (nerve.edgeMk (C := D) (x := x) (y := y) f))).cast rfl
          (congrArg (fun w : D => SSet.realizedVertex (X := nerve D)
            ((nerveEquiv (C := D)).symm w)) h).symm) := by
  obtain ⟨hc⟩ := (nerve.nonempty_compStruct_iff f (eqToHom h)
    (f ≫ eqToHom h)).mpr rfl
  exact (SSet.realizedCompStructHomotopic hc).trans
    (appendRealizedEqToHom (TopCat.pathEquiv (SSet.realizedEdgePath
      (nerve.edgeMk (C := D) (x := x) (y := y) f))) h)

end SSet

end
