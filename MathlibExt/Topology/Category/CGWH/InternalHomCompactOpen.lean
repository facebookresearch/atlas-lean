/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CGWH.GeneratedHomCompactOpen
public import MathlibExt.Topology.Category.CGWH.CartesianClosed

/-! # The original internal Hom with its actual compact-open forward map -/

noncomputable section
universe v
open Set Topology CategoryTheory
public section

namespace CGWH

/-- The actual compact-generation counit followed by the original raw
compact-open topology comparison. This is a continuous forward map from
the native internal Hom, with its original underlying functions. -/
@[expose] noncomputable def internalHomToCompactOpen
    (A B : CGWH.{v, v}) [T2Space A] : C(internalHom A B, C(A, B)) :=
  (generatedMapHomeomorphCompactOpenOfT2 A B :
      C(ContinuousMapGeneratedBy CompactlyGenerated.compactHausProbes.{v} A B, C(A, B))).comp
    (internalHomToRawGenerated A B).hom

/-- Its value is the SAME original underlying generated function. -/
theorem internalHomToCompactOpen_apply
    (A B : CGWH.{v, v}) [T2Space A] (h : internalHom A B) (a : A) :
    internalHomToCompactOpen A B h a =
      (WithGeneratedByTopology.equiv
        (X := CompactlyGenerated.compactHausProbes.{v})
        (Y := ContinuousMapGeneratedBy CompactlyGenerated.compactHausProbes.{v} A B) h :
          ContinuousMapGeneratedBy CompactlyGenerated.compactHausProbes.{v} A B) a := rfl


end CGWH
