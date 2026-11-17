/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Reconstruction by the original ambient evaluation and adjunctions

The map is computed by precomposing the actual ambient module-Hom
evaluation with L^E to R^E, taking its native tensor-Hom mate, then
taking the beta/projection mate. The source evaluation and both quotient
units are retained. The isomorphism of this reconstruction map is a
separate holonomic output.

Source: DK arXiv:1311.2374v2, Proposition 9.5.1; native adjunction units,
mates and inverse maps: Mathlib56a005855ea17e0b0958f73ec801ae140b0a1679,
Apache 2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.NativeAmbientReconstructionMaps

open _root_.CategoryTheory

universe uA uC uE vA vC vE
variable {A : Type uA} {C : Type uC} {E : Type uE}
  [Category.{vA} A] [Category.{vC} C] [Category.{vE} E]
  (Q : C ⥤ E) (Lrep Rrep : E ⥤ C)
  (LQ : Lrep ⊣ Q) (QR : Q ⊣ Rrep)
  [∀ K : E, IsIso (LQ.unit.app K)]
  (tensor : C ⥤ C ⥤ C) [∀ K : C, (tensor.obj K).IsLeftAdjoint]
  (pull : A ⥤ C) (push : C ⥤ A) (projection : pull ⊣ push)

/-- The actual left representative maps to the right-local source object through both native units. -/
def leftRepresentativeToSource (H : C) [IsIso (QR.unit.app H)] :
    Lrep.obj (Q.obj H) ⟶ H :=
  QR.unit.app (Lrep.obj (Q.obj H)) ≫
    Rrep.map (inv (LQ.unit.app (Q.obj H))) ≫ inv (QR.unit.app H)

/-- The original evaluation, its ambient tensor-Hom mate and its beta/projection mate. -/
def reconstructionMap (M : A) (H : C) [IsIso (QR.unit.app H)] (O : E)
    (evaluation : (tensor.obj H).obj (pull.obj M) ⟶ Rrep.obj O) :
    M ⟶ push.obj (((tensor.obj (Lrep.obj (Q.obj H))).rightAdjoint).obj (Rrep.obj O)) :=
  projection.homEquiv M _
    ((Adjunction.ofIsLeftAdjoint (tensor.obj (Lrep.obj (Q.obj H)))).homEquiv _ _
      ((tensor.map (leftRepresentativeToSource Q Lrep Rrep LQ QR H)).app (pull.obj M) ≫
        evaluation))

end MathlibExt.CategoryTheory.NativeAmbientReconstructionMaps
