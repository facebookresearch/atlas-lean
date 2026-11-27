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
evaluation with the counit `L^E Q H ⟶ H` of `L^E ⊣ Q`, taking its native
tensor-Hom mate, then taking the beta/projection mate. No invertibility of
the quotient units is assumed: when they are invertible, the counit is the
composite through `R^E` (`leftRepresentativeToSource_eq`). The isomorphism
of this reconstruction map is a separate holonomic output.

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
  (Q : C ⥤ E) (Lrep Rrep : E ⥤ C) (LQ : Lrep ⊣ Q)
  (tensor : C ⥤ C ⥤ C) [∀ K : C, (tensor.obj K).IsLeftAdjoint]
  (pull : A ⥤ C) (push : C ⥤ A) (projection : pull ⊣ push)

/-- The left representative of the class of a source object maps to it by the counit of
`L ⊣ Q`. -/
def leftRepresentativeToSource (H : C) : Lrep.obj (Q.obj H) ⟶ H :=
  LQ.counit.app H

/-- When the units of `L ⊣ Q` at `Q H` and of `Q ⊣ R` at `H` are invertible, the counit is the
composite through the right representative. -/
theorem leftRepresentativeToSource_eq (QR : Q ⊣ Rrep) (H : C)
    [IsIso (LQ.unit.app (Q.obj H))] [IsIso (QR.unit.app H)] :
    leftRepresentativeToSource Q Lrep LQ H =
      QR.unit.app (Lrep.obj (Q.obj H)) ≫ Rrep.map (inv (LQ.unit.app (Q.obj H))) ≫
        inv (QR.unit.app H) := by
  have hQ : Q.map (LQ.counit.app H) = inv (LQ.unit.app (Q.obj H)) :=
    IsIso.eq_inv_of_hom_inv_id (LQ.right_triangle_components H)
  have hnat : LQ.counit.app H ≫ QR.unit.app H =
      QR.unit.app (Lrep.obj (Q.obj H)) ≫ Rrep.map (Q.map (LQ.counit.app H)) :=
    QR.unit.naturality (LQ.counit.app H)
  rw [← hQ, ← Category.assoc, ← hnat, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rfl

/-- The original evaluation, its ambient tensor-Hom mate and its beta/projection mate. -/
def reconstructionMap (M : A) (H : C) (O : E)
    (evaluation : (tensor.obj H).obj (pull.obj M) ⟶ Rrep.obj O) :
    M ⟶ push.obj (((tensor.obj (Lrep.obj (Q.obj H))).rightAdjoint).obj (Rrep.obj O)) :=
  projection.homEquiv M _
    ((Adjunction.ofIsLeftAdjoint (tensor.obj (Lrep.obj (Q.obj H)))).homEquiv _ _
      ((tensor.map (leftRepresentativeToSource Q Lrep LQ H)).app (pull.obj M) ≫
        evaluation))

end MathlibExt.CategoryTheory.NativeAmbientReconstructionMaps
