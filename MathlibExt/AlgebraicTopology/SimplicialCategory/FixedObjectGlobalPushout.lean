/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CarrierLabelReadback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# The SAME full fixed-object pushout is the genuine varying-object carrier pushout

Every original fixed-object map has the SAME full object-label family.
The supplied original carrier cocone therefore has one common actual
object function on all four corners. Canonical original reindexing and
whole-map readback retain every full Hom. The genuine fixed-object
pushout then supplies the actual full carrier universal property, with
no global pushout or desired weak conclusion as an input.
-/

noncomputable section
universe u
open CategoryTheory Limits

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.GlobalPushout
variable {O : Type u} {A B C P : FixedObjects O}
  {f : A ⟶ B} {g : A ⟶ C} {j : B ⟶ P} {k : C ⟶ P}
  (sq : IsPushout f g j k)

include sq in
/-- The SAME whole original fixed-object square commutes after retaining its actual carrier maps. -/
theorem condition : f.val ≫ j.val = g.val ≫ k.val :=
  congrArg (fun h : A ⟶ P => h.val) sq.w

/-- The complete original carrier pushout cocone retains the SAME two supplied full original
legs. -/
def cocone : PushoutCocone f.val g.val := PushoutCocone.mk j.val k.val (condition sq)

variable (s : PushoutCocone f.val g.val)

/-- Read the actual original common object function at every original fixed label. -/
def labels (o : O) : s.pt := s.inl.obj (vertex B o)

/-- The SAME original right object assignment agrees at every whole original fixed label. -/
theorem right_labels (o : O) : s.inr.obj (vertex C o) = labels s o := by
  have ho := congrArg (fun h : A.val ⟶ s.pt => h.obj (vertex A o)) s.condition
  change s.inl.obj (f.val.obj (vertex A o)) = s.inr.obj (g.val.obj (vertex A o)) at ho
  exact (congrArg s.inr.obj (map_vertex g o)).symm.trans
    (ho.symm.trans (congrArg s.inl.obj (map_vertex f o)))

/-- Reindex the SAME full original left cocone map through its actual common object function. -/
def left : B ⟶ CarrierReindexing.object s.pt (labels s) :=
  CarrierLabelReadback.map B (labels s) s.inl (fun _o => rfl)

/-- Reindex the SAME full original right cocone map through that same actual object function. -/
def right : C ⟶ CarrierReindexing.object s.pt (labels s) :=
  CarrierLabelReadback.map C (labels s) s.inr (right_labels s)

/-- The SAME whole original left carrier map is recovered literally through its canonical
projection. -/
theorem left_fac : (left s).val ≫ CarrierReindexing.toTarget s.pt (labels s) = s.inl :=
  CarrierLabelReadback.map_fac B (labels s) s.inl (fun _o => rfl)

/-- The SAME whole original right carrier map is recovered literally through that same
projection. -/
theorem right_fac : (right s).val ≫ CarrierReindexing.toTarget s.pt (labels s) = s.inr :=
  CarrierLabelReadback.map_fac C (labels s) s.inr (right_labels s)

/-- The original full carrier cocone condition gives the SAME original fixed-object cocone
square. -/
theorem fixed_condition : f ≫ left s = g ≫ right s := by
  apply CarrierLabelMaps.projection_injective (labels s)
  change (f.val ≫ (left s).val) ≫ CarrierReindexing.toTarget s.pt (labels s) =
    (g.val ≫ (right s).val) ≫ CarrierReindexing.toTarget s.pt (labels s)
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun h => f.val ≫ h) (left_fac s)).trans
      (s.condition.trans ((congrArg (fun h => g.val ≫ h) (right_fac s).symm).trans
        (Category.assoc _ _ _).symm)))

/-- The genuine supplied fixed-object pushout evaluates this SAME complete original cocone. -/
def fixedDesc : P ⟶ CarrierReindexing.object s.pt (labels s) :=
  sq.desc (left s) (right s) (fixed_condition s)

/-- The SAME whole original carrier descender, retaining all original object and full Hom maps. -/
def desc : P.val ⟶ s.pt := (fixedDesc sq s).val ≫ CarrierReindexing.toTarget s.pt (labels s)

/-- The actual whole original left carrier cocone leg factors through this SAME descender. -/
theorem desc_left : j.val ≫ desc sq s = s.inl := by
  have h : j.val ≫ (fixedDesc sq s).val = (left s).val :=
    congrArg (fun h : B ⟶ CarrierReindexing.object s.pt (labels s) => h.val)
      (sq.inl_desc (left s) (right s) (fixed_condition s))
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun h => h ≫ CarrierReindexing.toTarget s.pt (labels s)) h).trans (left_fac s))

/-- The actual whole original right carrier cocone leg factors through this SAME descender. -/
theorem desc_right : k.val ≫ desc sq s = s.inr := by
  have h : k.val ≫ (fixedDesc sq s).val = (right s).val :=
    congrArg (fun h : C ⟶ CarrierReindexing.object s.pt (labels s) => h.val)
      (sq.inr_desc (left s) (right s) (fixed_condition s))
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun h => h ≫ CarrierReindexing.toTarget s.pt (labels s)) h).trans (right_fac s))

/-- Any actual whole carrier cocone extension has the SAME original common label function. -/
theorem desc_labels (H : P.val ⟶ s.pt) (hH : j.val ≫ H = s.inl) (o : O) :
    H.obj (vertex P o) = labels s o := by
  have ho := congrArg (fun h : B.val ⟶ s.pt => h.obj (vertex B o)) hH
  change H.obj (j.val.obj (vertex B o)) = s.inl.obj (vertex B o) at ho
  exact (congrArg H.obj (map_vertex j o)).symm.trans ho

/-- Every whole carrier extension is determined on the SAME original full Hom maps and
object labels. -/
theorem desc_unique (H : P.val ⟶ s.pt) (hF : j.val ≫ H = s.inl) (hG : k.val ≫ H = s.inr) :
    H = desc sq s := by
  let Q : P ⟶ CarrierReindexing.object s.pt (labels s) :=
    CarrierLabelReadback.map P (labels s) H (desc_labels s H hF)
  have hQ : Q.val ≫ CarrierReindexing.toTarget s.pt (labels s) = H :=
    CarrierLabelReadback.map_fac P (labels s) H (desc_labels s H hF)
  have hQF : j ≫ Q = left s := by
    apply CarrierLabelMaps.projection_injective (labels s)
    change (j.val ≫ Q.val) ≫ CarrierReindexing.toTarget s.pt (labels s) =
      (left s).val ≫ CarrierReindexing.toTarget s.pt (labels s)
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun h => j.val ≫ h) hQ).trans (hF.trans (left_fac s).symm))
  have hQG : k ≫ Q = right s := by
    apply CarrierLabelMaps.projection_injective (labels s)
    change (k.val ≫ Q.val) ≫ CarrierReindexing.toTarget s.pt (labels s) =
      (right s).val ≫ CarrierReindexing.toTarget s.pt (labels s)
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun h => k.val ≫ h) hQ).trans (hG.trans (right_fac s).symm))
  have he : Q = fixedDesc sq s :=
    sq.hom_ext (hQF.trans (sq.inl_desc (left s) (right s) (fixed_condition s)).symm)
      (hQG.trans (sq.inr_desc (left s) (right s) (fixed_condition s)).symm)
  exact hQ.symm.trans (congrArg (fun h : P ⟶ CarrierReindexing.object s.pt (labels s) =>
    h.val ≫ CarrierReindexing.toTarget s.pt (labels s)) he)

/-- The SAME supplied fixed-object pushout cocone has the full genuine original carrier
universal property. -/
def isColimit : IsColimit (cocone sq) :=
  PushoutCocone.IsColimit.mk (condition sq) (desc sq) (desc_left sq) (desc_right sq)
    (desc_unique sq)

include sq in
/-- The SAME entire fixed-object square is a genuine varying-object carrier pushout. -/
theorem isPushout : IsPushout f.val g.val j.val k.val := IsPushout.of_isColimit (isColimit sq)

end CategoryTheory.SimplicialEnrichment.FixedObjects.GlobalPushout
