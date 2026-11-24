/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.IteratedStage

/-!
# The constructed constant-zero object in every original iterated stage

Every recursive zero diagram is constant at the previously constructed
zero object, starting from the original chosen base zero C. The existing
pointwise-zero stage theorem supplies membership. Original carrier
transport and its exactness retain the same constructed object.

This object is distinct from an existentially chosen stage zero; their
canonical zero isomorphism is retained explicitly. It supplies the
original constant diagrams needed for coherent interval collapse.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type (max u v)) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

private structure CanonicalZeroData (ns : List ℕ) where
  obj : IteratedStage C ns
  isZero : IsZero obj

private def canonicalZeroData : (ns : List ℕ) → CanonicalZeroData C ns
  | [] =>
      ⟨(0 : IteratedStage C []), isZero_zero (IteratedStage C [])⟩
  | n :: ns => by
      let Z := canonicalZeroData ns
      let D := IteratedStage C ns
      letI : HasZeroObject (Stage D n) := generalStageHasZeroObject D n
      letI : WaldhausenCategoryWithoutGluing (Stage D n) := generalStageWaldhausenCategory D n
      let Q : Stage D n :=
        ⟨(Functor.const (Ar n)).obj Z.obj,
          isStage_of_pointwise_zero D _ (fun _ => Z.isZero)⟩
      have hQ : IsZero Q := by
        apply IsZero.of_full_of_faithful_of_isZero (forget D n)
        exact Functor.isZero _ (fun _ => Z.isZero)
      exact ⟨(iteratedStageConsEquivalence C n ns).inverse.obj Q,
        (iteratedStageConsEquivalence_exact C n ns).2.map_isZero hQ⟩

/-- The actual recursively constructed zero diagram, constant at the original base zero in every
direction. -/
@[no_expose]
def iteratedStageCanonicalZero (ns : List ℕ) : IteratedStage C ns :=
  (canonicalZeroData C ns).obj

/-- The constructed original constant diagram is zero in the original iterated category. -/
theorem iteratedStageCanonicalZero_isZero (ns : List ℕ) :
    IsZero (iteratedStageCanonicalZero C ns) := (canonicalZeroData C ns).isZero

/-- The constructed base zero is the actual original zero object after its canonical nil transport.
-/
theorem iteratedStageCanonicalZero_nil :
    (iteratedStageNilEquivalence C).functor.obj (iteratedStageCanonicalZero C []) = (0 : C) := by
  change (iteratedStageNilEquivalence C).functor.obj (0 : IteratedStage C []) = (0 : C)
  exact iteratedStageNilEquivalence_obj_zero C

/-- At zero iterations the constructed zero is the original base zero
in the same literal original carrier. -/
theorem iteratedStageCanonicalZero_nil_obj :
    iteratedStageCanonicalZero C [] = (0 : IteratedStage C []) := by
  rfl

/-- The actual constructed zero and the existing chosen zero have their canonical original zero
isomorphism. -/
def iteratedStageCanonicalZeroIsoChosen (ns : List ℕ) :
    iteratedStageCanonicalZero C ns ≅ (0 : IteratedStage C ns) :=
  (iteratedStageCanonicalZero_isZero C ns).isoZero

set_option backward.isDefEq.respectTransparency false in
/-- The successor constructed zero retains the complete original constant diagram in the outer
direction. -/
theorem iteratedStageCanonicalZero_cons_obj (n : ℕ) (ns : List ℕ) :
    ((iteratedStageConsEquivalence C n ns).functor.obj
      (iteratedStageCanonicalZero C (n :: ns))).obj =
      (Functor.const (Ar n)).obj (iteratedStageCanonicalZero C ns) := by
  let Q : Stage (IteratedStage C ns) n :=
    ⟨(Functor.const (Ar n)).obj (iteratedStageCanonicalZero C ns),
      isStage_of_pointwise_zero _ _ (fun _ => iteratedStageCanonicalZero_isZero C ns)⟩
  change ((iteratedStageConsEquivalence C n ns).functor.obj
    ((iteratedStageConsEquivalence C n ns).inverse.obj Q)).obj = _
  exact congrArg ObjectProperty.FullSubcategory.obj
    (Functor.congr_obj (iteratedStageConsEquivalence_inverse_functor C n ns) Q)

/-- Equality of original degree lists transports the same actual constructed constant-zero object.
-/
theorem iteratedStageCanonicalZero_list_transport {ns ms : List ℕ} (h : ns = ms) :
    (iteratedStageListEquivalence C h).functor.obj (iteratedStageCanonicalZero C ns) =
      iteratedStageCanonicalZero C ms := by
  subst ms
  rfl

/-- The actual tuple successor carrier retains the complete original canonical zero diagram. -/
theorem iteratedStageCanonicalZero_tuple_successor {r : ℕ} (d : Fin (r + 1) → ℕ) :
    ((iteratedStageOfFnSuccEquivalence C d).functor.obj
      (iteratedStageCanonicalZero C (List.ofFn d))).obj =
      (Functor.const (Ar (d 0))).obj
        (iteratedStageCanonicalZero C (List.ofFn (fun i => d i.succ))) := by
  unfold iteratedStageOfFnSuccEquivalence
  change ((iteratedStageConsEquivalence C (d 0) (List.ofFn (fun i => d i.succ))).functor.obj
    ((iteratedStageListEquivalence C (List.ofFn_succ (f := d))).functor.obj
      (iteratedStageCanonicalZero C (List.ofFn d)))).obj = _
  rw [iteratedStageCanonicalZero_list_transport]
  exact iteratedStageCanonicalZero_cons_obj C _ _

end CategoryTheory.Waldhausen.SConstruction
