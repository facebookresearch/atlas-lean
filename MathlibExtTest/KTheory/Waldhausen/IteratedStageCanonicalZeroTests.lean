/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.IteratedStageCanonicalZero

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
namespace MathlibExtTest.IteratedStageCanonicalZero
open CategoryTheory.Waldhausen.SConstruction
variable (C : Type (max u v)) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- The complete original constant diagram is zero after every actual finite iteration. -/
theorem originalConstructedZero (ns : List ℕ) : IsZero (iteratedStageCanonicalZero C ns) :=
  iteratedStageCanonicalZero_isZero C ns

/-- The complete successor diagram is literally constant at the previously constructed original
zero. -/
theorem originalSuccessorDiagram (n : ℕ) (ns : List ℕ) :
    ((iteratedStageConsEquivalence C n ns).functor.obj
      (iteratedStageCanonicalZero C (n :: ns))).obj =
      (Functor.const (Ar n)).obj (iteratedStageCanonicalZero C ns) :=
  iteratedStageCanonicalZero_cons_obj C n ns

/-- Actual equal-list transport keeps the same constructed zero object. -/
theorem originalListTransport {ns ms : List ℕ} (h : ns = ms) :
    (iteratedStageListEquivalence C h).functor.obj (iteratedStageCanonicalZero C ns) =
      iteratedStageCanonicalZero C ms :=
  iteratedStageCanonicalZero_list_transport C h

/-- Every tuple successor retains the whole constant diagram in its original carrier. -/
theorem originalTupleSuccessor {r : ℕ} (d : Fin (r + 1) → ℕ) :
    ((iteratedStageOfFnSuccEquivalence C d).functor.obj
      (iteratedStageCanonicalZero C (List.ofFn d))).obj =
      (Functor.const (Ar (d 0))).obj
        (iteratedStageCanonicalZero C (List.ofFn (fun i => d i.succ))) :=
  iteratedStageCanonicalZero_tuple_successor C d

end MathlibExtTest.IteratedStageCanonicalZero
