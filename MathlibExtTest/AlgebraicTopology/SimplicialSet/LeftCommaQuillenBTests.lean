/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

/-
Tests for the variance-symmetric categorical Quillen-B completion: the
realization-reversal iso and its naturality, weak-equivalence transfer,
and vertex fixity, plus the left-comma/opposite-reversal package (base
square, transition comparison, fiber transport, comparison, and main
weak-equivalence theorem).

This tests only the stated interface contract and makes no BK-total,
homotopy-invariance, pullback, or model-structure claim.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.ToTopReversal
import MathlibExt.AlgebraicTopology.SimplicialSet.LeftCommaQuillenB

namespace SSet

namespace LeftCommaQuillenBTests

open CategoryTheory Opposite Simplicial

universe u

variable {C D : Type u} [Category.{0} C] [Category.{0} D]

section Reversal

variable {X Y : SSet.{u}}

noncomputable example (X : SSet.{u}) :
    toTop.obj (SimplicialObject.opFunctor.obj X) ≅ toTop.obj X :=
  toTopReversalIso X

noncomputable example (f : X ⟶ Y) :
    toTop.map (SimplicialObject.opFunctor.map f) ≫ (toTopReversalIso Y).hom =
      (toTopReversalIso X).hom ≫ toTop.map f :=
  toTopReversalIso_naturality f

noncomputable example (f : X ⟶ Y)
    (h : TopCat.weakHomotopyEquivalences (toTop.map f)) :
    TopCat.weakHomotopyEquivalences
      (toTop.map (SimplicialObject.opFunctor.map f)) :=
  toTopReversal_mem_weakHomotopyEquivalences f h

noncomputable example (f : X ⟶ Y) :
    TopCat.weakHomotopyEquivalences
        (toTop.map (SimplicialObject.opFunctor.map f)) ↔
      TopCat.weakHomotopyEquivalences (toTop.map f) :=
  toTopReversal_mem_weakHomotopyEquivalences_iff f

noncomputable example (x : X _⦋0⦌) :
    (toTopReversalIso X).hom (realizedVertex (opVertex x)) =
      realizedVertex x :=
  toTopReversalIso_realizedVertex X x

noncomputable example (x : X _⦋0⦌) :
    (SimplicialObject.opFunctor.obj X) _⦋0⦌ :=
  opVertex x

end Reversal

section LeftComma

variable (F : C ⥤ D)

noncomputable example (d : Dᵒᵖ) :
    toTop.obj (nerve (StructuredArrow d.unop F)) ≅
      toTop.obj (nerve (CostructuredArrow F.op d)) :=
  leftCommaRealizationIso F d

noncomputable example :
    toTop.obj (nerve Dᵒᵖ) ≅ toTop.obj (nerve D) :=
  nerveRealizationOppositeIso D

noncomputable example :
    toTop.map (nerveMap F.op) ≫ (nerveRealizationOppositeIso D).hom =
      (nerveRealizationOppositeIso C).hom ≫ toTop.map (nerveMap F) :=
  leftCommaBaseSquare_comm F

noncomputable example (d : D) :
    (nerveRealizationOppositeIso D).hom
        (realizedVertex (ComposableArrows.mk₀ (op d) :
          (nerve Dᵒᵖ : SSet.{u}) _⦋0⦌)) =
      realizedVertex (ComposableArrows.mk₀ d :
        (nerve D : SSet.{u}) _⦋0⦌) :=
  leftCommaBaseVertex_eq d

noncomputable example {d d' : Dᵒᵖ} (g : d ⟶ d') :
    TopCat.weakHomotopyEquivalences
        (toTop.map (nerveMap (StructuredArrow.map (S := d'.unop)
          (S' := d.unop) (T := F) g.unop))) ↔
      TopCat.weakHomotopyEquivalences
        (toTop.map (nerveMap (CostructuredArrow.map (S := F.op) g))) :=
  leftCommaTransition_mem_weakHomotopyEquivalences_iff F g

noncomputable example (d : D) :
    TopCat.homotopyFiber (toTop.map (nerveMap F.op))
        (realizedVertex (ComposableArrows.mk₀ (op d) :
          (nerve Dᵒᵖ : SSet.{u}) _⦋0⦌)) ⟶
      TopCat.homotopyFiber (toTop.map (nerveMap F))
        (realizedVertex (ComposableArrows.mk₀ d :
          (nerve D : SSet.{u}) _⦋0⦌)) :=
  leftCommaFiberTransport F d

noncomputable example (d : D) :
    TopCat.weakHomotopyEquivalences (leftCommaFiberTransport F d) :=
  leftCommaFiberTransport_mem_weakHomotopyEquivalences F d

noncomputable example (d : D) :
    toTop.obj (nerve (StructuredArrow d F)) ⟶
      TopCat.homotopyFiber (toTop.map (nerveMap F))
        (realizedVertex (ComposableArrows.mk₀ d :
          (nerve D : SSet.{u}) _⦋0⦌)) :=
  leftCommaHomotopyFiberComparison F d

noncomputable example
    (hF : ∀ (d d' : D) (g : d ⟶ d'),
      TopCat.weakHomotopyEquivalences
        (toTop.map (nerveMap (StructuredArrow.map (S := d) (S' := d')
          (T := F) g))))
    (d : D) :
    TopCat.weakHomotopyEquivalences (leftCommaHomotopyFiberComparison F d) :=
  leftCommaHomotopyFiberComparison_mem_weakHomotopyEquivalences F hF d

end LeftComma

end LeftCommaQuillenBTests

end SSet
