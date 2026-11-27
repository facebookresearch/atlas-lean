/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.Fiber
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

/-!
# Fibrancy of strict simplicial fibres

The generic strict-fibre API is reexported from its lightweight owner.
This module proves the original fibration and fibrancy consequences.
-/

@[expose] public section
universe u
open CategoryTheory Simplicial SSet Limits HomotopicalAlgebra Opposite
open SSet.modelCategoryQuillen

namespace SSet.Subcomplex

private instance isFibrant_ofSimplex {X : SSet.{u}} (y : X _⦋0⦌) :
    IsFibrant (Subcomplex.ofSimplex y : SSet.{u}) := by
  rw [isFibrant_iff (X := (Subcomplex.ofSimplex y : SSet.{u}))]
  have hIso : IsIso (terminal.from (Subcomplex.ofSimplex y : SSet.{u})) :=
    isIso_of_isTerminal (isTerminalOfSimplex (X := X) y) terminalIsTerminal _
  infer_instance

/-- Pullback of a Kan fibration is a Kan fibration, derived directly
from `preimage_isPullback`. -/
private instance fibration_fromPreimage {X Y : SSet.{u}} (f : X ⟶ Y) (B : Y.Subcomplex)
    [Fibration f] : Fibration (B.fromPreimage f) := by
  have hpb : IsPullback (B.preimage f).ι (B.fromPreimage f) f B.ι :=
    preimage_isPullback B f
  have hf : J.rlp f := by
    have : fibrations SSet.{u} f := Fibration.mem (f := f)
    rwa [fibrations_eq] at this
  have hg : J.rlp (B.fromPreimage f) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := J.rlp) hpb hf
  have : fibrations SSet.{u} (B.fromPreimage f) := by
    rwa [← fibrations_eq] at hg
  exact ⟨this⟩

/-- The fiber of a Kan fibration is fibrant. -/
instance isFibrant_fiber {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌) [Fibration f] :
    IsFibrant (fiber f y : SSet.{u}) := by
  rw [isFibrant_iff]
  have h1 : Fibration ((Subcomplex.ofSimplex y).fromPreimage f) :=
    fibration_fromPreimage (X := X) (Y := Y) f (Subcomplex.ofSimplex y)
  have h2 : Fibration (terminal.from (Subcomplex.ofSimplex y : SSet.{u})) :=
    (isFibrant_iff (X := (Subcomplex.ofSimplex y : SSet.{u}))).mp (isFibrant_ofSimplex (X := Y) y)
  have h3 :
      Fibration
        (((Subcomplex.ofSimplex y).fromPreimage f) ≫
          terminal.from (Subcomplex.ofSimplex y : SSet.{u})) := by
    infer_instance
  have hEq :
      ((Subcomplex.ofSimplex y).fromPreimage f) ≫
          terminal.from (Subcomplex.ofSimplex y : SSet.{u}) =
        terminal.from (fiber f y : SSet.{u}) := by
    apply IsTerminal.hom_ext terminalIsTerminal
  rw [hEq] at h3
  exact h3

end SSet.Subcomplex
