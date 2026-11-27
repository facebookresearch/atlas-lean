/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.Stage
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.Zero

/-!
# Degree-zero Waldhausen stage has a canonical terminal object

Categorical only: `stageZero C` is terminal in `Stage C 0`, with exactly one
morphism from any stage into the constant zero diagram. This does not claim
realization or topological contractibility, and adds no `S₁`, simplicial object,
nerve, realization, G-theory, or K-group content.
-/

@[expose] public section

open CategoryTheory Limits ZeroObject

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [Limits.HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Canonical zero stage in degree zero. -/
noncomputable def stageZero : Stage C 0 :=
  ⟨zeroDiagram C 0, isStage_zeroDiagram C 0⟩

/-- `stageZero C` is terminal in `Stage C 0`: every stage admits exactly one
morphism into the constant zero diagram, pointwise. Categorical only, not a
realization or topological contractibility claim. -/
noncomputable def stageZero_isTerminal : Limits.IsTerminal (stageZero C) :=
  Limits.IsTerminal.ofUniqueHom
    (fun A =>
      ObjectProperty.homMk
        ((Functor.isTerminalConst (Ar 0) (isZero_zero C).isTerminal).from A.obj))
    (by
      intro A m
      apply ObjectProperty.hom_ext
      exact (Functor.isTerminalConst (Ar 0) (isZero_zero C).isTerminal).hom_ext _ _)

end CategoryTheory.Waldhausen.SConstruction
