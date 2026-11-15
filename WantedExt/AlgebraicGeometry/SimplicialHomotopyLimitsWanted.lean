/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.SimplicialHomotopyLimits

/-!
# Wanted Quillen space-model choices

The outputs have actual diagonal/endpoint and diagram maps with the
standard lifting conditions. The native pullbacks, limits and their
comparisons are already computed in the public module. No geometric,
closed-form, enhanced-category or descent theorem is an input.

References: Bousfield--Kan, Chapters X--XI; the native pre-path and
Kan-fibration interfaces imported by the public module.
-/

open CategoryTheory
open MathlibExt.AlgebraicGeometry.SimplicialHomotopyLimits

universe u

/-- Choose a path model of the actual Kan space. -/
def_wanted simplicial_kan_path_model (Y : SSet.{u}) [SSet.KanComplex Y] : KanPathModel Y

/-- Choose the actual injectively fibrant replacement of a small space diagram. -/
def_wanted simplicial_fibrant_diagram_replacement (J : Type u) [Category.{u} J]
    (D : J ⥤ SSet.{u}) : FibrantDiagramReplacement D
