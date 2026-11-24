/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicTopology.QuasicategoricalModels
public import MathlibExt.AlgebraicTopology.NativeQuasicategoryFunctors

/-!
# Wanted generic categorical model choices

These are shared quasicategory/core/model constructions. They concern
the actual edge-defined core, native simplicial Hom and categorical
injective replacement. Perf and arc descent are subsequent theorems
and are not assumed by these requests.
The native simplicial-functor quasicategory law is already proved in
NativeQuasicategoryFunctors.mapping_quasicategory.

Reference: Lurie, Higher Topos Theory, §§1.2.5 and 2.2.5.
-/

namespace WantedExt.AlgebraicGeometry.QuasicategoricalModelsWanted

open CategoryTheory
open MathlibExt.AlgebraicTopology.QuasicategoricalModels

universe u v w

/-- The actual equivalence-edge core of a quasicategory is a Kan complex. -/
theorem_wanted quasicategory_core_kan (X : SSet) [SSet.Quasicategory X] :
  SSet.KanComplex (core X)

/-- Choose the categorical injective replacement of an actual diagram. -/
def_wanted categorical_fibrant_diagram_replacement (J : Type v) [Category.{w} J]
    (D : J ⥤ SSet.{max u v w}) : CategoricalDiagramReplacement.{u, v, w} D

/-- The native limit of the categorical replacement is a quasicategory. -/
theorem_wanted categorical_homotopy_limit_quasicategory (J : Type v) [Category.{w} J]
    (D : J ⥤ SSet.{max u v w}) (R : CategoricalDiagramReplacement.{u, v, w} D) :
  SSet.Quasicategory (homotopyLimit.{u, v, w} R)

end WantedExt.AlgebraicGeometry.QuasicategoricalModelsWanted
