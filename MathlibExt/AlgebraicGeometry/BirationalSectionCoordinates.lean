/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LogPairs
public import MathlibExt.AlgebraicGeometry.LineBundleTaskContracts
public import MathlibExt.AlgebraicGeometry.GenericSectionMaps

/-!
# Actual birational section coordinates

The global section, its local line trivialization, the germ and the map to the
actual function field are fixed native operations. A linear-evaluation adapter
is characterized on every section by that composition, so it is not a section
value oracle. The formulas generalize the completed complex-Fano section
coordinates; all base fields and line modules are allowed.

Sources: Mathlib/AlgebraicGeometry/Modules/Sheaf and OrderOfVanishing at
56a005855ea17e0b0958f73ec801ae140b0a1679 (Apache 2.0);
Atlas FanoVanishingFiltrations (same Meta license), generalized to normal
varieties and arbitrary fields. This does not supply Cartier/model producers.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.BirationalSectionCoordinates

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.LogPairs
open MathlibExt.AlgebraicGeometry.LineBundleTaskContracts

variable {k : Type} [Field k] {n : ℕ}

abbrev SectionSpace (V : NormalVariety k n) (M : V.X.left.Modules) :=
  (sectionsFunctor V.X.hom).obj M

/-- The actual module morphism represented by a global section: the shared
`GenericSectionMaps.topSectionHom`. -/
abbrev sectionHom (V : NormalVariety k n) (M : V.X.left.Modules) (s : SectionSpace V M) :
    structureModule V.X.left ⟶ M :=
  GenericSectionMaps.topSectionHom V.X.left M s

/-- An actual local frame, not a chosen numerical evaluator. -/
structure LocalFrame (V : NormalVariety k n) (x : V.X.left) (M : V.X.left.Modules) where
  openSet : V.X.left.Opens
  contains : x ∈ openSet
  trivialization : (Scheme.Modules.pullback openSet.ι).obj M ≅
    structureModule openSet.toScheme

/-- Value in the actual local ring through the native section pullback and germ. -/
def localValue {V : NormalVariety k n} {x : V.X.left} {M : V.X.left.Modules}
    (F : LocalFrame V x M) (s : SectionSpace V M) : LocalRing V x :=
  let pulled := LineBundleTaskContracts.pullbackSection F.openSet.ι (sectionHom V M s)
  let q := pulled ≫ F.trivialization.hom
  let value : Γ(F.openSet.toScheme, ⊤) := (q.val.app (op ⊤)).hom (1 : Γ(F.openSet.toScheme, ⊤))
  (V.X.left.presheaf.germ F.openSet x F.contains).hom (F.openSet.topIso.hom value)

/-- The actual rational-function value of the displayed local section. -/
def fieldValue {V : NormalVariety k n} {x : V.X.left} {M : V.X.left.Modules}
    (F : LocalFrame V x M) (s : SectionSpace V M) : FunctionField V :=
  localToField V x (localValue F s)

/-- Proof-only linearity/faithfulness adapter for the fixed section/germ formula.
No value function is freely supplied: every value is required to be fieldValue. -/
structure Evaluation (V : NormalVariety k n) (x : V.X.left) (M : V.X.left.Modules) where
  frame : LocalFrame V x M
  map :
    letI := fractionAlgebra V
    SectionSpace V M →ₗ[k] FunctionField V
  normalized : ∀ s, map s = fieldValue frame s
  injective : Function.Injective map

end MathlibExt.AlgebraicGeometry.BirationalSectionCoordinates
