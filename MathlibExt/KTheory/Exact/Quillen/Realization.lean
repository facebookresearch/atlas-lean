/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Quillen.Nerve
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import MathlibExt.Topology.Category.PointedTopCat

/-!
# Geometric realization of the Quillen Q-nerve, with distinguished point

For an exact category `C`, `NQReal C` is `SSet.toTop.obj (NQ C)` in
`TopCat.{max u v}`. Exact functors act by `SSet.toTop.map (NQ.map F)`.
The zero vertex gives `NQ.zeroVertexInclusion C : Δ[0] ⟶ NQ C` via
`SSet.const`, realized as `NQReal.basepoint C` by applying the realized
map to the unique `default : |Δ[0]|`. The bundled pointed object
`NQReal.toPointed C : PointedTopCat` is `Under.mk (NQReal.basepointMap C)`.

The realization maps are induced by the nerve maps. The distinguished point
is the realization of the chosen zero vertex.
-/

@[expose] public section

open CategoryTheory Limits Opposite Simplicial ZeroObject
open CategoryTheory.ExactCategory

universe v u

namespace AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type u} [Category.{v} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable {E : Type u} [Category.{v} E] [Preadditive E]
  [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]

/-- Unpointed geometric realization of `NQ C`. -/
noncomputable abbrev NQReal (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] :=
  SSet.toTop.obj (NQ C)

/-- Induced map of realizations, via `SSet.toTop.map (NQ.map F)`. -/
noncomputable def NQReal.map (F : C ⥤ D) [F.Additive] [F.IsExact] :
    NQReal C ⟶ NQReal D :=
  SSet.toTop.map (NQ.map F)

@[simp]
theorem NQReal.map_id : NQReal.map (𝟭 C) = 𝟙 (NQReal C) := by
  unfold NQReal.map NQReal
  rw [NQ.map_id]
  exact SSet.toTop.map_id _

@[simp]
theorem NQReal.map_comp (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] :
    NQReal.map F ≫ NQReal.map G = NQReal.map (F ⋙ G) := by
  unfold NQReal.map
  rw [← Functor.map_comp, NQ.map_comp]

/-- Zero-vertex inclusion `Δ[0] ⟶ NQ C`, via `SSet.const`. -/
noncomputable def NQ.zeroVertexInclusion (C : Type u) [Category.{v} C]
    [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
    [ExactCategory C] :
    (Δ[0] : SSet.{max u v}) ⟶ NQ C :=
  SSet.const (NQ.zeroVertex C)

/-- Realized basepoint, from the zero-vertex inclusion. -/
noncomputable def NQReal.basepoint (C : Type u) [Category.{v} C]
    [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
    [ExactCategory C] :
    NQReal C :=
  SSet.toTop.map (NQ.zeroVertexInclusion C) default

/-- Constant map from the point into the realization, at the basepoint. -/
noncomputable def NQReal.basepointMap (C : Type u) [Category.{v} C]
    [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
    [ExactCategory C] :
    TopCat.of PUnit ⟶ NQReal C :=
  TopCat.ofHom (ContinuousMap.const _ (NQReal.basepoint C))

/-- Bundled pointed realization, via `Under.mk`. -/
noncomputable def NQReal.toPointed (C : Type u) [Category.{v} C]
    [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
    [ExactCategory C] :
    PointedTopCat.{max u v} :=
  Under.mk (NQReal.basepointMap C)

@[simp]
theorem NQReal.toPointed_right (C : Type u) [Category.{v} C]
    [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
    [ExactCategory C] :
    (NQReal.toPointed C).right = NQReal C :=
  rfl

@[simp]
theorem NQReal.toPointed_hom_apply (C : Type u) [Category.{v} C]
    [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
    [ExactCategory C] :
    (NQReal.toPointed C).hom PUnit.unit = NQReal.basepoint C :=
  rfl

end AlgebraicKTheory
