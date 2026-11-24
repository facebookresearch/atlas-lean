/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalNecklaceComplex

/-!
# Actual native necklace morphisms and their simplicial functor

An original morphism retains its endpoint-preserving ordinal map and the
actual full native bead containment. The same map gives a simplicial
necklace map in every coefficient universe, with its original inclusion
and vertex equations.
-/

@[expose] public section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.OriginalNecklace

/-- An actual original necklace map, with its entire native bead containment. -/
structure Morphism (T U : Data) where
  /-- The same original ordinal vertex operator. -/
  operator : ⦋T.dimension⦌ ⟶ ⦋U.dimension⦌
  /-- The original source vertex is retained. -/
  source : operator.toOrderHom 0 = 0
  /-- The original terminal vertex is retained. -/
  target : operator.toOrderHom (Fin.last T.dimension) = Fin.last U.dimension
  /-- Every complete original source bead maps into the original target necklace. -/
  lands : complex.{0} T.joints ≤
    (complex.{0} U.joints).preimage (SSet.stdSimplex.map operator)

namespace Morphism

/-- Original necklace morphisms are determined by their same original vertex operator. -/
@[ext]
theorem ext {T U : Data} {f g : Morphism T U} (h : f.operator = g.operator) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- The whole native original bead containment is independent of the coefficient universe. -/
theorem lands_universe {T U : Data} (f : Morphism T U)
    {d : ℕ} (s : (Δ[T.dimension] : SSet.{u}) _⦋d⦌)
    (hs : s ∈ (complex T.joints).obj (op ⦋d⦌)) :
    (SSet.stdSimplex.map f.operator).app (op ⦋d⦌) s ∈
      (complex U.joints).obj (op ⦋d⦌) := by
  let s₀ : (Δ[T.dimension] : SSet.{0}) _⦋d⦌ :=
    stdSimplex.objEquiv.{0}.symm (stdSimplex.objEquiv s)
  have hs₀ : s₀ ∈ (complex T.joints).obj (op ⦋d⦌) :=
    (mem_complex_iff T.joints s₀).mpr ((mem_complex_iff T.joints s).mp hs)
  have h := f.lands (op ⦋d⦌) hs₀
  exact (mem_complex_iff _ _).mpr
    ((mem_complex_iff U.joints ((SSet.stdSimplex.{0}.map f.operator).app (op ⦋d⦌) s₀)).mp h)

/-- The literal original full simplicial map in the selected coefficient universe. -/
def map {T U : Data} (f : Morphism T U) : T.object.{u} ⟶ U.object.{u} :=
  Subcomplex.lift ((complex T.joints).ι ≫ SSet.stdSimplex.map f.operator) (by
    intro q s hs
    obtain ⟨a, rfl⟩ := hs
    exact f.lands_universe a.val a.property)

/-- The complete original map retains its literal native standard-simplex equation. -/
@[reassoc]
theorem map_ι {T U : Data} (f : Morphism T U) :
    f.map.{u} ≫ (complex U.joints).ι =
      (complex T.joints).ι ≫ SSet.stdSimplex.map f.operator := rfl

/-- The actual original identity morphism. -/
def id (T : Data) : Morphism T T where
  operator := 𝟙 ⦋T.dimension⦌
  source := rfl
  target := rfl
  lands := by
    intro q s hs
    simpa using hs

/-- Composition keeps the same two original ordinal operators and full bead maps. -/
def comp {T U V : Data} (f : Morphism T U) (g : Morphism U V) : Morphism T V where
  operator := f.operator ≫ g.operator
  source := (congrArg g.operator.toOrderHom f.source).trans g.source
  target := (congrArg g.operator.toOrderHom f.target).trans g.target
  lands := by
    intro q s hs
    have h := g.lands q (f.lands q hs)
    change (SSet.stdSimplex.map (f.operator ≫ g.operator)).app q s ∈
      (complex V.joints).obj q
    rw [Functor.map_comp]
    exact h

/-- The original identity retains the entire native simplicial necklace. -/
theorem map_id (T : Data) : (id T).map.{u} = 𝟙 T.object := by
  apply (cancel_mono (complex.{u} T.joints).ι).mp
  rw [map_ι]
  change (complex.{u} T.joints).ι ≫ SSet.stdSimplex.map (𝟙 ⦋T.dimension⦌) =
    𝟙 T.object ≫ (complex T.joints).ι
  rw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]

/-- The entire original simplicial map follows genuine necklace composition. -/
theorem map_comp {T U V : Data} (f : Morphism T U) (g : Morphism U V) :
    (comp f g).map.{u} = f.map ≫ g.map := by
  apply (cancel_mono (complex.{u} V.joints).ι).mp
  calc
    (comp f g).map ≫ (complex V.joints).ι =
        (complex T.joints).ι ≫ SSet.stdSimplex.map (f.operator ≫ g.operator) := map_ι _
    _ = ((complex T.joints).ι ≫ SSet.stdSimplex.map f.operator) ≫
        SSet.stdSimplex.map g.operator := by
      rw [Functor.map_comp, Category.assoc]
    _ = (f.map ≫ g.map) ≫ (complex V.joints).ι := by
      symm
      calc
        (f.map ≫ g.map) ≫ (complex V.joints).ι =
            f.map ≫ (g.map ≫ (complex V.joints).ι) := Category.assoc _ _ _
        _ = f.map ≫ ((complex U.joints).ι ≫ SSet.stdSimplex.map g.operator) :=
          congrArg (fun h => f.map ≫ h) (map_ι g)
        _ = (f.map ≫ (complex U.joints).ι) ≫ SSet.stdSimplex.map g.operator :=
          (Category.assoc _ _ _).symm
        _ = ((complex T.joints).ι ≫ SSet.stdSimplex.map f.operator) ≫
            SSet.stdSimplex.map g.operator :=
          congrArg (fun h => h ≫ SSet.stdSimplex.map g.operator) (map_ι f)

/-- Every original ordinal vertex map follows the same whole necklace map. -/
theorem vertex_map {T U : Data} (f : Morphism T U) (i : Fin (T.dimension + 1)) :
    vertexMap.{u} T.joints i ≫ f.map =
      vertexMap U.joints (f.operator.toOrderHom i) := by
  apply (cancel_mono (complex.{u} U.joints).ι).mp
  calc
    (vertexMap T.joints i ≫ f.map) ≫ (complex U.joints).ι =
        SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋T.dimension⦌ i) ≫
          SSet.stdSimplex.map f.operator := by
      rw [Category.assoc, map_ι, ← Category.assoc, vertexMap_ι]
    _ = vertexMap U.joints (f.operator.toOrderHom i) ≫ (complex U.joints).ι := by
      rw [vertexMap_ι, ← Functor.map_comp]
      rfl

end Morphism

/-- The genuine category of native original necklaces. -/
instance : Category Data where
  Hom := Morphism
  id := Morphism.id
  comp := Morphism.comp
  id_comp f := Morphism.ext (Category.id_comp f.operator)
  comp_id f := Morphism.ext (Category.comp_id f.operator)
  assoc f g h := Morphism.ext (Category.assoc f.operator g.operator h.operator)

/-- The whole original native necklace diagram in any coefficient universe. -/
def functor : Data ⥤ SSet.{u} where
  obj := Data.object
  map := Morphism.map
  map_id := Morphism.map_id
  map_comp := Morphism.map_comp

/-- The same original initial vertex is retained by every whole necklace map. -/
@[reassoc]
theorem source_map {T U : Data} (f : T ⟶ U) :
    T.source.{u} ≫ f.map = U.source := by
  change vertexMap T.joints 0 ≫ f.map = vertexMap U.joints 0
  exact (Morphism.vertex_map f 0).trans (congrArg (vertexMap U.joints) f.source)

/-- The same original terminal vertex is retained by every whole necklace map. -/
@[reassoc]
theorem target_map {T U : Data} (f : T ⟶ U) :
    T.target.{u} ≫ f.map = U.target := by
  change vertexMap T.joints (Fin.last T.dimension) ≫ f.map =
    vertexMap U.joints (Fin.last U.dimension)
  exact (Morphism.vertex_map f (Fin.last T.dimension)).trans
    (congrArg (vertexMap U.joints) f.target)

end SSet.OriginalNecklace
