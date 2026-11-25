/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# The actual marked simplicial-set carrier

A marking is a set of actual one-simplices containing every degenerate
edge. Morphisms retain the original simplicial map and preserve that set.
Minimal and maximal markings give the two genuine forgetful adjunctions.
This carrier construction does not assert a marked model structure or
straightening equivalence.
-/

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet

/-- A simplicial set with a specified marking of its actual one-simplices. -/
structure Marked where
  /-- The original simplicial-set carrier. -/
  toSSet : SSet.{u}
  /-- The specified marked edges. -/
  marking : Set (toSSet _⦋1⦌)
  /-- Every original degenerate edge is marked. -/
  degenerate_mem (x : toSSet _⦋0⦌) : toSSet.σ (0 : Fin 1) x ∈ marking

namespace Marked

/-- A marked morphism retains its actual simplicial map and edge-preservation property. -/
structure Hom (X Y : Marked.{u}) where
  /-- The original simplicial map. -/
  hom : X.toSSet ⟶ Y.toSSet
  /-- Every marked edge maps to a marked edge. -/
  preserve {e : X.toSSet _⦋1⦌} (he : e ∈ X.marking) : hom.app (op ⦋1⦌) e ∈ Y.marking

@[ext] theorem Hom.ext {X Y : Marked.{u}} {f g : Hom X Y} (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

instance : Category Marked.{u} where
  Hom := Hom
  id X := ⟨𝟙 X.toSSet, fun he => he⟩
  comp f g := ⟨f.hom ≫ g.hom, fun he => g.preserve (f.preserve he)⟩
  id_comp f := Hom.ext (Category.id_comp f.hom)
  comp_id f := Hom.ext (Category.comp_id f.hom)
  assoc f g h := Hom.ext (Category.assoc f.hom g.hom h.hom)

/-- Forget only the specified marking, retaining every original map. -/
def forget : Marked.{u} ⥤ SSet.{u} where
  obj X := X.toSSet
  map f := f.hom

instance : forget.{u}.Faithful where
  map_injective h := Hom.ext h

/-- The minimal marking consists of precisely the actual degenerate edges. -/
def min (X : SSet.{u}) : Marked.{u} where
  toSSet := X
  marking := Set.range (X.σ (0 : Fin 1))
  degenerate_mem x := ⟨x, rfl⟩

/-- The maximal marking contains every original edge. -/
def max (X : SSet.{u}) : Marked.{u} where
  toSSet := X
  marking := Set.univ
  degenerate_mem _ := Set.mem_univ _

/-- Every original simplicial map out of a minimally marked source preserves its marking. -/
def ofMin {X : SSet.{u}} {Y : Marked.{u}} (f : X ⟶ Y.toSSet) : min X ⟶ Y where
  hom := f
  preserve he := by
    obtain ⟨x, rfl⟩ := he
    exact (SSet.σ_naturality_apply f (0 : Fin 1) x).symm ▸ Y.degenerate_mem (f.app _ x)

/-- Every original simplicial map into a maximally marked target preserves its marking. -/
def toMax {X : Marked.{u}} {Y : SSet.{u}} (f : X.toSSet ⟶ Y) : X ⟶ max Y where
  hom := f
  preserve _ := Set.mem_univ _

/-- The minimal-marking functor uses the same original simplicial maps. -/
def minimal : SSet.{u} ⥤ Marked.{u} where
  obj := min
  map f := ofMin f
  map_id _ := Hom.ext rfl
  map_comp _ _ := Hom.ext rfl

/-- The maximal-marking functor uses the same original simplicial maps. -/
def maximal : SSet.{u} ⥤ Marked.{u} where
  obj := max
  map f := toMax f
  map_id _ := Hom.ext rfl
  map_comp _ _ := Hom.ext rfl

/-- Minimal source markings retain the entire original simplicial Hom set. -/
def minimalHomEquiv (X : SSet.{u}) (Y : Marked.{u}) :
    (minimal.obj X ⟶ Y) ≃ (X ⟶ forget.obj Y) where
  toFun f := f.hom
  invFun f := ofMin f
  left_inv _ := Hom.ext rfl
  right_inv _ := rfl

/-- Maximal target markings retain the entire original simplicial Hom set. -/
def maximalHomEquiv (X : Marked.{u}) (Y : SSet.{u}) :
    (X ⟶ maximal.obj Y) ≃ (forget.obj X ⟶ Y) where
  toFun f := f.hom
  invFun f := toMax f
  left_inv _ := Hom.ext rfl
  right_inv _ := rfl

/-- The minimal-marking/forgetful adjunction is constructed from these same actual maps. -/
def minimalAdjunction : minimal.{u} ⊣ forget.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := minimalHomEquiv
      homEquiv_naturality_left_symm := by intro X' X Y f g; exact Hom.ext rfl
      homEquiv_naturality_right := by intro X Y Y' f g; rfl }

/-- Forgetting the marking is left adjoint to the maximal-marking functor on the same carriers. -/
def maximalAdjunction : forget.{u} ⊣ maximal.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y => (maximalHomEquiv X Y).symm
      homEquiv_naturality_left_symm := by intro X' X Y f g; rfl
      homEquiv_naturality_right := by intro X Y Y' f g; exact Hom.ext rfl }

/-- Pull back the specified marking along an actual simplicial map. -/
def comap (Y : Marked.{u}) {X : SSet.{u}} (f : X ⟶ Y.toSSet) : Marked.{u} where
  toSSet := X
  marking := f.app (op ⦋1⦌) ⁻¹' Y.marking
  degenerate_mem x := by
    change f.app (op ⦋1⦌) (X.σ (0 : Fin 1) x) ∈ Y.marking
    exact (SSet.σ_naturality_apply f (0 : Fin 1) x).symm ▸ Y.degenerate_mem (f.app _ x)

/-- The original base-change map preserves the pulled-back marking literally. -/
def comapHom (Y : Marked.{u}) {X : SSet.{u}} (f : X ⟶ Y.toSSet) : comap Y f ⟶ Y :=
  ⟨f, fun he => he⟩

/-- Identity base change keeps the entire original marked object. -/
theorem comap_id (X : Marked.{u}) : comap X (𝟙 X.toSSet) = X := by
  cases X
  rfl

/-- Successive base changes retain the same literal pulled-back edge set. -/
theorem comap_comp (Z : Marked.{u}) {X Y : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z.toSSet) :
    comap Z (f ≫ g) = comap (comap Z g) f := rfl

end Marked
end SSet
