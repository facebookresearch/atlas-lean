/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeUpperHom
import MathlibExt.CategoryTheory.NerveHomotopy

/-!
# The full original marked upper layer identifies with its native Hom

The two actual whole-subset functors are inverse on every original
object and inclusion. Their genuine categorical equivalence and native
nerve maps identify the actual inherited marked upper layer with the
maximally marked entire coherent Hom nerve. Both full endpoint subsets
and every original simplex remain unchanged.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq

/-- Original coherent path inclusions are proof-unique; this local wrapper proof preserves their actual
  induced-category morphisms. -/
local instance pathHomSubsingleton {n : ℕ} (i k : Vertex.{u} n)
    (p q : SimplicialThickening.Path i k) : Subsingleton (p ⟶ q) :=
  ⟨fun f g => InducedCategory.Hom.ext (Subsingleton.elim f.hom g.hom)⟩

/-- The native subset conversions compose to the identity upper-layer functor, including every original inclusion. -/
theorem upperConePathFunctor_comp {n : ℕ} (i k : Vertex.{u} n) :
    upperConePathFunctor i k ⋙ pathUpperConeFunctor i k = 𝟭 (UpperCone i k) :=
  CategoryTheory.Functor.ext (fun a => pathUpperCone_upperConePath a) (fun _ _ _ => Subsingleton.elim _ _)

/-- The whole original coherent path functor is recovered in the other direction. -/
theorem pathUpperConeFunctor_comp {n : ℕ} (i k : Vertex.{u} n) :
    pathUpperConeFunctor i k ⋙ upperConePathFunctor i k = 𝟭 (SimplicialThickening.Path i k) :=
  CategoryTheory.Functor.ext (fun p => upperConePath_pathUpperCone p) (fun _ _ _ => Subsingleton.elim _ _)

/-- The genuine original upper layer and entire coherent Hom are equivalent through their actual whole
  subset conversions. -/
def upperConeHomEquivalence {n : ℕ} (i k : Vertex.{u} n) : UpperCone i k ≌ SimplicialThickening.Path i k where
  functor := upperConePathFunctor i k
  inverse := pathUpperConeFunctor i k
  unitIso := NatIso.ofComponents (fun a => eqToIso (pathUpperCone_upperConePath a).symm)
    (fun _ => Subsingleton.elim _ _)
  counitIso := NatIso.ofComponents (fun p => eqToIso (upperConePath_pathUpperCone p))
    (fun _ => Subsingleton.elim _ _)
  functor_unitIso_comp _ := Subsingleton.elim _ _

/-- The original full upper-layer inclusion retains its whole original cone subset and each actual inclusion. -/
def upperConeInclusion {n : ℕ} (i k : Vertex.{u} n) : UpperCone i k ⥤ ConeSubset i where
  obj a := a.val
  map f := homOfLE (leOfHom f)

/-- The actual upper layer inherits precisely the original cone marking along its entire native inclusion map. -/
def upperConeWeight {n : ℕ} (i k : Vertex.{u} n) : Marked.{u} :=
  comap (coneWeight i) (nerveMap (upperConeInclusion i k))

/-- Every whole original upper-layer edge is marked because both endpoints retain the same actual maximum. -/
theorem upperConeWeight_all_marked {n : ℕ} (i k : Vertex.{u} n) (e : (nerve (UpperCone i k)) _⦋1⦌) :
    e ∈ (upperConeWeight i k).marking :=
  (e.obj 0).property.trans (e.obj 1).property.symm

/-- The inherited original upper-layer marking is exactly maximal, through identity maps on every whole simplex. -/
def upperConeMaxIso {n : ℕ} (i k : Vertex.{u} n) : upperConeWeight i k ≅ max (nerve (UpperCone i k)) :=
  isoMk (Iso.refl _) (fun e => ⟨fun _ => Set.mem_univ _, fun _ => upperConeWeight_all_marked i k e⟩)

/-- The actual entire original marked upper layer is the whole coherent Hom nerve, with both native inverse
  simplex maps proved. -/
def upperConeHomIso {n : ℕ} (i k : Vertex.{u} n) :
    upperConeWeight i k ≅ max (nerve (SimplicialThickening.Path i k)) :=
  upperConeMaxIso i k ≪≫
    { hom := maximal.map (nerveMap (upperConePathFunctor i k))
      inv := maximal.map (nerveMap (pathUpperConeFunctor i k))
      hom_inv_id := by
        apply Hom.ext
        change nerveMap (upperConePathFunctor i k) ≫ nerveMap (pathUpperConeFunctor i k) = 𝟙 _
        rw [nerveMap_comp, upperConePathFunctor_comp, nerveMap_id]
      inv_hom_id := by
        apply Hom.ext
        change nerveMap (pathUpperConeFunctor i k) ≫ nerveMap (upperConePathFunctor i k) = 𝟙 _
        rw [nerveMap_comp, pathUpperConeFunctor_comp, nerveMap_id] }

end SSet.Marked.CoherentWeight
