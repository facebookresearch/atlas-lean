/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.InternalHomAdjunction

/-!
# Maximal-parameter families and the actual marked mapping complex

Maps from the maximally marked original parameter product are represented
by the actual maximal marked mapping complex. Currying retains each whole
parameter prism; uncurrying is the previously proved original marked
evaluation map. The inverse and naturality equations hold without a
fibrancy hypothesis on the parameter, source, or target.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked

/-- The original maximally marked family gives all of its original parameter prisms. -/
def maxCurry {K : SSet.{u}} {X Y : Marked.{u}} (f : prod (max K) X ⟶ Y) :
    K ⟶ mappingComplex .maximal X Y where
  app n := ↾fun a => prodMap (maximal.map (SSet.yonedaEquiv.symm a)) (𝟙 X) ≫ f
  naturality n m a := by
    ext z
    apply Hom.ext
    let F : K ⊗ X.toSSet ⟶ Y.toSSet := f.hom
    change (SSet.yonedaEquiv.symm (K.map a z) ▷ X.toSSet) ≫ F =
      (SSet.stdSimplex.map a.unop ▷ X.toSSet) ≫ (SSet.yonedaEquiv.symm z ▷ X.toSSet) ≫ F
    rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight,
      SSet.yonedaEquiv_symm_naturality_left]
    rfl

/-- A map into the actual maximal mapping complex preserves the original internal-Hom edge marking. -/
def maxMapToInternalHom {K : SSet.{u}} {X Y : Marked.{u}}
    (g : K ⟶ mappingComplex .maximal X Y) : max K ⟶ internalHom X Y where
  hom := g ≫ mappingComplexMaxToMin X Y
  preserve {e} _ := ⟨g.app (op ⦋1⦌) e, rfl⟩

/-- Uncurrying uses the already proved original marked evaluation map. -/
def maxUncurry {K : SSet.{u}} {X Y : Marked.{u}}
    (g : K ⟶ mappingComplex .maximal X Y) : prod (max K) X ⟶ Y :=
  uncurry (maxMapToInternalHom g)

/-- This uncurrying reads the whole original prism at the identity parameter simplex. -/
theorem maxUncurry_app {K : SSet.{u}} {X Y : Marked.{u}}
    (g : K ⟶ mappingComplex .maximal X Y) (n : SimplexCategoryᵒᵖ)
    (a : K.obj n) (x : X.toSSet.obj n) :
    (maxUncurry g).hom.app n (a, x) = (g.app n a).hom.app n
      (SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj n.unop)), x) := rfl

/-- Reading these same prisms recovers the original marked family. -/
@[simp]
theorem maxUncurry_maxCurry {K : SSet.{u}} {X Y : Marked.{u}}
    (f : prod (max K) X ⟶ Y) : maxUncurry (maxCurry f) = f := by
  apply Hom.ext
  ext n a
  let F : K ⊗ X.toSSet ⟶ Y.toSSet := f.hom
  change F.app n ((SSet.yonedaEquiv.symm a.1).app n
    (SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj n.unop))), a.2) = F.app n a
  rw [SSet.yonedaEquiv_symm_app_id]
  rfl

/-- Restricting the original evaluation composite recovers every entire maximal mapping simplex. -/
@[simp]
theorem maxCurry_maxUncurry {K : SSet.{u}} {X Y : Marked.{u}}
    (g : K ⟶ mappingComplex .maximal X Y) : maxCurry (maxUncurry g) = g := by
  ext n a
  apply Hom.ext
  ext m z
  let z₀ : (SSet.stdSimplex.obj n.unop ⊗ X.toSSet).obj m := z
  let F : SSet.stdSimplex.obj n.unop ⊗ X.toSSet ⟶ Y.toSSet := (g.app n a).hom
  have h := congrArg (fun q => q.hom.app m
    (SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj m.unop)), z₀.2))
      (NatTrans.naturality_apply g (SSet.stdSimplex.objEquiv z₀.1).op a)
  change (g.app m (K.map (SSet.stdSimplex.objEquiv z₀.1).op a)).hom.app m
      (SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj m.unop)), z₀.2) =
    F.app m ((SSet.stdSimplex.map (SSet.stdSimplex.objEquiv z₀.1)).app m
      (SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj m.unop))), z₀.2) at h
  have hp : (SSet.stdSimplex.map (SSet.stdSimplex.objEquiv z₀.1)).app m
      (SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj m.unop))) = z₀.1 := by
    change SSet.stdSimplex.objEquiv.symm (𝟙 m.unop ≫ SSet.stdSimplex.objEquiv z₀.1) = z₀.1
    rw [Category.id_comp]
    exact Equiv.symm_apply_apply _ z₀.1
  rw [hp] at h
  exact h

/-- The actual maximal marked mapping complex represents the original maximally marked parameter families. -/
def maxFamilyHomEquiv (K : SSet.{u}) (X Y : Marked.{u}) :
    (prod (max K) X ⟶ Y) ≃ (K ⟶ mappingComplex .maximal X Y) where
  toFun := maxCurry
  invFun := maxUncurry
  left_inv := maxUncurry_maxCurry
  right_inv := maxCurry_maxUncurry

/-- The same original marked target map commutes with maximal currying. -/
theorem maxCurry_post {K : SSet.{u}} {X Y Z : Marked.{u}}
    (f : prod (max K) X ⟶ Y) (p : Y ⟶ Z) :
    maxCurry (f ≫ p) = maxCurry f ≫ mappingComplexPost .maximal X p := by
  ext n a
  exact Hom.ext rfl

/-- The original parameter map is retained by maximal currying. -/
theorem maxCurry_pre {K K' : SSet.{u}} {X Y : Marked.{u}}
    (a : K' ⟶ K) (f : prod (max K) X ⟶ Y) :
    maxCurry (prodMap (maximal.map a) (𝟙 X) ≫ f) = a ≫ maxCurry f := by
  ext n z
  apply Hom.ext
  let F : K ⊗ X.toSSet ⟶ Y.toSSet := f.hom
  change (SSet.yonedaEquiv.symm z ▷ X.toSSet) ≫ (a ▷ X.toSSet) ≫ F =
    (SSet.yonedaEquiv.symm (a.app n z) ▷ X.toSSet) ≫ F
  rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight, SSet.yonedaEquiv_symm_comp]

/-- Original parameter precomposition commutes with the same marked evaluation composite. -/
theorem maxUncurry_pre {K K' : SSet.{u}} {X Y : Marked.{u}}
    (a : K' ⟶ K) (g : K ⟶ mappingComplex .maximal X Y) :
    maxUncurry (a ≫ g) = prodMap (maximal.map a) (𝟙 X) ≫ maxUncurry g := by
  apply Hom.ext
  rfl

end SSet.Marked
