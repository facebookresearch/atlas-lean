/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.InternalHomCarrier
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Interval

/-!
# The actual marked product and internal-Hom adjunction

Currying sends each original source simplex to its entire marked prism.
Evaluation reads that same prism on the identity parameter simplex.
The maximal-interval edge classifier proves preservation of the original
marks. The inverse equations and both adjunction triangles concern these
literal maps; no marked model structure is assumed.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked

/-- The whole prism at each source simplex gives the original underlying curried map. -/
def curryUnderlying {A X Y : Marked.{u}} (f : prod A X ⟶ Y) :
    A.toSSet ⟶ (internalHom X Y).toSSet where
  app n := ↾fun a => prodMap (ofMin (SSet.yonedaEquiv.symm a)) (𝟙 X) ≫ f
  naturality n m a := by
    apply ConcreteCategory.hom_ext
    intro z
    apply Hom.ext
    let f₀ : A.toSSet ⊗ X.toSSet ⟶ Y.toSSet := f.hom
    change (SSet.yonedaEquiv.symm (A.toSSet.map a z) ▷ X.toSSet) ≫ f₀ =
      (SSet.stdSimplex.map a.unop ▷ X.toSSet) ≫
        (SSet.yonedaEquiv.symm z ▷ X.toSSet) ≫ f₀
    rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight,
      SSet.yonedaEquiv_symm_naturality_left]
    rfl

/-- Actual product maps curry to marked internal-Hom maps with the same complete prisms. -/
def curry {A X Y : Marked.{u}} (f : prod A X ⟶ Y) : A ⟶ internalHom X Y where
  hom := curryUnderlying f
  preserve {e} he := by
    refine ⟨prodMap (intervalMapOfMarkedEdge e he) (𝟙 X) ≫ f, ?_⟩
    apply Hom.ext
    rfl

/-- Evaluation reads the original prism on the identity parameter simplex. -/
def evaluationUnderlying (X Y : Marked.{u}) :
    (prod (internalHom X Y) X).toSSet ⟶ Y.toSSet where
  app n := ↾fun a => a.1.hom.app n
    (SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj n.unop)), a.2)
  naturality n m a := by
    apply ConcreteCategory.hom_ext
    intro z
    let F : SSet.stdSimplex.obj n.unop ⊗ X.toSSet ⟶ Y.toSSet := z.1.hom
    let t : (SSet.stdSimplex.obj n.unop ⊗ X.toSSet).obj n :=
      (SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj n.unop)), z.2)
    have h := NatTrans.naturality_apply F a t
    exact h

/-- The original evaluation map preserves the supplied source and internal-Hom markings. -/
def evaluation (X Y : Marked.{u}) : prod (internalHom X Y) X ⟶ Y where
  hom := evaluationUnderlying X Y
  preserve {e} he := by
    obtain ⟨f, hf⟩ := he.1
    have h := f.preserve
      (show (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), e.2) ∈
        (prod (max (Δ[1] : SSet.{u})) X).marking from ⟨Set.mem_univ _, he.2⟩)
    change e.1.hom.app (op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), e.2) ∈ Y.marking
    rw [← hf]
    exact h

/-- Uncurrying is the original product map followed by the actual evaluation map. -/
def uncurry {A X Y : Marked.{u}} (g : A ⟶ internalHom X Y) : prod A X ⟶ Y :=
  prodMap g (𝟙 X) ≫ evaluation X Y

/-- Uncurrying a curried map retains the original product map in every degree. -/
@[simp]
theorem uncurry_curry {A X Y : Marked.{u}} (f : prod A X ⟶ Y) :
    uncurry (curry f) = f := by
  apply Hom.ext
  ext n a
  let F : A.toSSet ⊗ X.toSSet ⟶ Y.toSSet := f.hom
  change F.app n ((SSet.yonedaEquiv.symm a.1).app n
    (SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj n.unop))), a.2) = F.app n a
  rw [SSet.yonedaEquiv_symm_app_id]
  rfl

/-- Currying the actual evaluation composite retains the whole original internal-Hom map. -/
@[simp]
theorem curry_uncurry {A X Y : Marked.{u}} (g : A ⟶ internalHom X Y) :
    curry (uncurry g) = g := by
  apply Hom.ext
  ext n a
  apply Hom.ext
  ext m z
  let z₀ : (SSet.stdSimplex.obj n.unop ⊗ X.toSSet).obj m := z
  let F : SSet.stdSimplex.obj n.unop ⊗ X.toSSet ⟶ Y.toSSet := (g.hom.app n a).hom
  have h := congrArg (fun q => q.hom.app m
    (SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj m.unop)), z₀.2))
      (NatTrans.naturality_apply g.hom (SSet.stdSimplex.objEquiv z₀.1).op a)
  change (g.hom.app m (A.toSSet.map (SSet.stdSimplex.objEquiv z₀.1).op a)).hom.app m
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

/-- The full marked product/internal-Hom universal property uses these same native maps. -/
def internalHomHomEquiv (A X Y : Marked.{u}) :
    (prod A X ⟶ Y) ≃ (A ⟶ internalHom X Y) where
  toFun := curry
  invFun := uncurry
  left_inv := uncurry_curry
  right_inv := curry_uncurry

/-- Uncurrying is natural in the original source map. -/
theorem uncurry_natural_left {A A' X Y : Marked.{u}}
    (a : A' ⟶ A) (g : A ⟶ internalHom X Y) :
    uncurry (a ≫ g) = prodMap a (𝟙 X) ≫ uncurry g := by
  apply Hom.ext
  rfl

/-- Currying commutes with the original marked target map. -/
theorem curry_natural_right {A X Y Y' : Marked.{u}}
    (f : prod A X ⟶ Y) (p : Y ⟶ Y') :
    curry (f ≫ p) = curry f ≫ internalHomPost X p := by
  apply Hom.ext
  ext n a
  exact Hom.ext rfl

/-- The actual marked product functor is left adjoint to the native marked internal-Hom functor. -/
def internalHomAdjunction (X : Marked.{u}) : prodRight X ⊣ internalHomFunctor X :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun A Y => internalHomHomEquiv A X Y
      homEquiv_naturality_left_symm := by
        intro A' A Y a g
        exact uncurry_natural_left a g
      homEquiv_naturality_right := by
        intro A Y Y' f p
        exact curry_natural_right f p }

end SSet.Marked
