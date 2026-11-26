/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.SimplicialCategory.SimplicialObject
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Actual mapping simplicial sets and cosimplicial totalization

The mapping object has n-simplices `X × Δ[n] → Y`. Totalization has
n-simplices the compatible maps `Δ[•] × Δ[n] → C[•]`. These are actual
functor/natural-transformation carriers. They will be used with explicitly
specified fibrant replacements; strict totalization alone is not asserted
to compute a derived limit of every diagram.

References: Bousfield--Kan, *Homotopy limits, completions and
localizations*, Chapters X--XI; PTVV arXiv:1111.3209v4, conventions and
§1; Bhatt--Mathew arXiv:1807.04725, Theorems 1.7--1.10.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.SimplicialDerivedModels

open CategoryTheory MonoidalCategory Opposite

universe u

/-- Postcomposition on the actual generalized loops. -/
def mapLoop {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ) (x : X)
    (a : GenLoop (Fin n) X x) : GenLoop (Fin n) Y (f x) :=
  ⟨f.hom.comp a.val, by
    intro t ht
    change f (a.val t) = f x
    rw [a.property t ht]⟩

/-- The actual homotopy class of a generalized loop. -/
def loopClass {X : TopCat.{u}} (n : ℕ) (x : X)
    (a : GenLoop (Fin n) X x) : HomotopyGroup.Pi n X x :=
  Quotient.mk _ a

/-- Weak homotopy equivalence in the geometric realization model:
bijective path components and bijective pointed homotopy groups. The
loop clauses are the quotient-surjectivity/injectivity formulation and
therefore do not choose a free homotopy invariant. -/
def IsWeakHomotopyEquivalence {X Y : TopCat.{u}} (f : X ⟶ Y) : Prop :=
  (∀ y : Y, ∃ x : X, Joined (f x) y) ∧
  (∀ x x' : X, Joined (f x) (f x') → Joined x x') ∧
  ∀ (n : ℕ), 0 < n → ∀ x : X,
    (∀ a : GenLoop (Fin n) Y (f x), ∃ b : GenLoop (Fin n) X x,
      loopClass n (f x) (mapLoop f n x b) = loopClass n (f x) a) ∧
    (∀ a b : GenLoop (Fin n) X x,
      loopClass n (f x) (mapLoop f n x a) = loopClass n (f x) (mapLoop f n x b) →
        loopClass n x a = loopClass n x b)

/-- Simplicial weak equivalence is bound to the actual realization map. -/
def WeakEquivalence {X Y : SSet.{u}} (f : X ⟶ Y) : Prop :=
  IsWeakHomotopyEquivalence (SSet.toTop.map f)

/-- The simplicial mapping space of simplicial sets $X$ and $Y$: the internal Hom of simplicial
sets, whose $n$-simplices are the maps $X \times \Delta[n] \to Y$. -/
abbrev mapping (X Y : SSet.{u}) : SSet.{u} :=
  SimplicialCategory.sHom X Y

/-- The native zero-simplex comparison, not a free map-space carrier. -/
def mappingZero (X Y : SSet.{u}) :
    (X ⟶ Y) ≃ (mapping X Y).obj (op (SimplexCategory.mk 0)) :=
  SimplicialCategory.homEquiv' X Y

/-- The cosimplicial product of the standard simplex with a fixed
parameter simplicial set. -/
def cylinder (P : SSet.{u}) : SimplexCategory ⥤ SSet.{u} where
  obj n := SSet.stdSimplex.obj n ⊗ P
  map f := SSet.stdSimplex.map f ⊗ₘ 𝟙 P
  map_id n := by simp
  map_comp f g := by
    simp only [Functor.map_comp]
    rw [tensorHom_comp_tensorHom]
    simp

/-- A parameter map induces the literal product map in every
cosimplicial degree. -/
def cylinderMap {P Q : SSet.{u}} (f : P ⟶ Q) : cylinder P ⟶ cylinder Q where
  app n := 𝟙 (SSet.stdSimplex.obj n) ⊗ₘ f
  naturality a b g := by
    simp only [cylinder, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]

@[simp]
theorem cylinderMap_id (P : SSet.{u}) : cylinderMap (𝟙 P) = 𝟙 (cylinder P) := by
  ext n m x
  rfl

@[simp]
theorem cylinderMap_comp {P Q R : SSet.{u}} (f : P ⟶ Q) (g : Q ⟶ R) :
    cylinderMap (f ≫ g) = cylinderMap f ≫ cylinderMap g := by
  ext n m x
  rfl

/-- Actual cosimplicial totalization. A simplex is a compatible natural
family, not an arbitrarily supplied object called a homotopy limit. -/
def totalization (X : SimplexCategory ⥤ SSet.{u}) : SSet.{u} where
  obj n := cylinder (SSet.stdSimplex.obj n.unop) ⟶ X
  map f := ↾fun a => cylinderMap (SSet.stdSimplex.map f.unop) ≫ a
  map_id n := by
    ext a
    simp
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro a
    change cylinderMap (SSet.stdSimplex.map (g.unop ≫ f.unop)) ≫ a =
      cylinderMap (SSet.stdSimplex.map g.unop) ≫
        (cylinderMap (SSet.stdSimplex.map f.unop) ≫ a)
    simp only [Functor.map_comp, cylinderMap_comp, Category.assoc]

/-- Totalization maps are postcomposition by the actual diagram map. -/
def totalizationMap {X Y : SimplexCategory ⥤ SSet.{u}} (f : X ⟶ Y) :
    totalization X ⟶ totalization Y where
  app n := ↾fun a => a ≫ f
  naturality a b g := by
    ext x
    exact Category.assoc _ _ _

/-- The based homotopy fibre model uses the actual mapping-path object
and both endpoint maps; fibrant-replacement requirements are retained by
the separate model interface. -/
def mappingPathObject (Y : SSet.{u}) : SSet.{u} :=
  mapping (SSet.stdSimplex.obj (SimplexCategory.mk 1)) Y

/-- A simplicial path, with literal source and target endpoint equations. -/
structure Path (Y : SSet.{u})
    (x y : (SSet.stdSimplex.obj (SimplexCategory.mk 0)) ⟶ Y) where
  edge : (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ⟶ Y
  source : SSet.stdSimplex.δ 1 ≫ edge = x
  target : SSet.stdSimplex.δ 0 ≫ edge = y

end MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
