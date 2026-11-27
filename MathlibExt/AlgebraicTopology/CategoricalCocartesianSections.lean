/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.QuasicategoricalModels
public import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration

/-!
# Actual cocartesian sections and their categorical coherence

Cocartesian edges use the relative special-outer-horn lifting test.
A section simplex is a native simplicial Hom simplex, hence an actual
map from the parameter simplex times the entire base. Its projection is
the identity on the base in every degree. The horizontal base edges at
each parameter vertex are cocartesian. Parameter edges retain all
noninvertible module maps.

The resulting literal subcomplex is the category of cocartesian
sections of the fixed cocartesian fibration. It models the categorical
limit of the corresponding covariant functor. No Kan core or ordinary
space homotopy limit substitutes for this category of sections.

References: Lurie, Higher Topos Theory, §§2.4.1 and 3.3.3,
especially Proposition 2.4.1.10 and Corollary 3.3.3.2.
Only native simplicial Hom, horn inclusions and subcomplexes are used.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicTopology.CategoricalCocartesianSections

open CategoryTheory Opposite
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open MathlibExt.AlgebraicTopology.QuasicategoricalModels
open scoped Simplicial

universe u

/-- The actual first edge of the n+2 simplex. -/
def firstEdge (n : ℕ) : (Δ[1] : SSet.{u}) ⟶ Δ[n + 2] :=
  SSet.stdSimplex.map
    (edgeInclusion (0 : Fin (n + 3)) (1 : Fin (n + 3)) (Fin.zero_le _))

/-- Cocartesian means the displayed relative special-outer-horn lifting test.
The initial-edge inclusion into the horn is tested by its actual composite. -/
def IsCocartesianEdge {E B : SSet.{u}} (p : E ⟶ B) (e : E _⦋1⦌) : Prop :=
  ∀ (n : ℕ) (a : (Λ[n + 2, 0] : SSet.{u}) ⟶ E) (b : Δ[n + 2] ⟶ B)
    (j : Δ[1] ⟶ (Λ[n + 2, 0] : SSet.{u})),
    j ≫ Λ[n + 2, 0].ι = firstEdge n →
    j ≫ a = SSet.yonedaEquiv.symm e →
    a ≫ p = Λ[n + 2, 0].ι ≫ b →
    ∃ c : Δ[n + 2] ⟶ E, Λ[n + 2, 0].ι ≫ c = a ∧ c ≫ p = b

/-- An actual cocartesian fibration has inner lifting and all edge transports. -/
structure CocartesianFibration {E B : SSet.{u}} (p : E ⟶ B) : Prop where
  inner : SSet.InnerFibration p
  lift : ∀ (b : B _⦋1⦌) (x : E _⦋0⦌),
    p.app (op ⦋0⦌) x = B.δ 1 b →
      ∃ e : E _⦋1⦌,
        E.δ 1 e = x ∧ p.app (op ⦋1⦌) e = b ∧ IsCocartesianEdge p e

/-- The constant parameter edge at one vertex of the parameter simplex. -/
def vertexParameter (n : SimplexCategoryᵒᵖ) (i : Fin (n.unop.len + 1)) : n ⟶ op ⦋1⦌ :=
  Quiver.Hom.op (SimplexCategory.Hom.mk (OrderHom.const (Fin 2) i))

/-- Parameter restriction maps its vertices by the actual simplex order map. -/
theorem vertexParameter_comp {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    (i : Fin (m.unop.len + 1)) :
    f ≫ vertexParameter m i = vertexParameter n (f.unop.toOrderHom i) := by
  apply Quiver.Hom.unop_inj
  ext t
  rfl

/-- A section simplex fixes its base on every simplex and retains cocartesian
horizontal transports at every parameter vertex. -/
def IsSectionSimplex {E B : SSet.{u}} (p : E ⟶ B) (n : SimplexCategoryᵒᵖ)
    (a : (mapping B E).obj n) : Prop :=
  (∀ (m : SimplexCategoryᵒᵖ) (f : n ⟶ m) (x : B.obj m),
    p.app m ((a.app m f) x) = x) ∧
  ∀ (i : Fin (n.unop.len + 1)) (e : B _⦋1⦌),
    IsCocartesianEdge p ((a.app (op ⦋1⦌) (vertexParameter n i)) e)

/-- The literal subcomplex of native Hom consisting of cocartesian sections. -/
def sectionSubcomplex {E B : SSet.{u}} (p : E ⟶ B) : (mapping B E).Subcomplex where
  obj n := {a | IsSectionSimplex p n a}
  map {n m} f a h := by
    refine ⟨?_, ?_⟩
    · intro l g x
      exact h.1 l (f ≫ g) x
    · intro i e
      change IsCocartesianEdge p ((a.app (op ⦋1⦌) (f ≫ vertexParameter m i)) e)
      rw [vertexParameter_comp]
      exact h.2 (f.unop.toOrderHom i) e

/-- The full categorical section object, with all parameter arrows retained. -/
abbrev sections {E B : SSet.{u}} (p : E ⟶ B) : SSet.{u} :=
  (sectionSubcomplex p).toSSet

/-- A vertex is an actual compatible cocartesian section. -/
abbrev Section {E B : SSet.{u}} (p : E ⟶ B) := (sections p) _⦋0⦌

/-- A section over an actual base map fixes that map in every simplicial degree. -/
def IsSectionSimplexOver {E B A : SSet.{u}} (p : E ⟶ B) (q : A ⟶ B)
    (n : SimplexCategoryᵒᵖ) (a : (mapping A E).obj n) : Prop :=
  (∀ (m : SimplexCategoryᵒᵖ) (f : n ⟶ m) (x : A.obj m),
    p.app m ((a.app m f) x) = q.app m x) ∧
  ∀ (i : Fin (n.unop.len + 1)) (e : A _⦋1⦌),
    IsCocartesianEdge p ((a.app (op ⦋1⦌) (vertexParameter n i)) e)

/-- The literal cocartesian section subcomplex over q, equivalent to sections
of the native pullback fibration. Parameter arrows remain unrestricted. -/
def sectionSubcomplexOver {E B A : SSet.{u}} (p : E ⟶ B) (q : A ⟶ B) :
    (mapping A E).Subcomplex where
  obj n := {a | IsSectionSimplexOver p q n a}
  map {n m} f a h := by
    refine ⟨?_, ?_⟩
    · intro l g x
      exact h.1 l (f ≫ g) x
    · intro i e
      change IsCocartesianEdge p ((a.app (op ⦋1⦌) (f ≫ vertexParameter m i)) e)
      rw [vertexParameter_comp]
      exact h.2 (f.unop.toOrderHom i) e

/-- The actual categorical section object over q. -/
abbrev sectionsOver {E B A : SSet.{u}} (p : E ⟶ B) (q : A ⟶ B) : SSet.{u} :=
  (sectionSubcomplexOver p q).toSSet

/-- Native precomposition on the full simplicial Hom. -/
def precompose {A B E : SSet.{u}} (f : A ⟶ B) : mapping B E ⟶ mapping A E :=
  ((SimplicialCategory.sHomFunctor SSet).map f.op).app E

/-- Reindex actual cocartesian sections by the full simplicial base map. -/
def sectionsOverMap {E B A C : SSet.{u}} (p : E ⟶ B)
    (q : A ⟶ B) (r : C ⟶ B) (f : C ⟶ A) (h : f ≫ q = r) :
    sectionsOver p q ⟶ sectionsOver p r where
  app n := ↾fun a => ⟨(precompose f).app n a.val, by
    refine ⟨?_, ?_⟩
    · intro m g x
      change p.app m ((a.val.app m g) (f.app m x)) = r.app m x
      rw [a.property.1 m g (f.app m x)]
      exact congrArg (fun t => t.app m x) h
    · intro i e
      change IsCocartesianEdge p ((a.val.app (op ⦋1⦌) (vertexParameter n i))
        (f.app (op ⦋1⦌) e))
      exact a.property.2 i (f.app (op ⦋1⦌) e)⟩
  naturality n m g := by
    ext a
    apply Subtype.ext
    exact congrArg (fun t => t a.val) ((precompose f).naturality g)

end MathlibExt.AlgebraicTopology.CategoricalCocartesianSections
