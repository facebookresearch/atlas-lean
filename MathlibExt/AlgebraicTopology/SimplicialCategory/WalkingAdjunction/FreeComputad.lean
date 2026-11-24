/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.CategoryTheory.Enriched.Basic
public import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# Simplicial computads with fixed objects

Each scalar degree is the native free path category on its atomic arrows.
A simplex operator can send an atomic arrow to an actual composite path.
This permits a cell face to be the original composition rather than an
independent, unrelated generator. All identity, composition and operator
equations are retained in the resulting simplicial enrichment.

The object and generator universes are independent. Since a path includes
its intermediate objects, the resulting Hom universe is their maximum.
-/

@[expose] public section

universe u v

open CategoryTheory MonoidalCategory

namespace SSet.SimplicialComputad

variable {O : Type v} {G H K : O → O → Type u}

/-- An unchanged object label, carrying its specified atomic-arrow family. -/
structure Vertex (G : O → O → Type u) where
  /-- The original object label. -/
  label : O

instance (G : O → O → Type u) : Quiver.{u} (Vertex G) where
  Hom x y := G x.label y.label

/-- The native paths on a specified family of atomic arrows. -/
abbrev Path (G : O → O → Type u) (x y : O) :=
  Quiver.Path (Vertex.mk (G := G) x) (Vertex.mk (G := G) y)

/-- An atomic arrow regarded as its original singleton path. -/
def single {x y : O} (g : G x y) : Path G x y :=
  @Quiver.Hom.toPath (Vertex G) _ ⟨x⟩ ⟨y⟩ g

/-- The native free-category extension of an assignment of atoms to paths. -/
def pathMap (f : ∀ {x y}, G x y → Path H x y) {x y : O} : Path G x y → Path H x y :=
  let φ : Vertex G ⥤q Paths (Vertex H) :=
    { obj := fun x => ⟨x.label⟩
      map := f }
  (Paths.lift φ).map

/-- Free extension preserves the original identity path. -/
theorem pathMap_nil (f : ∀ {x y}, G x y → Path H x y) (x : O) :
    pathMap f (Quiver.Path.nil : Path G x x) = Quiver.Path.nil := rfl

/-- Free extension evaluates a cons by the actual target path composition. -/
theorem pathMap_cons (f : ∀ {x y}, G x y → Path H x y) {x y z : O}
    (p : Path G x y) (g : G y z) :
    pathMap f (p.cons g) = (pathMap f p).comp (f g) := rfl

/-- Free extension sends a singleton to its prescribed original path. -/
theorem pathMap_single (f : ∀ {x y}, G x y → Path H x y) {x y : O} (g : G x y) :
    pathMap f (single g) = f g := by
  change Quiver.Path.nil.comp (f g) = f g
  exact Quiver.Path.nil_comp _

/-- Free extension preserves the full path composition. -/
theorem pathMap_comp (f : ∀ {x y}, G x y → Path H x y) {x y z : O}
    (p : Path G x y) (q : Path G y z) :
    pathMap f (p.comp q) = (pathMap f p).comp (pathMap f q) := by
  let φ : Vertex G ⥤q Paths (Vertex H) :=
    { obj := fun x => ⟨x.label⟩
      map := f }
  exact (Paths.lift φ).map_comp p q

/-- The singleton assignment extends to the identity on all original paths. -/
theorem pathMap_id {x y : O} (p : Path G x y) :
    pathMap (fun g => single g) p = p := by
  suffices h : ∀ {a b : Vertex G} (q : Quiver.Path a b),
      pathMap (fun g => single g) q = q from h p
  intro a b q
  induction q with
  | nil => rfl
  | cons p g ih =>
    rw [pathMap_cons, ih]
    rfl

/-- Two free extensions agree if they agree on every atomic arrow. -/
theorem pathMap_congr (f g : ∀ {x y}, G x y → Path H x y)
    (h : ∀ {x y} (a : G x y), f a = g a) {x y : O} (p : Path G x y) :
    pathMap f p = pathMap g p := by
  suffices hh : ∀ {a b : Vertex G} (q : Quiver.Path a b),
      pathMap f q = pathMap g q from hh p
  intro a b q
  induction q with
  | nil => rfl
  | cons p a ih => rw [pathMap_cons, pathMap_cons, ih, h]

/-- Iterated free extension is the extension of the actual composite assignment. -/
theorem pathMap_pathMap (f : ∀ {x y}, G x y → Path H x y)
    (g : ∀ {x y}, H x y → Path K x y) {x y : O} (p : Path G x y) :
    pathMap g (pathMap f p) = pathMap (fun a => pathMap g (f a)) p := by
  suffices h : ∀ {a b : Vertex G} (q : Quiver.Path a b),
      pathMap g (pathMap f q) = pathMap (fun a => pathMap g (f a)) q from h p
  intro a b q
  induction q with
  | nil => rfl
  | cons p a ih =>
    rw [pathMap_cons, pathMap_comp, ih, pathMap_cons]

end SSet.SimplicialComputad

namespace SSet

/-- A fixed-object simplicial computad whose scalar levels are native free categories. -/
structure SimplicialComputad (O : Type v) where
  /-- The actual atomic arrows at each scalar simplex. -/
  generator : SimplexCategoryᵒᵖ → O → O → Type u
  /-- A scalar operator sends an atom to its original, possibly composite, path. -/
  operator {Δ Δ' : SimplexCategoryᵒᵖ} (θ : Δ ⟶ Δ') {x y : O} :
    generator Δ x y → SimplicialComputad.Path (generator Δ') x y
  /-- The identity operator is the original singleton path. -/
  operator_id (Δ : SimplexCategoryᵒᵖ) {x y : O} (g : generator Δ x y) :
    operator (𝟙 Δ) g = SimplicialComputad.single g
  /-- Composite operators use actual native path composition. -/
  operator_comp {Δ Δ' Δ'' : SimplexCategoryᵒᵖ} (θ : Δ ⟶ Δ') (φ : Δ' ⟶ Δ'')
      {x y : O} (g : generator Δ x y) :
    operator (θ ≫ φ) g =
      SimplicialComputad.pathMap (operator φ) (operator θ g)

namespace SimplicialComputad

variable {O : Type v} (A : SimplicialComputad.{u, v} O)

/-- The whole scalar operator on all paths, using the native free extension. -/
def map {Δ Δ' : SimplexCategoryᵒᵖ} (θ : Δ ⟶ Δ') {x y : O} :
    Path (A.generator Δ) x y → Path (A.generator Δ') x y :=
  pathMap (A.operator θ)

/-- The full identity scalar operator is the identity on every path. -/
theorem map_id (Δ : SimplexCategoryᵒᵖ) {x y : O} (p : Path (A.generator Δ) x y) :
    A.map (𝟙 Δ) p = p :=
  (pathMap_congr _ _ (fun g => A.operator_id Δ g) p).trans (pathMap_id p)

/-- The full scalar operators obey composition on every original path. -/
theorem map_comp {Δ Δ' Δ'' : SimplexCategoryᵒᵖ} (θ : Δ ⟶ Δ') (φ : Δ' ⟶ Δ'')
    {x y : O} (p : Path (A.generator Δ) x y) :
    A.map (θ ≫ φ) p = A.map φ (A.map θ p) := by
  exact (pathMap_congr _ _ (fun g => A.operator_comp θ φ g) p).trans
    (pathMap_pathMap (A.operator θ) (A.operator φ) p).symm

/-- The actual enriched Hom of paths, with all original scalar operators. -/
def hom (x y : O) : SSet.{max u v} where
  obj Δ := Path (A.generator Δ) x y
  map θ := ↾A.map θ
  map_id Δ := by
    ext p
    exact A.map_id Δ p
  map_comp θ φ := by
    ext p
    exact A.map_comp θ φ p

/-- An object label in the enriched category of the specified computad. -/
structure Object (A : SimplicialComputad.{u, v} O) where
  /-- The original, unchanged object label. -/
  label : O

/-- The full simplicial enrichment constructed from the native degreewise path categories. -/
instance : EnrichedCategory SSet.{max u v} A.Object where
  Hom x y := A.hom x.label y.label
  id x :=
    { app Δ := ↾fun _ => Quiver.Path.nil
      naturality := by
        intro Δ Δ' θ
        ext p
        rfl }
  comp x y z :=
    { app Δ := ↾fun p => p.1.comp p.2
      naturality := by
        intro Δ Δ' θ
        ext p
        exact (pathMap_comp (A.operator θ) p.1 p.2).symm }
  id_comp x y := by
    ext Δ p
    exact Quiver.Path.nil_comp p
  comp_id x y := by
    ext Δ p
    rfl
  assoc w x y z := by
    ext Δ p
    exact Quiver.Path.comp_assoc p.1 p.2.1 p.2.2

end SimplicialComputad

end SSet
