/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.AlgebraicTopology.SimplicialNerve
import Mathlib.CategoryTheory.Enriched.EnrichedCat
import Mathlib.CategoryTheory.PathCategory.Basic
import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.ComputadRepresentation

/-!
# The actual free simplicial category on a simplicial quiver

Objects are the supplied vertices. In each scalar degree the Hom objects
are genuine finite paths of supplied quiver arrows. Simplicial operators
act on every arrow of those same paths; identities are empty paths and
composition concatenates paths. All enriched laws are proved on these
actual maps, without a model structure or a comparison outcome input.

This is a label-preserving adapter to `SSet.SimplicialComputad`: the
canonical construction supplies the operators, evaluation and universal
property. The explicit path relabeling retains the existing path API on
the supplied vertex type instead of exposing the computad's label wrapper.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialQuiver

/-- Original vertex-indexed simplicial generating Hom objects. -/
structure Data (O : Type u) where
  /-- The actual simplicial object of generating arrows at the two supplied vertices. -/
  Hom : O → O → SSet.{u}

variable {O : Type u}

/-- A simplicial quiver is the canonical computad with singleton operator images. -/
def computad (Q : Data O) : SSet.SimplicialComputad.{u, u} O where
  generator n x y := (Q.Hom x y).obj n
  operator {n m} f {x y} a := SSet.SimplicialComputad.single ((Q.Hom x y).map f a)
  operator_id n {x y} a := by
    rw [(Q.Hom x y).map_id]
    rfl
  operator_comp {n m k} f g {x y} a := by
    rw [SSet.SimplicialComputad.pathMap_single, (Q.Hom x y).map_comp]
    rfl

/-- The actual generating quiver in one scalar degree. -/
@[instance_reducible]
def quiverAt (Q : Data O) (n : SimplexCategoryᵒᵖ) : Quiver O where
  Hom x y := (Q.Hom x y).obj n

/-- Every arrow in a free Hom is an actual finite original generating path. -/
def Path (Q : Data O) (n : SimplexCategoryᵒᵖ) (x y : O) : Type u :=
  @Quiver.Path O (quiverAt Q n) x y

/-- An original simplex operator acts on the generating arrows and keeps each original
vertex fixed. -/
def operator (Q : Data O) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    @Prefunctor O (quiverAt Q n) O (quiverAt Q m) :=
  @Prefunctor.mk O (quiverAt Q n) O (quiverAt Q m) (fun x => x)
    (fun {x y} a => (Q.Hom x y).map f a)

/-- The same simplex operator acts on the whole original generating path. -/
def mapPath (Q : Data O) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) {x y : O}
    (p : Path Q n x y) : Path Q m x y :=
  @Prefunctor.mapPath O (quiverAt Q n) O (quiverAt Q m) (operator Q f) x y p

/-- The unchanged generating arrows with the canonical computad's label wrapper. -/
def toComputadQuiver (Q : Data O) (n : SimplexCategoryᵒᵖ) :
    @Prefunctor O (quiverAt Q n)
      (SSet.SimplicialComputad.Vertex ((computad Q).generator n)) inferInstance :=
  @Prefunctor.mk O (quiverAt Q n)
    (SSet.SimplicialComputad.Vertex ((computad Q).generator n)) inferInstance
    (fun x => ⟨x⟩) (fun {_x _y} a => a)

/-- Read the same original label and arrow from the canonical computad quiver. -/
def fromComputadQuiver (Q : Data O) (n : SimplexCategoryᵒᵖ) :
    @Prefunctor (SSet.SimplicialComputad.Vertex ((computad Q).generator n)) inferInstance
      O (quiverAt Q n) :=
  @Prefunctor.mk (SSet.SimplicialComputad.Vertex ((computad Q).generator n)) inferInstance
    O (quiverAt Q n) (fun x => x.label) (fun {_x _y} a => a)

/-- Relabel an original path as the same path in the canonical computad. -/
def toNativePath (Q : Data O) (n : SimplexCategoryᵒᵖ) {x y : O} (p : Path Q n x y) :
    SSet.SimplicialComputad.Path ((computad Q).generator n) x y :=
  @Prefunctor.mapPath O (quiverAt Q n)
    (SSet.SimplicialComputad.Vertex ((computad Q).generator n)) inferInstance
    (toComputadQuiver Q n) x y p

/-- Read the original labels of a canonical computad path. -/
def fromNativePath (Q : Data O) (n : SimplexCategoryᵒᵖ) {x y : O}
    (p : SSet.SimplicialComputad.Path ((computad Q).generator n) x y) : Path Q n x y :=
  @Prefunctor.mapPath (SSet.SimplicialComputad.Vertex ((computad Q).generator n)) inferInstance
    O (quiverAt Q n) (fromComputadQuiver Q n) ⟨x⟩ ⟨y⟩ p

/-- Relabeling and reading back retain every arrow of the original path. -/
theorem fromNativePath_toNativePath (Q : Data O) (n : SimplexCategoryᵒᵖ)
    {x y : O} (p : Path Q n x y) : fromNativePath Q n (toNativePath Q n p) = p := by
  let := quiverAt Q n
  induction p with
  | nil => rfl
  | cons p a ih =>
    change Quiver.Path.cons (fromNativePath Q n (toNativePath Q n p)) a = p.cons a
    rw [ih]

/-- Reading and relabeling retain every arrow of the canonical path. -/
theorem toNativePath_fromNativePath (Q : Data O) (n : SimplexCategoryᵒᵖ)
    {x y : O} (p : SSet.SimplicialComputad.Path ((computad Q).generator n) x y) :
    toNativePath Q n (fromNativePath Q n p) = p := by
  suffices h : ∀ {a b : SSet.SimplicialComputad.Vertex ((computad Q).generator n)}
      (q : Quiver.Path a b), toNativePath Q n (fromNativePath Q n q) = q from h p
  intro a b q
  induction q with
  | nil => rfl
  | cons q g ih =>
    change Quiver.Path.cons (toNativePath Q n (fromNativePath Q n q)) g = q.cons g
    rw [ih]

/-- The native label relabeling is an actual equivalence on complete paths. -/
def nativePathEquiv (Q : Data O) (n : SimplexCategoryᵒᵖ) (x y : O) :
    Path Q n x y ≃ SSet.SimplicialComputad.Path ((computad Q).generator n) x y where
  toFun := toNativePath Q n
  invFun := fromNativePath Q n
  left_inv := fromNativePath_toNativePath Q n
  right_inv := toNativePath_fromNativePath Q n

/-- The label adapter preserves the actual full path composition. -/
theorem toNativePath_comp (Q : Data O) (n : SimplexCategoryᵒᵖ) {x y z : O}
    (p : Path Q n x y) (q : Path Q n y z) :
    toNativePath Q n (@Quiver.Path.comp O (quiverAt Q n) x y z p q) =
      (toNativePath Q n p).comp (toNativePath Q n q) :=
  @Prefunctor.mapPath_comp O (quiverAt Q n)
    (SSet.SimplicialComputad.Vertex ((computad Q).generator n)) inferInstance
    (toComputadQuiver Q n) x y p z q

/-- The label adapter commutes with every canonical computad operator. -/
theorem toNativePath_map (Q : Data O) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    {x y : O} (p : Path Q n x y) :
    toNativePath Q m (mapPath Q f p) = (computad Q).map f (toNativePath Q n p) := by
  let := quiverAt Q n
  induction p with
  | nil => rfl
  | @cons y z p a ih =>
    change Quiver.Path.cons (toNativePath Q m (mapPath Q f p)) ((Q.Hom y z).map f a) =
      Quiver.Path.cons ((computad Q).map f (toNativePath Q n p)) ((Q.Hom y z).map f a)
    rw [ih]

/-- The identity operator fixes each full original path. -/
theorem mapPath_id (Q : Data O) (n : SimplexCategoryᵒᵖ) {x y : O} (p : Path Q n x y) :
    mapPath Q (𝟙 n) p = p := by
  apply (nativePathEquiv Q n x y).injective
  exact (toNativePath_map Q (𝟙 n) p).trans ((computad Q).map_id n (toNativePath Q n p))

/-- Composition of original simplex operators has the same action on every generating path. -/
theorem mapPath_comp (Q : Data O) {n m k : SimplexCategoryᵒᵖ} (f : n ⟶ m) (g : m ⟶ k)
    {x y : O} (p : Path Q n x y) : mapPath Q (f ≫ g) p = mapPath Q g (mapPath Q f p) := by
  apply (nativePathEquiv Q k x y).injective
  change toNativePath Q k (mapPath Q (f ≫ g) p) = toNativePath Q k (mapPath Q g (mapPath Q f p))
  rw [toNativePath_map, (computad Q).map_comp, toNativePath_map, toNativePath_map]

/-- The actual free simplicial Hom between the supplied individual original vertices. -/
def freeHom (Q : Data O) (x y : O) : SSet.{u} where
  obj n := Path Q n x y
  map f := ↾fun p => mapPath Q f p
  map_id n := by
    ext p
    exact mapPath_id Q n p
  map_comp f g := by
    ext p
    exact mapPath_comp Q f g p

/-- The original free Hom is the canonical computad Hom with only its labels unwrapped. -/
def freeHomIso (Q : Data O) (x y : O) : freeHom Q x y ≅ (computad Q).hom x y where
  hom :=
    { app n := ↾toNativePath Q n
      naturality := by
        intro n m f
        ext p
        exact toNativePath_map Q f p }
  inv :=
    { app n := ↾fromNativePath Q n
      naturality := by
        intro n m f
        ext p
        change SSet.SimplicialComputad.Path ((computad Q).generator n) x y at p
        apply (nativePathEquiv Q m x y).injective
        change toNativePath Q m (fromNativePath Q m ((computad Q).map f p)) =
          toNativePath Q m (mapPath Q f (fromNativePath Q n p))
        rw [toNativePath_map, toNativePath_fromNativePath, toNativePath_fromNativePath] }
  hom_inv_id := by
    ext n p
    exact fromNativePath_toNativePath Q n p
  inv_hom_id := by
    ext n p
    exact toNativePath_fromNativePath Q n p

/-- The actual free identity is the empty original path in every scalar degree. -/
def freeId (Q : Data O) (x : O) : 𝟙_ SSet.{u} ⟶ freeHom Q x x where
  app n := ↾fun _ => @Quiver.Path.nil O (quiverAt Q n) x
  naturality n m f := by
    ext p
    rfl

/-- The actual free composition concatenates the two original finite paths. -/
def freeComp (Q : Data O) (x y z : O) : freeHom Q x y ⊗ freeHom Q y z ⟶ freeHom Q x z where
  app n := ↾fun p => @Quiver.Path.comp O (quiverAt Q n) x y z p.1 p.2
  naturality n m f := by
    ext p
    exact (@Prefunctor.mapPath_comp O (quiverAt Q n) O (quiverAt Q m) (operator Q f) x y p.1
      z p.2).symm

/-- The complete free enriched category structure on the unchanged original vertex type. -/
@[instance_reducible]
def freeEnrichment (Q : Data O) : EnrichedCategory SSet.{u} O where
  Hom := freeHom Q
  id := freeId Q
  comp := freeComp Q
  id_comp x y := by
    ext n p
    let : Quiver O := quiverAt Q n
    exact Quiver.Path.nil_comp p
  comp_id x y := by
    ext n p
    let : Quiver O := quiverAt Q n
    exact Quiver.Path.comp_nil p
  assoc w x y z := by
    ext n p
    let : Quiver O := quiverAt Q n
    exact Quiver.Path.comp_assoc p.1 p.2.1 p.2.2

/-- Bundle the same actual free enriched category, with no quotient or replacement of
original objects. -/
def free (Q : Data O) : EnrichedCat SSet.{u} := by
  letI : EnrichedCategory SSet.{u} O := freeEnrichment Q
  exact EnrichedCat.of SSet.{u} O

/-- The actual enriched label adapter to the canonical computad construction. -/
def toComputad (Q : Data O) : EnrichedFunctor SSet.{u} (free Q) (computad Q).Object where
  obj x := ⟨x⟩
  map x y := (freeHomIso Q x y).hom
  map_id x := by
    ext n p
    rfl
  map_comp x y z := by
    ext n p
    exact toNativePath_comp Q n p.1 p.2

/-- The inverse enriched label adapter retains the same original objects and paths. -/
def fromComputad (Q : Data O) : EnrichedFunctor SSet.{u} (computad Q).Object (free Q) where
  obj x := x.label
  map x y := (freeHomIso Q x.label y.label).inv
  map_id x := by
    ext n p
    rfl
  map_comp x y z := by
    ext n p
    change SSet.SimplicialComputad.Path ((computad Q).generator n) x.label y.label ×
      SSet.SimplicialComputad.Path ((computad Q).generator n) y.label z.label at p
    apply (nativePathEquiv Q n x.label z.label).injective
    change toNativePath Q n (fromNativePath Q n (p.1.comp p.2)) =
      toNativePath Q n (@Quiver.Path.comp O (quiverAt Q n) x.label y.label z.label
        (fromNativePath Q n p.1) (fromNativePath Q n p.2))
    rw [toNativePath_comp, toNativePath_fromNativePath, toNativePath_fromNativePath,
      toNativePath_fromNativePath]

/-- A specified generating arrow is the same length-one original free path. -/
def generator (Q : Data O) (x y : O) : Q.Hom x y ⟶ freeHom Q x y where
  app n := ↾fun a => @Quiver.Hom.toPath O (quiverAt Q n) x y a
  naturality n m f := by
    ext a
    rfl

/-- Length of the actual original path in its specified generating scalar quiver. -/
def pathLength (Q : Data O) (n : SimplexCategoryᵒᵖ) {x y : O} (p : Path Q n x y) : ℕ :=
  @Quiver.Path.length O (quiverAt Q n) x y p

/-- The free generator retains exactly one supplied original arrow. -/
theorem generator_length (Q : Data O) (n : SimplexCategoryᵒᵖ) (x y : O) (a : (Q.Hom x y).obj n) :
    pathLength Q n ((generator Q x y).app n a) = 1 := rfl

end CategoryTheory.SimplicialQuiver
