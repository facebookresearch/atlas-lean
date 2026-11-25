/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedArtinAtlasModels
public import MathlibExt.AlgebraicTopology.FullEnhancedSubcategory

/-!
# Actual derived open substacks and local geometricity

A derived affine open retains all mapping simplices whose vertices have
ordinary pi-zero scheme image in the chosen actual open. The open is in
Spec pi-zero(QA), the actual source of the derived affine mapping functor.
This permits nonaffine opens such as a punctured affine plane.

An open substack is tested after every actual derived affine family by
the native homotopy fibre and its comparison to this open functor, with
the projection fixed. Local geometricity permits an open cover with
different finite Artin levels; it imposes no single global level bound.
The cover condition is joint surjectivity on the `π₀`-schemes of all
affine families, as for étale covers.

References: HAG II, Part 2, §2.2; Toën--Vaquié,
arXiv:math/0503269v5, §2.1 and Theorem3.6.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedOpenSubstacks

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedEtaleStackModels
open MathlibExt.AlgebraicGeometry.DerivedStackFibreModels
open MathlibExt.AlgebraicGeometry.DerivedArtinAtlasModels
open scoped Simplicial

universe u
variable {k : Type u} [CommRing k]

/-- A lifted affine vertex is its actual simplicial algebra map out of QA. -/
def affineVertexMap (Q : AlgebraReplacementFunctor k) (A B : SAlg k)
    (x : ((affineMapping k Q A).obj B) _⦋0⦌) : Q.functor.obj A ⟶ B :=
  (SimplicialCategory.homEquiv' (Q.functor.obj A) B).symm x.down

/-- Target-algebra reindexing is the literal composition of algebra maps. -/
theorem affineVertexMap_map (Q : AlgebraReplacementFunctor k) (A : SAlg k)
    {B C : SAlg k} (f : B ⟶ C) (x : ((affineMapping k Q A).obj B) _⦋0⦌) :
    affineVertexMap Q A C (((affineMapping k Q A).map f).app (op ⦋0⦌) x) =
      affineVertexMap Q A B x ≫ f := rfl

/-- The actual ordinary scheme image determines membership in the specified open. -/
def IsInAffineOpen (Q : AlgebraReplacementFunctor k) (A B : SAlg k)
    (U : (piZeroScheme (Q.functor.obj A)).Opens)
    (x : ((affineMapping k Q A).obj B) _⦋0⦌) : Prop :=
  Set.range (piZeroSchemeMap (affineVertexMap Q A B x)) ⊆ U

/-- The pi-zero scheme map preserves the actual contravariant composition. -/
theorem piZeroSchemeMap_comp {A B C : SAlg k} (f : A ⟶ B) (g : B ⟶ C) :
    piZeroSchemeMap (f ≫ g) = piZeroSchemeMap g ≫ piZeroSchemeMap f := by
  unfold piZeroSchemeMap piZeroMap
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    _root_.AlgebraicGeometry.Spec.map_comp]

/-- Further affine base change preserves the same actual open-image test. -/
theorem isInAffineOpen_map (Q : AlgebraReplacementFunctor k) (A : SAlg k)
    {B C : SAlg k} (f : B ⟶ C) (U : (piZeroScheme (Q.functor.obj A)).Opens)
    (x : ((affineMapping k Q A).obj B) _⦋0⦌) (hx : IsInAffineOpen Q A B U x) :
    IsInAffineOpen Q A C U (((affineMapping k Q A).map f).app (op ⦋0⦌) x) := by
  rintro _ ⟨p, rfl⟩
  rw [affineVertexMap_map, piZeroSchemeMap_comp,
    _root_.AlgebraicGeometry.Scheme.Hom.comp_apply]
  exact hx ⟨piZeroSchemeMap f p, rfl⟩

/-- The literal full subcomplex retains every simplex lying in the chosen affine open. -/
def affineOpen (Q : AlgebraReplacementFunctor k) (A : SAlg k)
    (U : (piZeroScheme (Q.functor.obj A)).Opens) (B : SAlg k) : SSet.{u + 1} :=
  (((affineMapping k Q A).obj B).fullEnhancedSubcategory (IsInAffineOpen Q A B U)).toSSet

/-- The actual scalar-induced map between these open mapping spaces. -/
def affineOpenMap (Q : AlgebraReplacementFunctor k) (A : SAlg k)
    (U : (piZeroScheme (Q.functor.obj A)).Opens) {B C : SAlg k} (f : B ⟶ C) :
    affineOpen Q A U B ⟶ affineOpen Q A U C :=
  SSet.Subcomplex.lift
    ((((affineMapping k Q A).obj B).fullEnhancedSubcategory (IsInAffineOpen Q A B U)).ι ≫
      ((affineMapping k Q A).map f)) (by
    rw [SSet.range_le_fullEnhancedSubcategory_iff]
    intro x
    exact isInAffineOpen_map Q A f U x.val
      ((SSet.mem_fullEnhancedSubcategory_obj_zero_iff _ x.val).mp x.property))

/-- The genuine derived affine-open functor, including every restriction map. -/
def affineOpenFunctor (Q : AlgebraReplacementFunctor k) (A : SAlg k)
    (U : (piZeroScheme (Q.functor.obj A)).Opens) : Prestack k where
  obj := affineOpen Q A U
  map := affineOpenMap Q A U
  map_id B := by
    ext n x
    apply Subtype.ext
    exact congrArg (fun f => (f.app n) x.val)
      (CategoryTheory.Functor.map_id (affineMapping k Q A) B)
  map_comp f g := by
    ext n x
    apply Subtype.ext
    exact congrArg (fun f => (f.app n) x.val)
      (CategoryTheory.Functor.map_comp (affineMapping k Q A) f g)

/-- The native inclusion fixes the map of each actual open family to the ambient affine. -/
def affineOpenInclusion (Q : AlgebraReplacementFunctor k) (A : SAlg k)
    (U : (piZeroScheme (Q.functor.obj A)).Opens) :
    affineOpenFunctor Q A U ⟶ affineMapping k Q A where
  app B := (((affineMapping k Q A).obj B).fullEnhancedSubcategory (IsInAffineOpen Q A B U)).ι
  naturality _ _ _ := by ext n x; rfl

/-- Open representability allows general scheme opens and fixes every fibre projection. -/
def IsOpenImmersion {Q : AlgebraReplacementFunctor k} {F G : DerivedStack Q}
    (f : StackMap F G) : Prop :=
  ∀ (A : SAlg k) (M : AffineStackModel Q A) (x : StackMap M.stack G)
    (P : NaturalPathModel G), ∃ (V : FibreStackModel P f x)
    (U : (piZeroScheme (Q.functor.obj A)).Opens)
    (a : affineOpenFunctor Q A U ⟶ V.stack.functor),
    (∀ B : SAlg k, WeakEquivalence (a.app B)) ∧
      a ≫ second V = affineOpenInclusion Q A U ≫ M.augmentation

/-- Local geometricity: an open cover of `F` by derived Artin stacks, possibly of different finite
Artin levels. The cover condition is tested on every affine family `x` of `F` (an augmented derived
affine `M` of `A` with a map to `F`): every point `p` of the `π₀`-scheme of `A` lies in the open `U`
by which some `G i` restricts to `x`. This is the joint surjectivity on `π₀`-schemes used for étale
covers (`IsEtaleCover`), applied to open immersions, so the family is a Zariski cover.

Over the zero base ring every `π₀`-scheme is empty, so the empty family covers. This is correct:
there the empty presieve covers every algebra, so hyperdescent makes every derived stack
contractible, hence affine, and every stack is locally geometric. -/
def IsLocallyGeometric {Q : AlgebraReplacementFunctor k} (F : DerivedStack Q) : Prop :=
  ∃ (I : Type (u + 1)) (G : I → DerivedStack Q) (a : ∀ i, StackMap (G i) F),
    (∀ i, IsDerivedArtin (G i) ∧ IsOpenImmersion (a i)) ∧
      ∀ (A : SAlg k) (M : AffineStackModel Q A) (x : StackMap M.stack F)
        (P : NaturalPathModel F) (p : piZeroScheme (Q.functor.obj A)),
        ∃ (i : I) (V : FibreStackModel P (a i) x) (U : (piZeroScheme (Q.functor.obj A)).Opens)
          (b : affineOpenFunctor Q A U ⟶ V.stack.functor),
          (∀ B : SAlg k, WeakEquivalence (b.app B)) ∧
            b ≫ second V = affineOpenInclusion Q A U ≫ M.augmentation ∧ p ∈ U

end MathlibExt.AlgebraicGeometry.DerivedOpenSubstacks
