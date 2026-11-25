/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The algebraic-stack, representable-diagonal and atlas definitions follow
AxiomMath/Stacks at c496df0d9beea9deaeabcea8492605f9a0a2313b:
StacksFrontier/AlgebraicGeometry/Stacks/AlgebraicStack.lean,
StacksFrontier/AlgebraicGeometry/Stacks/RepresentableDiagonal.lean,
StacksFrontier/AlgebraicGeometry/Spaces/Basic.lean and Smooth.lean.
Public source: https://github.com/AxiomMath/Stacks.
The source is licensed under Apache 2.0 and has no individual author or
copyright notice in those files. Modifications: the stacks are the fppf
stacks in groupoids of `FppfStacks`, isomorphism presheaves are Mathlib's
`Pseudofunctor.presheafHom`, algebraic spaces are modelled by chosen étale
presentations, and 2-fibre products of categories are Mathlib's categorical
pullbacks.
-/
module

public import MathlibExt.AlgebraicGeometry.EtaleSpacePresentations
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Bicategory.Modification.Pseudo
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import Mathlib.CategoryTheory.Sites.Descent.IsPrestack

/-!
# Algebraic spaces over a scheme, algebraic stacks and Deligne–Mumford stacks

The stacks are the fppf stacks in groupoids over all schemes of
`MathlibExt.AlgebraicGeometry.FppfStacks` (and, for stacks over a base scheme `S`, fppf stacks in
groupoids on schemes over `S`). An algebraic space over a scheme `T` is modelled by the quotient
fppf sheaf of a chosen étale equivalence relation together with a structure map to `T`; every
algebraic space admits such a presentation (Stacks, Lemma 65.9.1).

* `HasRepresentableDiagonal`: for every scheme `T` and objects `x y` over `T`, the sheaf of
  isomorphisms `Isom(x, y)` on schemes over `T` is an algebraic space over `T`; this is equivalent
  to representability of the diagonal by algebraic spaces (Stacks, Lemma 94.10.11).
* `SmoothAtlas`, `EtaleAtlas`: a scheme `U` with an object `u` over `U` such that for every scheme
  `T` and object `y` over `T` the 2-fibre product `U ×_X T` is an algebraic space over `T` whose
  structure map is surjective and smooth (resp. étale). Properties of the structure map of an
  algebraic space are checked on the étale atlas of its presentation.
* `IsArtinStack`, `IsDeligneMumfordStack`: representable diagonal together with a smooth
  (resp. étale) atlas (Stacks, Definitions 94.12.1 and 94.12.2).

The file also provides the 2-fibre product of categories (`IsoFibre`), used pointwise for 2-fibre
products of stacks (`TwoFibreSquare`, `TwoFibreModel`), and the same notions for stacks over a base
scheme (`RelativeStack`).

## References

* [Stacks Project, Lemma 65.9.1 (Tag 0262)](https://stacks.math.columbia.edu/tag/0262)
* [Stacks Project, Section 67.5 (Tag 03MC)](https://stacks.math.columbia.edu/tag/03MC)
* [Stacks Project, Definition 67.37.1 (Tag 03ZC)](https://stacks.math.columbia.edu/tag/03ZC)
* [Stacks Project, Lemma 94.10.11 (Tag 045G)](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Definition 94.12.1 (Tag 026O)](https://stacks.math.columbia.edu/tag/026O)
* [Stacks Project, Definition 94.12.2 (Tag 03YO)](https://stacks.math.columbia.edu/tag/03YO)
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.GeneralStackGeometry

open CategoryTheory CategoryTheory.Limits Opposite
open FppfStacks EtaleSpacePresentations
open scoped Pseudofunctor.StrongTrans

universe u v w

section TwoFibre

variable {A : Type u} {B : Type v} {C : Type w}
  [Category A] [Category B] [Category C]

/-- The 2-fibre product of categories of functors `f : A ⥤ C` and `g : B ⥤ C`, the categorical
pullback: its objects are triples `(a, b, f a ≅ g b)` and its morphisms are pairs of morphisms
commuting with the comparison isomorphisms. Its projections are `Limits.CategoricalPullback.π₁` and
`π₂`, its 2-cell is the `CatCommSq` instance, and functors from a category `X` into it correspond
to pairs of functors `X ⥤ A`, `X ⥤ B` with a natural isomorphism between their composites with `f`
and `g` (`Limits.CategoricalPullback.functorEquiv`). -/
abbrev IsoFibre (f : A ⥤ C) (g : B ⥤ C) := Limits.CategoricalPullback f g

/-- The 2-fibre product of groupoids is a groupoid. -/
instance isoFibre_isGroupoid (f : A ⥤ C) (g : B ⥤ C)
    [IsGroupoid A] [IsGroupoid B] : IsGroupoid (IsoFibre f g) where
  all_isIso h := (Limits.CategoricalPullback.isIso_iff f g h).2 ⟨inferInstance, inferInstance⟩

end TwoFibre

/-- The fibre category of a stack over a scheme `T`. -/
abbrev Fibre (X : StackInGroupoids.{u}) (T : Scheme.{u}) :=
  X.toSchPseudofunctor.obj (.mk (op T))

/-- Pullback along a morphism of schemes `V ⟶ T`. -/
abbrev reindex (X : StackInGroupoids.{u}) {T V : Scheme.{u}} (a : V ⟶ T) :
    Fibre X T ⥤ Fibre X V :=
  (X.toSchPseudofunctor.map a.op.toLoc).toFunctor

/-- The component at a scheme `T` of a morphism of stacks. -/
abbrev component {X Y : StackInGroupoids.{u}} (f : StackInGroupoids.Hom X Y)
    (T : Scheme.{u}) : Fibre X T ⥤ Fibre Y T := (f.app (.mk (op T))).toFunctor

/-- The 2-fibre product over a scheme `T` of the components of two morphisms of stacks. -/
abbrev twoFibreAt {X Y Z : StackInGroupoids.{u}}
    (f : StackInGroupoids.Hom X Z) (g : StackInGroupoids.Hom Y Z) (T : Scheme.{u}) :=
  IsoFibre (component f T) (component g T)

/-- An invertible modification between two morphisms of stacks `p q : X ⟶ Y`: an isomorphism
from `p` to `q` in the category `Pseudofunctor.StrongTrans.homCategory` of strong transformations
between the underlying pseudofunctors and modifications. -/
abbrev TwoIso {X Y : StackInGroupoids.{u}} (p q : StackInGroupoids.Hom X Y) : Type (u + 1) :=
  @Iso (X.toSchPseudofunctor ⟶ Y.toSchPseudofunctor) _ p q

/-- The component over a scheme `T` of an invertible modification between morphisms of stacks. -/
def componentIso {X Y : StackInGroupoids.{u}} {p q : StackInGroupoids.Hom X Y} (e : TwoIso p q)
    (T : Scheme.{u}) : component p T ≅ component q T :=
  Cat.Hom.toNatIso
    { hom := e.hom.as.app (.mk (op T))
      inv := e.inv.as.app (.mk (op T))
      hom_inv_id := congrArg (fun m => m.as.app (.mk (op T))) e.hom_inv_id
      inv_hom_id := congrArg (fun m => m.as.app (.mk (op T))) e.inv_hom_id }

@[simp]
theorem componentIso_hom_app {X Y : StackInGroupoids.{u}} {p q : StackInGroupoids.Hom X Y}
    (e : TwoIso p q) (T : Scheme.{u}) (x : Fibre X T) :
    (componentIso e T).hom.app x = (e.hom.as.app (.mk (op T))).toNatTrans.app x := rfl

/-- A 2-commutative square of stacks: morphisms `fst : W ⟶ X` and `snd : W ⟶ Y` with an invertible
modification `fst ≫ f ≅ snd ≫ g`. -/
structure TwoFibreSquare {X Y Z : StackInGroupoids.{u}}
    (f : StackInGroupoids.Hom X Z) (g : StackInGroupoids.Hom Y Z) where
  /-- The apex of the square. -/
  apex : StackInGroupoids.{u}
  /-- The first leg. -/
  fst : StackInGroupoids.Hom apex X
  /-- The second leg. -/
  snd : StackInGroupoids.Hom apex Y
  /-- The invertible modification making the square 2-commute. -/
  commutes : TwoIso (Pseudofunctor.StrongTrans.vcomp fst f) (Pseudofunctor.StrongTrans.vcomp snd g)

/-- The functor from the fibre of the apex of a 2-commutative square to the 2-fibre product of
the fibres, induced by the legs of the square and its 2-cell. -/
def TwoFibreSquare.comparisonFunctor {X Y Z : StackInGroupoids.{u}}
    {f : StackInGroupoids.Hom X Z} {g : StackInGroupoids.Hom Y Z}
    (P : TwoFibreSquare f g) (T : Scheme.{u}) : Fibre P.apex T ⥤ twoFibreAt f g T :=
  (Limits.CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
    (component f T) (component g T) (Fibre P.apex T)).obj
      ⟨component P.fst T, component P.snd T, componentIso P.commutes T⟩

/-- The comparison functor followed by the first projection is the first leg. -/
theorem TwoFibreSquare.comparison_fst {X Y Z : StackInGroupoids.{u}}
    {f : StackInGroupoids.Hom X Z} {g : StackInGroupoids.Hom Y Z}
    (P : TwoFibreSquare f g) (T : Scheme.{u}) :
    P.comparisonFunctor T ⋙ Limits.CategoricalPullback.π₁ (component f T) (component g T) =
      component P.fst T := rfl

/-- The comparison functor followed by the second projection is the second leg. -/
theorem TwoFibreSquare.comparison_snd {X Y Z : StackInGroupoids.{u}}
    {f : StackInGroupoids.Hom X Z} {g : StackInGroupoids.Hom Y Z}
    (P : TwoFibreSquare f g) (T : Scheme.{u}) :
    P.comparisonFunctor T ⋙ Limits.CategoricalPullback.π₂ (component f T) (component g T) =
      component P.snd T := rfl

/-- The comparison functor sends an object to the comparison isomorphism given by the 2-cell. -/
@[simp]
theorem TwoFibreSquare.comparisonFunctor_obj_iso {X Y Z : StackInGroupoids.{u}}
    {f : StackInGroupoids.Hom X Z} {g : StackInGroupoids.Hom Y Z}
    (P : TwoFibreSquare f g) (T : Scheme.{u}) (w : Fibre P.apex T) :
    ((P.comparisonFunctor T).obj w).iso = (componentIso P.commutes T).app w := rfl

/-- A 2-fibre product of two morphisms of stacks: a 2-commutative square whose comparison functor
is an equivalence on the fibres over every scheme. -/
structure TwoFibreModel {X Y Z : StackInGroupoids.{u}}
    (f : StackInGroupoids.Hom X Z) (g : StackInGroupoids.Hom Y Z)
    extends TwoFibreSquare f g where
  comparison_equivalence : ∀ T : Scheme.{u},
    (toTwoFibreSquare.comparisonFunctor T).IsEquivalence

/-- An algebraic space over a scheme `T`, presented as the quotient sheaf of an étale equivalence
relation, together with its structure map to `T`. -/
structure AlgebraicSpaceOver (T : Scheme.{u}) where
  presentation : EtaleEquivalencePresentation.{u}
  structural : quotientSheaf presentation ⟶ represented.obj T

/-- The fppf sheaf underlying the algebraic space. -/
abbrev AlgebraicSpaceOver.sheaf {T : Scheme.{u}} (A : AlgebraicSpaceOver T) :=
  quotientSheaf A.presentation

/-- The algebraic space as a presheaf on schemes over `T`: its value on `V ⟶ T` is the set of
points of the space over `V` lying over that morphism. -/
def AlgebraicSpaceOver.relativePresheaf {T : Scheme.{u}} (A : AlgebraicSpaceOver T) :
    (Over T)ᵒᵖ ⥤ Type (u + 1) where
  obj V := {x : A.sheaf.obj.obj (op V.unop.left) //
    A.structural.hom.app (op V.unop.left) x = ULift.up V.unop.hom}
  map {V W} a := ↾fun x ↦ ⟨A.sheaf.obj.map a.unop.left.op x.val, by
    have h := ConcreteCategory.congr_hom
      (A.structural.hom.naturality a.unop.left.op) x.val
    change A.structural.hom.app (op W.unop.left)
      (A.sheaf.obj.map a.unop.left.op x.val) = ULift.up W.unop.hom
    change A.structural.hom.app (op W.unop.left)
      (A.sheaf.obj.map a.unop.left.op x.val) =
        (represented.obj T).obj.map a.unop.left.op
          (A.structural.hom.app (op V.unop.left) x.val) at h
    exact h.trans (by
      rw [x.property]
      change ULift.up (a.unop.left ≫ V.unop.hom) = ULift.up W.unop.hom
      exact congrArg ULift.up (Over.w a.unop))⟩
  map_id V := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact ConcreteCategory.congr_hom (A.sheaf.obj.map_id (op V.unop.left)) x.val
  map_comp a b := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact ConcreteCategory.congr_hom
      (A.sheaf.obj.map_comp a.unop.left.op b.unop.left.op) x.val

/-- A morphism of schemes `U ⟶ T` from the atlas of the presentation inducing the structure map.
It exists and is unique since the represented-sheaf functor is fully faithful. -/
structure AlgebraicSpaceOver.Chart {T : Scheme.{u}} (A : AlgebraicSpaceOver T) where
  map : A.presentation.U ⟶ T
  normalization : atlas A.presentation ≫ A.structural = represented.map map

/-- The algebraic space is smooth over `T`: smoothness can be checked on the étale atlas of the
presentation (Stacks, Definition 67.37.1). -/
def AlgebraicSpaceOver.IsSmooth {T : Scheme.{u}} (A : AlgebraicSpaceOver T) : Prop :=
  ∃ c : A.Chart, Smooth c.map

/-- The algebraic space is étale over `T`, checked on the étale atlas of the presentation. -/
def AlgebraicSpaceOver.IsEtale {T : Scheme.{u}} (A : AlgebraicSpaceOver T) : Prop :=
  ∃ c : A.Chart, Etale c.map

/-- The algebraic space is surjective over `T`, checked on the étale atlas of the presentation
(surjective on underlying points; Stacks, Section 67.5). This is weaker than being an epimorphism
of fppf sheaves (`AlgebraicSpaceOver.IsFppfLocallySurjective`) in general, and equivalent to it
for smooth structure maps. -/
def AlgebraicSpaceOver.IsSurjective {T : Scheme.{u}} (A : AlgebraicSpaceOver T) : Prop :=
  ∃ c : A.Chart, Surjective c.map

/-- The structure map is an epimorphism of fppf sheaves: points of `T` lift to the space fppf
locally. -/
abbrev AlgebraicSpaceOver.IsFppfLocallySurjective {T : Scheme.{u}} (A : AlgebraicSpaceOver T) :=
  Epi A.structural

/-- The presheaf `Isom(x, y)` on schemes over `T` (the presheaf of morphisms, all of which are
invertible since the fibres are groupoids). -/
abbrev isomPresheaf (X : StackInGroupoids.{u}) {T : Scheme.{u}} (x y : Fibre X T) :=
  X.toSchPseudofunctor.presheafHom x y ⋙ uliftFunctor.{u + 1, u}

/-- The values of `isomPresheaf` are the isomorphisms between the pullbacks. -/
def isomPresheafObjEquiv (X : StackInGroupoids.{u}) {T : Scheme.{u}}
    (x y : Fibre X T) (V : Over T) :
    ULift.{u + 1} ((reindex X V.hom).obj x ≅ (reindex X V.hom).obj y) ≃
      (isomPresheaf X x y).obj (op V) where
  toFun e := ULift.up e.down.hom
  invFun a := ULift.up (asIso a.down)
  left_inv e := by apply ULift.ext; apply Iso.ext; rfl
  right_inv a := rfl

/-- The diagonal is representable by algebraic spaces: for every scheme `T` and objects `x y`
over `T`, the presheaf `Isom(x, y)` is an algebraic space over `T` (Stacks, Lemma 94.10.11). -/
def HasRepresentableDiagonal (X : StackInGroupoids.{u}) : Prop :=
  ∀ (T : Scheme.{u}) (x y : Fibre X T), ∃ A : AlgebraicSpaceOver T,
    Nonempty (A.relativePresheaf ≅ isomPresheaf X x y)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The presheaf of comparison arrows between two points `x` over `U` and `y` over `T` of a
`Cat`-valued pseudofunctor, on objects over `T`: its value on `V ⟶ T` consists of a morphism
`a : V ⟶ U` and a morphism `a^* x ⟶ (V ⟶ T)^* y` in the fibre over `V`. When the fibres are
groupoids (as for stacks in groupoids) these morphisms are isomorphisms and this presheaf is the
2-fibre product `U ×_F T`; in general it is a comma construction. -/
def pointComparisonPresheaf {D : Type (u + 1)} [Category.{u} D]
    (F : Pseudofunctor (LocallyDiscrete Dᵒᵖ) Cat.{u, u + 1}) {U T : D}
    (x : F.obj (.mk (op U))) (y : F.obj (.mk (op T))) : (Over T)ᵒᵖ ⥤ Type u where
  obj V := Σ a : V.unop.left ⟶ U,
    (F.map a.op.toLoc).toFunctor.obj x ⟶ (F.map V.unop.hom.op.toLoc).toFunctor.obj y
  map {V W} f := ↾fun z ↦ ⟨f.unop.left ≫ z.1,
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := F)
      z.2 f.unop.left (f.unop.left ≫ z.1) W.unop.hom rfl (Over.w f.unop)⟩
  map_id V := by
    apply ConcreteCategory.hom_ext
    rintro ⟨a, phi⟩
    dsimp
    let pair (q : {b : V.unop.left ⟶ U // (𝟙 V.unop.left) ≫ a = b}) :
        Σ b : V.unop.left ⟶ U,
          (F.map b.op.toLoc).toFunctor.obj x ⟶
            (F.map V.unop.hom.op.toLoc).toFunctor.obj y :=
      ⟨q.val, Pseudofunctor.LocallyDiscreteOpToCat.pullHom phi (𝟙 _)
        q.val V.unop.hom q.property (Category.id_comp _)⟩
    have harg :
        (⟨(𝟙 V.unop.left) ≫ a, rfl⟩ :
          {b : V.unop.left ⟶ U // (𝟙 V.unop.left) ≫ a = b}) =
        ⟨a, Category.id_comp a⟩ := Subtype.ext (Category.id_comp a)
    exact (congrArg pair harg).trans
      (congrArg (Sigma.mk a) (Pseudofunctor.LocallyDiscreteOpToCat.pullHom_id phi))
  map_comp {V W Z} f g := by
    apply ConcreteCategory.hom_ext
    rintro ⟨a, phi⟩
    dsimp
    simp only [Pseudofunctor.LocallyDiscreteOpToCat.pullHom_pullHom]
    let pair (q : {b : Z.unop.left ⟶ U // (g.unop.left ≫ f.unop.left) ≫ a = b}) :
        Σ b : Z.unop.left ⟶ U,
          (F.map b.op.toLoc).toFunctor.obj x ⟶
            (F.map Z.unop.hom.op.toLoc).toFunctor.obj y :=
      ⟨q.val, Pseudofunctor.LocallyDiscreteOpToCat.pullHom phi
        (g.unop.left ≫ f.unop.left) q.val Z.unop.hom q.property (Over.w (f ≫ g).unop)⟩
    have harg :
        (⟨(g.unop.left ≫ f.unop.left) ≫ a, rfl⟩ :
          {b : Z.unop.left ⟶ U // (g.unop.left ≫ f.unop.left) ≫ a = b}) =
        ⟨g.unop.left ≫ f.unop.left ≫ a, Category.assoc _ _ _⟩ :=
      Subtype.ext (Category.assoc _ _ _)
    exact congrArg pair harg

/-- The 2-fibre product `U ×_X T` of two points of a stack in groupoids, as a presheaf on schemes
over `T`. -/
abbrev schemePointFibrePresheaf (X : StackInGroupoids.{u}) {U T : Scheme.{u}}
    (x : Fibre X U) (y : Fibre X T) :=
  pointComparisonPresheaf X.toSchPseudofunctor x y

/-- `schemePointFibrePresheaf`, lifted to the universe of the quotient sheaves. -/
abbrev atlasFibrePresheaf (X : StackInGroupoids.{u}) {U T : Scheme.{u}}
    (x : Fibre X U) (y : Fibre X T) :=
  schemePointFibrePresheaf X x y ⋙ uliftFunctor.{u + 1, u}

/-- A scheme `U` with an object `point` over `U` such that for every scheme `T` and object `y`
over `T` the 2-fibre product `U ×_X T` is an algebraic space over `T` whose structure map is
surjective. -/
structure Atlas (X : StackInGroupoids.{u}) where
  U : Scheme.{u}
  point : Fibre X U
  baseChange : ∀ (T : Scheme.{u}) (_y : Fibre X T), AlgebraicSpaceOver T
  comparison : ∀ (T : Scheme.{u}) (y : Fibre X T),
    (baseChange T y).relativePresheaf ≅ atlasFibrePresheaf X point y
  surjective : ∀ (T : Scheme.{u}) (y : Fibre X T), (baseChange T y).IsSurjective

/-- A smooth atlas: an atlas whose base changes are smooth over `T`. -/
structure SmoothAtlas (X : StackInGroupoids.{u}) extends Atlas X where
  smooth : ∀ (T : Scheme.{u}) (y : Fibre X T), (baseChange T y).IsSmooth

/-- An étale atlas: an atlas whose base changes are étale over `T`. -/
structure EtaleAtlas (X : StackInGroupoids.{u}) extends Atlas X where
  etale : ∀ (T : Scheme.{u}) (y : Fibre X T), (baseChange T y).IsEtale

/-- An étale atlas is a smooth atlas. -/
def EtaleAtlas.toSmoothAtlas {X : StackInGroupoids.{u}} (a : EtaleAtlas X) : SmoothAtlas X where
  toAtlas := a.toAtlas
  smooth T y := by
    obtain ⟨c, hc⟩ := a.etale T y
    exact ⟨c, by have := hc; infer_instance⟩

/-- An algebraic (Artin) stack: representable diagonal and a smooth atlas (Stacks,
Definition 94.12.1). -/
def IsArtinStack (X : StackInGroupoids.{u}) : Prop :=
  HasRepresentableDiagonal X ∧ Nonempty (SmoothAtlas X)

/-- A Deligne–Mumford stack: representable diagonal and an étale atlas (Stacks,
Definition 94.12.2). -/
def IsDeligneMumfordStack (X : StackInGroupoids.{u}) : Prop :=
  HasRepresentableDiagonal X ∧ Nonempty (EtaleAtlas X)

/-- A Deligne–Mumford stack is an algebraic stack. -/
theorem isArtinStack_of_isDeligneMumfordStack {X : StackInGroupoids.{u}}
    (h : IsDeligneMumfordStack X) : IsArtinStack X :=
  ⟨h.1, h.2.map EtaleAtlas.toSmoothAtlas⟩

/-! ## Stacks over a base scheme

Stacks in groupoids on schemes over a base scheme `S`, with the same notions of representable
diagonal and atlas; algebraic spaces over `T ⟶ S` are those over `T`, through the equivalence
between objects over `T` in `Over S` and schemes over `T`.
-/

/-- An fppf stack in groupoids on schemes over `S`. -/
structure RelativeStack (S : Scheme.{u}) where
  toPseudofunctor : Pseudofunctor (LocallyDiscrete (Over S)ᵒᵖ) Cat.{u, u + 1}
  isGroupoid : ∀ T : Over S, IsGroupoid (toPseudofunctor.obj (.mk (op T)))
  isStack : toPseudofunctor.IsStack (Scheme.fppfTopology.over S)

attribute [instance] RelativeStack.isGroupoid RelativeStack.isStack

/-- The stack over `S` given by a pseudofunctor with groupoid fibres satisfying the stack
condition. -/
def RelativeStack.of (S : Scheme.{u})
    (F : Pseudofunctor (LocallyDiscrete (Over S)ᵒᵖ) Cat.{u, u + 1})
    (groupoids : ∀ T : Over S, IsGroupoid (F.obj (.mk (op T))))
    (stack : F.IsStack (Scheme.fppfTopology.over S)) : RelativeStack S :=
  ⟨F, groupoids, stack⟩

@[simp]
theorem RelativeStack.of_toPseudofunctor (S : Scheme.{u})
    (F : Pseudofunctor (LocallyDiscrete (Over S)ᵒᵖ) Cat.{u, u + 1})
    (groupoids : ∀ T : Over S, IsGroupoid (F.obj (.mk (op T))))
    (stack : F.IsStack (Scheme.fppfTopology.over S)) :
    (RelativeStack.of S F groupoids stack).toPseudofunctor = F := rfl

/-- The fibre category over a scheme over `S`. -/
abbrev RelativeStack.Fibre {S : Scheme.{u}} (X : RelativeStack S) (T : Over S) :=
  X.toPseudofunctor.obj (.mk (op T))

/-- An algebraic space over `T.left` as a presheaf on objects over `T` in `Over S`. -/
abbrev relativeSpacePresheaf {S : Scheme.{u}} (T : Over S)
    (A : AlgebraicSpaceOver T.left) := T.iteratedSliceForward.op ⋙ A.relativePresheaf

/-- The diagonal of a stack over `S` is representable by algebraic spaces. -/
def RelativeStack.HasRepresentableDiagonal {S : Scheme.{u}} (X : RelativeStack S) : Prop :=
  ∀ (T : Over S) (x y : X.Fibre T), ∃ A : AlgebraicSpaceOver T.left,
    Nonempty (relativeSpacePresheaf T A ≅
      X.toPseudofunctor.presheafHom x y ⋙ uliftFunctor.{u + 1, u})

/-- An atlas of a stack over `S`; see `Atlas`. -/
structure RelativeStack.Atlas {S : Scheme.{u}} (X : RelativeStack S) where
  U : Over S
  point : X.Fibre U
  baseChange : ∀ (T : Over S) (_y : X.Fibre T), AlgebraicSpaceOver T.left
  comparison : ∀ (T : Over S) (y : X.Fibre T),
    relativeSpacePresheaf T (baseChange T y) ≅
      pointComparisonPresheaf X.toPseudofunctor point y ⋙ uliftFunctor.{u + 1, u}
  surjective : ∀ (T : Over S) (y : X.Fibre T), (baseChange T y).IsSurjective

/-- A smooth atlas of a stack over `S`. -/
structure RelativeStack.SmoothAtlas {S : Scheme.{u}} (X : RelativeStack S)
    extends X.Atlas where
  smooth : ∀ (T : Over S) (y : X.Fibre T), (baseChange T y).IsSmooth

/-- An étale atlas of a stack over `S`. -/
structure RelativeStack.EtaleAtlas {S : Scheme.{u}} (X : RelativeStack S)
    extends X.Atlas where
  etale : ∀ (T : Over S) (y : X.Fibre T), (baseChange T y).IsEtale

/-- A stack over `S` is algebraic (Artin): representable diagonal and a smooth atlas. -/
def RelativeStack.IsArtinStack {S : Scheme.{u}} (X : RelativeStack S) : Prop :=
  X.HasRepresentableDiagonal ∧ Nonempty X.SmoothAtlas

/-- A stack over `S` is Deligne–Mumford: representable diagonal and an étale atlas. -/
def RelativeStack.IsDeligneMumfordStack {S : Scheme.{u}} (X : RelativeStack S) : Prop :=
  X.HasRepresentableDiagonal ∧ Nonempty X.EtaleAtlas

end AlgebraicGeometry.GeneralStackGeometry
