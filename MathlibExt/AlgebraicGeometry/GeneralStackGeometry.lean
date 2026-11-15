/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The algebraic-stack, representable-diagonal and atlas contracts follow
AxiomMath/Stacks at c496df0d9beea9deaeabcea8492605f9a0a2313b:
StacksFrontier/AlgebraicGeometry/Stacks/AlgebraicStack.lean,
StacksFrontier/AlgebraicGeometry/Stacks/RepresentableDiagonal.lean,
StacksFrontier/AlgebraicGeometry/Spaces/Basic.lean and Smooth.lean.
Public source: https://github.com/AxiomMath/Stacks.
The source is licensed under Apache 2.0 and has no individual author or
copyright notice in those files. Modification notice: use the existing
actual scheme-pseudofunctor stack carrier, Mathlib's actual morphism
presheaf, and an explicit chosen étale-presentation model of algebraic
spaces. The actual pointwise 2-fibre category is the isomorphism part of
Mathlib's comma category; no Axiom package import or new existence
request is introduced.
-/
module

public import MathlibExt.AlgebraicGeometry.EtaleSpacePresentations
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Comma.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Sites.Descent.IsPrestack

/-!
# General algebraic-stack and actual 2-fibre task contracts

The carrier is the existing fppf stack in groupoids on all schemes. An
algebraic space is modelled by its actual quotient fppf sheaf with a
chosen étale equivalence presentation. Such presentations and their
quotient algebraicity are complete public Axiom mathematics (including
`Spaces/QuotientSheafPresentationUnconditional.lean`); choosing a
presentation is not a restriction to a special class of algebraic spaces.
The full source comparison/provider closure is tracked separately.

The diagonal uses actual sheaves of fibre morphisms, which are
isomorphisms because the fibres are groupoids. Atlas base changes use
the actual scheme arrows and actual fibre isomorphisms, with the native
pseudofunctor coherence in every restriction map. Smoothness and étaleness
are checked on actual scheme charts, and surjectivity is the actual
epimorphism of fppf sheaves. These contracts do not assert an atlas or
algebraicity for an arbitrary stack.

Sources: Stacks Project, Tags 025Y, 026O, 03ZC, 045G and 03YO;
the completed Axiom sources quoted above. The source's generic stack and
2-fibre results are not re-requested as Wanted items.
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.GeneralStackGeometry

open CategoryTheory CategoryTheory.Limits Opposite
open FppfStacks EtaleSpacePresentations

universe u v w

section TwoFibre

variable {A : Type u} {B : Type v} {C : Type w}
  [Category A] [Category B] [Category C]

/-- The actual 2-fibre category: objects are `(a,b,f(a) ≅ g(b))`, and
morphisms are actual pairs commuting with the comparison isomorphism. -/
abbrev IsoFibre (f : A ⥤ C) (g : B ⥤ C) :=
  (show ObjectProperty (Comma f g) from fun q ↦ IsIso q.hom).FullSubcategory

/-- The actual 2-fibre category of groupoids is itself a groupoid;
inverses are the literal inverses of both component arrows. -/
instance isoFibre_isGroupoid (f : A ⥤ C) (g : B ⥤ C)
    [IsGroupoid A] [IsGroupoid B] : IsGroupoid (IsoFibre f g) where
  all_isIso h := by
    let k := ObjectProperty.homMk (P := fun q : Comma f g ↦ IsIso q.hom)
      (X := _) (Y := _)
      { left := inv h.hom.left
        right := inv h.hom.right
        w := by
          apply (cancel_epi (f.map h.hom.left)).mp
          simp only [← Category.assoc, ← Functor.map_comp, IsIso.hom_inv_id]
          rw [h.hom.w]
          simp [Category.assoc] }
    exact ⟨⟨k, by
      apply ObjectProperty.hom_ext
      apply Comma.hom_ext <;> simp [k], by
      apply ObjectProperty.hom_ext
      apply Comma.hom_ext <;> simp [k]⟩⟩

/-- The literal first projection from the actual isomorphism-comma category. -/
@[implicit_reducible]
def isoFibreFst (f : A ⥤ C) (g : B ⥤ C) : IsoFibre f g ⥤ A :=
  (show ObjectProperty (Comma f g) from fun q ↦ IsIso q.hom).ι ⋙ Comma.fst f g

/-- The literal second projection from the same category. -/
@[implicit_reducible]
def isoFibreSnd (f : A ⥤ C) (g : B ⥤ C) : IsoFibre f g ⥤ B :=
  (show ObjectProperty (Comma f g) from fun q ↦ IsIso q.hom).ι ⋙ Comma.snd f g

/-- The actual invertible 2-cell retained by a 2-fibre product. -/
def isoFibreComparison (f : A ⥤ C) (g : B ⥤ C) :
    isoFibreFst f g ⋙ f ≅ isoFibreSnd f g ⋙ g :=
  NatIso.ofComponents (fun q : IsoFibre f g ↦ by
    change f.obj q.obj.left ≅ g.obj q.obj.right
    exact @asIso _ _ _ _ q.obj.hom q.property) (by
      intro p q h
      change f.map h.hom.left ≫ q.obj.hom = p.obj.hom ≫ g.map h.hom.right
      exact h.hom.w)

/-- A normalized actual cone induces its literal functor into the 2-fibre category. -/
def isoFibreLift {D : Type*} [Category D] (f : A ⥤ C) (g : B ⥤ C)
    (p : D ⥤ A) (q : D ⥤ B) (e : p ⋙ f ≅ q ⋙ g) : D ⥤ IsoFibre f g where
  obj d := ⟨⟨p.obj d, q.obj d, e.hom.app d⟩, by dsimp; infer_instance⟩
  map h := ObjectProperty.homMk ⟨p.map h, q.map h, e.hom.naturality h⟩
  map_id d := by
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext <;> simp
  map_comp h k := by
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext <;> simp

@[simp]
theorem isoFibreLift_comparison {D : Type*} [Category D] (f : A ⥤ C) (g : B ⥤ C)
    (p : D ⥤ A) (q : D ⥤ B) (e : p ⋙ f ≅ q ⋙ g) (d : D) :
    ((isoFibreLift f g p q e).obj d).obj.hom = e.hom.app d := rfl

end TwoFibre

/-- The actual fibre category of the specified fppf stack. -/
abbrev Fibre (X : StackInGroupoids.{u}) (T : Scheme.{u}) :=
  X.toSchPseudofunctor.obj (.mk (op T))

/-- Actual contravariant pullback in the specified stack. -/
abbrev reindex (X : StackInGroupoids.{u}) {T V : Scheme.{u}} (a : V ⟶ T) :
    Fibre X T ⥤ Fibre X V :=
  (X.toSchPseudofunctor.map a.op.toLoc).toFunctor

/-- The actual component of a strong stack morphism. -/
abbrev component {X Y : StackInGroupoids.{u}} (f : StackInGroupoids.Hom X Y)
    (T : Scheme.{u}) : Fibre X T ⥤ Fibre Y T := (f.app (.mk (op T))).toFunctor

/-- Pointwise 2-fibres of actual strong stack morphisms. -/
abbrev twoFibreAt {X Y Z : StackInGroupoids.{u}}
    (f : StackInGroupoids.Hom X Z) (g : StackInGroupoids.Hom Y Z) (T : Scheme.{u}) :=
  IsoFibre (component f T) (component g T)

/-- An actual invertible modification of strong stack transformations.
Its naturality is the literal compatibility with the two strong
pullback-comparison isomorphisms. -/
structure TwoIso {X Y : StackInGroupoids.{u}} (p q : StackInGroupoids.Hom X Y) where
  app : ∀ T : Scheme.{u}, component p T ≅ component q T
  naturality : ∀ {T V : Scheme.{u}} (a : V ⟶ T),
    Functor.whiskerLeft (reindex X a) (app V).hom ≫
        (Cat.Hom.toNatIso (q.naturality a.op.toLoc)).hom =
      (Cat.Hom.toNatIso (p.naturality a.op.toLoc)).hom ≫
        Functor.whiskerRight (app T).hom (reindex Y a)

/-- The identity invertible modification. -/
def TwoIso.refl {X Y : StackInGroupoids.{u}} (p : StackInGroupoids.Hom X Y) :
    TwoIso p p where
  app _ := Iso.refl _
  naturality _ := by simp

/-- A genuine 2-commutative square of stacks, retaining both strong
projection transformations and their actual invertible modification. -/
structure TwoFibreSquare {X Y Z : StackInGroupoids.{u}}
    (f : StackInGroupoids.Hom X Z) (g : StackInGroupoids.Hom Y Z) where
  apex : StackInGroupoids.{u}
  fst : StackInGroupoids.Hom apex X
  snd : StackInGroupoids.Hom apex Y
  commutes : TwoIso (Pseudofunctor.StrongTrans.vcomp fst f)
    (Pseudofunctor.StrongTrans.vcomp snd g)

/-- The comparison functor is computed from the literal square legs and
2-cell; it is not an independently supplied equivalence or an object map. -/
def TwoFibreSquare.comparisonFunctor {X Y Z : StackInGroupoids.{u}}
    {f : StackInGroupoids.Hom X Z} {g : StackInGroupoids.Hom Y Z}
    (P : TwoFibreSquare f g) (T : Scheme.{u}) : Fibre P.apex T ⥤ twoFibreAt f g T :=
  isoFibreLift (component f T) (component g T) (component P.fst T)
    (component P.snd T) (P.commutes.app T)

/-- The computed 2-fibre comparison has the given first stack projection. -/
theorem TwoFibreSquare.comparison_fst {X Y Z : StackInGroupoids.{u}}
    {f : StackInGroupoids.Hom X Z} {g : StackInGroupoids.Hom Y Z}
    (P : TwoFibreSquare f g) (T : Scheme.{u}) :
    P.comparisonFunctor T ⋙ isoFibreFst (component f T) (component g T) =
      component P.fst T := rfl

/-- It also has the given second stack projection. -/
theorem TwoFibreSquare.comparison_snd {X Y Z : StackInGroupoids.{u}}
    {f : StackInGroupoids.Hom X Z} {g : StackInGroupoids.Hom Y Z}
    (P : TwoFibreSquare f g) (T : Scheme.{u}) :
    P.comparisonFunctor T ⋙ isoFibreSnd (component f T) (component g T) =
      component P.snd T := rfl

/-- A normalized actual stack 2-fibre model: the computed comparison is
an equivalence on every fibre, including actual Hom sets. Existence and
algebraicity of stack 2-fibre products are completed Axiom results; their
provider port is separate, and is not re-requested here. -/
structure TwoFibreModel {X Y Z : StackInGroupoids.{u}}
    (f : StackInGroupoids.Hom X Z) (g : StackInGroupoids.Hom Y Z)
    extends TwoFibreSquare f g where
  comparison_equivalence : ∀ T : Scheme.{u},
    (toTwoFibreSquare.comparisonFunctor T).IsEquivalence

/-- An actual algebraic-space model over T, with its actual structural
map from a chosen étale quotient presentation. -/
structure AlgebraicSpaceOver (T : Scheme.{u}) where
  presentation : EtaleEquivalencePresentation.{u}
  structural : quotientSheaf presentation ⟶ represented.obj T

/-- The actual quotient sheaf underlying the chosen algebraic space. -/
abbrev AlgebraicSpaceOver.sheaf {T : Scheme.{u}} (A : AlgebraicSpaceOver T) :=
  quotientSheaf A.presentation

/-- The actual presheaf of sections of an algebraic space which lie over
the specified scheme-valued point of T. -/
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

/-- An actual scheme chart of the structural map, normalized through the
chosen quotient atlas and the fully faithful represented-sheaf functor. -/
structure AlgebraicSpaceOver.Chart {T : Scheme.{u}} (A : AlgebraicSpaceOver T) where
  map : A.presentation.U ⟶ T
  normalization : atlas A.presentation ≫ A.structural = represented.map map

/-- Smoothness through actual étale scheme charts of the actual space. -/
def AlgebraicSpaceOver.IsSmooth {T : Scheme.{u}} (A : AlgebraicSpaceOver T) : Prop :=
  ∃ c : A.Chart, Smooth c.map

/-- Étaleness through those same actual scheme charts. -/
def AlgebraicSpaceOver.IsEtale {T : Scheme.{u}} (A : AlgebraicSpaceOver T) : Prop :=
  ∃ c : A.Chart, Etale c.map

/-- Actual fppf-local surjectivity of the structural map. -/
abbrev AlgebraicSpaceOver.IsSurjective {T : Scheme.{u}} (A : AlgebraicSpaceOver T) :=
  Epi A.structural

/-- The literal isomorphism presheaf in a stack fibre. The morphisms are
all invertible because X is a stack in groupoids. -/
abbrev isomPresheaf (X : StackInGroupoids.{u}) {T : Scheme.{u}} (x y : Fibre X T) :=
  X.toSchPseudofunctor.presheafHom x y ⋙ uliftFunctor.{u + 1, u}

/-- The morphism-presheaf values are exactly the actual isomorphisms,
with no extra invertibility predicate or freely supplied set of arrows. -/
def isomPresheafObjEquiv (X : StackInGroupoids.{u}) {T : Scheme.{u}}
    (x y : Fibre X T) (V : Over T) :
    ULift.{u + 1} ((reindex X V.hom).obj x ≅ (reindex X V.hom).obj y) ≃
      (isomPresheaf X x y).obj (op V) where
  toFun e := ULift.up e.down.hom
  invFun a := ULift.up (asIso a.down)
  left_inv e := by apply ULift.ext; apply Iso.ext; rfl
  right_inv a := rfl

/-- Representability of the actual stack diagonal by algebraic spaces,
equivalently the actual isomorphism sheaves of every pair of scheme points. -/
def HasRepresentableDiagonal (X : StackInGroupoids.{u}) : Prop :=
  ∀ (T : Scheme.{u}) (x y : Fibre X T), ∃ A : AlgebraicSpaceOver T,
    Nonempty (A.relativePresheaf ≅ isomPresheaf X x y)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual comparison-morphism presheaf of two points of a
Cat-valued pseudofunctor. In groupoid fibres all these comparisons are
isomorphisms. The same construction applies to schemes and schemes over
a specified base. -/
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

/-- The actual 2-fibre of two scheme-valued points of a stack, using its
genuine comparison isomorphisms and pullback maps. -/
abbrev schemePointFibrePresheaf (X : StackInGroupoids.{u}) {U T : Scheme.{u}}
    (x : Fibre X U) (y : Fibre X T) :=
  pointComparisonPresheaf X.toSchPseudofunctor x y

/-- The actual scheme-point fibre presheaf at the quotient-sheaf universe. -/
abbrev atlasFibrePresheaf (X : StackInGroupoids.{u}) {U T : Scheme.{u}}
    (x : Fibre X U) (y : Fibre X T) :=
  schemePointFibrePresheaf X x y ⋙ uliftFunctor.{u + 1, u}

/-- A scheme atlas candidate, with every actual scheme base change
represented by its actual algebraic-space model and normalized presheaf. -/
structure Atlas (X : StackInGroupoids.{u}) where
  U : Scheme.{u}
  point : Fibre X U
  baseChange : ∀ (T : Scheme.{u}) (_y : Fibre X T), AlgebraicSpaceOver T
  comparison : ∀ (T : Scheme.{u}) (y : Fibre X T),
    (baseChange T y).relativePresheaf ≅ atlasFibrePresheaf X point y
  surjective : ∀ (T : Scheme.{u}) (y : Fibre X T), (baseChange T y).IsSurjective

/-- A smooth surjective actual scheme atlas, with no existence asserted
for a general stack. -/
structure SmoothAtlas (X : StackInGroupoids.{u}) extends Atlas X where
  smooth : ∀ (T : Scheme.{u}) (y : Fibre X T), (baseChange T y).IsSmooth

/-- An étale surjective actual scheme atlas. -/
structure EtaleAtlas (X : StackInGroupoids.{u}) extends Atlas X where
  etale : ∀ (T : Scheme.{u}) (y : Fibre X T), (baseChange T y).IsEtale

/-- An actual étale atlas is an actual smooth atlas by the completed
scheme implication, using the same charts and normalization maps. -/
def EtaleAtlas.toSmoothAtlas {X : StackInGroupoids.{u}} (a : EtaleAtlas X) : SmoothAtlas X where
  toAtlas := a.toAtlas
  smooth T y := by
    obtain ⟨c, hc⟩ := a.etale T y
    exact ⟨c, by have := hc; infer_instance⟩

/-- The general algebraic/Artin-stack contract on the actual fppf stack. -/
def IsArtinStack (X : StackInGroupoids.{u}) : Prop :=
  HasRepresentableDiagonal X ∧ Nonempty (SmoothAtlas X)

/-- The general Deligne--Mumford-stack contract on that same carrier. -/
def IsDeligneMumfordStack (X : StackInGroupoids.{u}) : Prop :=
  HasRepresentableDiagonal X ∧ Nonempty (EtaleAtlas X)

/-- The Deligne--Mumford contract implies the general Artin contract. -/
theorem isArtinStack_of_isDeligneMumfordStack {X : StackInGroupoids.{u}}
    (h : IsDeligneMumfordStack X) : IsArtinStack X :=
  ⟨h.1, h.2.map EtaleAtlas.toSmoothAtlas⟩

/-! ## Native stacks over a specified base scheme

These adapters retain the native `(Over S)`-indexed pseudofunctor.
Representability and atlas contracts use the very same actual
algebraic-space models, via the completed iterated-slice equivalence.
For example, a root-stack pseudofunctor over X can bind these types
directly with its groupoid and fppf-stack dependencies.
-/

/-- The actual relative stack carrier, indexed by schemes over S. -/
structure RelativeStack (S : Scheme.{u}) where
  toPseudofunctor : Pseudofunctor (LocallyDiscrete (Over S)ᵒᵖ) Cat.{u, u + 1}
  isGroupoid : ∀ T : Over S, IsGroupoid (toPseudofunctor.obj (.mk (op T)))
  isStack : toPseudofunctor.IsStack (Scheme.fppfTopology.over S)

attribute [instance] RelativeStack.isGroupoid RelativeStack.isStack

/-- Bind an existing native relative pseudofunctor and its named
groupoid/stack dependencies, retaining that exact pseudofunctor. -/
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

/-- Actual fibres of the native relative stack. -/
abbrev RelativeStack.Fibre {S : Scheme.{u}} (X : RelativeStack S) (T : Over S) :=
  X.toPseudofunctor.obj (.mk (op T))

/-- Actual space sections on the native iterated slice, transported by
Mathlib's fixed scheme-map normalization. -/
abbrev relativeSpacePresheaf {S : Scheme.{u}} (T : Over S)
    (A : AlgebraicSpaceOver T.left) := T.iteratedSliceForward.op ⋙ A.relativePresheaf

/-- Relative diagonal representability, on the actual isomorphism
presheaf of the supplied native pseudofunctor. -/
def RelativeStack.HasRepresentableDiagonal {S : Scheme.{u}} (X : RelativeStack S) : Prop :=
  ∀ (T : Over S) (x y : X.Fibre T), ∃ A : AlgebraicSpaceOver T.left,
    Nonempty (relativeSpacePresheaf T A ≅
      X.toPseudofunctor.presheafHom x y ⋙ uliftFunctor.{u + 1, u})

/-- A native relative scheme atlas with actual normalized algebraic-space
base changes and actual fppf-local surjectivity. -/
structure RelativeStack.Atlas {S : Scheme.{u}} (X : RelativeStack S) where
  U : Over S
  point : X.Fibre U
  baseChange : ∀ (T : Over S) (_y : X.Fibre T), AlgebraicSpaceOver T.left
  comparison : ∀ (T : Over S) (y : X.Fibre T),
    relativeSpacePresheaf T (baseChange T y) ≅
      pointComparisonPresheaf X.toPseudofunctor point y ⋙ uliftFunctor.{u + 1, u}
  surjective : ∀ (T : Over S) (y : X.Fibre T), (baseChange T y).IsSurjective

/-- Actual smooth relative atlases, on schemes over the given base. -/
structure RelativeStack.SmoothAtlas {S : Scheme.{u}} (X : RelativeStack S)
    extends X.Atlas where
  smooth : ∀ (T : Over S) (y : X.Fibre T), (baseChange T y).IsSmooth

/-- Actual étale relative atlases on the same native carrier. -/
structure RelativeStack.EtaleAtlas {S : Scheme.{u}} (X : RelativeStack S)
    extends X.Atlas where
  etale : ∀ (T : Over S) (y : X.Fibre T), (baseChange T y).IsEtale

/-- The general Artin condition directly on the native relative stack. -/
def RelativeStack.IsArtinStack {S : Scheme.{u}} (X : RelativeStack S) : Prop :=
  X.HasRepresentableDiagonal ∧ Nonempty X.SmoothAtlas

/-- The general DM condition directly on that same relative carrier. -/
def RelativeStack.IsDeligneMumfordStack {S : Scheme.{u}} (X : RelativeStack S) : Prop :=
  X.HasRepresentableDiagonal ∧ Nonempty X.EtaleAtlas

end AlgebraicGeometry.GeneralStackGeometry
