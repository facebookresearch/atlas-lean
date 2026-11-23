/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.StackChowGroups
public import MathlibExt.AlgebraicGeometry.AffineConeAtlas
public import MathlibExt.AlgebraicGeometry.AffineNormalConeMaps
public import Mathlib.CategoryTheory.Grothendieck
public import Mathlib.CategoryTheory.Whiskering

/-!
# Locally presented bundle stacks and the relative intrinsic cone

Bundle-stack local models are the actual translation groupoids of two
vector-bundle modules. The global affine-point pseudofunctor has actual
finite locally free point modules, semilinear restrictions and linear
homotopies as coherence cells. The local chart is compared to this global
linear model over the source. No two globally cartesian bundle sheaves on
the original stack are required.

The intrinsic cone has compatible views on every actual smooth
presentation and refinement, with identity/composition coherence. Its
chart groupoid is the actual Rees cone modulo ambient tangent translations.
Both Čech point arrows are retained and the comparison is fixed by literal
global fibre reindexing, coefficients, degree one and Kähler pure tensors.
Transition comparison 2-cells have their actual coefficient maps and
zero/homothety behavior; ordinary cocycle coherence alone is insufficient.
Embeddings are tested directly in the fixed GLOBAL E.linear functor on
all object values, coefficient/base-arrow translations and actual
refinement-cell images. No local embedding isomorphism replaces that map.

References: Kresch arXiv:math/9810166v1, Theorem 2.1.12(vi),(x),
Proposition 5.3.2; Behrend--Fantechi arXiv:alg-geom/9601010,
Sections 1--3; Manolache arXiv:0805.2065v2, Definitions 2.7--2.10,
Condition 3.3 and Construction 3.6. Rees and conormal definitions reuse
the completed native scheme modules. No obstruction-theory or virtual
bivariant theorem is included in the input cone model.
-/

set_option maxHeartbeats 2000000

@[expose] public noncomputable section
namespace AlgebraicGeometry.StackBundleCones

open CategoryTheory CategoryTheory.Limits Opposite
open GeneralStackGeometry StackCycleGeometry StackFibreModels StackAffineModules
open StackVectorBundles StackProjectiveModels StackCycleRelations StackChowGroups
open scoped TensorProduct

variable {S : Scheme.{0}} {scope : Stack S → Prop}

/-- A scheme-valued point is represented by its literal slice in the
native fibred category, retaining the map to the stack. -/
structure PointSchemeModel (X : Stack S) (T : Over S) (x : X.Fibre T) where
  stack : Stack S
  map : StackHom stack X
  toPoint : ∀ q : Total stack, (totalMap map).obj q ⟶ point T x
  naturality : ∀ {q r : Total stack} (h : q ⟶ r),
    (totalMap map).map h ≫ toPoint r = toPoint q

def PointSchemeModel.graph {X : Stack S} {T : Over S} {x : X.Fibre T}
    (M : PointSchemeModel X T x) : Total M.stack ⥤ Over (point T x) where
  obj q := Over.mk (M.toPoint q)
  map h := Over.homMk ((totalMap M.map).map h) (M.naturality h)
  map_id q := by apply Over.OverMorphism.ext; exact (totalMap M.map).map_id q
  map_comp h k := by apply Over.OverMorphism.ext; exact (totalMap M.map).map_comp h k

def PointSchemeModel.IsNormalized {X : Stack S} {T : Over S} {x : X.Fibre T}
    (M : PointSchemeModel X T x) : Prop := M.graph.IsEquivalence

structure AdditiveQuotient {R : Type} [CommRing R] {M N : Type}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (d : M →ₗ[R] N) where
  value : N

namespace AdditiveQuotient

variable {R : Type} [CommRing R] {M N : Type}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] {d : M →ₗ[R] N}

structure Hom (a b : AdditiveQuotient d) where
  translation : M
  relation : b.value = a.value + d translation

@[ext] theorem hom_ext {a b : AdditiveQuotient d} {f g : Hom a b}
    (h : f.translation = g.translation) : f = g := by cases f; cases g; cases h; rfl

instance : Groupoid (AdditiveQuotient d) where
  Hom := Hom
  id a := ⟨0, by simp⟩
  comp f g := ⟨f.translation + g.translation, by rw [g.relation, f.relation]; simp [add_assoc]⟩
  inv f := ⟨-f.translation, by rw [f.relation]; simp [add_assoc]⟩
  id_comp f := by apply hom_ext; exact zero_add _
  comp_id f := by apply hom_ext; exact add_zero _
  assoc f g h := by apply hom_ext; exact add_assoc _ _ _
  inv_comp f := by apply hom_ext; exact neg_add_cancel _

end AdditiveQuotient

def pointIsoArrow {X : Stack S} {T : Over S} {x y : X.Fibre T} (h : x ≅ y) :
    point T x ⟶ point T y where
  base := 𝟙 T
  fiber := h.hom ≫
    (X.toPseudofunctor.mapId (.mk (op T))).inv.toNatTrans.app y


def quotientRestriction {X : Stack S} {E F : VectorBundle X} (d : BundleMap E F)
    {a b : (AffinePoint X)ᵒᵖ} (f : a ⟶ b) :
    AdditiveQuotient (R := (rings X).obj a) (d.linear.app a).hom ⥤
      AdditiveQuotient (R := (rings X).obj b) (d.linear.app b).hom where
  obj q := ⟨F.module.val.presheaf.restrictₛₗ f q.value⟩
  map h := ⟨E.module.val.presheaf.restrictₛₗ f h.translation, by
    change F.module.val.presheaf.restrictₛₗ f _ =
      F.module.val.presheaf.restrictₛₗ f _ +
        (d.linear.app b) (E.module.val.presheaf.restrictₛₗ f _)
    rw [h.relation, map_add]
    congr 1
    exact (PresheafOfModules.naturality_apply d.linear f h.translation).symm⟩
  map_id q := by apply AdditiveQuotient.hom_ext; exact map_zero _
  map_comp h k := by apply AdditiveQuotient.hom_ext; exact map_add _ _ _

/-- The diagram is fixed on objects and on every actual restriction map. -/
structure QuotientDiagram {X : Stack S} {E F : VectorBundle X} (d : BundleMap E F) where
  functor : (AffinePoint X)ᵒᵖ ⥤ Cat.{0, 0}
  object_eq : ∀ a, functor.obj a =
    Cat.of (AdditiveQuotient (R := (rings X).obj a) (d.linear.app a).hom)
  map_eq : ∀ {a b : (AffinePoint X)ᵒᵖ} (f : a ⟶ b),
    eqToHom (object_eq a).symm ≫ functor.map f ≫ eqToHom (object_eq b) =
      (quotientRestriction d f).toCatHom

def quotientForget {X : Stack S} {E F : VectorBundle X} {d : BundleMap E F}
    (Q : QuotientDiagram d) : (Grothendieck Q.functor)ᵒᵖ ⥤ AffinePoint X :=
  (Grothendieck.forget Q.functor).leftOp

structure QuotientStackModel {X : Stack S} {E F : VectorBundle X} (d : BundleMap E F) where
  diagram : QuotientDiagram d
  total : Stack S
  projection : StackHom total X
  comparison : AffinePoint total ≌ (Grothendieck diagram.functor)ᵒᵖ
  overBase : comparison.functor ⋙ quotientForget diagram ≅ affineMap projection

def QuotientStackModel.inverseBase {X : Stack S} {E F : VectorBundle X} {d : BundleMap E F}
    (Q : QuotientStackModel d) : Q.comparison.inverse ⋙ affineMap Q.projection ≅
      quotientForget Q.diagram :=
  (Functor.isoWhiskerLeft Q.comparison.inverse Q.overBase).symm ≪≫
    Functor.isoWhiskerRight Q.comparison.counitIso (quotientForget Q.diagram)

structure BundlePointModules (R : CommRingCat.{0}) (n : ℤ) where
  degreeZero : ModuleCat.{0} R
  degreeOne : ModuleCat.{0} R
  rankZero : ℕ
  rankOne : ℕ
  rankZero_normalized : LocalRank R degreeZero rankZero
  rankOne_normalized : LocalRank R degreeOne rankOne
  finiteZero : Module.FinitePresentation R degreeZero
  finiteOne : Module.FinitePresentation R degreeOne
  differential : degreeZero ⟶ degreeOne
  rank_eq : (rankOne : ℤ) - rankZero = n

abbrev BundlePointModules.Point {R : CommRingCat.{0}} {n : ℤ} (M : BundlePointModules R n) :=
  AdditiveQuotient (R := R) M.differential.hom

structure SemilinearQuotientMap {R A : Type} [CommRing R] [CommRing A]
    {M₀ M₁ N₀ N₁ : Type} [AddCommGroup M₀] [Module R M₀] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup N₀] [Module A N₀] [AddCommGroup N₁] [Module A N₁]
    (d : M₀ →ₗ[R] M₁) (e : N₀ →ₗ[A] N₁) (φ : R →+* A) where
  degreeZero : M₀ →ₛₗ[φ] N₀
  degreeOne : M₁ →ₛₗ[φ] N₁
  commutes : ∀ x, degreeOne (d x) = e (degreeZero x)

def SemilinearQuotientMap.functor {R A : Type} [CommRing R] [CommRing A]
    {M₀ M₁ N₀ N₁ : Type} [AddCommGroup M₀] [Module R M₀] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup N₀] [Module A N₀] [AddCommGroup N₁] [Module A N₁]
    {d : M₀ →ₗ[R] M₁} {e : N₀ →ₗ[A] N₁} {φ : R →+* A} (L : SemilinearQuotientMap d e φ) :
    AdditiveQuotient d ⥤ AdditiveQuotient e where
  obj a := ⟨L.degreeOne a.value⟩
  map h := ⟨L.degreeZero h.translation, by rw [h.relation, map_add, L.commutes]⟩
  map_id a := by apply AdditiveQuotient.hom_ext; exact map_zero _
  map_comp h k := by apply AdditiveQuotient.hom_ext; exact map_add _ _ _

/-- The GLOBAL O-linear groupoid diagram on actual affine stack points.
The point modules need not form two globally cartesian bundle sheaves:
restriction is a semilinear chain map and coherence is a linear homotopy.
This permits locally perfect presentations while excluding affine/torsor
or nonlinear gluing disguised as a vector-bundle stack. -/
structure LinearBundleDiagram (X : Stack S) (n : ℤ) where
  modules : ∀ a : AffinePoint X, BundlePointModules ((rings X).obj (op a)) n
  pseudofunctor : Pseudofunctor (LocallyDiscrete (AffinePoint X)ᵒᵖ) Cat.{0, 0}
  objects : ∀ a : AffinePoint X,
    pseudofunctor.obj (.mk (op a)) = Cat.of (modules a).Point
  restriction : ∀ {a b : AffinePoint X} (f : a ⟶ b),
    SemilinearQuotientMap (modules b).differential.hom (modules a).differential.hom
      ((rings X).map f.op).hom
  maps : ∀ {a b : AffinePoint X} (f : a ⟶ b),
    eqToHom (objects b).symm ≫ pseudofunctor.map f.op.toLoc ≫ eqToHom (objects a) =
      (restriction f).functor.toCatHom
  identityLinear : ∀ a : AffinePoint X,
    ∃ h : (modules a).degreeOne →ₗ[((rings X).obj (op a))] (modules a).degreeZero,
      ∀ q : pseudofunctor.obj (.mk (op a)),
        ((eqToHom (objects a)).toFunctor.map
          ((pseudofunctor.mapId (.mk (op a))).hom.toNatTrans.app q)).translation =
          h (((eqToHom (objects a)).toFunctor.obj q).value)
  compositionLinear : ∀ {a b c : AffinePoint X} (f : a ⟶ b) (g : b ⟶ c),
    ∃ h : (modules c).degreeOne →ₛₗ[((rings X).map (g.op ≫ f.op)).hom] (modules a).degreeZero,
      ∀ q : pseudofunctor.obj (.mk (op c)),
        ((eqToHom (objects a)).toFunctor.map
          ((pseudofunctor.mapComp g.op.toLoc f.op.toLoc).hom.toNatTrans.app q)).translation =
          h (((eqToHom (objects c)).toFunctor.obj q).value)
  inclusion : ∀ a : AffinePoint X,
    (modules a).Point ⥤ Pseudofunctor.CoGrothendieck pseudofunctor
  inclusion_objects : ∀ (a : AffinePoint X) (q : (modules a).Point),
    (inclusion a).obj q = ⟨a, (eqToHom (objects a).symm).toFunctor.obj q⟩
  inclusion_base : ∀ a : AffinePoint X,
    inclusion a ⋙ Pseudofunctor.CoGrothendieck.forget pseudofunctor = (Functor.const _).obj a
  inclusion_morphisms : ∀ (a : AffinePoint X) (q r : (modules a).Point) (h : q ⟶ r),
    HEq ((inclusion a).map h).fiber
      ((eqToHom (objects a).symm).toFunctor.map h ≫
        (pseudofunctor.mapId (.mk (op a))).inv.toNatTrans.app
          ((eqToHom (objects a).symm).toFunctor.obj r))

structure LinearBundleModel {X B : Stack S} (π : StackHom B X) (n : ℤ) where
  diagram : LinearBundleDiagram X n
  comparison : AffinePoint B ≌ Pseudofunctor.CoGrothendieck diagram.pseudofunctor
  overBase : comparison.functor ⋙ Pseudofunctor.CoGrothendieck.forget diagram.pseudofunctor ≅
    affineMap π

def LinearBundleModel.inverseBase {X B : Stack S} {π : StackHom B X} {n : ℤ}
    (M : LinearBundleModel π n) : M.comparison.inverse ⋙ affineMap π ≅
      Pseudofunctor.CoGrothendieck.forget M.diagram.pseudofunctor :=
  (Functor.isoWhiskerLeft M.comparison.inverse M.overBase).symm ≪≫
    Functor.isoWhiskerRight M.comparison.counitIso
      (Pseudofunctor.CoGrothendieck.forget M.diagram.pseudofunctor)

def quotientCoefficient {X : Stack S} {E F : VectorBundle X} {d : BundleMap E F}
    (Q : QuotientDiagram d) (a : AffinePoint X) :
    AdditiveQuotient (R := (rings X).obj (op a)) (d.linear.app (op a)).hom ⥤
      (Grothendieck Q.functor)ᵒᵖ :=
  (Groupoid.invEquivalence _).functor ⋙
    (eqToHom (Q.object_eq (op a)).symm).toFunctor.op ⋙ (Grothendieck.ι Q.functor (op a)).op

/-- The morphism of affine points induced, at one affine point, by an invertible modification:
over the identity of the base, with fibre part the component of the modification. -/
def twoIsoPointHom {X Y : Stack S} {p q : StackHom X Y} (e : StackVectorBundles.TwoIso p q)
    (a : AffinePoint X) : (affineMap p).obj a ⟶ (affineMap q).obj a :=
  ObjectProperty.homMk
    (⟨𝟙 a.obj.base, (e.app a.obj.base).hom.app a.obj.fiber ≫
      (Y.toPseudofunctor.mapId ⟨op a.obj.base⟩).inv.toNatTrans.app _⟩ :
      Pseudofunctor.CoGrothendieck.Hom ((totalMap p).obj a.obj) ((totalMap q).obj a.obj))

section Reindexing

universe v₁ u₁ v₂ u₂ v₃ u₃
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The canonical functor from the CoGrothendieck construction of a pseudofunctor reindexed along
`F` to the CoGrothendieck construction of the pseudofunctor itself, over `F`. -/
def reindexTotal (F : C ⥤ D) (G : Pseudofunctor (LocallyDiscrete Dᵒᵖ) Cat.{v₃, u₃}) :
    Pseudofunctor.CoGrothendieck ((F.op.toPseudofunctor).comp G) ⥤
      Pseudofunctor.CoGrothendieck G where
  obj x := ⟨F.obj x.base, x.fiber⟩
  map f := ⟨F.map f.base, f.fiber⟩
  map_id x := by
    ext
    · simp
    · simp [Pseudofunctor.comp, Functor.toPseudofunctor, pseudofunctorOfIsLocallyDiscrete,
        PrelaxFunctor.map₂_eqToHom]
  map_comp f g := by
    ext
    · simp
    · dsimp [Pseudofunctor.comp, Functor.toPseudofunctor, pseudofunctorOfIsLocallyDiscrete,
        Quiver.Hom.toLoc]
      simp [PrelaxFunctor.map₂_eqToHom]

end Reindexing

/-- A linear map of linear bundle diagrams over `p`: a strong transformation from `M` to the
reindexing of `N` along `p`, whose component at each affine point of `T` is the map of quotient
groupoids induced by a linear map of the two-term presentations (over the identity of the common
coordinate ring), and whose naturality cell at each restriction arrow is a linear homotopy.
This is descent data: the comparison is coherent across restriction arrows, not chosen
independently on each affine fibre. -/
structure LinearDiagramMap {T X : Stack S} {n m : ℤ} (M : LinearBundleDiagram T n)
    (N : LinearBundleDiagram X m) (p : StackHom T X) where
  trans : Pseudofunctor.StrongTrans M.pseudofunctor
    (((affineMap p).op.toPseudofunctor).comp N.pseudofunctor)
  linear : ∀ a : AffinePoint T,
    SemilinearQuotientMap (R := (rings T).obj (op a))
      (A := (rings X).obj (op ((affineMap p).obj a)))
      (M.modules a).differential.hom
      (N.modules ((affineMap p).obj a)).differential.hom
      (RingHom.id ((rings X).obj (op ((affineMap p).obj a))))
  components : ∀ a : AffinePoint T,
    eqToHom (M.objects a).symm ≫ trans.app (.mk (op a)) ≫
        eqToHom (N.objects ((affineMap p).obj a)) = (linear a).functor.toCatHom
  naturalityLinear : ∀ {a b : AffinePoint T} (f : a ⟶ b),
    ∃ h : (M.modules b).degreeOne →ₛₗ[(RingHom.id ((rings X).obj (op ((affineMap p).obj a)))).comp
          ((rings T).map f.op).hom]
        (N.modules ((affineMap p).obj a)).degreeZero,
      ∀ q : M.pseudofunctor.obj (.mk (op b)),
        ((eqToHom (N.objects ((affineMap p).obj a))).toFunctor.map
          ((trans.naturality f.op.toLoc).hom.toNatTrans.app q)).translation =
          h (((eqToHom (M.objects b)).toFunctor.obj q).value)

/-- The functor of total CoGrothendieck categories induced by a linear diagram map. -/
def LinearDiagramMap.total {T X : Stack S} {n m : ℤ} {M : LinearBundleDiagram T n}
    {N : LinearBundleDiagram X m} {p : StackHom T X} (Φ : LinearDiagramMap M N p) :
    Pseudofunctor.CoGrothendieck M.pseudofunctor ⥤ Pseudofunctor.CoGrothendieck N.pseudofunctor :=
  Pseudofunctor.CoGrothendieck.map Φ.trans ⋙ reindexTotal (affineMap p) N.pseudofunctor

/-- `G` is the strict linear diagram of the global two-term complex `d : E₀ → E₁` on `X`: on each
affine point its presentation is identified with the sections of `d`, compatibly with the
restriction maps, and its unit and composition cells are trivial. -/
structure PresentsComplex {X : Stack S} {n : ℤ} (G : LinearBundleDiagram X n)
    {E₀ E₁ : VectorBundle X} (d : BundleMap E₀ E₁) where
  zero : ∀ a : AffinePoint X,
    (G.modules a).degreeZero ≃ₗ[(rings X).obj (op a)] E₀.module.val.presheaf.obj (op a)
  one : ∀ a : AffinePoint X,
    (G.modules a).degreeOne ≃ₗ[(rings X).obj (op a)] E₁.module.val.presheaf.obj (op a)
  differential : ∀ (a : AffinePoint X) (x : (G.modules a).degreeZero),
    one a ((G.modules a).differential.hom x) = (d.linear.app (op a)).hom (zero a x)
  restrictionZero : ∀ {a b : AffinePoint X} (f : a ⟶ b) (x : (G.modules b).degreeZero),
    zero a ((G.restriction f).degreeZero x) = (E₀.module.val.presheaf.map f.op).hom (zero b x)
  restrictionOne : ∀ {a b : AffinePoint X} (f : a ⟶ b) (x : (G.modules b).degreeOne),
    one a ((G.restriction f).degreeOne x) = (E₁.module.val.presheaf.map f.op).hom (one b x)
  identityStrict : ∀ (a : AffinePoint X) (q : G.pseudofunctor.obj (.mk (op a))),
    ((eqToHom (G.objects a)).toFunctor.map
      ((G.pseudofunctor.mapId (.mk (op a))).hom.toNatTrans.app q)).translation = 0
  compositionStrict : ∀ {a b c : AffinePoint X} (f : a ⟶ b) (g : b ⟶ c)
      (q : G.pseudofunctor.obj (.mk (op c))),
    ((eqToHom (G.objects a)).toFunctor.map
      ((G.pseudofunctor.mapComp g.op.toLoc f.op.toLoc).hom.toNatTrans.app q)).translation = 0

/-- A linear isomorphism of bundle stacks over `p`: a linear diagram map inducing an equivalence of
quotient groupoids on every affine point, whose induced total functor is the displayed total-space
map `q` on all affine points (including restriction arrows), over the base 2-cell `square`. A map
that only gives a Cartesian square of total spaces, or one that is linear fibre by fibre but not
coherently (a shear through stabilizers), is not linear. -/
structure LinearBundleIso {T X B C : Stack S} {π : StackHom B T} {ρ : StackHom C X} {n m : ℤ}
    (M : LinearBundleModel π n) (N : LinearBundleModel ρ m) (p : StackHom T X) (q : StackHom B C)
    (square : StackVectorBundles.TwoIso (Pseudofunctor.StrongTrans.vcomp q ρ)
      (Pseudofunctor.StrongTrans.vcomp π p)) where
  diagramMap : LinearDiagramMap M.diagram N.diagram p
  /-- On each affine point the induced map of quotient groupoids is an equivalence (a
  quasi-isomorphism of the two-term presentations). -/
  equivalence : ∀ a : AffinePoint T, (diagramMap.linear a).functor.IsEquivalence
  normalized : M.comparison.functor ⋙ diagramMap.total ⋙ N.comparison.inverse ≅ affineMap q
  /-- `normalized` lies over `square`: projected to affine points of `X`, it is the base comparison
  of `N`, the base comparison of `M` transported along `p`, and the inverse cell of `square`. -/
  based : ∀ b : AffinePoint B,
    (affineMap ρ).map (normalized.hom.app b) =
      N.inverseBase.hom.app (diagramMap.total.obj (M.comparison.functor.obj b)) ≫
        (affineMap p).map (M.overBase.hom.app b) ≫ square.pointInv b

/-- A local quotient presentation on a genuine scheme atlas of X. -/
structure VectorBundleStack (X : Stack S) where
  total : Stack S
  projection : StackHom total X
  virtualRank : ℤ
  atlas : X.SmoothAtlas
  base : PointSchemeModel X atlas.U atlas.point
  base_normalized : base.IsNormalized
  degreeZero : VectorBundle base.stack
  degreeOne : VectorBundle base.stack
  differential : BundleMap degreeZero degreeOne
  quotient : QuotientStackModel differential
  map : StackHom quotient.total total
  commutes : StackVectorBundles.TwoIso (Pseudofunctor.StrongTrans.vcomp map projection)
    (Pseudofunctor.StrongTrans.vcomp quotient.projection base.map)
  cartesian : ∀ T : Over S,
    ((CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
      (StackCycleGeometry.component projection T) (StackCycleGeometry.component base.map T) _).obj
      ⟨StackCycleGeometry.component map T, StackCycleGeometry.component quotient.projection T,
        commutes.app T⟩).IsEquivalence
  rank_eq : virtualRank = (degreeOne.rank : ℤ) - degreeZero.rank
  linear : LinearBundleModel projection virtualRank
  /-- The linear structure over the atlas: there, the linear model is coherently (over all affine
  points of the atlas, including restriction arrows) the strict diagram of the atlas complex.
  The displayed square `map`/`commutes`/`cartesian` only identifies the total spaces; no linearity
  of `map` is asserted. -/
  chartDescent : ∃ (G : LinearBundleDiagram base.stack virtualRank)
      (_ : PresentsComplex G differential) (Φ : LinearDiagramMap G linear.diagram base.map),
    ∀ a : AffinePoint base.stack, (Φ.linear a).functor.IsEquivalence

/-- The bundle stack `E` is the quotient of the global two-term complex `d` on `X`: its linear
model is equivalent, coherently over all affine points (descent data over the identity of `X`),
to the strict linear diagram of `d`. -/
def IsQuotientOf {X : Stack S} (E : VectorBundleStack X) {E₀ E₁ : VectorBundle X}
    (d : BundleMap E₀ E₁) : Prop :=
  ∃ (G : LinearBundleDiagram X E.virtualRank) (_ : PresentsComplex G d)
    (Φ : LinearDiagramMap G E.linear.diagram (Pseudofunctor.StrongTrans.id X.toPseudofunctor)),
    ∀ a : AffinePoint X, (Φ.linear a).functor.IsEquivalence

/-- The base change of a bundle stack: a 2-Cartesian total-space square whose map is linear for
the two linear models (it cannot, for example, move the origin of a line). -/
structure BundleStackPullback {T X : Stack S} (p : StackHom T X) (E : VectorBundleStack X) where
  bundle : VectorBundleStack T
  rank_eq : bundle.virtualRank = E.virtualRank
  map : StackHom bundle.total E.total
  commutes : StackVectorBundles.TwoIso (Pseudofunctor.StrongTrans.vcomp map E.projection)
    (Pseudofunctor.StrongTrans.vcomp bundle.projection p)
  cartesian : ∀ U : Over S,
    ((CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
      (StackCycleGeometry.component E.projection U) (StackCycleGeometry.component p U) _).obj
      ⟨StackCycleGeometry.component map U, StackCycleGeometry.component bundle.projection U,
        commutes.app U⟩).IsEquivalence
  linearMap : LinearBundleIso bundle.linear E.linear p map commutes

def zeroElementFunctor {X : Stack S} (E : VectorBundle X) :
    AffinePoint X ⥤ (sectionPresheaf E.module.val).Elementsᵒᵖ where
  obj a := op ((sectionPresheaf E.module.val).elementsMk (op a)
    (0 : E.module.val.presheaf.obj (op a)))
  map f := (Functor.Elements.homMk f.op (by
    change E.module.val.presheaf.presheaf.map f.op 0 = 0
    exact map_zero _)).op
  map_id a := by rfl
  map_comp f g := by rfl

structure ZeroSection {X : Stack S} (E : VectorBundle X) where
  map : StackHom X E.total
  overBase : StackVectorBundles.TwoIso (Pseudofunctor.StrongTrans.vcomp map E.projection)
    (Pseudofunctor.StrongTrans.id X.toPseudofunctor)
  normalized : affineMap map ⋙ E.comparison.functor ≅ zeroElementFunctor E
  closed : StackFibreModels.IsClosed map

structure LocallyClosedSubstack (X : Stack S) where
  closed : ClosedSubstack X
  opened : OpenSubstack closed.source

def LocallyClosedSubstack.source {X : Stack S} (Z : LocallyClosedSubstack X) : Stack S :=
  Z.opened.source

def LocallyClosedSubstack.predicate {X : Stack S} (Z : LocallyClosedSubstack X)
    (T : Over S) (x : X.Fibre T) : Prop :=
  ∃ y : Z.closed.source.Fibre T,
    Nonempty ((StackCycleGeometry.component Z.closed.inclusion T).obj y ≅ x) ∧
    Z.opened.predicate T y

/-- Faithful stabilizer action of a genuine vector bundle, measured by
its actual affine-point restriction maps. The frame space then gives the
source GL(n) quotient presentation, rather than a freely named quotient. -/
def FaithfulOnFibres {X : Stack S} (E : VectorBundle X) : Prop :=
  ∀ {a b : AffinePoint X} (f g : a ⟶ b), f.hom.base = g.hom.base →
    E.module.val.presheaf.presheaf.map f.op = E.module.val.presheaf.presheaf.map g.op → f = g

structure QuotientStratification (X : Stack S) where
  length : ℕ
  strata : Fin length → LocallyClosedSubstack X
  bundle : ∀ i, VectorBundle (strata i).source
  faithful : ∀ i, FaithfulOnFibres (bundle i)
  exhaustive : ∀ (K : Type) [Field K] (q : Spec (.of K) ⟶ S)
    (x : X.Fibre (Over.mk q)), ∃ i, (strata i).predicate (Over.mk q) x
  disjoint : ∀ (K : Type) [Field K] (q : Spec (.of K) ⟶ S)
    (x : X.Fibre (Over.mk q)) (i j : Fin length),
    (strata i).predicate (Over.mk q) x → (strata j).predicate (Over.mk q) x → i = j

structure BundleHomotopyData (D : CycleConstructionData S scope) (K : KreschPresentation D)
    {X : Stack S} (hX : scope X) (E : VectorBundle X) (hE : scope E.total)
    (P : FlatChowPullData D K hE hX E.projection E.rank) where
  isomorphism : ∀ d : ℤ, ChowGroup D K X hX (d - E.rank) ≃+ ChowGroup D K E.total hE d
  normalized : ∀ (d : ℤ) (a : ChowGroup D K X hX (d - E.rank)),
    isomorphism d a = chowRegrade D K E.total hE (by omega) (P.map (d - E.rank) a)

def zeroSectionGysin {D : CycleConstructionData S scope} {K : KreschPresentation D}
    {X : Stack S} {hX : scope X} {E : VectorBundle X} {hE : scope E.total}
    {P : FlatChowPullData D K hE hX E.projection E.rank}
    (H : BundleHomotopyData D K hX E hE P) (d : ℤ) :
    ChowGroup D K E.total hE d →+ ChowGroup D K X hX (d - E.rank) :=
  (H.isomorphism d).symm.toAddMonoidHom

def eulerOperator {D : CycleConstructionData S scope} {K : KreschPresentation D}
    {X : Stack S} {hX : scope X} {E : VectorBundle X} {hE : scope E.total}
    {P : FlatChowPullData D K hE hX E.projection E.rank}
    (H : BundleHomotopyData D K hX E hE P) (z : ZeroSection E)
    (push : ProjectiveChowPushData D K hX hE z.map) (d : ℤ) :
    ChowGroup D K X hX d →+ ChowGroup D K X hX (d - E.rank) :=
  (zeroSectionGysin H d).comp (push.map d)

def firstChernOperator {D : CycleConstructionData S scope} {K : KreschPresentation D}
    {X : Stack S} {hX : scope X} {E : VectorBundle X} {hE : scope E.total}
    {P : FlatChowPullData D K hE hX E.projection E.rank}
    (H : BundleHomotopyData D K hX E hE P) (z : ZeroSection E)
    (push : ProjectiveChowPushData D K hX hE z.map) (rankOne : E.rank = 1) (d : ℤ) :
    ChowGroup D K X hX d →+ ChowGroup D K X hX (d - 1) :=
  (chowRegrade D K X hX (by simp [rankOne])).comp (eulerOperator H z push d)

structure BundleStackHomotopyData (D : CycleConstructionData S scope) (K : KreschPresentation D)
    {X : Stack S} (hX : scope X) (E : VectorBundleStack X) (hE : scope E.total)
    (P : FlatChowPullData D K hE hX E.projection E.virtualRank) where
  isomorphism : ∀ d : ℤ,
    ChowGroup D K X hX (d - E.virtualRank) ≃+ ChowGroup D K E.total hE d
  normalized : ∀ (d : ℤ) (a : ChowGroup D K X hX (d - E.virtualRank)),
    isomorphism d a = chowRegrade D K E.total hE (by omega) (P.map (d - E.virtualRank) a)

def bundleStackZeroSectionInverse {D : CycleConstructionData S scope} {K : KreschPresentation D}
    {X : Stack S} {hX : scope X} {E : VectorBundleStack X} {hE : scope E.total}
    {P : FlatChowPullData D K hE hX E.projection E.virtualRank}
    (H : BundleStackHomotopyData D K hX E hE P) (d : ℤ) :
    ChowGroup D K E.total hE d →+ ChowGroup D K X hX (d - E.virtualRank) :=
  (H.isomorphism d).symm.toAddMonoidHom

/-- Only affine test schemes are retained here, with their full arrows. -/
abbrev AffineFibreCategory {X Y : Stack S} (f : StackHom X Y) (T : Over S) (y : Y.Fibre T) :=
  (show ObjectProperty (FibreCategory f T y) from fun q => IsAffine q.left.base.left).FullSubcategory

def affineFibreForget {X Y : Stack S} (f : StackHom X Y) (T : Over S) (y : Y.Fibre T) :
    AffineFibreCategory f T y ⥤ Over T.left :=
  (show ObjectProperty (FibreCategory f T y) from fun q => IsAffine q.left.base.left).ι ⋙
    fibreForget f T y ⋙ T.iteratedSliceForward

structure ConeChartGeometry {F G : Stack S} (f : StackHom F G) where
  target : G.SmoothAtlas
  [targetAffine : IsAffine target.U.left]
  targetModel : PointSchemeModel G target.U target.point
  target_normalized : targetModel.IsNormalized
  square : TwoCartesianSquare f targetModel.map
  source : square.apex.EtaleAtlas
  [sourceAffine : IsAffine source.U.left]
  [sourceNoetherian : IsNoetherian source.U.left]
  [sourceFiniteType : LocallyOfFiniteType source.U.hom]

attribute [instance] ConeChartGeometry.targetAffine ConeChartGeometry.sourceAffine
  ConeChartGeometry.sourceNoetherian ConeChartGeometry.sourceFiniteType

def ConeChartGeometry.map {F G : Stack S} {f : StackHom F G} (c : ConeChartGeometry f) :
    c.source.U ⟶ c.target.U :=
  (c.targetModel.toPoint (point c.source.U
    ((StackCycleGeometry.component c.square.snd c.source.U).obj c.source.point))).base

abbrev ConeChartGeometry.sourcePoint {F G : Stack S} {f : StackHom F G}
    (c : ConeChartGeometry f) : F.Fibre c.source.U :=
  (StackCycleGeometry.component c.square.fst c.source.U).obj c.source.point

@[instance_reducible]
def ConeChartGeometry.algebra {F G : Stack S} {f : StackHom F G} (c : ConeChartGeometry f) :
    Algebra Γ(c.target.U.left, ⊤) Γ(c.source.U.left, ⊤) := c.map.left.appTop.hom.toAlgebra

structure IntrinsicConeChart {F G : Stack S} (f : StackHom F G) where
  geometry : ConeChartGeometry f
  presentation : letI := geometry.algebra
    _root_.Algebra.Extension.{0} Γ(geometry.target.U.left, ⊤) Γ(geometry.source.U.left, ⊤)
  smooth : letI := geometry.algebra
    _root_.Algebra.Smooth Γ(geometry.target.U.left, ⊤) presentation.Ring

section AffineCone

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
  (P : _root_.Algebra.Extension.{0} A B)

open MathlibExt.AlgebraicGeometry.AffineConeAtlas

structure IntrinsicConePoint (C : Type) [CommRing C] [Algebra B C] where
  map : normalAlgebra P →ₐ[B] C

namespace IntrinsicConePoint

variable {P} {C : Type} [CommRing C] [Algebra B C]

structure Hom (a b : IntrinsicConePoint P C) where
  tangent : P.CotangentSpace →ₗ[B] C
  relation : ∀ x : P.Cotangent,
    b.map (normalCotangent P x) = a.map (normalCotangent P x) + tangent (P.cotangentComplex x)

@[ext] theorem hom_ext {a b : IntrinsicConePoint P C} {f g : Hom a b}
    (h : f.tangent = g.tangent) : f = g := by cases f; cases g; cases h; rfl

instance : Groupoid (IntrinsicConePoint P C) where
  Hom := Hom
  id a := ⟨0, by intro x; simp⟩
  comp f g := ⟨f.tangent + g.tangent, by intro x; rw [g.relation, f.relation]; simp [add_assoc]⟩
  inv f := ⟨-f.tangent, by intro x; rw [f.relation]; simp [add_assoc]⟩
  id_comp f := by apply hom_ext; exact zero_add _
  comp_id f := by apply hom_ext; exact add_zero _
  assoc f g h := by apply hom_ext; exact add_assoc _ _ _
  inv_comp f := by apply hom_ext; exact neg_add_cancel _

end IntrinsicConePoint

def coneCoefficientFunctor {C D : Type} [CommRing C] [CommRing D] [Algebra B C] [Algebra B D]
    (h : C →ₐ[B] D) : IntrinsicConePoint P C ⥤ IntrinsicConePoint P D where
  obj a := ⟨h.comp a.map⟩
  map f := ⟨h.toLinearMap.comp f.tangent, by intro x; simpa using congrArg h (f.relation x)⟩
  map_id a := by apply IntrinsicConePoint.hom_ext; exact LinearMap.comp_zero _
  map_comp f g := by apply IntrinsicConePoint.hom_ext; exact LinearMap.comp_add _ _ _

structure IntrinsicConeDiagram where
  functor : CommAlgCat.{0} B ⥤ Cat.{0, 0}
  object_eq : ∀ C, functor.obj C = Cat.of (IntrinsicConePoint P C)
  map_eq : ∀ {C D : CommAlgCat.{0} B} (h : C ⟶ D),
    eqToHom (object_eq C).symm ≫ functor.map h ≫ eqToHom (object_eq D) =
      (coneCoefficientFunctor P h.hom).toCatHom

end AffineCone

section ConeHomotheties
open MathlibExt.AlgebraicGeometry.AffineConeAtlas

def IsZeroConePoint {A B D : Type} [CommRing A] [CommRing B] [Algebra A B]
    [CommRing D] [Algebra B D] (P : _root_.Algebra.Extension.{0} A B)
    (a : IntrinsicConePoint P D) : Prop :=
  ∀ x : P.ker, a.map (normalDegreeOne P x) = 0

def IsScaledConePoint {A B D : Type} [CommRing A] [CommRing B] [Algebra A B]
    [CommRing D] [Algebra B D] (P : _root_.Algebra.Extension.{0} A B)
    (r : D) (a b : IntrinsicConePoint P D) : Prop :=
  ∀ x : P.ker, b.map (normalDegreeOne P x) = r * a.map (normalDegreeOne P x)

end ConeHomotheties

section ConeCoordinateRead

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
  (P : _root_.Algebra.Extension.{0} A B) (D : IntrinsicConeDiagram P)

@[implicit_reducible]
def coneObject (R : CommAlgCat.{0} B) (a : IntrinsicConePoint P R) :
    (Grothendieck D.functor)ᵒᵖ :=
  op ⟨R, (eqToHom (D.object_eq R).symm).toFunctor.obj a⟩

def conePoint (q : (Grothendieck D.functor)ᵒᵖ) : IntrinsicConePoint P q.unop.base :=
  (eqToHom (D.object_eq q.unop.base)).toFunctor.obj q.unop.fiber

/-- Includes coefficient arrows: the fibre of h.unop is read in the
source coefficient algebra of h, with its actual semilinear restriction. -/
def coneArrowTangent {q r : (Grothendieck D.functor)ᵒᵖ} (h : q ⟶ r) :
    P.CotangentSpace →ₗ[B] q.unop.base :=
  ((eqToHom (D.object_eq q.unop.base)).toFunctor.map h.unop.fiber).tangent

def IsScaledConeArrow {R T : CommAlgCat.{0} B} (r : R) (s : T)
    {a a' : IntrinsicConePoint P R} {b b' : IntrinsicConePoint P T}
    (h : coneObject P D R a ⟶ coneObject P D T b)
    (h' : coneObject P D R a' ⟶ coneObject P D T b') : Prop :=
  h'.unop.base = h.unop.base ∧ h.unop.base.hom s = r ∧
    ∀ x, (show R from coneArrowTangent P D h' x) = r * (show R from coneArrowTangent P D h x)

end ConeCoordinateRead


/-- The affine coefficient functor is the actual relative Spec functor. -/
def specOver (B : CommRingCat.{0}) : (CommAlgCat.{0} B)ᵒᵖ ⥤ Over (Spec B) where
  obj C := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap B C.unop)))
  map {C D} f := Over.homMk (Spec.map (CommRingCat.ofHom f.unop.hom.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom f.unop.hom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap B D.unop)) =
        Spec.map (CommRingCat.ofHom (algebraMap B C.unop))
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact f.unop.hom.commutes x)
  map_id C := by apply Over.OverMorphism.ext; simp
  map_comp f g := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom g.unop.hom.toRingHom ≫
      CommRingCat.ofHom f.unop.hom.toRingHom) = _
    rw [Spec.map_comp]
    rfl

/-- The total cone is fixed by the full affine fibre category of the
relative Rees/tangent quotient on a genuine étale chart. -/
structure LocalIntrinsicConeView {F G : Stack S} (f : StackHom F G) where
  total : Stack S
  projection : StackHom total F
  chart : IntrinsicConeChart f
  diagram : letI := chart.geometry.algebra
    IntrinsicConeDiagram chart.presentation
  comparison : letI := chart.geometry.algebra
    AffineFibreCategory projection chart.geometry.source.U
      chart.geometry.sourcePoint ≌ (Grothendieck diagram.functor)ᵒᵖ
  overBase : letI := chart.geometry.algebra
    comparison.functor ⋙ (Grothendieck.forget diagram.functor).op ⋙
    specOver Γ(chart.geometry.source.U.left, ⊤) ⋙
      Over.map chart.geometry.source.U.left.isoSpec.inv ≅
        affineFibreForget projection chart.geometry.source.U chart.geometry.sourcePoint

@[implicit_reducible]
def restrictAlgebra {B C : Type} [CommRing B] [CommRing C] (β : B →+* C) :
    CommAlgCat.{0} C ⥤ CommAlgCat.{0} B where
  obj D := by
    letI : Algebra B D := ((algebraMap C D).comp β).toAlgebra
    exact CommAlgCat.of B D
  map {D E} h := by
    letI : Algebra B D := ((algebraMap C D).comp β).toAlgebra
    letI : Algebra B E := ((algebraMap C E).comp β).toAlgebra
    exact CommAlgCat.ofHom
      { toRingHom := h.hom.toRingHom
        commutes' b := h.hom.commutes (β b) }
  map_id D := by ext x; rfl
  map_comp f g := by ext x; rfl

section ConeMaps

open MathlibExt.AlgebraicGeometry.AffineConeAtlas
open MathlibExt.AlgebraicGeometry.AffineNormalConeMaps

variable {A B A' B' : Type} [CommRing A] [CommRing B] [Algebra A B]
  [CommRing A'] [CommRing B'] [Algebra A' B']
  (P : _root_.Algebra.Extension.{0} A B) (Q : _root_.Algebra.Extension.{0} A' B')
  (φ : P.Ring →+* Q.Ring) (β : B →+* B')
  (h : (algebraMap Q.Ring B').comp φ = β.comp (algebraMap P.Ring B))
  (N : NormalMap P Q φ β h) (D : IntrinsicConeDiagram Q) (E : IntrinsicConeDiagram P)

def coneMapComponent (τ : D.functor ⟶ restrictAlgebra β ⋙ E.functor)
    (C : CommAlgCat.{0} B') :
    IntrinsicConePoint Q C ⥤ IntrinsicConePoint P ((restrictAlgebra β).obj C) :=
  (eqToHom (D.object_eq C).symm ≫ τ.app C ≫
    eqToHom (E.object_eq ((restrictAlgebra β).obj C))).toFunctor

/-- Coordinates are the fixed coefficient/degree-one Rees map. Tangents
are the actual Kähler pullback, fixed on every pure differential tensor. -/
structure ConeDiagramMap where
  cotangent : P.CotangentSpace →ₛₗ[β] Q.CotangentSpace
  cotangent_normalized : ∀ (b : B) (r : P.Ring),
    cotangent (b ⊗ₜ[P.Ring] KaehlerDifferential.D A P.Ring r) =
      β b ⊗ₜ[Q.Ring] KaehlerDifferential.D A' Q.Ring (φ r)
  transformation : D.functor ⟶ restrictAlgebra β ⋙ E.functor
  objects : ∀ (C : CommAlgCat.{0} B') (a : IntrinsicConePoint Q C),
    ((coneMapComponent P Q β D E transformation C).obj a).map.toRingHom = a.map.toRingHom.comp N.map
  morphisms : ∀ (C : CommAlgCat.{0} B') (a b : IntrinsicConePoint Q C) (f : a ⟶ b)
    (x : P.CotangentSpace),
    ((coneMapComponent P Q β D E transformation C).map f).tangent x = f.tangent (cotangent x)

@[implicit_reducible]
def ConeDiagramMap.grothendieck (M : ConeDiagramMap P Q φ β h N D E) :
    Grothendieck D.functor ⥤ Grothendieck E.functor :=
  Grothendieck.map M.transformation ⋙ Grothendieck.pre E.functor (restrictAlgebra β)

end ConeMaps

def ConeChartGeometry.arrow {F G : Stack S} {f : StackHom F G} (c : ConeChartGeometry f) :
    (totalMap f).obj (point c.source.U c.sourcePoint) ⟶ point c.target.U c.target.point where
  base := c.map
  fiber := (c.square.commutes.app c.source.U).hom.app c.source.point ≫
    (c.targetModel.toPoint (point c.source.U
      ((StackCycleGeometry.component c.square.snd c.source.U).obj c.source.point))).fiber

/-- The actual global fibre reindexing along a native chart arrow. Its
objects keep the same cone point and postcompose the comparison arrow. -/
def affineFibreReindex {C F : Stack S} (π : StackHom C F)
    {U V : Over S} {x : F.Fibre U} {y : F.Fibre V} (a : point V y ⟶ point U x) :
    AffineFibreCategory π V y ⥤ AffineFibreCategory π U x where
  obj q := ⟨CostructuredArrow.mk (q.obj.hom ≫ a), q.property⟩
  map h := ObjectProperty.homMk (CostructuredArrow.homMk h.hom.left (by
    change (totalMap π).map h.hom.left ≫ (_ ≫ a) = _ ≫ a
    exact (Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ a) h.hom.w)))
  map_id q := by rfl
  map_comp h k := by rfl

/-- Local Rees/tangent data for a specified global cone and specified
actual smooth presentation. The comparison alone is only a local view. -/
structure ConeChartView {F G C : Stack S} {f : StackHom F G}
    (π : StackHom C F) (c : IntrinsicConeChart f) where
  diagram : letI := c.geometry.algebra
    IntrinsicConeDiagram c.presentation
  comparison : letI := c.geometry.algebra
    AffineFibreCategory π c.geometry.source.U c.geometry.sourcePoint ≌
      (Grothendieck diagram.functor)ᵒᵖ
  overBase : letI := c.geometry.algebra
    comparison.functor ⋙ (Grothendieck.forget diagram.functor).op ⋙
      specOver Γ(c.geometry.source.U.left, ⊤) ⋙ Over.map c.geometry.source.U.left.isoSpec.inv ≅
        affineFibreForget π c.geometry.source.U c.geometry.sourcePoint

def ConeChartView.inverseSchemes {F G C : Stack S} {f : StackHom F G}
    {π : StackHom C F} {c : IntrinsicConeChart f} (V : ConeChartView π c) :
    letI := c.geometry.algebra
    V.comparison.inverse ⋙ affineFibreForget π c.geometry.source.U c.geometry.sourcePoint ⋙
      Over.forget c.geometry.source.U.left ≅
    (Grothendieck.forget V.diagram.functor).op ⋙ specOver Γ(c.geometry.source.U.left, ⊤) ⋙
      Over.map c.geometry.source.U.left.isoSpec.inv ⋙ Over.forget c.geometry.source.U.left := by
  letI := c.geometry.algebra
  exact Functor.isoWhiskerRight
    ((Functor.isoWhiskerLeft V.comparison.inverse V.overBase).symm ≪≫
      Functor.isoWhiskerRight V.comparison.counitIso
        ((Grothendieck.forget V.diagram.functor).op ⋙ specOver Γ(c.geometry.source.U.left, ⊤) ⋙
          Over.map c.geometry.source.U.left.isoSpec.inv)) (Over.forget c.geometry.source.U.left)

/-- A refinement is an actual native source/target chart arrow with the
literal ambient-ring lift. Both Čech projections are such arrows; their
point isomorphisms are retained in the CoGrothendieck arrows. -/
structure ConeChartRefinement {F G : Stack S} {f : StackHom F G}
    (c d : IntrinsicConeChart f) where
  source : point d.geometry.source.U d.geometry.sourcePoint ⟶
    point c.geometry.source.U c.geometry.sourcePoint
  target : point d.geometry.target.U d.geometry.target.point ⟶
    point c.geometry.target.U c.geometry.target.point
  overMorphism : (totalMap f).map source ≫ c.geometry.arrow = d.geometry.arrow ≫ target
  ambient : letI := c.geometry.algebra; letI := d.geometry.algebra
    c.presentation.Ring →+* d.presentation.Ring
  quotient : letI := c.geometry.algebra; letI := d.geometry.algebra
    (algebraMap d.presentation.Ring Γ(d.geometry.source.U.left, ⊤)).comp ambient =
      source.base.left.appTop.hom.comp
        (algebraMap c.presentation.Ring Γ(c.geometry.source.U.left, ⊤))
  coefficient : letI := c.geometry.algebra; letI := d.geometry.algebra
    ∀ r : Γ(c.geometry.target.U.left, ⊤),
      ambient (algebraMap Γ(c.geometry.target.U.left, ⊤) c.presentation.Ring r) =
        algebraMap Γ(d.geometry.target.U.left, ⊤) d.presentation.Ring
          (target.base.left.appTop.hom r)

structure ConeViewComparison {F G C : Stack S} {f : StackHom F G}
    {π : StackHom C F} {c d : IntrinsicConeChart f}
    (Vc : ConeChartView π c) (Vd : ConeChartView π d) (r : ConeChartRefinement c d) where
  normalMap : letI := c.geometry.algebra; letI := d.geometry.algebra
    MathlibExt.AlgebraicGeometry.AffineNormalConeMaps.NormalMap c.presentation d.presentation
      r.ambient r.source.base.left.appTop.hom r.quotient
  diagramMap : letI := c.geometry.algebra; letI := d.geometry.algebra
    ConeDiagramMap c.presentation d.presentation r.ambient r.source.base.left.appTop.hom
      r.quotient normalMap Vd.diagram Vc.diagram
  normalized : letI := c.geometry.algebra; letI := d.geometry.algebra
    Vd.comparison.functor ⋙ diagramMap.grothendieck.op ≅
      affineFibreReindex π r.source ⋙ Vc.comparison.functor

def ConeViewComparison.coefficientCell {F G C : Stack S} {f : StackHom F G}
    {π : StackHom C F} {c d : IntrinsicConeChart f}
    {Vc : ConeChartView π c} {Vd : ConeChartView π d} {r : ConeChartRefinement c d}
    (T : ConeViewComparison Vc Vd r) :
    letI := c.geometry.algebra; letI := d.geometry.algebra
    T.diagramMap.grothendieck.op ≅
      Vd.comparison.inverse ⋙ affineFibreReindex π r.source ⋙ Vc.comparison.functor := by
  letI := c.geometry.algebra; letI := d.geometry.algebra
  exact (Functor.isoWhiskerRight Vd.comparison.counitIso T.diagramMap.grothendieck.op).symm ≪≫
    Functor.isoWhiskerLeft Vd.comparison.inverse T.normalized

def ConeViewComparison.cellTangent {F G C : Stack S} {f : StackHom F G}
    {π : StackHom C F} {c d : IntrinsicConeChart f}
    {Vc : ConeChartView π c} {Vd : ConeChartView π d} {r : ConeChartRefinement c d}
    (T : ConeViewComparison Vc Vd r) :
    letI := c.geometry.algebra; letI := d.geometry.algebra
    ∀ (B : CommAlgCat.{0} Γ(d.geometry.source.U.left, ⊤)), IntrinsicConePoint d.presentation B →
      c.presentation.CotangentSpace → B := by
  letI := c.geometry.algebra; letI := d.geometry.algebra
  intro B a x
  exact coneArrowTangent c.presentation Vc.diagram
    (T.coefficientCell.hom.app (coneObject d.presentation Vd.diagram B a)) x

/-- The actual transition cell has the native coefficient map and is
zero/homogeneous in Rees coordinates. Cocycle coherence alone would allow
constant or quadratic tangent torsors; these conditions constrain the
actual comparison components, not a replacement local isomorphism. -/
structure ConeViewTransition {F G C : Stack S} {f : StackHom F G}
    {π : StackHom C F} {c d : IntrinsicConeChart f}
    (Vc : ConeChartView π c) (Vd : ConeChartView π d) (r : ConeChartRefinement c d)
    extends ConeViewComparison Vc Vd r where
  coefficient : letI := c.geometry.algebra; letI := d.geometry.algebra
    ∀ (B : CommAlgCat.{0} Γ(d.geometry.source.U.left, ⊤)) (a : IntrinsicConePoint d.presentation B),
      let q := coneObject d.presentation Vd.diagram B a
      Spec.map (CommRingCat.ofHom
        (toConeViewComparison.coefficientCell.hom.app q).unop.base.hom.toRingHom) ≫
          (Vc.overBase.hom.app ((affineFibreReindex π r.source).obj (Vd.comparison.inverse.obj q))).left =
        (Vd.inverseSchemes.app q).inv
  zero : letI := c.geometry.algebra; letI := d.geometry.algebra
    ∀ (B : CommAlgCat.{0} Γ(d.geometry.source.U.left, ⊤)) (a : IntrinsicConePoint d.presentation B),
      IsZeroConePoint d.presentation a → ∀ x,
      toConeViewComparison.cellTangent B a x = 0
  homothety : letI := c.geometry.algebra; letI := d.geometry.algebra
    ∀ (B : CommAlgCat.{0} Γ(d.geometry.source.U.left, ⊤)) (s : B)
      (a a' : IntrinsicConePoint d.presentation B), IsScaledConePoint d.presentation s a a' → ∀ x,
      toConeViewComparison.cellTangent B a' x = s * toConeViewComparison.cellTangent B a x

def ConeViewTransition.coefficientCell {F G C : Stack S} {f : StackHom F G}
    {π : StackHom C F} {c d : IntrinsicConeChart f}
    {Vc : ConeChartView π c} {Vd : ConeChartView π d} {r : ConeChartRefinement c d}
    (T : ConeViewTransition Vc Vd r) := T.toConeViewComparison.coefficientCell

/-- The GLOBAL intrinsic cone: views on every actual smooth presentation
and all actual compatible refinements. The fixed global fibre reindexing
is prescribed by Rees coefficients, degree one and Kähler pure tensors.
This excludes a twisted global cone with one matching local chart. -/
structure IntrinsicConeModel {F G : Stack S} (f : StackHom F G)
    extends LocalIntrinsicConeView f where
  views : ∀ c : IntrinsicConeChart f, ConeChartView projection c
  chosen : views chart =
    { diagram := toLocalIntrinsicConeView.diagram
      comparison := toLocalIntrinsicConeView.comparison
      overBase := toLocalIntrinsicConeView.overBase }
  transitions : ∀ (c d : IntrinsicConeChart f) (r : ConeChartRefinement c d),
    ConeViewTransition (views c) (views d) r
  identity : ∀ (c : IntrinsicConeChart f) (r : ConeChartRefinement c c),
    r.source = 𝟙 _ → r.target = 𝟙 _ →
    (letI := c.geometry.algebra; r.ambient = RingHom.id _) →
    letI := c.geometry.algebra
    ∃ (hc : (transitions c c r).diagramMap.grothendieck.op = 𝟭 _)
      (hr : affineFibreReindex projection r.source = 𝟭 _),
      (transitions c c r).normalized.hom = eqToHom (by rw [hc, hr]; rfl)
  composition : ∀ (c d e : IntrinsicConeChart f)
    (r : ConeChartRefinement c d) (s : ConeChartRefinement d e) (t : ConeChartRefinement c e),
    t.source = s.source ≫ r.source → t.target = s.target ≫ r.target →
    (letI := c.geometry.algebra; letI := d.geometry.algebra; letI := e.geometry.algebra
      t.ambient = s.ambient.comp r.ambient) →
    letI := c.geometry.algebra; letI := d.geometry.algebra; letI := e.geometry.algebra
    ∃ (hc : (transitions c e t).diagramMap.grothendieck.op =
        (transitions d e s).diagramMap.grothendieck.op ⋙
          (transitions c d r).diagramMap.grothendieck.op)
      (hr : affineFibreReindex projection t.source =
        affineFibreReindex projection s.source ⋙ affineFibreReindex projection r.source),
      (transitions c e t).normalized.hom =
        eqToHom (congrArg (fun k => (views e).comparison.functor ⋙ k) hc) ≫
          Functor.whiskerRight (transitions d e s).normalized.hom
            (transitions c d r).diagramMap.grothendieck.op ≫
          Functor.whiskerLeft (affineFibreReindex projection s.source)
            (transitions c d r).normalized.hom ≫
          eqToHom (congrArg (fun k => k ⋙ (views c).comparison.functor) hr.symm)

def affinePointToTotal (X : Stack S) : AffinePoint X ⥤ Total X :=
  (show ObjectProperty (Total X) from fun q => IsAffine q.base.left).ι

def affineFibreToTotal {C F : Stack S} (π : StackHom C F) (T : Over S) (x : F.Fibre T) :
    AffineFibreCategory π T x ⥤ Total C :=
  (show ObjectProperty (FibreCategory π T x) from fun q => IsAffine q.left.base.left).ι ⋙
    CostructuredArrow.proj (totalMap π) (point T x)

def affineFibrePoint {C F : Stack S} (π : StackHom C F) (T : Over S) (x : F.Fibre T) :
    AffineFibreCategory π T x ⥤ AffinePoint C where
  obj q := ⟨q.obj.left, q.property⟩
  map h := ObjectProperty.homMk h.hom.left
  map_id q := by rfl
  map_comp h k := by rfl

def ConeViewTransition.pointCell {F G C : Stack S} {f : StackHom F G}
    {π : StackHom C F} {c d : IntrinsicConeChart f}
    {Vc : ConeChartView π c} {Vd : ConeChartView π d} {r : ConeChartRefinement c d}
    (T : ConeViewTransition Vc Vd r) :
    letI := c.geometry.algebra; letI := d.geometry.algebra
    T.diagramMap.grothendieck.op ⋙ Vc.comparison.inverse ⋙
      affineFibrePoint π c.geometry.source.U c.geometry.sourcePoint ≅
    Vd.comparison.inverse ⋙ affineFibrePoint π d.geometry.source.U d.geometry.sourcePoint := by
  letI := c.geometry.algebra; letI := d.geometry.algebra
  exact Functor.isoWhiskerRight
    (Functor.isoWhiskerRight T.coefficientCell Vc.comparison.inverse ≪≫
      Functor.isoWhiskerLeft (Vd.comparison.inverse ⋙ affineFibreReindex π r.source)
        Vc.comparison.unitIso.symm)
    (affineFibrePoint π c.geometry.source.U c.geometry.sourcePoint)

def LinearBundleDiagram.pointValue {X : Stack S} {n : ℤ} (D : LinearBundleDiagram X n)
    (q : Pseudofunctor.CoGrothendieck D.pseudofunctor) : (D.modules q.base).degreeOne :=
  ((eqToHom (D.objects q.base)).toFunctor.obj q.fiber).value

/-- The actual fibre of a CoGroth arrow, including descent on base arrows. -/
def LinearBundleDiagram.arrowTranslation {X : Stack S} {n : ℤ} (D : LinearBundleDiagram X n)
    {q r : Pseudofunctor.CoGrothendieck D.pseudofunctor} (h : q ⟶ r) :
    (D.modules q.base).degreeZero :=
  ((eqToHom (D.objects q.base)).toFunctor.map h.fiber).translation

/-- This is the actual global image; no chart comparison into E.quotient
is used to compute either its objects or its morphisms. -/
def actualConeImage {F G : Stack S} {f : StackHom F G}
    (C : IntrinsicConeModel f) (E : VectorBundleStack F) (m : StackHom C.total E.total)
    (c : IntrinsicConeChart f) :
    letI := c.geometry.algebra
    (Grothendieck (C.views c).diagram.functor)ᵒᵖ ⥤
      Pseudofunctor.CoGrothendieck E.linear.diagram.pseudofunctor := by
  letI := c.geometry.algebra
  exact (C.views c).comparison.inverse ⋙
    affineFibrePoint C.projection c.geometry.source.U c.geometry.sourcePoint ⋙
      affineMap m ⋙ E.linear.comparison.functor

def actualConeScheme {F G : Stack S} {f : StackHom F G}
    (C : IntrinsicConeModel f) (E : VectorBundleStack F) (m : StackHom C.total E.total)
    (c : IntrinsicConeChart f) :
    letI := c.geometry.algebra
    ∀ q : (Grothendieck (C.views c).diagram.functor)ᵒᵖ,
      (pointScheme F).obj ((actualConeImage C E m c).obj q).base ≅ Spec (.of q.unop.base) := by
  letI := c.geometry.algebra
  intro q
  exact (pointScheme F).mapIso
    (E.linear.overBase.app ((affineMap m).obj
      ((affineFibrePoint C.projection c.geometry.source.U c.geometry.sourcePoint).obj
        ((C.views c).comparison.inverse.obj q)))) ≪≫ (C.views c).inverseSchemes.app q

def actualConeScalar {F G : Stack S} {f : StackHom F G}
    (C : IntrinsicConeModel f) (E : VectorBundleStack F) (m : StackHom C.total E.total)
    (c : IntrinsicConeChart f) :
    letI := c.geometry.algebra
    ∀ q : (Grothendieck (C.views c).diagram.functor)ᵒᵖ,
      q.unop.base →+* (rings F).obj (op ((actualConeImage C E m c).obj q).base) := by
  letI := c.geometry.algebra
  intro q
  exact ((Scheme.ΓSpecIso (.of q.unop.base)).inv ≫
    Scheme.Γ.map (actualConeScheme C E m c q).hom.op).hom

def actualConeToPoint {F G : Stack S} {f : StackHom F G}
    (C : IntrinsicConeModel f) (E : VectorBundleStack F) (m : StackHom C.total E.total)
    (p : totalMap m ⋙ totalMap E.projection ≅ totalMap C.projection) (c : IntrinsicConeChart f) :
    letI := c.geometry.algebra
    ∀ q : (Grothendieck (C.views c).diagram.functor)ᵒᵖ,
      ((actualConeImage C E m c).obj q).base.obj ⟶
        point c.geometry.source.U c.geometry.sourcePoint := by
  letI := c.geometry.algebra
  intro q
  let a := (C.views c).comparison.inverse.obj q
  exact (E.linear.overBase.hom.app ((affineMap m).obj
    ((affineFibrePoint C.projection c.geometry.source.U c.geometry.sourcePoint).obj a))).hom ≫
      p.hom.app a.obj.left ≫ a.obj.hom

/-- Only the native coefficient/base transport is admitted. For a fixed
scheme map its point arrow over the chart is unique; a torsor-valued local
comparison cannot be substituted for the actual global m-image. -/
structure NativePointTransport {F : Stack S} (a b : AffinePoint F) (R : CommRingCat.{0})
    (sa : (pointScheme F).obj a ≅ Spec R) (sb : (pointScheme F).obj b ≅ Spec R)
    {U : Over S} {x : F.Fibre U} (pa : a.obj ⟶ point U x) (pb : b.obj ⟶ point U x) where
  iso : a ≅ b
  scheme : iso.hom.hom.base.left = sa.hom ≫ sb.inv
  point : iso.hom.hom ≫ pb = pa

def actualRefinementImage {F G : Stack S} {f : StackHom F G}
    (C : IntrinsicConeModel f) (E : VectorBundleStack F) (m : StackHom C.total E.total)
    (c d : IntrinsicConeChart f) (r : ConeChartRefinement c d) :
    letI := c.geometry.algebra; letI := d.geometry.algebra
    (C.transitions c d r).diagramMap.grothendieck.op ⋙ actualConeImage C E m c ≅
      actualConeImage C E m d := by
  letI := c.geometry.algebra; letI := d.geometry.algebra
  exact Functor.isoWhiskerRight (C.transitions c d r).pointCell
    (affineMap m ⋙ E.linear.comparison.functor)

structure ChartActualConicality {F : Stack S} {n : ℤ} (M : LinearBundleDiagram F n)
    {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    (P : _root_.Algebra.Extension.{0} A B) (D : IntrinsicConeDiagram P)
    (image : (Grothendieck D.functor)ᵒᵖ ⥤ Pseudofunctor.CoGrothendieck M.pseudofunctor)
    (schemes : ∀ q, (pointScheme F).obj (image.obj q).base ≅ Spec (.of q.unop.base))
    (scalar : ∀ q, q.unop.base →+* (rings F).obj (op (image.obj q).base))
    {U : Over S} {x : F.Fibre U} (toPoint : ∀ q, (image.obj q).base.obj ⟶ point U x) where
  transport : ∀ (R : CommAlgCat.{0} B) (a a' : IntrinsicConePoint P R),
    let q := coneObject P D R a
    let q' := coneObject P D R a'
    NativePointTransport (image.obj q).base (image.obj q').base (.of R)
      (schemes q) (schemes q') (toPoint q) (toPoint q')
  zeroObjects : ∀ (R : CommAlgCat.{0} B) (a : IntrinsicConePoint P R), IsZeroConePoint P a →
    M.pointValue (image.obj (coneObject P D R a)) = 0
  scaledObjects : ∀ (R : CommAlgCat.{0} B) (s : R) (a a' : IntrinsicConePoint P R),
    IsScaledConePoint P s a a' →
    (M.restriction (transport R a a').iso.hom).degreeOne (M.pointValue (image.obj (coneObject P D R a'))) =
      scalar (coneObject P D R a) s • M.pointValue (image.obj (coneObject P D R a))
  zeroArrows : ∀ (R T : CommAlgCat.{0} B) (a : IntrinsicConePoint P R) (b : IntrinsicConePoint P T)
    (h : coneObject P D R a ⟶ coneObject P D T b),
    IsZeroConePoint P a → IsZeroConePoint P b → (∀ x, coneArrowTangent P D h x = 0) →
      M.arrowTranslation (image.map h) = 0
  scaledArrows : ∀ (R T : CommAlgCat.{0} B) (s : R) (t : T)
    (a a' : IntrinsicConePoint P R) (b b' : IntrinsicConePoint P T)
    (h : coneObject P D R a ⟶ coneObject P D T b)
    (h' : coneObject P D R a' ⟶ coneObject P D T b'),
    IsScaledConePoint P s a a' → IsScaledConePoint P t b b' → IsScaledConeArrow P D s t h h' →
      (M.restriction (transport R a a').iso.hom).degreeZero (M.arrowTranslation (image.map h')) =
        scalar (coneObject P D R a) s • M.arrowTranslation (image.map h)

structure RefinementActualConicality {F : Stack S} {n : ℤ} (M : LinearBundleDiagram F n)
    {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    (P : _root_.Algebra.Extension.{0} A B) (D : IntrinsicConeDiagram P)
    (left right : (Grothendieck D.functor)ᵒᵖ ⥤ Pseudofunctor.CoGrothendieck M.pseudofunctor)
    (cell : left ≅ right)
    (schemes : ∀ q, (pointScheme F).obj (left.obj q).base ≅ Spec (.of q.unop.base))
    (scalar : ∀ q, q.unop.base →+* (rings F).obj (op (left.obj q).base))
    {U : Over S} {x : F.Fibre U} (toPoint : ∀ q, (left.obj q).base.obj ⟶ point U x) where
  transport : ∀ (R : CommAlgCat.{0} B) (a a' : IntrinsicConePoint P R),
    let q := coneObject P D R a
    let q' := coneObject P D R a'
    NativePointTransport (left.obj q).base (left.obj q').base (.of R)
      (schemes q) (schemes q') (toPoint q) (toPoint q')
  zero : ∀ (R : CommAlgCat.{0} B) (a : IntrinsicConePoint P R), IsZeroConePoint P a →
    M.arrowTranslation (cell.hom.app (coneObject P D R a)) = 0
  homothety : ∀ (R : CommAlgCat.{0} B) (s : R) (a a' : IntrinsicConePoint P R),
    IsScaledConePoint P s a a' →
      (M.restriction (transport R a a').iso.hom).degreeZero
        (M.arrowTranslation (cell.hom.app (coneObject P D R a'))) =
        scalar (coneObject P D R a) s • M.arrowTranslation (cell.hom.app (coneObject P D R a))

def actualRefinementScheme {F G : Stack S} {f : StackHom F G}
    (C : IntrinsicConeModel f) (E : VectorBundleStack F) (m : StackHom C.total E.total)
    (c d : IntrinsicConeChart f) (r : ConeChartRefinement c d) :
    letI := c.geometry.algebra; letI := d.geometry.algebra
    ∀ q : (Grothendieck (C.views d).diagram.functor)ᵒᵖ,
      (pointScheme F).obj (((C.transitions c d r).diagramMap.grothendieck.op ⋙
        actualConeImage C E m c).obj q).base ≅ Spec (.of q.unop.base) := by
  letI := c.geometry.algebra; letI := d.geometry.algebra
  intro q
  exact actualConeScheme C E m c ((C.transitions c d r).diagramMap.grothendieck.op.obj q)

def actualRefinementScalar {F G : Stack S} {f : StackHom F G}
    (C : IntrinsicConeModel f) (E : VectorBundleStack F) (m : StackHom C.total E.total)
    (c d : IntrinsicConeChart f) (r : ConeChartRefinement c d) :
    letI := c.geometry.algebra; letI := d.geometry.algebra
    ∀ q : (Grothendieck (C.views d).diagram.functor)ᵒᵖ,
      q.unop.base →+* (rings F).obj (op (((C.transitions c d r).diagramMap.grothendieck.op ⋙
        actualConeImage C E m c).obj q).base) := by
  letI := c.geometry.algebra; letI := d.geometry.algebra
  intro q
  exact actualConeScalar C E m c ((C.transitions c d r).diagramMap.grothendieck.op.obj q)

def actualRefinementToPoint {F G : Stack S} {f : StackHom F G}
    (C : IntrinsicConeModel f) (E : VectorBundleStack F) (m : StackHom C.total E.total)
    (p : totalMap m ⋙ totalMap E.projection ≅ totalMap C.projection)
    (c d : IntrinsicConeChart f) (r : ConeChartRefinement c d) :
    letI := c.geometry.algebra; letI := d.geometry.algebra
    ∀ q : (Grothendieck (C.views d).diagram.functor)ᵒᵖ,
      (((C.transitions c d r).diagramMap.grothendieck.op ⋙ actualConeImage C E m c).obj q).base.obj ⟶
        point c.geometry.source.U c.geometry.sourcePoint := by
  letI := c.geometry.algebra; letI := d.geometry.algebra
  intro q
  exact actualConeToPoint C E m p c ((C.transitions c d r).diagramMap.grothendieck.op.obj q)

/-- The helper records have no independent observation functor here:
every argument is fixed by the actual m, the global E.linear comparison,
the native Γ(Spec R) transport, and actual source refinement cells. -/
structure ActualGlobalConicality {F G : Stack S} {f : StackHom F G}
    (C : IntrinsicConeModel f) (E : VectorBundleStack F) (m : StackHom C.total E.total)
    (p : totalMap m ⋙ totalMap E.projection ≅ totalMap C.projection) where
  charts : ∀ c : IntrinsicConeChart f,
    letI := c.geometry.algebra
    ChartActualConicality E.linear.diagram c.presentation (C.views c).diagram
      (actualConeImage C E m c) (actualConeScheme C E m c) (actualConeScalar C E m c)
      (actualConeToPoint C E m p c)
  refinements : ∀ (c d : IntrinsicConeChart f) (r : ConeChartRefinement c d),
    letI := c.geometry.algebra; letI := d.geometry.algebra
    RefinementActualConicality E.linear.diagram d.presentation (C.views d).diagram
      ((C.transitions c d r).diagramMap.grothendieck.op ⋙ actualConeImage C E m c)
      (actualConeImage C E m d) (actualRefinementImage C E m c d r)
      (actualRefinementScheme C E m c d r) (actualRefinementScalar C E m c d r)
      (actualRefinementToPoint C E m p c d r)

/-- The actual affine coefficient point of a fixed scheme-valued object. -/
def ringPoint {X : Stack S} (U : Over S) [IsAffine U.left] (x : X.Fibre U)
    (B : CommAlgCat.{0} Γ(U.left, ⊤)) : AffinePoint X :=
  ⟨point (Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(U.left, ⊤) B)) ≫ U.left.isoSpec.inv ≫ U.hom))
    ((pull X (Over.homMk
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(U.left, ⊤) B)) ≫ U.left.isoSpec.inv)
      (by simp only [Category.assoc]; rfl))).obj x), by
        change IsAffine (Spec (.of B)); infer_instance⟩

def ringPointArrow {X : Stack S} (U : Over S) [IsAffine U.left] (x : X.Fibre U)
    (B : CommAlgCat.{0} Γ(U.left, ⊤)) : (ringPoint U x B).obj ⟶ point U x where
  base := Over.homMk
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(U.left, ⊤) B)) ≫ U.left.isoSpec.inv)
    (by rfl)
  fiber := 𝟙 _


section ConicalCoordinates

open MathlibExt.AlgebraicGeometry.AffineConeAtlas


def bundleConeComponent {F G : Stack S} {f : StackHom F G} (E : VectorBundleStack F)
    (c : IntrinsicConeChart f) (D : letI := c.geometry.algebra; IntrinsicConeDiagram c.presentation)
    (b : (CommAlgCat.{0} Γ(c.geometry.source.U.left, ⊤))ᵒᵖ ⥤ AffinePoint E.base.stack)
    (τ : letI := c.geometry.algebra; D.functor ⟶ b.rightOp ⋙ E.quotient.diagram.functor)
    (B : CommAlgCat.{0} Γ(c.geometry.source.U.left, ⊤)) :
    letI := c.geometry.algebra
    IntrinsicConePoint c.presentation B ⥤
      AdditiveQuotient (R := (rings E.base.stack).obj (op (b.obj (op B))))
        (E.differential.linear.app (op (b.obj (op B)))).hom :=
  by
    letI := c.geometry.algebra
    exact (eqToHom (D.object_eq B).symm ≫ τ.app B ≫
      eqToHom (E.quotient.diagram.object_eq (op (b.obj (op B))))).toFunctor

/-- Native coefficient scalars in the actual FP-module section ring. -/
def ringPointScalar {X : Stack S} {U : Over S} [IsAffine U.left] {x : X.Fibre U}
    {b : (CommAlgCat.{0} Γ(U.left, ⊤))ᵒᵖ ⥤ AffinePoint X}
    (objects : ∀ B, b.obj (op B) = ringPoint U x B)
    (B : CommAlgCat.{0} Γ(U.left, ⊤)) : B →+* (rings X).obj (op (b.obj (op B))) :=
  ((Scheme.ΓSpecIso (.of B)).inv ≫ eqToHom
    (show (rings X).obj (op (b.obj (op B))) = Γ(Spec (.of B), ⊤) by
      rw [objects B]; rfl).symm).hom

end ConicalCoordinates

/-- Conicality belongs to the ACTUAL global map in the fixed global
models. The source projection iso is the native based 2-cell. Object,
coefficient-arrow and refinement-cell tests are read directly in E.linear;
no local comparison isomorphism can replace the global map. -/
structure ConicalEmbeddingData {F G : Stack S} {f : StackHom F G}
    (C : IntrinsicConeModel f) (E : VectorBundleStack F) (m : StackHom C.total E.total)
    (overBase : StackVectorBundles.TwoIso (Pseudofunctor.StrongTrans.vcomp m E.projection)
      C.projection) where
  sourceProjection : totalMap m ⋙ totalMap E.projection ≅ totalMap C.projection
  sourceProjection_base : ∀ q : Total C.total, (sourceProjection.hom.app q).base = 𝟙 q.base
  sourceProjection_fibre : ∀ q : Total C.total,
    HEq (sourceProjection.hom.app q).fiber
      ((overBase.app q.base).hom.app q.fiber ≫
        (F.toPseudofunctor.mapId (.mk (op q.base))).inv.toNatTrans.app
          ((StackCycleGeometry.component C.projection q.base).obj q.fiber))
  actualGlobal : ActualGlobalConicality C E m sourceProjection

structure ConeEmbedding {F G : Stack S} {f : StackHom F G}
    (C : IntrinsicConeModel f) (E : VectorBundleStack F) where
  map : StackHom C.total E.total
  closed : StackFibreModels.IsClosed map
  overBase : StackVectorBundles.TwoIso (Pseudofunctor.StrongTrans.vcomp map E.projection) C.projection
  conical : ConicalEmbeddingData C E map overBase

/-- Manolache's Condition (star), retaining the fixed closed embedding. -/
structure ConditionStar {F G : Stack S} (f : StackHom F G) (E : VectorBundleStack F) where
  dmType : StackFibreModels.IsDMType f
  cone : IntrinsicConeModel f
  embedding : ConeEmbedding cone E

structure StackEquivalence (X Y : Stack S) where
  hom : StackHom X Y
  inv : StackHom Y X
  unit : StackVectorBundles.TwoIso (Pseudofunctor.StrongTrans.vcomp hom inv)
    (Pseudofunctor.StrongTrans.id X.toPseudofunctor)
  counit : StackVectorBundles.TwoIso (Pseudofunctor.StrongTrans.vcomp inv hom)
    (Pseudofunctor.StrongTrans.id Y.toPseudofunctor)

/-- In the finite-type Noetherian scope, a closed immersion is regular
of codimension c precisely when its actual normal cone is this rank-c
vector bundle. No refined Gysin conclusion is assumed here. -/
structure RegularNormalModel {X Y : Stack S} (f : StackHom X Y) (c : ℕ) where
  closed : StackFibreModels.IsClosed f
  cone : IntrinsicConeModel f
  bundle : VectorBundle X
  rank_eq : bundle.rank = c
  comparison : StackEquivalence cone.total bundle.total
  overBase : StackVectorBundles.TwoIso
    (Pseudofunctor.StrongTrans.vcomp comparison.hom bundle.projection) cone.projection


def affineConeMap {F G F' G' : Stack S} {f : StackHom F G} {f' : StackHom F' G'}
    (p : StackHom F' F) (C' : IntrinsicConeModel f') (C : IntrinsicConeModel f)
    (m : StackHom C'.total C.total)
    (e : totalMap m ⋙ totalMap C.projection ≅ totalMap C'.projection ⋙ totalMap p)
    (a : (totalMap p).obj (point C'.chart.geometry.source.U C'.chart.geometry.sourcePoint) ⟶
      point C.chart.geometry.source.U C.chart.geometry.sourcePoint) :
    AffineFibreCategory C'.projection C'.chart.geometry.source.U C'.chart.geometry.sourcePoint ⥤
      AffineFibreCategory C.projection C.chart.geometry.source.U C.chart.geometry.sourcePoint where
  obj q := ⟨CostructuredArrow.mk
    (e.hom.app q.obj.left ≫ (totalMap p).map q.obj.hom ≫ a), q.property⟩
  map {q r} k := ObjectProperty.homMk (CostructuredArrow.homMk ((totalMap m).map k.hom.left) (by
    have hn := e.hom.naturality k.hom.left
    dsimp only [Functor.comp_map] at hn
    change (totalMap C.projection).map ((totalMap m).map k.hom.left) ≫
      (e.hom.app r.obj.left ≫ (totalMap p).map r.obj.hom ≫ a) = _
    rw [← Category.assoc, ← Category.assoc, hn]
    simp only [Category.assoc, ← Functor.map_comp, k.hom.w]
    rfl))
  map_id q := by
    apply ObjectProperty.hom_ext
    apply CostructuredArrow.hom_ext
    exact (totalMap m).map_id _
  map_comp k l := by
    apply ObjectProperty.hom_ext
    apply CostructuredArrow.hom_ext
    exact (totalMap m).map_comp _ _

/-- The canonical relative cone base-change map, fixed on all chart
objects and arrows by the actual Rees and Kähler maps. -/
structure ConeBaseChangeData {F G F' G' : Stack S} (f' : StackHom F' G') (f : StackHom F G)
    (p : StackHom F' F) (q : StackHom G' G)
    (C' : IntrinsicConeModel f') (C : IntrinsicConeModel f) where
  commutes : StackVectorBundles.TwoIso (Pseudofunctor.StrongTrans.vcomp p f)
    (Pseudofunctor.StrongTrans.vcomp f' q)
  cartesian : ∀ T : Over S,
    ((CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
      (StackCycleGeometry.component f T) (StackCycleGeometry.component q T) _).obj
      ⟨StackCycleGeometry.component p T, StackCycleGeometry.component f' T,
        commutes.app T⟩).IsEquivalence
  squareTotal : totalMap p ⋙ totalMap f ≅ totalMap f' ⋙ totalMap q
  squareTotal_base : ∀ x : Total F', (squareTotal.hom.app x).base = 𝟙 x.base
  squareTotal_fibre : ∀ x : Total F',
    HEq (squareTotal.hom.app x).fiber
      ((commutes.app x.base).hom.app x.fiber ≫
        (G.toPseudofunctor.mapId (.mk (op x.base))).inv.toNatTrans.app
          ((StackCycleGeometry.component (Pseudofunctor.StrongTrans.vcomp f' q) x.base).obj x.fiber))
  map : StackHom C'.total C.total
  pullback : TwoCartesianSquare C.projection p
  intoPullback : StackHom C'.total pullback.apex
  closed : StackFibreModels.IsClosed intoPullback
  pullbackCone : StackVectorBundles.TwoIso
    (Pseudofunctor.StrongTrans.vcomp intoPullback pullback.fst) map
  pullbackBase : StackVectorBundles.TwoIso
    (Pseudofunctor.StrongTrans.vcomp intoPullback pullback.snd) C'.projection
  overBase : StackVectorBundles.TwoIso (Pseudofunctor.StrongTrans.vcomp map C.projection)
    (Pseudofunctor.StrongTrans.vcomp C'.projection p)
  overTotal : totalMap map ⋙ totalMap C.projection ≅ totalMap C'.projection ⋙ totalMap p
  overTotalBase : ∀ x : Total C'.total, (overTotal.hom.app x).base = 𝟙 x.base
  overTotal_fibre : ∀ x : Total C'.total,
    HEq (overTotal.hom.app x).fiber
      ((overBase.app x.base).hom.app x.fiber ≫
        (F.toPseudofunctor.mapId (.mk (op x.base))).inv.toNatTrans.app
          ((StackCycleGeometry.component (Pseudofunctor.StrongTrans.vcomp C'.projection p) x.base).obj x.fiber))
  sourceChart : (totalMap p).obj
    (point C'.chart.geometry.source.U C'.chart.geometry.sourcePoint) ⟶
      point C.chart.geometry.source.U C.chart.geometry.sourcePoint
  targetChart : (totalMap q).obj
    (point C'.chart.geometry.target.U C'.chart.geometry.target.point) ⟶
      point C.chart.geometry.target.U C.chart.geometry.target.point
  charts_overSquare : (totalMap f).map sourceChart ≫ C.chart.geometry.arrow =
    squareTotal.hom.app (point C'.chart.geometry.source.U C'.chart.geometry.sourcePoint) ≫
      (totalMap q).map C'.chart.geometry.arrow ≫ targetChart
  ambient : letI := C.chart.geometry.algebra; letI := C'.chart.geometry.algebra
    C.chart.presentation.Ring →+* C'.chart.presentation.Ring
  quotient : letI := C.chart.geometry.algebra; letI := C'.chart.geometry.algebra
    (algebraMap C'.chart.presentation.Ring Γ(C'.chart.geometry.source.U.left, ⊤)).comp ambient =
      sourceChart.base.left.appTop.hom.comp
        (algebraMap C.chart.presentation.Ring Γ(C.chart.geometry.source.U.left, ⊤))
  ambient_normalized : letI := C.chart.geometry.algebra; letI := C'.chart.geometry.algebra
    ∀ r : Γ(C.chart.geometry.target.U.left, ⊤),
      ambient (algebraMap Γ(C.chart.geometry.target.U.left, ⊤) C.chart.presentation.Ring r) =
        algebraMap Γ(C'.chart.geometry.target.U.left, ⊤) C'.chart.presentation.Ring
          (targetChart.base.left.appTop.hom r)
  normalMap : letI := C.chart.geometry.algebra; letI := C'.chart.geometry.algebra
    MathlibExt.AlgebraicGeometry.AffineNormalConeMaps.NormalMap C.chart.presentation
      C'.chart.presentation ambient sourceChart.base.left.appTop.hom quotient
  diagramMap : letI := C.chart.geometry.algebra; letI := C'.chart.geometry.algebra
    ConeDiagramMap C.chart.presentation C'.chart.presentation ambient
      sourceChart.base.left.appTop.hom quotient normalMap C'.diagram C.diagram
  normalized : letI := C.chart.geometry.algebra; letI := C'.chart.geometry.algebra
    C'.comparison.functor ⋙ diagramMap.grothendieck.op ≅
      affineConeMap p C' C map overTotal sourceChart ⋙ C.comparison.functor

end AlgebraicGeometry.StackBundleCones
