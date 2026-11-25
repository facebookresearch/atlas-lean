/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LiGluingRelativeTypes
public import MathlibExt.AlgebraicGeometry.LiExpandedCentralModels
public import MathlibExt.AlgebraicGeometry.StackVirtualPullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# The actual Li matching square, glued maps and image

The two evaluations use the same D^r, with the right divisor transported
by the specified original divisor isomorphism. The matching apex is the
native two-fibre square over the diagonal of that D^r. It represents the
full groupoid of actual matching relative families, including empty sides.

Source gluing identifies precisely the ordered root sections and retains
the chosen shuffle of ordinary markings. Target gluing is the public
native divisor pushout. Phi is normalized on both resulting scheme maps.
Its image predicate is the fppf-local essential image of that exact Phi;
finite-etale pure degree is imposed over that image, never over the whole
central moduli stack. The degree is the computed root-group cardinal.

Source: Jun Li arXiv:math/0110113v1, introduction pp3--4, Section3.1
equations(3.1)--(3.2), pp31--32, and diagram(3.14), Theorem3.15, pp39--40.
Components are labelled by numerical classes, the degrees against all line bundles of the
central fibre and of the two sides (Li, math/0009097v1, Def. 4.6), which are locally constant;
the vertex classes add up to the central class.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.LiGluingGeometryModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open ExpandedTargetChainGeometry RelativeProjectiveLineModels StandardRelativeExpansionModels
open ExpandedTargetGluingModels MarkedCurveStabilization RelativeExpandedMapFamilies
open StackCycleGeometry StackCycleRelations StackChowGroups StackFibreModels StackVectorBundles
open StackBundleCones StackVirtualPullbacks
open LiGluingRelativeTypes
open scoped BigOperators

variable {k : Type} [Field k]

structure LegOrdering (n n' : ℕ) where
  labels : Fin n ⊕ Fin n' ≃ Fin (n + n')
  leftOrdered : StrictMono (fun i : Fin n => labels (Sum.inl i))
  rightOrdered : StrictMono (fun i : Fin n' => labels (Sum.inr i))

variable {n n' r g : ℕ} (G : FullType n r) (H : FullType n' r)
  (P Q : RelativePair (k := k)) (W0 : SingularTarget P Q)
  [LocallyOfFiniteType P.target.hom] [LocallyOfFiniteType Q.target.hom]
  [LocallyOfFiniteType W0.scheme.hom]
  [IsNoetherian P.target.left] [IsNoetherian Q.target.left] [IsNoetherian W0.scheme.left]
  (beta : Fin G.vertices → StableMapNumericalClasses.NumericalClass P.target.left)
  (gamma : Fin H.vertices → StableMapNumericalClasses.NumericalClass Q.target.left)
  (total : StableMapNumericalClasses.NumericalClass W0.scheme.left)

structure AdmissibleTriple where
  contact : ∀ i : Fin r, G.order i = H.order i
  nonempty : 0 < G.vertices + H.vertices
  genus : g + G.vertices + H.vertices =
    (∑ v, G.genus v) + (∑ v, H.genus v) + r + 1
  connected : ∀ a b : Fin G.vertices ⊕ Fin H.vertices, Relation.ReflTransGen
    (fun a b => ∃ i : Fin r,
      (a = Sum.inl (G.rootLabels i).1 ∧ b = Sum.inr (H.rootLabels i).1) ∨
      (b = Sum.inl (G.rootLabels i).1 ∧ a = Sum.inr (H.rootLabels i).1)) a b
  legs : LegOrdering n n'
  /-- The vertex classes add up to the central class: against every line bundle on the central
  fibre, the central degree is the sum of the vertex degrees of its restrictions to the two
  sides. -/
  degree : ∀ (L : ProjectiveLineSystems.LineBundle W0.scheme.left)
    (hl : CoherentCurveLinearSeries.IsLineBundle
      ((Scheme.Modules.pullback W0.left.left).obj L.val))
    (hr : CoherentCurveLinearSeries.IsLineBundle
      ((Scheme.Modules.pullback W0.right.left).obj L.val)),
    total L = (∑ v, beta v ⟨_, hl⟩) + ∑ v, gamma v ⟨_, hr⟩

variable (R : ProjectiveLine P.divisor.left (normalLineModule P))
  (R' : ProjectiveLine Q.divisor.left (normalLineModule Q))
  (S : StandardRelativeExpansionModels.StandardSystem P R)
  (S' : StandardRelativeExpansionModels.StandardSystem Q R')
  (T : Over (Spec (.of k))) (F : LiGluingRelativeTypes.Family P R S G T)
  (F' : LiGluingRelativeTypes.Family Q R' S' H T)

def rootSection (i : Fin r) : T.left ⟶ (F.maps (G.rootLabels i).1).curve.X :=
  (F.maps (G.rootLabels i).1).curve.marking
    (Fin.natAdd (G.legs (G.rootLabels i).1) (G.rootLabels i).2)

def rightRootSection (i : Fin r) : T.left ⟶ (F'.maps (H.rootLabels i).1).curve.X :=
  (F'.maps (H.rootLabels i).1).curve.marking
    (Fin.natAdd (H.legs (H.rootLabels i).1) (H.rootLabels i).2)

def RootMatch : Prop :=
  ∀ i : Fin r, LiGluingRelativeTypes.evaluation P R S G T F i ≫ W0.divisor.hom =
    LiGluingRelativeTypes.evaluation Q R' S' H T F' i

structure SourceJoin (I : LegOrdering n n') where
  curve : MarkedFamily T.left (n + n') g
  left : ∀ v : Fin G.vertices, (F.maps v).curve.X ⟶ curve.X
  right : ∀ v : Fin H.vertices, (F'.maps v).curve.X ⟶ curve.X
  leftOver : ∀ v, left v ≫ curve.π = (F.maps v).curve.π
  rightOver : ∀ v, right v ≫ curve.π = (F'.maps v).curve.π
  roots : ∀ i : Fin r, rootSection G P R S T F i ≫ left (G.rootLabels i).1 =
    rightRootSection H Q R' S' T F' i ≫ right (H.rootLabels i).1
  leftLegs : ∀ i : Fin n,
    (F.maps (G.legLabels i).1).curve.marking
      (Fin.castAdd (G.roots (G.legLabels i).1) (G.legLabels i).2) ≫ left (G.legLabels i).1 =
    curve.marking (I.labels (Sum.inl i))
  rightLegs : ∀ i : Fin n',
    (F'.maps (H.legLabels i).1).curve.marking
      (Fin.castAdd (H.roots (H.legLabels i).1) (H.legLabels i).2) ≫ right (H.legLabels i).1 =
    curve.marking (I.labels (Sum.inr i))
  universal : ∀ (Z : Scheme.{0}) (z : Z ⟶ T.left)
      (f : ∀ v : Fin G.vertices, (F.maps v).curve.X ⟶ Z)
      (h : ∀ v : Fin H.vertices, (F'.maps v).curve.X ⟶ Z),
    (∀ v, f v ≫ z = (F.maps v).curve.π) → (∀ v, h v ≫ z = (F'.maps v).curve.π) →
    (∀ i : Fin r, rootSection G P R S T F i ≫ f (G.rootLabels i).1 =
      rightRootSection H Q R' S' T F' i ≫ h (H.rootLabels i).1) →
    ∃! q : curve.X ⟶ Z, q ≫ z = curve.π ∧
      (∀ v, left v ≫ q = f v) ∧ (∀ v, right v ≫ q = h v)

variable {G H P Q W0 R R' S S' T F F'}

structure JoinedMap {I : LegOrdering n n'}
    (X : TargetJoin P Q R R' S S' W0 T F.target F'.target)
    (C : SourceJoin (g := g) G H P Q R R' S S' T F F' I) where
  map : C.curve.X ⟶ X.scheme.left
  over : map ≫ X.projection.left = C.curve.π
  left : ∀ v, C.left v ≫ map = (F.maps v).map ≫ X.left.left
  right : ∀ v, C.right v ≫ map = (F'.maps v).map ≫ X.right.left

section Stacks

variable {baseScheme : Scheme.{0}}

def reindexArrow {F : Stack baseScheme} {T U : Over baseScheme} (f : T ⟶ U) (x : F.Fibre U) :
    point T ((pull F f).obj x) ⟶ point U x := ⟨f, 𝟙 _⟩

/-- A representable stack model of the fixed scheme, with every base restriction. -/
structure SchemeStackModel (D : Over baseScheme) where
  stack : Stack baseScheme
  family : ∀ T : Over baseScheme, stack.Fibre T ⥤ Discrete (T ⟶ D)
  equivalence : ∀ T, (family T).IsEquivalence
  reindex : ∀ {T U : Over baseScheme} (f : T ⟶ U) (x : stack.Fibre U),
    ((family T).obj ((pull stack f).obj x)).as = f ≫ ((family U).obj x).as

structure ProductStackModel (A B : Stack baseScheme) where
  stack : Stack baseScheme
  left : StackHom stack A
  right : StackHom stack B
  family : ∀ T : Over baseScheme, stack.Fibre T ⥤ (A.Fibre T × B.Fibre T)
  equivalence : ∀ T, (family T).IsEquivalence
  leftObject : ∀ T (x : stack.Fibre T), ((family T).obj x).1 = (component left T).obj x
  rightObject : ∀ T (x : stack.Fibre T), ((family T).obj x).2 = (component right T).obj x
  leftArrow : ∀ T {x y : stack.Fibre T} (f : x ⟶ y),
    eqToHom (leftObject T x).symm ≫ ((family T).map f).1 ≫ eqToHom (leftObject T y) =
      (component left T).map f
  rightArrow : ∀ T {x y : stack.Fibre T} (f : x ⟶ y),
    eqToHom (rightObject T x).symm ≫ ((family T).map f).2 ≫ eqToHom (rightObject T y) =
      (component right T).map f

structure FppfCover (T : Over baseScheme) where
  index : Type
  scheme : index → Over baseScheme
  map : ∀ i, scheme i ⟶ T
  flat : ∀ i, Flat (map i).left
  presentation : ∀ i, LocallyOfFinitePresentation (map i).left
  covers : ∀ t : T.left, ∃ (i : index) (s : (scheme i).left), (map i).left s = t

def FppfLocallyInImage {A B : Stack baseScheme} (f : StackHom A B)
    (T : Over baseScheme) (y : B.Fibre T) : Prop :=
  ∃ C : FppfCover T, ∀ i, ∃ x : A.Fibre (C.scheme i),
    Nonempty ((component f (C.scheme i)).obj x ≅ (pull B (C.map i)).obj y)

structure FiniteEtalePureDegree {A B : Stack baseScheme} (f : StackHom A B) (degree : ℕ) where
  fibre : ∀ (T : Over baseScheme) (y : B.Fibre T), SchemeFibreModel f T y
  finite : ∀ T y, IsFinite (fibre T y).scheme.hom
  etale : ∀ T y, Etale (fibre T y).scheme.hom
  geometricFinite : ∀ (T : Over baseScheme) (y : B.Fibre T) (Ω : Type) [Field Ω] [IsAlgClosed Ω]
      (t : Spec (.of Ω) ⟶ T.left), Finite (pullback (fibre T y).scheme.hom t : Scheme.{0})
  geometricDegree : ∀ (T : Over baseScheme) (y : B.Fibre T) (Ω : Type) [Field Ω] [IsAlgClosed Ω]
      (t : Spec (.of Ω) ⟶ T.left), Nat.card (pullback (fibre T y).scheme.hom t : Scheme.{0}) = degree

end Stacks

section Matching

variable (G : FullType n r) (H : FullType n' r)
  (P Q : RelativePair (k := k)) (W0 : SingularTarget P Q)
  [LocallyOfFiniteType P.target.hom] [LocallyOfFiniteType Q.target.hom]
  [LocallyOfFiniteType W0.scheme.hom]
  [IsNoetherian P.target.left] [IsNoetherian Q.target.left] [IsNoetherian W0.scheme.left]
  (R : ProjectiveLine P.divisor.left (normalLineModule P))
  (R' : ProjectiveLine Q.divisor.left (normalLineModule Q))
  (S : StandardRelativeExpansionModels.StandardSystem P R)
  (S' : StandardRelativeExpansionModels.StandardSystem Q R')
  (beta : Fin G.vertices → StableMapNumericalClasses.NumericalClass P.target.left)
  (gamma : Fin H.vertices → StableMapNumericalClasses.NumericalClass Q.target.left)
  (ML : LiGluingRelativeTypes.ModuliModel P R S G beta)
  (MR : LiGluingRelativeTypes.ModuliModel Q R' S' H gamma)

abbrev boundaryPower : Over (Spec (.of k)) := ∏ᶜ (fun _ : Fin r => P.divisor)

def rightEvaluation (T : Over (Spec (.of k)))
    (F : LiGluingRelativeTypes.Family Q R' S' H T) : T ⟶ boundaryPower (r := r) P :=
  Pi.lift (fun i => LiGluingRelativeTypes.evaluation Q R' S' H T F i ≫ W0.divisor.inv)

abbrev MatchingFamily (T : Over (Spec (.of k))) :=
  (show ObjectProperty (LiGluingRelativeTypes.StableFamily P R S G T beta ×
    LiGluingRelativeTypes.StableFamily Q R' S' H T gamma) from
    fun x => RootMatch G H P Q W0 R R' S S' T x.1.obj x.2.obj).FullSubcategory

structure MatchingModel where
  boundary : SchemeStackModel (boundaryPower (r := r) P)
  twice : SchemeStackModel (prod (boundaryPower (r := r) P) (boundaryPower (r := r) P))
  product : ProductStackModel ML.stack MR.stack
  diagonal : StackHom boundary.stack twice.stack
  diagonalNormalized : ∀ T (x : boundary.stack.Fibre T),
    ((twice.family T).obj ((component diagonal T).obj x)).as =
      prod.lift ((boundary.family T).obj x).as ((boundary.family T).obj x).as
  leftEvaluation : StackHom ML.stack boundary.stack
  leftNormalized : ∀ T (x : ML.stack.Fibre T),
    ((boundary.family T).obj ((component leftEvaluation T).obj x)).as =
      LiGluingRelativeTypes.allEvaluations P R S G T ((ML.family T).obj x).obj
  rightEvaluation : StackHom MR.stack boundary.stack
  rightNormalized : ∀ T (x : MR.stack.Fibre T),
    ((boundary.family T).obj ((component rightEvaluation T).obj x)).as =
      LiGluingGeometryModels.rightEvaluation H P Q W0 R' S' T ((MR.family T).obj x).obj
  pairEvaluation : StackHom product.stack twice.stack
  pairNormalized : ∀ T (x : product.stack.Fibre T),
    ((twice.family T).obj ((component pairEvaluation T).obj x)).as = prod.lift
      ((boundary.family T).obj ((component leftEvaluation T).obj ((component product.left T).obj x))).as
      ((boundary.family T).obj ((component rightEvaluation T).obj ((component product.right T).obj x))).as
  square : TwoCartesianSquare pairEvaluation diagonal
  family : ∀ T : Over (Spec (.of k)), square.apex.Fibre T ⥤ MatchingFamily G H P Q W0 R R' S S' beta gamma T
  equivalence : ∀ T, (family T).IsEquivalence
  leftObject : ∀ T (x : square.apex.Fibre T), (((family T).obj x).obj.1) =
    (ML.family T).obj ((component product.left T).obj ((component square.fst T).obj x))
  rightObject : ∀ T (x : square.apex.Fibre T), (((family T).obj x).obj.2) =
    (MR.family T).obj ((component product.right T).obj ((component square.fst T).obj x))
  leftArrow : ∀ T {x y : square.apex.Fibre T} (h : x ⟶ y),
    eqToHom (leftObject T x).symm ≫ (((family T).map h).hom).1 ≫ eqToHom (leftObject T y) =
      (ML.family T).map ((component product.left T).map ((component square.fst T).map h))
  rightArrow : ∀ T {x y : square.apex.Fibre T} (h : x ⟶ y),
    eqToHom (rightObject T x).symm ≫ (((family T).map h).hom).2 ≫ eqToHom (rightObject T y) =
      (MR.family T).map ((component product.right T).map ((component square.fst T).map h))

variable (W : LiExpandedDegenerationModels.OneParameter P Q W0)
  (WS : LiExpandedDegenerationModels.StandardSystem W)
  (total : StableMapNumericalClasses.NumericalClass W0.scheme.left)
  (eta : AdmissibleTriple (g := g) G H P Q W0 beta gamma total)
  (MC : LiExpandedCentralModels.ModuliModel W WS (n + n') g total)
  (M : MatchingModel G H P Q W0 R R' S S' beta gamma ML MR)

structure FamilyJoin (T : Over (Spec (.of k))) (x : M.square.apex.Fibre T)
    (F : LiExpandedCentralModels.Family W WS (n + n') g T) where
  target : TargetJoin P Q R R' S S' W0 T
    (((M.family T).obj x).obj.1.obj.target) (((M.family T).obj x).obj.2.obj.target)
  source : SourceJoin (g := g) G H P Q R R' S S' T
    (((M.family T).obj x).obj.1.obj) (((M.family T).obj x).obj.2.obj) eta.legs
  map : JoinedMap target source
  targetIso : target.scheme ≅ F.target.scheme
  targetOver : targetIso.hom ≫ F.target.projection = target.projection
  targetContraction : targetIso.hom ≫ F.target.contraction = target.contraction ≫
    W.central.hom ≫ pullback.fst W.projection W.zero
  sourceIso : source.curve.X ≅ F.curve.X
  sourceOver : sourceIso.hom ≫ F.curve.π = source.curve.π
  marking : ∀ i, source.curve.marking i ≫ sourceIso.hom = F.curve.marking i
  normalizedMap : sourceIso.hom ≫ F.map = map.map ≫ targetIso.hom.left

structure GluingModel where
  phi : StackHom M.square.apex MC.stack
  join : ∀ (T : Over (Spec (.of k))) (x : M.square.apex.Fibre T),
    FamilyJoin G H P Q W0 R R' S S' beta gamma ML MR W WS total eta M T x
      ((MC.family T).obj ((component phi T).obj x)).obj
  leftSourceNaturality : ∀ (T : Over (Spec (.of k))) {x y : M.square.apex.Fibre T} (h : x ⟶ y) v,
    (join T x).source.left v ≫ (join T x).sourceIso.hom ≫
      ((MC.family T).map ((component phi T).map h)).hom.source.hom =
    (((((M.family T).map h).hom).1).hom.source v).hom ≫
      (join T y).source.left v ≫ (join T y).sourceIso.hom
  rightSourceNaturality : ∀ (T : Over (Spec (.of k))) {x y : M.square.apex.Fibre T} (h : x ⟶ y) v,
    (join T x).source.right v ≫ (join T x).sourceIso.hom ≫
      ((MC.family T).map ((component phi T).map h)).hom.source.hom =
    (((((M.family T).map h).hom).2).hom.source v).hom ≫
      (join T y).source.right v ≫ (join T y).sourceIso.hom
  leftTargetNaturality : ∀ (T : Over (Spec (.of k))) {x y : M.square.apex.Fibre T} (h : x ⟶ y),
    (join T x).target.left ≫ (join T x).targetIso.hom ≫
      ((MC.family T).map ((component phi T).map h)).hom.target.iso.hom =
    ((((M.family T).map h).hom).1).hom.target.iso.hom ≫
      (join T y).target.left ≫ (join T y).targetIso.hom
  rightTargetNaturality : ∀ (T : Over (Spec (.of k))) {x y : M.square.apex.Fibre T} (h : x ⟶ y),
    (join T x).target.right ≫ (join T x).targetIso.hom ≫
      ((MC.family T).map ((component phi T).map h)).hom.target.iso.hom =
    ((((M.family T).map h).hom).2).hom.target.iso.hom ≫
      (join T y).target.right ≫ (join T y).targetIso.hom
  reindex : ∀ {T U : Over (Spec (.of k))} (f : T ⟶ U) (x : M.square.apex.Fibre U),
    LiExpandedCentralModels.FamilyBaseChange W WS (n + n') g f
      ((MC.family T).obj ((component phi T).obj ((pull M.square.apex f).obj x))).obj
      ((MC.family U).obj ((component phi U).obj x)).obj
  targetReindexNormalized : ∀ {T U : Over (Spec (.of k))} (f : T ⟶ U) (x : M.square.apex.Fibre U),
    (reindex f x).target =
      ((MC.family T).map (((totalMap phi).map (reindexArrow f x)).fiber)).hom.target.iso.hom ≫
        (MC.reindex f ((component phi U).obj x)).target
  sourceReindexNormalized : ∀ {T U : Over (Spec (.of k))} (f : T ⟶ U) (x : M.square.apex.Fibre U),
    (reindex f x).source =
      ((MC.family T).map (((totalMap phi).map (reindexArrow f x)).fiber)).hom.source.hom ≫
        (MC.reindex f ((component phi U).obj x)).source
  image : ClosedSubstack MC.stack
  actualImage : ∀ (T : Over (Spec (.of k))) (x : MC.stack.Fibre T),
    image.predicate T x ↔ FppfLocallyInImage phi T x
  toImage : StackHom M.square.apex image.source
  factors : StackVectorBundles.TwoIso
    (Pseudofunctor.StrongTrans.vcomp toImage image.inclusion) phi
  finiteEtale : FiniteEtalePureDegree toImage (equivalenceOrder G beta H gamma)

end Matching

section Output

variable {n n' r g : ℕ} (G : FullType n r) (H : FullType n' r)
  (P Q : RelativePair (k := k)) (W0 : SingularTarget P Q)
  [LocallyOfFiniteType P.target.hom] [LocallyOfFiniteType Q.target.hom]
  [LocallyOfFiniteType W0.scheme.hom]
  [IsNoetherian P.target.left] [IsNoetherian Q.target.left] [IsNoetherian W0.scheme.left]
  (beta : Fin G.vertices → StableMapNumericalClasses.NumericalClass P.target.left)
  (gamma : Fin H.vertices → StableMapNumericalClasses.NumericalClass Q.target.left)
  (total : StableMapNumericalClasses.NumericalClass W0.scheme.left)
  (eta : AdmissibleTriple (g := g) G H P Q W0 beta gamma total)
  (W : LiExpandedDegenerationModels.OneParameter P Q W0)

/-- Source-qualified geometry output from the original degeneration and type.
No final moduli, target, matching, Phi or image is an input to this package. -/
structure GeometryOutput where
  expanded : LiExpandedDegenerationModels.StandardSystem W
  leftLine : ProjectiveLine P.divisor.left (normalLineModule P)
  rightLine : ProjectiveLine Q.divisor.left (normalLineModule Q)
  leftExpanded : StandardRelativeExpansionModels.StandardSystem P leftLine
  rightExpanded : StandardRelativeExpansionModels.StandardSystem Q rightLine
  leftModuli : LiGluingRelativeTypes.ModuliModel P leftLine leftExpanded G beta
  rightModuli : LiGluingRelativeTypes.ModuliModel Q rightLine rightExpanded H gamma
  centralModuli : LiExpandedCentralModels.ModuliModel W expanded (n + n') g total
  matching : MatchingModel G H P Q W0 leftLine rightLine leftExpanded rightExpanded
    beta gamma leftModuli rightModuli
  gluing : GluingModel G H P Q W0 leftLine rightLine leftExpanded rightExpanded
    beta gamma leftModuli rightModuli W expanded total eta centralModuli matching

end Output

end MathlibExt.AlgebraicGeometry.LiGluingGeometryModels
