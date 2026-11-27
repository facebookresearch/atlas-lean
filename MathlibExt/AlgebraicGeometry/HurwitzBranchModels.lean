/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.PerfectTorsionCartierOrigins
public import MathlibExt.AlgebraicGeometry.StableMapCompositionStacks
public import MathlibExt.AlgebraicGeometry.GeneralStableMapCurveClasses

/-!
# Source normalized Hurwitz branch maps and differentials

Degree is the actual pushed fundamental curve class. The target scheme
classifies finite-flat effective Cartier subschemes by their embedded
ideals, on every scheme parameter. Its branch map is a natural map of
the actual moduli fibers. At every family its ideal is fixed by the
perfect torsion origin of Rf_*[f*ω_D/T→ω_C/T].

The chart differential is the actual full cotangent arrow of that same
scheme map and its dual-number classes. Boundary families and
nonreduced parameters remain part of the branch-origin condition.
References: Fantechi–Pandharipande math/9905104v1, Theorem 1;
Graber–Harris–Starr math/0109220v1, §2.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.HurwitzBranchModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.GeneralStackGeometry
open MathlibExt.AlgebraicGeometry.FourierMukai
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.RelativeCurveClasses
open MathlibExt.AlgebraicGeometry.GeneralStableMapFamilies
open MathlibExt.AlgebraicGeometry.QuasicoherentDualityReferences
open MathlibExt.AlgebraicGeometry.HurwitzBranchComplexes
open MathlibExt.AlgebraicGeometry.PerfectTorsionCartierOrigins
open MathlibExt.AlgebraicGeometry.SchemeFirstOrderDifferentials
open MathlibExt.AlgebraicGeometry.MarkedMapDeformationCones
open MathlibExt.AlgebraicGeometry.GlobalPerfectObstructionTheory
open MathlibExt.AlgebraicGeometry.ModuleDerivedSquares
open MathlibExt.AlgebraicGeometry.BirationalDualityReferences
attribute [local instance] HasDerivedCategory.standard

variable {k : Type} [Field k] (D : Over (Spec (.of k)))

/-- The actual degree-d target curve class, with its length-weighted fundamental cycle. -/
def targetClass [LocallyOfFiniteType D.hom] [IsNoetherian D.left] (d : ℕ) : CurveClass D :=
  (d : ℚ) • pushedCurveClass D.left (𝟙 D.left)

abbrev DegreeFamilies [LocallyOfFiniteType D.hom] [IsNoetherian D.left]
    (n g d : ℕ) (T : Over (Spec (.of k))) :=
  (show ObjectProperty (Family D.hom n g T.left T.hom) from fun F =>
    IsGeometricallyStable F ∧ HasCurveClass D T F (targetClass D d)).FullSubcategory

/-- The actual fixed-degree stable-map moduli fibers. -/
structure DegreeModuli [LocallyOfFiniteType D.hom] [IsNoetherian D.left] (n g d : ℕ) where
  stack : RelativeStack (Spec (.of k))
  fibre : ∀ T : Over (Spec (.of k)), stack.Fibre T ≌ DegreeFamilies D n g d T

def DegreeModuli.family [LocallyOfFiniteType D.hom] [IsNoetherian D.left]
    {n g d : ℕ} (M : DegreeModuli D n g d) (T : Over (Spec (.of k))) (x : M.stack.Fibre T) :=
  ((M.fibre T).functor.obj x).obj

def DegreeModuli.sourceFunctor [LocallyOfFiniteType D.hom] [IsNoetherian D.left]
    {n g d : ℕ} (M : DegreeModuli D n g d) (T : Over (Spec (.of k))) :
    M.stack.Fibre T ⥤ Scheme.{0} where
  obj x := (DegreeModuli.family D M T x).curve.X
  map f := ((M.fibre T).functor.map f).hom.iso.hom
  map_id x := by rw [(M.fibre T).functor.map_id]; rfl
  map_comp f g := by rw [(M.fibre T).functor.map_comp f g]; rfl

/-- Source normalization of all fixed-degree moduli pullbacks, with actual Cartesian curves. -/
structure DegreeBaseChange [LocallyOfFiniteType D.hom] [IsNoetherian D.left]
    {n g d : ℕ} (M : DegreeModuli D n g d) where
  map : ∀ {T U : Over (Spec (.of k))} (f : T ⟶ U) (x : M.stack.Fibre U),
    (DegreeModuli.family D M T ((M.stack.toPseudofunctor.map f.op.toLoc).toFunctor.obj x)).curve.X ⟶
      (DegreeModuli.family D M U x).curve.X
  square : ∀ {T U : Over (Spec (.of k))} (f : T ⟶ U) (x : M.stack.Fibre U),
    IsPullback (map f x)
      (DegreeModuli.family D M T ((M.stack.toPseudofunctor.map f.op.toLoc).toFunctor.obj x)).curve.π
      (DegreeModuli.family D M U x).curve.π f.left
  markings : ∀ {T U : Over (Spec (.of k))} (f : T ⟶ U) (x : M.stack.Fibre U) (i : Fin n),
    (DegreeModuli.family D M T
      ((M.stack.toPseudofunctor.map f.op.toLoc).toFunctor.obj x)).curve.marking i ≫
      map f x = f.left ≫ (DegreeModuli.family D M U x).curve.marking i
  target : ∀ {T U : Over (Spec (.of k))} (f : T ⟶ U) (x : M.stack.Fibre U),
    map f x ≫ (DegreeModuli.family D M U x).map =
      (DegreeModuli.family D M T ((M.stack.toPseudofunctor.map f.op.toLoc).toFunctor.obj x)).map
  natural : ∀ {T U : Over (Spec (.of k))} (f : T ⟶ U) {x y : M.stack.Fibre U} (a : x ⟶ y),
    (DegreeModuli.sourceFunctor D M T).map
        ((M.stack.toPseudofunctor.map f.op.toLoc).toFunctor.map a) ≫ map f y =
      map f x ≫ (DegreeModuli.sourceFunctor D M U).map a
  identity : ∀ (T : Over (Spec (.of k))) (x : M.stack.Fibre T), map (𝟙 T) x =
    (DegreeModuli.sourceFunctor D M T).map ((Cat.Hom.toNatIso
      (M.stack.toPseudofunctor.mapId (.mk (op T)))).hom.app x)
  composition : ∀ {T U W : Over (Spec (.of k))} (f : T ⟶ U) (j : U ⟶ W) (x : M.stack.Fibre W),
    map (f ≫ j) x = (DegreeModuli.sourceFunctor D M T).map ((Cat.Hom.toNatIso
      (M.stack.toPseudofunctor.mapComp j.op.toLoc f.op.toLoc)).hom.app x) ≫
        map f ((M.stack.toPseudofunctor.map j.op.toLoc).toFunctor.obj x) ≫ map j x

/-- The actual target/base product of a stable-map family. -/
def relativeTarget (T : Over (Spec (.of k))) : Over (Spec (.of k)) :=
  Over.mk (pullback.snd D.hom T.hom ≫ T.hom)

def sourceCurve {n g : ℕ} {T : Over (Spec (.of k))}
    (F : Family D.hom n g T.left T.hom) : Over (Spec (.of k)) :=
  Over.mk (F.curve.π ≫ T.hom)

def sourceProjection {n g : ℕ} {T : Over (Spec (.of k))}
    (F : Family D.hom n g T.left T.hom) : sourceCurve D F ⟶ T :=
  Over.homMk F.curve.π rfl

def targetProjection (T : Over (Spec (.of k))) : relativeTarget D T ⟶ T :=
  Over.homMk (pullback.snd D.hom T.hom) rfl

def familyMap {n g : ℕ} {T : Over (Spec (.of k))}
    (F : Family D.hom n g T.left T.hom) : sourceCurve D F ⟶ relativeTarget D T :=
  Over.homMk (mapToRelativeTarget F) (by
    change pullback.lift F.map F.curve.π F.over ≫
      (pullback.snd D.hom T.hom ≫ T.hom) = F.curve.π ≫ T.hom
    rw [← Category.assoc, pullback.lift_snd])

theorem familyMap_over {n g : ℕ} {T : Over (Spec (.of k))}
    (F : Family D.hom n g T.left T.hom) :
    familyMap D F ≫ targetProjection D T = sourceProjection D F := by
  apply Over.OverMorphism.ext
  change pullback.lift F.map F.curve.π F.over ≫ pullback.snd D.hom T.hom = F.curve.π
  exact pullback.lift_snd _ _ _

variable [HasDerivedPushforwards.{0}]

/-- Complete native branch-complex inputs for the same actual family. -/
structure BranchComplexData {n g : ℕ} {T : Over (Spec (.of k))}
    (F : Family D.hom n g T.left T.hom) where
  source : RelativeFormsData (sourceCurve D F) T (sourceProjection D F)
  target : RelativeFormsData (relativeTarget D T) T (targetProjection D T)
  differential : RelativeFormsMap (familyMap D F) (familyMap_over D F) source target
  proper : ProperReference F.curve.π
  fundamental : NodalFundamentalClass source (properCanonicalModule proper 1)

def BranchComplexData.object {n g : ℕ} {T : Over (Spec (.of k))}
    {F : Family D.hom n g T.left T.hom} (B : BranchComplexData D F) :
    FourierMukai.D (relativeTarget D T).left :=
  branchComplex B.differential B.proper B.fundamental

/-- The actual symmetric-divisor scheme and its full scheme-valued Cartier classifier. -/
structure DivisorScheme (r : ℕ) where
  scheme : Over (Spec (.of k))
  family : ∀ (T : Over (Spec (.of k))) (_a : T ⟶ scheme),
    EffectiveCartierFamily (pullback.snd D.hom T.hom) r
  classifier : ∀ T : Over (Spec (.of k)),
    (T ⟶ scheme) ≃ CartierClasses (pullback.snd D.hom T.hom) r
  normalized : ∀ (T : Over (Spec (.of k))) (a : T ⟶ scheme),
    classifier T a = cartierClass (family T a)
  sourceMap : ∀ {T U : Over (Spec (.of k))} (f : T ⟶ U) (a : U ⟶ scheme),
    (family T (f ≫ a)).Z ⟶ (family U a).Z
  baseChange : ∀ {T U : Over (Spec (.of k))} (f : T ⟶ U) (a : U ⟶ scheme),
    IsPullback (sourceMap f a) ((family T (f ≫ a)).inclusion ≫ pullback.snd D.hom T.hom)
      ((family U a).inclusion ≫ pullback.snd D.hom U.hom) f.left
  inclusion : ∀ {T U : Over (Spec (.of k))} (f : T ⟶ U) (a : U ⟶ scheme),
    sourceMap f a ≫ (family U a).inclusion =
      (family T (f ≫ a)).inclusion ≫
        pullback.map D.hom T.hom D.hom U.hom (𝟙 D.left) f.left (𝟙 _)
          (by simp) (by simp)

/-- A branch map is natural on all moduli objects; its ideal is fixed
by the native branch complex. -/
structure BranchModel [LocallyOfFiniteType D.hom] [IsNoetherian D.left]
    {n g d r : ℕ} (M : DegreeModuli D n g d) (S : DivisorScheme D r) where
  map : ∀ (T : Over (Spec (.of k))) (_x : M.stack.Fibre T), T ⟶ S.scheme
  isomorphism : ∀ (T : Over (Spec (.of k))) (x y : M.stack.Fibre T) (_e : x ⟶ y), map T x = map T y
  baseChange : ∀ {T U : Over (Spec (.of k))} (f : T ⟶ U) (x : M.stack.Fibre U),
    map T ((M.stack.toPseudofunctor.map f.op.toLoc).toFunctor.obj x) = f ≫ map U x
  complex : ∀ (T : Over (Spec (.of k))) (x : M.stack.Fibre T),
    BranchComplexData D (DegreeModuli.family D M T x)
  origin : ∀ (T : Over (Spec (.of k))) (x : M.stack.Fibre T),
    CartierOrigin (S.family T (map T x)) (BranchComplexData.object D (complex T x))

/-- The parameter differential is the full cotangent arrow of this same source-fixed branch map. -/
structure BranchDifferentialData [LocallyOfFiniteType D.hom] [IsNoetherian D.left]
    {n g d r : ℕ} {M : DegreeModuli D n g d} {S : DivisorScheme D r}
    (B : BranchModel D M S) (T : Over (Spec (.of k))) (x : M.stack.Fibre T) where
  source : CotangentNormalization T.hom
  target : CotangentNormalization S.scheme.hom
  differential : RelativeDifferential (B.map T x).left (Over.w (B.map T x)) source target
  sourceForms : CotangentFormsProjection T source
  targetForms : CotangentFormsProjection S.scheme target

variable [HasDerivedPullbacks.{0}] [HasDerivedTensors.{0}]

/-- The branch differential on actual cotangent classes is precomposition
by this same scheme-valued branch map. -/
def BranchDifferentialData.pointClassMap [LocallyOfFiniteType D.hom] [IsNoetherian D.left]
    {n g d r : ℕ} {M : DegreeModuli D n g d} {S : DivisorScheme D r}
    {B : BranchModel D M S} {T : Over (Spec (.of k))} {x : M.stack.Fibre T}
    (E : BranchDifferentialData D B T x) {Ω : Type} [Field Ω] (p : Spec (.of Ω) ⟶ T.left)
    (P : PullbackPasting p (B.map T x).left)
    (ξ : pointCotangent T E.source p ⟶ derivedUnit (Spec (.of Ω))) :
    pointCotangent S.scheme E.target (p ≫ (B.map T x).left) ⟶ derivedUnit (Spec (.of Ω)) :=
  mapPointClass T E.source p (B.map T x) E.target E.differential P ξ

end MathlibExt.AlgebraicGeometry.HurwitzBranchModels
