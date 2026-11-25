/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.StackBundleCones
public import MathlibExt.AlgebraicGeometry.GlobalPerfectObstructionTheory

/-!
# Full affine-source normalization of a stack cotangent complex

A chart is an actual target smooth atlas followed by an actual source
etale atlas of the two-Cartesian pullback. Its relative ring map A to B
therefore models the specified stack morphism. Every refinement retains
the native CoGrothendieck arrows and their two-cell over that morphism.

The cotangent value is the actual polynomial-resolution complex for B/A.
All polynomial, coefficient, augmentation and cochain maps are retained,
including their pure-differential formulas and identity/composition laws.
The global object is one module-presheaf cochain diagram on ALL affine
stack points, not a tuple of independently chosen chart isomorphisms.

The ring map k to A to B is not replaced by the absolute k to B map.
This is a native descent/port normalization for the implemented Axiom
Scheme.Hom.cotangentComplex, not a new theorem asserting that an arbitrary
object L is a cotangent complex. Source: AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b,
StacksFrontier/Cotangent/SchemeCotangentComplex.lean (08T2, Apache 2.0),
and ResolutionCotangentAny.lean (08QI); Behrend–Fantechi §4.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.GlobalStackCotangentModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open GeneralStackGeometry StackCycleGeometry StackAffineModules StackFibreModels StackBundleCones
open _root_.AlgebraicTopology _root_.Simplicial
open GeometricCotangentComplex
open scoped Simplicial TensorProduct ChangeOfRings
attribute [local instance] HasDerivedCategory.standard

variable {S : Scheme.{0}} {X Y : Stack S}

abbrev Complex (X : Stack S) := CochainComplex (ModulePresheaf X) ℤ

abbrev chartPoint {f : StackHom X Y} (c : IntrinsicConeChart f) : AffinePoint X :=
  ⟨StackFibreModels.point c.geometry.source.U c.geometry.sourcePoint, by
    change IsAffine c.geometry.source.U.left
    infer_instance⟩

abbrev baseRing {f : StackHom X Y} (c : IntrinsicConeChart f) :=
  Γ(c.geometry.target.U.left, ⊤)
abbrev sourceRing {f : StackHom X Y} (c : IntrinsicConeChart f) :=
  Γ(c.geometry.source.U.left, ⊤)

instance {f : StackHom X Y} (c : IntrinsicConeChart f) : Algebra (baseRing c) (sourceRing c) :=
  c.geometry.algebra

def chartArrow {f : StackHom X Y} {c d : IntrinsicConeChart f}
    (r : ConeChartRefinement c d) : chartPoint d ⟶ chartPoint c :=
  ObjectProperty.homMk (X := chartPoint d) (Y := chartPoint c) r.source

def evaluate (K : Complex X) (p : AffinePoint X) :
    CochainComplex (ModuleCat.{0} ((rings X).obj (op p))) ℤ :=
  ((PresheafOfModules.evaluation (rings X ⋙ forget₂ CommRingCat RingCat) (op p)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K

def restrictPoint (K : Complex X) {p q : AffinePoint X} (f : p ⟶ q) :
    evaluate K q ⟶
      ((ModuleCat.restrictScalars ((rings X).map f.op).hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (evaluate K p) where
  f j := (K.X j).map f.op
  comm' i j _ := (K.d i j).naturality f.op

/-- The displayed balanced tensor is the canonical native base-change map. -/
structure DerivedBaseChange (K : Complex X) {p q : AffinePoint X} (f : p ⟶ q) where
  map : ((ModuleCat.extendScalars ((rings X).map f.op).hom).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (evaluate K q) ⟶ evaluate K p
  pure : ∀ j (r : (rings X).obj (op p)) (x : (evaluate K q).X j),
    map.f j (r ⊗ₜ[(rings X).obj (op q), ((rings X).map f.op).hom] x) =
      r • (show (evaluate K p).X j from (K.X j).map f.op x)
  quasi : QuasiIso map

/-- An actual augmentation-preserving map of polynomial resolutions,
with its induced cotangent cochain map fixed on every pure differential. -/
structure ResolutionMap {A B A' B' : Type}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra A B] [Algebra A' B']
    (α : A →+* A') (β : B →+* B')
    (R : PolynomialResolution A B) (T : PolynomialResolution A' B') where
  polynomial : ∀ n, R.algebra.obj n →+* T.algebra.obj n
  scalar : ∀ n (a : A), polynomial n (algebraMap A (R.algebra.obj n) a) =
    algebraMap A' (T.algebra.obj n) (α a)
  augmentation : ∀ n (b : R.algebra.obj n),
    T.augmentation.app n (polynomial n b) = β (R.augmentation.app n b)
  simplicial : ∀ {i j} (f : i ⟶ j) (b : R.algebra.obj i),
    polynomial j (R.algebra.map f b) = T.algebra.map f (polynomial i b)
  map : affineComplex R ⟶
    ((ModuleCat.restrictScalars β).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (affineComplex T)
  pure : ∀ (n : ℕ) (b : R.algebra.obj (op ⦋n⦌)),
    (affineDegreeIso T n).hom ((map.f (-(n : ℤ)))
      ((affineDegreeIso R n).inv
        (CommAlgCat.resolutionCotangentTermDifferential A (CommAlgCat.of A B)
          R.algebra R.augmentation (op ⦋n⦌) b))) =
      CommAlgCat.resolutionCotangentTermDifferential A' (CommAlgCat.of A' B')
        T.algebra T.augmentation (op ⦋n⦌) (polynomial (op ⦋n⦌) b)

/-- Projective-cofibrant point models make the displayed scalar tensor
the actual derived pullback, including nonflat coefficient maps. -/
def IsCofibrant {A : Type} [CommRing A] (K : CochainComplex (ModuleCat.{0} A) ℤ) : Prop :=
  ∀ (L M : CochainComplex (ModuleCat.{0} A) ℤ) (p : L ⟶ M),
    QuasiIso p → (∀ j : ℤ, Function.Surjective ((p.f j).hom)) →
      ∀ f : K ⟶ M, ∃ g : K ⟶ L, g ≫ p = f

/-- A global, derived-cartesian native cotangent diagram. Target values
and every source/refinement map are normalized against the specified
actual relative morphism. Constructor/port availability is separate. -/
structure Normalization (f : StackHom X Y) where
  complex : Complex X
  cofibrant : ∀ p : AffinePoint X,
    IsCofibrant (evaluate complex p)
  baseChange : ∀ {p q : AffinePoint X} (g : p ⟶ q), DerivedBaseChange complex g
  resolution : ∀ c : IntrinsicConeChart f, PolynomialResolution (baseRing c) (sourceRing c)
  comparison : ∀ c : IntrinsicConeChart f,
    affineComplex (resolution c) ⟶ evaluate complex (chartPoint c)
  [quasi : ∀ c : IntrinsicConeChart f, QuasiIso (comparison c)]
  refinement : ∀ {c d : IntrinsicConeChart f} (r : ConeChartRefinement c d),
    ResolutionMap (A := baseRing c) (B := sourceRing c)
      (A' := baseRing d) (B' := sourceRing d)
      r.target.base.left.appTop.hom ((rings X).map (chartArrow r).op).hom
      (resolution c) (resolution d)
  naturality : ∀ {c d : IntrinsicConeChart f} (r : ConeChartRefinement c d),
    comparison c ≫ restrictPoint complex (chartArrow r) =
      (refinement r).map ≫
        ((ModuleCat.restrictScalars ((rings X).map (chartArrow r).op).hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (comparison d)
  identity : ∀ (c : IntrinsicConeChart f)
    (r : ConeChartRefinement c c), r.source = 𝟙 _ → r.target = 𝟙 _ →
      ∀ n, (refinement r).polynomial n = RingHom.id _
  composition : ∀ {b c d : IntrinsicConeChart f}
    (u : ConeChartRefinement b c) (v : ConeChartRefinement c d)
    (w : ConeChartRefinement b d),
      w.source = v.source ≫ u.source → w.target = v.target ≫ u.target →
      ∀ n, (refinement w).polynomial n =
        ((refinement v).polynomial n).comp ((refinement u).polynomial n)

attribute [instance] Normalization.quasi

end MathlibExt.AlgebraicGeometry.GlobalStackCotangentModels
