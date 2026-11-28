/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GlobalBoundedDeterminantModels
public import MathlibExt.AlgebraicGeometry.FinitePointNormLines
public import MathlibExt.AlgebraicGeometry.DeterminantZeroUnits
public import MathlibExt.AlgebraicGeometry.MetrizedFibrePowerModels
public import MathlibExt.AlgebraicGeometry.RelativePolynomialProjectivity
public import MathlibExt.AlgebraicGeometry.CanonicalKoszulDeterminants
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Sections, Cartier maps and canonical acyclic torsion for Deligne symbols

The algebraic line is the existing full bounded determinant Deligne line.
A rational section is represented on a genuine dense scheme open, with
regular numerator and denominator equations in actual line frames.
Effective zero divisors retain the injective stalk section map, its native
cokernel, the closed zero scheme and the actual two-term Koszul complex.

Regular symbols are the images of the actual acyclic torsion of the full
section Koszul cochain. Original subset sheaves have their signed insertion
maps in degrees card(subset)-(n+1). The comparison uses the SAME original
subset presentations and ordered termwise exterior exact-sequence maps.
Actual affine localization covers, all basis choices and every original
scalar/cochain transition fix its coefficients. Generic determinant words
remain available as ordinary source calculations; they do not define symbols.

Reference: Yuan--Zhang, arXiv:2105.13587v9, Sections 4.2.1--4.2.2,
printed pp108--110, and Theorem 4.1.3. The imported exterior determinant
source retains the Apache-2.0 attribution in ProjectiveDeterminantModules.
Construction and independence of canonical symbols are requested in WantedExt.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DeligneSymbolModels

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open _root_.AlgebraicGeometry
open CoherentCurveLinearSeries GenericSectionMaps RelativeDeterminantPairings
open ProjectiveDeterminantModules GlobalBoundedDeterminantModels
open BoundedProjectiveDeterminants BoundedDeterminantTransportModels
open scoped TensorProduct

/-- The exact relative geometric scope of the source Deligne pairing. -/
structure RelativeScope {X Y : Scheme.{0}} (f : X ⟶ Y) (n : ℕ) : Prop where
  projective : ∀ (S : CommRingCat.{0}) (a : Spec S ⟶ Y),
    RelativePolynomialProjectivity.IsProjective (pullback.snd f a)
  flat : Flat f
  pureDimension : IsPureRelativeDimension f n
  integral : IsIntegral X
  targetIntegral : IsIntegral Y
  normal : ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧
    IsIntegrallyClosed (Y.presheaf.stalk y)

variable {X : Scheme.{0}} (L : X.Modules)

/-- A local frame equation for a rational section, with regular denominators. -/
structure FractionChart (U : X.Opens) (s : Γ(L,U)) where
  openSet : X.Opens
  frameBasis : ∀ (x : X) (_hx : x ∈ openSet),
    Module.Basis Unit (X.presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk L.val.presheaf x : AddCommGrpCat.{0}))
  frameSection : Γ(L,openSet)
  generator : ∀ (x : X) (hx : x ∈ openSet), frameBasis x hx () =
    TopCat.Presheaf.germ L.val.presheaf openSet x hx frameSection
  numerator : Γ(X,openSet)
  denominator : Γ(X,openSet)
  regularDenominator : ∀ (x : X) (hx : x ∈ openSet),
    Function.Injective (fun a : X.presheaf.stalk x ↦
      X.presheaf.germ openSet x hx denominator * a)
  equation : ∀ (x : X) (hU : x ∈ U) (hV : x ∈ openSet),
    X.presheaf.germ openSet x hV denominator •
        TopCat.Presheaf.germ L.val.presheaf U x hU s =
      X.presheaf.germ openSet x hV numerator •
        TopCat.Presheaf.germ L.val.presheaf openSet x hV frameSection

/-- A genuine rational section; the dense domain and all local equations are retained. -/
structure RationalSection where
  domain : X.Opens
  dense : Dense (domain : Set X)
  value : Γ(L,domain)
  charts : Type
  chart : charts → FractionChart L domain value
  cover : ∀ x : X, ∃ c : charts, x ∈ (chart c).openSet

/-- The actual two-term section Koszul complex, in degrees zero and one. -/
structure SectionKoszul (s : Γ(L,⊤)) where
  cochain : CochainComplex X.Modules ℤ
  source : cochain.X 0 ≅ structureModule X
  target : cochain.X 1 ≅ L
  zeroTerms : ∀ i : ℤ, i ≠ 0 → i ≠ 1 → IsZero (cochain.X i)
  differential : cochain.d 0 1 = source.hom ≫ topSectionHom X L s ≫ target.inv

/-- An effective Cartier divisor is the actual closed zero scheme of a regular section. -/
structure CartierZero (s : Γ(L,⊤)) where
  scheme : Scheme.{0}
  inclusion : scheme ⟶ X
  [closed : IsClosedImmersion inclusion]
  regular : ∀ x : X, Function.Injective
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (topSectionHom X L s).mapPresheaf)
  zeroLocus : ∀ x : X, x ∈ Set.range inclusion ↔ ¬ IsIso
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (topSectionHom X L s).mapPresheaf)
  koszul : SectionKoszul L s
  cokernel : cokernel (topSectionHom X L s) ≅
    (Scheme.Modules.pushforward inclusion).obj ((Scheme.Modules.pullback inclusion).obj L)
  cokernelMap : CategoryTheory.Limits.cokernel.π (topSectionHom X L s) ≫ cokernel.hom =
    (Scheme.Modules.pullbackPushforwardAdjunction inclusion).unit.app L

attribute [instance] CartierZero.closed

/-- The actual zero/pole presentation of a rational line section. -/
structure CartierFraction (s : RationalSection L) where
  positiveLine : X.Modules
  negativeLine : X.Modules
  positiveIsLine : IsLineBundle positiveLine
  negativeIsLine : IsLineBundle negativeLine
  numerator : Γ(positiveLine,⊤)
  denominator : Γ(negativeLine,⊤)
  positive : CartierZero positiveLine numerator
  negative : CartierZero negativeLine denominator
  comparison : CurvePositivity.moduleTensor X L negativeLine ≅ positiveLine
  equation : ∀ (x : X) (hx : x ∈ s.domain),
    TopCat.Presheaf.germ positiveLine.val.presheaf ⊤ x (by trivial) numerator =
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        comparison.hom.mapPresheaf)
        (TopCat.Presheaf.germ (CurvePositivity.moduleTensor X L negativeLine).val.presheaf
          s.domain x hx
          (MetrizedFibrePowerModels.tensorSectionAt L negativeLine s.domain s.value
            (negativeLine.val.map (homOfLE (le_top : s.domain ≤ ⊤)).op denominator)))

variable (R : Type) [CommRing R]

/-- The native sorted tensor of actual local sections, including the scalar unit. -/
def sectionTensor {Z : Scheme.{0}} {m : ℕ} (Ns : Fin m → Z.Modules) (U : Z.Opens)
    (e : ∀ i : Fin m, Γ(Ns i,U)) :
    (is : List (Fin m)) → Γ(is.foldr
      (fun i M ↦ AlgebraicLineBundleFamilies.moduleTensor Z (Ns i) M) (structureModule Z),U)
  | [] => (1 : Γ(Z,U))
  | i :: is => MetrizedFibrePowerModels.tensorSectionAt (Ns i)
      (is.foldr (fun j M ↦ AlgebraicLineBundleFamilies.moduleTensor Z (Ns j) M)
        (structureModule Z)) U (e i) (sectionTensor Ns U e is)

def subsetSection {Z : Scheme.{0}} {m : ℕ} (Ns : Fin m → Z.Modules) (U : Z.Opens)
    (e : ∀ i : Fin m, Γ(Ns i,U)) (t : Finset (Fin m)) : Γ(subsetTensor Ns t,U) :=
  sectionTensor Ns U e (t.sort (· ≤ ·))

abbrev GradedSubsets (m : ℕ) (i : ℤ) :=
  {t : Finset (Fin m) // CanonicalKoszulDeterminants.subsetDegree t = i}

instance gradedSubsetsFintype (m : ℕ) (i : ℤ) : Fintype (GradedSubsets m i) :=
  Fintype.ofFinite _

local instance schemeFiniteBiproducts (Z : Scheme.{0}) : HasFiniteBiproducts Z.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- Every full section Koszul term is the actual sum of its original subset sheaves. -/
structure KoszulSubsetTerms {Z : Scheme.{0}} {m : ℕ} (Ns : Fin m → Z.Modules) where
  cochain : CochainComplex Z.Modules ℤ
  terms : ∀ i : ℤ, cochain.X i ≅
    biproduct (fun t : GradedSubsets m i ↦ subsetTensor Ns t.val)

def KoszulSubsetTerms.inclusion {Z : Scheme.{0}} {m : ℕ} {Ns : Fin m → Z.Modules}
    (K : KoszulSubsetTerms Ns) (t : Finset (Fin m)) :
    subsetTensor Ns t ⟶ K.cochain.X (CanonicalKoszulDeterminants.subsetDegree t) :=
  biproduct.ι (fun u : GradedSubsets m (CanonicalKoszulDeterminants.subsetDegree t) ↦
    subsetTensor Ns u.val) ⟨t,rfl⟩ ≫ (K.terms _).inv

def KoszulSubsetTerms.projection {Z : Scheme.{0}} {m : ℕ} {Ns : Fin m → Z.Modules}
    (K : KoszulSubsetTerms Ns) (t : Finset (Fin m)) :
    K.cochain.X (CanonicalKoszulDeterminants.subsetDegree t) ⟶ subsetTensor Ns t :=
  (K.terms _).hom ≫
    biproduct.π (fun u : GradedSubsets m (CanonicalKoszulDeterminants.subsetDegree t) ↦
      subsetTensor Ns u.val) ⟨t,rfl⟩

def KoszulSubsetTerms.block {Z : Scheme.{0}} {m : ℕ} {Ns : Fin m → Z.Modules}
    (K : KoszulSubsetTerms Ns) (t u : Finset (Fin m)) : subsetTensor Ns t ⟶ subsetTensor Ns u :=
  K.inclusion t ≫ K.cochain.d (CanonicalKoszulDeterminants.subsetDegree t)
    (CanonicalKoszulDeterminants.subsetDegree u) ≫ K.projection u

/-- The actual full section Koszul complex, with signed insertion in the original
subset degrees. Every insertion is fixed on all genuine local pure tensors. -/
structure FullSectionKoszul {Z : Scheme.{0}} {m : ℕ} (Ns : Fin m → Z.Modules)
    (s : ∀ i : Fin m, Γ(Ns i,⊤)) extends KoszulSubsetTerms Ns where
  insertion : ∀ (t : Finset (Fin m)) (j : Fin m), j ∉ t →
    (subsetTensor Ns t ⟶ subsetTensor Ns (insert j t))
  insertion_normalized : ∀ (t : Finset (Fin m)) (j : Fin m) (hj : j ∉ t)
    (U : Z.Opens) (e : ∀ i : Fin m, Γ(Ns i,U)),
    (insertion t j hj).app U (subsetSection Ns U e t) =
      subsetSection Ns U
        (fun i ↦ if i = j then (Ns i).val.map (homOfLE (le_top : U ≤ ⊤)).op (s i) else e i)
        (insert j t)
  differential_insert : ∀ (t : Finset (Fin m)) (j : Fin m) (hj : j ∉ t),
    toKoszulSubsetTerms.block t (insert j t) =
      ((-1 : ℤ) ^ (t.filter (· < j)).card) • insertion t j hj
  differential_other : ∀ t u : Finset (Fin m),
    (∀ j : Fin m, j ∉ t → insert j t ≠ u) → toKoszulSubsetTerms.block t u = 0
  acyclic : ∀ i : ℤ, (cochain.sc i).Exact

/-- Evaluation of a line and its actual module dual fixes every coefficient. -/
structure EvaluationSource (M : ModuleCat.{0} R) where
  comparison : (ModuleCat.of R (Module.Dual R M) ⊗ M) ≅ 𝟙_ (ModuleCat.{0} R)
  normalized : ∀ (f : Module.Dual R M) (x : M), comparison.hom (f ⊗ₜ[R] x) = f x

attribute [local instance] HasDerivedCategory.standard

/-- The primitive source maps of a bounded determinant calculation. -/
inductive DeterminantWord : ModuleCat.{0} R → ModuleCat.{0} R → Type 1
  | identity (M) : DeterminantWord M M
  | compose {M N P} : DeterminantWord M N → DeterminantWord N P → DeterminantWord M P
  | inverse {M N} : DeterminantWord M N → DeterminantWord N M
  | tensor {M N P Q} : DeterminantWord M N → DeterminantWord P Q →
      DeterminantWord (M ⊗ P) (N ⊗ Q)
  | associate (M N P) : DeterminantWord ((M ⊗ N) ⊗ P) (M ⊗ (N ⊗ P))
  | commute (M N) : DeterminantWord (M ⊗ N) (N ⊗ M)
  | leftUnit (M) : DeterminantWord ((𝟙_ (ModuleCat.{0} R)) ⊗ M) M
  | rightUnit (M) : DeterminantWord (M ⊗ (𝟙_ (ModuleCat.{0} R))) M
  | evaluate (M) (E : EvaluationSource R M) :
      DeterminantWord (ModuleCat.of R (Module.Dual R M) ⊗ M) (𝟙_ (ModuleCat.{0} R))
  | zero (M : ModuleCat.{0} R) (h : IsZero M) :
      DeterminantWord (ModuleCat.of R (determinantModule R M)) (𝟙_ (ModuleCat.{0} R))
  | exact (M N : ModuleCat.{0} R) [Module.Finite R M] [Module.Projective R M]
      [Module.Finite R N] [Module.Projective R N]
      (f : M →ₗ[R] N) (hf : Function.Surjective f) (E : ShortExactDeterminant f hf) :
      DeterminantWord
        (ModuleCat.of R (determinantModule R (LinearMap.ker f)) ⊗
          ModuleCat.of R (determinantModule R N))
        (ModuleCat.of R (determinantModule R M))
  | strict (C D : BoundedProjectiveDeterminants.Complex R) (e : C.cochain ≅ D.cochain) :
      DeterminantWord (determinantObject R C) (determinantObject R D)
  | derived (I : TransportSystem R) (C D : BoundedProjectiveDeterminants.Complex R)
      (e : DerivedCategory.Q.obj C.cochain ≅ DerivedCategory.Q.obj D.cochain) :
      DeterminantWord (determinantObject R C) (determinantObject R D)

variable {R} in
/-- The map is the literal evaluation of that source word. -/
def DeterminantWord.map {M N : ModuleCat.{0} R} : DeterminantWord R M N → (M ≅ N)
  | .identity _ => Iso.refl _
  | .compose a b => a.map ≪≫ b.map
  | .inverse a => a.map.symm
  | .tensor a b => tensorIso a.map b.map
  | .associate _ _ _ => α_ _ _ _
  | .commute _ _ => β_ _ _
  | .leftUnit _ => λ_ _
  | .rightUnit _ => ρ_ _
  | .evaluate _ E => E.comparison
  | .zero M h => (DeterminantZeroUnits.zeroEquiv R M h).toModuleIso
  | @DeterminantWord.exact _ _ M N _ _ _ _ f hf E => E.comparison.toModuleIso
  | .strict C D e => determinantIso R C D e
  | .derived I C D e => I.map ⟨C⟩ ⟨D⟩ e

variable [FourierMukai.HasDerivedPullbacks.{0}] [FourierMukai.HasDerivedPushforwards.{0}]
  [AffineDerivedCoefficientModules.HasDerivedScalarExtensions.{0}]
  [∀ S : CommRingCat.{0}, PreservesFiniteLimits (tilde.functor S)]
  [∀ S : CommRingCat.{0}, ProjectiveSources S]

/-- The actual boundary quotient map of the source differential. -/
def boundaryMap (C : BoundedProjectiveDeterminants.Complex R) (i : ℤ) :
    C.cochain.X i →ₗ[R] LinearMap.ker ((C.cochain.d (i+1) (i+2)).hom) :=
  ((C.cochain.d i (i+1)).hom).codRestrict _ (by
    intro x
    change (C.cochain.d (i+1) (i+2)) ((C.cochain.d i (i+1)) x) = 0
    exact congrArg (fun q : C.cochain.X i ⟶ C.cochain.X (i+2) ↦ q x)
      (C.cochain.d_comp_d i (i+1) (i+2)))

/-- A bounded source is the actual affine derived image of this section Koszul map. -/
structure KoszulAffineSource {Z Y : Scheme.{0}} (f : Z ⟶ Y)
    (N : Z.Modules) (s : Γ(N,⊤)) (S : CommRingCat.{0}) (a : Spec S ⟶ Y) where
  koszul : SectionKoszul N s
  complex : BoundedProjectiveDeterminants.Complex S
  comparison : (AffineDerivedCoefficientModules.derivedTilde S).obj
    (DerivedCategory.Q.obj complex.cochain) ≅
      (FourierMukai.derivedPullback a).obj
        ((FourierMukai.derivedPushforward f).obj (DerivedCategory.Q.obj koszul.cochain))
  sourcePresentation : AffinePresentation (directImage f (structureModule Z)) S a
  targetPresentation : AffinePresentation (directImage f N) S a
  sectionMap : sourcePresentation.complex.cochain ⟶ targetPresentation.complex.cochain
  sectionMap_normalized :
    (AffineDerivedCoefficientModules.derivedTilde S).map (DerivedCategory.Q.map sectionMap) ≫
      targetPresentation.comparison.hom = sourcePresentation.comparison.hom ≫
        (FourierMukai.derivedPullback a).map
          ((FourierMukai.derivedPushforward f).map
            ((DerivedCategory.singleFunctor Z.Modules 0).map (topSectionHom Z N s)))

/-- Tensor-twisted Cartier maps are pinned on every actual local section. -/
structure TwistedSectionKoszul {Z : Scheme.{0}} (E N : Z.Modules) (s : Γ(N,⊤)) where
  sectionMap : E ⟶ CurvePositivity.moduleTensor Z E N
  sectionNormalized : ∀ (U : Z.Opens) (e : Γ(E,U)), sectionMap.app U e =
    MetrizedFibrePowerModels.tensorSectionAt E N U e
      (N.val.map (homOfLE (le_top : U ≤ ⊤)).op s)
  cochain : CochainComplex Z.Modules ℤ
  source : cochain.X 0 ≅ E
  target : cochain.X 1 ≅ CurvePositivity.moduleTensor Z E N
  zeroTerms : ∀ i : ℤ, i ≠ 0 → i ≠ 1 → IsZero (cochain.X i)
  differential : cochain.d 0 1 = source.hom ≫ sectionMap ≫ target.inv

structure TwistedKoszulAffineSource {Z Y : Scheme.{0}} (f : Z ⟶ Y)
    (E N : Z.Modules) (s : Γ(N,⊤)) (S : CommRingCat.{0}) (a : Spec S ⟶ Y) where
  koszul : TwistedSectionKoszul E N s
  complex : BoundedProjectiveDeterminants.Complex S
  comparison : (AffineDerivedCoefficientModules.derivedTilde S).obj
    (DerivedCategory.Q.obj complex.cochain) ≅
      (FourierMukai.derivedPullback a).obj
        ((FourierMukai.derivedPushforward f).obj (DerivedCategory.Q.obj koszul.cochain))
  sourcePresentation : AffinePresentation (directImage f E) S a
  targetPresentation : AffinePresentation (directImage f (CurvePositivity.moduleTensor Z E N)) S a
  sectionMap : sourcePresentation.complex.cochain ⟶ targetPresentation.complex.cochain
  sectionMap_normalized :
    (AffineDerivedCoefficientModules.derivedTilde S).map (DerivedCategory.Q.map sectionMap) ≫
      targetPresentation.comparison.hom = sourcePresentation.comparison.hom ≫
        (FourierMukai.derivedPullback a).map
          ((FourierMukai.derivedPushforward f).map
            ((DerivedCategory.singleFunctor Z.Modules 0).map koszul.sectionMap))

/-- Derived shift maps are fixed by the COMPLETE native cochain unit/counit
squares. Their data cannot rescale a filtration connecting morphism. -/
class DerivedFunctorShiftSources where
  [pushforward : ∀ {Z T : Scheme.{0}} (g : Z ⟶ T), (FourierMukai.derivedPushforward g).CommShift ℤ]
  [pullback : ∀ {Z T : Scheme.{0}} (g : Z ⟶ T), (FourierMukai.derivedPullback g).CommShift ℤ]
  pushforward_normalized : ∀ {Z T : Scheme.{0}} (g : Z ⟶ T) (C : CochainComplex Z.Modules ℤ),
    (FourierMukai.derivedPushforwardUnit g).app (C⟦(1 : ℤ)⟧) ≫
      (FourierMukai.derivedPushforward g).map ((DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app C) ≫
      ((FourierMukai.derivedPushforward g).commShiftIso (1 : ℤ)).hom.app (DerivedCategory.Q.obj C) =
    DerivedCategory.Q.map
        ((((Scheme.Modules.pushforward g).mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso
          (1 : ℤ)).hom.app C) ≫
      (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
        (((Scheme.Modules.pushforward g).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) ≫
      ((FourierMukai.derivedPushforwardUnit g).app C)⟦(1 : ℤ)⟧'
  pullback_normalized : ∀ {Z T : Scheme.{0}} (g : Z ⟶ T) (C : CochainComplex T.Modules ℤ),
    (FourierMukai.derivedPullback g).map ((DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app C) ≫
      ((FourierMukai.derivedPullback g).commShiftIso (1 : ℤ)).hom.app (DerivedCategory.Q.obj C) ≫
      ((FourierMukai.derivedPullbackCounit g).app C)⟦(1 : ℤ)⟧' =
    (FourierMukai.derivedPullbackCounit g).app (C⟦(1 : ℤ)⟧) ≫
      DerivedCategory.Q.map
        ((((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso
          (1 : ℤ)).hom.app C) ≫
      (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
        (((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj C)

attribute [instance_reducible] DerivedFunctorShiftSources.pushforward DerivedFunctorShiftSources.pullback
attribute [instance] DerivedFunctorShiftSources.pushforward DerivedFunctorShiftSources.pullback

@[instance_reducible] def derivedTildeShift (S : CommRingCat.{0}) :
    (AffineDerivedCoefficientModules.derivedTilde S).CommShift ℤ := by
  dsimp [AffineDerivedCoefficientModules.derivedTilde]
  infer_instance

attribute [instance] derivedTildeShift

def shiftedAffineComparison [DerivedFunctorShiftSources] {Z Y : Scheme.{0}}
    {f : Z ⟶ Y} {N : Z.Modules} {S : CommRingCat.{0}} {a : Spec S ⟶ Y}
    (P₀ : AffinePresentation (directImage f N) S a) (p : ℤ) :
    (AffineDerivedCoefficientModules.derivedTilde S).obj
        (DerivedCategory.Q.obj (P₀.complex.cochain⟦-p⟧)) ≅
      (FourierMukai.derivedPullback a).obj ((FourierMukai.derivedPushforward f).obj
        (DerivedCategory.Q.obj (((CochainComplex.singleFunctor Z.Modules 0).obj N)⟦-p⟧))) :=
  (AffineDerivedCoefficientModules.derivedTilde S).mapIso
      ((DerivedCategory.Q.commShiftIso (-p)).app P₀.complex.cochain) ≪≫
    ((AffineDerivedCoefficientModules.derivedTilde S).commShiftIso (-p)).app
      (DerivedCategory.Q.obj P₀.complex.cochain) ≪≫
    (shiftFunctor _ (-p)).mapIso P₀.comparison ≪≫
    (((FourierMukai.derivedPushforward f ⋙ FourierMukai.derivedPullback a).commShiftIso (-p)).app
      ((DerivedCategory.singleFunctor Z.Modules 0).obj N)).symm ≪≫
    (FourierMukai.derivedPushforward f ⋙ FourierMukai.derivedPullback a).mapIso
      ((DerivedCategory.Q.commShiftIso (-p)).app ((CochainComplex.singleFunctor Z.Modules 0).obj N)).symm

/-- The FULL pushed Koszul filtration, including every native SES connecting
map. Coefficients are the SAME original P modules and literal subset sums.
The triangle comparisons have fixed graded maps, so a higher fill cannot
be multiplied by an arbitrary unit, even when the full derived object is zero. -/
structure FilteredKoszulSource {Z Y : Scheme.{0}} (f : Z ⟶ Y) {m : ℕ}
    (Ns : Fin m → Z.Modules) (s : ∀ i : Fin m, Γ(Ns i,⊤))
    (K : FullSectionKoszul Ns s) (S : CommRingCat.{0}) (a : Spec S ⟶ Y)
    (P₀ : Presentations f Ns S a)
    (M : CanonicalKoszulDeterminants.TotalTermModel S (fun t ↦ (P₀ t).complex)) where
  [shifts : DerivedFunctorShiftSources]
  coefficient : ∀ p : ℤ, CanonicalKoszulDeterminants.ListTermModel S (fun t ↦ (P₀ t).complex)
    ((CanonicalKoszulDeterminants.subsets m).filter (fun t ↦ p ≤ CanonicalKoszulDeterminants.subsetDegree t))
  gradedCoefficient : ∀ p : ℤ, CanonicalKoszulDeterminants.ListTermModel S (fun t ↦ (P₀ t).complex)
    ((CanonicalKoszulDeterminants.subsets m).filter (fun t ↦ CanonicalKoszulDeterminants.subsetDegree t = p))
  fullCoefficient : (coefficient (-(m : ℤ))).complex.cochain = M.complex.cochain
  coefficientInFull : ∀ p : ℤ, (coefficient p).complex.cochain ⟶ M.complex.cochain
  coefficientInFull_normalized : ∀ (p i : ℤ)
    (x : CanonicalKoszulDeterminants.sumTerms S (fun t ↦ (P₀ t).complex) i
      ((CanonicalKoszulDeterminants.subsets m).filter (fun t ↦ p ≤ CanonicalKoszulDeterminants.subsetDegree t))),
    (M.assembly.termIso i).hom ((coefficientInFull p).f i (((coefficient p).termIso i).inv x)) =
      CanonicalKoszulDeterminants.sumBetween S (fun t ↦ (P₀ t).complex) i
        ((CanonicalKoszulDeterminants.subsets m).filter (fun t ↦ p ≤ CanonicalKoszulDeterminants.subsetDegree t))
        (CanonicalKoszulDeterminants.subsets m) x
  inclusion : ∀ p : ℤ, (coefficient (p+1)).complex.cochain ⟶ (coefficient p).complex.cochain
  inclusion_normalized : ∀ (p i : ℤ)
    (x : CanonicalKoszulDeterminants.sumTerms S (fun t ↦ (P₀ t).complex) i
      ((CanonicalKoszulDeterminants.subsets m).filter (fun t ↦ p+1 ≤ CanonicalKoszulDeterminants.subsetDegree t))),
    ((coefficient p).termIso i).hom ((inclusion p).f i (((coefficient (p+1)).termIso i).inv x)) =
      CanonicalKoszulDeterminants.sumBetween S (fun t ↦ (P₀ t).complex) i
        ((CanonicalKoszulDeterminants.subsets m).filter (fun t ↦ p+1 ≤ CanonicalKoszulDeterminants.subsetDegree t))
        ((CanonicalKoszulDeterminants.subsets m).filter (fun t ↦ p ≤ CanonicalKoszulDeterminants.subsetDegree t)) x
  quotient : ∀ p : ℤ, (coefficient p).complex.cochain ⟶ (gradedCoefficient p).complex.cochain
  quotient_normalized : ∀ (p i : ℤ)
    (x : CanonicalKoszulDeterminants.sumTerms S (fun t ↦ (P₀ t).complex) i
      ((CanonicalKoszulDeterminants.subsets m).filter (fun t ↦ p ≤ CanonicalKoszulDeterminants.subsetDegree t))),
    ((gradedCoefficient p).termIso i).hom ((quotient p).f i (((coefficient p).termIso i).inv x)) =
      CanonicalKoszulDeterminants.sumBetween S (fun t ↦ (P₀ t).complex) i
        ((CanonicalKoszulDeterminants.subsets m).filter (fun t ↦ p ≤ CanonicalKoszulDeterminants.subsetDegree t))
        ((CanonicalKoszulDeterminants.subsets m).filter (fun t ↦ CanonicalKoszulDeterminants.subsetDegree t = p)) x
  coefficient_zero : ∀ p : ℤ, inclusion p ≫ quotient p = 0
  coefficientExact : ∀ p : ℤ, (ShortComplex.mk (inclusion p) (quotient p) (coefficient_zero p)).ShortExact
  sheaf : ℤ → CochainComplex Z.Modules ℤ
  fullSheaf : sheaf (-(m : ℤ)) = K.cochain
  sheafTerms : ∀ (p i : ℤ), p ≤ i → (sheaf p).X i = K.cochain.X i
  sheafZero : ∀ (p i : ℤ), i < p → IsZero ((sheaf p).X i)
  sheafInFull : ∀ p : ℤ, sheaf p ⟶ K.cochain
  sheafInFull_normalized : ∀ (p i : ℤ), p ≤ i → HEq ((sheafInFull p).f i) (𝟙 (K.cochain.X i))
  sheafInclusion : ∀ p : ℤ, sheaf (p+1) ⟶ sheaf p
  sheafInclusion_normalized : ∀ p : ℤ, sheafInclusion p ≫ sheafInFull p = sheafInFull (p+1)
  sheafQuotient : ∀ p : ℤ, sheaf p ⟶ (CochainComplex.singleFunctor Z.Modules p).obj (K.cochain.X p)
  sheafQuotient_normalized : ∀ p : ℤ, HEq ((sheafQuotient p).f p) (𝟙 (K.cochain.X p))
  sheaf_zero : ∀ p : ℤ, sheafInclusion p ≫ sheafQuotient p = 0
  sheafExact : ∀ p : ℤ, (ShortComplex.mk (sheafInclusion p) (sheafQuotient p) (sheaf_zero p)).ShortExact
  originalInclusion : ∀ t : Finset (Fin m),
    (P₀ t).complex.cochain⟦-CanonicalKoszulDeterminants.subsetDegree t⟧ ⟶
      (gradedCoefficient (CanonicalKoszulDeterminants.subsetDegree t)).complex.cochain
  originalInclusion_normalized : ∀ (t : Finset (Fin m)) (i : ℤ),
    HEq (((originalInclusion t).f i) ≫ ((gradedCoefficient (CanonicalKoszulDeterminants.subsetDegree t)).termIso i).hom)
      (ModuleCat.ofHom (CanonicalKoszulDeterminants.sumInclusion S (fun u ↦ (P₀ u).complex) i t
        ((CanonicalKoszulDeterminants.subsets m).filter
          (fun u ↦ CanonicalKoszulDeterminants.subsetDegree u = CanonicalKoszulDeterminants.subsetDegree t))))
  originalSingle : ∀ t : Finset (Fin m),
    ((CochainComplex.singleFunctor Z.Modules 0).obj (subsetTensor Ns t))⟦-CanonicalKoszulDeterminants.subsetDegree t⟧ ≅
      (CochainComplex.singleFunctor Z.Modules (CanonicalKoszulDeterminants.subsetDegree t)).obj (subsetTensor Ns t)
  originalSingle_normalized : ∀ t : Finset (Fin m),
    HEq ((originalSingle t).hom.f (CanonicalKoszulDeterminants.subsetDegree t)) (𝟙 (subsetTensor Ns t))
  comparison : ∀ p : ℤ,
    (AffineDerivedCoefficientModules.derivedTilde S).obj (DerivedCategory.Q.obj (coefficient p).complex.cochain) ≅
      (FourierMukai.derivedPullback a).obj ((FourierMukai.derivedPushforward f).obj (DerivedCategory.Q.obj (sheaf p)))
  gradedComparison : ∀ p : ℤ,
    (AffineDerivedCoefficientModules.derivedTilde S).obj (DerivedCategory.Q.obj (gradedCoefficient p).complex.cochain) ≅
      (FourierMukai.derivedPullback a).obj ((FourierMukai.derivedPushforward f).obj
        ((DerivedCategory.singleFunctor Z.Modules p).obj (K.cochain.X p)))
  graded_normalized : ∀ t : Finset (Fin m),
    (AffineDerivedCoefficientModules.derivedTilde S).map (DerivedCategory.Q.map (originalInclusion t)) ≫
      (gradedComparison (CanonicalKoszulDeterminants.subsetDegree t)).hom =
    (shiftedAffineComparison (P₀ t) (CanonicalKoszulDeterminants.subsetDegree t)).hom ≫
      (FourierMukai.derivedPushforward f ⋙ FourierMukai.derivedPullback a).map
        (DerivedCategory.Q.map (originalSingle t).hom) ≫
      (FourierMukai.derivedPushforward f ⋙ FourierMukai.derivedPullback a).map
        ((DerivedCategory.singleFunctor Z.Modules (CanonicalKoszulDeterminants.subsetDegree t)).map
          (K.toKoszulSubsetTerms.inclusion t))
  triangle : ∀ p : ℤ,
    (AffineDerivedCoefficientModules.derivedTilde S).mapTriangle.obj
      (DerivedCategory.triangleOfSES (coefficientExact p)) ≅
    (FourierMukai.derivedPushforward f ⋙ FourierMukai.derivedPullback a).mapTriangle.obj
      (DerivedCategory.triangleOfSES (sheafExact p))
  triangle_first : ∀ p : ℤ, (triangle p).hom.hom₁ = (comparison (p+1)).hom
  triangle_middle : ∀ p : ℤ, (triangle p).hom.hom₂ = (comparison p).hom
  triangle_last : ∀ p : ℤ, (triangle p).hom.hom₃ = (gradedComparison p).hom

def FilteredKoszulSource.fullComparison {Z Y : Scheme.{0}} {f : Z ⟶ Y} {m : ℕ}
    {Ns : Fin m → Z.Modules} {s : ∀ i : Fin m, Γ(Ns i,⊤)} {K : FullSectionKoszul Ns s}
    {S : CommRingCat.{0}} {a : Spec S ⟶ Y} {P₀ : Presentations f Ns S a}
    {M : CanonicalKoszulDeterminants.TotalTermModel S (fun t ↦ (P₀ t).complex)}
    (T : FilteredKoszulSource f Ns s K S a P₀ M) :
    (AffineDerivedCoefficientModules.derivedTilde S).obj (DerivedCategory.Q.obj M.complex.cochain) ≅
      (FourierMukai.derivedPullback a).obj
        ((FourierMukai.derivedPushforward f).obj (DerivedCategory.Q.obj K.cochain)) :=
  (AffineDerivedCoefficientModules.derivedTilde S).mapIso (DerivedCategory.Q.mapIso (eqToIso T.fullCoefficient)).symm ≪≫
    T.comparison (-(m : ℤ)) ≪≫
    (FourierMukai.derivedPushforward f ⋙ FourierMukai.derivedPullback a).mapIso
      (DerivedCategory.Q.mapIso (eqToIso T.fullSheaf))

/-- The full actual affine cochain totalization. The subset terms are literally
the original P modules. Diagonal differentials and section insertions retain
their native coefficients; higher coherent terms can only increase subsets. -/
structure FullKoszulAffineSource {Z Y : Scheme.{0}} (f : Z ⟶ Y) {m : ℕ}
    (Ns : Fin m → Z.Modules) (s : ∀ i : Fin m, Γ(Ns i,⊤))
    (K : FullSectionKoszul Ns s) (S : CommRingCat.{0}) (a : Spec S ⟶ Y)
    (P₀ : Presentations f Ns S a) extends
      CanonicalKoszulDeterminants.TotalTermModel S (fun t ↦ (P₀ t).complex) where
  filtered : FilteredKoszulSource f Ns s K S a P₀ toTotalTermModel
  sectionMap : ∀ (t : Finset (Fin m)) (j : Fin m), j ∉ t →
    ((P₀ t).complex.cochain ⟶ (P₀ (insert j t)).complex.cochain)
  sectionMap_normalized : ∀ (t : Finset (Fin m)) (j : Fin m) (hj : j ∉ t),
    (AffineDerivedCoefficientModules.derivedTilde S).map
        (DerivedCategory.Q.map (sectionMap t j hj)) ≫ (P₀ (insert j t)).comparison.hom =
      (P₀ t).comparison.hom ≫ (FourierMukai.derivedPullback a).map
        ((FourierMukai.derivedPushforward f).map
          ((DerivedCategory.singleFunctor Z.Modules 0).map (K.insertion t j hj)))
  diagonal : ∀ (i : ℤ) (t : Finset (Fin m)),
    HEq (toTotalTermModel.block i t t)
      (((-1 : ℤ) ^ (CanonicalKoszulDeterminants.subsetDegree t).natAbs) •
        (P₀ t).complex.cochain.d (i-CanonicalKoszulDeterminants.subsetDegree t)
          (i-CanonicalKoszulDeterminants.subsetDegree t+1))
  insertion : ∀ (i : ℤ) (t : Finset (Fin m)) (j : Fin m) (hj : j ∉ t),
    HEq (toTotalTermModel.block i t (insert j t))
      (((-1 : ℤ) ^ (t.filter (· < j)).card) •
        (sectionMap t j hj).f (i-CanonicalKoszulDeterminants.subsetDegree t))
  upperTriangular : ∀ (i : ℤ) (t u : Finset (Fin m)),
    ¬ t ⊆ u → toTotalTermModel.block i t u = 0
  acyclic : ∀ i : ℤ, Function.Surjective (CanonicalKoszulDeterminants.boundaryMap S complex i)

def FullKoszulAffineSource.comparison {Z Y : Scheme.{0}} {f : Z ⟶ Y} {m : ℕ}
    {Ns : Fin m → Z.Modules} {s : ∀ i : Fin m, Γ(Ns i,⊤)}
    {K : FullSectionKoszul Ns s} {S : CommRingCat.{0}} {a : Spec S ⟶ Y}
    {P₀ : Presentations f Ns S a} (C : FullKoszulAffineSource f Ns s K S a P₀) :
    (AffineDerivedCoefficientModules.derivedTilde S).obj (DerivedCategory.Q.obj C.complex.cochain) ≅
      (FourierMukai.derivedPullback a).obj
        ((FourierMukai.derivedPushforward f).obj (DerivedCategory.Q.obj K.cochain)) :=
  C.filtered.fullComparison

def FullKoszulAffineSource.presentation {Z Y : Scheme.{0}} {f : Z ⟶ Y} {m : ℕ}
    {Ns : Fin m → Z.Modules} {s : ∀ i : Fin m, Γ(Ns i,⊤)}
    {K : FullSectionKoszul Ns s} {S : CommRingCat.{0}} {a : Spec S ⟶ Y}
    {P₀ : Presentations f Ns S a} (C : FullKoszulAffineSource f Ns s K S a P₀) :
    AffinePresentation ((FourierMukai.derivedPushforward f).obj
      (DerivedCategory.Q.obj K.cochain)) S a := ⟨C.complex, C.comparison⟩

variable {Y : Scheme.{0}} (I : DeterminantSources) (f : X ⟶ Y) (n : ℕ)
  (Ls : Fin (n + 1) → X.Modules)
  (P : ∀ (S : CommRingCat.{0}) (a : Spec S ⟶ Y), Presentations f Ls S a)
  (D : DeligneLine I f n Ls P)

/-- Actual finite Tor-dimension, measured by homology of the native derived
pullback on EVERY original degree-zero module sheaf. -/
def FiniteTorDimension {Z T : Scheme.{0}} (g : Z ⟶ T) : Prop :=
  ∃ a b : ℤ, ∀ (N : T.Modules) (i : ℤ), i < a ∨ b < i →
    IsZero ((DerivedCategory.homologyFunctor Z.Modules i).obj
      ((FourierMukai.derivedPullback g).obj ((DerivedCategory.singleFunctor T.Modules 0).obj N)))

/-- The algebraic finite-Tor induction scope of pp107--108. The source may
be nonreduced/nonintegral and f need not be flat; the actual normal integral
base fixes extension of the canonical regular section from a dense open. -/
structure FiniteTorRelativeScope {Z T : Scheme.{0}} (g : Z ⟶ T) (d : ℕ) : Prop where
  projective : ∀ (R : CommRingCat.{0}) (a : Spec R ⟶ T),
    RelativePolynomialProjectivity.IsProjective (pullback.snd g a)
  finiteTor : FiniteTorDimension g
  pureDimension : IsPureRelativeDimension g d
  targetIntegral : IsIntegral T
  normal : ∀ t : T, IsDomain (T.presheaf.stalk t) ∧ IsIntegrallyClosed (T.presheaf.stalk t)

/-- The source ORDERED strongly regular tuple. Only this order's successive
Cartier intersections are required to be pure over the base; a permutation
can have a vertical first divisor. The final map may be nonflat and the
final section may have zeros, exactly as in Yuan--Zhang pp107--108. -/
structure StrongRegularTuple where
  isLine : ∀ i : Fin (n+1), IsLineBundle (Ls i)
  sectionValue : ∀ i, Γ(Ls i,⊤)
  flag : Fin (n+1) → Scheme.{0}
  inclusion : ∀ j, flag j ⟶ X
  first : flag 0 ≅ X
  firstMap : first.hom = inclusion 0
  restricted : ∀ j, Γ((Scheme.Modules.pullback (inclusion j)).obj (Ls j),⊤)
  restrictedSource : ∀ j, restricted j =
    localPullbackSection (inclusion j) (Ls j) ⊤ ⊤ (by simp) (sectionValue j)
  divisor : ∀ j : Fin n,
    CartierZero ((Scheme.Modules.pullback (inclusion j.castSucc)).obj (Ls j.castSucc))
      (restricted j.castSucc)
  next : ∀ j : Fin n, (divisor j).scheme ≅ flag j.succ
  nextMap : ∀ j : Fin n,
    (next j).hom ≫ inclusion j.succ = (divisor j).inclusion ≫ inclusion j.castSucc
  finiteTor : ∀ j, FiniteTorDimension (inclusion j ≫ f)
  relativeDimension : ∀ j, IsPureRelativeDimension (inclusion j ≫ f) (n-j.val)
  finiteLast : IsFinite (inclusion (Fin.last n) ≫ f)
  lastCartier : CartierZero ((Scheme.Modules.pullback (inclusion (Fin.last n))).obj (Ls (Fin.last n)))
    (restricted (Fin.last n))

/-- All orders of a chosen local generator are retained for source transitions. -/
structure AllOrderRegularTuple where
  isLine : ∀ i : Fin (n+1), IsLineBundle (Ls i)
  sectionValue : ∀ i, Γ(Ls i,⊤)
  flag : ∀ σ : Equiv.Perm (Fin (n+1)), Fin (n+1) → Scheme.{0}
  inclusion : ∀ σ j, flag σ j ⟶ X
  first : ∀ σ, flag σ 0 ≅ X
  firstMap : ∀ σ, (first σ).hom = inclusion σ 0
  restricted : ∀ σ j, Γ((Scheme.Modules.pullback (inclusion σ j)).obj (Ls (σ j)),⊤)
  restrictedSource : ∀ σ j, restricted σ j =
    localPullbackSection (inclusion σ j) (Ls (σ j)) ⊤ ⊤ (by simp) (sectionValue (σ j))
  divisor : ∀ σ (j : Fin n),
    CartierZero ((Scheme.Modules.pullback (inclusion σ j.castSucc)).obj (Ls (σ j.castSucc)))
      (restricted σ j.castSucc)
  next : ∀ σ (j : Fin n), (divisor σ j).scheme ≅ flag σ j.succ
  nextMap : ∀ σ (j : Fin n),
    (next σ j).hom ≫ inclusion σ j.succ = (divisor σ j).inclusion ≫ inclusion σ j.castSucc
  finiteTor : ∀ σ j, FiniteTorDimension (inclusion σ j ≫ f)
  relativeDimension : ∀ σ j, IsPureRelativeDimension (inclusion σ j ≫ f) (n-j.val)
  finiteLast : ∀ σ, IsFinite (inclusion σ (Fin.last n) ≫ f)
  lastCartier : ∀ σ,
    CartierZero ((Scheme.Modules.pullback (inclusion σ (Fin.last n))).obj (Ls (σ (Fin.last n))))
      (restricted σ (Fin.last n))

/-- A local generator tuple is the strongly regular source on the open
where its final section is invertible. Full source sections are retained
separately by CanonicalRegularSection and may vanish on the base. -/
structure RegularTuple extends AllOrderRegularTuple f n Ls where
  emptyCommonZero : ∀ σ, ∀ z : flag σ (Fin.last n), IsIso
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat z).map
      (topSectionHom _ _ (restricted σ (Fin.last n))).mapPresheaf)

/-- Canonical regular symbols on the SAME original subset pairing. The
full section Koszul totalization, its exact exterior comparison, actual
acyclic torsion, all principal localization covers and all original
scalar/cochain transitions are retained in this construction output. -/
structure SymbolSources (s : RegularTuple f n Ls) where
  fullKoszul : FullSectionKoszul Ls s.sectionValue
  total : ∀ (S : CommRingCat.{0}) (a : Spec S ⟶ Y),
    FullKoszulAffineSource f Ls s.sectionValue fullKoszul S a (P S a)
  canonical : ∀ (S : CommRingCat.{0}) (a : Spec S ⟶ Y),
    CanonicalKoszulDeterminants.CanonicalEvaluation I (fun t ↦ (P S a t).complex)
      (total S a).complex (total S a).toTotalTermModel.assembly
  koszulAffine : ∀ σ j (S : CommRingCat.{0}) (a : Spec S ⟶ Y),
    KoszulAffineSource (s.inclusion σ j ≫ f)
      ((Scheme.Modules.pullback (s.inclusion σ j)).obj (Ls (σ j)))
      (s.restricted σ j) S a
  comparison_transition : ∀ {R S : CommRingCat.{0}} (g : R ⟶ S)
    (a : Spec R ⟶ Y) (a' : Spec S ⟶ Y) (h : Spec.map g ≫ a = a')
    (C : DeterminantPullbackCoherence.Coherence.{0})
    (B : AffineDerivedCoefficientModules.DerivedComparison g)
    (F : (AffineDerivedCoefficientModules.derivedTilde S).FullyFaithful)
    (T : DeterminantScalarTensorModels.ScalarTensorSources g),
    (determinantTransition I ((FourierMukai.derivedPushforward f).obj
        (DerivedCategory.Q.obj fullKoszul.cochain)) g a a' h
      (total R a).presentation (total S a').presentation C B F).hom ≫
        (canonical S a').comparison.hom =
      (ModuleCat.extendScalars g.hom).map (canonical R a).comparison.hom ≫
        (pairingTransition I f Ls g a a' h (P R a) (P S a') C B F T).hom
  torsion_transition : ∀ {R S : CommRingCat.{0}} (g : R ⟶ S)
    (a : Spec R ⟶ Y) (a' : Spec S ⟶ Y) (h : Spec.map g ≫ a = a')
    (C : DeterminantPullbackCoherence.Coherence.{0})
    (B : AffineDerivedCoefficientModules.DerivedComparison g)
    (F : (AffineDerivedCoefficientModules.derivedTilde S).FullyFaithful),
    (determinantTransition I ((FourierMukai.derivedPushforward f).obj
        (DerivedCategory.Q.obj fullKoszul.cochain)) g a a' h
      (total R a).presentation (total S a').presentation C B F).hom
        (DeterminantScalarTensorModels.vector g
          (determinantObject R (total R a).complex) (canonical R a).torsion) =
      (canonical S a').torsion
  sectionValue : Γ(D.line,⊤)
  affineNormalized : ∀ (S : CommRingCat.{0}) (a : Spec S ⟶ Y),
    (D.affine S a).hom.app ⊤
      (localPullbackSection a D.line ⊤ ⊤ (by simp) sectionValue) =
        (tilde.isoTop (R := S) (localPairing (P S a))).hom (canonical S a).value
  koszulSource : ∀ σ (j : Fin n),
    (s.divisor σ j).koszul.cochain.d 0 1 =
      (s.divisor σ j).koszul.source.hom ≫
        topSectionHom _ _ (s.restricted σ j.castSucc) ≫
          (s.divisor σ j).koszul.target.inv

/-- The section is the image of the fixed canonical acyclic torsion. -/
def localSymbol (s : RegularTuple f n Ls) (S : SymbolSources I f n Ls P D s)
    (T : CommRingCat.{0}) (a : Spec T ⟶ Y) : localPairing (P T a) :=
  (S.canonical T a).value

end MathlibExt.AlgebraicGeometry.DeligneSymbolModels
