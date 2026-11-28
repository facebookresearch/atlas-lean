/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DeligneCubicalModels
public import MathlibExt.AlgebraicGeometry.FiniteCoverLocalComparison

/-!
# Actual open base change for canonical Deligne symbols

The original affine subset cochains are reused literally on an open base.
Only their geometric comparison is transported, through the native open
pullback/pushforward mate and the complete cochain unit/counit square.
Open tensor comparisons retain every actual local section and scalar unit.
Thus a rational symbol on X over the base open is a generator of the SAME
original localPairing, including negative source line bundles.

Sources: Yuan--Zhang, arXiv:2105.13587v9, Section 4.2.1 and Theorem 4.1.3;
Stacks Project, Tags 08IB and 08EU. Proof availability is separate from
these fixed native source maps and comparison requirements.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.OpenDeligneSymbolSources

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
open CoherentCurveLinearSeries RelativeDeterminantPairings GenericSectionMaps
open GlobalBoundedDeterminantModels DeterminantPullbackCoherence
open DeligneSymbolModels DeligneCubicalModels FourierMukai

attribute [local instance] HasDerivedCategory.standard

variable [HasDerivedPullbacks.{0}] [HasDerivedPushforwards.{0}]
  [AffineDerivedCoefficientModules.HasDerivedScalarExtensions.{0}]
  [∀ R : CommRingCat.{0}, PreservesFiniteLimits (tilde.functor R)]
  [∀ R : CommRingCat.{0}, BoundedProjectiveDeterminants.ProjectiveSources R]

def pushedComplex {X Y : Scheme.{0}} (f : X ⟶ Y) (C : Cochains X) : Cochains Y :=
  ((Scheme.Modules.pushforward f).mapHomologicalComplex (ComplexShape.up ℤ)).obj C

/-- Invertibility/coherence is required for the actual native mate, not an assigned base-change map. -/
structure DerivedOpenBaseChange {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) where
  cochainMate : ∀ C : Cochains X,
    pulledComplex U.ι (pushedComplex f C) ⟶
      pushedComplex (FiniteCoverLocalComparison.restrictedMap f U) (pulledComplex (f ⁻¹ᵁ U).ι C)
  component : ∀ (C : Cochains X) (i : ℤ),
    (cochainMate C).f i = FiniteCoverLocalComparison.openBaseChangeMap f U (C.X i)
  comparison : derivedPushforward f ⋙ derivedPullback U.ι ≅
    derivedPullback (f ⁻¹ᵁ U).ι ⋙ derivedPushforward (FiniteCoverLocalComparison.restrictedMap f U)
  normalized : ∀ C : Cochains X,
    (derivedPullback U.ι).map ((derivedPushforwardUnit f).app C) ≫
      comparison.hom.app (DerivedCategory.Q.obj C) ≫
      (derivedPushforward (FiniteCoverLocalComparison.restrictedMap f U)).map
        ((derivedPullbackCounit (f ⁻¹ᵁ U).ι).app C) =
      (derivedPullbackCounit U.ι).app (pushedComplex f C) ≫
        DerivedCategory.Q.map (cochainMate C) ≫
          (derivedPushforwardUnit (FiniteCoverLocalComparison.restrictedMap f U)).app
            (pulledComplex (f ⁻¹ᵁ U).ι C)

def openLines {X Y : Scheme.{0}} (f : X ⟶ Y) {m : ℕ} (L : Fin m → X.Modules)
    (U : Y.Opens) : Fin m → (f ⁻¹ᵁ U).toScheme.Modules :=
  fun i ↦ (Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj (L i)

structure OpenSubsetPullback {X Y : Scheme.{0}} (f : X ⟶ Y) {m : ℕ}
    (L : Fin m → X.Modules) (U : Y.Opens) where
  subset : ∀ t : Finset (Fin m),
    (Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj (subsetTensor L t) ≅ subsetTensor (openLines f L U) t
  normalized : ∀ (t : Finset (Fin m)) (V : X.Opens) (W : (f ⁻¹ᵁ U).toScheme.Opens)
    (h : W ≤ (f ⁻¹ᵁ U).ι ⁻¹ᵁ V) (s : ∀ i : Fin m, Γ(L i,V)),
    (subset t).hom.app W
      (localPullbackSection (f ⁻¹ᵁ U).ι (subsetTensor L t) V W h (subsetSection L V s t)) =
        subsetSection (openLines f L U) W
          (fun i ↦ localPullbackSection (f ⁻¹ᵁ U).ι (L i) V W h (s i)) t
  single : ∀ t : Finset (Fin m),
    pulledComplex (f ⁻¹ᵁ U).ι ((CochainComplex.singleFunctor X.Modules 0).obj (subsetTensor L t)) ≅
      (CochainComplex.singleFunctor (f ⁻¹ᵁ U).toScheme.Modules 0).obj (subsetTensor (openLines f L U) t)
  singleAtZero : ∀ t : Finset (Fin m), HEq ((single t).hom.f 0) (subset t).hom
  counit : ∀ t : Finset (Fin m), IsIso
    ((derivedPullbackCounit (f ⁻¹ᵁ U).ι).app
      ((CochainComplex.singleFunctor X.Modules 0).obj (subsetTensor L t)))

def OpenSubsetPullback.derived {X Y : Scheme.{0}} {f : X ⟶ Y} {m : ℕ}
    {L : Fin m → X.Modules} {U : Y.Opens} (S : OpenSubsetPullback f L U) (t : Finset (Fin m)) :
    (derivedPullback (f ⁻¹ᵁ U).ι).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj (subsetTensor L t)) ≅
      (DerivedCategory.singleFunctor (f ⁻¹ᵁ U).toScheme.Modules 0).obj
        (subsetTensor (openLines f L U) t) := by
  letI := S.counit t
  exact asIso ((derivedPullbackCounit (f ⁻¹ᵁ U).ι).app
      ((CochainComplex.singleFunctor X.Modules 0).obj (subsetTensor L t))) ≪≫
    DerivedCategory.Q.mapIso (S.single t)

structure OpenSources {X Y : Scheme.{0}} (f : X ⟶ Y) {m : ℕ}
    (L : Fin m → X.Modules) (U : Y.Opens) where
  pullbacks : Coherence.{0}
  baseChange : DerivedOpenBaseChange f U
  tensor : OpenSubsetPullback f L U

/-- The actual Cartesian mate from native module units, counits and composition maps. -/
def cartesianMate {Z Y Z' Y' : Scheme.{0}} (f : Z ⟶ Y) (g : Y' ⟶ Y)
    (x : Z' ⟶ Z) (f' : Z' ⟶ Y') (h : x ≫ f = f' ≫ g) (M : Z.Modules) :
    (Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward f).obj M) ⟶
      (Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback x).obj M) :=
  let N := (Scheme.Modules.pullback x).obj M
  (Scheme.Modules.pullback g).map
    ((Scheme.Modules.pushforward f).map ((Scheme.Modules.pullbackPushforwardAdjunction x).unit.app M) ≫
      (Scheme.Modules.pushforwardComp x f).hom.app N ≫
      (Scheme.Modules.pushforwardCongr h).hom.app N ≫
      (Scheme.Modules.pushforwardComp f' g).inv.app N) ≫
    (Scheme.Modules.pullbackPushforwardAdjunction g).counit.app ((Scheme.Modules.pushforward f').obj N)

structure DerivedCartesianBaseChange {Z Y Z' Y' : Scheme.{0}}
    (f : Z ⟶ Y) (g : Y' ⟶ Y) (x : Z' ⟶ Z) (f' : Z' ⟶ Y')
    (square : IsPullback x f' f g) where
  cochainMate : ∀ C : Cochains Z,
    pulledComplex g (pushedComplex f C) ⟶ pushedComplex f' (pulledComplex x C)
  component : ∀ (C : Cochains Z) (i : ℤ),
    (cochainMate C).f i = cartesianMate f g x f' square.w (C.X i)
  comparison : derivedPushforward f ⋙ derivedPullback g ≅ derivedPullback x ⋙ derivedPushforward f'
  normalized : ∀ C : Cochains Z,
    (derivedPullback g).map ((derivedPushforwardUnit f).app C) ≫
      comparison.hom.app (DerivedCategory.Q.obj C) ≫
      (derivedPushforward f').map ((derivedPullbackCounit x).app C) =
      (derivedPullbackCounit g).app (pushedComplex f C) ≫ DerivedCategory.Q.map (cochainMate C) ≫
        (derivedPushforwardUnit f').app (pulledComplex x C)

def pullbackLines {Z Z' : Scheme.{0}} (x : Z' ⟶ Z) {m : ℕ} (L : Fin m → Z.Modules) :
    Fin m → Z'.Modules := fun i ↦ (Scheme.Modules.pullback x).obj (L i)

structure PullbackSubsetSources {Z Z' : Scheme.{0}} (x : Z' ⟶ Z) {m : ℕ} (L : Fin m → Z.Modules) where
  subset : ∀ t : Finset (Fin m),
    (Scheme.Modules.pullback x).obj (subsetTensor L t) ≅ subsetTensor (pullbackLines x L) t
  normalized : ∀ (t : Finset (Fin m)) (U : Z.Opens) (V : Z'.Opens)
    (h : V ≤ x ⁻¹ᵁ U) (s : ∀ i : Fin m, Γ(L i,U)),
    (subset t).hom.app V (localPullbackSection x (subsetTensor L t) U V h (subsetSection L U s t)) =
      subsetSection (pullbackLines x L) V (fun i ↦ localPullbackSection x (L i) U V h (s i)) t
  single : ∀ t : Finset (Fin m),
    pulledComplex x ((CochainComplex.singleFunctor Z.Modules 0).obj (subsetTensor L t)) ≅
      (CochainComplex.singleFunctor Z'.Modules 0).obj (subsetTensor (pullbackLines x L) t)
  singleAtZero : ∀ t : Finset (Fin m), HEq ((single t).hom.f 0) (subset t).hom
  counit : ∀ t : Finset (Fin m), IsIso
    ((derivedPullbackCounit x).app ((CochainComplex.singleFunctor Z.Modules 0).obj (subsetTensor L t)))

def PullbackSubsetSources.derived {Z Z' : Scheme.{0}} {x : Z' ⟶ Z} {m : ℕ} {L : Fin m → Z.Modules}
    (T : PullbackSubsetSources x L) (t : Finset (Fin m)) :
    (derivedPullback x).obj ((DerivedCategory.singleFunctor Z.Modules 0).obj (subsetTensor L t)) ≅
      (DerivedCategory.singleFunctor Z'.Modules 0).obj (subsetTensor (pullbackLines x L) t) := by
  letI := T.counit t
  exact asIso ((derivedPullbackCounit x).app ((CochainComplex.singleFunctor Z.Modules 0).obj (subsetTensor L t))) ≪≫
    DerivedCategory.Q.mapIso (T.single t)

/-- Generic-fibre comparison retains the original affine cochains literally. -/
def cartesianTopPresentations {Z Y Z' : Scheme.{0}} {R : CommRingCat.{0}}
    {f : Z ⟶ Y} {g : Spec R ⟶ Y} {x : Z' ⟶ Z} {f' : Z' ⟶ Spec R}
    {square : IsPullback x f' f g} {m : ℕ} {L : Fin m → Z.Modules}
    (B : DerivedCartesianBaseChange f g x f' square) (T : PullbackSubsetSources x L)
    (H : Coherence.{0}) (P : Presentations f L R g) :
    Presentations f' (pullbackLines x L) R (𝟙 _) := fun t ↦
  ⟨(P t).complex, (P t).comparison ≪≫
    B.comparison.app ((DerivedCategory.singleFunctor Z.Modules 0).obj (subsetTensor L t)) ≪≫
    (derivedPushforward f').mapIso (T.derived t) ≪≫
    ((H.identity (Spec R)).comparison.app (directImage f' (subsetTensor (pullbackLines x L) t))).symm⟩

/-- The complex is literally the original P complex. Its comparison is the
computed native open-base-change transport of the SAME source. -/
def presentations {X Y : Scheme.{0}} {f : X ⟶ Y} {m : ℕ} {L : Fin m → X.Modules}
    {U : Y.Opens} (O : OpenSources f L U)
    (P : ∀ (R : CommRingCat.{0}) (a : Spec R ⟶ Y), Presentations f L R a)
    (R : CommRingCat.{0}) (r : Spec R ⟶ U.toScheme) :
    Presentations (FiniteCoverLocalComparison.restrictedMap f U) (openLines f L U) R r :=
  fun t ↦ ⟨(P R (r ≫ U.ι) t).complex,
    (P R (r ≫ U.ι) t).comparison ≪≫
      ((O.pullbacks.composition r U.ι).comparison.app (directImage f (subsetTensor L t))).symm ≪≫
      (derivedPullback r).mapIso
        (O.baseChange.comparison.app ((DerivedCategory.singleFunctor X.Modules 0).obj (subsetTensor L t))) ≪≫
      (derivedPullback r).mapIso
        ((derivedPushforward (FiniteCoverLocalComparison.restrictedMap f U)).mapIso (O.tensor.derived t))⟩

/-- The full source canonical regular section, including its actual Cartier
zero divisor. It may vanish. Its restriction to a genuine dense native base
open is the image of the SAME original subset/cochain Koszul torsion.
The base is the actual normal integral source of Theorem4.1.3; no basis or
invertibility of the global section is required. -/
structure CanonicalRegularSection {X Y : Scheme.{0}} (I : DeterminantSources)
    (f : X ⟶ Y) (n : ℕ) (L : Fin (n + 1) → X.Modules)
    (P : ∀ (R : CommRingCat.{0}) (a : Spec R ⟶ Y), Presentations f L R a)
    (D : DeligneLine I f n L P) (s : StrongRegularTuple f n L) where
  scope : FiniteTorRelativeScope f n
  generatorDomain : Y.Opens
  dense : Dense (generatorDomain : Set Y)
  openSource : OpenSources f L generatorDomain
  openTuple : RegularTuple (FiniteCoverLocalComparison.restrictedMap f generatorDomain) n
    (openLines f L generatorDomain)
  sectionSource : ∀ i : Fin (n+1), openTuple.sectionValue i =
    localPullbackSection (f ⁻¹ᵁ generatorDomain).ι (L i) ⊤ ⊤ (by simp) (s.sectionValue i)
  flagSource : ∀ j : Fin (n+1),
    openTuple.flag (Equiv.refl _) j ≅ pullback (s.inclusion j ≫ f) generatorDomain.ι
  flagMapSource : ∀ j : Fin (n+1),
    (flagSource j).hom ≫ pullback.fst (s.inclusion j ≫ f) generatorDomain.ι ≫ s.inclusion j =
      openTuple.inclusion (Equiv.refl _) j ≫ (f ⁻¹ᵁ generatorDomain).ι
  openD : DeligneLine I (FiniteCoverLocalComparison.restrictedMap f generatorDomain) n
    (openLines f L generatorDomain) (presentations openSource P)
  generator : SymbolSources I (FiniteCoverLocalComparison.restrictedMap f generatorDomain) n
    (openLines f L generatorDomain) (presentations openSource P) openD openTuple
  sectionValue : Γ(D.line,⊤)
  divisor : CartierZero D.line sectionValue
  affineNormalized : ∀ (R : CommRingCat.{0}) (r : Spec R ⟶ generatorDomain.toScheme),
    (D.affine R (r ≫ generatorDomain.ι)).hom.app ⊤
      (localPullbackSection (r ≫ generatorDomain.ι) D.line ⊤ ⊤ (by simp) sectionValue) =
      (tilde.isoTop (R := R) (localPairing (P R (r ≫ generatorDomain.ι)))).hom
        (generator.canonical R r).value

end MathlibExt.AlgebraicGeometry.OpenDeligneSymbolSources
