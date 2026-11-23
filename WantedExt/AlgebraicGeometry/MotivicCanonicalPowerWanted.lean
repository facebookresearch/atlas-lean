/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.MotivicPowerCoefficients
public import MathlibExt.AlgebraicGeometry.MotivicPowerSuspensions

/-!
# Source-qualified canonical motivic power and prime-class requests

These are construction and comparison requests on the actual native
finite-cycle sheaf, quotient torsors, permutation/cokernel bundles,
coefficient cones, Thom classes and geometric classifying colimit.
They do not assume P^0, Cartan, Bockstein identities or operation laws
as fields of a provider.

The independent perfect-field affine/Tate source fixes weak equivalence,
coefficient change, multiplicativity and the original rank-one orientation.
Affine source assemblies and actual affine torsor replacements keep the
cycle/Thom normalizations from becoming empty tests on larger bases.

No primitive root is required for the prime class or completed expansion.
Full generation/uniqueness of all bistable operations, HZ endomorphisms,
and a reconstruction of the whole Adem provider are outside this packet.

Source: Voevodsky, arXiv:math/0107109v1, Sections 2, 5, 6, 8 and 9.
The based clause of Theorem 6.14 and the completion of Theorem 6.16
are retained literally in the native model types.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.MotivicCanonicalPowerWanted

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open FiniteTransferCycleModels FiniteTransferProductModels NisnevichTransferModels
open MotivicStandardSchemes EffectiveMotivicComplexModels PointedMotivicModels
open PointedMotivicQuotients ReducedMotivicCohomologyModels MotivicRealizationComparisons
open MotivicAffineQuotientModels MotivicAffineTateComparisons
open MotivicCycleProducts MotivicTensorOperations MotivicCohomologyProducts MotivicPointedProducts
open GeneralMotivicBundleThom MotivicFinitePermutationModels
open MotivicGeometricClassifyingSpaces MotivicPrimeClassGeometry MotivicPrimeClasses
open MotivicBocksteinModels MotivicTorusClassModels MotivicUnitRootClasses
open MotivicCanonicalPowerModels MotivicPowerCoefficients MotivicPowerSuspensions

/-- Construct the regular polynomial free-locus quotients with every original zero-block arrow. -/
def_wanted geometricFiniteGroupApproximation (k H : Type) [Field k] [Group H] [Fintype H]
    [Gconst : ConstantGroupGeometry (k := k) (H := H)] :
    GeometricApproximation (k := k) (H := H)

/-- The actual regular identity vector represents the trivial torsor point. -/
def_wanted geometricTrivialTorsorPoint (k H : Type) [Field k] [Group H] [Fintype H]
    [Gconst : ConstantGroupGeometry (k := k) (H := H)] (P : SmoothProductSystem k)
    (G : GeometricApproximation (k := k) (H := H)) : BasedApproximation P G

/-- Construct the original permutation line and actual cokernel bundle diagram. -/
def_wanted primePermutationQuotientDiagram (k : Type) [Field k] (ell : ℕ) [Fact ell.Prime]
    [Gconst : ConstantGroupGeometry (k := k) (H := Equiv.Perm (Fin ell))]
    (G : GeometricApproximation (k := k) (H := Equiv.Perm (Fin ell))) :
    PrimeThomDiagram G

variable {k : Type} [Field k]
  [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)]
  {D₀ : CompositionSystem k} {G₀ : GraphSystem k}
  [CorrespondenceLaws D₀ G₀] [CorrespondenceAdditivity D₀ G₀]
  {P : SmoothProductSystem k} {E : ExternalSystem P}
  {C : CorrespondenceProductModel D₀ G₀ P E} {A : StandardSchemes P}
  {R₀ : RepresentableSystem D₀ G₀} {S₀ : TransferSheafificationModel D₀ G₀}
  (T : CycleComplexSystem (D := D₀) (G := G₀) (P := P) (E := E)
    (C := C) (A := A) (R := R₀))
  (N : NisTensorSystem k) [N.functor.Additive] [∀ H, (N.functor.obj H).Additive]
  (B : CoefficientComplexSystem (D := D₀) (G := G₀) (P := P) (E := E)
    (C := C) (A := A) (R := R₀) (S := S₀) T N)
  (I : KInjectiveResolutionSystem k) (Q : PointedSimplicialModuleFunctor k)
  (F : ReducedFreeNisSystem k) (J : ReducedFreeAdjunction F Q)
  (Msec : ModuleSectionSystem Q)
  (V : AffineTateMapSystem (N := N) (B := B) (I := I) (Q := Q))
  (T₀ : AffineThomCycleSections (D₀ := D₀) (G := G₀) (P := P)
    (A := A) (R := R₀) (N := N) (Q := Q) (M := Msec))
  {J₀ : TorusConcatenation A}
  {M₀ : SingularCycleProduct (S := S₀) N T J₀} {EZ : EilenbergZilberModel N}
  {V₀ : NegativeTensorComparison N}
  (K₀ : CoefficientMultiplicationSystem N T B M₀ EZ V₀)
  (F₀ : KFlatResolutionSystem N) (D : DerivedTensorSource N F₀)
  (S : DerivedTensorShifts N F₀ D) (M₁ : ReducedSmashComultiplication N F)
  (hF : IsFreeTensorComparison N F₀ D F) (U₀ : IntegerCoefficientUnits)
  (Kt : PointedTateProducts N B I Q F J K₀ F₀ D S M₁ hF)
  (Et : AffineCycleProduct (D := D₀) (G := G₀) (P := P) (A := A) (R := R₀) N Q E Msec)
  (O : MotivicTateThomModels.TorusOpenAffine (P := P) (A := A))
  (Raff : MotivicTateThomModels.RelativeA1CofiberSource O)
  (Caff : MotivicCofiberComparisons.CofiberChainSource F
    (MotivicTateThomModels.relativeTorusMap O))
  (Lt : TorusCycleLinearization (S := S₀) T F)
  (Zi : IntegerCoefficientInclusions (N := N) (T := T) (B := B))
  (canonical : CanonicalAffineSource N B I Q F J V T₀ K₀ F₀ D S M₁ hF
    Kt Et O Raff Caff Lt Zi)
  (Rep : RepresentabilityMap (A := A) B I Q F J)
  (hRep : ∀ (X : PointedSpaces (k := k)) (p q : ℤ) (V₁ : ModuleCat.{1} ℤ),
    Function.Bijective (Rep.map X p q V₁))
  (hSmash : ∀ W : PointedSpaces (k := k), SmashLocalizationSource A W)

/-- The localization descent is a theorem about the actual native smash functor. -/
theorem_wanted nativeSmashLocalization [PerfectField k] (W : PointedSpaces (k := k)) :
    SmashLocalizationSource A W

/-- The actual circle orientation has its original ordered edge, not an arbitrary sign. -/
def_wanted nativeCircleOrientation : CircleCycleOrientation (S₀ := S₀) T F

/-- The suspension source is independent of the power laws and uses the actual sigma_s/sigma_t cups. -/
def_wanted nativeSuspensionEquivalences [PerfectField k] (ell : ℕ) [Fact ell.Prime]
    (hchar : (ell : k) ≠ 0) (Ls : CircleCycleOrientation (S₀ := S₀) T F) :
    SuspensionEquivalences T F N B Zi K₀ F₀ D S M₁ hF U₀ Ls Lt ell

variable {H : Type} [Group H] [Fintype H]
  [Gconst : ConstantGroupGeometry (k := k) (H := H)]
  (U : FreeQuotient (k := k) (H := H)) {n : ℕ}
  (r : H →* Equiv.Perm (Fin n)) (i : ℕ) (R : Type 1) [CommRing R]

/-- Every original affine coefficient cycle admits its full native quotient/diagonal/Thom source assembly. -/
def_wanted affinePowerThomAssembly [PerfectField k] [IsAffine U.base.scheme.left]
    (independentCanonicalAffineSource : CanonicalAffineSource N B I Q F J V T₀ K₀ F₀ D S M₁ hF
      Kt Et O Raff Caff Lt Zi)
    (X : SmoothScheme k) [IsAffine X.scheme.left]
    (z : MotivicFinitePowerCycles.CoefficientCycles X (A.affine i) R) :
    {t : FinitePowerThomTest A N B I Q F J Msec V K₀ F₀ D S M₁ hF U₀ T₀ U r i R //
      t.X = X ∧ HEq t.input z}

/-- A supplied affine replacement permits source descent on larger quotient bases. -/
def_wanted finiteCanonicalPower [PerfectField k] (hn : 0 < n)
    (replacement : AffineFreeReplacement A U) :
    {f : PowerRealizationMorphism A N B I Q (representedPointed U.base) i n R //
      IsFinitePowerNormalization A N B I Q F J Msec V Rep K₀ F₀ D S M₁ hF U₀ T₀ U r i R
        hn (hSmash _) (canonical.weak i _) (fun X => hRep X _ _ _) f ∧
      IsAffineCoverPowerNormalization A N B I Q F J Msec V Rep K₀ F₀ D S M₁ hF U₀ T₀ U r i R
        hn hSmash (canonical.weak i _) (fun X => hRep X _ _ _) f}

/-- Regular geometric free quotients have actual affine equivariant motivic replacements. -/
def_wanted regularStageAffineReplacement [PerfectField k]
    (G : GeometricApproximation (k := k) (H := H)) (m : ℕ) :
    AffineFreeReplacement A (G.step m).quotient

/-- Assemble the original compatible finite powers through the actual geometric quotient colimit. -/
def_wanted geometricCanonicalPower [PerfectField k] (hn : 0 < n)
    (G : GeometricApproximation (k := k) (H := H)) :
    {f : PowerRealizationMorphism A N B I Q (geometricClassifyingSpace G) i n R //
      IsGeometricPowerNormalization A N B I Q F J Msec V Rep K₀ F₀ D S M₁ hF U₀ T₀ r i R G
        hn hSmash (canonical.weak i _) (fun X => hRep X _ _ _) f}

variable {ell : ℕ} [Fact ell.Prime]
  [Gprime : ConstantGroupGeometry (k := k) (H := Equiv.Perm (Fin ell))]
  {G : GeometricApproximation (k := k) (H := Equiv.Perm (Fin ell))}
  (Eprime : PrimeThomDiagram G) (point : BasedApproximation P G)

/-- The integral Thom class is normalized on the actual xi_ell/O diagram, before mod-ell reduction. -/
def_wanted universalPrimeThomClass [PerfectField k]
    (independentCanonicalAffineSource : CanonicalAffineSource N B I Q F J V T₀ K₀ F₀ D S M₁ hF
      Kt Et O Raff Caff Lt Zi) (hchar : (ell : k) ≠ 0) :
    GlobalPrimeThomClass N B I Q F J V T₀ Eprime

variable (t : GlobalPrimeThomClass N B I Q F J V T₀ Eprime)
  (delta : CoefficientConeSource B (integralSequence ell) (primeWeight ell))

/-- Theorem 6.14 constructs c with both its integral boundary and actual trivial-torsor augmentation. -/
def_wanted basedPrimeBoundaryClass [PerfectField k]
    (independentCanonicalAffineSource : CanonicalAffineSource N B I Q F J V T₀ K₀ F₀ D S M₁ hF
      Kt Et O Raff Caff Lt Zi) (hchar : (ell : k) ≠ 0) :
    BasedIntegralLift N B I Q F J V T₀ Eprime point t delta

/-- The normalized lift, including the based clause, is unique. -/
theorem_wanted basedPrimeBoundaryUnique [PerfectField k]
    (independentCanonicalAffineSource : CanonicalAffineSource N B I Q F J V T₀ K₀ F₀ D S M₁ hF
      Kt Et O Raff Caff Lt Zi) (hchar : (ell : k) ≠ 0)
    (c c' : BasedIntegralLift N B I Q F J V T₀ Eprime point t delta) : c.value = c'.value

/-- Root classes use the actual units and native integral boundary, without a primitive-root input. -/
def_wanted nativeRootClass [PerfectField k] (hchar : (ell : k) ≠ 0)
    (deltaOne : CoefficientConeSource B (integralSequence ell) (1 : ℤ)) :
    RootClassSource A N B F Lt Zi ell deltaOne

variable (c : BasedIntegralLift N B I Q F J V T₀ Eprime point t delta)

/-- Theorem 6.16 is a formal completed c/d expansion on every actual pointed source and integer bidegree. -/
def_wanted canonicalCompletedBSExpansion [PerfectField k]
    (independentCanonicalAffineSource : CanonicalAffineSource N B I Q F J V T₀ K₀ F₀ D S M₁ hF
      Kt Et O Raff Caff Lt Zi) (hchar : (ell : k) ≠ 0)
    (X : PointedSpaces (k := k)) (p q : ℤ) :
    CompletedBSDecomposition N B I Q F J V T₀ K₀ F₀ D S M₁ hF Eprime point t delta c X p q

/-- The native mod-ell boundary of the based c is the already reduced integral Euler class. -/
theorem_wanted beta_prime_c [PerfectField k]
    (independentCanonicalAffineSource : CanonicalAffineSource N B I Q F J V T₀ K₀ F₀ D S M₁ hF
      Kt Et O Raff Caff Lt Zi) (hchar : (ell : k) ≠ 0)
    (betaSource : CoefficientConeSource B (modSequence ell) (primeWeight ell)) :
    regrade N (B := B) (R₁ := F) (geometricClassifyingSpace G) (ModCoefficients ell)
      (show cDegree ell + 1 = dDegree ell from by simp [cDegree]) rfl
      (bockstein B ell F (geometricClassifyingSpace G) (cDegree ell) (primeWeight ell)
        betaSource c.value) = d N B I Q F J V T₀ Eprime t

/-- The odd-prime completed basis has square-zero c. -/
theorem_wanted odd_prime_c_square [PerfectField k]
    (independentCanonicalAffineSource : CanonicalAffineSource N B I Q F J V T₀ K₀ F₀ D S M₁ hF
      Kt Et O Raff Caff Lt Zi) (hchar : (ell : k) ≠ 0) (hodd : ell ≠ 2) :
    cupRing N B K₀ F₀ D S F M₁ hF (ULift.{1} (ZMod ell)) (geometricClassifyingSpace G)
      (cDegree ell) (primeWeight ell) (cDegree ell) (primeWeight ell) c.value c.value = 0

/-- The ell=2 basis retains the actual mu_2 tau and minus-one rho classes. -/
theorem_wanted two_prime_c_square [PerfectField k]
    (independentCanonicalAffineSource : CanonicalAffineSource N B I Q F J V T₀ K₀ F₀ D S M₁ hF
      Kt Et O Raff Caff Lt Zi) (hchar : (ell : k) ≠ 0) (hell : ell = 2)
    (deltaTwo : CoefficientConeSource B (integralSequence 2) (1 : ℤ))
    (rootTwo : RootClassSource A N B F Lt Zi 2 deltaTwo) :
    let tauK := ReducedMotivicCohomologyModels.coefficientMap B F (representedPointed P.unit) 0 1
      (eqToHom (congrArg ModCoefficients hell.symm)) (tau A N B F Lt Zi deltaTwo rootTwo)
    let tauG := ReducedMotivicCohomologyModels.pullback B F (geometricProjection P G)
      0 1 (ModCoefficients ell) tauK
    let rhoG := ReducedMotivicCohomologyModels.pullback B F (geometricProjection P G)
      1 1 (ModCoefficients ell) (rho A N B F Lt Zi ell)
    cupRing N B K₀ F₀ D S F M₁ hF (ULift.{1} (ZMod ell)) (geometricClassifyingSpace G)
      (cDegree ell) (primeWeight ell) (cDegree ell) (primeWeight ell) c.value c.value =
      regrade N (B := B) (R₁ := F) (geometricClassifyingSpace G) (ModCoefficients ell)
        (by subst ell; norm_num [cDegree, dDegree, primeWeight])
        (by subst ell; norm_num [primeWeight])
        (cupRing N B K₀ F₀ D S F M₁ hF (ULift.{1} (ZMod ell)) (geometricClassifyingSpace G)
          0 1 (dDegree ell) (primeWeight ell) tauG (d N B I Q F J V T₀ Eprime t)) +
      regrade N (B := B) (R₁ := F) (geometricClassifyingSpace G) (ModCoefficients ell)
        (by subst ell; norm_num [cDegree, dDegree, primeWeight])
        (by subst ell; norm_num [primeWeight])
        (cupRing N B K₀ F₀ D S F M₁ hF (ULift.{1} (ZMod ell)) (geometricClassifyingSpace G)
          1 1 (cDegree ell) (primeWeight ell) rhoG c.value)

end WantedExt.AlgebraicGeometry.MotivicCanonicalPowerWanted
