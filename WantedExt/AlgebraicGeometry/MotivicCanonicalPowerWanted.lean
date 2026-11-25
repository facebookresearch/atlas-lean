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

/-- The permutation bundle diagram of $S_ℓ$: for a field $k$, a prime $ℓ$, the given constant group
geometry of the symmetric group $S_ℓ$ (`Gconst`) and a geometric approximation `G` of its
classifying space, a `PrimeThomDiagram G`: at every stage, the bundle $ξ_ℓ$ associated with the
permutation representation, its diagonal line $\mathcal O → ξ_ℓ$ and the cokernel bundle
$ξ_ℓ/\mathcal O$ with its Thom space, with transition maps between consecutive stages compatible
with the permutation frames, the lines, the cokernels and the zero sections. -/
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

/-- Smashing with a pointed space preserves motivic weak equivalences: over a perfect field $k$, for
the given standard schemes `A` and every pointed motivic space $W$, the functor $X ↦ X ∧ W$ followed
by localization to the motivic homotopy category inverts motivic weak equivalences
(`SmashLocalizationSource A W`). -/
theorem_wanted nativeSmashLocalization [PerfectField k] (W : PointedSpaces (k := k)) :
    SmashLocalizationSource A W

/-- The actual circle orientation has its original ordered edge, not an arbitrary sign. -/
def_wanted nativeCircleOrientation : CircleCycleOrientation (S₀ := S₀) T F

/-- The suspension isomorphisms of mod-$ℓ$ motivic cohomology (Voevodsky, Theorem 2.4): over a
perfect field $k$, for a prime $ℓ$ invertible in $k$, the given motivic interface data and an
orientation `Ls` of the simplicial circle, for every pointed space $X$ and all $p, q ∈ ℤ$, the
external products with the circle class and with the torus class are isomorphisms
$\tilde H^{p,q}(X, \mathbb Z/ℓ) ≅ \tilde H^{p+1,q}(X ∧ S^1_s, \mathbb Z/ℓ)$ and
$\tilde H^{p,q}(X, \mathbb Z/ℓ) ≅ \tilde H^{p+1,q+1}(X ∧ \mathbb G_m, \mathbb Z/ℓ)$
(`SuspensionEquivalences`). -/
def_wanted nativeSuspensionEquivalences [PerfectField k] (ell : ℕ) [Fact ell.Prime]
    (hchar : (ell : k) ≠ 0) (Ls : CircleCycleOrientation (S₀ := S₀) T F) :
    SuspensionEquivalences T F N B Zi K₀ F₀ D S M₁ hF U₀ Ls Lt ell

variable {H : Type} [Group H] [Fintype H]
  [Gconst : ConstantGroupGeometry (k := k) (H := H)]
  (U : FreeQuotient (k := k) (H := H)) {n : ℕ}
  (r : H →* Equiv.Perm (Fin n)) (i : ℕ) (R : Type 1) [CommRing R]

/-- Thom data for powers of affine cycles: over a perfect field $k$, for the given motivic interface
data (whose comparison maps
$\mathbb{Z}_{tr}(\mathbb{A}^m)/\mathbb{Z}_{tr}(\mathbb{A}^m - 0) \otimes M \to K(M(m), 2m)$ are
assumed to be motivic weak equivalences, natural in $M$, multiplicative and normalized in rank one),
a free quotient `U` of a finite group $H$ with affine base, a permutation representation
$r : H → S_n$, $i \in \mathbb{N}$ and a ring $R$, every finite correspondence $z$ with coefficients
in $R$ from a smooth affine $k$-scheme $X$ to the affine space $\mathbb A^i$ of `A` is the input of
a `FinitePowerThomTest` on $X$: a power quotient with its cycle descent and diagonal, the
pulled-back power bundle and its complement, and a Thom class whose Thom action is bijective,
assembled for $z$. -/
def_wanted affinePowerThomAssembly [PerfectField k] [IsAffine U.base.scheme.left]
    (independentCanonicalAffineSource : CanonicalAffineSource N B I Q F J V T₀ K₀ F₀ D S M₁ hF
      Kt Et O Raff Caff Lt Zi)
    (X : SmoothScheme k) [IsAffine X.scheme.left]
    (z : MotivicFinitePowerCycles.CoefficientCycles X (A.affine i) R) :
    {t : FinitePowerThomTest A N B I Q F J Msec V K₀ F₀ D S M₁ hF U₀ T₀ U r i R //
      t.X = X ∧ HEq t.input z}

/-- The canonical $n$-th power on a free quotient (Voevodsky, §5): over a perfect field $k$, for the
given motivic interface data (whose comparison maps
$\mathbb{Z}_{tr}(\mathbb{A}^m)/\mathbb{Z}_{tr}(\mathbb{A}^m - 0) \otimes M \to K(M(m), 2m)$ are
assumed to be motivic weak equivalences, natural in $M$, multiplicative and normalized in rank one),
assuming that the representability map is bijective and that smashing with every pointed space,
followed by localization, inverts motivic weak equivalences, and for $n > 0$, a free quotient `U` of
a finite group $H$, a permutation representation $r : H → S_n$, $i \in \mathbb{N}$, a ring $R$ and
an affine free replacement of `U` (an affine free quotient with an equivariant map to `U` whose map
of bases is a motivic weak equivalence), there is a morphism from the smash product of the affine
model of $K(R(i), 2i)$ with the base of `U` to $K(R(ni), 2ni)$ in the motivic homotopy category that
satisfies the finite power normalization on `U` and on every affine free quotient over `U`. -/
def_wanted finiteCanonicalPower [PerfectField k] (hn : 0 < n)
    (replacement : AffineFreeReplacement A U) :
    {f : PowerRealizationMorphism A N B I Q (representedPointed U.base) i n R //
      IsFinitePowerNormalization A N B I Q F J Msec V Rep K₀ F₀ D S M₁ hF U₀ T₀ U r i R
        hn (hSmash _) (canonical.weak i _) (fun X => hRep X _ _ _) f ∧
      IsAffineCoverPowerNormalization A N B I Q F J Msec V Rep K₀ F₀ D S M₁ hF U₀ T₀ U r i R
        hn hSmash (canonical.weak i _) (fun X => hRep X _ _ _) f}

/-- Affine replacements of the stages of a geometric approximation: over a perfect field $k$, for
the given standard schemes `A`, a finite group $H$ with the given constant group geometry, a
geometric approximation `G` of its classifying space and every $m$, there is an affine free
$H$-quotient with an equivariant map to the $m$-th stage of `G` whose map of bases is a motivic weak
equivalence (`AffineFreeReplacement`). -/
def_wanted regularStageAffineReplacement [PerfectField k]
    (G : GeometricApproximation (k := k) (H := H)) (m : ℕ) :
    AffineFreeReplacement A (G.step m).quotient

/-- The canonical $n$-th power on the geometric classifying space (Voevodsky, Construction 5.3):
over a perfect field $k$, for the given motivic interface data (whose comparison maps
$\mathbb{Z}_{tr}(\mathbb{A}^m)/\mathbb{Z}_{tr}(\mathbb{A}^m - 0) \otimes M \to K(M(m), 2m)$ are
assumed to be motivic weak equivalences, natural in $M$, multiplicative and normalized in rank one),
assuming that the representability map is bijective and that smashing with every pointed space,
followed by localization, inverts motivic weak equivalences, and for $n > 0$, a finite group $H$
with a permutation representation $r : H → S_n$, $i \in \mathbb{N}$, a ring $R$ and a geometric
approximation `G` of $BH$, there is a morphism from the smash product of the affine model of
$K(R(i), 2i)$ with the geometric classifying space of `G` to $K(R(ni), 2ni)$ in the motivic
homotopy category whose restriction to every stage of `G` satisfies the finite power normalization
on that stage and on every affine free quotient over it. -/
def_wanted geometricCanonicalPower [PerfectField k] (hn : 0 < n)
    (G : GeometricApproximation (k := k) (H := H)) :
    {f : PowerRealizationMorphism A N B I Q (geometricClassifyingSpace G) i n R //
      IsGeometricPowerNormalization A N B I Q F J Msec V Rep K₀ F₀ D S M₁ hF U₀ T₀ r i R G
        hn hSmash (canonical.weak i _) (fun X => hRep X _ _ _) f}

variable {ell : ℕ} [Fact ell.Prime]
  [Gprime : ConstantGroupGeometry (k := k) (H := Equiv.Perm (Fin ell))]
  {G : GeometricApproximation (k := k) (H := Equiv.Perm (Fin ell))}
  (Eprime : PrimeThomDiagram G) (point : BasedApproximation P G)

/-- The universal Thom class of the permutation bundle (Voevodsky, §6): over a perfect field $k$,
for a prime $ℓ$ invertible in $k$, the given motivic interface data (whose comparison maps
$\mathbb{Z}_{tr}(\mathbb{A}^m)/\mathbb{Z}_{tr}(\mathbb{A}^m - 0) \otimes M \to K(M(m), 2m)$ are
assumed to be motivic weak equivalences, natural in $M$, multiplicative and normalized in rank one),
and the permutation bundle diagram `Eprime` of a geometric approximation of $BS_ℓ$, there is an
integral class of bidegree $(2(ℓ-1), ℓ-1)$ on the colimit of the Thom spaces of the cokernel bundles
$ξ_ℓ/\mathcal O$ that restricts at every stage to a Thom class of $ξ_ℓ/\mathcal O$
(`GlobalPrimeThomClass`). -/
def_wanted universalPrimeThomClass [PerfectField k]
    (independentCanonicalAffineSource : CanonicalAffineSource N B I Q F J V T₀ K₀ F₀ D S M₁ hF
      Kt Et O Raff Caff Lt Zi) (hchar : (ell : k) ≠ 0) :
    GlobalPrimeThomClass N B I Q F J V T₀ Eprime

variable (t : GlobalPrimeThomClass N B I Q F J V T₀ Eprime)
  (delta : CoefficientConeSource B (integralSequence ell) (primeWeight ell))

/-- The based class $c$ (Voevodsky, Theorem 6.14): over a perfect field $k$, for a prime $ℓ$
invertible in $k$, the given motivic interface data (whose comparison maps
$\mathbb{Z}_{tr}(\mathbb{A}^m)/\mathbb{Z}_{tr}(\mathbb{A}^m - 0) \otimes M \to K(M(m), 2m)$ are
assumed to be motivic weak equivalences, natural in $M$, multiplicative and normalized in rank one),
a base point `point` of the geometric approximation of $BS_ℓ$, a universal Thom class `t` of its
permutation bundle diagram and the given integral Bockstein data `delta`, there is a class
$c ∈ \tilde H^{2ℓ-3, ℓ-1}(BS_ℓ, \mathbb Z/ℓ)$ whose integral Bockstein is the integral Euler class
(the pullback of `t` along the zero section, whose reduction mod $ℓ$ is $d$) and whose pullback to
the base point vanishes (`BasedIntegralLift`). -/
def_wanted basedPrimeBoundaryClass [PerfectField k]
    (independentCanonicalAffineSource : CanonicalAffineSource N B I Q F J V T₀ K₀ F₀ D S M₁ hF
      Kt Et O Raff Caff Lt Zi) (hchar : (ell : k) ≠ 0) :
    BasedIntegralLift N B I Q F J V T₀ Eprime point t delta

/-- Uniqueness of the based class $c$ (Voevodsky, Theorem 6.14): over a perfect field $k$, for a
prime $ℓ$ invertible in $k$, the given motivic interface data (whose comparison maps
$\mathbb{Z}_{tr}(\mathbb{A}^m)/\mathbb{Z}_{tr}(\mathbb{A}^m - 0) \otimes M \to K(M(m), 2m)$ are
assumed to be motivic weak equivalences, natural in $M$, multiplicative and normalized in rank one),
a base point of the geometric approximation of $BS_ℓ$, a universal Thom class `t` of its permutation
bundle diagram and the given integral Bockstein data `delta`, any two classes in
$\tilde H^{2ℓ-3, ℓ-1}(BS_ℓ, \mathbb Z/ℓ)$ whose integral Bockstein is the integral Euler class (the
pullback of `t` along the zero section, whose reduction mod $ℓ$ is $d$) and whose pullback to the
base point vanishes (`BasedIntegralLift`) are equal. -/
theorem_wanted basedPrimeBoundaryUnique [PerfectField k]
    (independentCanonicalAffineSource : CanonicalAffineSource N B I Q F J V T₀ K₀ F₀ D S M₁ hF
      Kt Et O Raff Caff Lt Zi) (hchar : (ell : k) ≠ 0)
    (c c' : BasedIntegralLift N B I Q F J V T₀ Eprime point t delta) : c.value = c'.value

/-- Roots of unity as weight-one classes: over a perfect field $k$, for a prime $ℓ$ invertible in
$k$, the given motivic interface data and integral Bockstein data `deltaOne` in weight one, there is
a bijection between $H^{0,1}(\operatorname{Spec} k, \mathbb Z/ℓ)$ and the group of $ℓ$-th roots of
unity in $k$ under which the integral Bockstein of each class is the class
$[u] ∈ H^{1,1}(\operatorname{Spec} k, \mathbb Z)$ of the corresponding root $u$
(`RootClassSource`). -/
def_wanted nativeRootClass [PerfectField k] (hchar : (ell : k) ≠ 0)
    (deltaOne : CoefficientConeSource B (integralSequence ell) (1 : ℤ)) :
    RootClassSource A N B F Lt Zi ell deltaOne

variable (c : BasedIntegralLift N B I Q F J V T₀ Eprime point t delta)

/-- The completed $c$, $d$ expansion of the cohomology of $X ∧ BS_ℓ$ (Voevodsky, Theorem 6.16): over
a perfect field $k$, for a prime $ℓ$ invertible in $k$, the given motivic interface data (whose
comparison maps
$\mathbb{Z}_{tr}(\mathbb{A}^m)/\mathbb{Z}_{tr}(\mathbb{A}^m - 0) \otimes M \to K(M(m), 2m)$ are
assumed to be motivic weak equivalences, natural in $M$, multiplicative and normalized in rank one),
the based class `c` (for a base point, a universal Thom class `t` of the permutation bundle diagram
and integral Bockstein data `delta`) and the mod-$ℓ$ Euler class $d$ (the reduction mod $ℓ$ of the
pullback of `t` along the zero section), and for every pointed space $X$ and all
$p, q \in \mathbb{Z}$, there is an additive isomorphism from $\tilde H^{p,q}(X ∧ BS_ℓ, \mathbb Z/ℓ)$
to the product, over $i ≥ 0$, of the coefficient groups of $d^i$ and of $c\,d^i$ (the groups
$\tilde H^{*,*}(X, \mathbb Z/ℓ)$ in the complementary bidegrees) that sends the external products
$a × d^i$ and $a × c\,d^i$ to $a$ in the corresponding factor, and every class is the sum of its
series $\sum_i (a_i × d^i + b_i × c\,d^i)$, converging in the topology given by the stages of $BS_ℓ$
(`CompletedBSDecomposition`). -/
def_wanted canonicalCompletedBSExpansion [PerfectField k]
    (independentCanonicalAffineSource : CanonicalAffineSource N B I Q F J V T₀ K₀ F₀ D S M₁ hF
      Kt Et O Raff Caff Lt Zi) (hchar : (ell : k) ≠ 0)
    (X : PointedSpaces (k := k)) (p q : ℤ) :
    CompletedBSDecomposition N B I Q F J V T₀ K₀ F₀ D S M₁ hF Eprime point t delta c X p q

/-- $β(c) = d$ (Voevodsky, §6): over a perfect field $k$, for a prime $ℓ$ invertible in $k$, the
given motivic interface data (whose comparison maps
$\mathbb{Z}_{tr}(\mathbb{A}^m)/\mathbb{Z}_{tr}(\mathbb{A}^m - 0) \otimes M \to K(M(m), 2m)$ are
assumed to be motivic weak equivalences, natural in $M$, multiplicative and normalized in rank one)
and the given mod-$ℓ$ Bockstein data `betaSource`, the Bockstein of the based class `c` (for a base
point of the geometric approximation of $BS_ℓ$, a universal Thom class `t` of its permutation bundle
diagram and integral Bockstein data `delta`) is the mod-$ℓ$ Euler class $d$ (the reduction mod $ℓ$
of the pullback of `t` along the zero section) in $\tilde H^{2ℓ-2, ℓ-1}(BS_ℓ, \mathbb Z/ℓ)$. -/
theorem_wanted beta_prime_c [PerfectField k]
    (independentCanonicalAffineSource : CanonicalAffineSource N B I Q F J V T₀ K₀ F₀ D S M₁ hF
      Kt Et O Raff Caff Lt Zi) (hchar : (ell : k) ≠ 0)
    (betaSource : CoefficientConeSource B (modSequence ell) (primeWeight ell)) :
    regrade N (B := B) (R₁ := F) (geometricClassifyingSpace G) (ModCoefficients ell)
      (show cDegree ell + 1 = dDegree ell from by simp [cDegree]) rfl
      (bockstein B ell F (geometricClassifyingSpace G) (cDegree ell) (primeWeight ell)
        betaSource c.value) = d N B I Q F J V T₀ Eprime t

/-- $c^2 = 0$ for odd $ℓ$ (Voevodsky, §6): over a perfect field $k$, for an odd prime $ℓ$ invertible
in $k$ and the given motivic interface data (whose comparison maps
$\mathbb{Z}_{tr}(\mathbb{A}^m)/\mathbb{Z}_{tr}(\mathbb{A}^m - 0) \otimes M \to K(M(m), 2m)$ are
assumed to be motivic weak equivalences, natural in $M$, multiplicative and normalized in rank one),
the based class `c` (for a base point, a universal Thom class `t` and integral Bockstein data
`delta`: a class in $\tilde H^{2ℓ-3, ℓ-1}(BS_ℓ, \mathbb Z/ℓ)$ whose integral Bockstein is the
pullback of `t` along the zero section and whose pullback to the base point vanishes) satisfies
$c ∪ c = 0$ in the mod-$ℓ$ motivic cohomology of $BS_ℓ$. -/
theorem_wanted odd_prime_c_square [PerfectField k]
    (independentCanonicalAffineSource : CanonicalAffineSource N B I Q F J V T₀ K₀ F₀ D S M₁ hF
      Kt Et O Raff Caff Lt Zi) (hchar : (ell : k) ≠ 0) (hodd : ell ≠ 2) :
    cupRing N B K₀ F₀ D S F M₁ hF (ULift.{1} (ZMod ell)) (geometricClassifyingSpace G)
      (cDegree ell) (primeWeight ell) (cDegree ell) (primeWeight ell) c.value c.value = 0

/-- $c^2 = τd + ρc$ for $ℓ = 2$ (Voevodsky, §6): over a perfect field $k$ in which $2$ is
invertible, for the given motivic interface data (whose comparison maps
$\mathbb{Z}_{tr}(\mathbb{A}^m)/\mathbb{Z}_{tr}(\mathbb{A}^m - 0) \otimes M \to K(M(m), 2m)$ are
assumed to be motivic weak equivalences, natural in $M$, multiplicative and normalized in rank one),
integral Bockstein data `deltaTwo` in weight one and a root-class bijection `rootTwo`, the based
class `c` (for a base point, a universal Thom class `t` and integral Bockstein data `delta`)
satisfies $c ∪ c = τ ∪ d + ρ ∪ c$ in the mod-$2$ motivic cohomology of $BS_2$, where $τ ∈ H^{0,1}$
is the class of the root $-1$ under `rootTwo` and $ρ ∈ H^{1,1}$ the class of the unit $-1$, both
pulled back from $\operatorname{Spec} k$, and $d$ is the mod-$2$ Euler class (the reduction mod $2$
of the pullback of `t` along the zero section). -/
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
