/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.MotivicPowerDescentModels
public import MathlibExt.AlgebraicGeometry.FiniteBundleThomComparisons

/-!
# The computed Thom class of the original finite power cycle

Complement choices retain the actual sum module and its original free
frame. The finite relative power cycle is the result of external power,
free quotient descent and the original diagonal. Construction 5.1 is
applied to that same cycle, with its actual support and coefficients.

Its class on X times U/G is the preimage under the already computed
native Thom action. The input bijectivity is an independently requested
shared Thom theorem, rather than a claimed power-map identity. The
normalization equation is proved for this actual inverse construction.
No existence of a global free complement on arbitrary bases is asserted.

Source: Voevodsky, arXiv:math/0107109v1, Constructions 5.1/5.3,
Equation 5.2 and Lemma 5.4. Later power sheaf/coefficient operations
use the source-normalized affine/Tate comparison independently.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.MotivicPowerThomModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open FiniteTransferCycleModels FiniteTransferProductModels NisnevichTransferModels
open MotivicStandardSchemes EffectiveMotivicComplexModels
open MotivicFinitePermutationModels MotivicPermutationBundleModels
open MotivicFinitePowerCycles MotivicPowerQuotientModels MotivicPowerDescentModels
open MotivicBundleModels PointedMotivicModels PointedMotivicQuotients
open ReducedMotivicCohomologyModels MotivicRealizationComparisons
open MotivicAffineQuotientModels MotivicAffineTateComparisons
open MotivicTensorOperations MotivicCycleProducts MotivicCohomologyProducts
open GeneralMotivicBundleThom FiniteBundleCycleRealization FiniteBundleThomComparisons

variable {k : Type} [Field k]
  [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)]
  {D₀ : CompositionSystem k} {G₀ : GraphSystem k}
  [CorrespondenceLaws D₀ G₀] [CorrespondenceAdditivity D₀ G₀]
  {P : SmoothProductSystem k} {E : ExternalSystem P}
  {C : CorrespondenceProductModel D₀ G₀ P E} {A : StandardSchemes P}
  {R₀ : RepresentableSystem D₀ G₀} {S₀ : TransferSheafificationModel D₀ G₀}
  {T : CycleComplexSystem (D := D₀) (G := G₀) (P := P) (E := E)
    (C := C) (A := A) (R := R₀)}
  (N : NisTensorSystem k) [N.functor.Additive] [∀ H, (N.functor.obj H).Additive]
  (B : CoefficientComplexSystem (D := D₀) (G := G₀) (P := P) (E := E)
    (C := C) (A := A) (R := R₀) (S := S₀) T N)
  (I : KInjectiveResolutionSystem k) (Q : PointedSimplicialModuleFunctor k)
  (F : ReducedFreeNisSystem k) (J : ReducedFreeAdjunction F Q)
  (Msec : ModuleSectionSystem Q)
  (V₀ : AffineTateMapSystem (N := N) (B := B) (I := I) (Q := Q))

/-- Every original ring-coefficient finite cycle is the sum of its native affine quotient classes. -/
def affineCoefficientCycleClass (i : ℕ) (R : Type 1) [CommRing R]
    (X : SmoothScheme k) (z : CoefficientCycles X (A.affine i) R) :
    (affineCoefficient (D := D₀) (G := G₀) (P := P) (A := A)
      (R := R₀) N i (ModuleCat.of ℤ R)).obj.obj (op X) :=
  z.sum fun g c => affineCoefficientClass (D := D₀) (G := G₀) (P := P) (A := A)
    (R := R₀) N i (ModuleCat.of ℤ R) X (generatorCycle g) c

/-- The source pointed map uses that same actual coefficient section. -/
def affineCoefficientCycleMap (i : ℕ) (R : Type 1) [CommRing R]
    (X : SmoothScheme k) (z : CoefficientCycles X (A.affine i) R) :
    representedPointed X ⟶ affineK (D := D₀) (G := G₀) (P := P) (A := A)
      (R := R₀) N Q i (ModuleCat.of ℤ R) :=
  Msec.sectionMap _ X (affineCoefficientCycleClass N i R X z)

/-- The input cohomology class is fixed before any power is chosen. -/
def affineInputClass (i : ℕ) (R : Type 1) [CommRing R]
    (X : SmoothScheme k) (z : CoefficientCycles X (A.affine i) R) :
    ReducedCohomology B F (representedPointed X) (2 * (i : ℤ)) (i : ℤ) (ModuleCat.of ℤ R) :=
  realizationToCohomology B I Q F J (representedPointed X)
    (2 * (i : ℤ)) (i : ℤ) (ModuleCat.of ℤ R)
      (affineCoefficientCycleMap N Q Msec i R X z ≫ V₀.map i (ModuleCat.of ℤ R))

/-- Native product-to-smash is fixed by the original two scheme projections. -/
def productPointedMap (X Y : SmoothScheme k) :
    representedPointed (P.obj X Y) ⟶ smash (representedPointed X) (representedPointed Y) :=
  smashDiagonal (representedPointed (P.obj X Y)) ≫
    smashMap (representedMap (P.geometry X Y).fst) (representedMap (P.geometry X Y).snd)

variable {H : Type} [Group H] [Fintype H]
  [Gconst : ConstantGroupGeometry (k := k) (H := H)]
  (U : FreeQuotient (k := k) (H := H)) {n : ℕ}
  (r : H →* Equiv.Perm (Fin n)) {X : SmoothScheme k} (i : ℕ)
  (V : VectorQuotient P U r A i)
  (W : PullbackPowerBundle P U r A i V (X := X))

/-- A chosen actual complement is an input, including its whole sum-module frame. -/
structure PowerComplement (W : PullbackPowerBundle P U r A i V (X := X)) where
  rank : ℕ
  module : (P.obj X U.base).scheme.left.Modules
  bundle : BundleGeometry (P.obj X U.base) module rank
  sum : BundleGeometry (P.obj X U.base)
    (((Scheme.Modules.pullback (P.geometry X U.base).snd.left).obj V.module.module) ⊞ module)
      (n * i + rank)
  frame : (((Scheme.Modules.pullback (P.geometry X U.base).snd.left).obj V.module.module) ⊞ module) ≅
    SheafOfModules.free (R := (P.obj X U.base).scheme.left.ringCatSheaf) (Fin (n * i + rank))

variable (L : PowerComplement (P := P) U r i V W)
  (C_G : ∀ z : W.bundle.RelativeGenerator,
    CycleGeometry A W.bundle L.bundle L.sum L.frame z)
  (R : Type 1) [CommRing R]
  (z : RelativePowerCycles P U r R A i V W)
  (hz : ComplementNull (D₀ := D₀) (G₀ := G₀) (R := R₀)
    A W.bundle L.bundle L.sum L.frame N Q Msec C_G (ModuleCat.of ℤ R) z)

/-- Construction 5.1 realizes the same original relative power cycle. -/
def powerThomClass : ReducedCohomology B F L.bundle.thom
    (2 * ((n * i + L.rank : ℕ) : ℤ)) ((n * i + L.rank : ℕ) : ℤ) (ModuleCat.of ℤ R) :=
  finiteThomClass (N := N) (B := B) (I := I) (Q := Q) (F := F) (J := J)
    (Msec := Msec) (V := V₀) (G := W.bundle) (G_L := L.bundle) (G_S := L.sum)
    (φ := L.frame) (C_G := C_G) (ModuleCat.of ℤ R) z hz

variable {J₀ : TorusConcatenation A}
  {M₀ : SingularCycleProduct (S := S₀) N T J₀} {Z₀ : EilenbergZilberModel N}
  {V₁ : NegativeTensorComparison N}
  (K : CoefficientMultiplicationSystem N T B M₀ Z₀ V₁)
  (F₀ : KFlatResolutionSystem N) (D : DerivedTensorSource N F₀)
  (S : DerivedTensorShifts N F₀ D) (M₁ : ReducedSmashComultiplication N F)
  (hF : IsFreeTensorComparison N F₀ D F)
  (U₀ : IntegerCoefficientUnits)
  (T₀ : AffineThomCycleSections (D₀ := D₀) (G := G₀) (P := P)
    (A := A) (R := R₀) (N := N) (Q := Q) (M := Msec))
  (Δ : BundleThomDiagonals L.bundle) (t : ThomClass N B I Q F J V₀ T₀ L.bundle)

/-- The preimage is taken under the actual source-normalized native Thom action. -/
def powerBundleClass
    (bijective : Function.Bijective (baseThomAction N B I Q F J V₀ T₀ K F₀ D S M₁ hF U₀
      L.bundle Δ t (2 * ((n * i : ℕ) : ℤ)) ((n * i : ℕ) : ℤ) (ModuleCat.of ℤ R))) :
    ReducedCohomology B F (representedPointed (P.obj X U.base))
      (2 * ((n * i : ℕ) : ℤ)) ((n * i : ℕ) : ℤ) (ModuleCat.of ℤ R) :=
  Classical.choose (bijective.surjective
    (finiteThomClassRegraded (N := N) (B := B) (I := I) (Q := Q) (F := F) (J := J)
      (Msec := Msec) (V := V₀) (G := W.bundle) (G_L := L.bundle) (G_S := L.sum)
      (φ := L.frame) (C_G := C_G) rfl (ModuleCat.of ℤ R) z hz))

/-- Equation 5.2 is proved for this computed inverse and the original finite cycle class. -/
theorem powerBundleClass_normalized
    (bijective : Function.Bijective (baseThomAction N B I Q F J V₀ T₀ K F₀ D S M₁ hF U₀
      L.bundle Δ t (2 * ((n * i : ℕ) : ℤ)) ((n * i : ℕ) : ℤ) (ModuleCat.of ℤ R))) :
    IsFiniteBundleCycleClass (N := N) (B := B) (I := I) (Q := Q) (F := F) (J := J)
      (Msec := Msec) (V := V₀) (G := W.bundle) (G_L := L.bundle) (G_S := L.sum)
      (φ := L.frame) (C_G := C_G) K F₀ D S M₁ hF U₀ T₀ Δ t rfl (ModuleCat.of ℤ R) z hz
      (powerBundleClass N B I Q F J Msec V₀ U r i V W L C_G R z hz
        K F₀ D S M₁ hF U₀ T₀ Δ t bijective) :=
  Classical.choose_spec (bijective.surjective
    (finiteThomClassRegraded (N := N) (B := B) (I := I) (Q := Q) (F := F) (J := J)
      (Msec := Msec) (V := V₀) (G := W.bundle) (G_L := L.bundle) (G_S := L.sum)
      (φ := L.frame) (C_G := C_G) rfl (ModuleCat.of ℤ R) z hz))

end MathlibExt.AlgebraicGeometry.MotivicPowerThomModels
