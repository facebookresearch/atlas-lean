/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.FiniteBundleThomComparisons

/-!
# Source constructions for general bundle Thom and finite-cycle maps

The coefficient unit and diagonal maps are fixed on all original pure
tensors and simplices. A class and a Thom isomorphism are requested only
with the independent source properties of the canonical affine-to-Tate
comparison. The actual comparison already has its own source constructor;
it is not requested again here. The class constructor also supplies the
finite-type spread of the generic-point normalization on actual opens.

Source: Voevodsky, arXiv:math/0107109v1, Proposition 4.3, Corollary 4.4,
Construction 5.1 and Lemma 5.2. Thom bijectivity and complement/frame
independence are outputs, never inputs to the finite-cycle construction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.GeneralMotivicBundleThom

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open FiniteTransferCycleModels FiniteTransferProductModels NisnevichTransferModels
open MotivicStandardSchemes MotivicBundleModels GeneralMotivicBundleFrameMaps
open PointedMotivicModels PointedMotivicQuotients ReducedMotivicCohomologyModels
open EffectiveMotivicComplexModels MotivicRealizationComparisons
open MotivicAffineQuotientModels MotivicAffineTateComparisons
open MotivicTensorOperations MotivicCycleProducts MotivicCohomologyProducts
open MotivicPointedProducts MotivicTateThomModels MotivicTorusClassModels
open MotivicCofiberComparisons GeneralMotivicBundleThom
open FiniteBundleCycleRealization FiniteBundleThomComparisons

/-- Transport the native integer tensor unit to the fixed lifted coefficient module. -/
public def_wanted native_integer_coefficient_units : IntegerCoefficientUnits

/-- The computed frame map has its actual restriction to the nonzero complement. -/
public def_wanted native_frame_complement (k : Type) [Field k]
    [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)]
    (P : SmoothProductSystem k) (A : StandardSchemes P)
    (X : SmoothScheme k) (M : X.scheme.left.Modules) (d : ℕ)
    (G : BundleGeometry X M d)
    (φ : M ≅ SheafOfModules.free (R := X.scheme.left.ringCatSheaf) (Fin d)) :
    FrameComplementMap A G φ

/-- The original section map on a pulled-back bundle preserves the nonzero complement. -/
public def_wanted native_pullback_complement (k : Type) [Field k]
    [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)]
    (X Y : SmoothScheme k) (f : X ⟶ Y) (M : Y.scheme.left.Modules) (d : ℕ)
    (G : BundleGeometry Y M d)
    (H : BundleGeometry X ((Scheme.Modules.pullback f.left).obj M) d) :
    ComplementMap H G f (𝟙 _)

/-- A locally free cokernel makes the original monomorphism fibrewise injective. -/
public def_wanted native_subbundle_complement (k : Type) [Field k]
    [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)]
    (X : SmoothScheme k) (M N : X.scheme.left.Modules) (d e q : ℕ)
    (G : BundleGeometry X M d) (H : BundleGeometry X N e)
    (a : M ⟶ (Scheme.Modules.pullback (𝟙 X.scheme.left)).obj N) [Mono a]
    (hQ : AlgebraicBundleGeometry.IsBundle (cokernel a) q) :
    ComplementMap G H (𝟙 X) a

/-- Construct the native bundle-base and parameterized diagonals on all original simplices. -/
public def_wanted native_bundle_thom_diagonals (k : Type) [Field k]
    [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)]
    (X : SmoothScheme k) (M : X.scheme.left.Modules) (d : ℕ)
    (G : BundleGeometry X M d) : BundleThomDiagonals G

/-- Construct the actual finite generic-image cycle of the original support and whole frame. -/
public def_wanted native_finite_bundle_cycle_geometry (k : Type) [Field k]
    [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)]
    (P : SmoothProductSystem k) (A : StandardSchemes P)
    (X : SmoothScheme k) (M L : X.scheme.left.Modules) (d e n : ℕ)
    (G : BundleGeometry X M d) (G_L : BundleGeometry X L e)
    (G_S : BundleGeometry X (M ⊞ L) n)
    (φ : (M ⊞ L) ≅ SheafOfModules.free (R := X.scheme.left.ringCatSheaf) (Fin n))
    (z : G.RelativeGenerator) : CycleGeometry A G G_L G_S φ z

variable {k : Type} [Field k]
  [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)]
  {D₀ : CompositionSystem k} {G₀ : GraphSystem k}
  [CorrespondenceLaws D₀ G₀] [CorrespondenceAdditivity D₀ G₀]
  {P : SmoothProductSystem k} {E : ExternalSystem P}
  {C : CorrespondenceProductModel D₀ G₀ P E} {A : StandardSchemes P}
  {R : RepresentableSystem D₀ G₀} {S : TransferSheafificationModel D₀ G₀}
  {T : CycleComplexSystem (D := D₀) (G := G₀) (P := P) (E := E)
    (C := C) (A := A) (R := R)}
  (N : NisTensorSystem k) [N.functor.Additive] [∀ H, (N.functor.obj H).Additive]
  (B : CoefficientComplexSystem (D := D₀) (G := G₀) (P := P) (E := E)
    (C := C) (A := A) (R := R) (S := S) T N)
  (I : KInjectiveResolutionSystem k) (Q : PointedSimplicialModuleFunctor k)
  (F : ReducedFreeNisSystem k) (J : ReducedFreeAdjunction F Q)
  (Msec : ModuleSectionSystem Q)
  (V : AffineTateMapSystem (N := N) (B := B) (I := I) (Q := Q))
  (T₀ : AffineThomCycleSections (D₀ := D₀) (G := G₀) (P := P)
    (A := A) (R := R) (N := N) (Q := Q) (M := Msec))
  {J₀ : TorusConcatenation A}
  {M₀ : SingularCycleProduct (S := S) N T J₀} {Z : EilenbergZilberModel N}
  {V₀ : NegativeTensorComparison N}
  (K : CoefficientMultiplicationSystem N T B M₀ Z V₀)
  (F₀ : KFlatResolutionSystem N) (D : DerivedTensorSource N F₀)
  (H : DerivedTensorShifts N F₀ D) (M₁ : ReducedSmashComultiplication N F)
  (hF : IsFreeTensorComparison N F₀ D F)
  (K₀ : PointedTateProducts N B I Q F J K F₀ D H M₁ hF)
  (E₀ : AffineCycleProduct (D := D₀) (G := G₀) (P := P) (A := A) (R := R)
    N Q E Msec)
  (O : TorusOpenAffine (P := P) (A := A)) (R₀ : RelativeA1CofiberSource O)
  (C₀ : CofiberChainSource F (relativeTorusMap O))
  (L₀ : TorusCycleLinearization (S := S) T F)
  (Z₀ : IntegerCoefficientInclusions (T := T) (N := N) (B := B))

local notation "AffineSource" => CanonicalAffineSource
  (N := N) (B := B) (I := I) (Q := Q) (F := F) (J := J) (V := V) (T₀ := T₀)
  (L := K) (F₀ := F₀) (D := D) (H := H) (M₁ := M₁) (hF := hF)
  K₀ E₀ O R₀ C₀ L₀ Z₀

/-- Construct the generic-open normalized class from the actual canonical affine source. -/
public def_wanted native_bundle_thom_class [PerfectField k]
    (hSource : AffineSource) (X : SmoothScheme k) (M : X.scheme.left.Modules) (d : ℕ)
    (G : BundleGeometry X M d) : ThomClass N B I Q F J V T₀ G

/-- The actual generic-open normalization uniquely fixes the Thom class. -/
public theorem_wanted native_bundle_thom_class_unique [PerfectField k]
    (hSource : AffineSource) (X : SmoothScheme k) (M : X.scheme.left.Modules) (d : ℕ)
    (G : BundleGeometry X M d) (a b : ThomClass N B I Q F J V T₀ G) : a.value = b.value

/-- Pullback uses the original whole total-space map and its nonzero complement square. -/
public theorem_wanted native_bundle_thom_class_pullback [PerfectField k]
    (hSource : AffineSource) (X Y : SmoothScheme k) (f : X ⟶ Y)
    (M : Y.scheme.left.Modules) (d : ℕ) (G : BundleGeometry Y M d)
    (G' : BundleGeometry X ((Scheme.Modules.pullback f.left).obj M) d)
    (Cj : ComplementMap G' G f (𝟙 _))
    (t : ThomClass N B I Q F J V T₀ G) (t' : ThomClass N B I Q F J V T₀ G') :
    ReducedMotivicCohomologyModels.pullback B F (thomMap G' G f (𝟙 _) Cj)
      (2 * (d : ℤ)) (d : ℤ) integerCoefficients t.value = t'.value

/-- The Euler comparison is the actual zero-section pullback on both sides. -/
public theorem_wanted native_bundle_euler_pullback [PerfectField k]
    (hSource : AffineSource) (X Y : SmoothScheme k) (f : X ⟶ Y)
    (M : Y.scheme.left.Modules) (d : ℕ) (G : BundleGeometry Y M d)
    (G' : BundleGeometry X ((Scheme.Modules.pullback f.left).obj M) d)
    (t : ThomClass N B I Q F J V T₀ G) (t' : ThomClass N B I Q F J V T₀ G') :
    ReducedMotivicCohomologyModels.pullback B F (representedMap f)
      (2 * (d : ℤ)) (d : ℤ) integerCoefficients (euler N B I Q F J V T₀ G t) =
    euler N B I Q F J V T₀ G' t'

/-- Lemma 4.6 uses native direct-sum bundles and the original coefficient cup product. -/
public theorem_wanted native_bundle_euler_sum [PerfectField k]
    (hSource : AffineSource) (X : SmoothScheme k) (M N₁ : X.scheme.left.Modules)
    (d e : ℕ) (G : BundleGeometry X M d) (G' : BundleGeometry X N₁ e)
    (G_S : BundleGeometry X (M ⊞ N₁) (d + e))
    (t : ThomClass N B I Q F J V T₀ G) (t' : ThomClass N B I Q F J V T₀ G')
    (t_S : ThomClass N B I Q F J V T₀ G_S) (U₀ : IntegerCoefficientUnits) :
    euler N B I Q F J V T₀ G_S t_S =
    MotivicCohomologyProducts.regrade (N := N) (B := B) (R₁ := F)
      (representedPointed X) integerCoefficients
      (show 2 * (d : ℤ) + 2 * (e : ℤ) = 2 * ((d + e : ℕ) : ℤ) from by simp; ring)
      (show (d : ℤ) + (e : ℤ) = ((d + e : ℕ) : ℤ) from by simp)
      (MotivicCohomologyProducts.cup N B K F₀ D H F M₁ hF
        (representedPointed X) (2 * (d : ℤ)) (d : ℤ) (2 * (e : ℤ)) (e : ℤ)
        integerCoefficients integerCoefficients integerCoefficients
        (U₀.map integerCoefficients) (euler N B I Q F J V T₀ G t)
        (euler N B I Q F J V T₀ G' t'))

/-- The source's general pointed Thom action is bijective in every bidegree and coefficient. -/
public theorem_wanted native_general_thom_isomorphism [PerfectField k]
    (hSource : AffineSource) (X : SmoothScheme k) (M : X.scheme.left.Modules) (d : ℕ)
    (G : BundleGeometry X M d) (Δ : BundleThomDiagonals G)
    (t : ThomClass N B I Q F J V T₀ G) (U₀ : IntegerCoefficientUnits)
    (W : PointedSpaces (k := k)) (p q : ℤ) (A₁ : ModuleCat.{1} ℤ) :
    Function.Bijective (thomAction N B I Q F J V T₀ K F₀ D H M₁ hF U₀
      G Δ t W p q A₁)

/-- The original bundle-base Thom action is bijective, with no assumed inverse in its recipe. -/
public theorem_wanted native_base_thom_isomorphism [PerfectField k]
    (hSource : AffineSource) (X : SmoothScheme k) (M : X.scheme.left.Modules) (d : ℕ)
    (G : BundleGeometry X M d) (Δ : BundleThomDiagonals G)
    (t : ThomClass N B I Q F J V T₀ G) (U₀ : IntegerCoefficientUnits)
    (p q : ℤ) (A₁ : ModuleCat.{1} ℤ) :
    Function.Bijective (baseThomAction N B I Q F J V T₀ K F₀ D H M₁ hF U₀
      G Δ t p q A₁)

/-- The actual finite-cycle coefficient section vanishes on the original nonzero complement. -/
public theorem_wanted native_finite_bundle_complement_null
    (X : SmoothScheme k) (M L : X.scheme.left.Modules) (d e n : ℕ)
    (G : BundleGeometry X M d) (G_L : BundleGeometry X L e)
    (G_S : BundleGeometry X (M ⊞ L) n)
    (φ : (M ⊞ L) ≅ SheafOfModules.free (R := X.scheme.left.ringCatSheaf) (Fin n))
    (C_G : ∀ z : G.RelativeGenerator, CycleGeometry A G G_L G_S φ z)
    (A₁ : ModuleCat.{1} ℤ) (z : RelativeCoefficientCycles G A₁) :
    ComplementNull (D₀ := D₀) (G₀ := G₀) (R := R)
      A G G_L G_S φ N Q Msec C_G A₁ z

/-- The source cycle class is constructed after its actual cofiber realization and Thom action. -/
public def_wanted native_finite_bundle_cycle_class [PerfectField k]
    (hSource : AffineSource)
    (X : SmoothScheme k) (M L : X.scheme.left.Modules) (d e n : ℕ)
    (G : BundleGeometry X M d) (G_L : BundleGeometry X L e)
    (G_S : BundleGeometry X (M ⊞ L) n)
    (φ : (M ⊞ L) ≅ SheafOfModules.free (R := X.scheme.left.ringCatSheaf) (Fin n))
    (C_G : ∀ z : G.RelativeGenerator, CycleGeometry A G G_L G_S φ z)
    (Δ : BundleThomDiagonals G_L) (t : ThomClass N B I Q F J V T₀ G_L)
    (U₀ : IntegerCoefficientUnits) (hn : n = d + e)
    (A₁ : ModuleCat.{1} ℤ) (z : RelativeCoefficientCycles G A₁)
    (h : ComplementNull (D₀ := D₀) (G₀ := G₀) (R := R)
      A G G_L G_S φ N Q Msec C_G A₁ z) :
    {u : ReducedCohomology B F (representedPointed X) (2 * (d : ℤ)) (d : ℤ) A₁ //
      IsFiniteBundleCycleClass N B I Q F J Msec V G G_L G_S φ C_G
        K F₀ D H M₁ hF U₀ T₀ Δ t hn A₁ z h u}

/-- Lemma5.2 compares the classes extracted from two actual complement bundles and frames. -/
public theorem_wanted native_finite_bundle_cycle_class_independent [PerfectField k]
    (hSource : AffineSource) (X : SmoothScheme k) (M L L' : X.scheme.left.Modules)
    (d e e' n n' : ℕ) (G : BundleGeometry X M d)
    (G_L : BundleGeometry X L e) (G_L' : BundleGeometry X L' e')
    (G_S : BundleGeometry X (M ⊞ L) n) (G_S' : BundleGeometry X (M ⊞ L') n')
    (φ : (M ⊞ L) ≅ SheafOfModules.free (R := X.scheme.left.ringCatSheaf) (Fin n))
    (φ' : (M ⊞ L') ≅ SheafOfModules.free (R := X.scheme.left.ringCatSheaf) (Fin n'))
    (C_G : ∀ z : G.RelativeGenerator, CycleGeometry A G G_L G_S φ z)
    (C_G' : ∀ z : G.RelativeGenerator, CycleGeometry A G G_L' G_S' φ' z)
    (Δ : BundleThomDiagonals G_L) (Δ' : BundleThomDiagonals G_L')
    (t : ThomClass N B I Q F J V T₀ G_L) (t' : ThomClass N B I Q F J V T₀ G_L')
    (U₀ : IntegerCoefficientUnits) (hn : n = d + e) (hn' : n' = d + e')
    (A₁ : ModuleCat.{1} ℤ) (z : RelativeCoefficientCycles G A₁)
    (h : ComplementNull (D₀ := D₀) (G₀ := G₀) (R := R)
      A G G_L G_S φ N Q Msec C_G A₁ z)
    (h' : ComplementNull (D₀ := D₀) (G₀ := G₀) (R := R)
      A G G_L' G_S' φ' N Q Msec C_G' A₁ z)
    (u v : ReducedCohomology B F (representedPointed X) (2 * (d : ℤ)) (d : ℤ) A₁)
    (hu : IsFiniteBundleCycleClass N B I Q F J Msec V G G_L G_S φ C_G
      K F₀ D H M₁ hF U₀ T₀ Δ t hn A₁ z h u)
    (hv : IsFiniteBundleCycleClass N B I Q F J Msec V G G_L' G_S' φ' C_G'
      K F₀ D H M₁ hF U₀ T₀ Δ' t' hn' A₁ z h' v) : u = v

end WantedExt.AlgebraicGeometry.GeneralMotivicBundleThom
