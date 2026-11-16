/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.FiniteBundleCycleRealization
public import MathlibExt.AlgebraicGeometry.GeneralMotivicBundleThom

/-!
# Fixed Tate classes of finite bundle cycles

Construction 5.1 first gives a literal pointed map from Thom(L) to the
affine finite-cycle model K_n,A. Compose it with the independently fixed
affine-to-Tate map and native reduced-free evaluation. Only then is the
source class on X characterized through the actual general Thom action.
Its existence and independence of the complement/frame remain outputs.

Source: Voevodsky, arXiv:math/0107109v1, Construction 5.1 and Lemma 5.2.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.FiniteBundleThomComparisons

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open FiniteTransferCycleModels FiniteTransferProductModels NisnevichTransferModels
open MotivicStandardSchemes MotivicBundleModels GeneralMotivicBundleFrameMaps
open PointedMotivicModels PointedMotivicQuotients ReducedMotivicCohomologyModels
open EffectiveMotivicComplexModels MotivicRealizationComparisons
open MotivicAffineQuotientModels MotivicAffineTateComparisons
open MotivicTensorOperations MotivicCycleProducts MotivicCohomologyProducts
open GeneralMotivicBundleThom FiniteBundleCycleRealization

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
  {X : SmoothScheme k} {M L : X.scheme.left.Modules} {d e n : ℕ}
  (G : BundleGeometry X M d) (G_L : BundleGeometry X L e)
  (G_S : BundleGeometry X (M ⊞ L) n)
  (φ : (M ⊞ L) ≅ SheafOfModules.free (R := X.scheme.left.ringCatSheaf) (Fin n))
  (C_G : ∀ z : G.RelativeGenerator, CycleGeometry A G G_L G_S φ z)

/-- The Tate class is native realization of the actual finite-cycle cofiber map. -/
def finiteThomClass (A₁ : ModuleCat.{1} ℤ) (z : RelativeCoefficientCycles G A₁)
    (h : ComplementNull (D₀ := D₀) (G₀ := G₀) (R := R)
      A G G_L G_S φ N Q Msec C_G A₁ z) :
    ReducedCohomology B F G_L.thom (2 * (n : ℤ)) (n : ℤ) A₁ :=
  realizationToCohomology B I Q F J G_L.thom (2 * (n : ℤ)) (n : ℤ) A₁
    (realizationMap (D₀ := D₀) (G₀ := G₀) (R := R)
      A G G_L G_S φ N Q Msec C_G A₁ z h ≫ V.map n A₁)

/-- The reindexing is exactly the equality of the source bundle ranks. -/
def finiteThomClassRegraded (hn : n = d + e) (A₁ : ModuleCat.{1} ℤ)
    (z : RelativeCoefficientCycles G A₁)
    (h : ComplementNull (D₀ := D₀) (G₀ := G₀) (R := R)
      A G G_L G_S φ N Q Msec C_G A₁ z) :
    ReducedCohomology B F G_L.thom (2 * (d : ℤ) + 2 * (e : ℤ))
      ((d : ℤ) + (e : ℤ)) A₁ :=
  MotivicCohomologyProducts.regrade (N := N) (B := B) (R₁ := F) G_L.thom A₁
    (show 2 * (n : ℤ) = 2 * (d : ℤ) + 2 * (e : ℤ) from by simp [hn]; ring)
    (show (n : ℤ) = (d : ℤ) + (e : ℤ) from by simp [hn])
    (finiteThomClass (N := N) (B := B) (I := I) (Q := Q) (F := F) (J := J)
      (Msec := Msec) (V := V) (G := G) (G_L := G_L) (G_S := G_S)
      (φ := φ) (C_G := C_G) A₁ z h)

variable {J₀ : TorusConcatenation A}
  {M₀ : SingularCycleProduct (S := S) N T J₀} {Z : EilenbergZilberModel N}
  {V₀ : NegativeTensorComparison N}
  (K : CoefficientMultiplicationSystem N T B M₀ Z V₀)
  (F₀ : KFlatResolutionSystem N) (D : DerivedTensorSource N F₀)
  (H : DerivedTensorShifts N F₀ D) (M₁ : ReducedSmashComultiplication N F)
  (hF : IsFreeTensorComparison N F₀ D F)
  (U₀ : IntegerCoefficientUnits)
  (T₀ : AffineThomCycleSections (D₀ := D₀) (G := G₀) (P := P)
    (A := A) (R := R) (N := N) (Q := Q) (M := Msec))

/-- A source cycle class is characterized by the actual Thom action and already fixed realization. -/
def IsFiniteBundleCycleClass (Δ : BundleThomDiagonals G_L)
    (t : ThomClass N B I Q F J V T₀ G_L) (hn : n = d + e)
    (A₁ : ModuleCat.{1} ℤ) (z : RelativeCoefficientCycles G A₁)
    (h : ComplementNull (D₀ := D₀) (G₀ := G₀) (R := R)
      A G G_L G_S φ N Q Msec C_G A₁ z)
    (u : ReducedCohomology B F (representedPointed X) (2 * (d : ℤ)) (d : ℤ) A₁) : Prop :=
  baseThomAction N B I Q F J V T₀ K F₀ D H M₁ hF U₀ G_L Δ t
      (2 * (d : ℤ)) (d : ℤ) A₁ u =
    finiteThomClassRegraded (N := N) (B := B) (I := I) (Q := Q) (F := F) (J := J)
      (Msec := Msec) (V := V) (G := G) (G_L := G_L) (G_S := G_S)
      (φ := φ) (C_G := C_G) hn A₁ z h

end MathlibExt.AlgebraicGeometry.FiniteBundleThomComparisons
