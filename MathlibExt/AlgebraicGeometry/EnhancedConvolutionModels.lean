/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.BorderedGraphKernelModels
public import MathlibExt.AlgebraicGeometry.BorderedRealTimeModels
public import MathlibExt.AlgebraicGeometry.BoundedIndOperationSources
public import MathlibExt.AlgebraicGeometry.EnhancedNullClosureModels
public import MathlibExt.CategoryTheory.NativeParametrizedAdjoints

/-!
# Actual enhanced real convolution, internal Hom and evaluation

The prequotient convolution is the original real formula
Rmu_!!(q1-inverse(K1) tensor q2-inverse(K2)). The sum is the computed
finite-real bordered sum, and its image uses its actual graph kernel.
The complete native bifunctor is localized through the original
enhanced weak maps in both inputs. Internal Hom is the native right
adjoint to this fixed convolution, with parameter maps given by the
native mates. Evaluation is its actual adjunction counit.

Structural source inputs provide the original bounded images, native
descent and adjoint existence. The convolution and Hom functors are
computed from these prescribed operators and universal constructions.

Source: D'Agnolo--Kashiwara1311.2374v2, Definitions3.3.4,4.1.2 and
4.4.1, Proposition4.1.5. Native localization and mates are Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679, Apache2.0, Joël Riou.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.EnhancedConvolutionModels

open _root_.CategoryTheory _root_.Opposite
open CompactSupportIndSheaves BorderedRealSpaceModels BorderedIndDerivedModels
open EnhancedIndQuotientModels BorderedGraphKernelModels BorderedRealTimeModels
open BoundedIndOperationSources EnhancedNullClosureModels
open MathlibExt.CategoryTheory.NativeParametrizedAdjoints

variable (k : Type) [Field k] (M : TopCat.{0}) [T2Space M]
  [CompactSheafSource k M]
  [CompactSheafSource k (enhancedSpace M).ambient]
  [CompactSheafSource k (boundarySpace (enhancedSpace M))]

local instance convolutionAbelianPreadditive (X : TopCat.{0}) [CompactSheafSource k X] :
    Preadditive (IndSheaf k X) := Abelian.toPreadditive

attribute [local instance] HasDerivedCategory.standard

local instance enhancedAmbientHausdorff : T2Space (enhancedSpace M).ambient :=
  inferInstanceAs (T2Space (M × EReal))

variable (B : ProperSource k (boundaryInclusion (enhancedSpace M)))
  (P : InverseSource k (baseProjection M))

/-- The original native enhanced quotient, with its fixed boundary and base-inverse-image sources. -/
abbrev EnhancedCategory :=
  letI := B.additive
  letI := P.additive
  EnhancedDerived k M B.compact B.ind B.derived P.ordinary P.ind P.exact

/-- The same original enhanced weak maps on the original bounded ambient category. -/
def enhancedSourceWeak : MorphismProperty (BoundedIndDerived k (enhancedSpace M).ambient) :=
  letI := B.additive
  letI := P.additive
  enhancedWeak k M B.compact B.ind B.derived P.ordinary P.ind P.exact

/-- The same original native enhanced quotient functor. -/
def enhancedSourceProjection :
    BoundedIndDerived k (enhancedSpace M).ambient ⥤ EnhancedCategory k M B P :=
  letI := B.additive
  letI := P.additive
  enhancedQuotient k M B.compact B.ind B.derived P.ordinary P.ind P.exact

instance enhancedSourceWeak_containsIdentities : (enhancedSourceWeak k M B P).ContainsIdentities := by
  have := B.additive
  have := P.additive
  exact enhancedWeak_containsIdentities k M B.compact B.ind B.derived P.ordinary P.ind P.exact

instance enhancedSourceProjection_isLocalization :
    (enhancedSourceProjection k M B P).IsLocalization (enhancedSourceWeak k M B P) := by
  have := B.additive
  have := P.additive
  exact inferInstanceAs (((enhancedWeak k M B.compact B.ind B.derived P.ordinary P.ind P.exact).Q).IsLocalization
    (enhancedWeak k M B.compact B.ind B.derived P.ordinary P.ind P.exact))

/-- The original product ambient used by the actual real-sum graph. -/
abbrev sumProduct := ambientProduct (doubleTimeSpace M) (enhancedSpace M)

variable
  [CompactSheafSource k (doubleTimeSpace M).ambient]
  [CompactSheafSource k (sumProduct M)]
  [HasSheafify (Opens.grothendieckTopology (doubleTimeSpace M).ambient) (ModuleCat.{0} k)]
  [HasSheafify (Opens.grothendieckTopology (sumProduct M)) (ModuleCat.{0} k)]
  (G : TimeSumGraphSource M)
  [HasSheafify (Opens.grothendieckTopology
    (closedGraphSpace (doubleTimeSpace M) (enhancedSpace M) (timeSumBordered M G))) (ModuleCat.{0} k)]
  (S : TensorSource k (sumProduct M))
  (I : InverseSource k (firstProjection (doubleTimeSpace M) (enhancedSpace M)))
  (Q : ProperSource k (secondProjection (doubleTimeSpace M) (enhancedSpace M)))

/-- The original real-sum graph proper image, using its actual finite-interior graph coefficient object. -/
def sumGraphImage :
    BoundedIndDerived k (doubleTimeSpace M).ambient ⥤ BoundedIndDerived k (enhancedSpace M).ambient :=
  inverseFunctor k (firstProjection (doubleTimeSpace M) (enhancedSpace M)) I ⋙
    (tensorFunctor k (sumProduct M) S).obj
      (graphKernel (doubleTimeSpace M) (enhancedSpace M) (timeSumBordered M G) k I.ordinary S.cohomology) ⋙
    properFunctor k (secondProjection (doubleTimeSpace M) (enhancedSpace M)) Q

variable (T : TensorSource k (doubleTimeSpace M).ambient)
  (I₁ : InverseSource k (timeFirst M)) (I₂ : InverseSource k (timeSecond M))

/-- The complete actual real convolution bifunctor on source representatives, followed by the native enhanced quotient. -/
def convolutionBeforeQuotient :
    BoundedIndDerived k (enhancedSpace M).ambient ⥤
      BoundedIndDerived k (enhancedSpace M).ambient ⥤ EnhancedCategory k M B P :=
  inverseFunctor k (timeFirst M) I₁ ⋙ tensorFunctor k (doubleTimeSpace M).ambient T ⋙
    (Functor.whiskeringLeft (BoundedIndDerived k (enhancedSpace M).ambient)
      (BoundedIndDerived k (doubleTimeSpace M).ambient)
      (BoundedIndDerived k (doubleTimeSpace M).ambient)).obj (inverseFunctor k (timeSecond M) I₂) ⋙
    (Functor.whiskeringRight (BoundedIndDerived k (enhancedSpace M).ambient)
      (BoundedIndDerived k (doubleTimeSpace M).ambient) (EnhancedCategory k M B P)).obj
      (sumGraphImage k M G S I Q ⋙ enhancedSourceProjection k M B P)

/-- Native descent concerns every actual enhanced weak map in both inputs of this exact real formula. -/
structure ConvolutionDescentSource : Prop where
  inverts : MorphismProperty.IsInvertedBy₂ (enhancedSourceWeak k M B P) (enhancedSourceWeak k M B P)
    (convolutionBeforeQuotient k M B P G S I Q T I₁ I₂)

/-- The actual enhanced real convolution is the native two-input localization of that exact source formula. -/
def convolution (H : ConvolutionDescentSource k M B P G S I Q T I₁ I₂) :
    EnhancedCategory k M B P ⥤ EnhancedCategory k M B P ⥤ EnhancedCategory k M B P :=
  Localization.lift₂ (convolutionBeforeQuotient k M B P G S I Q T I₁ I₂) H.inverts
    (enhancedSourceProjection k M B P) (enhancedSourceProjection k M B P)

variable (H : ConvolutionDescentSource k M B P G S I Q T I₁ I₂)

/-- The condition that the enhanced convolution defined by the given source data is closed: for
every object $K$ of the enhanced category, the functor $L ↦ K ⋆ L$ is a left adjoint. -/
structure ConvolutionClosedSource : Prop where
  closed : ∀ K : EnhancedCategory k M B P,
    ((convolution k M B P G S I Q T I₁ I₂ H).obj K).IsLeftAdjoint

/-- Actual enhanced internal Hom, contravariant in its first input and covariant in its second. -/
def enhancedIhomPlus (C : ConvolutionClosedSource k M B P G S I Q T I₁ I₂ H) :
    (EnhancedCategory k M B P)ᵒᵖ ⥤ EnhancedCategory k M B P ⥤ EnhancedCategory k M B P :=
  letI := C.closed
  rightAdjointBifunctor (convolution k M B P G S I Q T I₁ I₂ H)

/-- The full native convolution/Hom adjunction includes all parameter mate maps. -/
def convolutionIhomAdjunction (C : ConvolutionClosedSource k M B P G S I Q T I₁ I₂ H) :
    convolution k M B P G S I Q T I₁ I₂ H ⊣₂ enhancedIhomPlus k M B P G S I Q T I₁ I₂ H C :=
  letI := C.closed
  nativeParametrizedAdjunction (convolution k M B P G S I Q T I₁ I₂ H)

/-- Enhanced evaluation is the actual native counit of this fixed convolution/internal-Hom pair. -/
def enhancedEvaluation (C : ConvolutionClosedSource k M B P G S I Q T I₁ I₂ H)
    (K L : EnhancedCategory k M B P) :
    ((convolution k M B P G S I Q T I₁ I₂ H).obj K).obj
        (((enhancedIhomPlus k M B P G S I Q T I₁ I₂ H C).obj (op K)).obj L) ⟶ L :=
  letI := C.closed
  (Adjunction.ofIsLeftAdjoint ((convolution k M B P G S I Q T I₁ I₂ H).obj K)).counit.app L

end MathlibExt.AlgebraicGeometry.EnhancedConvolutionModels
