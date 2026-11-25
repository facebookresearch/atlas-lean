/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.MotivicRealizationComparisons

/-!
# Source-normalized motivic realization comparison requests

The maps are evaluated by reduced-free generators, native Dold--Kan,
native truncation and the fixed K-injective augmentation. Locality,
fibrancy, localization descent and representability are conclusions.
Termwise injectivity refines the published K-injective resolution source;
it is not inferred from K-injectivity alone.

Sources: Voevodsky arXiv:math/0107109v1, Section 2, pp. 3--6;
Mazza--Voevodsky--Weibel, Lectures 3, 13 and 14. Strict Nisnevich
homotopy invariance uses the stated perfect-field hypothesis.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.MotivicRealizationComparisonsWanted

open _root_.CategoryTheory
open MathlibExt.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.FiniteTransferCycleModels
open MathlibExt.AlgebraicGeometry.FiniteTransferProductModels
open MathlibExt.AlgebraicGeometry.NisnevichTransferModels
open MathlibExt.AlgebraicGeometry.MotivicStandardSchemes
open MathlibExt.AlgebraicGeometry.EffectiveMotivicComplexModels
open MathlibExt.AlgebraicGeometry.PointedMotivicModels
open MathlibExt.AlgebraicGeometry.ReducedMotivicCohomologyModels
open MathlibExt.AlgebraicGeometry.MotivicEilenbergMacLaneModels
open MathlibExt.AlgebraicGeometry.MotivicRealizationComparisons

def_wanted reduced_free_adjunction (k : Type) [Field k]
    [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)]
    (F : ReducedFreeNisSystem k) (Q : PointedSimplicialModuleFunctor k) :
    ReducedFreeAdjunction F Q

def_wanted termwise_injective_resolution (k : Type) [Field k]
    [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)] :
    {I : KInjectiveResolutionSystem k // IsTermwiseInjective I}

variable {k : Type} [Field k]
  [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)]
  {D : CompositionSystem k} {G : GraphSystem k}
  [CorrespondenceLaws D G] [CorrespondenceAdditivity D G]
  {P : SmoothProductSystem k} {E : ExternalSystem P}
  {C : CorrespondenceProductModel D G P E} {A : StandardSchemes P}
  {R : RepresentableSystem D G} {S : TransferSheafificationModel D G}
  {T : CycleComplexSystem (D := D) (G := G) (P := P) (E := E)
    (C := C) (A := A) (R := R)} {N : NisTensorSystem k}
  (B : CoefficientComplexSystem (D := D) (G := G) (P := P) (E := E)
    (C := C) (A := A) (R := R) (S := S) T N)
  (I : KInjectiveResolutionSystem k) (Q : PointedSimplicialModuleFunctor k)
  (F : ReducedFreeNisSystem k) (J : ReducedFreeAdjunction F Q)

theorem_wanted motivic_fibrancy [PerfectField k] (hI : IsTermwiseInjective I)
    (p q : ℤ) (V : ModuleCat.{1} ℤ) :
    IsMotivicFibrant A (K B I Q p q V).right

def_wanted localization_comparison [PerfectField k] :
    RepresentabilityMap (A := A) B I Q F J

theorem_wanted realization_represents [PerfectField k]
    (M : RepresentabilityMap (A := A) B I Q F J)
    (X : PointedSpaces (k := k)) (p q : ℤ) (V : ModuleCat.{1} ℤ) :
    Function.Bijective (M.map X p q V)

theorem_wanted realization_pullback [PerfectField k]
    (M : RepresentabilityMap (A := A) B I Q F J)
    (X Y : PointedSpaces (k := k)) (a : X ⟶ Y) (p q : ℤ)
    (V : ModuleCat.{1} ℤ)
    (u : (motivicQ A).obj Y ⟶ (motivicQ A).obj (K B I Q p q V)) :
    M.map X p q V ((motivicQ A).map a ≫ u) =
      ReducedMotivicCohomologyModels.pullback B F a p q V (M.map Y p q V u)

theorem_wanted realization_coefficients [PerfectField k]
    (M : RepresentabilityMap (A := A) B I Q F J)
    (X : PointedSpaces (k := k)) (p q : ℤ)
    (V W : ModuleCat.{1} ℤ) (a : V ⟶ W)
    (u : (motivicQ A).obj X ⟶ (motivicQ A).obj (K B I Q p q V)) :
    M.map X p q W
      (u ≫ (motivicQ A).map (MotivicEilenbergMacLaneModels.coefficientMap B I Q p q a)) =
      ReducedMotivicCohomologyModels.coefficientMap B F X p q a (M.map X p q V u)

end WantedExt.AlgebraicGeometry.MotivicRealizationComparisonsWanted
