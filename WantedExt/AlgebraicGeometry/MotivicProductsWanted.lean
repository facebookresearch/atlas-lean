/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.MotivicCohomologyProducts

/-!
# Actual cycle, shuffle, coefficient and cup construction requests

Every construction target is normalized by literal external finite cycles,
all shuffle/face terms, actual coefficient pure tensors, the native
resolution augmentations or the reduced-free product generators. The
public cup is already the specified composite of these native source maps.
Quasi-isomorphism, free-source flatness and cup laws are separate goals.

Sources: Mazza--Voevodsky--Weibel, Constructions 3.10--3.11 and Lectures
8/14; Voevodsky arXiv:math/0107109v1, Section 2, equations 2.1--2.4.
The imported Alexander--Whitney/Dold--Kan ports retain Tau Ceti revision
62bbc0596dc3539d488232e4e924a338548ea0a9 and Apache 2.0 attribution.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.MotivicProductsWanted

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open MathlibExt.AlgebraicGeometry
open FiniteTransferCycleModels FiniteTransferProductModels
open NisnevichTransferModels MotivicStandardSchemes
open EffectiveMotivicComplexModels PointedMotivicModels
open ReducedMotivicCohomologyModels MotivicRealizationComparisons
open MotivicCycleProducts MotivicTensorOperations MotivicCohomologyProducts
open PointedMotivicQuotients
open scoped Simplicial

theorem_wanted tensor_left_additive (k : Type) [Field k]
    [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)]
    (N : NisTensorSystem k) : N.functor.Additive

theorem_wanted tensor_right_additive (k : Type) [Field k]
    [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)]
    (N : NisTensorSystem k) (F : NisModules (k := k)) : (N.functor.obj F).Additive

def_wanted torus_concatenation (k : Type) [Field k]
    (P : SmoothProductSystem k) (A : StandardSchemes P) : TorusConcatenation A

variable {k : Type} [Field k]
  [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)]
  (N : NisTensorSystem k) [N.functor.Additive] [∀ F, (N.functor.obj F).Additive]

def_wanted shuffle_alexander_whitney : EilenbergZilberModel N

def_wanted negative_tensor_comparison : NegativeTensorComparison N

def_wanted kflat_resolution : KFlatResolutionSystem N

def_wanted derived_tensor (F : KFlatResolutionSystem N) : DerivedTensorSource N F

def_wanted derived_tensor_shifts (F : KFlatResolutionSystem N)
    (D : DerivedTensorSource N F) : DerivedTensorShifts N F D

def_wanted reduced_smash_comultiplication (R₁ : ReducedFreeNisSystem k) :
    ReducedSmashComultiplication N R₁

theorem_wanted free_tensor_comparison (F : KFlatResolutionSystem N)
    (D : DerivedTensorSource N F) (R₁ : ReducedFreeNisSystem k) :
    IsFreeTensorComparison N F D R₁

theorem_wanted shuffle_quasi_iso (Z : EilenbergZilberModel N)
    (F H : SimplicialObject (NisModules (k := k))) : QuasiIso (Z.shuffle F H)

variable {D₀ : CompositionSystem k} {G : GraphSystem k}
  [CorrespondenceLaws D₀ G] [CorrespondenceAdditivity D₀ G]
  {P : SmoothProductSystem k} {E : ExternalSystem P}
  {C : CorrespondenceProductModel D₀ G P E} {A : StandardSchemes P}
  {R : RepresentableSystem D₀ G} {S : TransferSheafificationModel D₀ G}
  (T : CycleComplexSystem (D := D₀) (G := G) (P := P) (E := E)
    (C := C) (A := A) (R := R)) (J : TorusConcatenation A)

def_wanted singular_cycle_product : SingularCycleProduct (S := S) N T J

variable
  (B : CoefficientComplexSystem (D := D₀) (G := G) (P := P) (E := E)
    (C := C) (A := A) (R := R) (S := S) T N)
  (M₀ : SingularCycleProduct (S := S) N T J) (Z : EilenbergZilberModel N)
  (V : NegativeTensorComparison N)

def_wanted coefficient_cycle_product : CoefficientMultiplicationSystem N T B M₀ Z V

variable (L : CoefficientMultiplicationSystem N T B M₀ Z V)
  (F : KFlatResolutionSystem N) (D : DerivedTensorSource N F)
  (H : DerivedTensorShifts N F D) (R₁ : ReducedFreeNisSystem k)
  (M : ReducedSmashComultiplication N R₁)

theorem_wanted cup_pullback (hF : IsFreeTensorComparison N F D R₁)
    (X Y : PointedSpaces (k := k)) (a : X ⟶ Y) (p q r s : ℤ)
    (A₁ A₂ A₃ : ModuleCat.{1} ℤ) (μ : TensorProduct ℤ A₁ A₂ →ₗ[ℤ] A₃)
    (u : ReducedCohomology B R₁ Y p q A₁) (v : ReducedCohomology B R₁ Y r s A₂) :
    ReducedMotivicCohomologyModels.pullback B R₁ a (p + r) (q + s) A₃
      (cup N B L F D H R₁ M hF Y p q r s A₁ A₂ A₃ μ u v) =
    cup N B L F D H R₁ M hF X p q r s A₁ A₂ A₃ μ
      (ReducedMotivicCohomologyModels.pullback B R₁ a p q A₁ u)
      (ReducedMotivicCohomologyModels.pullback B R₁ a r s A₂ v)

end WantedExt.AlgebraicGeometry.MotivicProductsWanted
