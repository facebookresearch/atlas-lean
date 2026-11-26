/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.MotivicAffineTateComparisons

/-!
# Canonically oriented affine/Tate and pointed product construction goals

Theorem2.1 weak equivalence, coefficient naturality, multiplication and
the fixed native rank-one torus/cofiber orientation are *conclusions* of
the comparison construction. They are not supplied inside an input recipe
or used to define the underlying motivic complexes/cohomology.
All actual maps/objects are in the imported normalized source models.

Sources: Voevodsky arXiv:math/0107109v1, Section2/Theorem2.1 and Section4;
Mazza--Voevodsky--Weibel, Definition3.1 and Lectures3/14/16.
The source comparison proof uses the explicitly retained perfect-field scope.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.MotivicAffineTateWanted

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open MathlibExt.AlgebraicGeometry
open FiniteTransferCycleModels FiniteTransferProductModels
open NisnevichTransferModels MotivicStandardSchemes
open EffectiveMotivicComplexModels PointedMotivicModels
open ReducedMotivicCohomologyModels MotivicEilenbergMacLaneModels
open MotivicRealizationComparisons MotivicCycleProducts MotivicTensorOperations
open MotivicCohomologyProducts MotivicPointedProducts MotivicAffineQuotientModels
open MotivicTorusClassModels MotivicTateThomModels MotivicAffineTateComparisons
open MotivicCofiberComparisons

def_wanted standard_torus_open (k : Type) [Field k]
    [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)]
    (P : SmoothProductSystem k) (A : StandardSchemes P) : TorusOpenAffine (P := P) (A := A)

def_wanted relative_affine_cofiber (k : Type) [Field k]
    [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)]
    (P : SmoothProductSystem k) (A : StandardSchemes P)
    (O : TorusOpenAffine (P := P) (A := A)) : RelativeA1CofiberSource O

variable {k : Type} [Field k]
  [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)]
  {D₀ : CompositionSystem k} {G : GraphSystem k}
  [CorrespondenceLaws D₀ G] [CorrespondenceAdditivity D₀ G]
  {P : SmoothProductSystem k} {E : ExternalSystem P}
  {C : CorrespondenceProductModel D₀ G P E} {A : StandardSchemes P}
  {R : RepresentableSystem D₀ G} {S : TransferSheafificationModel D₀ G}
  (T : CycleComplexSystem (D := D₀) (G := G) (P := P) (E := E)
    (C := C) (A := A) (R := R)) (F : ReducedFreeNisSystem k)

def_wanted torus_graph_linearization : TorusCycleLinearization (S := S) T F

variable (N : NisTensorSystem k) [N.functor.Additive] [∀ H, (N.functor.obj H).Additive]
  (B : CoefficientComplexSystem (D := D₀) (G := G) (P := P) (E := E)
    (C := C) (A := A) (R := R) (S := S) T N)
  (I : KInjectiveResolutionSystem k) (Q : PointedSimplicialModuleFunctor k)
  (J : ReducedFreeAdjunction F Q) (M : ModuleSectionSystem Q)

def_wanted integer_coefficient_inclusion :
    IntegerCoefficientInclusions (T := T) (N := N) (B := B)

def_wanted affine_thom_cycle_sections :
    AffineThomCycleSections (D₀ := D₀) (G := G) (P := P) (A := A) (R := R)
      (N := N) (Q := Q) (M := M)

variable {J₀ : TorusConcatenation A}
  {M₀ : SingularCycleProduct (S := S) N T J₀} {Z : EilenbergZilberModel N}
  {V₀ : NegativeTensorComparison N}
  (L : CoefficientMultiplicationSystem N T B M₀ Z V₀)
  (F₀ : KFlatResolutionSystem N) (D : DerivedTensorSource N F₀)
  (H : DerivedTensorShifts N F₀ D) (M₁ : ReducedSmashComultiplication N F)
  (hF : IsFreeTensorComparison N F₀ D F)

def_wanted pointed_tate_products : PointedTateProducts N B I Q F J L F₀ D H M₁ hF

variable (K₀ : PointedTateProducts N B I Q F J L F₀ D H M₁ hF)
  (E₀ : AffineCycleProduct (D := D₀) (G := G) (P := P) (A := A) (R := R) N Q E M)
  (T₀ : AffineThomCycleSections (D₀ := D₀) (G := G) (P := P)
    (A := A) (R := R) (N := N) (Q := Q) (M := M))
  (O : TorusOpenAffine (P := P) (A := A)) (R₀ : RelativeA1CofiberSource O)
  (C₀ : CofiberChainSource F (relativeTorusMap O))
  (L₀ : TorusCycleLinearization (S := S) T F)
  (U₀ : IntegerCoefficientInclusions (T := T) (N := N) (B := B))

def_wanted canonical_affine_tate_comparison [PerfectField k] :
    {V : AffineTateMapSystem (N := N) (B := B) (I := I) (Q := Q) //
      IsMotivicComparison (N := N) (B := B) (I := I) (Q := Q) V ∧
      IsCoefficientNatural (N := N) (B := B) (I := I) (Q := Q) V ∧
      IsMultiplicative (N := N) (B := B) (I := I) (Q := Q) (F := F) (J := J)
        (M := M) V K₀ E₀ ∧
      HasRankOneNormalization (N := N) (B := B) (I := I) (Q := Q)
        (F := F) (J := J) (M := M) V T₀ O R₀ C₀ L₀ U₀}

end WantedExt.AlgebraicGeometry.MotivicAffineTateWanted
