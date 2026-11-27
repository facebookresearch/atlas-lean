/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.EtaleReducedGaloisStalks
public import MathlibExt.AlgebraicGeometry.IntegralRamificationModels
public import Mathlib.RingTheory.Henselian
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.Data.Int.Interval

/-!
# Source-fixed finite ramification models of actual vanishing stalks

Each finite Galois layer lies in the same separable closure as the
absolute Galois group. Its representation must agree on every restricted
automorphism with the actual reduced-stalk operator. Lower groups are
computed on the actual integral closure and its maximal-ideal quotients.

Total dimension is the alternating finite sum of the actual cohomological
dimensions and those Swan sums. Integrality is not an input. Bounds,
finite descent and ramification constructors are separate source requests.

Reference: Saito, arXiv:1510.03018v4, Section 1.3 and Theorem 4.9.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.FiniteRamificationStalkModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open AdicDerivedContracts IntegralRamificationModels
open _root_.MathlibExt.RingTheory.DerivedModuleScalarOperations
open scoped BigOperators

attribute [local instance] HasDerivedCategory.standard

variable (K : Type) [Field K]

def separableRestriction : Field.absoluteGaloisGroup K →* Gal(SeparableClosure K/K) where
  toFun g := g.separableClosure
  map_one' := rfl
  map_mul' _ _ := rfl

def finiteRestriction (E : IntermediateField K (SeparableClosure K)) [IsGalois K E] :
    Field.absoluteGaloisGroup K →* Gal(E/K) :=
  (AlgEquiv.restrictNormalHom E).comp (separableRestriction K)

variable (Λ κ : Type) [CommRing Λ] [Field κ] [finiteCoefficient : Finite κ]
  (r : Λ →+* κ) [HasExtension r] [DerivedFunctorTheory Λ]
  (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Algebra R K] [IsFractionRing R K] [henselianR : HenselianLocalRing R]
  (F : Derived Λ (Spec (.of K)))

include finiteCoefficient henselianR in
/-- A finite layer fixed by the original stalk and original valuation ring. -/
structure Layer (q : ℤ) where
  E : IntermediateField K (SeparableClosure K)
  [finite : FiniteDimensional K E]
  [galois : IsGalois K E]
  [baseAlgebra : Algebra R E]
  [tower : IsScalarTower R K E]
  [integerDVR : IsDiscreteValuationRing (integralClosure R E)]
  [finiteCohomology : Module.Finite κ (EtaleReducedGaloisStalks.cohomology Λ κ r K F q)]
  integralAction : IntegralAction R K E
  quotientActions : QuotientActions R K E integralAction
  cutoff : FiniteCut R K E quotientActions
  representation : Gal(E/K) →*
    Module.End κ (EtaleReducedGaloisStalks.cohomology Λ κ r K F q)
  normalized : ∀ g : Field.absoluteGaloisGroup K,
    representation (finiteRestriction K E g) = EtaleReducedGaloisStalks.operator Λ κ r K F q g

attribute [instance] Layer.finite Layer.galois Layer.baseAlgebra Layer.tower
  Layer.integerDVR

def Layer.swan {q : ℤ} (L : Layer K Λ κ r R F q) : ℚ :=
  letI := L.finiteCohomology
  IntegralRamificationModels.swan R K L.E L.representation L.quotientActions L.cutoff

def Layer.totalDimension {q : ℤ} (L : Layer K Λ κ r R F q) : ℚ :=
  letI := L.finiteCohomology
  (Module.finrank κ (EtaleReducedGaloisStalks.cohomology Λ κ r K F q) : ℚ) + L.swan

/-- One actual cohomological bound, with no unrelated finite list of representations. -/
structure BoundedRamification where
  lower : ℤ
  upper : ℤ
  vanishing : ∀ q : ℤ, q < lower ∨ upper < q →
    IsZero (EtaleReducedGaloisStalks.cohomology Λ κ r K F q)
  layer : ∀ q : Set.Icc lower upper, Layer K Λ κ r R F q.val

/-- The actual alternating dimension-plus-Swan sum in every cohomological degree. -/
def totalDimension (B : BoundedRamification K Λ κ r R F) : ℚ :=
  ∑ q : Set.Icc B.lower B.upper,
    (-1 : ℚ) ^ q.val.natAbs * (B.layer q).totalDimension

end MathlibExt.AlgebraicGeometry.FiniteRamificationStalkModels
