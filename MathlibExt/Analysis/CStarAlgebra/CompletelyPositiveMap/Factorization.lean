/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.CompletelyPositiveMap.Approximation
public import MathlibExt.Analysis.CStarAlgebra.CompletelyPositiveMap.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.Module.Submodule.LinearMap

/-!
# Genuine completely positive contractive factorizations

Two actual canonical CP maps and their contraction bounds factor through an
externally fixed C-star algebra. The matrix specialization uses the existing
C-star matrix algebra under explicit scalar spectral dictionaries. It admits
zero dimensions, zero coefficients and nonunital source/target algebras.

Approximation predicates quantify these genuine data. No approximation,
nuclearity, matrix model, norm, unit, representation or class comparison is
stored as an output field. Only the forward finite-linear-range argument is
included; reverse and unital-normalization comparisons are separate work.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace CompletelyPositiveMap

universe uA uB uD

/-- **Completely positive contraction factorization.** For nonunital complex C*-algebras `A,B,D` in
their spectral orders, a CP contraction factorization consists of contractions `α : A →CP D` and `β
: D →CP B`. Its composite is the map `a ↦ β(α(a))`. -/
structure ContractionFactorization
    (A : Type uA) (B : Type uB) (D : Type uD)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    [NonUnitalCStarAlgebra D] where
  /-- The actual forward CP contraction from A to the intermediate algebra D. -/
  toIntermediate : Canonical A D
  /-- The actual return CP contraction from the intermediate algebra D to B. -/
  fromIntermediate : Canonical D B
  toIntermediate_contractive :
    letI : PartialOrder A := CStarAlgebra.spectralOrder A
    letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
    letI : PartialOrder D := CStarAlgebra.spectralOrder D
    letI : StarOrderedRing D := CStarAlgebra.spectralOrderedRing D
    ∀ a : A, ‖toIntermediate a‖ ≤ ‖a‖
  fromIntermediate_contractive :
    letI : PartialOrder D := CStarAlgebra.spectralOrder D
    letI : StarOrderedRing D := CStarAlgebra.spectralOrderedRing D
    letI : PartialOrder B := CStarAlgebra.spectralOrder B
    letI : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
    ∀ d : D, ‖fromIntermediate d‖ ≤ ‖d‖

namespace ContractionFactorization

variable {A : Type uA} {B : Type uB} {D : Type uD}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable [NonUnitalCStarAlgebra D]

/-- **Equality of CP contraction factorizations.** For nonunital complex C*-algebras `A,B,D` in their
spectral orders, a CP contraction factorization consists of contractions `α : A →CP D` and `β : D
→CP B`. Two such factorizations are equal if their maps `α` and `β` agree. -/
@[ext]
theorem ext {P Q : ContractionFactorization A B D}
    (hTo : P.toIntermediate = Q.toIntermediate)
    (hFrom : P.fromIntermediate = Q.fromIntermediate) : P = Q := by
  cases P
  cases Q
  cases hTo
  cases hFrom
  rfl

/-- **Composite of CP contractions.** For nonunital complex C*-algebras `A,B,D` in their spectral
orders, a CP contraction factorization consists of contractions `α : A →CP D` and `β : D →CP B`.
Their composite `β ∘ α : A →CP B` is completely positive. -/
def composite (P : ContractionFactorization A B D) : Canonical A B := by
  letI : PartialOrder A := CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  letI : PartialOrder D := CStarAlgebra.spectralOrder D
  letI : StarOrderedRing D := CStarAlgebra.spectralOrderedRing D
  letI : PartialOrder B := CStarAlgebra.spectralOrder B
  letI : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  exact CompletelyPositiveMap.comp P.fromIntermediate P.toIntermediate

/-- **Evaluation of a CP factorization.** For nonunital complex C*-algebras `A,B,D` in their spectral
orders, a CP contraction factorization consists of contractions `α : A →CP D` and `β : D →CP B`. At
every `a ∈ A`, the composite equals `β(α(a))`. -/
theorem composite_apply (P : ContractionFactorization A B D) (a : A) :
    letI : PartialOrder A := CStarAlgebra.spectralOrder A
    letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
    letI : PartialOrder D := CStarAlgebra.spectralOrder D
    letI : StarOrderedRing D := CStarAlgebra.spectralOrderedRing D
    letI : PartialOrder B := CStarAlgebra.spectralOrder B
    letI : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
    P.composite a = P.fromIntermediate (P.toIntermediate a) := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let : PartialOrder D := CStarAlgebra.spectralOrder D
  let : StarOrderedRing D := CStarAlgebra.spectralOrderedRing D
  let : PartialOrder B := CStarAlgebra.spectralOrder B
  let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  exact CompletelyPositiveMap.comp_apply P.toIntermediate P.fromIntermediate a

/-- **Underlying linear composite of a CP factorization.** For nonunital complex C*-algebras `A,B,D` in
their spectral orders, a CP contraction factorization consists of contractions `α : A →CP D` and `β
: D →CP B`. The underlying complex-linear map is the composite of the underlying linear maps of `α`
and `β`, in that order. -/
theorem composite_toLinearMap (P : ContractionFactorization A B D) :
    letI : PartialOrder A := CStarAlgebra.spectralOrder A
    letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
    letI : PartialOrder D := CStarAlgebra.spectralOrder D
    letI : StarOrderedRing D := CStarAlgebra.spectralOrderedRing D
    letI : PartialOrder B := CStarAlgebra.spectralOrder B
    letI : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
    P.composite.toLinearMap =
      P.fromIntermediate.toLinearMap.comp P.toIntermediate.toLinearMap := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let : PartialOrder D := CStarAlgebra.spectralOrder D
  let : StarOrderedRing D := CStarAlgebra.spectralOrderedRing D
  let : PartialOrder B := CStarAlgebra.spectralOrder B
  let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  exact CompletelyPositiveMap.toLinearMap_comp P.toIntermediate P.fromIntermediate

/-- **A CP factorization is contractive.** For nonunital complex C*-algebras `A,B,D` in their spectral
orders, a CP contraction factorization consists of contractions `α : A →CP D` and `β : D →CP B`. For
every `a ∈ A`, `‖β(α(a))‖ ≤ ‖a‖`. -/
theorem composite_contractive (P : ContractionFactorization A B D) :
    letI : PartialOrder A := CStarAlgebra.spectralOrder A
    letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
    letI : PartialOrder D := CStarAlgebra.spectralOrder D
    letI : StarOrderedRing D := CStarAlgebra.spectralOrderedRing D
    letI : PartialOrder B := CStarAlgebra.spectralOrder B
    letI : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
    ∀ a : A, ‖P.composite a‖ ≤ ‖a‖ := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let : PartialOrder D := CStarAlgebra.spectralOrder D
  let : StarOrderedRing D := CStarAlgebra.spectralOrderedRing D
  let : PartialOrder B := CStarAlgebra.spectralOrder B
  let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  intro a
  rw [composite_apply]
  exact (P.fromIntermediate_contractive (P.toIntermediate a)).trans
    (P.toIntermediate_contractive a)

/-- **Zero CP contraction factorization.** For nonunital complex C*-algebras `A,B,D` in their spectral
orders, a CP contraction factorization consists of contractions `α : A →CP D` and `β : D →CP B`.
Choosing both maps to be zero gives a factorization through `D`, without any unit assumption. -/
def zero (A : Type uA) (B : Type uB) (D : Type uD)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    [NonUnitalCStarAlgebra D] : ContractionFactorization A B D := by
  letI : PartialOrder A := CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  letI : PartialOrder D := CStarAlgebra.spectralOrder D
  letI : StarOrderedRing D := CStarAlgebra.spectralOrderedRing D
  letI : PartialOrder B := CStarAlgebra.spectralOrder B
  letI : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  refine ⟨CompletelyPositiveMapClass.toCompletelyPositiveLinearMap
      (0 : A →⋆ₙₐ[ℂ] D),
    CompletelyPositiveMapClass.toCompletelyPositiveLinearMap (0 : D →⋆ₙₐ[ℂ] B), ?_, ?_⟩
  · intro a
    change ‖(0 : D)‖ ≤ ‖a‖
    simpa only [norm_zero] using norm_nonneg a
  · intro d
    change ‖(0 : B)‖ ≤ ‖d‖
    simpa only [norm_zero] using norm_nonneg d

/-- **Composite of the zero CP factorization.** For nonunital complex C*-algebras `A,B,D` in their
spectral orders, a CP contraction factorization consists of contractions `α : A →CP D` and `β : D
→CP B`. When both maps are zero, the composite evaluates to zero at every `a ∈ A`. -/
theorem zero_composite_apply (a : A) :
    letI : PartialOrder A := CStarAlgebra.spectralOrder A
    letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
    letI : PartialOrder D := CStarAlgebra.spectralOrder D
    letI : StarOrderedRing D := CStarAlgebra.spectralOrderedRing D
    letI : PartialOrder B := CStarAlgebra.spectralOrder B
    letI : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
    (zero A B D).composite a = 0 := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let : PartialOrder D := CStarAlgebra.spectralOrder D
  let : StarOrderedRing D := CStarAlgebra.spectralOrderedRing D
  let : PartialOrder B := CStarAlgebra.spectralOrder B
  let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  rfl

/-- **Factorization through the zero algebra.** For nonunital complex C*-algebras `A,B,D` in their
spectral orders, a CP contraction factorization consists of contractions `α : A →CP D` and `β : D
→CP B`. If `D` consists only of zero, the composite is zero at every point of `A`. -/
theorem composite_eq_zero_of_subsingleton [Subsingleton D]
    (P : ContractionFactorization A B D) (a : A) :
    letI : PartialOrder A := CStarAlgebra.spectralOrder A
    letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
    letI : PartialOrder D := CStarAlgebra.spectralOrder D
    letI : StarOrderedRing D := CStarAlgebra.spectralOrderedRing D
    letI : PartialOrder B := CStarAlgebra.spectralOrder B
    letI : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
    P.composite a = 0 := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let : PartialOrder D := CStarAlgebra.spectralOrder D
  let : StarOrderedRing D := CStarAlgebra.spectralOrderedRing D
  let : PartialOrder B := CStarAlgebra.spectralOrder B
  let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  rw [composite_apply, Subsingleton.elim (P.toIntermediate a) (0 : D)]
  exact map_zero P.fromIntermediate

/-- **Finite-set approximation by a CP factorization.** For nonunital complex C*-algebras `A,B,D` in
their spectral orders, a CP contraction factorization consists of contractions `α : A →CP D` and `β
: D →CP B`. For a function `f : A → B`, a finite subset `F ⊆ A`, and a real number `ε`, this means
`‖β(α(a)) - f(a)‖ < ε` for every `a ∈ F`. -/
def ApproximatesOn (P : ContractionFactorization A B D)
    (f : A → B) (F : Finset A) (ε : ℝ) : Prop :=
  letI : PartialOrder A := CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  letI : PartialOrder D := CStarAlgebra.spectralOrder D
  letI : StarOrderedRing D := CStarAlgebra.spectralOrderedRing D
  letI : PartialOrder B := CStarAlgebra.spectralOrder B
  letI : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  ∀ a ∈ F, ‖P.composite a - f a‖ < ε

/-- **Finite rank of a CP factorization.** For nonunital complex C*-algebras `A,B,D` in their spectral
orders, a CP contraction factorization consists of contractions `α : A →CP D` and `β : D →CP B`. If
the intermediate algebra `D` is finite-dimensional over `ℂ`, the complex-linear range of the
composite is finite-dimensional. -/
theorem finiteDimensional_range_composite [FiniteDimensional ℂ D]
    (P : ContractionFactorization A B D) :
    letI : PartialOrder A := CStarAlgebra.spectralOrder A
    letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
    letI : PartialOrder D := CStarAlgebra.spectralOrder D
    letI : StarOrderedRing D := CStarAlgebra.spectralOrderedRing D
    letI : PartialOrder B := CStarAlgebra.spectralOrder B
    letI : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
    FiniteDimensional ℂ (LinearMap.range P.composite.toLinearMap) := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let : PartialOrder D := CStarAlgebra.spectralOrder D
  let : StarOrderedRing D := CStarAlgebra.spectralOrderedRing D
  let : PartialOrder B := CStarAlgebra.spectralOrder B
  let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  rw [composite_toLinearMap]
  have hRange :=
    LinearMap.range_comp_le_range P.toIntermediate.toLinearMap P.fromIntermediate.toLinearMap
  let : FiniteDimensional ℂ (LinearMap.range P.fromIntermediate.toLinearMap) := inferInstance
  exact FiniteDimensional.of_injective (Submodule.inclusion hRange)
    (Submodule.inclusion_injective hRange)

end ContractionFactorization

/-- **Matrix CP contraction factorization.** For nonunital complex C*-algebras `A,B` and `n ∈ ℕ`, this
is a pair of completely positive contractions from `A` to the complex `n × n` C*-matrix algebra and
from that matrix algebra to `B`, all in their spectral orders. Size zero gives the zero intermediate
algebra. -/
abbrev MatrixFactorization
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] (n : ℕ) :=
  letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  letI : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing ℂ
  ContractionFactorization A B (CStarMatrix (Fin n) (Fin n) ℂ)

variable {A : Type uA} {B : Type uB}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- **Approximation through finite matrix algebras.** For nonunital complex C*-algebras `A,B`, a
function `f : A → B` has this property when, for every finite `F ⊆ A` and `ε > 0`, there is a
positive integer `n` and completely positive contractions `α : A → Mₙ(ℂ)` and `β : Mₙ(ℂ) → B` with
`‖β(α(a)) - f(a)‖ < ε` for every `a ∈ F`. -/
def HasMatrixCPCApproximation (f : A → B) : Prop :=
  letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  letI : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing ℂ
  ∀ (F : Finset A) (ε : ℝ), 0 < ε →
    ∃ n : ℕ+, ∃ P : MatrixFactorization A B (n : ℕ), P.ApproximatesOn f F ε

/-- **Matrix approximation implies finite-rank CP approximation.** For nonunital complex C*-algebras
`A,B`, if `f : A → B` is approximable on every finite set through finite complex matrix algebras by
completely positive contractions, then it is approximable on every finite set by finite-rank
completely positive contractions. -/
theorem HasMatrixCPCApproximation.hasFiniteRankCPCApproximation
    {f : A → B} (h : HasMatrixCPCApproximation f) :
    HasFiniteRankCPCApproximation f := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let : PartialOrder B := CStarAlgebra.spectralOrder B
  let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  let : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  let : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing ℂ
  change ∀ (F : Finset A) (ε : ℝ), 0 < ε →
    ∃ phi : Canonical A B,
      (∀ a : A, ‖phi a‖ ≤ ‖a‖) ∧
      FiniteDimensional ℂ (LinearMap.range phi.toLinearMap) ∧
      ∀ a ∈ F, ‖phi a - f a‖ < ε
  intro F ε hε
  obtain ⟨n, P, hP⟩ := h F ε hε
  let D := CStarMatrix (Fin n) (Fin n) ℂ
  let : PartialOrder D := CStarAlgebra.spectralOrder D
  let : StarOrderedRing D := CStarAlgebra.spectralOrderedRing D
  let : FiniteDimensional ℂ D :=
    (CStarMatrix.ofMatrixₗ (R := ℂ) (m := Fin n) (n := Fin n) (A := ℂ)).finiteDimensional
  refine ⟨P.composite, P.composite_contractive, P.finiteDimensional_range_composite, ?_⟩
  exact hP

end CompletelyPositiveMap

namespace CStarAlgebra

universe uA

/-- **Completely positive approximation property.** A nonunital complex C*-algebra `A` has CPAP when its
identity is approximable on every finite subset in norm by composites of completely positive
contractions `A → Mₙ(ℂ) → A`, with `n > 0`. Equivalently, every finite set and every positive
tolerance admit such a matrix factorization. -/
def HasCPAP (A : Type uA) [NonUnitalCStarAlgebra A] : Prop :=
  CompletelyPositiveMap.HasMatrixCPCApproximation (id : A → A)

end CStarAlgebra
