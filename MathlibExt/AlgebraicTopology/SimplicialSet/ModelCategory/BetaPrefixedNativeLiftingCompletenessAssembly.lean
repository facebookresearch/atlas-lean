/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Native lifting/prefixed equation assembly; final SAME-unit inputs still must be derived.
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FunctorialFactorizations

/-!
# Lifting through a trivial cofibration

A commuting square with a trivial cofibration on the left and a fibration on the right has a chosen lift satisfying both factorization equations. If the upper map is a realization weak equivalence, so is the lift; a strict equality after a weak prefix transfers weakness from a specified weak composite to the comparison map.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet

/-- The actual trivial-cofibration prefix and fibration endpoint square. -/
theorem betaLiftSquare {R Z H B : SSet.{u}}
    (β : R ⟶ Z) (rawEvaluation : R ⟶ H) (endpoint : H ⟶ B)
    (targetEvaluation : Z ⟶ B)
    (comm : rawEvaluation ≫ endpoint = β ≫ targetEvaluation) :
    CommSq rawEvaluation β endpoint targetEvaluation := ⟨comm⟩

/-- The lift is constructed from the native lifting property, not supplied by a caller. -/
def betaLift {R Z H B : SSet.{u}}
    (β : R ⟶ Z) (rawEvaluation : R ⟶ H) (endpoint : H ⟶ B)
    (targetEvaluation : Z ⟶ B)
    [Cofibration β] [WeakEquivalence β] [Fibration endpoint]
    (comm : rawEvaluation ≫ endpoint = β ≫ targetEvaluation) : Z ⟶ H :=
  (betaLiftSquare β rawEvaluation endpoint targetEvaluation comm).lift

/-- The literal original beta prefix followed by the constructed lift is the raw map. -/
theorem betaLift_prefixed_evaluation {R Z H B : SSet.{u}}
    (β : R ⟶ Z) (rawEvaluation : R ⟶ H) (endpoint : H ⟶ B)
    (targetEvaluation : Z ⟶ B)
    [Cofibration β] [WeakEquivalence β] [Fibration endpoint]
    (comm : rawEvaluation ≫ endpoint = β ≫ targetEvaluation) :
    β ≫ betaLift β rawEvaluation endpoint targetEvaluation comm = rawEvaluation :=
  (betaLiftSquare β rawEvaluation endpoint targetEvaluation comm).fac_left

/-- The same constructed lift has the exact two-endpoint evaluation after the fibration. -/
theorem betaLift_endpoint_equation {R Z H B : SSet.{u}}
    (β : R ⟶ Z) (rawEvaluation : R ⟶ H) (endpoint : H ⟶ B)
    (targetEvaluation : Z ⟶ B)
    [Cofibration β] [WeakEquivalence β] [Fibration endpoint]
    (comm : rawEvaluation ≫ endpoint = β ≫ targetEvaluation) :
    betaLift β rawEvaluation endpoint targetEvaluation comm ≫ endpoint = targetEvaluation :=
  (betaLiftSquare β rawEvaluation endpoint targetEvaluation comm).fac_right

/-- Weakness of the raw evaluation and beta prefix makes the constructed lift weak. -/
theorem betaLift_weak {R Z H B : SSet.{u}}
    (β : R ⟶ Z) (rawEvaluation : R ⟶ H) (endpoint : H ⟶ B)
    (targetEvaluation : Z ⟶ B)
    [Cofibration β] [WeakEquivalence β] [Fibration endpoint]
    (comm : rawEvaluation ≫ endpoint = β ≫ targetEvaluation)
    (hraw : realizationWeakEquivalences rawEvaluation) :
    realizationWeakEquivalences (betaLift β rawEvaluation endpoint targetEvaluation comm) := by
  have hβ : realizationWeakEquivalences β := (weakEquivalence_iff β).mp inferInstance
  exact realizationWeakEquivalences.of_precomp β _ hβ
    (by rw [betaLift_prefixed_evaluation]; exact hraw)

/-- A strict equation behind the SAME weak beta prefix proves the identity
comparison weak. No cancellation of a monomorphism or epimorphism is used. -/
theorem weak_identity_of_beta_prefixed_equation
    {A U Z H : SSet.{u}} (β : A ⟶ U) (completedSection : U ⟶ Z)
    (lift : Z ⟶ H) (identity : U ⟶ H)
    (hβ : realizationWeakEquivalences β)
    (hsection : realizationWeakEquivalences completedSection)
    (hlift : realizationWeakEquivalences lift)
    (strict_prefixed_equation : β ≫ completedSection ≫ lift = β ≫ identity) :
    realizationWeakEquivalences identity := by
  have composite : realizationWeakEquivalences (β ≫ completedSection ≫ lift) :=
    realizationWeakEquivalences.comp_mem β _ hβ
      (realizationWeakEquivalences.comp_mem completedSection lift hsection hlift)
  rw [strict_prefixed_equation] at composite
  exact realizationWeakEquivalences.of_precomp β identity hβ composite

end SSet
