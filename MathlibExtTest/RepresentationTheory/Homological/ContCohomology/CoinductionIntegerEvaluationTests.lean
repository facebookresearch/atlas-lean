/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RepresentationTheory.Homological.ContCohomology.CoinductionInvariantEvaluation
import MathlibExt.RepresentationTheory.Homological.ContCohomology.FiniteTupleEquiv
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.ZMod.Basic
meta import Mathlib.Tactic.NormNum

/-!
# Nonzero coinduced integers and coefficient-map evaluation

A discrete order-two group acts trivially on the discrete integer module. The constant
function three is a genuine nonzero coinduced invariant; evaluation at the identity and the
finite-tuple equivalence retain its value. Doubling coefficients sends its evaluation to
six and also doubles a nonconstant coinduced function. Coinduction preserves injectivity of
this concrete map and surjectivity of negation, with the coefficient proofs supplied.
-/

open CategoryTheory ContinuousCohomology

noncomputable section
set_option autoImplicit false

namespace CoinductionIntegerEvaluationTests

private abbrev G := Multiplicative (ZMod 2)
private instance : TopologicalSpace G := ⊥
private instance : DiscreteTopology G := ⟨rfl⟩
private instance : TopologicalSpace ℤ := ⊥
private instance : DiscreteTopology ℤ := ⟨rfl⟩
private instance : ContinuousSMul ℤ ℤ := ⟨continuous_of_discreteTopology⟩
private abbrev X : TopRep.{0, 0, 0} ℤ G := TopRep.of (ContRepresentation.trivial ℤ G ℤ)

private def s : G := Multiplicative.ofAdd (1 : ZMod 2)
private lemma s_ne_one : s ≠ 1 := by decide

private def invariantThree : X.coind₁.ρ.invariants :=
  ⟨ContinuousMap.const G (3 : ℤ), fun g => by
    apply ContinuousMap.ext
    intro h
    change X.ρ g (3 : ℤ) = 3
    rfl⟩

private lemma evaluation_three : coindInvariantEval X invariantThree = 3 := rfl

example : coindInvariantEval X invariantThree = 3 := evaluation_three

example : invariantThree ≠ 0 := by
  intro h
  have he := congrArg (coindInvariantEval X) h
  rw [evaluation_three, map_zero] at he
  exact (by norm_num : (3 : ℤ) ≠ 0) he

example : invariantThree.val s = 3 := by
  have h := coindInvariant_value X invariantThree s
  exact h.symm.trans (by rfl)

private abbrev double : X ⟶ X := (2 : ℤ) • 𝟙 X
private abbrev negate : X ⟶ X := (-1 : ℤ) • 𝟙 X

example : coindInvariantEval X
    (((TopRep.invariantsFunctor ℤ G).map ((TopRep.coind₁Functor ℤ G).map double)).hom
      invariantThree) = 6 := by
  have h := coindInvariantEval_naturality double invariantThree
  exact h.trans (by change (2 : ℤ) * 3 = 6; rfl)

private def varying : X.coind₁ :=
  ⟨fun g => if g = 1 then (0 : ℤ) else 3, continuous_of_discreteTopology⟩

example : (((TopRep.coind₁Functor ℤ G).map double).hom varying) s = 6 := by
  change (2 : ℤ) * (if s = 1 then (0 : ℤ) else 3) = 6
  rw [if_neg s_ne_one]
  rfl

example : Function.Injective ((TopRep.coind₁Functor ℤ G).map double).hom := by
  apply coindOneMap_injective double
  intro x y h
  change (2 : ℤ) * x = 2 * y at h
  exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) h

example : Function.Surjective ((TopRep.coind₁Functor ℤ G).map negate).hom := by
  apply coindOneMap_surjective negate
  intro y
  refine ⟨-y, ?_⟩
  change (-1 : ℤ) • (-y) = y
  simp

example : resolutionFinContinuousLinearEquiv X 1 invariantThree.val (fun _ => s) = 3 := by
  rw [resolutionFinContinuousLinearEquiv_apply]
  rfl

end CoinductionIntegerEvaluationTests
