/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalEndpoint

/-!
# Naive fibrant objects for the finite Joyal interval

The specified auxiliary terminal-map predicate is exactly the native
quasicategory predicate, for every simplicial set. Inner horns give the
forward implication. For the reverse, the actual endpoint function map
over a terminal target is isomorphic to endpoint evaluation, whose
monomorphism RLP supplies every endpoint-corner test.

This proves the naive-object consequence of Cisinski, *Higher Categories
and Homotopical Algebra*, July 30, 2026, Remarks 3.3.4 and 3.3.8 (printed
pp.94–95) and the proof of Theorem 3.6.1 (printed pp.112–113), before
model assembly.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed

universe u

namespace SSet.joyalInterval

/-- The actual auxiliary naive terminal-map predicate is equivalent to
quasicategory fibrancy for every simplicial set. -/
theorem auxiliaryNaiveFibrantObjects_iff (X : SSet.{u}) :
    auxiliaryNaiveFibrantObjects X ↔ Quasicategory X := by
  change auxiliaryNaiveFibrations (terminal.from X) ↔ Quasicategory X
  constructor
  · intro h
    exact (quasicategory_iff_innerFibration X).mpr
      ((auxiliaryNaiveFibrations_iff (terminal.from X)).mp h).1
  · intro hX
    have : Quasicategory X := hX
    rw [auxiliaryNaiveFibrations_iff_monomorphisms]
    refine ⟨inferInstance, ?_⟩
    intro ε
    have hT : IsTerminal ((ihom joyalInterval).obj (⊤_ SSet.{u})) :=
      IsTerminal.isTerminalObj (ihom joyalInterval) _ terminalIsTerminal
    have : IsIso (endpointEvaluation (⊤_ SSet.{u}) ε) :=
      isIso_of_isTerminal hT terminalIsTerminal _
    let e : Arrow.mk (endpointFunctionMap (terminal.from X) ε) ≅
        Arrow.mk (endpointEvaluation X ε) :=
      Arrow.isoMk' _ _ (Iso.refl _)
        (asIso (pullback.snd (endpointEvaluation (⊤_ SSet.{u}) ε) (terminal.from X)))
        (by simp)
    exact ((MorphismProperty.monomorphisms SSet).rlp.arrow_mk_iso_iff e).mpr
      (endpointEvaluation_mem_rlp_monomorphisms X ε)

/-- Equality of the actual auxiliary naive object property with the native
quasicategory predicate, without introducing a second predicate. -/
theorem auxiliaryNaiveFibrantObjects_eq_quasicategories :
    auxiliaryNaiveFibrantObjects.{u} = (Quasicategory : ObjectProperty SSet.{u}) := by
  funext X
  exact propext (auxiliaryNaiveFibrantObjects_iff X)

end SSet.joyalInterval
