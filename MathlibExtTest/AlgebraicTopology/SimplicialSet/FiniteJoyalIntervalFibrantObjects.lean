/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalFibrantObjects

/-!
# Finite Joyal Interval Fibrant Objects
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed
  SSet SSet.joyalInterval
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalFibrantObjects

variable {X : SSet.{u}}

/-- The forward criterion supplies native inner lifting for a complete
prescribed square, without an ambient model instance. -/
theorem innerSquareFromNaive (hX : auxiliaryNaiveFibrantObjects X)
    (n : ℕ) (k : Fin (n + 1)) (h0 : 0 < k) (hn : k < Fin.last n)
    (a : (Λ[n, k] : SSet.{u}) ⟶ X) (c : Δ[n] ⟶ ⊤_ SSet.{u})
    (sq : CommSq a Λ[n, k].ι (terminal.from X) c) :
    ∃ g : Δ[n] ⟶ X, Λ[n, k].ι ≫ g = a ∧ g ≫ terminal.from X = c := by
  have : Quasicategory X := (auxiliaryNaiveFibrantObjects_iff X).mp hX
  have : HasLiftingProperty Λ[n, k].ι (terminal.from X) :=
    (mem_innerFibrations (terminal.from X)) _ (horn_ι_mem_innerHornInclusions h0 hn)
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

/-- The reverse criterion lifts against every actual endpoint-corner
generator, retaining both equations of the whole prescribed square. -/
theorem endpointCornerSquare [Quasicategory X] (n : ℕ) (ε : Fin 2)
    (a : pushout ∂Δ[n].ι ((productPrecylinder.app (∂Δ[n] : SSet.{u})).endpoint ε) ⟶ X)
    (c : joyalInterval ⊗ Δ[n] ⟶ ⊤_ SSet.{u})
    (sq : CommSq a (productPrecylinder.{u}.endpointCorner ∂Δ[n].ι ε) (terminal.from X) c) :
    ∃ g : joyalInterval ⊗ Δ[n] ⟶ X,
      productPrecylinder.{u}.endpointCorner ∂Δ[n].ι ε ≫ g = a ∧ g ≫ terminal.from X = c := by
  have hX : auxiliaryNaiveFibrantObjects X :=
    (auxiliaryNaiveFibrantObjects_iff X).mpr inferInstance
  change auxiliaryNaiveFibrations (terminal.from X) at hX
  rw [auxiliaryNaiveFibrations_eq_generatorRlp] at hX
  have hp : HasLiftingProperty (productPrecylinder.{u}.endpointCorner ∂Δ[n].ι ε)
      (terminal.from X) := hX _ (auxiliaryGenerators.endpointCorner_mem n ε)
  have : sq.HasLift := hp.sq_hasLift sq
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

/-- The standard one-simplex is an auxiliary naive fibrant object. -/
theorem deltaOneNaive : auxiliaryNaiveFibrantObjects (Δ[1] : SSet.{u}) := by
  rw [auxiliaryNaiveFibrantObjects_eq_quasicategories]
  infer_instance

/-- A concrete dimension-zero corner square into the standard one-simplex
uses the actual specified pushout arrow, for either endpoint. -/
theorem boundaryZeroSquare (ε : Fin 2)
    (a : pushout ∂Δ[0].ι ((productPrecylinder.app (∂Δ[0] : SSet.{u})).endpoint ε) ⟶ Δ[1])
    (c : joyalInterval ⊗ Δ[0] ⟶ ⊤_ SSet.{u})
    (sq : CommSq a (productPrecylinder.{u}.endpointCorner ∂Δ[0].ι ε)
      (terminal.from (Δ[1] : SSet.{u})) c) :
    ∃ g : joyalInterval ⊗ Δ[0] ⟶ (Δ[1] : SSet.{u}),
      productPrecylinder.{u}.endpointCorner ∂Δ[0].ι ε ≫ g = a ∧
        g ≫ terminal.from (Δ[1] : SSet.{u}) = c :=
  endpointCornerSquare 0 ε a c sq

end MathlibExtTest.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalFibrantObjects
