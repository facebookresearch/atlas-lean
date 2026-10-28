/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The source square map is the actual Conway quadratic form for a nontrivial commutator. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1UniversalClassTwoSquareProduct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1BinaryInvariantQuadratics

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The source squares, with their proved source commutator companion, form a quadratic map. -/
def co1UniversalSquareQuadratic
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2) :
    QuadraticMap (ZMod 2) (Fin 24 → ZMod 2) (ZMod 2) where
  toFun := co1UniversalSquareCoefficient
  toFun_smul a v := by
    have h : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide +kernel
    rcases h a with ha | ha
    · simp only [ha, zero_smul, zero_mul,
        co1UniversalSquareCoefficient_zero hfinite hcard]
    · simp only [ha, one_smul, one_mul]
  exists_companion' := ⟨(co1UniversalCommutatorBilin hfinite hcard).flip,
    co1UniversalSquareCoefficient_add hfinite hcard⟩

/-- This quadratic map is invariant under the exact action on the original source presentation. -/
theorem co1UniversalSquareQuadratic_action
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (g : Co1) (v : Fin 24 → ZMod 2) :
    co1UniversalSquareQuadratic hfinite hcard (co1BinaryAction g v) =
      co1UniversalSquareQuadratic hfinite hcard v :=
  co1UniversalSquareCoefficient_action hfinite hcard g v

/-- A nontrivial bounded source commutator forces the actual nonzero Conway square form. -/
theorem co1UniversalSquareQuadratic_eq_squareQuad
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (hne : commutator Co1UniversalPresentation ≠ ⊥) :
    co1UniversalSquareQuadratic hfinite hcard = squareQuad := by
  rcases co1BinaryAction_invariant_quadratic_zero_or_squareQuad
      (co1UniversalSquareQuadratic hfinite hcard)
      (co1UniversalSquareQuadratic_action hfinite hcard) with hz | hs
  · obtain ⟨v, hv⟩ := co1UniversalSquareCoefficient_nonzero hfinite hcard hne
    exact False.elim (hv (DFunLike.congr_fun hz v))
  · exact hs

/-- The source square coefficient agrees on every actual binary coordinate with its square form. -/
theorem co1UniversalSquareCoefficient_eq_squareQuad
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (hne : commutator Co1UniversalPresentation ≠ ⊥) (v : Fin 24 → ZMod 2) :
    co1UniversalSquareCoefficient v = squareQuad v :=
  DFunLike.congr_fun (co1UniversalSquareQuadratic_eq_squareQuad hfinite hcard hne) v

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
