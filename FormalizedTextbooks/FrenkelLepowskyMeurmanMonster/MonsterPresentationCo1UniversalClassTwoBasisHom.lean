/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual coordinate involutions give exact binary homomorphisms into the source presentation. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1UniversalClassTwoBasis
public import Mathlib.Data.Finset.NoncommProd

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Each involutory source coordinate lift defines the exact homomorphism from a binary bit. -/
def co1UniversalBasisHom
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (hne : commutator Co1UniversalPresentation ≠ ⊥) (i : Fin 24) :
    Multiplicative (ZMod 2) →* Co1UniversalPresentation where
  toFun a := if a.toAdd = 0 then 1 else co1UniversalBasisLift i
  map_one' := by
    change (if (0 : ZMod 2) = 0 then 1 else _) = 1
    exact ite_eq_left rfl
  map_mul' a b := by
    have h : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide +kernel
    rcases h a.toAdd with ha | ha <;> rcases h b.toAdd with hb | hb
    all_goals
      change (if a.toAdd + b.toAdd = 0 then 1 else co1UniversalBasisLift i) =
        (if a.toAdd = 0 then 1 else co1UniversalBasisLift i) *
          (if b.toAdd = 0 then 1 else co1UniversalBasisLift i)
      simp only [ha, hb, zero_add, add_zero, ZModModule.add_self,
        show (1 : ZMod 2) ≠ 0 by decide, ite_true, ite_false,
        one_mul, mul_one, ← pow_two, co1UniversalBasisLift_square hfinite hcard hne, one_pow]

/-- Images of arbitrary bits in one actual hyperbolic half-block commute in the source group. -/
theorem co1UniversalBasisHom_half_commute
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (hne : commutator Co1UniversalPresentation ≠ ⊥) (b : Fin 2) (i j : Fin 12)
    (a c : Multiplicative (ZMod 2)) :
    Commute (co1UniversalBasisHom hfinite hcard hne (co1UniversalHalfIndex b i) a)
      (co1UniversalBasisHom hfinite hcard hne (co1UniversalHalfIndex b j) c) := by
  change Commute (if a.toAdd = 0 then 1 else _)
    (if c.toAdd = 0 then 1 else _)
  split_ifs
  · exact Commute.refl 1
  · exact Commute.one_left _
  · exact Commute.one_right _
  · exact co1UniversalBasisLift_half_commute hfinite hcard hne b i j

/-- A binary coordinate bit is retained exactly by the source coordinate homomorphism. -/
theorem co1UniversalBasisHom_image
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (hne : commutator Co1UniversalPresentation ≠ ⊥) (i : Fin 24)
    (a : Multiplicative (ZMod 2)) :
    co1UniversalIntoBinary (co1UniversalBasisHom hfinite hcard hne i a) =
      Multiplicative.ofAdd (Pi.single i a.toAdd) := by
  have h : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide +kernel
  change co1UniversalIntoBinary (if a.toAdd = 0 then 1 else co1UniversalBasisLift i) = _
  rcases h a.toAdd with ha | ha
  · simp only [ha, ite_true, map_one, Pi.single_zero]
    rfl
  · simp only [ha, show (1 : ZMod 2) ≠ 0 by decide, ite_false]
    exact co1UniversalBasisLift_image i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
