/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.DiscreteValuationRing.AdjoinSeparableLocalization
import Mathlib.Algebra.Field.ZMod

@[expose] public section

universe u v

/-- Exact-source consumer, with the original binders and explicit universes. -/
private theorem exactSource
    {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {M : Type v} [CommRing M] [IsDomain M] [Algebra O M]
    (hinj : Function.Injective (algebraMap O M))
    (e : M) (f : Polynomial O) (hf : f.Monic) (hfe : Polynomial.aeval e f = 0)
    (hsep : (f.map (IsLocalRing.residue O)).Separable)
    (P : Ideal ↥(Algebra.adjoin O ({e} : Set M))) [P.IsPrime]
    (hP : (IsLocalRing.maximalIdeal O).map
      (algebraMap O ↥(Algebra.adjoin O ({e} : Set M))) ≤ P) :
    IsDiscreteValuationRing (Localization.AtPrime P) ∧
      IsLocalRing.maximalIdeal (Localization.AtPrime P) =
        ((IsLocalRing.maximalIdeal O).map
          (algebraMap O ↥(Algebra.adjoin O ({e} : Set M)))).map
          (algebraMap ↥(Algebra.adjoin O ({e} : Set M)) (Localization.AtPrime P)) :=
  Algebra.adjoin.isDiscreteValuationRing_localization_and_maximalIdeal_eq_of_separable_map
    hinj e f hf hfe hsep P hP

/-- Boundary: separability of the reduction is not automatic. In residue
characteristic `2`, the reduction `X ^ 2 - 1` is not separable, so a monic
polynomial reducing to it is excluded by the separability hypothesis. -/
example : ¬ (Polynomial.X ^ 2 - 1 : Polynomial (ZMod 2)).Separable := by
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  intro hs
  have hs' : (Polynomial.X ^ 2 - Polynomial.C 1 : Polynomial (ZMod 2)).Separable := by
    simpa only [Polynomial.C_1] using hs
  have h2 := (Polynomial.X_pow_sub_C_separable_iff (F := ZMod 2) (n := 2) (x := 1)
    (by norm_num) one_ne_zero).mp hs'
  exact h2 (ZMod.natCast_self 2)
