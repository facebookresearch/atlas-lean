/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Algebra.Homology.Ext.VanishingBelow
public import Mathlib.Algebra.Category.ModuleCat.Ext.Finite
public import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension

/-!
# Projective-dimension bounds from bounded Ext vanishing

A finite module admits successive finite free covers over a Noetherian ring.
If finite free middle terms have a fixed bounded-Ext range, and finite modules
at the top of that range are projective, iterating the kernel direction of the
Ext depth lemma gives a projective-dimension bound.

## Main declaration

* `ModuleCat.hasProjectiveDimensionLE_of_vanishesBelow_add`
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Abelian

universe u v

namespace ModuleCat

/-- Iterating finite free covers converts bounded Ext vanishing below `e`
into a projective-dimension bound `n`, provided finite free middle terms
vanish below the fixed top bound `e + n` and finite modules attaining that
top bound are projective. -/
theorem hasProjectiveDimensionLE_of_vanishesBelow_add
    {R : Type u} [CommRing R] [IsNoetherianRing R] [Small.{v} R]
    (A : ModuleCat.{v} R)
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (e n : ℕ)
    (hfree : ∀ (P : Type v) [AddCommGroup P] [Module R P]
      [Module.Free R P] [Module.Finite R P],
      Ext.VanishesBelow A (ModuleCat.of R P) (e + n))
    (htop : ∀ (N : Type v) [AddCommGroup N] [Module R N]
      [Module.Finite R N],
      Ext.VanishesBelow A (ModuleCat.of R N) (e + n) →
        Projective (ModuleCat.of R N))
    (hM : Ext.VanishesBelow A (ModuleCat.of R M) e) :
    HasProjectiveDimensionLE (ModuleCat.of R M) n := by
  induction n generalizing e M with
  | zero =>
      apply (projective_iff_hasProjectiveDimensionLE_zero _).mp
      apply htop M
      simpa only [Nat.add_zero] using hM
  | succ n ih =>
      obtain ⟨P, _, _, _, _, f, hf⟩ :=
        Module.exists_finite_presentation R M
      let S : ShortComplex (ModuleCat.{v} R) := f.shortComplexKer
      have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer hf
      have hPdepth : Ext.VanishesBelow A S.X₂ (e + 1) := by
        apply (hfree P).mono
        omega
      have hKdepth : Ext.VanishesBelow A S.X₁ (e + 1) :=
        Ext.VanishesBelow.of_shortExact_X₁ hS A e hPdepth hM
      have hKpd : HasProjectiveDimensionLE S.X₁ n := by
        apply ih (e := e + 1)
        · intro P _ _ _ _
          simpa only [Nat.add_assoc, Nat.add_comm 1 n] using hfree P
        · intro N _ _ _ hN
          apply htop N
          simpa only [Nat.add_assoc, Nat.add_comm 1 n] using hN
        · exact hKdepth
      have hPproj : Projective S.X₂ := by
        change Projective (ModuleCat.of R P)
        infer_instance
      exact (hS.hasProjectiveDimensionLT_X₃_iff n hPproj).mpr hKpd

end ModuleCat
