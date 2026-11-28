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
# A projective-dimension criterion from bounded Ext vanishing

Let `R` be a commutative Noetherian ring that is small in module-carrier universe `v`, and fix
a probe module `A`. For natural `e` and `n`, suppose all finite free modules have vanishing
`Ext(A,-)` below `e + n`, and every finite module with that same vanishing range is
projective.

A finite module `M` with `Ext(A,M)` vanishing below `e` then has projective dimension at most
`n`. Successive finite free covers and the kernel direction of the Ext depth lemma raise the
vanishing bound until the projectivity criterion applies.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Abelian

universe u v

namespace ModuleCat

/-- Finite module projective dimension from a fixed-probe Ext criterion.

Assume `R` is commutative Noetherian and `Small.{v} R`. Fix `A : ModuleCat.{v} R`. If every
finite free module has `Ext(A,-)` vanishing below `e+n`, and every finite module with that
vanishing is categorically projective, then a finite `M` with `Ext(A,M)` vanishing below `e`
has projective dimension at most `n`. -/
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
