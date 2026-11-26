/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.MotivicPowerDescentModels
public import MathlibExt.AlgebraicGeometry.MotivicBocksteinModels
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Data.ZMod.Basic

/-!
# Short exactness of the mod-ℓ coefficient sequence

For a prime `ℓ`, the mod-`ℓ` coefficient sequence `modSequence`, namely
`0 → ZMod ℓ → ZMod (ℓ * ℓ) → ZMod ℓ → 0` with first map `n ↦ ℓ * n` and second
map reduction modulo `ℓ`, is short exact (`modCoefficientSequenceExact`).
Exactness, injectivity and surjectivity are proved for the underlying `ZMod`
maps and transferred to the lifted coefficient modules with
`ModuleCat.shortComplex_shortExact`.

Source: Voevodsky, *Reduced power operations in motivic cohomology*, arXiv:math/0107109v1,
Section 8, p. 32, where the mod-`ℓ` coefficient sequence is stated at the opening of the section.
-/

@[expose] public section

namespace WantedExt.AlgebraicGeometry.MotivicPowerCycleSourcesWanted

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open FiniteTransferCycleModels FiniteTransferProductModels MotivicStandardSchemes
open MotivicFinitePermutationModels MotivicPermutationBundleModels
open MotivicFinitePowerCycles MotivicPowerQuotientModels MotivicPowerDescentModels
open MotivicBocksteinModels PointedMotivicModels ReducedMotivicCohomologyModels
open NisnevichTransferModels EffectiveMotivicComplexModels MotivicTorusClassModels

/-- The injection sends an integer class `x` to `ℓ * x` in `ZMod (ℓ * ℓ)`. -/
private theorem modInjectionAdd_intCast (ell : ℕ) (x : ℤ) :
    modInjectionAdd ell (x : ZMod ell) = (((ell : ℤ) * x : ℤ) : ZMod (ell * ell)) := by
  rw [modInjectionAdd, ZMod.lift_coe]
  change (ell : ℤ) • ((x : ℤ) : ZMod (ell * ell)) = _
  rw [zsmul_eq_mul, ← Int.cast_mul]

/-- Reduction sends an integer class `b` to itself viewed modulo `ℓ`. -/
private theorem castHom_intCast (ell : ℕ) (b : ℤ) :
    (ZMod.castHom (dvd_mul_right ell ell) (ZMod ell)).toAddMonoidHom
      (b : ZMod (ell * ell)) = (b : ZMod ell) := by
  change (ZMod.castHom (dvd_mul_right ell ell) (ZMod ell)) _ = _
  exact map_intCast _ _

/-- For prime `ℓ`, multiplication by `ℓ` is injective from `ZMod ℓ` to
`ZMod (ℓ * ℓ)`. -/
private theorem injective_modInjectionAdd (ell : ℕ) [Fact ell.Prime] :
    Function.Injective (modInjectionAdd ell) := by
  have hprime : ell.Prime := Fact.out
  have hne : (ell : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hprime.ne_zero
  intro a b hab
  obtain ⟨x, rfl⟩ := ZMod.intCast_surjective a
  obtain ⟨y, rfl⟩ := ZMod.intCast_surjective b
  rw [modInjectionAdd_intCast, modInjectionAdd_intCast] at hab
  rw [ZMod.intCast_eq_intCast_iff, Int.modEq_iff_dvd] at hab
  rw [ZMod.intCast_eq_intCast_iff, Int.modEq_iff_dvd]
  have hsub : (ell : ℤ) * y - (ell : ℤ) * x = (ell : ℤ) * (y - x) := by ring
  rw [Nat.cast_mul, hsub, mul_dvd_mul_iff_left hne] at hab
  exact hab

/-- Reduction modulo `ℓ` is surjective. -/
private theorem surjective_castHomAdd (ell : ℕ) :
    Function.Surjective
      ⇑(ZMod.castHom (dvd_mul_right ell ell) (ZMod ell)).toAddMonoidHom :=
  ZMod.castHom_surjective (dvd_mul_right ell ell)

/-- The pair is exact: the kernel of reduction is the image of multiplication
by `ℓ`. -/
private theorem exact_pair (ell : ℕ) :
    Function.Exact ⇑(modInjectionAdd ell)
      ⇑(ZMod.castHom (dvd_mul_right ell ell) (ZMod ell)).toAddMonoidHom := by
  intro x
  constructor
  · intro hx
    obtain ⟨b, rfl⟩ := ZMod.intCast_surjective x
    rw [castHom_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd] at hx
    obtain ⟨c, hc⟩ := hx
    refine ⟨(c : ZMod ell), ?_⟩
    rw [modInjectionAdd_intCast, hc]
  · rintro ⟨a, ha⟩
    rw [← ha]
    obtain ⟨a', rfl⟩ := ZMod.intCast_surjective a
    rw [modInjectionAdd_intCast, castHom_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact dvd_mul_right _ _

/-- The lifted injection acts as `ULift.up` of the `ZMod` injection. -/
private theorem modInjection_apply (ell : ℕ) (v : ULift.{1} (ZMod ell)) :
    modInjection ell v = ULift.up (modInjectionAdd ell v.down) :=
  rfl

/-- The lifted reduction acts as `ULift.up` of the `ZMod` reduction. -/
private theorem modReduction_apply (ell : ℕ) (v : ULift.{1} (ZMod (ell * ell))) :
    modReduction ell v =
      ULift.up ((ZMod.castHom (dvd_mul_right ell ell) (ZMod ell)).toAddMonoidHom v.down) :=
  rfl

/-- The lifted injection is injective for prime `ℓ`. -/
private theorem injective_modInjection (ell : ℕ) [Fact ell.Prime] :
    Function.Injective ⇑(modInjection ell) := by
  intro a b hab
  rw [modInjection_apply, modInjection_apply] at hab
  have hdown : modInjectionAdd ell a.down = modInjectionAdd ell b.down := by
    have h2 := congrArg ULift.down hab
    simpa [ULift.down_up] using h2
  have hbase := injective_modInjectionAdd ell hdown
  have hup := congrArg ULift.up hbase
  rwa [ULift.up_down, ULift.up_down] at hup

/-- The lifted reduction is surjective. -/
private theorem surjective_modReduction (ell : ℕ) :
    Function.Surjective ⇑(modReduction ell) := by
  intro b
  obtain ⟨a, ha⟩ := surjective_castHomAdd ell b.down
  refine ⟨ULift.up a, ?_⟩
  rw [modReduction_apply, ULift.down_up, ha, ULift.up_down]

/-- The lifted pair is exact. -/
private theorem exact_pair_lifted (ell : ℕ) :
    Function.Exact ⇑(modInjection ell) ⇑(modReduction ell) := by
  intro x
  constructor
  · intro hx
    rw [modReduction_apply] at hx
    have hx0 :
        (ZMod.castHom (dvd_mul_right ell ell) (ZMod ell)).toAddMonoidHom x.down = 0 := by
      have hup0 : (0 : ULift.{1} (ZMod ell)) = ULift.up 0 := rfl
      rw [hup0] at hx
      have h2 := congrArg ULift.down hx
      simpa [ULift.down_up] using h2
    obtain ⟨a, ha⟩ := (exact_pair ell x.down).mp hx0
    refine ⟨ULift.up a, ?_⟩
    rw [modInjection_apply, ULift.down_up, ha, ULift.up_down]
  · rintro ⟨a, ha⟩
    rw [← ha, modInjection_apply, modReduction_apply, ULift.down_up]
    have hGF := (exact_pair ell (modInjectionAdd ell a.down)).mpr ⟨a.down, rfl⟩
    rw [hGF]
    rfl

/-- For a prime ℓ, the sequence of $\mathbb{Z}$-modules
$0 \to \mathbb{Z}/\ell \to \mathbb{Z}/\ell^2 \to \mathbb{Z}/\ell \to 0$, with first map
$n \mapsto \ell n$ and second map reduction modulo ℓ, is short exact. -/
theorem modCoefficientSequenceExact (ell : ℕ) [Fact ell.Prime] :
  (modSequence ell).ShortExact :=
  ModuleCat.shortComplex_shortExact _ (exact_pair_lifted ell)
    (injective_modInjection ell) (surjective_modReduction ell)

end WantedExt.AlgebraicGeometry.MotivicPowerCycleSourcesWanted
