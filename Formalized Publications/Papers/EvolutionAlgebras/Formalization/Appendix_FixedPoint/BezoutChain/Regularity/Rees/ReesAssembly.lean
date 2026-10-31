/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.KoszulComplex
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.SelfDuality
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.HomologyTransport
import Appendix_FixedPoint.BezoutChain.Regularity.Grade.GradeDepthFragment
import Appendix_FixedPoint.BezoutChain.Regularity.CohenMacaulayLink.VariableInductionCM
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.FiltrationStability
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.QuasiIsomorphismBridge
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.ReducedMasters
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.GradedSurjectionInjective
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedSurjection
import Mathlib.RingTheory.Depth.Rees
import Mathlib.RingTheory.Support
import Mathlib.Algebra.Module.Shrink
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.Algebra.MvPolynomial.Basic

/-!
# Rees assembly: Ext-vanishing to regular sequence to `DepthEqDimAt` (A6)

Step A6 of the Koszul plan: assemble the R-D3 Ext-subsingleton input below
`d` into a length-`d` regular sequence in the maximal ideal (via the Rees
backward direction), read off `grade ≥ d`, and close `DepthEqDimAt` with the
proved upper half (`grade ≤ dim`).

## Shapes
* `X := residueCat R (maximalIdeal R)` which unfolds to
  `ModuleCat.of R (Shrink.{u} (R ⧸ maximalIdeal R))`, i.e. the exact
  `ModuleCat.exists_isRegular_tfae` condition (2) instantiation
  (`Mathlib/RingTheory/Depth/Rees.lean`).
* `Y := ModuleCat.of R R` (i.e. `R_P` as a module over itself).
* `n := d` (sop length equals the Ext bound throughout).

## Contents

* (§1) `residueCat` + `residue_support_eq_zeroLocus`: the residue-field
  object and its support equation (mirrors the `suppQ` step of the Rees
  `tfae` proof).
* (§2) `exists_isRegular_of_residue_subsingleton`: Rees-backward wrapper —
  Ext-subsingletons below `d` give a length-`d` regular sequence in the
  maximal ideal (unconditional given the Ext input; side conditions
  `support`/`Finite`/`I • ⊤ < ⊤` proved inside).
* (§3) `le_grade_of_koszul_bridge`: grade lower bound, conditional-exact on
  the C1 quasi-iso bridge `(π, QuasiIso π)` (sequence/ExtComp shape) plus
  the C3 shift-side exactness `(e, hS, hS0)` (HomTransport shape).
* (§4) `depthEqDimAt_of_koszul_bridge`: `DepthEqDimAt` for `R_P`,
  conditional-exact on the same bridges plus the dimension equation
  `hdim : ↑↑d = ringKrullDim R_P`.

## References

Project (read-only):
* `Regularity/Koszul/SelfDuality.lean` (`koszulExt_subsingleton_below_of_homExact`)
  and (`koszulExt_subsingleton_below_ofSequence`).
* `Regularity/Koszul/HomologyTransport.lean` (`koszulHomCocycleExactBelow_ofSequence_of_iso`,
  `koszulHomZeroExact_ofSequence_of_iso`).
* `Regularity/Grade/GradeDepthFragment.lean` (`DepthEqDimAt`)
  (`grade_le_ringKrullDim`, upper half), (witness tooling).
* `Regularity/CohenMacaulayLink/VariableInductionCM.lean` (`maximalIdeal_smul_top_lt_top`),
  (`grade_eq_dim_of_maximal_regular`).
* `Regularity/Koszul/FiltrationStability.lean` (`isNoetherianRing_atPrime`).

Mathlib (`lean-toolchain` pins `v4.34.0`):
* `RingTheory/Depth/Rees.lean` (`ModuleCat.exists_isRegular_tfae`),
  backward direction `exists_isRegular_of_exists_subsingleton_ext`.
* `RingTheory/Support.lean` (`LinearEquiv.support_eq`)
  (`Module.support_eq_zeroLocus`).
* `RingTheory/Ideal/Colon.lean` (`Ideal.annihilator_quotient`).
* `Algebra/Module/Shrink.lean` (`Shrink.linearEquiv`).
* `RingTheory/Finiteness/Basic.lean` (`Module.Finite.self`),
  quotient instance, `equiv` theorem.
* `Logic/Small/Defs.lean` (`small_self`, `Small.{u} R` instance).

## Status

* §1 support: unconditional.
* §2 Rees wrapper: unconditional given the Ext-subsingleton input.
* §3 grade bound: conditional-exact on `[quasiIso-bridge (C1), hS/hS0 (C3)]`.
* §4 `DepthEqDimAt`: conditional-exact on the same bridges plus `hdim`.
  Partial result: the bridges close in parallel (C1+C3); this file only wires
  their exact shapes to the Rees/grade/dimension assembly.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace ReesAssembly

open CategoryTheory KoszulComplex SelfDuality HomologyTransport
open scoped Pointwise

universe u

/-! ## §1. Residue-field shapes -/

/-- The residue-field object in the exact Rees condition (2) shape:
`↧(Shrink (R ⧸ I))` as `ModuleCat.of R (Shrink.{u} (R ⧸ I))`.
A6 instantiates `I := maximalIdeal R` (and `R := R_P`).
-/
noncomputable abbrev residueCat (R : Type u) [CommRing R] (I : Ideal R) :
    ModuleCat.{u} R :=
  ModuleCat.of R (Shrink.{u} (R ⧸ I))

/-- Support of the shrunken residue field is the zero locus of `I`.
Mirrors the `suppQ` step of `ModuleCat.exists_isRegular_tfae`
(`Rees.lean`): transport along `Shrink.linearEquiv`, then
`support_eq_zeroLocus` (needs `Finite R (R ⧸ I)`, inferred via
`Finite.self` + `Finite.quotient`), then `annihilator_quotient`.
-/
theorem residue_support_eq_zeroLocus (R : Type u) [CommRing R]
    (I : Ideal R) :
    Module.support R (Shrink.{u} (R ⧸ I)) =
      PrimeSpectrum.zeroLocus I := by
  rw [(Shrink.linearEquiv R (R ⧸ I)).support_eq,
    Module.support_eq_zeroLocus, Ideal.annihilator_quotient]

/-! ## §2. Rees-backward wrapper -/

/-- Rees-backward wrapper at the maximal ideal (unconditional given the
Ext input): Ext-subsingletons below `d` for `X := residueCat`,
`Y := of R R` yield a length-`d` regular sequence in the maximal ideal.
Side conditions are proved inside: `support` (§1, definitionally the
`↥(residueCat)` form), `Finite` of the shrunken quotient (via
`Finite.equiv` + `Shrink.linearEquiv`), `Finite` of `R` (via
`Finite.self`), and `I • ⊤ < ⊤` (via
`VariableInductionCM.maximalIdeal_smul_top_lt_top`).
-/
theorem exists_isRegular_of_residue_subsingleton (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] {d : ℕ}
    (hSub : ∀ i < d, Subsingleton
      (Abelian.Ext (residueCat R (IsLocalRing.maximalIdeal R))
        (ModuleCat.of R R) i)) :
    ∃ rs : List R, rs.length = d ∧
      (∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R) ∧
      RingTheory.Sequence.IsRegular R rs := by
  have hsupp : Module.support R
      (Shrink.{u} (R ⧸ IsLocalRing.maximalIdeal R)) =
      PrimeSpectrum.zeroLocus (IsLocalRing.maximalIdeal R) :=
    residue_support_eq_zeroLocus R _
  have hsuppN : Module.support R
      ↥(residueCat R (IsLocalRing.maximalIdeal R)) =
      PrimeSpectrum.zeroLocus (IsLocalRing.maximalIdeal R) := hsupp
  have hfinN : Module.Finite R ↥(residueCat R (IsLocalRing.maximalIdeal R)) :=
    Module.Finite.equiv
      (Shrink.linearEquiv R (R ⧸ IsLocalRing.maximalIdeal R)).symm
  have hfinM : Module.Finite R ↥(ModuleCat.of R R) := Module.Finite.self R
  have hIlt : IsLocalRing.maximalIdeal R •
      (⊤ : Submodule R ↥(ModuleCat.of R R)) < ⊤ :=
    VariableInductionCM.maximalIdeal_smul_top_lt_top
  obtain ⟨rs, hlen, hmem, hreg⟩ :=
    @ModuleCat.exists_isRegular_of_exists_subsingleton_ext _ inferInstance
      inferInstance inferInstance (IsLocalRing.maximalIdeal R) d
      (ModuleCat.of R R) hfinM hIlt
      (residueCat R (IsLocalRing.maximalIdeal R)) hfinN hsuppN hSub
  exact ⟨rs, hlen, hmem, hreg⟩

/-! ## §3. Grade lower bound from the Koszul bridges -/

/-- Grade lower bound from the Koszul bridges (C1+C3 shapes, sequence form):
the C1 pair `(π, QuasiIso π)` resolves `X := residueCat` by `K(x)` with
`x : Fin d → R`, and the C3 triple `(e, hS, hS0)` supplies shift-side
exactness; HomTransport turns `(e, hS, hS0)` into the §13 Hom-exactness at
`Y := of R R`, Duality turns that plus `(π, hπ)` into Ext-subsingletons
below `d`, the §2 wrapper turns those into a length-`d` regular sequence,
and the sequence witnesses `(d : ℕ∞) ≤ grade`.

Conditional on exactly `[quasiIso-bridge (C1), hS/hS0 (C3)]`. -/
theorem le_grade_of_koszul_bridge (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R]
    {Ix : Type u} [LinearOrder Ix] {d : ℕ}
    (b : Module.Basis Ix R (Fin d → R)) (x : Fin d → R)
    (π : koszulChainComplexOfSequence x ⟶
      (ChainComplex.single₀ _).obj
        (residueCat R (IsLocalRing.maximalIdeal R)))
    (hπ : QuasiIso π)
    {S : CochainComplex (ModuleCat.{u} R) ℕ}
    (e : koszulDualComplex (koszulContractOfSequence x) ≅ S)
    (hS : ∀ i : ℕ, 1 ≤ i → i < d → S.ExactAt i)
    (hS0 : S.ExactAt 0) :
    (d : ℕ∞) ≤
      GradeDepthFragment.grade R R (IsLocalRing.maximalIdeal R) := by
  have hHom := koszulHomCocycleExactBelow_ofSequence_of_iso x e hS
  have h0 := koszulHomZeroExact_ofSequence_of_iso x e hS0
  have hSub := koszulExt_subsingleton_below_ofSequence b x π hπ hHom h0
  obtain ⟨rs, hlen, hmem, hreg⟩ :=
    exists_isRegular_of_residue_subsingleton R (fun i hi => hSub i hi)
  have hwit := GradeDepthFragment.mem_gradeSet_of_isRegular (R := R) (M := R)
    (IsLocalRing.maximalIdeal R) rs hlen hmem hreg
  exact GradeDepthFragment.le_grade_of_mem_gradeSet (R := R) (M := R)
    (IsLocalRing.maximalIdeal R) hwit

/-! ## §4. `DepthEqDimAt` assembly for `R_P` -/

/-- `DepthEqDimAt` for `R_P` from the Koszul bridges plus the dimension
equation (sequence form, exact wiring shapes): same C1+C3 inputs
as §3 with `R := Localization.AtPrime P`, `X := residueCat`,
`Y := of R_P R_P`, `n := d`, plus `hdim : ↑↑d = dim R_P`. The §2 wrapper
supplies the length-`d` regular sequence; rewriting `hdim` along its
length equation feeds `VariableInductionCM.grade_eq_dim_of_maximal_regular`
(which bundles the proved upper half `grade_le_ringKrullDim`).

Conditional on exactly `[quasiIso-bridge (C1), hS/hS0 (C3), hdim]`.
Partial result: C1+C3 close in parallel; `hdim` is the Hilbert–Serre input. -/
theorem depthEqDimAt_of_koszul_bridge (m : ℕ) (K : Type u) [Field K]
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime] {d : ℕ}
    {Ix : Type u} [LinearOrder Ix]
    (b : Module.Basis Ix (Localization.AtPrime P)
      (Fin d → Localization.AtPrime P))
    (x : Fin d → Localization.AtPrime P)
    (π : koszulChainComplexOfSequence x ⟶
      (ChainComplex.single₀ _).obj (residueCat (Localization.AtPrime P)
        (IsLocalRing.maximalIdeal (Localization.AtPrime P))))
    (hπ : QuasiIso π)
    {S : CochainComplex (ModuleCat.{u} (Localization.AtPrime P)) ℕ}
    (e : koszulDualComplex (koszulContractOfSequence x) ≅ S)
    (hS : ∀ i : ℕ, 1 ≤ i → i < d → S.ExactAt i)
    (hS0 : S.ExactAt 0)
    (hdim : ((((d : ℕ)) : ℕ∞) : WithBot ℕ∞) =
      ringKrullDim (Localization.AtPrime P)) :
    GradeDepthFragment.DepthEqDimAt m K P := by
  have hHom := koszulHomCocycleExactBelow_ofSequence_of_iso x e hS
  have h0 := koszulHomZeroExact_ofSequence_of_iso x e hS0
  have hSub := koszulExt_subsingleton_below_ofSequence b x π hπ hHom h0
  obtain ⟨rs, hlen, hmem, hreg⟩ :=
    exists_isRegular_of_residue_subsingleton (Localization.AtPrime P)
      (fun i hi => hSub i hi)
  have hdim' : ((((rs.length : ℕ)) : ℕ∞) : WithBot ℕ∞) =
      ringKrullDim (Localization.AtPrime P) := by
    rw [hlen]
    exact hdim
  exact VariableInductionCM.grade_eq_dim_of_maximal_regular hmem hreg hdim'

#print axioms residue_support_eq_zeroLocus
#print axioms exists_isRegular_of_residue_subsingleton
#print axioms le_grade_of_koszul_bridge
#print axioms depthEqDimAt_of_koszul_bridge

end ReesAssembly
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace ReesAssembly

open CategoryTheory KoszulComplex SelfDuality HomologyTransport
open scoped Pointwise

/-! ## §5. Shrink adapter: unshrunk residue field to `residueCat`

`QuasiIsomorphismBridge` resolves the unshrunk residue field
`koszulResidueField P = of (R_P ⧸ 𝔪)`, while the §2 Rees wrapper consumes
Ext input over the shrunk `residueCat R_P 𝔪 = of ↧(Shrink (R_P ⧸ 𝔪))`.
The adapter post-composes the C1 augmentation `π` with the `single₀`-map
of the `Shrink.linearEquiv` iso; `QuasiIso` transports along the composite
(`quasiIso_comp`, with the iso leg from `quasiIso_of_isIso` via
`Functor.map_isIso`). The domain is stated in the
`koszulChainComplexOfSequence` (sequence) shape, defeq to the
`koszulChainComplex (koszulContractOfSequence g)` shape C1 lies in.
-/

/-- The shrunken-vs-unshrunk residue-field iso, from `Shrink.linearEquiv`.
-/
noncomputable def residueIsoShrink (R : Type u) [CommRing R] (I : Ideal R) :
    ModuleCat.of R (R ⧸ I) ≅ residueCat R I :=
  (Shrink.linearEquiv R (R ⧸ I)).symm.toModuleIso

/-- The C1 augmentation retargeted at `residueCat`: post-compose
`koszulResiduePi` with the `single₀`-map of `residueIsoShrink`.
-/
noncomputable def residuePiShrunk (m : ℕ) (K : Type u) [Field K]
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime] (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    koszulChainComplexOfSequence g ⟶
      (ChainComplex.single₀ _).obj
        (residueCat (Localization.AtPrime P)
          (IsLocalRing.maximalIdeal (Localization.AtPrime P))) :=
  QuasiIsomorphismBridge.koszulResiduePi P d g hgen ≫
    (ChainComplex.single₀ _).map (residueIsoShrink _ _).hom

/-- `QuasiIso` of the retargeted augmentation, via
`koszulResiduePi_quasiIso` plus the iso leg.

Conditional on exactly `[hker]`. -/
theorem quasiIso_residuePiShrunk (m : ℕ) (K : Type u) [Field K]
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime] (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hker : RingHom.ker (GradedSurjection.polySurjResidue P d g hgen) = ⊥) :
    QuasiIso (residuePiShrunk m K P d g hgen) := by
  unfold residuePiShrunk
  have hπ : QuasiIso (QuasiIsomorphismBridge.koszulResiduePi P d g hgen) :=
    QuasiIsomorphismBridge.koszulResiduePi_quasiIso P d g hgen hker
  have he : QuasiIso ((ChainComplex.single₀ _).map
      (residueIsoShrink (Localization.AtPrime P)
        (IsLocalRing.maximalIdeal (Localization.AtPrime P))).hom) :=
    quasiIso_of_isIso _
  exact quasiIso_comp _ _ (hφ := hπ) (hφ' := he)

/-! ## §6. Main (`d ≥ 1`): `DepthEqDimAt` from C1 + C3 + `hdim`

Feeds the proved bridges into `depthEqDimAt_of_koszul_bridge` (§4):
C1 (`residuePiShrunk`, `quasiIso_residuePiShrunk`), C3
(`koszulShiftIsoSigned_commRing_ofSequence`, `shift_hS_of_r2Reduced`,
`shift_hS0_of_r2Reduced`), and `hdim` from
`grlift_r2_exact_reduced_full` (single-cast `ringKrullDim = d` turned
into the double-cast §4 shape by the definitional `WithBot.coe_natCast`).
-/

/-- Main (`d ≥ 1`): `DepthEqDimAt` for `R_P` from sop data plus `hker`.

Inputs: sop data `(g, hgen, hd)`, the Ext-comparison basis `b` (same
`{Ix : Type u} [LinearOrder Ix]` shape §4 consumes), `hker`, and `1 ≤ d`
(the `hS0` side condition).

Conditional on exactly `[hker]` (+ `1 ≤ d`), given sop data. -/
theorem depthEqDimAt_of_r2Reduced (m : ℕ) (K : Type u) [Field K]
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime] {d : ℕ}
    {Ix : Type u} [LinearOrder Ix]
    (b : Module.Basis Ix (Localization.AtPrime P)
      (Fin d → Localization.AtPrime P))
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hd : d = (IsLocalRing.maximalIdeal (Localization.AtPrime P)).spanFinrank)
    (hker : RingHom.ker (GradedSurjection.polySurjResidue P d g hgen) = ⊥)
    (hd1 : 1 ≤ d) :
    GradeDepthFragment.DepthEqDimAt m K P := by
  have hdim0 :=
    (ReducedMasters.grlift_r2_exact_reduced_full P d g hgen hd hker).1
  have hdim : ((((d : ℕ)) : ℕ∞) : WithBot ℕ∞) =
      ringKrullDim (Localization.AtPrime P) := by
    rw [hdim0]
    exact WithBot.coe_natCast d
  exact depthEqDimAt_of_koszul_bridge m K P b g
    (residuePiShrunk m K P d g hgen)
    (quasiIso_residuePiShrunk m K P d g hgen hker)
    (koszulShiftIsoSigned_commRing_ofSequence _ d g)
    (shift_hS_of_r2Reduced P d g hgen hker)
    (shift_hS0_of_r2Reduced P d g hgen hker hd1)
    hdim

/-! ## §7. `d = 0`: unconditional `DepthEqDimAt`

At `d = 0` the shift bridge is unavailable (`hS0` needs `1 ≤ d`), so this
goes direct: `hgen` forces the maximal ideal to `⊥`
(`hsAssemble_maximalIdeal_eq_bot_of_zero`), hence `R_P` is a field
(`IsLocalRing.isField_iff_maximalIdeal_eq`), hence `ringKrullDim R_P = 0`
(`ringKrullDim_eq_zero_of_isField`); the empty regular sequence then
closes `DepthEqDimAt` via `grade_eq_dim_of_maximal_regular`. (`hker` at
`d = 0` is independently closed by `hsAssemble_ker_eq_bot_zero`, but the
argument below does not need it.)
-/

/-- `d = 0`: `DepthEqDimAt` for `R_P`, unconditional given sop data
`(g, hgen)` (the Artinian/field case). -/
theorem depthEqDimAt_zero_of_sop (m : ℕ) (K : Type u) [Field K]
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (g : Fin 0 → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    GradeDepthFragment.DepthEqDimAt m K P := by
  have hbot :=
    GradedSurjectionInjective.hsAssemble_maximalIdeal_eq_bot_of_zero P g hgen
  have hfield : IsField (Localization.AtPrime P) :=
    IsLocalRing.isField_iff_maximalIdeal_eq.mpr hbot
  have hdim0 : ringKrullDim (Localization.AtPrime P) = 0 :=
    ringKrullDim_eq_zero_of_isField hfield
  have hdim : ((((List.length ([] : List (Localization.AtPrime P)) : ℕ)) : ℕ∞) :
      WithBot ℕ∞) = ringKrullDim (Localization.AtPrime P) := by
    simp only [List.length_nil]
    rw [hdim0, WithBot.coe_natCast]
    exact Nat.cast_zero
  exact VariableInductionCM.grade_eq_dim_of_maximal_regular
    (S := Localization.AtPrime P) (rs := [])
    (fun r hr => (List.not_mem_nil hr).elim)
    (RingTheory.Sequence.IsRegular.nil _ _) hdim

#print axioms residueIsoShrink
#print axioms residuePiShrunk
#print axioms quasiIso_residuePiShrunk
#print axioms depthEqDimAt_of_r2Reduced
#print axioms depthEqDimAt_zero_of_sop

end ReesAssembly
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
