/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.AssociatedPrimes.IschebeckAssembly
import Appendix_FixedPoint.AssociatedPrimes.AssociatedPrimeMap
import Appendix_FixedPoint.AssociatedPrimes.QuotientDimensionFacts
import Appendix_FixedPoint.BezoutChain.Regularity.Grade.GradeDepthFragment
import Appendix_FixedPoint.BezoutChain.Regularity.CohenMacaulayLink.CMPositiveDimHasDepth
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Finiteness.Basic

/-!
# UnmixedSqueeze: 17.2 unmixed step + 17.3(i) sup squeeze (D8)

The D8 package: `l_unmixed_step` (Matsumura 17.2 — every associated
prime has quotient dimension at least the grade, via AssociatedPrimeMap's Ext⁰ rung
against IschebeckAssembly's IschebeckAssembly vanishing at `i = 0`), the
`annihilator_self_eq_bot` micro-bridge, `squeeze_sup_over_ass`
(`dim S` as the sup over associated primes, via the proved L1
quotient-sup form), and `l_no_embedded` (17.3(i): at CM every
associated prime has full quotient dimension — the MinimalPrimesAtCM interface).

`[IsAlgClosed]`: not required and not used — everything here is over a
general commutative Noetherian (local) ring with no field hypotheses.

Proof constraints (squeeze only): `Q` appears only as the first variable
of `Hom`/`Ext` (Lemma 1) — no quotient-descent, no `S/(x)`; and no
`grade = height` or C3a-shaped fact anywhere — allowed height/dim facts
are definitional/monotone only (the external pins + L1 sup +
`le_antisymm`). `hCM` is an assumed hypothesis being unfolded, never a
proved equation.
-/


namespace AssociatedPrimes.UnmixedSqueeze

open CategoryTheory Abelian

universe v

/-- 17.2 `L-unmixed-step`: the grade is at most the quotient dimension
at every associated prime. Contrapositive of `l_ischebeck` at `i = 0`
against `assExt_zero_ne`; the `∞` case closes by `le_top`. -/
theorem l_unmixed_step
    {S : Type v} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    [Small.{v} S]
    {Q : Ideal S} (hQ : IsAssociatedPrime Q S) :
    ((EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradeDepthFragment.grade S S
      (IsLocalRing.maximalIdeal S) : ℕ∞) : WithBot ℕ∞)
      ≤ ringKrullDim (S ⧸ Q) := by
  have hQprime : Q.IsPrime := IsAssociatedPrime.isPrime hQ
  by_cases htop : ringKrullDim (S ⧸ Q) = ⊤
  · rw [htop]
    exact le_top
  · have hfinQ : ringKrullDim (S ⧸ Q) < ⊤ :=
      lt_top_iff_ne_top.mpr htop
    have hann : (⊤ : Submodule S
        ((ModuleCat.of S (S ⧸ Q)) : Type v)).annihilator = Q :=
      @AssociatedPrimes.IschebeckAssembly.annihilator_quot_primeQuot S _ Q hQprime
    have hfinQ' : ringKrullDim
        (S ⧸ (⊤ : Submodule S
          ((ModuleCat.of S (S ⧸ Q)) : Type v)).annihilator) < ⊤ := by
      rw [hann]
      exact hfinQ
    have hfinQmod : Module.Finite S (S ⧸ Q) := inferInstance
    have hfinSmod : Module.Finite S S := inferInstance
    have hntS : Nontrivial S := inferInstance
    have hfinN : Module.Finite S
        ((ModuleCat.of S (S ⧸ Q)) : Type v) := hfinQmod
    have hfinM : Module.Finite S ((ModuleCat.of S S) : Type v) :=
      hfinSmod
    have hntM : Nontrivial ((ModuleCat.of S S) : Type v) := hntS
    by_contra hcon
    rw [not_le] at hcon
    have hcon' : ringKrullDim
        (S ⧸ (⊤ : Submodule S
          ((ModuleCat.of S (S ⧸ Q)) : Type v)).annihilator) <
        ((EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradeDepthFragment.grade S S
          (IsLocalRing.maximalIdeal S) : ℕ∞) : WithBot ℕ∞) := by
      rw [hann]
      exact hcon
    have hbound : (((0 : ℕ)) : WithBot ℕ∞) +
        ringKrullDim
          (S ⧸ (⊤ : Submodule S
            ((ModuleCat.of S (S ⧸ Q)) : Type v)).annihilator) <
        ((EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradeDepthFragment.grade S S
          (IsLocalRing.maximalIdeal S) : ℕ∞) : WithBot ℕ∞) := by
      simpa using hcon'
    have hvan := @AssociatedPrimes.IschebeckAssembly.l_ischebeck S _ _ _ _
      (ModuleCat.of S S) (ModuleCat.of S (S ⧸ Q)) hfinM hfinN hntM _
      hfinQ' 0 hbound
    obtain ⟨e, he⟩ := assExt_zero_ne (M := ModuleCat.of S S) hQ
    exact he (Subsingleton.elim e 0)

/-- Micro-bridge: the annihilator of `S`-as-module-over-itself is `⊥`.
Feeds the `minimalPrimes`-over-`ann` pin in the squeeze. -/
theorem annihilator_self_eq_bot (S : Type v) [CommRing S] :
    Module.annihilator S S = ⊥ :=
  Module.annihilator_eq_bot.mpr inferInstance

/-- 17.3(i) sup packaging: `dim S` is the sup of quotient dimensions
over associated primes. Lowers via the minimal-prime/associated-prime
pin plus the micro-bridge; uppers via `ringKrullDim_quotient_le`. -/
theorem squeeze_sup_over_ass
    {S : Type v} [CommRing S] [IsNoetherianRing S] :
    ringKrullDim S =
      ⨆ p : { p : Ideal S // IsAssociatedPrime p S },
        ringKrullDim (S ⧸ p.1) := by
  rw [AssociatedPrimes.QuotientDimensionFacts.ringKrullDim_eq_sup_quotient_minimalPrimes S]
  apply le_antisymm
  · refine iSup_le fun p => ?_
    have hmin : (Module.annihilator S S).minimalPrimes
        = minimalPrimes S := by
      rw [annihilator_self_eq_bot]
    have hmem : p.1 ∈ (Module.annihilator S S).minimalPrimes := by
      rw [hmin]
      exact p.2
    have hass : IsAssociatedPrime p.1 S :=
      AssociatedPrimes.mem_iff.mp
        (Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes
          S S hmem)
    exact le_iSup (fun q : { p : Ideal S // IsAssociatedPrime p S } =>
      ringKrullDim (S ⧸ q.1)) ⟨p.1, hass⟩
  · refine iSup_le fun q => ?_
    calc ringKrullDim (S ⧸ q.1) ≤ ringKrullDim S :=
          ringKrullDim_quotient_le q.1
      _ = ⨆ p : { p : Ideal S // p ∈ minimalPrimes S },
            ringKrullDim (S ⧸ p.1) :=
          AssociatedPrimes.QuotientDimensionFacts.ringKrullDim_eq_sup_quotient_minimalPrimes S

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GapGradeSeq


/-- 17.3(i) `L-no-embedded` (the MinimalPrimesAtCM interface): at CM every
associated prime has full quotient dimension. The equality closes via
17.2 + the `hCM` rewrite + quotient-le; `_hkfin` is the pinned
finiteness witness, not a load-bearing rewrite. -/
theorem l_no_embedded
    {S : Type v} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    [Small.{v} S]
    (hCM : EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.CMPositiveDimHasDepth.IsCM S)
    (hfin : ringKrullDim S < ⊤)
    {Q : Ideal S} (hQ : IsAssociatedPrime Q S) :
    ringKrullDim (S ⧸ Q) = ringKrullDim S := by
  have _hkfin :
      ((EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradeDepthFragment.grade S S
        (IsLocalRing.maximalIdeal S) : ℕ∞) : WithBot ℕ∞) < ⊤ :=
    coe_grade_lt_top_of_isCM_of_dim_lt_top
      S hCM hfin
  have hke : ((EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradeDepthFragment.grade S S
      (IsLocalRing.maximalIdeal S) : ℕ∞) : WithBot ℕ∞)
      = ringKrullDim S := hCM
  have hlower : ringKrullDim S ≤ ringKrullDim (S ⧸ Q) := by
    rw [← hke]
    exact l_unmixed_step hQ
  have hupper : ringKrullDim (S ⧸ Q) ≤ ringKrullDim S :=
    ringKrullDim_quotient_le Q
  exact le_antisymm hupper hlower

end AssociatedPrimes.UnmixedSqueeze
