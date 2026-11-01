/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.AssociatedPrimes.UnmixedSqueeze
import Appendix_FixedPoint.AssociatedPrimes.QuotientDimensionFacts
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.PrimeAvoidance
import Appendix_FixedPoint.BezoutChain.Regularity.CohenMacaulayLink.CMPositiveDimHasDepth
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.Data.ENat.SuccOrder

/-!
# MinimalPrimesAtCM: associated primes are minimal at CM + Step 0 (D9)

Closes `AssociatedPrimes` (Prop-binder form): over a Noetherian local
ring of finite Krull dimension, at CM every prime all of whose elements
are zerodivisors has height zero.

* `associatedPrime_height_eq_zero` (finale): `Q ∈ Ass(S)` ⟹ `ht Q = 0`,
  via proved `UnmixedSqueeze.l_no_embedded` (`dim S⧸Q = dim S`) against proved
  `QuotientDimensionFacts.ringKrullDim_quotient_strictDrop` along a minimal prime
  `P' ≤ Q` ascended from `⊥`, closed by the `d < ⊤` fence (plus `d ≠ ⊥`
  via `krullDim_nonneg`).
* `gapBaseFin` (Step 0 + finale): `p` all-zerodivisors ⟹ `p ≤ Q` for some
  `Q ∈ Ass(S)` (contrapositive of the one-step PrimeAvoidance feed
  `exists_isSMulRegular_mem_of_forall_not_le_ass`) ⟹ `ht p ≤ ht Q = 0`.

`[IsAlgClosed]`: not required and not used — everything here is over a
general commutative Noetherian local ring with no field hypotheses.

Proof constraints (finale only): chain/height only — no quotient-descent
(`P'` ascends from `⊥` via `exists_minimalPrimes_le`; `S ⧸ Q`/`S ⧸ P'`
appear only as arguments to proved dim lemmas), and no `grade = height`
or C3a-shaped inputs (allowed height/dim facts are
`height_eq_zero_iff`, `height_mono`, proved `strictDrop`/`l_no_embedded`,
`ringKrullDim_quotient_le`). `hCM` is an assumed hypothesis consumed
opaquely by `l_no_embedded`, never unfolded or proved.
-/


namespace AssociatedPrimes.MinimalPrimesAtCM

universe v

/-- MinimalPrimesAtCM: at CM, every associated prime has height zero. If `Q` were
non-minimal, a minimal prime `P' < Q` would force `d + 1 ≤ d` for
`d := dim S⧸Q`, against the `d < ⊤` fence (and `d ≠ ⊥`). -/
theorem associatedPrime_height_eq_zero
    {S : Type v} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    [Small.{v} S]
    (hCM : EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.CMPositiveDimHasDepth.IsCM S)
    (hfin : ringKrullDim S < ⊤)
    {Q : Ideal S} (hQ : IsAssociatedPrime Q S) :
    Q.height = 0 := by
  have hQprime : Q.IsPrime := IsAssociatedPrime.isPrime hQ
  have hd : ringKrullDim (S ⧸ Q) = ringKrullDim S :=
    AssociatedPrimes.UnmixedSqueeze.l_no_embedded hCM hfin hQ
  suffices hQmin : Q ∈ minimalPrimes S from
    (@Ideal.height_eq_zero_iff S _ Q hQprime).mpr hQmin
  by_contra hQnonmin
  obtain ⟨P', hP'min, hle⟩ :=
    @Ideal.exists_minimalPrimes_le S _ ⊥ Q hQprime bot_le
  have hP'S : P' ∈ minimalPrimes S := hP'min
  have hP'prime : P'.IsPrime := IsMinimalPrime.isPrime hP'S
  have hlt : P' < Q := lt_of_le_of_ne hle (fun heq => hQnonmin (heq ▸ hP'S))
  have hdrop : ringKrullDim (S ⧸ Q) + 1 ≤ ringKrullDim (S ⧸ P') :=
    @AssociatedPrimes.QuotientDimensionFacts.ringKrullDim_quotient_strictDrop S _ P' Q hP'prime
      hQprime hlt
  have hle_dim : ringKrullDim (S ⧸ P') ≤ ringKrullDim S :=
    ringKrullDim_quotient_le P'
  have hcontra : ringKrullDim (S ⧸ Q) + 1 ≤ ringKrullDim (S ⧸ Q) :=
    calc ringKrullDim (S ⧸ Q) + 1 ≤ ringKrullDim (S ⧸ P') := hdrop
      _ ≤ ringKrullDim S := hle_dim
      _ = ringKrullDim (S ⧸ Q) := hd.symm
  have hfinQ : ringKrullDim (S ⧸ Q) < ⊤ := by
    rw [hd]
    exact hfin
  have hne : Nonempty (PrimeSpectrum (S ⧸ Q)) :=
    ⟨(AssociatedPrimes.QuotientDimensionFacts.specQuotient S Q).symm
      ⟨⟨Q, hQprime⟩, (le_rfl : (Q : Ideal S) ≤ Q)⟩⟩
  have h0le : (0 : WithBot ℕ∞) ≤ ringKrullDim (S ⧸ Q) :=
    @Order.krullDim_nonneg (PrimeSpectrum (S ⧸ Q)) _ hne
  have hbot0 : (⊥ : WithBot ℕ∞) < 0 := WithBot.bot_lt_coe _
  have hne_bot : ringKrullDim (S ⧸ Q) ≠ ⊥ :=
    ne_of_gt (lt_of_lt_of_le hbot0 h0le)
  obtain ⟨x, hx⟩ := WithBot.ne_bot_iff_exists.mp hne_bot
  rw [← hx] at hcontra hfinQ
  rw [← WithBot.coe_one, ← WithBot.coe_add, WithBot.coe_le_coe] at hcontra
  have hxne : x ≠ ⊤ := by
    rintro rfl
    rw [WithBot.coe_top] at hfinQ
    exact lt_irrefl _ hfinQ
  exact lt_irrefl _ ((ENat.add_one_le_iff hxne).mp hcontra)

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.PrimeAvoidance


/-- Step 0 + finale (`AssociatedPrimes`, §1 Prop-binder shape): a prime
all of whose elements are zerodivisors sits inside some associated
prime, hence has height zero. -/
theorem gapBaseFin
    {S : Type v} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    [Small.{v} S]
    (p : Ideal S) [p.IsPrime]
    (hfin : ringKrullDim S < ⊤)
    (hCM : EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.CMPositiveDimHasDepth.IsCM S)
    (hall : ∀ y ∈ p, ¬ IsSMulRegular S y) :
    p.height = 0 := by
  have hex : ∃ Q ∈ associatedPrimes S S, p ≤ Q := by
    by_contra hcon
    push Not at hcon
    obtain ⟨x, hxI, hxreg⟩ :=
      exists_isSMulRegular_mem_of_forall_not_le_ass
        p hcon
    exact (hall x hxI) hxreg
  obtain ⟨Q, hQmem, hpQ⟩ := hex
  have hQ : IsAssociatedPrime Q S := AssociatedPrimes.mem_iff.mp hQmem
  have hle : p.height ≤ Q.height := Ideal.height_mono hpQ
  have hQ0 : Q.height = 0 := associatedPrime_height_eq_zero hCM hfin hQ
  exact le_antisymm (hle.trans_eq hQ0) zero_le

end AssociatedPrimes.MinimalPrimesAtCM
