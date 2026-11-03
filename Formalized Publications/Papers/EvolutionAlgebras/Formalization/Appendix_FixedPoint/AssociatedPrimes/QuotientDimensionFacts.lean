/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.Order.KrullDimension
import Mathlib.Order.RelSeries
import Mathlib.Data.ENat.Lattice
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Finiteness.Defs

/-!
# Dimension facts for the GapBase finite-dimensional close (D1)

Elementary Krull-dimension package consumed by the dim-drop legs:
Spec-quotient correspondence, strict quotient drop, dimension as a
supremum over minimal primes (coheight and quotient forms), the dim-0
support description in the local case, quotient dimension via minimal
primes over an ideal, and the `𝔪M ≠ M` micro-split via Nakayama.

All height/dimension facts used are definitional or monotone
(`Order.coheight_add_one_le`, `Order.coheight_anti`,
`Ring.krullDimLE_zero_iff`, `ringKrullDim_quotient_le`,
`Ideal.exists_minimalPrimes_le`,
`Ideal.primeSpectrumQuotientOrderIsoZeroLocus`,
`Submodule.eq_bot_of_le_smul_of_le_jacobson_bot`); no form of
`grade = height` appears anywhere (Wall-2 N/A), and no prime is ever
descended through a quotient (Wall-1 N/A: the Spec-quotient order iso
only transports chains).

`[IsAlgClosed]`: not required and not used — every result is over a
general commutative ring with no field hypotheses at all.

Shape deviations from the design note (all forced, semantics unchanged):
* `ringKrullDim_eq_sup_minimalPrimes` uses the inside-coercion sup
  `⨆ p, ↑(coheight …)` and holds unconditionally; the outside-coercion
  reading is false for the trivial ring (`⊥` vs `↑0`), hence provided
  separately as `ringKrullDim_eq_coe_sup_minimalPrimes` under
  `[Nontrivial S]`.
* `support_eq_singleton_maximal_of_dim_zero` states the singleton in
  `PrimeSpectrum A` (the design note's `Set (Ideal A)` singleton is ill-typed
  against `Module.support`).
* Minimal-prime primality is witnessed by `IsMinimalPrime.isPrime`
  (definitionally the design note's `p.2.1.1`).
-/

namespace AssociatedPrimes.QuotientDimensionFacts

/-- (a) `Spec (S ⧸ I)` as the zero locus of `I`: thin wrapper over
`Ideal.primeSpectrumQuotientOrderIsoZeroLocus`. -/
noncomputable def specQuotient (S : Type*) [CommRing S] (I : Ideal S) :
    PrimeSpectrum (S ⧸ I) ≃o (PrimeSpectrum.zeroLocus (I : Set S)) :=
  Ideal.primeSpectrumQuotientOrderIsoZeroLocus I

/-- (a) Dimension transports across `specQuotient`. -/
lemma krullDim_quotient_eq_krullDim_zeroLocus (S : Type*) [CommRing S]
    (I : Ideal S) :
    ringKrullDim (S ⧸ I) =
      Order.krullDim (PrimeSpectrum.zeroLocus (I : Set S)) :=
  Order.krullDim_eq_of_orderIso (specQuotient S I)

/-- Chains of primes all containing `J` bound the dimension of `S ⧸ J`
(via its zero locus). Workhorse for (c)/(e). -/
lemma length_le_krullDim_zeroLocus_of_mem {S : Type*} [CommRing S]
    (c : LTSeries (PrimeSpectrum S)) (J : Ideal S)
    (hmem : ∀ i, J ≤ (c i).asIdeal) :
    (c.length : WithBot ℕ∞) ≤
      Order.krullDim (PrimeSpectrum.zeroLocus (J : Set S)) := by
  let c' : LTSeries (PrimeSpectrum.zeroLocus (J : Set S)) :=
    { length := c.length
      toFun := fun i => ⟨c i, hmem i⟩
      step := fun i => c.step i }
  exact Order.LTSeries.length_le_krullDim c'

/-- (b) Strict drop: modding out by a strictly larger prime drops the
Krull dimension by at least one. -/
lemma ringKrullDim_quotient_strictDrop {S : Type*} [CommRing S]
    {P Q : Ideal S} [P.IsPrime] [Q.IsPrime] (h : P < Q) :
    ringKrullDim (S ⧸ Q) + 1 ≤ ringKrullDim (S ⧸ P) := by
  have : Nonempty (PrimeSpectrum.zeroLocus (Q : Set S)) :=
    ⟨⟨⟨Q, ‹Q.IsPrime›⟩, (le_rfl : (Q : Ideal S) ≤ Q)⟩⟩
  have : Nonempty (PrimeSpectrum.zeroLocus (P : Set S)) :=
    ⟨⟨⟨P, ‹P.IsPrime›⟩, (le_rfl : (P : Ideal S) ≤ P)⟩⟩
  rw [krullDim_quotient_eq_krullDim_zeroLocus,
    krullDim_quotient_eq_krullDim_zeroLocus,
    Order.krullDim_eq_iSup_coheight_of_nonempty,
    Order.krullDim_eq_iSup_coheight_of_nonempty,
    ← WithBot.coe_one, ← WithBot.coe_add, ENat.iSup_add,
    WithBot.coe_le_coe]
  let j : (PrimeSpectrum.zeroLocus (Q : Set S)) →
    (PrimeSpectrum.zeroLocus (P : Set S)) :=
    fun q => ⟨q.1, le_trans (le_of_lt h) (q.2 : Q ≤ q.1.asIdeal)⟩
  have hj : StrictMono j := fun _ _ hab => hab
  let z : (PrimeSpectrum.zeroLocus (P : Set S)) :=
    ⟨⟨P, ‹P.IsPrime›⟩, (le_rfl : (P : Ideal S) ≤ P)⟩
  have hzq : ∀ q, z < j q := fun q =>
    (lt_of_lt_of_le h (q.2 : Q ≤ q.1.asIdeal) : (P : Ideal S) < q.1.asIdeal)
  refine iSup_le fun q => ?_
  calc Order.coheight q + 1
      ≤ Order.coheight (j q) + 1 :=
        add_le_add_left
          (Order.coheight_le_coheight_apply_of_strictMono j hj q) 1
    _ ≤ Order.coheight z := Order.coheight_add_one_le (hzq q)
    _ ≤ ⨆ p, Order.coheight p := le_iSup _ z

/-- (c) Dimension as the sup of coheights over minimal primes
(unconditional inside-coercion form). -/
lemma ringKrullDim_eq_sup_minimalPrimes (S : Type*) [CommRing S] :
    ringKrullDim S =
      ⨆ p : { p : Ideal S // p ∈ minimalPrimes S },
        ((Order.coheight
          (⟨p.1, IsMinimalPrime.isPrime p.2⟩ : PrimeSpectrum S) :
          ℕ∞) : WithBot ℕ∞) := by
  apply le_antisymm
  · change Order.krullDim (PrimeSpectrum S) ≤ _
    rw [Order.krullDim_eq_iSup_coheight]
    refine iSup_le fun q => ?_
    obtain ⟨p, hpmin, hle⟩ := Ideal.exists_minimalPrimes_le
      (show (⊥ : Ideal S) ≤ q.asIdeal from bot_le)
    have hpS : p ∈ minimalPrimes S := hpmin
    refine le_trans ?_
      (le_iSup _ (⟨p, hpS⟩ : { p : Ideal S // p ∈ minimalPrimes S }))
    refine WithBot.coe_le_coe.mpr (Order.coheight_anti ?_)
    exact hle
  · refine iSup_le fun p => ?_
    exact Order.coheight_le_krullDim _

/-- (c) Outside-coercion variant under `[Nontrivial S]`. -/
lemma ringKrullDim_eq_coe_sup_minimalPrimes (S : Type*) [CommRing S]
    [Nontrivial S] :
    ringKrullDim S =
      (((⨆ p : { p : Ideal S // p ∈ minimalPrimes S },
        Order.coheight
          (⟨p.1, IsMinimalPrime.isPrime p.2⟩ : PrimeSpectrum S)) :
        ℕ∞) : WithBot ℕ∞) := by
  have : Nonempty { p : Ideal S // p ∈ minimalPrimes S } := by
    obtain ⟨I, hImax⟩ := Ideal.exists_maximal S
    have hIprime := hImax.isPrime
    obtain ⟨p, hp, -⟩ := Ideal.exists_minimalPrimes_le
      (show (⊥ : Ideal S) ≤ I from bot_le)
    exact ⟨⟨p, hp⟩⟩
  rw [ringKrullDim_eq_sup_minimalPrimes,
    ← WithBot.coe_iSup (OrderTop.bddAbove _)]

/-- (c) Quotient form: dimension as the sup of `dim S ⧸ p` over minimal
primes (for UnmixedSqueeze). -/
lemma ringKrullDim_eq_sup_quotient_minimalPrimes (S : Type*)
    [CommRing S] :
    ringKrullDim S =
      ⨆ p : { p : Ideal S // p ∈ minimalPrimes S },
        ringKrullDim (S ⧸ p.1) := by
  apply le_antisymm
  · change (⨆ c : LTSeries (PrimeSpectrum S),
      (c.length : WithBot ℕ∞)) ≤ _
    refine iSup_le fun c => ?_
    obtain ⟨p, hpmin, hle⟩ := Ideal.exists_minimalPrimes_le
      (show (⊥ : Ideal S) ≤ (c.head).asIdeal from bot_le)
    have hpS : p ∈ minimalPrimes S := hpmin
    refine le_trans ?_
      (le_iSup _ (⟨p, hpS⟩ : { p : Ideal S // p ∈ minimalPrimes S }))
    rw [krullDim_quotient_eq_krullDim_zeroLocus]
    exact length_le_krullDim_zeroLocus_of_mem c p
      (fun i => le_trans hle (c.head_le i))
  · exact iSup_le fun p => ringKrullDim_quotient_le p.1

/-- (d) In Krull dimension zero over a local ring, the support of a
nonzero finite module is the singleton of the maximal ideal. -/
lemma support_eq_singleton_maximal_of_dim_zero {A M : Type*} [CommRing A]
    [IsLocalRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Nontrivial M] (h0 : Ring.KrullDimLE 0 A) :
    Module.support A M =
      {⟨IsLocalRing.maximalIdeal A, inferInstance⟩} := by
  have hall : ∀ I : Ideal A, I.IsPrime → I.IsMaximal :=
    Ring.krullDimLE_zero_iff.mp h0
  ext p
  simp only [Set.mem_singleton_iff]
  constructor
  · intro hp
    have hmax := hall p.asIdeal p.isPrime
    have heq : p.asIdeal = IsLocalRing.maximalIdeal A :=
      IsLocalRing.eq_maximalIdeal hmax
    exact PrimeSpectrum.ext_iff.mpr heq
  · intro hp
    subst hp
    rw [Module.mem_support_iff_exists_annihilator]
    obtain ⟨m, hm⟩ := exists_ne (0 : M)
    refine ⟨m, IsLocalRing.le_maximalIdeal ?_⟩
    intro htop
    have h1mem : (1 : A) ∈
        (Submodule.span A ({m} : Set M)).annihilator := by
      rw [htop]
      exact Submodule.mem_top
    have h10 : (1 : A) • m = 0 :=
      (Submodule.mem_annihilator_span_singleton m 1).mp h1mem
    rw [one_smul] at h10
    exact hm h10

/-- (e) Quotient dimension via minimal primes over the ideal. -/
lemma ringKrullDim_quotient_eq_sup_minimalPrimes (S : Type*) [CommRing S]
    (I : Ideal S) :
    ringKrullDim (S ⧸ I) =
      ⨆ p : { p : Ideal S // p ∈ I.minimalPrimes },
        ringKrullDim (S ⧸ p.1) := by
  apply le_antisymm
  · rw [krullDim_quotient_eq_krullDim_zeroLocus]
    change (⨆ c : LTSeries (PrimeSpectrum.zeroLocus (I : Set S)),
      (c.length : WithBot ℕ∞)) ≤ _
    refine iSup_le fun c => ?_
    let d : LTSeries (PrimeSpectrum S) :=
      c.map Subtype.val (fun _ _ hab => hab)
    have hdle : I ≤ (d.head).asIdeal := (c.head).2
    obtain ⟨p, hpmin, hle⟩ := Ideal.exists_minimalPrimes_le hdle
    refine le_trans ?_
      (le_iSup _ (⟨p, hpmin⟩ : { p : Ideal S // p ∈ I.minimalPrimes }))
    rw [krullDim_quotient_eq_krullDim_zeroLocus]
    have hlen : c.length = d.length := rfl
    rw [hlen]
    exact length_le_krullDim_zeroLocus_of_mem d p
      (fun i => le_trans hle (d.head_le i))
  · refine iSup_le fun p => ?_
    have hpI : I.IsMinimalPrime p.1 := p.2
    have hIJ : I ≤ p.1.comap (RingHom.id S) := by
      rw [Ideal.comap_id]
      exact hpI.le
    have hsurj : Function.Surjective
        (Ideal.quotientMap p.1 (RingHom.id S) hIJ) :=
      Ideal.quotientMap_surjective (fun x => ⟨x, rfl⟩)
    exact ringKrullDim_le_of_surjective _ hsurj

/-- (f) The `𝔪M ≠ M` micro-split via Nakayama: over a local ring, the
maximal ideal times a nonzero finite module is never the whole module. -/
lemma maximalIdeal_smul_ne_top {A M : Type*} [CommRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M] [Nontrivial M] :
    IsLocalRing.maximalIdeal A • (⊤ : Submodule A M) ≠ ⊤ := by
  intro hcon
  have hle : (⊤ : Submodule A M) ≤ IsLocalRing.maximalIdeal A • ⊤ :=
    hcon.ge
  have hFG : (⊤ : Submodule A M).FG := Module.Finite.fg_top
  have hjac : IsLocalRing.maximalIdeal A ≤ Ideal.jacobson ⊥ :=
    IsLocalRing.maximalIdeal_le_jacobson ⊥
  have hbot : (⊤ : Submodule A M) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ hFG hle hjac
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  have hmem : m ∈ (⊤ : Submodule A M) := Submodule.mem_top
  rw [hbot, Submodule.mem_bot] at hmem
  exact hm hmem

end AssociatedPrimes.QuotientDimensionFacts
