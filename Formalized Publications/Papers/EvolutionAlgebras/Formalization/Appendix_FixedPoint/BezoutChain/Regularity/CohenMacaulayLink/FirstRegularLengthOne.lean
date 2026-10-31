/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Regular.SMul
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Order.KrullDimension
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Appendix_FixedPoint.BezoutChain.Dimension.RegularSequenceDimDrop
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.AssHeightBound
import Appendix_FixedPoint.BezoutChain.Regularity.CohenMacaulayLink.CMQuotientFull
import Appendix_FixedPoint.BezoutChain.Regularity.CohenMacaulayLink.QuotientByRegularIsCM
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.RegularityBridge
import Appendix_FixedPoint.BezoutChain.Regularity.Unmixed.Unmixedness

/-!
# First regular element at length-1 CI quotients (`FirstReg`, `r = 1`)

Proves `firstReg_length_one`: every length-1 proper
CI quotient of positive dimension carries a regular element in `𝔪`, via the
localization-transfer route (global `k = 1` unmixedness G1 + Stacks 0310 +
GHT + exact C2 dim-drop). No CM/UFD/DVR input about any local ring is used.

## Implementation notes (deviations from the design note, all verified)

* The design note's lq+AE transport (§3.1 steps 2-3) is replaced by a direct
  `IsLocalizedModule` instance (`isLocalizedModule_quotToQuot`) on the natural
  map `quotToQuot : R ⧸ span{f} →ₗ[R] R_Q ⧸ span{x}`. This avoids the
  `LocalizedModule`-self identification (no such linear equiv over the
  localization ring exists in mathlib) while feeding Stacks 0310r
  (`comap_mem_associatedPrimes_of_mem_associatedPrimes_of_isLocalizedModule_of_fg`)
  exactly the data it asks for.
* L-QUOT-MAX is proved unconditionally (comap of maximal
  along surjective is maximal; no `J ≤ 𝔪` hypothesis needed).
* TC-note fixes from the verdict are applied: `Ideal.under` is used by defeq
  (`rfl`, no `under_eq_comap`), L-SUCC1 mirrors `Unmixedness.lean`
  with no quotient equiv, L-DIM is hand-rolled via `PrimeSpectrum.comapEquiv`.
* `FRCore` (§4) is stated as a `def` (sketch residual for `r ≥ 2`), with
  no placeholders.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace FirstRegularLengthOne

open RingTheory.Sequence
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain
open Module.associatedPrimes

/-! ## L-AVOID: `𝔪 ∉ Ass` gives a regular element in `𝔪` -/

/-- L-AVOID: `𝔪 ∉ Ass` gives a regular element in `𝔪` (composes L-av1
`exists_mem_maximal_avoid_ass` with L-av2
`isSMulRegular_of_forall_notMem_associatedPrimes`). -/
theorem firstReg_of_maximalIdeal_notMem_ass
    (S : Type*) [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    (hmax : IsLocalRing.maximalIdeal S ∉ associatedPrimes S S) :
    ∃ z ∈ IsLocalRing.maximalIdeal S, IsSMulRegular S z := by
  obtain ⟨y, hyM, hyavoid⟩ :=
    CMQuotientFull.exists_mem_maximal_avoid_ass S hmax
  exact ⟨y, hyM,
    CMQuotientFull.isSMulRegular_of_forall_notMem_associatedPrimes
      S y hyM hyavoid⟩

#print axioms firstReg_of_maximalIdeal_notMem_ass

/-! ## L-QUOT-ASS + L-QUOT-MAX: associated primes descend through quotients -/

/-- L-QUOT-ASS: associated primes descend from the quotient to the base along
`mk`. Proof: `AssociatedPrimes.mem_iff` + comap-of-annihilator algebra
(`(mk r)^n • x = r^n • x` on the quotient). No mathlib quotient-`Ass` lemma
exists, so this is hand-rolled. -/
theorem comap_mem_associatedPrimes_of_mem_associatedPrimes_quotient
    (R : Type*) [CommRing R] (J : Ideal R)
    (p : Ideal (R ⧸ J)) [p.IsPrime]
    (hmem : p ∈ associatedPrimes (R ⧸ J) (R ⧸ J)) :
    p.comap (Ideal.Quotient.mk J) ∈ associatedPrimes R (R ⧸ J) := by
  rw [AssociatedPrimes.mem_iff] at hmem ⊢
  obtain ⟨-, x, hx⟩ := hmem
  refine ⟨Ideal.comap_isPrime (Ideal.Quotient.mk J) p, x, ?_⟩
  rw [hx]
  ext r
  have hbridge : ∀ n : ℕ, (r ^ n : R) • x =
      (((Ideal.Quotient.mk J r) ^ n : R ⧸ J)) • x := by
    intro n
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_pow, smul_eq_mul]
  simp only [Ideal.mem_comap, Ideal.mem_radical_iff,
    Submodule.mem_colon_singleton, Submodule.mem_bot]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, by rwa [hbridge]⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by rwa [hbridge] at hn⟩

#print axioms comap_mem_associatedPrimes_of_mem_associatedPrimes_quotient

/-- L-QUOT-MAX: the comap of the quotient maximal ideal
along `mk` is the base maximal ideal (unconditional: comap of maximal along
surjective is maximal, and maximal ideals in a local ring are unique). -/
theorem comap_maximalIdeal_quotient_mk
    (R : Type*) [CommRing R] [IsLocalRing R] (J : Ideal R)
    [IsLocalRing (R ⧸ J)] :
    (IsLocalRing.maximalIdeal (R ⧸ J)).comap (Ideal.Quotient.mk J)
      = IsLocalRing.maximalIdeal R := by
  have hmax : ((IsLocalRing.maximalIdeal (R ⧸ J)).comap
      (Ideal.Quotient.mk J)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk J)
      Ideal.Quotient.mk_surjective
  exact IsLocalRing.eq_maximalIdeal hmax

#print axioms comap_maximalIdeal_quotient_mk

/-! ## L-FRAC: denominator clearing for the length-1 generator -/

/-- A regular element in a nontrivial ring is nonzero (`0 • ·` is not
injective). -/
theorem ne_zero_of_isSMulRegular (R : Type*) [CommRing R] [Nontrivial R]
    (x : R) (hreg : IsSMulRegular R x) : x ≠ 0 := by
  intro hcon
  have hinj : Function.Injective ((x • ·) : R → R) := hreg
  rw [hcon] at hinj
  have h01 : (0 : R) = 1 := hinj (by simp)
  exact zero_ne_one h01

#print axioms ne_zero_of_isSMulRegular

/-- L-FRAC: clear the denominator of a length-1 generator. Writing
`x = f/s₀`, `s₀` is a unit so
`span{x} = span{algebraMap f} = map (span{f})`. -/
theorem span_singleton_atPrime_eq_map_span (m : ℕ) (K : Type*) [Field K]
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (x : Localization.AtPrime Q) (hx0 : x ≠ 0) :
    ∃ f : MvPolynomial (Fin m) K, f ≠ 0 ∧
      Ideal.span ({x} : Set (Localization.AtPrime Q)) =
        Ideal.map (algebraMap (MvPolynomial (Fin m) K) (Localization.AtPrime Q))
          (Ideal.span {f}) := by
  obtain ⟨f, s, hfrac⟩ := IsLocalization.exists_mk'_eq Q.primeCompl x
  have hunit : IsUnit (algebraMap (MvPolynomial (Fin m) K)
      (Localization.AtPrime Q) (s : MvPolynomial (Fin m) K)) :=
    IsLocalization.map_units _ s
  obtain ⟨u, hu⟩ := hunit
  have hspec := IsLocalization.mk'_spec (Localization.AtPrime Q) f s
  rw [hfrac, ← hu] at hspec
  refine ⟨f, ?_, ?_⟩
  · intro hcon
    apply hx0
    rw [hcon, map_zero] at hspec
    have h := congrArg (· * (↑u⁻¹ : Localization.AtPrime Q)) hspec
    rw [mul_assoc, Units.mul_inv, mul_one, zero_mul] at h
    exact h
  · have hxeq : x = algebraMap (MvPolynomial (Fin m) K)
        (Localization.AtPrime Q) f * (↑u⁻¹ : Localization.AtPrime Q) := by
      have h1 : x * ((u : Localization.AtPrime Q) *
            (↑u⁻¹ : Localization.AtPrime Q)) =
          algebraMap (MvPolynomial (Fin m) K) (Localization.AtPrime Q) f *
            (↑u⁻¹ : Localization.AtPrime Q) := by
        rw [← mul_assoc, hspec]
      rw [Units.mul_inv, mul_one] at h1
      exact h1
    rw [hxeq, Ideal.span_singleton_mul_right_unit u⁻¹.isUnit _,
      Ideal.map_span, Set.image_singleton]

#print axioms span_singleton_atPrime_eq_map_span

/-! ## L-SUCC1: length-1 successive regularity over the domain -/

/-- L-SUCC1: a nonzero `f` is successive-regular of length 1 over the
polynomial domain (mirror of the `Unmixedness.lean` injectivity
transfer; no quotient equiv is used). -/
theorem successiveSMulRegular_singleton_of_ne_zero (m : ℕ) (K : Type*)
    [Field K] (f : MvPolynomial (Fin m) K) (hf : f ≠ 0) :
    RegularityBridge.SuccessiveSMulRegular
      (![f] : Fin 1 → MvPolynomial (Fin m) K) := by
  intro i
  have hval : ∀ j : Fin 1, j.val = 0 :=
    fun j => congrArg Fin.val (Fin.eq_zero j)
  have hempty : Set.image (![f] : Fin 1 → MvPolynomial (Fin m) K)
      {j : Fin 1 | j.val < i.val} = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro _ ⟨j, hj, rfl⟩
    have hj' : j.val < i.val := hj
    rw [hval j, hval i] at hj'
    exact lt_irrefl 0 hj'
  have hspan : Ideal.span (Set.image (![f] : Fin 1 → MvPolynomial (Fin m) K)
      {j : Fin 1 | j.val < i.val}) = ⊥ := by
    rw [hempty, Ideal.span_empty]
  have hfi : (![f] : Fin 1 → MvPolynomial (Fin m) K) i = f := by
    have hi : i = 0 := Fin.eq_zero i
    subst hi
    rfl
  rw [RegularSequenceDimDrop.span_smul_top, hspan, hfi]
  intro a b hab
  obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
  have hab' : f • Ideal.Quotient.mk (⊥ : Ideal (MvPolynomial (Fin m) K)) a' =
      f • Ideal.Quotient.mk (⊥ : Ideal (MvPolynomial (Fin m) K)) b' := hab
  rw [Algebra.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
    ← map_mul, ← map_mul] at hab'
  have hab0 : Ideal.Quotient.mk (⊥ : Ideal (MvPolynomial (Fin m) K))
      (f * a' - f * b') = 0 := by
    rw [map_sub, sub_eq_zero]
    exact hab'
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_bot] at hab0
  have hmul : f * (a' - b') = 0 := by
    have hring : f * (a' - b') = f * a' - f * b' := by ring
    rw [hring]
    exact hab0
  rcases mul_eq_zero.mp hmul with h | h
  · exact absurd h hf
  · have heq : a' = b' := sub_eq_zero.mp h
    rw [heq]

#print axioms successiveSMulRegular_singleton_of_ne_zero

/-! ## Localized-module data on the quotient map (replaces lq+AE) -/

/-- The natural `R`-linear map `R ⧸ span{f} →ₗ[R] R_Q ⧸ span{x}` induced by
`algebraMap`, using L-FRAC to kill `span{f}`. -/
noncomputable def quotToQuot (m : ℕ) (K : Type*) [Field K]
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (f : MvPolynomial (Fin m) K)
    (x : Localization.AtPrime Q)
    (hspan : Ideal.span ({x} : Set (Localization.AtPrime Q)) =
      Ideal.map (algebraMap (MvPolynomial (Fin m) K) (Localization.AtPrime Q))
        (Ideal.span {f})) :
    (MvPolynomial (Fin m) K) ⧸ (Ideal.span {f}) →ₗ[MvPolynomial (Fin m) K]
      ((Localization.AtPrime Q) ⧸
        Ideal.span ({x} : Set (Localization.AtPrime Q))) := by
  refine Submodule.liftQ _ (Algebra.linearMap _ _) ?_
  intro a ha
  rw [LinearMap.mem_ker, Algebra.linearMap_apply]
  have haJ : a ∈ Ideal.span ({f} : Set (MvPolynomial (Fin m) K)) := ha
  have hmem : algebraMap (MvPolynomial (Fin m) K) (Localization.AtPrime Q) a ∈
      Ideal.span ({x} : Set (Localization.AtPrime Q)) := by
    rw [hspan]
    exact Ideal.mem_map_of_mem _ haJ
  have hbridge : algebraMap (MvPolynomial (Fin m) K)
        ((Localization.AtPrime Q) ⧸ Ideal.span ({x} : Set (Localization.AtPrime Q))) a =
      Ideal.Quotient.mk _ (algebraMap (MvPolynomial (Fin m) K)
        (Localization.AtPrime Q) a) := rfl
  rw [hbridge, Ideal.Quotient.eq_zero_iff_mem]
  exact hmem

#print axioms quotToQuot

/-- `quotToQuot` on representatives is `algebraMap`. -/
theorem quotToQuot_mk (m : ℕ) (K : Type*) [Field K]
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (f : MvPolynomial (Fin m) K)
    (x : Localization.AtPrime Q)
    (hspan : Ideal.span ({x} : Set (Localization.AtPrime Q)) =
      Ideal.map (algebraMap (MvPolynomial (Fin m) K) (Localization.AtPrime Q))
        (Ideal.span {f}))
    (b : MvPolynomial (Fin m) K) :
    quotToQuot m K Q f x hspan (Ideal.Quotient.mk _ b) =
      algebraMap (MvPolynomial (Fin m) K)
        ((Localization.AtPrime Q) ⧸ Ideal.span ({x} : Set (Localization.AtPrime Q))) b :=
  rfl

#print axioms quotToQuot_mk

set_option maxSynthPendingDepth 3 in
/-- `quotToQuot` exhibits `R_Q ⧸ span{x}` as the localization of
`R ⧸ span{f}` at `Q.primeCompl`: units act invertibly, every class is a
fraction, and equal images clear denominators (via L-FRAC +
`algebraMap_mem_map_algebraMap_iff`). -/
theorem isLocalizedModule_quotToQuot (m : ℕ) (K : Type*) [Field K]
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (f : MvPolynomial (Fin m) K)
    (x : Localization.AtPrime Q)
    (hspan : Ideal.span ({x} : Set (Localization.AtPrime Q)) =
      Ideal.map (algebraMap (MvPolynomial (Fin m) K) (Localization.AtPrime Q))
        (Ideal.span {f})) :
    IsLocalizedModule Q.primeCompl (quotToQuot m K Q f x hspan) := by
  constructor
  · intro s
    have hunitRQ : IsUnit (algebraMap (MvPolynomial (Fin m) K)
        (Localization.AtPrime Q) (s : MvPolynomial (Fin m) K)) :=
      IsLocalization.map_units _ s
    have hu : IsUnit (algebraMap (MvPolynomial (Fin m) K)
        ((Localization.AtPrime Q) ⧸ Ideal.span ({x} : Set (Localization.AtPrime Q)))
        (s : MvPolynomial (Fin m) K)) :=
      RingHom.isUnit_map (Ideal.Quotient.mk _) hunitRQ
    obtain ⟨u, hu⟩ := hu
    rw [Module.End.isUnit_iff]
    have hact : ∀ y : ((Localization.AtPrime Q) ⧸
          Ideal.span ({x} : Set (Localization.AtPrime Q))),
        (algebraMap (MvPolynomial (Fin m) K)
          (Module.End (MvPolynomial (Fin m) K)
            ((Localization.AtPrime Q) ⧸ Ideal.span ({x} : Set (Localization.AtPrime Q))))
          (s : MvPolynomial (Fin m) K)) y = (u : _) * y := by
      intro y
      rw [Module.algebraMap_end_apply, Algebra.smul_def, ← hu]
    constructor
    · intro a b hab
      simp only [hact] at hab
      have h2 := congrArg ((↑u⁻¹ : Localization.AtPrime Q ⧸
        Ideal.span ({x} : Set (Localization.AtPrime Q))) * ·) hab
      simp only [← mul_assoc, Units.inv_mul, one_mul] at h2
      exact h2
    · intro b
      refine ⟨(↑u⁻¹ : Localization.AtPrime Q ⧸
        Ideal.span ({x} : Set (Localization.AtPrime Q))) * b, ?_⟩
      rw [hact, ← mul_assoc, Units.mul_inv, one_mul]
  · intro y
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨⟨b, t⟩, hst⟩ := IsLocalization.surj Q.primeCompl z
    refine ⟨(Ideal.Quotient.mk _ b, t), ?_⟩
    rw [Submonoid.smul_def, Algebra.smul_def, quotToQuot_mk]
    have e1 : algebraMap (MvPolynomial (Fin m) K)
          ((Localization.AtPrime Q) ⧸ Ideal.span ({x} : Set (Localization.AtPrime Q)))
          (t : MvPolynomial (Fin m) K) =
        Ideal.Quotient.mk _ (algebraMap (MvPolynomial (Fin m) K)
          (Localization.AtPrime Q) (t : MvPolynomial (Fin m) K)) := rfl
    have e2 : algebraMap (MvPolynomial (Fin m) K)
          ((Localization.AtPrime Q) ⧸ Ideal.span ({x} : Set (Localization.AtPrime Q))) b =
        Ideal.Quotient.mk _ (algebraMap (MvPolynomial (Fin m) K)
          (Localization.AtPrime Q) b) := rfl
    rw [e1, e2, ← map_mul]
    congr 1
    rw [mul_comm]
    exact hst
  · intro x₁ x₂ h
    obtain ⟨b₁, rfl⟩ := Ideal.Quotient.mk_surjective x₁
    obtain ⟨b₂, rfl⟩ := Ideal.Quotient.mk_surjective x₂
    rw [quotToQuot_mk, quotToQuot_mk] at h
    have hmem : algebraMap (MvPolynomial (Fin m) K) (Localization.AtPrime Q)
        (b₁ - b₂) ∈ Ideal.span ({x} : Set (Localization.AtPrime Q)) := by
      have h' : (Ideal.Quotient.mk (Ideal.span ({x} : Set (Localization.AtPrime Q)))
          (algebraMap (MvPolynomial (Fin m) K) (Localization.AtPrime Q) b₁)) =
          Ideal.Quotient.mk _ (algebraMap (MvPolynomial (Fin m) K)
            (Localization.AtPrime Q) b₂) := h
      have hsub : Ideal.Quotient.mk (Ideal.span ({x} : Set (Localization.AtPrime Q)))
            (algebraMap (MvPolynomial (Fin m) K) (Localization.AtPrime Q) b₁) -
          Ideal.Quotient.mk _ (algebraMap (MvPolynomial (Fin m) K)
            (Localization.AtPrime Q) b₂) = 0 := sub_eq_zero.mpr h'
      rw [← map_sub, ← map_sub, Ideal.Quotient.eq_zero_iff_mem] at hsub
      exact hsub
    rw [hspan] at hmem
    obtain ⟨c, hc, hmem2⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff Q.primeCompl
        (Localization.AtPrime Q) (Ideal.span {f}) (b₁ - b₂)).mp hmem
    refine ⟨⟨c, hc⟩, ?_⟩
    rw [Submonoid.smul_def, Submonoid.smul_def]
    have hsmul : ∀ (d e : MvPolynomial (Fin m) K),
        (d : MvPolynomial (Fin m) K) •
          (Ideal.Quotient.mk (Ideal.span {f}) e) =
          Ideal.Quotient.mk _ (d * e) := by
      intro d e
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul]
    rw [hsmul, hsmul]
    have h0 : Ideal.Quotient.mk (Ideal.span {f}) (c * b₁ - c * b₂) = 0 := by
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      have hring : c * b₁ - c * b₂ = c * (b₁ - b₂) := by ring
      rw [hring]
      exact hmem2
    rw [map_sub] at h0
    exact sub_eq_zero.mp h0

#print axioms isLocalizedModule_quotToQuot

/-! ## L-DIM + L-FIN: transports across the abstract-`S` equiv -/

/-- L-DIM: `¬KrullDimLE 0` crosses a ring equiv (hand-rolled chain transport
via `PrimeSpectrum.comapEquiv`; no C3 import needed). -/
theorem not_krullDimLE_zero_of_ringEquiv {S T : Type*} [CommRing S] [CommRing T]
    [IsLocalRing S] [IsLocalRing T]
    (e : S ≃+* T) (h : ¬ Ring.KrullDimLE 0 S) : ¬ Ring.KrullDimLE 0 T := by
  rw [Ring.krullDimLE_iff] at h ⊢
  have hdim : ringKrullDim S = ringKrullDim T := by
    unfold ringKrullDim
    exact Order.krullDim_eq_of_orderIso (PrimeSpectrum.comapEquiv e)
  rw [← hdim]
  exact h

#print axioms not_krullDimLE_zero_of_ringEquiv

/-- L-FIN: the witnessed regular element crosses the equiv (`e` preserves
units hence `𝔪`; `IsSMulRegular` injectivity transfers along `map_mul`). -/
theorem exists_regular_of_ringEquiv {S T : Type*} [CommRing S] [CommRing T]
    [IsLocalRing S] [IsLocalRing T]
    (e : S ≃+* T) (h : ∃ z ∈ IsLocalRing.maximalIdeal T, IsSMulRegular T z) :
    ∃ z ∈ IsLocalRing.maximalIdeal S, IsSMulRegular S z := by
  obtain ⟨w, hwM, hwreg⟩ := h
  refine ⟨e.symm w, ?_, ?_⟩
  · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hwM
    intro hu
    have hmap : IsUnit (e (e.symm w)) := RingHom.isUnit_map e.toRingHom hu
    rw [e.apply_symm_apply] at hmap
    exact hwM hmap
  · intro a b hab
    have hcon : w • (e a) = w • (e b) := by
      have h2 := congrArg (⇑e) hab
      simp only [smul_eq_mul, map_mul, e.apply_symm_apply] at h2 ⊢
      exact h2
    have heq : e a = e b := hwreg hcon
    exact e.injective heq

#print axioms exists_regular_of_ringEquiv

/-! ## FR1: `FirstReg` at `r = 1` -/

/-- FR1: `FirstReg` at `r = 1`. By L-AVOID it suffices to show
`𝔪_T ∉ Ass(T)`; supposing otherwise, L-QUOT-ASS + L-QUOT-MAX put
`𝔪_{R_Q} ∈ Ass(T)`, Stacks 0310r transfers to `Q ∈ Ass(R ⧸ span{f})`,
G1 + H-eq + GHT force `dim R_Q = 1`, and C2-dim forces `dim T = 0`,
contradicting L-DIM. L-FIN moves the witness to `S`. -/
theorem firstReg_length_one (m : ℕ) (K : Type*) [Field K]
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (S : Type*) [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    (x : Localization.AtPrime Q)
    (hx : x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (hreg : IsRegular (Localization.AtPrime Q) [x])
    (e : S ≃+* ((Localization.AtPrime Q) ⧸ Ideal.span {y | y ∈ [x]}))
    (hpos : ¬ Ring.KrullDimLE 0 S) :
    ∃ z ∈ IsLocalRing.maximalIdeal S, IsSMulRegular S z := by
  have hsmul : IsSMulRegular (Localization.AtPrime Q) x :=
    ((isRegular_cons_iff _ x []).mp hreg).1
  have hx0 : x ≠ 0 := ne_zero_of_isSMulRegular _ x hsmul
  obtain ⟨f, hf0, hspan⟩ := span_singleton_atPrime_eq_map_span m K Q x hx0
  have hset : ({y | y ∈ [x]} : Set (Localization.AtPrime Q)) = {x} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, List.mem_singleton]
  have hJeq : Ideal.span {y | y ∈ [x]} =
      Ideal.span ({x} : Set (Localization.AtPrime Q)) := by
    rw [hset]
  have e' : S ≃+* ((Localization.AtPrime Q) ⧸ Ideal.span ({x} : Set _)) :=
    e.trans (Ideal.quotEquivOfEq hJeq)
  have hle : Ideal.span ({x} : Set (Localization.AtPrime Q)) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime Q) :=
    (Ideal.span_singleton_le_iff_mem _).mpr hx
  have hJne : Ideal.span ({x} : Set (Localization.AtPrime Q)) ≠ ⊤ := by
    intro hcon
    rw [hcon] at hle
    have h1 : (1 : Localization.AtPrime Q) ∈
        IsLocalRing.maximalIdeal (Localization.AtPrime Q) :=
      hle (by simp)
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h1
    exact h1 isUnit_one
  have hnontrivT : Nontrivial
      ((Localization.AtPrime Q) ⧸ Ideal.span ({x} : Set _)) :=
    Ideal.Quotient.nontrivial_iff.mpr hJne
  have hlocalT : IsLocalRing
      ((Localization.AtPrime Q) ⧸ Ideal.span ({x} : Set _)) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _)
      Ideal.Quotient.mk_surjective
  have hposT : ¬ Ring.KrullDimLE 0
      ((Localization.AtPrime Q) ⧸ Ideal.span ({x} : Set _)) :=
    not_krullDimLE_zero_of_ringEquiv (S := S)
      (T := (Localization.AtPrime Q) ⧸
        Ideal.span ({x} : Set (Localization.AtPrime Q))) e' hpos
  have hcore : IsLocalRing.maximalIdeal
        ((Localization.AtPrime Q) ⧸ Ideal.span ({x} : Set _)) ∉
      associatedPrimes _
        ((Localization.AtPrime Q) ⧸ Ideal.span ({x} : Set _)) := by
    intro hmem
    have hmaxT : (IsLocalRing.maximalIdeal
        ((Localization.AtPrime Q) ⧸ Ideal.span ({x} : Set _))).IsMaximal :=
      inferInstance
    have hprimeT := hmaxT.isPrime
    have hcomap := comap_mem_associatedPrimes_of_mem_associatedPrimes_quotient
      (Localization.AtPrime Q) (Ideal.span ({x} : Set _))
      (IsLocalRing.maximalIdeal _) hmem
    rw [comap_maximalIdeal_quotient_mk] at hcomap
    have hlocmod := isLocalizedModule_quotToQuot m K Q f x hspan
    have hfg : ((IsLocalRing.maximalIdeal (Localization.AtPrime Q)).comap
        (algebraMap (MvPolynomial (Fin m) K) (Localization.AtPrime Q))).FG :=
      (isNoetherianRing_iff_ideal_fg _).mp inferInstance _
    have h0310 :=
      comap_mem_associatedPrimes_of_mem_associatedPrimes_of_isLocalizedModule_of_fg
        Q.primeCompl (quotToQuot m K Q f x hspan)
        (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) hcomap hfg
    have hunder : (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).comap
        (algebraMap (MvPolynomial (Fin m) K) (Localization.AtPrime Q)) = Q :=
      Localization.AtPrime.under_maximalIdeal
    rw [hunder] at h0310
    have hsucc := successiveSMulRegular_singleton_of_ne_zero m K f hf0
    have hrange : Set.range (![f] : Fin 1 → MvPolynomial (Fin m) K) = {f} := by
      ext r
      simp only [Set.mem_range, Set.mem_singleton_iff]
      constructor
      · rintro ⟨i, rfl⟩
        have hi : i = 0 := Fin.eq_zero i
        subst hi
        rfl
      · intro hr
        subst hr
        exact ⟨0, rfl⟩
    have hmin : Q ∈ (Ideal.span {f}).minimalPrimes :=
      mem_minimalPrimes_of_successive_singleton m K ![f] hsucc
        (Ideal.span {f}) (by rw [hrange]) Q h0310
    have hheight : Q.height = ((1 : ℕ) : ℕ∞) :=
      AssHeightBound.height_eq_of_mem_minimalPrimes ![f] hsucc
        (Ideal.span {f}) (by rw [hrange]) Q hmin
    have hGHT := IsLocalization.AtPrime.ringKrullDim_eq_height Q
      (Localization.AtPrime Q)
    have hC2 := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim
      hsmul hx
    rw [hGHT, hheight] at hC2
    have hT0 : ringKrullDim ((Localization.AtPrime Q) ⧸
        Ideal.span ({x} : Set _)) = 0 := by
      have h1 : ringKrullDim ((Localization.AtPrime Q) ⧸
          Ideal.span ({x} : Set _)) + 1 = (0 : WithBot ℕ∞) + 1 := by
        rw [hC2]
        simp
      exact QuotientByRegularIsCM.withBot_eNat_add_one_cancel _ _ h1
    have hle0 : Ring.KrullDimLE 0 ((Localization.AtPrime Q) ⧸
        Ideal.span ({x} : Set _)) :=
      Ring.krullDimLE_iff.mpr (by rw [hT0, Nat.cast_zero])
    exact hposT hle0
  have hwit : ∃ z ∈ IsLocalRing.maximalIdeal
      ((Localization.AtPrime Q) ⧸ Ideal.span ({x} : Set _)),
      IsSMulRegular _ z :=
    firstReg_of_maximalIdeal_notMem_ass
      (S := (Localization.AtPrime Q) ⧸ Ideal.span ({x} : Set _)) hcore
  exact exists_regular_of_ringEquiv (S := S)
    (T := (Localization.AtPrime Q) ⧸ Ideal.span ({x} : Set _)) e' hwit

#print axioms firstReg_length_one

/-! ## Residual register: fr-core at `r ≥ 2` (sketch) -/

/-- `[FR-CORE]` residual (sketch, Serre-adjacent): `𝔪 ∉ Ass` for proper CI
quotients of length `≥ 2`. Weakest firing form: `FirstReg` at `r ≥ 2`
follows by L-AVOID. Even at `dim S = 1` this is dim-1 CI unmixedness,
unproven. -/
def FRCore : Prop :=
  ∀ (m : ℕ) (K : Type*) [Field K]
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (S : Type*) [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    (rs₀ : List (Localization.AtPrime Q)),
    2 ≤ rs₀.length →
    (∀ r ∈ rs₀, r ∈ IsLocalRing.maximalIdeal (Localization.AtPrime Q)) →
    IsRegular (Localization.AtPrime Q) rs₀ →
    Nonempty (S ≃+* ((Localization.AtPrime Q) ⧸ Ideal.span {x | x ∈ rs₀})) →
    ¬ Ring.KrullDimLE 0 S →
    IsLocalRing.maximalIdeal S ∉ associatedPrimes S S

end FirstRegularLengthOne
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
