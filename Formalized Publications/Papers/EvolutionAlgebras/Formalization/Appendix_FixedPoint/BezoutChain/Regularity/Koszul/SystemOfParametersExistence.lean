/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Order.KrullDimension
import Mathlib.Order.RelSeries
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.RingTheory.Spectrum.Prime.Defs
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.PrimeAvoidance
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.YSopStep

/-!
# System of parameters existence (prime-avoidance induction)

For a Noetherian local ring of finite Krull dimension, a system of
parameters exists: `d = dim R` elements of the maximal ideal whose span
cuts the ring down to dimension zero. This is the standard
prime-avoidance induction (Matsumura, *Commutative Ring Theory*,
Theorem 12.1; Atiyah–Macdonald Chapter 11): at each step, pick
`x ∈ 𝔪` avoiding the minimal primes over the previous generators
(possible by prime avoidance unless a minimal prime is `𝔪` itself, in
which case the quotient is already zero-dimensional along that
component), and the Krull dimension drops by at least one.

* (§0) `exists_krullDimLE_of_finiteRingKrullDim`: finite dimension
  unfolds to `KrullDimLE e` for `e` the longest-series length.
* (§1) `IsSystemOfParameters`: the predicate (tuple in `𝔪` +
  zero-dimensional quotient).
* (§2) `exists_mem_maximal_avoid_minimalPrimes_ne_maximal`: the
  avoidance selection over minimal primes `≠ 𝔪`.
* (§3) `krullDimLE_quotient_sup_span_singleton`: the dimension-drop
  step. A chain in `Spec (R ⧸ J')` pushes forward to `Spec (R ⧸ J)`;
  since `x` avoids every minimal prime over `J` except possibly `𝔪`,
  the bottom prime is not minimal (unless it is `𝔪`, in which case the
  chain is trivial), so a minimal prime prepends and the length grows
  by one — hence every chain in the smaller spectrum has length `≤ e`.
* (§4) `exists_systemOfParameters_of_krullDimLE`: the induction.
* (§5) Corollaries: finite-dimension form, exact-length form
  (`length = ringKrullDim`), and the `List`/`Ideal.ofList` form in the
  exact `SystemOfParameters` shape.
* (§6) Shape bridges for consumers: the minimal-primes-are-`𝔪`
  reformulation of the zero-dimensionality conclusion.

## References

Project (read-only):
* `Regularity/Avoid/PrimeAvoidance.lean`: `exists_mem_notMem_of_forall_not_le_finite`.
* `Regularity/Koszul/YSopStep.lean`: `span_range_snoc_eq_sup`.
* `Regularity/Koszul/SystemOfParameters.lean`: the `List`/`Ideal.ofList` consumer shape.

Mathlib (`lean-toolchain` pins `v4.34.0`):
* `Ideal.subset_union_prime_finite`
  (`RingTheory/Ideal/Operations.lean`).
* `Ring.krullDimLE_iff` (`RingTheory/KrullDimension/Basic.lean`),
  `ringKrullDim_eq_of_ringEquiv`.
* `Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal`
  (`RingTheory/KrullDimension/Zero.lean`).
* `Ideal.exists_minimalPrimes_le`
  (`RingTheory/Ideal/MinimalPrime/Basic.lean`),
  `Ideal.IsMinimalPrime.isPrime`/`le`.
* `Ideal.finite_minimalPrimes_of_isNoetherianRing`
  (`RingTheory/Ideal/MinimalPrime/Noetherian.lean`).
* `Ideal.Quotient.factor`/`factor_mk`
  (`RingTheory/Ideal/Quotient/Defs.lean`/`176`),
  `Ideal.mk_ker` (`RingTheory/Ideal/Quotient/Operations.lean`),
  `RingEquiv.quotientBot`.
* `Ideal.map_comap_of_surjective`/`comap_injective_of_surjective`/
  `comap_mono`/`ker_le_comap`/`IsPrime.comap`
  (`RingTheory/Ideal/Maps.lean`/`327`/`84`/`1052`/`137`).
* `Ideal.IsMaximal.eq_of_le` (`RingTheory/Ideal/Maximal.lean`).
* `IsLocalRing.le_maximalIdeal_of_isPrime`/`eq_maximalIdeal`/
  `maximalIdeal.isMaximal`
  (`RingTheory/LocalRing/MaximalIdeal/Basic.lean`/`56`/`36`).
* `PrimeSpectrum.comap`/`comap_asIdeal`
  (`RingTheory/Spectrum/Prime/RingHom.lean`/`47`),
  `Ideal.primeSpectrumQuotientOrderIsoZeroLocus` ,
  `PrimeSpectrum.zeroLocus`/`mem_zeroLocus`
  (`RingTheory/Spectrum/Prime/Basic.lean`/`141`),
  `PrimeSpectrum.asIdeal_lt_asIdeal`
  (`RingTheory/Spectrum/Prime/Defs.lean`).
* `Order.krullDim_eq_iSup_coheight` , `Order.coheight_le`
  , `Order.length_le_coheight_head` ,
  `Order.coheight_le_krullDim` , `Order.coheight_eq_zero`
  , `Order.krullDim_eq_length_of_finiteDimensionalOrder`
   (`Order/KrullDimension.lean`).
* `LTSeries.map`/`LTSeries.head_map` (`Order/RelSeries.lean`/`916`),
  `RelSeries.cons`/`RelSeries.cons_length` (generated).
* `Ideal.ofList` (`RingTheory/Regular/RegularSequence.lean`),
  `List.mem_ofFn'` (`Data/List/OfFn.lean`),
  `Fin.forall_fin_succ'` (`Data/Fin/SuccPred.lean`),
  `Fin.snoc_castSucc`/`Fin.snoc_last`
  (`Data/Fin/Tuple/Basic.lean`/`540`).

## Status

* `exists_krullDimLE_of_finiteRingKrullDim`: unconditional.
* `exists_mem_maximal_avoid_minimalPrimes_ne_maximal`: unconditional.
* `krullDimLE_quotient_sup_span_singleton`: unconditional.
* `exists_systemOfParameters_of_krullDimLE`: unconditional.
* `krullDimLE_quotient_bot_of_krullDimLE`: unconditional.
* `exists_systemOfParameters_of_finite`: unconditional.
* `exists_systemOfParameters_length_eq_krullDim`: unconditional.
* `exists_systemOfParameters_list_of_krullDimLE`: unconditional.
* `krullDimLE_zero_quotient_iff_minimalPrimes_eq_maximal`: unconditional.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace SystemOfParametersExistence

/-! ## §0 Finite dimension unfolds to `KrullDimLE` -/

/-- Finite Krull dimension unfolds to `KrullDimLE e` for `e` the
longest-series length (`krullDim` is exactly that length).
-/
theorem exists_krullDimLE_of_finiteRingKrullDim (R : Type*) [CommSemiring R]
    [FiniteRingKrullDim R] : ∃ e : ℕ, Ring.KrullDimLE e R :=
  ⟨(LTSeries.longestOf (PrimeSpectrum R)).length,
    (Order.krullDimLE_iff _ _).mpr
      Order.krullDim_eq_length_of_finiteDimensionalOrder.le⟩

/-! ## §1 The system-of-parameters predicate -/

/-- A system of parameters of length `e`: a tuple in the maximal ideal
whose span cuts the ring down to dimension zero. The `KrullDimLE 0`
conclusion is equivalent to "every minimal prime over the span is
maximal" (`krullDimLE_zero_quotient_iff_minimalPrimes_eq_maximal`). -/
def IsSystemOfParameters {R : Type*} [CommRing R] [IsLocalRing R] (e : ℕ)
    (g : Fin e → R) : Prop :=
  (∀ i, g i ∈ IsLocalRing.maximalIdeal R) ∧
    Ring.KrullDimLE 0 (R ⧸ Ideal.span (Set.range g))

/-! ## §2 Avoidance selection over minimal primes `≠ 𝔪` -/

/-- The avoidance selection: some `x ∈ 𝔪` lies outside every minimal
prime over `J` except possibly `𝔪` itself. Per-prime non-containment
is maximality (`𝔪 ≤ Q` forces `Q = 𝔪` since `Q` is prime).
-/
theorem exists_mem_maximal_avoid_minimalPrimes_ne_maximal {R : Type*}
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (J : Ideal R) :
    ∃ x ∈ IsLocalRing.maximalIdeal R,
      ∀ Q ∈ J.minimalPrimes, Q ≠ IsLocalRing.maximalIdeal R → x ∉ Q := by
  have hfin : {Q : Ideal R | Q ∈ J.minimalPrimes ∧
      Q ≠ IsLocalRing.maximalIdeal R}.Finite :=
    (Ideal.finite_minimalPrimes_of_isNoetherianRing R J).subset
      (fun Q hQ => hQ.1)
  obtain ⟨x, hx, hxavoid⟩ :=
    PrimeAvoidance.exists_mem_notMem_of_forall_not_le_finite (R := R)
      (ι := Ideal R)
      (s := {Q : Ideal R | Q ∈ J.minimalPrimes ∧
        Q ≠ IsLocalRing.maximalIdeal R}) hfin (f := id)
      (⊥ : Ideal R) (⊥ : Ideal R)
      (fun Q hQ _ _ => Ideal.IsMinimalPrime.isPrime hQ.1)
      (IsLocalRing.maximalIdeal R)
      (fun Q hQ hle => hQ.2 (((IsLocalRing.maximalIdeal.isMaximal R).eq_of_le
        (Ideal.IsMinimalPrime.isPrime hQ.1).ne_top hle).symm))
  exact ⟨x, hx, fun Q hQ hQm => hxavoid Q ⟨hQ, hQm⟩⟩

/-! ## §3 The dimension-drop step -/

/-- The dimension-drop step: adjoining to `J` an element `x` that
avoids every minimal prime over `J` except possibly `𝔪` drops the
quotient dimension by at least one (no hypothesis `x ∈ 𝔪` is needed
for the drop itself). A series in `Spec (R ⧸ J')`
pushes forward along the quotient map to `Spec (R ⧸ J)`; the bottom
prime contains `x`, hence is not minimal over `J` unless it is `𝔪`
(in which case the pushed-forward series is trivial since its head
is maximal). Otherwise a minimal prime over `J` strictly below it
prepends, giving a series of length `+1` in `Spec (R ⧸ J)`.
-/
theorem krullDimLE_quotient_sup_span_singleton {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (J : Ideal R) (x : R)
    (havoid : ∀ Q ∈ J.minimalPrimes, Q ≠ IsLocalRing.maximalIdeal R → x ∉ Q)
    (e : ℕ) (hJ : Ring.KrullDimLE (e + 1) (R ⧸ J)) :
    Ring.KrullDimLE e (R ⧸ (J ⊔ Ideal.span {x})) := by
  set J' : Ideal R := J ⊔ Ideal.span {x}
  have hJJ' : J ≤ J' := le_sup_left
  have hxJ' : x ∈ J' := Submodule.mem_sup_right (Ideal.mem_span_singleton_self x)
  set π : R ⧸ J →+* R ⧸ J' := Ideal.Quotient.factor hJJ'
  have hπsurj : Function.Surjective π := by
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk J a, Ideal.Quotient.factor_mk hJJ' a⟩
  have hπmk : ∀ a : R, π (Ideal.Quotient.mk J a) = Ideal.Quotient.mk J' a :=
    fun a => Ideal.Quotient.factor_mk hJJ' a
  have hφ : StrictMono (PrimeSpectrum.comap π) := by
    have hmono : Monotone (PrimeSpectrum.comap π) := by
      intro a b hab
      change (PrimeSpectrum.comap π a).asIdeal ≤
        (PrimeSpectrum.comap π b).asIdeal
      rw [PrimeSpectrum.comap_asIdeal, PrimeSpectrum.comap_asIdeal]
      exact Ideal.comap_mono hab
    have hinj : Function.Injective (PrimeSpectrum.comap π) := by
      intro a b hab
      apply PrimeSpectrum.ext
      apply Ideal.comap_injective_of_surjective π hπsurj
      have h2 := PrimeSpectrum.ext_iff.mp hab
      rwa [PrimeSpectrum.comap_asIdeal, PrimeSpectrum.comap_asIdeal] at h2
    exact hmono.strictMono_of_injective hinj
  rw [Ring.KrullDimLE, Order.krullDimLE_iff, Order.krullDim_eq_iSup_coheight,
    iSup_le_iff]
  intro 𝔭₀
  have hcoh : Order.coheight 𝔭₀ ≤ (e : ℕ∞) := by
    apply Order.coheight_le
    intro q _
    set t := LTSeries.map q (PrimeSpectrum.comap π) hφ
    have hlen : t.length = q.length := rfl
    have hhead : t.head = PrimeSpectrum.comap π q.head :=
      LTSeries.head_map _ _ _
    have hJP : J ≤ Ideal.comap (Ideal.Quotient.mk J) t.head.asIdeal :=
      calc J = RingHom.ker (Ideal.Quotient.mk J) := J.mk_ker.symm
        _ ≤ Ideal.comap (Ideal.Quotient.mk J) t.head.asIdeal :=
          Ideal.ker_le_comap _
    have hPJ : Ideal.comap (Ideal.Quotient.mk J) t.head.asIdeal ≤
        IsLocalRing.maximalIdeal R :=
      IsLocalRing.le_maximalIdeal_of_isPrime _
    have hxP : x ∈ Ideal.comap (Ideal.Quotient.mk J) t.head.asIdeal := by
      have hmem : Ideal.Quotient.mk J' x ∈ (q.head).asIdeal := by
        have hle : J' ≤ Ideal.comap (Ideal.Quotient.mk J') (q.head).asIdeal :=
          calc J' = RingHom.ker (Ideal.Quotient.mk J') := J'.mk_ker.symm
            _ ≤ Ideal.comap (Ideal.Quotient.mk J') (q.head).asIdeal :=
              Ideal.ker_le_comap _
        exact hle hxJ'
      rw [hhead]
      change Ideal.Quotient.mk J x ∈ (PrimeSpectrum.comap π q.head).asIdeal
      rw [PrimeSpectrum.comap_asIdeal]
      change π (Ideal.Quotient.mk J x) ∈ (q.head).asIdeal
      rw [hπmk]
      exact hmem
    by_cases hPm : Ideal.comap (Ideal.Quotient.mk J) t.head.asIdeal =
      IsLocalRing.maximalIdeal R
    · -- The head is maximal, so the pushed-forward series is trivial.
      have hmax : IsMax t.head := by
        intro b hle
        have hleI : t.head.asIdeal ≤ b.asIdeal := hle
        rcases eq_or_lt_of_le hleI with heq | hlt
        · have hle' : b.asIdeal ≤ t.head.asIdeal := le_of_eq heq.symm
          exact hle'
        · exfalso
          have hcomap_le : Ideal.comap (Ideal.Quotient.mk J) t.head.asIdeal ≤
              Ideal.comap (Ideal.Quotient.mk J) b.asIdeal :=
            Ideal.comap_mono hleI
          rw [hPm] at hcomap_le
          have hne : Ideal.comap (Ideal.Quotient.mk J) b.asIdeal ≠ ⊤ := by
            intro htop
            have hmc := Ideal.map_comap_of_surjective (Ideal.Quotient.mk J)
              Ideal.Quotient.mk_surjective b.asIdeal
            rw [htop, Ideal.map_top] at hmc
            exact b.isPrime.ne_top hmc.symm
          have hmaximal : (IsLocalRing.maximalIdeal R).IsMaximal := inferInstance
          have heqM : IsLocalRing.maximalIdeal R =
              Ideal.comap (Ideal.Quotient.mk J) b.asIdeal :=
            hmaximal.eq_of_le hne hcomap_le
          have hcontra : t.head.asIdeal = b.asIdeal := by
            apply Ideal.comap_injective_of_surjective (Ideal.Quotient.mk J)
              Ideal.Quotient.mk_surjective
            rw [hPm, heqM]
          exact ne_of_lt hlt hcontra
      have hlen0 : q.length = 0 := by
        have h1 : ((t.length : ℕ) : ℕ∞) ≤ Order.coheight t.head :=
          Order.length_le_coheight_head
        have h0 : Order.coheight t.head = 0 := Order.coheight_eq_zero.mpr hmax
        rw [h0] at h1
        have htz : t.length = 0 := by
          have hle0 : t.length ≤ 0 := by exact_mod_cast h1
          exact Nat.le_zero.mp hle0
        rw [hlen] at htz
        exact htz
      rw [hlen0]
      exact Nat.cast_le.mpr (Nat.zero_le e)
    · -- The bottom prime is not minimal; prepend a minimal prime below it.
      obtain ⟨Q, hQmem, hQP⟩ := Ideal.exists_minimalPrimes_le hJP
      have hQprime : Q.IsPrime := Ideal.IsMinimalPrime.isPrime hQmem
      have hJQ : J ≤ Q := Ideal.IsMinimalPrime.le hQmem
      have hQm : Q ≠ IsLocalRing.maximalIdeal R := by
        intro hQm
        apply hPm
        apply le_antisymm hPJ
        rw [← hQm]
        exact hQP
      have hxQ : x ∉ Q := havoid Q hQmem hQm
      have hQP' : Q < Ideal.comap (Ideal.Quotient.mk J) t.head.asIdeal :=
        lt_of_le_of_ne hQP (fun heq => hxQ (by rwa [heq]))
      set iso := Ideal.primeSpectrumQuotientOrderIsoZeroLocus J
      have hQmem' : (⟨Q, hQprime⟩ : PrimeSpectrum R) ∈
          PrimeSpectrum.zeroLocus (↑J : Set R) := fun _ hx => hJQ hx
      set 𝔮 : PrimeSpectrum (R ⧸ J) := iso.symm ⟨⟨Q, hQprime⟩, hQmem'⟩ with hqdef
      have hlt : 𝔮 < t.head := by
        have h1 : iso 𝔮 < iso t.head := by
          rw [hqdef, OrderIso.apply_symm_apply]
          have h2 : iso t.head =
              (⟨PrimeSpectrum.comap (Ideal.Quotient.mk J) t.head, J.mk_ker.symm.trans_le
                (Ideal.ker_le_comap (Ideal.Quotient.mk J))⟩ :
                PrimeSpectrum.zeroLocus (↑J : Set R)) := rfl
          rw [h2]
          refine Subtype.mk_lt_mk.mpr ?_
          rw [← PrimeSpectrum.asIdeal_lt_asIdeal, PrimeSpectrum.comap_asIdeal]
          exact hQP'
        exact iso.lt_iff_lt.mp h1
      have hlen2 : (t.cons 𝔮 hlt).length = q.length + 1 := by
        rw [RelSeries.cons_length, hlen]
      have h4 : Order.krullDim (PrimeSpectrum (R ⧸ J)) ≤ ((e + 1 : ℕ) : WithBot ℕ∞) :=
        Ring.krullDimLE_iff.mp hJ
      have h1 : (((t.cons 𝔮 hlt).length : ℕ) : ℕ∞) ≤
          Order.coheight (t.cons 𝔮 hlt).head :=
        Order.length_le_coheight_head
      have h1' : ((((t.cons 𝔮 hlt).length : ℕ) : ℕ∞) : WithBot ℕ∞)
          ≤ ((Order.coheight (t.cons 𝔮 hlt).head : ℕ∞) : WithBot ℕ∞) :=
        WithBot.coe_le_coe.mpr h1
      have hchain : ((((t.cons 𝔮 hlt).length : ℕ) : ℕ∞) : WithBot ℕ∞)
          ≤ ((e + 1 : ℕ) : WithBot ℕ∞) :=
        h1'.trans ((Order.coheight_le_krullDim _).trans h4)
      rw [hlen2] at hchain
      have hleN : q.length + 1 ≤ e + 1 :=
        WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp hchain)
      have hfin : q.length ≤ e := by omega
      exact Nat.cast_le.mpr hfin
  exact WithBot.coe_le_coe.mpr hcoh

/-! ## §4 The induction -/

/-- System of parameters of length `e` over `J`: induction on `e`.
At each step the avoidance selection (§2) feeds the drop step (§3),
and the new element snocs onto the tuple (`Fin.snoc`, with the span
splitting by `YSopStep.span_range_snoc_eq_sup`).
-/
theorem exists_systemOfParameters_of_krullDimLE {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (J : Ideal R) (e : ℕ) :
    Ring.KrullDimLE e (R ⧸ J) → ∃ g : Fin e → R,
      (∀ i, g i ∈ IsLocalRing.maximalIdeal R) ∧
      Ring.KrullDimLE 0 (R ⧸ (J ⊔ Ideal.span (Set.range g))) := by
  revert J
  induction e with
  | zero =>
    intro J h
    refine ⟨Fin.elim0, fun i => Fin.elim0 i, ?_⟩
    have hrange : Set.range (Fin.elim0 : Fin 0 → R) = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.mpr ?_
      rintro y ⟨i, rfl⟩
      exact absurd i.isLt (Nat.not_lt_zero _)
    rw [hrange, Ideal.span_empty, sup_bot_eq]
    exact h
  | succ e ih =>
    intro J h
    obtain ⟨x, hx, havoid⟩ :=
      exists_mem_maximal_avoid_minimalPrimes_ne_maximal J
    have hdrop : Ring.KrullDimLE e (R ⧸ (J ⊔ Ideal.span {x})) :=
      krullDimLE_quotient_sup_span_singleton J x havoid e h
    obtain ⟨g, hg, hg0⟩ := ih (J ⊔ Ideal.span {x}) hdrop
    refine ⟨Fin.snoc g x, ?_, ?_⟩
    · rw [Fin.forall_fin_succ']
      constructor
      · intro j
        rw [Fin.snoc_castSucc]
        exact hg j
      · rw [Fin.snoc_last]
        exact hx
    · have hspan := YSopStep.span_range_snoc_eq_sup (R := R) e g x
      have hJeq : J ⊔ Ideal.span (Set.range (Fin.snoc g x))
          = (J ⊔ Ideal.span {x}) ⊔ Ideal.span (Set.range g) := by
        rw [hspan, sup_assoc]
      rw [hJeq]
      exact hg0

/-! ## §5 Corollaries -/

/-- Transfer `KrullDimLE` across `R ⧸ ⊥ ≃ R`.
-/
theorem krullDimLE_quotient_bot_of_krullDimLE {R : Type*} [CommRing R] (e : ℕ)
    (h : Ring.KrullDimLE e R) : Ring.KrullDimLE e (R ⧸ (⊥ : Ideal R)) := by
  have h4 : ringKrullDim (R ⧸ (⊥ : Ideal R)) ≤ (e : WithBot ℕ∞) := by
    rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot R)]
    exact Ring.krullDimLE_iff.mp h
  exact Ring.krullDimLE_iff.mpr h4

/-- System of parameters for a Noetherian local ring of finite
dimension: some length `e` works.
-/
theorem exists_systemOfParameters_of_finite {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] [FiniteRingKrullDim R] :
    ∃ e : ℕ, ∃ g : Fin e → R, IsSystemOfParameters e g := by
  obtain ⟨e, he⟩ := exists_krullDimLE_of_finiteRingKrullDim (R := R)
  have heBot : Ring.KrullDimLE e (R ⧸ (⊥ : Ideal R)) :=
    krullDimLE_quotient_bot_of_krullDimLE e he
  obtain ⟨g, hg, hg0⟩ := exists_systemOfParameters_of_krullDimLE (⊥ : Ideal R) e
    heBot
  refine ⟨e, g, ?_⟩
  constructor
  · exact hg
  · rwa [bot_sup_eq] at hg0

/-- System of parameters of length exactly `ringKrullDim`: the length
is the longest-series length, which is definitionally the dimension.
-/
theorem exists_systemOfParameters_length_eq_krullDim {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] [FiniteRingKrullDim R] :
    ∃ e : ℕ, ∃ g : Fin e → R, IsSystemOfParameters e g ∧
      ((e : ℕ) : WithBot ℕ∞) = ringKrullDim R := by
  refine ⟨(LTSeries.longestOf (PrimeSpectrum R)).length, ?_⟩
  have he : Ring.KrullDimLE (LTSeries.longestOf (PrimeSpectrum R)).length R :=
    (Order.krullDimLE_iff _ _).mpr
      Order.krullDim_eq_length_of_finiteDimensionalOrder.le
  have heq : ((((LTSeries.longestOf (PrimeSpectrum R)).length : ℕ)) :
      WithBot ℕ∞) = ringKrullDim R :=
    Order.krullDim_eq_length_of_finiteDimensionalOrder.symm
  have heBot : Ring.KrullDimLE (LTSeries.longestOf (PrimeSpectrum R)).length
      (R ⧸ (⊥ : Ideal R)) :=
    krullDimLE_quotient_bot_of_krullDimLE _ he
  obtain ⟨g, hg, hg0⟩ := exists_systemOfParameters_of_krullDimLE (⊥ : Ideal R) _
    heBot
  refine ⟨g, ?_, heq⟩
  constructor
  · exact hg
  · rwa [bot_sup_eq] at hg0

/-- System of parameters as a `List` in the exact `SystemOfParameters` shape:
`Ideal.ofList rs` cuts `J` down to dimension zero, with
`rs.length = e`.
-/
theorem exists_systemOfParameters_list_of_krullDimLE {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (J : Ideal R) (e : ℕ)
    (h : Ring.KrullDimLE e (R ⧸ J)) :
    ∃ rs : List R, (∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R) ∧
      Ring.KrullDimLE 0 (R ⧸ (J ⊔ Ideal.ofList rs)) ∧ rs.length = e := by
  obtain ⟨g, hg, hg0⟩ := exists_systemOfParameters_of_krullDimLE J e h
  refine ⟨List.ofFn g, ?_, ?_, List.length_ofFn⟩
  · intro r hr
    rw [List.mem_ofFn'] at hr
    obtain ⟨i, rfl⟩ := hr
    exact hg i
  · have hof : Ideal.ofList (List.ofFn g) = Ideal.span (Set.range g) := by
      have hset : {r : R | r ∈ List.ofFn g} = Set.range g := by
        ext r
        exact List.mem_ofFn' g r
      change Ideal.span {r : R | r ∈ List.ofFn g} = _
      rw [hset]
    rw [hof]
    exact hg0

/-! ## §6 Shape bridges for consumers -/

/-- The zero-dimensionality conclusion reformulated: over `J`, every
minimal prime is the maximal ideal itself (maximality is unique in a
local ring).
-/
theorem krullDimLE_zero_quotient_iff_minimalPrimes_eq_maximal {R : Type*}
    [CommRing R] [IsLocalRing R] (J : Ideal R) :
    Ring.KrullDimLE 0 (R ⧸ J) ↔
      ∀ Q ∈ J.minimalPrimes, Q = IsLocalRing.maximalIdeal R := by
  rw [Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal]
  constructor
  · intro h Q hQ
    exact IsLocalRing.eq_maximalIdeal (h Q hQ)
  · intro h Q hQ
    rw [h Q hQ]
    exact IsLocalRing.maximalIdeal.isMaximal R

#print axioms exists_krullDimLE_of_finiteRingKrullDim
#print axioms exists_mem_maximal_avoid_minimalPrimes_ne_maximal
#print axioms krullDimLE_quotient_sup_span_singleton
#print axioms exists_systemOfParameters_of_krullDimLE
#print axioms krullDimLE_quotient_bot_of_krullDimLE
#print axioms exists_systemOfParameters_of_finite
#print axioms exists_systemOfParameters_length_eq_krullDim
#print axioms exists_systemOfParameters_list_of_krullDimLE
#print axioms krullDimLE_zero_quotient_iff_minimalPrimes_eq_maximal

end SystemOfParametersExistence
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
