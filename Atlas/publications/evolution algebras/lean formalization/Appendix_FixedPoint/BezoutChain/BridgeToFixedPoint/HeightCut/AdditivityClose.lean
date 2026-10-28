/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoid.A3aCloserDimKit
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.HeightCut.HeightCutDischarge
import Appendix_FixedPoint.BezoutChain.Dimension.HeightLowerBound
import Appendix_FixedPoint.BezoutChain.Dimension.IntegralDimension
import Appendix_FixedPoint.BezoutChain.Dimension.PolynomialCatenary
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Data.ENat.Basic
import Mathlib.Data.ENat.Monoid
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Order.KrullDimension
import Mathlib.Order.RelSeries
import Mathlib.Order.WithBot
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid

/-!
# R-B2: `HeightCutAdditivity` at general `t`

This module proves the `HeightCutAdditivity` gap of
`A3aCloserDimKit`, making its three
conditional results (`height_le_of_mem_minimalPrimes_cut`,
`bridgeNotMem_zMem_of_algebraData`,
`zMemAvoidCloser_of_algebraData`) unconditional.

## Route (nothing removable)

For primes `Q ≤ P'` in `R = MvPolynomial (Fin (t + 2)) K`, with
`D = R ⧸ Q` and `Pbar = P'.map (mk Q)`:

1. Lemma F-general (`dim_le_height_add_dim_quotient_map`): the
   going-down core at general arity and symbolic `Pbar.height`,
   `dim D ≤ height(Pbar) + dim(D/Pbar)`. Noether normalization
   presents `D` as integral over `A = MvPolynomial (Fin s) K`.
   For `s ≥ 2` the poly base is normal (UFD chain), so going-down
   gives `height(q) ≤ height(Pbar)` for the contraction `q`
   (`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`;
   going-up would prove the reverse inequality and cannot be
   substituted); going-up chain lifting on the quotient algebras
   gives `dim(A/q) ≤ dim(D/Pbar)`; the unconditional catenary
   equality at `A` (`hlow_uncond` +
   `mvPolynomial_catenary_eq_of_lower_bound`) closes by rewriting.
   For `s = 0` and `s = 1` (where `hlow_uncond` cannot fire) the
   bound closes by direct `WithBot` arithmetic from
   `Pbar.height ≥ 0` and `dim(D/Pbar) ≥ 0`, splitting on
   `Pbar = ⊥` in the `s = 1` case.
2. Lemma C (`height_le_of_add_dim_le`): generalized mirror
   cancellation on `WithBot ℕ∞` (from `h + d = ↑N` and
   `↑N ≤ K + d`, conclude `h ≤ K`).
3. Assembly (`heightCutAdditivity`): F-general plus Lemma T reused
   by import (`HeightCutDischarge.dim_quotient_quotient`) plus the
   catenary equation at `Q` and `P'` plus Lemma C.

## Correctness note

`height(P') ≤ height(Q) + height(P'/Q)` is false in general
(counterexample `R₀ = k[a,b,c]/(ac,bc)`), so the
ambient catenary pair (at `Q` and `P'`) is forced: the proof
invokes `hlow_uncond` plus the catenary equation only on poly
rings, hypotheses the counterexample cannot satisfy.

Assumptions: `[IsAlgClosed K]` [algClosed] (via `hlow_uncond`;
already in the consumers' context). No depth, regular sequences,
minimal-equals-associated, or Cohen-Macaulay content is used.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace AdditivityClose

open scoped BigOperators

/-- Nonnegativity of quotient dimension (shared by the `s = 0` and
`s = 1` closes): quotients by primes have non-`⊥` dimension. The
prime spectrum is nonempty (`Nontrivial` via the quotient domain),
so the singleton series of length `0` bounds `krullDim` from below.
Stated in direct-cast form to match the `WithBot` goal sides. -/
theorem dim_map_quot_nonneg (n : ℕ) (K : Type*) [Field K]
    (Q : Ideal (MvPolynomial (Fin n) K))
    (Pbar : Ideal (MvPolynomial (Fin n) K ⧸ Q)) [Pbar.IsPrime] :
    ((0 : ℕ) : WithBot ℕ∞) ≤
      ringKrullDim ((MvPolynomial (Fin n) K ⧸ Q) ⧸ Pbar) := by
  have hne : Nonempty (PrimeSpectrum ((MvPolynomial (Fin n) K ⧸ Q) ⧸ Pbar)) :=
    PrimeSpectrum.nonempty_iff_nontrivial.mpr inferInstance
  obtain ⟨a⟩ := hne
  have hL := Order.LTSeries.length_le_krullDim (RelSeries.singleton _ a :
    LTSeries (PrimeSpectrum ((MvPolynomial (Fin n) K ⧸ Q) ⧸ Pbar)))
  have hlen : (RelSeries.singleton _ a :
    LTSeries (PrimeSpectrum ((MvPolynomial (Fin n) K ⧸ Q) ⧸ Pbar))).length
      = 0 := rfl
  rw [hlen] at hL
  unfold ringKrullDim
  simpa using hL

#print axioms dim_map_quot_nonneg

/-- Direct-cast `0 ≤ height`: every ideal height is bounded below by
`((0 : ℕ) : WithBot ℕ∞)`. Feeds the paired `WithBot` steps in the
`s = 0` and `s = 1` closes (one-sided `le_add_right`-style bounds
are false over `WithBot`). -/
theorem zero_le_height_direct (D : Type*) [CommRing D] (P : Ideal D) :
    ((0 : ℕ) : WithBot ℕ∞) ≤ (P.height : WithBot ℕ∞) := by
  have hz : ((0 : ℕ) : ℕ∞) ≤ P.height := by
    rw [Nat.cast_zero]
    exact zero_le
  have hc := WithBot.coe_le_coe.mpr hz
  rwa [WithBot.coe_natCast] at hc

#print axioms zero_le_height_direct

/-- Normalization fiber inequality (Lemma F-general, going-down core):
for `D = R ⧸ Q` with `R` a poly ring over a field and
`Pbar ∈ Spec(D)`, `dim D ≤ height(Pbar) + dim(D/Pbar)` at general
arity and symbolic `Pbar.height`.

Route: Noether normalization presents `D` as integral over
`A = MvPolynomial (Fin s) K`. For `s ≥ 2` the poly base is normal
(UFD chain), so going-down applies (Matsumura Thm 9.4,
`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`), giving
`height(q) ≤ height(Pbar)` for the contraction `q`; going-up chain
lifting on the quotient algebras gives `dim(A/q) ≤ dim(D/Pbar)`; the
unconditional catenary equality at `A` (`hlow_uncond` +
`mvPolynomial_catenary_eq_of_lower_bound`) closes by rewriting the
goal and pairing both sides via `add_le_add`. For `s = 0` and
`s = 1` the bound closes by direct `WithBot` arithmetic
(`zero_le_height_direct` + `dim_map_quot_nonneg`), splitting on
`Pbar = ⊥` when `s = 1`. Needs `[IsAlgClosed K]` [algClosed] via
`hlow_uncond`. -/
theorem dim_le_height_add_dim_quotient_map (n : ℕ) (K : Type*) [Field K]
    [IsAlgClosed K]
    (Q : Ideal (MvPolynomial (Fin n) K)) [Q.IsPrime]
    (Pbar : Ideal (MvPolynomial (Fin n) K ⧸ Q)) [Pbar.IsPrime] :
    ringKrullDim (MvPolynomial (Fin n) K ⧸ Q) ≤
      (Pbar.height : WithBot ℕ∞) +
        ringKrullDim ((MvPolynomial (Fin n) K ⧸ Q) ⧸ Pbar) := by
  have hQne : Q ≠ ⊤ := ‹Q.IsPrime›.ne_top
  obtain ⟨s, _, g, hinj, hint⟩ := exists_integral_inj_algHom_of_quotient Q hQne
  have hdimD : ringKrullDim (MvPolynomial (Fin n) K ⧸ Q) = (s : WithBot ℕ∞) := by
    rw [ringKrullDim_eq_of_algHom_isIntegral g hinj hint, mvPolynomial_ringKrullDim]
  rw [hdimD]
  by_cases hs2 : 2 ≤ s
  · obtain ⟨u, rfl⟩ : ∃ u, s = u + 2 := ⟨s - 2, (Nat.sub_add_cancel hs2).symm⟩
    let : Algebra (MvPolynomial (Fin (u + 2)) K)
        (MvPolynomial (Fin n) K ⧸ Q) :=
      g.toRingHom.toAlgebra
    have : Algebra.IsIntegral (MvPolynomial (Fin (u + 2)) K)
        (MvPolynomial (Fin n) K ⧸ Q) := by
      rw [← algebraMap_isIntegral_iff, RingHom.algebraMap_toAlgebra]
      exact hint
    have : FaithfulSMul (MvPolynomial (Fin (u + 2)) K)
        (MvPolynomial (Fin n) K ⧸ Q) := by
      rw [faithfulSMul_iff_algebraMap_injective, RingHom.algebraMap_toAlgebra]
      exact hinj
    have : IsNoetherianRing (MvPolynomial (Fin n) K ⧸ Q) :=
      isNoetherianRing_of_surjective _ _ (Ideal.Quotient.mk Q)
        Ideal.Quotient.mk_surjective
    have hGD := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
      (Pbar.under (MvPolynomial (Fin (u + 2)) K)) Pbar
    have h4 : (Pbar.under (MvPolynomial (Fin (u + 2)) K)).height ≤ Pbar.height := by
      rw [hGD]
      exact le_self_add
    have h5 : ringKrullDim ((MvPolynomial (Fin (u + 2)) K) ⧸
          Pbar.under (MvPolynomial (Fin (u + 2)) K)) ≤
        ringKrullDim ((MvPolynomial (Fin n) K ⧸ Q) ⧸ Pbar) := by
      have key : ∀ l : LTSeries (PrimeSpectrum ((MvPolynomial (Fin (u + 2)) K) ⧸
            Pbar.under (MvPolynomial (Fin (u + 2)) K))),
          ∃ L : LTSeries (PrimeSpectrum ((MvPolynomial (Fin n) K ⧸ Q) ⧸ Pbar)),
            L.length = l.length := by
        intro l
        have hbot : (⊥ : Ideal ((MvPolynomial (Fin n) K ⧸ Q) ⧸ Pbar)).under
            ((MvPolynomial (Fin (u + 2)) K) ⧸
              Pbar.under (MvPolynomial (Fin (u + 2)) K)) ≤
            (RelSeries.head l).asIdeal := by
          rw [Ideal.under_bot]
          exact bot_le
        obtain ⟨Q0, -, hQ0prime, hQ0under⟩ :=
          Ideal.exists_ideal_over_prime_of_isIntegral (RelSeries.head l).asIdeal ⊥ hbot
        have := hQ0prime
        have hLO0 : Q0.LiesOver (RelSeries.head l).asIdeal := ⟨hQ0under.symm⟩
        have := hLO0
        obtain ⟨L, hlen, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l Q0
        exact ⟨L, hlen⟩
      unfold ringKrullDim Order.krullDim
      refine iSup_le fun l => ?_
      obtain ⟨L, hlen⟩ := key l
      rw [← hlen]
      exact Order.LTSeries.length_le_krullDim L
    have hlowA := hlow_uncond u K (Pbar.under (MvPolynomial (Fin (u + 2)) K))
    have hcatA := mvPolynomial_catenary_eq_of_lower_bound K (u + 2)
      (Pbar.under (MvPolynomial (Fin (u + 2)) K)) hlowA
    rw [← hcatA]
    exact add_le_add (WithBot.coe_le_coe.mpr h4) h5
  · have hs10 : s ≤ 1 := by omega
    have hs01 : s = 0 ∨ s = 1 := by omega
    rcases hs01 with rfl | rfl
    · have hH := zero_le_height_direct (MvPolynomial (Fin n) K ⧸ Q) Pbar
      have hD0 := dim_map_quot_nonneg n K Q Pbar
      have h := add_le_add hH hD0
      simpa using h
    · by_cases hbot : Pbar = ⊥
      · subst hbot
        have hD : ringKrullDim ((MvPolynomial (Fin n) K ⧸ Q) ⧸
              (⊥ : Ideal (MvPolynomial (Fin n) K ⧸ Q))) =
            ringKrullDim (MvPolynomial (Fin n) K ⧸ Q) :=
          ringKrullDim_eq_of_ringEquiv
            (RingEquiv.quotientBot (MvPolynomial (Fin n) K ⧸ Q))
        rw [hD, hdimD]
        have hH := zero_le_height_direct (MvPolynomial (Fin n) K ⧸ Q) ⊥
        have h := add_le_add hH
          (le_rfl : ((1 : ℕ) : WithBot ℕ∞) ≤ ((1 : ℕ) : WithBot ℕ∞))
        have h01 : ((0 : ℕ) : WithBot ℕ∞) + ((1 : ℕ) : WithBot ℕ∞) =
            ((1 : ℕ) : WithBot ℕ∞) := by simp
        rw [h01] at h
        exact h
      · have hlt : (⊥ : Ideal (MvPolynomial (Fin n) K ⧸ Q)) < Pbar :=
          bot_lt_iff_ne_bot.mpr hbot
        have hstep := Ideal.height_add_one_le_of_lt_of_isPrime hlt
        have h1e : ((1 : ℕ) : ℕ∞) ≤ Pbar.height := by
          have h0 : (0 : ℕ∞) + 1 ≤
              (⊥ : Ideal (MvPolynomial (Fin n) K ⧸ Q)).height + 1 :=
            add_le_add_left zero_le _
          have h1 := h0.trans hstep
          simpa using h1
        have hc := WithBot.coe_le_coe.mpr h1e
        rw [WithBot.coe_natCast] at hc
        have hD0 := dim_map_quot_nonneg n K Q Pbar
        have h := add_le_add hc hD0
        simpa using h

#print axioms dim_le_height_add_dim_quotient_map

/-- Generalized mirror cancellation on `WithBot ℕ∞` (Lemma C): from
`h + d = ↑N` and `↑N ≤ K + d`, conclude `h ≤ K`. All sides with `⊥`
contradict finiteness of `↑N`; the `coe` case descends to `ℕ∞`
where `↑N` cancels on the right (`ENat.add_le_add_iff_right`),
splitting on whether the cancelled term is `⊤`. The RHS uses the
direct `ℕ` cast to match the catenary equation's output form. -/
theorem height_le_of_add_dim_le (h d K : WithBot ℕ∞) (N : ℕ)
    (hcat : h + d = ((N : ℕ) : WithBot ℕ∞))
    (hle : ((N : ℕ) : WithBot ℕ∞) ≤ K + d) : h ≤ K := by
  have hNbot : ((N : ℕ) : WithBot ℕ∞) ≠ ⊥ := WithBot.natCast_ne_bot N
  cases h with
  | bot =>
      rw [WithBot.bot_add] at hcat
      exact (hNbot hcat.symm).elim
  | coe h' =>
      cases d with
      | bot =>
          rw [WithBot.add_bot] at hcat
          exact (hNbot hcat.symm).elim
      | coe d' =>
          cases K with
          | bot =>
              rw [WithBot.bot_add] at hle
              have hcon : ((N : ℕ) : WithBot ℕ∞) = ⊥ := le_bot_iff.mp hle
              exact (hNbot hcon).elim
          | coe k' =>
              rw [← WithBot.coe_natCast, ← WithBot.coe_add,
                WithBot.coe_eq_coe] at hcat
              rw [← WithBot.coe_natCast, ← WithBot.coe_add,
                WithBot.coe_le_coe] at hle
              rw [WithBot.coe_le_coe]
              cases d' with
              | top =>
                  simp at hcat
              | coe m =>
                  rw [← hcat] at hle
                  exact (ENat.add_le_add_iff_right (ENat.natCast_ne_top m)).mp hle

#print axioms height_le_of_add_dim_le

/-- Height additivity under containment (general-`t`
`HeightCutAdditivity`, unconditional): for primes `Q ≤ P'` in
`MvPolynomial (Fin (t + 2)) K`,
`height(P') ≤ height(Q) + height(P'/Q)`.

Assembles Lemma F-general
(`dim_le_height_add_dim_quotient_map`), Lemma T reused by import
(`HeightCutDischarge.dim_quotient_quotient`), the catenary equation at
`Q` and `P'` (`hlow_uncond` +
`mvPolynomial_catenary_eq_of_lower_bound`), and Lemma C
(`height_le_of_add_dim_le`). Discharges the `hadd` hypothesis of
`A3aCloserDimKit.height_le_of_mem_minimalPrimes_cut`,
`A3aCloserDimKit.bridgeNotMem_zMem_of_algebraData`, and
`A3aCloserDimKit.zMemAvoidCloser_of_algebraData` (via
instantiation in a follow-up). Needs `[IsAlgClosed K]` [algClosed]
via `hlow_uncond`. -/
theorem heightCutAdditivity (t : ℕ) (K : Type*) [Field K] [IsAlgClosed K] :
    A3aCloserDimKit.HeightCutAdditivity t K := by
  intro Q P' hQ hP hle
  have := hQ
  have := hP
  have : (Ideal.map (Ideal.Quotient.mk Q) P').IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime hle
  have hcatQ := mvPolynomial_catenary_eq_of_lower_bound K (t + 2) Q
    (hlow_uncond t K Q)
  have hcatP := mvPolynomial_catenary_eq_of_lower_bound K (t + 2) P'
    (hlow_uncond t K P')
  have hT := HeightCutDischarge.dim_quotient_quotient (t + 2) K Q P' hle
  have hF := dim_le_height_add_dim_quotient_map (t + 2) K Q
    (Ideal.map (Ideal.Quotient.mk Q) P')
  have hchain : ((t + 2 : ℕ) : WithBot ℕ∞) ≤
      ((Q.height : WithBot ℕ∞) +
        ((Ideal.map (Ideal.Quotient.mk Q) P').height : WithBot ℕ∞)) +
        ringKrullDim (MvPolynomial (Fin (t + 2)) K ⧸ P') := by
    rw [← hcatQ]
    calc (Q.height : WithBot ℕ∞) +
            ringKrullDim (MvPolynomial (Fin (t + 2)) K ⧸ Q)
        ≤ (Q.height : WithBot ℕ∞) +
            (((Ideal.map (Ideal.Quotient.mk Q) P').height : WithBot ℕ∞) +
              ringKrullDim ((MvPolynomial (Fin (t + 2)) K ⧸ Q) ⧸
                Ideal.map (Ideal.Quotient.mk Q) P')) :=
          add_le_add_right hF _
      _ = ((Q.height : WithBot ℕ∞) +
              ((Ideal.map (Ideal.Quotient.mk Q) P').height : WithBot ℕ∞)) +
            ringKrullDim ((MvPolynomial (Fin (t + 2)) K ⧸ Q) ⧸
              Ideal.map (Ideal.Quotient.mk Q) P') := by
          rw [add_assoc]
      _ = ((Q.height : WithBot ℕ∞) +
              ((Ideal.map (Ideal.Quotient.mk Q) P').height : WithBot ℕ∞)) +
            ringKrullDim (MvPolynomial (Fin (t + 2)) K ⧸ P') := by
          rw [hT]
  have hconcl := height_le_of_add_dim_le _ _ _ (t + 2) hcatP hchain
  rw [← WithBot.coe_add] at hconcl
  exact WithBot.coe_le_coe.mp hconcl

#print axioms heightCutAdditivity

/-- A3a per-rung avoidance, unconditional: discharges `[hadd]` with
`heightCutAdditivity`. Added by parent integrator at integration.

note: `_hj` (`2 ≤ j.val`) is carried unused for address
compatibility with E10's `hA3a` — the contraction-free count
needs no lower bound on `j` (same note as upstream
`RB2DimA3.bridgeNotMem_zMem_of_algebraData`). -/
theorem bridgeNotMem_zMem_unconditional
    (K E : Type*) [Field K] [IsAlgClosed K]
    [NonUnitalNonAssocSemiring E] [Module K E]
    [IsScalarTower K E E] [SMulCommClass K E E]
    (n : ℕ) (hn : 0 < n)
    (c : Fin n → Fin n → Fin n → K)
    (V : Submodule K E) (b : Module.Basis (Fin n) K V)
    (hexp : ∀ i j, (b i : E) * (b j : E) = ∑ k, c i j k • (b k : E))
    (hN : absNilpotent K E V = {0})
    (j : Fin (statementIndex n + 1)) (_hj : 2 ≤ j.val)
    (Q : Ideal (MvPolynomial (Fin (statementIndex n + 2)) K))
    (hQmin : Q ∈ (MinAvoidRungs.stageIdeal n K c hn j).minimalPrimes)
    (hz : AvoidanceCoreDimGe3.zVarPoly n K ∈ Q) :
    (bridgeSystem n K c hn) j ∉ Q :=
  A3aCloserDimKit.bridgeNotMem_zMem_of_algebraData K E n hn c V b hexp hN
    j _hj Q hQmin hz (heightCutAdditivity (statementIndex n) K)

#print axioms bridgeNotMem_zMem_unconditional

/-- A3a ∀-form closer, unconditional: discharges `[hadd]` with
`heightCutAdditivity`. Added by parent integrator at integration. -/
theorem zMemAvoidCloser_unconditional
    (K E : Type*) [Field K] [IsAlgClosed K]
    [NonUnitalNonAssocSemiring E] [Module K E]
    [IsScalarTower K E E] [SMulCommClass K E E]
    (n : ℕ) (hn : 0 < n)
    (c : Fin n → Fin n → Fin n → K)
    (V : Submodule K E) (b : Module.Basis (Fin n) K V)
    (hexp : ∀ i j, (b i : E) * (b j : E) = ∑ k, c i j k • (b k : E))
    (hN : absNilpotent K E V = {0}) :
    ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      ¬ (MinAvoidRungs.stageIdeal n K c hn j).IsPrime →
      AvoidanceCoreDimGe3.ZMemAvoidCloser n K c hn j :=
  A3aCloserDimKit.zMemAvoidCloser_of_algebraData K E n hn c V b hexp hN
    (heightCutAdditivity (statementIndex n) K)

#print axioms zMemAvoidCloser_unconditional

/-- D3 PIT-cut bound, unconditional (adds the `[IsAlgClosed K]` binder the
`heightCutAdditivity` proof requires, per verdict correction C3). Added by
parent integrator at integration. -/
theorem height_le_of_mem_minimalPrimes_cut_unconditional (t : ℕ) (K : Type*)
    [Field K] [IsAlgClosed K]
    (Q P' : Ideal (MvPolynomial (Fin (t + 2)) K))
    [Q.IsPrime] [P'.IsPrime]
    (cuts : Finset (MvPolynomial (Fin (t + 2)) K))
    (hP' : P' ∈ (Q ⊔ Ideal.span (↑cuts : Set (MvPolynomial (Fin (t + 2)) K))).minimalPrimes) :
    P'.height ≤ Q.height + ((cuts.card : ℕ) : ℕ∞) :=
  A3aCloserDimKit.height_le_of_mem_minimalPrimes_cut t K Q P' cuts hP'
    (heightCutAdditivity t K)

#print axioms height_le_of_mem_minimalPrimes_cut_unconditional

end AdditivityClose
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
