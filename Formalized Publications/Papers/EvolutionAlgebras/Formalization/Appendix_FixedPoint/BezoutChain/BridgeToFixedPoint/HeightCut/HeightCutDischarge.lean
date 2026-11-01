/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoidRungs
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.HeightCut.ConeCutAvoidance
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
import Mathlib.Order.WithBot
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid

/-!
# R-B3: discharge of `[hcut]` — `height(P') ≤ 3` for `P' ∈ Min(Q + (z))`

This module makes `ConeCutAvoidance.minAvoidRung_two_of_cut` unconditional by
proving its `[hcut]` hypothesis.

## Route (nothing removable)

For `Q ∈ Min(J₂)` and `P' ∈ Min(Q + (z))`, with `D = R ⧸ Q` and
`Pbar = P'.map (mk Q)`:

1. `height(Pbar) ≤ 1` by Krull's PIT
   (`Ideal.map_height_le_one_of_mem_minimalPrimes`).
2. Noether normalization presents `D` as integral over
   `A = MvPolynomial (Fin s) K`, with `dim D = s`.
3. The poly base `A` is normal (UFD chain, `infer_instance`), so the
   normalization satisfies going-down
   (`Algebra.HasGoingDown A D`, Matsumura Thm 9.4).
4. Going-down gives `height(q) ≤ height(Pbar)` for the contraction `q`
   (`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`). Going-up would
   prove the reverse inequality and cannot be substituted.
5. Going-up chain lifting on the quotient algebras gives
   `dim(A/q) ≤ dim(D/Pbar)` (no Mathlib shortcut; built by hand).
6. The unconditional catenary equality at `A` (`hlow_uncond` +
   `mvPolynomial_catenary_eq_of_lower_bound`) plus the proved cancellation
   (`ConeCutAvoidance.dim_ge_of_height_add_dim_eq`) forces `dim(D/Pbar) ≥ 1`.
7. Third-isomorphism transport (`DoubleQuot.quotQuotEquivQuotOfLE`) moves this
   to `dim(R/P') ≥ 1`; the catenary equality at `P'` plus the mirror
   cancellation (`height_le_of_add_dim_eq` below) closes `height(P') ≤ 3`.

## Correctness note

`height(P') ≤ height(Q) + height(P'/Q)` is false in general (counterexample
`R₀ = k[a,b,c]/(ac,bc)`), so no direct chain-combinatorics proof
exists: catenary input through the normal base (steps 2-6) is forced.

Assumptions: `[IsAlgClosed K]` [algClosed] (via `hlow_uncond` and
`ConeCutAvoidance.quot_dim_ge_two`; already in `[hcut]`'s context). No depth,
regular sequences, `Min = Ass`, or Cohen-Macaulay content is used.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace HeightCutDischarge

open scoped BigOperators

/-- Cancellation for `WithBot ℕ∞` (mirror image of
`ConeCutAvoidance.dim_ge_of_height_add_dim_eq`): from `h + d = ↑N` and `↑m ≤ d`
with `k + m = N`, conclude `h ≤ ↑k`. Both sides are lifted to `ℕ∞` (all cases
with `⊥` contradict finiteness of `↑N`) and `ENat` cancels `↑m` on the
right. -/
theorem height_le_of_add_dim_eq (h d : WithBot ℕ∞) (k m N : ℕ)
    (hN : k + m = N)
    (hcat : h + d = ((((N : ℕ)) : ℕ∞) : WithBot ℕ∞))
    (hle : ((((m : ℕ)) : ℕ∞) : WithBot ℕ∞) ≤ d) :
    h ≤ ((((k : ℕ)) : ℕ∞) : WithBot ℕ∞) := by
  have hNbot : ((((N : ℕ)) : ℕ∞) : WithBot ℕ∞) ≠ ⊥ := WithBot.coe_ne_bot
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
          rw [← WithBot.coe_add, WithBot.coe_eq_coe] at hcat
          rw [WithBot.coe_le_coe] at hle
          rw [WithBot.coe_le_coe]
          have hN' : ((N : ℕ) : ℕ∞) = ((k : ℕ) : ℕ∞) + ((m : ℕ) : ℕ∞) := by
            rw [← hN, Nat.cast_add]
          rw [hN'] at hcat
          have hle2 : h' + ((m : ℕ) : ℕ∞) ≤ ((k : ℕ) : ℕ∞) + ((m : ℕ) : ℕ∞) := by
            rw [← hcat]
            exact add_le_add_right hle h'
          exact (ENat.add_le_add_iff_right (ENat.natCast_ne_top _)).mp hle2

#print axioms height_le_of_add_dim_eq

/-- Third-isomorphism transport (Lemma T): quotienting `R ⧸ Q` by the image of
`P'` has the same Krull dimension as `R ⧸ P'`, via
`DoubleQuot.quotQuotEquivQuotOfLE` ("The Third Isomorphism theorem for
rings"). -/
theorem dim_quotient_quotient (n : ℕ) (K : Type*) [Field K]
    (Q P' : Ideal (MvPolynomial (Fin n) K)) (hle : Q ≤ P') :
    ringKrullDim ((MvPolynomial (Fin n) K ⧸ Q) ⧸ P'.map (Ideal.Quotient.mk Q)) =
      ringKrullDim (MvPolynomial (Fin n) K ⧸ P') :=
  ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hle)

#print axioms dim_quotient_quotient

set_option maxSynthPendingDepth 3 in
/-- Normalization fiber inequality (Lemma F, going-down core): for
`D = R ⧸ Q` with `ringKrullDim D ≥ 2` and `Pbar ∈ Spec(D)` of height `≤ 1`,
the quotient `D ⧸ Pbar` has dimension `≥ 1`.

Route: Noether normalization presents `D` as integral over
`A = MvPolynomial (Fin s) K`; the poly base is normal (UFD chain), so
going-down applies (Matsumura Thm 9.4,
`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`), giving
`height(q) ≤ height(Pbar)` for the contraction `q`; going-up chain lifting on
the quotient algebras gives `dim(A/q) ≤ dim(D/Pbar)`; the unconditional
catenary equality at `A` (`hlow_uncond` +
`mvPolynomial_catenary_eq_of_lower_bound`) then forces `dim(D/Pbar) ≥ 1` via
`ConeCutAvoidance.dim_ge_of_height_add_dim_eq`. Needs `[IsAlgClosed K]`
[algClosed] via `hlow_uncond`. -/
theorem one_le_dim_quotient_map_of_height_le_one (n : ℕ) (K : Type*) [Field K]
    [IsAlgClosed K]
    (Q : Ideal (MvPolynomial (Fin n) K)) [Q.IsPrime]
    (Pbar : Ideal (MvPolynomial (Fin n) K ⧸ Q)) [Pbar.IsPrime]
    (hP1 : Pbar.height ≤ 1)
    (hs : ((((2 : ℕ)) : ℕ∞) : WithBot ℕ∞) ≤
      ringKrullDim (MvPolynomial (Fin n) K ⧸ Q)) :
    ((((1 : ℕ)) : ℕ∞) : WithBot ℕ∞) ≤
      ringKrullDim ((MvPolynomial (Fin n) K ⧸ Q) ⧸ Pbar) := by
  have hQne : Q ≠ ⊤ := ‹Q.IsPrime›.ne_top
  obtain ⟨s, _, g, hinj, hint⟩ := exists_integral_inj_algHom_of_quotient Q hQne
  have hdimD : ringKrullDim (MvPolynomial (Fin n) K ⧸ Q) = (s : WithBot ℕ∞) := by
    rw [ringKrullDim_eq_of_algHom_isIntegral g hinj hint, mvPolynomial_ringKrullDim]
  have h2s : ((((2 : ℕ)) : ℕ∞) : WithBot ℕ∞) ≤ (s : WithBot ℕ∞) := by
    rw [← hdimD]
    exact hs
  have hs2 : 2 ≤ s := by
    rw [← WithBot.coe_natCast s] at h2s
    rw [WithBot.coe_le_coe] at h2s
    exact_mod_cast h2s
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 2 := ⟨s - 2, (Nat.sub_add_cancel hs2).symm⟩
  let : Algebra (MvPolynomial (Fin (t + 2)) K) (MvPolynomial (Fin n) K ⧸ Q) :=
    g.toRingHom.toAlgebra
  have : Algebra.IsIntegral (MvPolynomial (Fin (t + 2)) K)
      (MvPolynomial (Fin n) K ⧸ Q) := by
    rw [← algebraMap_isIntegral_iff, RingHom.algebraMap_toAlgebra]
    exact hint
  have : FaithfulSMul (MvPolynomial (Fin (t + 2)) K)
      (MvPolynomial (Fin n) K ⧸ Q) := by
    rw [faithfulSMul_iff_algebraMap_injective, RingHom.algebraMap_toAlgebra]
    exact hinj
  have : IsNoetherianRing (MvPolynomial (Fin n) K ⧸ Q) :=
    isNoetherianRing_of_surjective _ _ (Ideal.Quotient.mk Q)
      Ideal.Quotient.mk_surjective
  have hGD := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    (Pbar.under (MvPolynomial (Fin (t + 2)) K)) Pbar
  have h4 : (Pbar.under (MvPolynomial (Fin (t + 2)) K)).height ≤ Pbar.height := by
    rw [hGD]
    exact le_self_add
  have h5 : ringKrullDim ((MvPolynomial (Fin (t + 2)) K) ⧸
        Pbar.under (MvPolynomial (Fin (t + 2)) K)) ≤
      ringKrullDim ((MvPolynomial (Fin n) K ⧸ Q) ⧸ Pbar) := by
    have key : ∀ l : LTSeries (PrimeSpectrum ((MvPolynomial (Fin (t + 2)) K) ⧸
          Pbar.under (MvPolynomial (Fin (t + 2)) K))),
        ∃ L : LTSeries (PrimeSpectrum ((MvPolynomial (Fin n) K ⧸ Q) ⧸ Pbar)),
          L.length = l.length := by
      intro l
      have hbot : (⊥ : Ideal ((MvPolynomial (Fin n) K ⧸ Q) ⧸ Pbar)).under
          ((MvPolynomial (Fin (t + 2)) K) ⧸
            Pbar.under (MvPolynomial (Fin (t + 2)) K)) ≤
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
  have hlowA := hlow_uncond t K (Pbar.under (MvPolynomial (Fin (t + 2)) K))
  have hcatA := mvPolynomial_catenary_eq_of_lower_bound K (t + 2)
    (Pbar.under (MvPolynomial (Fin (t + 2)) K)) hlowA
  have hP1c : Pbar.height ≤ ((1 : ℕ) : ℕ∞) := by exact_mod_cast hP1
  have hq1 : ((Pbar.under (MvPolynomial (Fin (t + 2)) K)).height : WithBot ℕ∞) ≤
      ((((1 : ℕ)) : ℕ∞) : WithBot ℕ∞) :=
    le_trans (WithBot.coe_le_coe.mpr h4) (WithBot.coe_le_coe.mpr hP1c)
  have hcatA' : ((Pbar.under (MvPolynomial (Fin (t + 2)) K)).height : WithBot ℕ∞) +
        ringKrullDim ((MvPolynomial (Fin (t + 2)) K) ⧸
          Pbar.under (MvPolynomial (Fin (t + 2)) K)) =
      ((((t + 2 : ℕ)) : ℕ∞) : WithBot ℕ∞) := by
    rw [WithBot.coe_natCast]
    exact hcatA
  have hNt : 1 + (t + 2 - 1) = t + 2 := by omega
  have hge := ConeCutAvoidance.dim_ge_of_height_add_dim_eq _ _ 1 (t + 2 - 1) (t + 2)
    hNt hcatA' hq1
  have h1t : ((((1 : ℕ)) : ℕ∞) : WithBot ℕ∞) ≤
      ((((t + 2 - 1 : ℕ)) : ℕ∞) : WithBot ℕ∞) := by
    rw [WithBot.coe_le_coe]
    exact_mod_cast (show 1 ≤ t + 2 - 1 by omega)
  exact le_trans h1t (le_trans hge h5)

#print axioms one_le_dim_quotient_map_of_height_le_one

/-- R-B3 height cut (`[hcut]` discharged, unconditional): for `Q ∈ Min(J₂)` at
rung `j`, `j.val = 2`, and `P' ∈ Min(Q + (z))`, `height(P') ≤ 3`.

Assembles Lemma F (`one_le_dim_quotient_map_of_height_le_one`, fed by PIT
`Ideal.map_height_le_one_of_mem_minimalPrimes` and
`ConeCutAvoidance.quot_dim_ge_two`), Lemma T (`dim_quotient_quotient`), the
catenary equality at `P'` (`hlow_uncond` +
`mvPolynomial_catenary_eq_of_lower_bound`), and the mirror cancellation
(`height_le_of_add_dim_eq`). Needs `[IsAlgClosed K]` [algClosed] (via
`hlow_uncond` / `quot_dim_ge_two`; already in `[hcut]`'s context). -/
theorem height_cut_le_three (K : Type*) [Field K] [IsAlgClosed K]
    (c : Fin 3 → Fin 3 → Fin 3 → K) (hn : 0 < 3)
    (j : Fin (statementIndex 3 + 1)) (hj : j.val = 2)
    (Q : Ideal (MvPolynomial (Fin (statementIndex 3 + 2)) K))
    (hQ : Q ∈ (MinAvoidRungs.stageIdeal 3 K c hn j).minimalPrimes)
    (P' : Ideal (MvPolynomial (Fin (statementIndex 3 + 2)) K))
    (hP' : P' ∈ (Q ⊔ Ideal.span {ConeCutAvoidance.zVar K}).minimalPrimes) :
    P'.height ≤ ((3 : ℕ) : ℕ∞) := by
  have : Q.IsPrime := hQ.isPrime
  have hP'prime : P'.IsPrime := hP'.isPrime
  have hleQP : Q ≤ P' := le_sup_left.trans hP'.le
  have hP1 : (P'.map (Ideal.Quotient.mk Q)).height ≤ 1 :=
    Ideal.map_height_le_one_of_mem_minimalPrimes hP'
  have : (P'.map (Ideal.Quotient.mk Q)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rw [Q.mk_ker]; exact hleQP)
  have hs := ConeCutAvoidance.quot_dim_ge_two K c hn j hj Q hQ
  have hF := one_le_dim_quotient_map_of_height_le_one (statementIndex 3 + 2) K Q
    (P'.map (Ideal.Quotient.mk Q)) hP1 hs
  have hT := dim_quotient_quotient (statementIndex 3 + 2) K Q P' hleQP
  have hD1 : ((((1 : ℕ)) : ℕ∞) : WithBot ℕ∞) ≤
      ringKrullDim (MvPolynomial (Fin (statementIndex 3 + 2)) K ⧸ P') := by
    rw [← hT]
    exact hF
  have hlow := @hlow_uncond 2 K _ _ P' hP'prime
  have hcat := @mvPolynomial_catenary_eq_of_lower_bound K _
    (statementIndex 3 + 2) P' hP'prime hlow
  have hN : statementIndex 3 + 2 = 4 := by decide
  have hcat' : ((P'.height : WithBot ℕ∞)) +
      ringKrullDim (MvPolynomial (Fin (statementIndex 3 + 2)) K ⧸ P')
      = ((((4 : ℕ)) : ℕ∞) : WithBot ℕ∞) := by
    have hRHS : (((statementIndex 3 + 2 : ℕ)) : WithBot ℕ∞)
        = ((((4 : ℕ)) : ℕ∞) : WithBot ℕ∞) := by
      rw [hN]
      exact (WithBot.coe_natCast 4).symm
    rw [hRHS] at hcat
    exact hcat
  have h31 : 3 + 1 = 4 := rfl
  have hconcl : ((P'.height : WithBot ℕ∞)) ≤ ((((3 : ℕ)) : ℕ∞) : WithBot ℕ∞) :=
    height_le_of_add_dim_eq _ _ 3 1 4 h31 hcat' hD1
  exact WithBot.coe_le_coe.mp hconcl

#print axioms height_cut_le_three

/-- R-B3 cone-cut avoidance, unconditional (rung 2 closed): discharges the
`[hcut]` hypothesis of `ConeCutAvoidance.minAvoidRung_two_of_cut` with
`height_cut_le_three`. Added by parent integrator at integration. -/
theorem minAvoidRung_two_unconditional (K E : Type*) [Field K]
    [NonUnitalNonAssocSemiring E] [Module K E]
    [IsScalarTower K E E] [SMulCommClass K E E] [IsAlgClosed K]
    (V : Submodule K E)
    (c : Fin 3 → Fin 3 → Fin 3 → K)
    (b : Module.Basis (Fin 3) K V)
    (hexp : ∀ i j, (b i : E) * (b j : E) = ∑ k, c i j k • (b k : E))
    (hN : absNilpotent K E V = {0})
    (hn : 0 < 3)
    (j : Fin (statementIndex 3 + 1)) (hj : j.val = 2) :
    MinAvoidRungs.MinAvoidRung 3 K c hn j :=
  ConeCutAvoidance.minAvoidRung_two_of_cut K E V c b hexp hN hn j hj
    (fun Q hQ P' hP' => height_cut_le_three K c hn j hj Q hQ P' hP')

#print axioms minAvoidRung_two_unconditional

end HeightCutDischarge
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
