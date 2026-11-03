/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Appendix_FixedPoint.BezoutChain.Regularity.Unmixed.Unmixedness
import Appendix_FixedPoint.BezoutChain.Regularity.Unmixed.CohenMacaulayFragment
import Appendix_FixedPoint.BezoutChain.Regularity.Unmixed.HeightDrop
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.Lattice
import Mathlib.RingTheory.Nakayama
import Appendix_FixedPoint.BezoutChain.Geometry.UnmixednessAtLengthTwo
import Appendix_FixedPoint.BezoutChain.Regularity.Grade.GradeDepthFragment
import Appendix_FixedPoint.BezoutChain.Regularity.Unmixed.HeightDropSharp
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.ChiDegreeMaster
import Appendix_FixedPoint.BezoutChain.Regularity.DimensionEquality.ChiReduceSubstitution
import Appendix_FixedPoint.BezoutChain.Regularity.DimensionEquality.MinAtAssCloser
import Appendix_FixedPoint.BezoutChain.Regularity.DimensionEquality.MinAtAssClosure
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.RegularSequenceProbe
import Appendix_FixedPoint.BezoutChain.Regularity.CohenMacaulayLink.CMQuotientFull
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.ColonTransfer
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.SelectedPathDepth
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.InfiniteResidueFields
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.SesClosure
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.TraceRepBridge
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.TowerClosure
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.RegularityBridge
/-!
# B1 `k = 2` slice: conditional close through the proved u2 chain

Atoms A1 (interface) +
A2. This file is the priority slice: R2 at `r = 3` needs B1 at `k = 2`
first. It proves independently of the
general-`k` case.

## Main results

* `mem_minimalPrimes_of_two_of_heightDropPair`: the `k = 2` slice of
  `FRGlobalUnmixed`, closed modulo exactly `HeightDropResidualPair`
  (`P.height ≤ 2` for `P ∈ Ass` over a length-2 successive span). Fires the
  primary-route chain `u2_dim_zero_of_height_le_two` +
  `unmixed_two_of_u2` (`CohenMacaulayFragment.lean`), discharging the `[P.IsPrime]`
  instance the B1 binder lacks via the standard
  `AssociatedPrimes.mem_iff` fact.
* `frGlobalUnmixed_of_le_two_of_pair`: re-packages the proved
  `frGlobalUnmixed_of_le_one` pattern (`k = 0 ∨ k = 1` by `omega`) with the
  `k = 2` slice into the `k ≤ 2` prefix, modulo the universal length-2
  residual. Mirrors the former `FRCoreResiduesE6b.lean` pattern.

## Residual (exact)

The unconditional `k = 2` close needs `HeightDropResidualPair` itself —
the regular-element height-drop in the non-UFD quotient `R ⧸ (q₀)`
(design note §3, atom A1: no live sketch). The
only in-tree height upper bound (`height_le_of_mem_minimalPrimes`, Krull)
takes minimality over `J` as input, i.e. the goal itself
(`heightDrop_iff_forall_mem_minimalPrimes`); the length-0/1 upper bounds do
not replay at length 2 (route-R5 note at `HeightDrop.lean`); the
catenary lower-bound program is provably insufficient standalone (4b) and
the DVR link inequality is false in general (`CohenMacaulayFragment.lean`). No
restricted-list hypothesis is assumed anywhere in this file.

Import closure: `Unmixedness` (G1 side) + `CohenMacaulayFragment` + `HeightDrop` +
mathlib only — within the allowed closure (no grade-fragment,
bridge-assembly, or scoped-link imports).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace FRGlobalUnmixedKTwo

/-- `k = 2` slice of `FRGlobalUnmixed`, closed modulo exactly
`HeightDropResidualPair`: the residual supplies `P.height ≤ 2`, which fires
the proved u2 chain (`u2_dim_zero_of_height_le_two` +
`unmixed_two_of_u2`). The `[P.IsPrime]` instance the B1 binder lacks is
discharged from `hP` via `AssociatedPrimes.mem_iff` (finding F2). -/
theorem mem_minimalPrimes_of_two_of_heightDropPair (m : ℕ) (K : Type*)
    [Field K]
    (q : Fin 2 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (P : Ideal (MvPolynomial (Fin m) K))
    (hP : P ∈ associatedPrimes _ (_ ⧸ J))
    (hdrop : HeightDrop.HeightDropResidualPair m K q hsucc J hJ) :
    P ∈ J.minimalPrimes := by
  have hprime : P.IsPrime := (AssociatedPrimes.mem_iff.mp hP).isPrime
  have hle : P.height ≤ ((2 : ℕ) : ℕ∞) := @hdrop P hprime hP
  have hle2 : P.height ≤ 2 := by exact_mod_cast hle
  exact @unmixed_two_of_height_le_two_closed m K _ q hsucc J hJ P hprime hP
    hle2

#print axioms mem_minimalPrimes_of_two_of_heightDropPair

/-- `k ≤ 2` prefix of `FRGlobalUnmixed`, modulo the universal length-2
residual: extends the proved `frGlobalUnmixed_of_le_one` (`k = 0 ∨ k = 1`)
with the `k = 2` slice above. The residual hypothesis quantifies over all
length-2 successive data at the ambient `m`, `K`. -/
theorem frGlobalUnmixed_of_le_two_of_pair (m k : ℕ) (K : Type*) [Field K]
    (hk : k ≤ 2)
    (q : Fin k → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (P : Ideal (MvPolynomial (Fin m) K))
    (hP : P ∈ associatedPrimes _ (_ ⧸ J))
    (hpair : ∀ (q₂ : Fin 2 → MvPolynomial (Fin m) K)
      (hsucc₂ : RegularityBridge.SuccessiveSMulRegular q₂)
      (J₂ : Ideal (MvPolynomial (Fin m) K))
      (hJ₂ : J₂ = Ideal.span (Set.range q₂)),
      HeightDrop.HeightDropResidualPair m K q₂ hsucc₂ J₂ hJ₂) :
    P ∈ J.minimalPrimes := by
  have hk02 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hk02 with rfl | rfl | rfl
  · exact mem_minimalPrimes_of_successive_zero m K q hsucc J hJ P hP
  · exact mem_minimalPrimes_of_successive_singleton m K q hsucc J hJ P hP
  · exact mem_minimalPrimes_of_two_of_heightDropPair m K q hsucc J hJ P hP
      (hpair q hsucc J hJ)

#print axioms frGlobalUnmixed_of_le_two_of_pair

end FRGlobalUnmixedKTwo
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

/-!
# C1 tower gate: reshape is false, gated firing on `[FirstReg + C3aGapAll]`

`C3aGapAll` is closed (`AssociatedPrimes.FiniteDimDischarge`) — `hC3a` binders
below are vestigial; downstream results need only `[FirstReg]`
(see discharge wrappers).

Re-scoped atoms T1–T4 (§(b)); B1/B4 as scoped
are not proved (falsehood / vacuous transport).

* **T1 — formal `¬`-hardening (shared with R-RB4; proved once):**
  `not_supTowerPosDim_of_height_ge2`: `¬ KrullDimLE 1 R → ¬ SupTowerPosDim`
  over general Noetherian-local UFD `R` (plus the `R_Q` corollary
  `not_supTowerPosDim_atPrime_of_height_ge2`). Witness `J' = span{x} * 𝔪`
  for order-one `x` (Nakayama); `(x)` is prime (order-one ⟹ irreducible ⟹
  prime) of height ≤ 1 (Krull PIT, self-minimal), hence strictly below `𝔪`
  (height = dim ≥ 2), giving pos-dim of `R ⧸ J'`; the uncapped colon
  equation fails at every `y ∈ 𝔪` (unit-`1-b` order argument). Neither the
  positivity guard nor any residue-field hypothesis is used.
* **T2 — C1 falsity-instance record:** `not_reshapedTowerAtAss_of_height_ge2`
  refutes `ReshapedTowerAtAss` at any `Q ∈ Ass` with `¬ KrullDimLE 1 R_Q`.
  The prose instance: `m = 3`, any field `K`, `J = (x,y)` successive,
  `Q = (x,y) ∈ Ass(R ⧸ J)`, `ht Q = 2`; `J' = u·𝔪_Q` (`u` order-one) kills
  `SupTowerPosDim (R := R_Q)`, hence `¬ ReshapedTowerAtAss 3 K J`.
* **T3 — gated rework + endgame (the firing):** H5 via
  `hChiReduceAtAss_of_gatedTowers` (pin `dimPin_atAss_unconditional`, tower
  `supTowerExactGated_of_quot_of_traceVV` on `[Infinite K]` residues,
  depth `supPathDepthSel_bot_of_cm`) → `HdimEqMinAtAss` (unconditional H4)
  → `hker` → `hdepth` → C0-mpr residuals (uniform + `k = 2` pair) → the B1
  `k = 2` minimality slice. All conditional-exact on
  `[FirstReg.{u,u} + C3aGapAll.{u}]` (+ ambient `[Infinite K]`); only
  Sel-path-scoped depth is used, never any `∀J'`-depth vehicle.
* **T4 — dim-≤-1 record (prose pointer, no Lean):** H5 at `ht ≤ 1`
  is closed by the T3 firing above.

## Residual register (exact)

T1/T2/T3 done, no residual. T3's `[FirstReg + C3aGapAll]` are pass-through
hypotheses at their E6/E7 addresses (the remaining CM obligations, owned by
R/R-C1d-followup/R-R2R2/GapBase — not this lane). The general-`k`
`FRGlobalUnmixed` binder additionally needs the uniform residual at finite
`K` (this leaf's residual is `[Infinite K]`-gated); the `k = 2` slice fires.

Scope: `DepthEqDimAt` only as conclusion; no refuted `∀`-form assumed;
`[FirstReg + C3aGapAll]` pass-through only. Import cycle note: the endgame
substitution lives here, never inside `HeightDrop.lean` (`GradeDepthFragment`
imports `HeightDrop`).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace K2SliceClose

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradeDepthFragment
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.HeightDrop
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.HeightDropSharp
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.UnmixednessAtLengthTwo
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.ChiDegreeMaster
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.ChiReduceSubstitution
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.MinAtAssCloser
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.MinAtAssClosure
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.ColonTransfer
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.SelectedPathDepth
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.InfiniteResidueFields
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.SesClosure
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.TraceRepBridge
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.TowerClosure
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.RegularityBridge
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.FRGlobalUnmixedKTwo

universe u

/-! ## §1. T1: the `∀J'` positivity-guarded tower is false at height ≥ 2 -/

/-- T1 `¬`-hardening (shared with R-RB4 — land once): over general
Noetherian-local UFD `R`, `¬ KrullDimLE 1 R → ¬ SupTowerPosDim`.
Witness `J' = span{x} * 𝔪` for order-one `x` (Nakayama gives `𝔪 ≠ 𝔪²`
since `𝔪 ≠ ⊥`): `(x)` is prime (order-one ⟹ irreducible, proved, ⟹
prime in a UFD) of height ≤ 1 (Krull PIT, self-minimal), hence strictly
below `𝔪` (height = dim ≥ 2), so `R ⧸ J'` is pos-dim; the uncapped colon
equation fails at every `y ∈ 𝔪` (`x·y ∈ J'` puts `x` in every colon-LHS
while `x ∉ 𝔪^{n+1} ⊔ J'` by the unit-`1-b` order argument). Neither the
positivity guard nor any residue-field hypothesis is used.
-/
theorem not_supTowerPosDim_of_height_ge2 {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [UniqueFactorizationMonoid R]
    (h2 : ¬ Ring.KrullDimLE 1 R) :
    ¬ SupTowerPosDim (R := R) := by
  have hmax_ne_top : IsLocalRing.maximalIdeal R ≠ ⊤ :=
    (IsLocalRing.maximalIdeal.isMaximal R).ne_top
  -- Step 0: `𝔪 ≠ ⊥` (else every prime is maximal, so dim ≤ 0 ≤ 1).
  have hmax_ne_bot : IsLocalRing.maximalIdeal R ≠ ⊥ := by
    intro hcon
    apply h2
    have h0 : Ring.KrullDimLE 0 R :=
      Ring.krullDimLE_zero_iff.mpr (fun P hP => by
        have hle : P ≤ IsLocalRing.maximalIdeal R :=
          IsLocalRing.le_maximalIdeal hP.ne_top
        rw [hcon] at hle
        have hPeq : P = ⊥ := le_bot_iff.mp hle
        rw [hPeq, ← hcon]
        exact IsLocalRing.maximalIdeal.isMaximal R)
    exact @Order.KrullDimLE.mono 0 1 zero_le_one (PrimeSpectrum R) _ h0
  -- Step 1: order-one `x ∈ 𝔪 ∖ 𝔪²`, via Nakayama (`𝔪 ≠ 𝔪²`).
  have hmsq : IsLocalRing.maximalIdeal R ≠ (IsLocalRing.maximalIdeal R) ^ 2 := by
    intro hcon
    have hFG := Ideal.fg_of_isNoetherianRing (IsLocalRing.maximalIdeal R)
    have e : ((IsLocalRing.maximalIdeal R : Ideal R) : Submodule R R)
        = ((IsLocalRing.maximalIdeal R * IsLocalRing.maximalIdeal R : Ideal R) :
          Submodule R R) := by
      conv_lhs => rw [hcon, pow_two]
    have hIN : ((IsLocalRing.maximalIdeal R : Ideal R) : Submodule R R)
        ≤ IsLocalRing.maximalIdeal R
          • ((IsLocalRing.maximalIdeal R : Ideal R) : Submodule R R) := by
      conv_lhs => rw [e]
      exact le_rfl
    have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
      (IsLocalRing.maximalIdeal R) _ hFG hIN
      (IsLocalRing.maximalIdeal_le_jacobson ⊥)
    exact hmax_ne_bot hbot
  have hsq_le : (IsLocalRing.maximalIdeal R) ^ 2
      ≤ IsLocalRing.maximalIdeal R := by
    rw [pow_two]
    exact Ideal.mul_le_right
  have hsq_lt : (IsLocalRing.maximalIdeal R) ^ 2
      < IsLocalRing.maximalIdeal R :=
    lt_of_le_of_ne hsq_le (Ne.symm hmsq)
  obtain ⟨x, hxm, hxsq⟩ := SetLike.exists_of_lt hsq_lt
  -- Step 2: `(x)` is prime (order-one ⟹ irreducible ⟹ prime in a UFD).
  have hxne : x ≠ 0 :=
    RegularSequenceProbe.ne_zero_of_not_mem_pow _ _ x hxsq
  have hirr : Irreducible x :=
    RegularSequenceProbe.irreducible_of_mem_maximalIdeal_not_mem_sq x hxm hxsq
  have hPrime : Prime x := UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr
  have hprime : (Ideal.span {x}).IsPrime :=
    (Ideal.span_singleton_prime hxne).mpr hPrime
  -- Step 3: `(x)` is self-minimal, so height ≤ 1 (Krull PIT); hence
  -- `(x) ⊂ 𝔪` strictly (height `𝔪` = dim ≥ 2).
  have hselfmin : Ideal.span {x} ∈ (Ideal.span {x}).minimalPrimes := by
    change (Ideal.span {x}).IsMinimalPrime (Ideal.span {x})
    refine ⟨⟨hprime, le_rfl⟩, ?_⟩
    intro Q hQ _
    exact hQ.2
  have hpit : (Ideal.span {x}).height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hselfmin
  have hspan_le : Ideal.span {x} ≤ IsLocalRing.maximalIdeal R :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hxm)
  have hspan_ne : Ideal.span {x} ≠ IsLocalRing.maximalIdeal R := by
    intro hcon
    apply h2
    rw [Ring.krullDimLE_iff]
    have hdim := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R)
    rw [← hdim, ← hcon]
    simpa using hpit
  have hspan_lt : Ideal.span {x} < IsLocalRing.maximalIdeal R :=
    lt_of_le_of_ne hspan_le hspan_ne
  -- Step 4: the witness `J'` and its basic facts.
  set J' : Ideal R := Ideal.span {x} * IsLocalRing.maximalIdeal R with hJ'def
  have hJ'le_span : J' ≤ Ideal.span {x} := by
    rw [hJ'def]
    exact Ideal.mul_le_left
  have hJ'le_sq : J' ≤ (IsLocalRing.maximalIdeal R) ^ 2 := by
    rw [hJ'def, pow_two]
    refine Ideal.mul_le.mpr ?_
    intro r hr s hs
    exact Ideal.mul_mem_mul (hspan_le hr) hs
  have hJ'ne : J' ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (le_trans hJ'le_span hspan_le)
      (IsLocalRing.maximalIdeal.isMaximal R).lt_top)
  -- Step 5: pos-dim of `R ⧸ J'` via `map (x) < map 𝔪`.
  have hpos : ¬ Ring.KrullDimLE 0 (R ⧸ J') := by
    intro h0
    have hP₁ : (Ideal.map (Ideal.Quotient.mk J') (Ideal.span {x})).IsPrime :=
      Ideal.map_isPrime_of_surjective (f := Ideal.Quotient.mk J')
        (hf := Ideal.Quotient.mk_surjective) (I := Ideal.span {x})
        (H := hprime) (hk := by rw [Ideal.mk_ker]; exact hJ'le_span)
    have hmaximal : (Ideal.map (Ideal.Quotient.mk J')
        (Ideal.span {x})).IsMaximal :=
      Ring.krullDimLE_zero_iff.mp h0 _ hP₁
    obtain ⟨y, hym, hynspan⟩ := SetLike.exists_of_lt hspan_lt
    have hmyM : Ideal.Quotient.mk J' y ∈ Ideal.map (Ideal.Quotient.mk J')
        (IsLocalRing.maximalIdeal R) :=
      Ideal.mem_map_of_mem _ hym
    have hmyNP : Ideal.Quotient.mk J' y ∉ Ideal.map (Ideal.Quotient.mk J')
        (Ideal.span {x}) := by
      intro hcon
      obtain ⟨z, hzp, hzy⟩ :=
        (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hcon
      have hsub : z - y ∈ J' := (Ideal.Quotient.eq (I := J')).mp hzy
      have hsubspan : z - y ∈ Ideal.span {x} := hJ'le_span hsub
      have hym' : y ∈ Ideal.span {x} := by
        have hmem : z - (z - y) ∈ Ideal.span {x} := sub_mem hzp hsubspan
        rwa [sub_sub_cancel] at hmem
      exact hynspan hym'
    have hle12 : Ideal.map (Ideal.Quotient.mk J') (Ideal.span {x})
        ≤ Ideal.map (Ideal.Quotient.mk J') (IsLocalRing.maximalIdeal R) :=
      Ideal.map_mono hspan_le
    have hne12 : Ideal.map (Ideal.Quotient.mk J') (Ideal.span {x})
        ≠ Ideal.map (Ideal.Quotient.mk J') (IsLocalRing.maximalIdeal R) := by
      intro hcon
      apply hmyNP
      rw [hcon]
      exact hmyM
    have hmapm_ne : Ideal.map (Ideal.Quotient.mk J')
        (IsLocalRing.maximalIdeal R) ≠ ⊤ := by
      intro htop
      have h1 : (1 : R ⧸ J') ∈ Ideal.map (Ideal.Quotient.mk J')
          (IsLocalRing.maximalIdeal R) := by
        rw [htop]
        simp
      obtain ⟨z, hzm, hzy⟩ :=
        (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp h1
      have hzy' : Ideal.Quotient.mk J' z = Ideal.Quotient.mk J' 1 := by
        rw [hzy]
        exact ((Ideal.Quotient.mk J').map_one).symm
      have hsub : z - 1 ∈ J' := (Ideal.Quotient.eq (I := J')).mp hzy'
      have hsubm : z - 1 ∈ IsLocalRing.maximalIdeal R :=
        (le_trans hJ'le_span hspan_le) hsub
      have h1m : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
        have hmem : z - (z - 1) ∈ IsLocalRing.maximalIdeal R :=
          sub_mem hzm hsubm
        rwa [sub_sub_cancel] at hmem
      exact hmax_ne_top ((Ideal.eq_top_iff_one _).mpr h1m)
    have heq := hmaximal.eq_of_le hmapm_ne hle12
    exact hne12 heq
  -- Step 6: the uncapped colon equation fails at every `y₀ ∈ 𝔪`.
  intro htower
  obtain ⟨y₀, hsel, hcol⟩ := htower J' hJ'ne hpos
  have hy₀m : y₀ ∈ IsLocalRing.maximalIdeal R := hsel.1
  obtain ⟨c, hc⟩ := hcol
  have hn1 : 1 ≤ max c 1 := le_max_right _ _
  have hnc : c ≤ max c 1 := le_max_left _ _
  have heq := hc (max c 1) hnc
  have hxLHS : x ∈ ((IsLocalRing.maximalIdeal R ^ (max c 1 + 2) ⊔ J' : Ideal R) :
      Submodule R R).colon {y₀} := by
    rw [Submodule.mem_colon_singleton, smul_eq_mul]
    have hxy : x * y₀ ∈ J' := by
      rw [hJ'def]
      exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self x) hy₀m
    exact Submodule.mem_sup_right hxy
  rw [heq] at hxLHS
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hxLHS
  have hb2 : b ∈ Ideal.span {x} * IsLocalRing.maximalIdeal R := by
    rw [← hJ'def]
    exact hb
  obtain ⟨t, htm, hbt⟩ := Ideal.mem_span_singleton_mul.mp hb2
  have hpow : IsLocalRing.maximalIdeal R ^ (max c 1 + 1)
      ≤ (IsLocalRing.maximalIdeal R) ^ 2 := by
    have e : max c 1 + 1 = 2 + (max c 1 - 1) := by omega
    rw [e, pow_add]
    exact Ideal.mul_le_left
  have ha2 : a ∈ (IsLocalRing.maximalIdeal R) ^ 2 := hpow ha
  have hxu : x * (1 - t) = a := by
    have h1 : x * (1 - t) = x - b := by rw [mul_sub, mul_one, hbt]
    rw [h1, ← hab]
    rw [add_sub_assoc, sub_self, add_zero]
  have hxu_mem : x * (1 - t) ∈ (IsLocalRing.maximalIdeal R) ^ 2 := by
    rw [hxu]
    exact ha2
  have hu : IsUnit (1 - t) := by
    by_contra hnu
    have hmem : (1 - t) ∈ IsLocalRing.maximalIdeal R :=
      (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)
    have h1m : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
      have h := add_mem hmem htm
      rwa [sub_add_cancel] at h
    exact hmax_ne_top ((Ideal.eq_top_iff_one _).mpr h1m)
  have hxmem : x ∈ (IsLocalRing.maximalIdeal R) ^ 2 := by
    rw [mul_comm x (1 - t)] at hxu_mem
    exact (Ideal.unit_mul_mem_iff_mem _ hu).mp hxu_mem
  exact hxsq hxmem

#print axioms not_supTowerPosDim_of_height_ge2

/-- T1 at `R_Q` (C1/R-RB4 handoff form): the general `¬`-theorem
instantiated at `Localization.AtPrime Q` (all instances automatic).
-/
theorem not_supTowerPosDim_atPrime_of_height_ge2 (m : ℕ) (K : Type u) [Field K]
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (h2 : ¬ Ring.KrullDimLE 1 (Localization.AtPrime Q)) :
    ¬ SupTowerPosDim (R := Localization.AtPrime Q) :=
  not_supTowerPosDim_of_height_ge2 h2

#print axioms not_supTowerPosDim_atPrime_of_height_ge2

/-! ## §2. T2: C1 falsity-instance record -/

/-- T2 falsity instance (formal conditional on top of T1): `ReshapedTowerAtAss`
is refuted at any `Q ∈ Ass(R ⧸ J)` with `¬ KrullDimLE 1 R_Q` — the tower
conjunct dies by T1. Prose instance: `m = 3`, any `K`, `J = (x,y)`
successive, `Q = (x,y) ∈ Ass(R ⧸ J)`, `ht Q = 2`.
-/
theorem not_reshapedTowerAtAss_of_height_ge2 (m : ℕ) (K : Type u) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J))
    (h2 : ¬ Ring.KrullDimLE 1 (Localization.AtPrime Q)) :
    ¬ ReshapedTowerAtAss m K J := by
  intro h
  obtain ⟨_, _, htower, _⟩ := h Q hQ
  exact (not_supTowerPosDim_atPrime_of_height_ge2 m K Q h2) htower

#print axioms not_reshapedTowerAtAss_of_height_ge2

/-! ## §3. T3: gated rework + endgame substitution (the firing) -/

/-- T3 gated H5 on `[FirstReg + C3aGapAll]` (general successive-span `J`;
C1-flavored sibling of R-RB4's T3): fires `hChiReduceAtAss_of_gatedTowers`
with the unconditional pin, the discharged Rep gated tower on `[Infinite K]`
residues, and Sel-path depth from `⊥`. Only Sel-path-scoped depth is used.

Conditional on exactly `[FirstReg.{u,u} + C3aGapAll.{u}]`. -/
theorem hChiReduceAtAss_gated_of_cm (m : ℕ) (K : Type u) [Field K] [Infinite K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hFR : CMQuotientFull.FirstReg.{u, u})
    (hC3a : CMQuotientFull.C3aGapAll.{u}) :
    HchiReduceAtAss m K J := by
  apply hChiReduceAtAss_of_gatedTowers
  intro Q _ hQ
  obtain ⟨dimN, hpin⟩ := dimPin_atAss_unconditional m K J Q hQ
  exact ⟨dimN, hpin,
    supTowerExactGated_of_quot_of_traceVV (atPrime_residue_infinite m K Q),
    supPathDepthSel_bot_of_cm m K J Q hQ hFR hC3a⟩

#print axioms hChiReduceAtAss_gated_of_cm

/-- T3 re-targeted `HdimEqMinAtAss` (general `(m,K,J)`): unconditional H4 +
gated H5 through the H4+H5 closer.

Conditional on exactly `[FirstReg.{u,u} + C3aGapAll.{u}]`. -/
theorem hdimEqMinAtAss_gated_of_cm (m : ℕ) (K : Type u) [Field K] [Infinite K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hFR : CMQuotientFull.FirstReg.{u, u})
    (hC3a : CMQuotientFull.C3aGapAll.{u}) :
    HdimEqMinAtAss m K J :=
  hdimEqMinAtAss_close_of_h4H5 m K J (hchiGrowthAtAss_close m K J)
    (hChiReduceAtAss_gated_of_cm m K J hFR hC3a)

#print axioms hdimEqMinAtAss_gated_of_cm

/-- T3 gated `hker` (minimal `d`-split discharge).

Conditional on exactly `[FirstReg.{u,u} + C3aGapAll.{u}]`. -/
theorem hkerMinAtAss_gated_of_cm (m : ℕ) (K : Type u) [Field K] [Infinite K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hFR : CMQuotientFull.FirstReg.{u, u})
    (hC3a : CMQuotientFull.C3aGapAll.{u}) :
    HkerMinAtAss m K J :=
  hkerMinAtAss_of_hdimEqMin m K J
    (hdimEqMinAtAss_gated_of_cm m K J hFR hC3a)

#print axioms hkerMinAtAss_gated_of_cm

/-- T3 gated `hdepth`: per-prime `DepthEqDimAt` (conclusion only).

Conditional on exactly `[FirstReg.{u,u} + C3aGapAll.{u}]`. -/
theorem hdepth_gated_of_cm (m : ℕ) (K : Type u) [Field K] [Infinite K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hFR : CMQuotientFull.FirstReg.{u, u})
    (hC3a : CMQuotientFull.C3aGapAll.{u})
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J)) :
    DepthEqDimAt m K Q :=
  hdepth_of_hkerMin m K J (hkerMinAtAss_gated_of_cm m K J hFR hC3a) Q hQ

#print axioms hdepth_gated_of_cm

/-- T3 uniform height-drop residual on `[FirstReg + C3aGapAll]` (C0-mpr:
gated `hdepth` at every `Ass` prime).

Conditional on exactly `[FirstReg.{u,u} + C3aGapAll.{u}]`. -/
theorem heightDropResidual_gated_of_cm (m : ℕ) {k : ℕ} (K : Type u) [Field K]
    [Infinite K]
    (q : Fin k → MvPolynomial (Fin m) K)
    (hsucc : SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (hFR : CMQuotientFull.FirstReg.{u, u})
    (hC3a : CMQuotientFull.C3aGapAll.{u}) :
    HeightDropResidualAt m K q hsucc J hJ :=
  (residual_iff_depthEqDimAtAss m K q hsucc J hJ).mpr
    (fun P _ hP => hdepth_gated_of_cm m K J hFR hC3a P hP)

#print axioms heightDropResidual_gated_of_cm

/-- T3 uniform residual with all binders explicit (the shape feeding the `k = 2` endgame).

Conditional on exactly `[FirstReg.{u,u} + C3aGapAll.{u}]`. -/
theorem heightDropResidual_uniform_of_cm (m k : ℕ) (K : Type u) [Field K]
    [Infinite K]
    (q : Fin k → MvPolynomial (Fin m) K)
    (hsucc : SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (hFR : CMQuotientFull.FirstReg.{u, u})
    (hC3a : CMQuotientFull.C3aGapAll.{u}) :
    HeightDropResidualAt m K q hsucc J hJ :=
  heightDropResidual_gated_of_cm m K q hsucc J hJ hFR hC3a

#print axioms heightDropResidual_uniform_of_cm

/-- T3 `k = 2` pair residual on `[FirstReg + C3aGapAll]` (C0-mpr pair alias).

Conditional on exactly `[FirstReg.{u,u} + C3aGapAll.{u}]`. -/
theorem heightDropResidualPair_gated_of_cm (m : ℕ) (K : Type u) [Field K]
    [Infinite K]
    (q : Fin 2 → MvPolynomial (Fin m) K)
    (hsucc : SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (hFR : CMQuotientFull.FirstReg.{u, u})
    (hC3a : CMQuotientFull.C3aGapAll.{u}) :
    HeightDropResidualPair m K q hsucc J hJ :=
  (residualPair_iff_depthEqDimAtAss m K q hsucc J hJ).mpr
    (fun P _ hP => hdepth_gated_of_cm m K J hFR hC3a P hP)

#print axioms heightDropResidualPair_gated_of_cm

/-- T3 `k = 2` endgame: minimality over length-2 successive spans on
`[FirstReg + C3aGapAll]`, firing the proved u2 chain with the gated pair
residual. R2's `r = 3` call site fires on the same hypotheses.

Conditional on exactly `[FirstReg.{u,u} + C3aGapAll.{u}]`. -/
theorem mem_minimalPrimes_of_two_gated_of_cm (m : ℕ) (K : Type u) [Field K]
    [Infinite K]
    (q : Fin 2 → MvPolynomial (Fin m) K)
    (hsucc : SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (P : Ideal (MvPolynomial (Fin m) K))
    (hP : P ∈ associatedPrimes _ (_ ⧸ J))
    (hFR : CMQuotientFull.FirstReg.{u, u})
    (hC3a : CMQuotientFull.C3aGapAll.{u}) :
    P ∈ J.minimalPrimes :=
  mem_minimalPrimes_of_two_of_heightDropPair m K q hsucc J hJ P hP
    (heightDropResidualPair_gated_of_cm m K q hsucc J hJ hFR hC3a)

#print axioms mem_minimalPrimes_of_two_gated_of_cm

end K2SliceClose
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
