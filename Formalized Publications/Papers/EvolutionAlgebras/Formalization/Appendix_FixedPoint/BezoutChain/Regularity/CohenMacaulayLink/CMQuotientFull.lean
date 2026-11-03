/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.QuotSMulTop
import Appendix_FixedPoint.BezoutChain.Regularity.Grade.GradeDepthFragment
import Appendix_FixedPoint.BezoutChain.Regularity.CohenMacaulayLink.VariableInductionCM
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.SystemOfParameters
import Appendix_FixedPoint.BezoutChain.Regularity.CohenMacaulayLink.CMQuotientPartial
import Appendix_FixedPoint.BezoutChain.Regularity.CohenMacaulayLink.QuotientByRegularIsCM
import Appendix_FixedPoint.BezoutChain.Regularity.CohenMacaulayLink.CMPositiveDimHasDepth

/-!
# C1-full via restructure-(b): regular-quotient induction (partial)

Proves the C1-full block:
`IsCM R_Q` for `R_Q = Localization.AtPrime Q` at every prime `Q`, by the
restructure-(b) greedy regular-sequence induction over CI quotients
(statement `K(n)` below), plus the top corollary `DepthEqDimAt` at every `Q`.

## Status: partial (exact residual stated)

* Unconditional: `K_zero`, the domain first-element case
  (`isDomain_of_ciQuotient_nil`, `firstReg_domain_case`), adapters A1/A2/A3,
  the B-reg bridge, prime avoidance over `Ass`, the mingen repackaging, and
  the dim-≤-1 slice of the top corollary.
* Conditional: `K_of_residuals`, `isCM_atPrime_of_residuals`, and
  `depthEqDimAt_of_residuals` on
  `[FirstReg] + [C3aGapAll] + [GreedyOfResiduals]`.
  (`C3aGapAll` closed via `AssociatedPrimes.FiniteDimDischarge` — true
  residuals are `[FirstReg]`-only; `GreedyOfResiduals` proved.)
* Closed: `GreedyOfResiduals n` — the §3 greedy assembly
  is proved in `CMQuotientGreedyTower.lean`
  (`repConcat_proof`, `greedy_of_residuals`;
  consumed by `SelectedPathDepth.lean`). The remaining residuals
  behind the top corollaries are
  `[FirstReg]` + `[C3aGapAll]` only.) The `[algClosed]` standing
  authorization is vacuous for this route (C2-av needs no infinitude)
  and is not taken as a binder.

## What this file proves

* `IsCIQuotient`, `K`, `FirstReg`, `C3aGapAll`, `GreedyWitness`,
  `GreedyOfResiduals` — design note §2 defs plus the exact residual register (§4).
* `K_zero` — `K 0` via the empty sequence + capstone.
* `firstReg_domain_case` — first regular element at `rs₀ = []` (domain).
* `isCM_of_isCM_quotient_span` (A1), `maximalIdeal_notMem_associatedPrimes`
  (A2, direct-`S` C3 fire), `assPrimes_finset` (A3).
* `K_of_greedy`, `K_of_residuals`, `isCM_atPrime_of_residuals`,
  `depthEqDimAt_of_residuals`, `depthEqDimAt_of_dim_le_one`.

## Circularity

This file (and its project imports `GradeDepthFragment`, `VariableInductionCM`,
`SystemOfParameters`,
`CMQuotientPartial/C2/C3`) uses no graded machinery and no crux-ring
members: a verification grep for the forbidden identifiers is empty here
and in each consumed file. The file never invokes the C3a localization
theorem directly (that route would be circular per design note §4); C3 enters
only via the close at smaller dimension (A2). The F7 C2-iteration is not
consumed (it has no non-circular use inside C1-full per design note §0).

## Status

`K_zero`, `firstReg_domain_case`, A1/A2/A3, B-reg, avoidance, mingens,
`depthEqDimAt_of_dim_le_one`: unconditional. `K_of_residuals` and the top
corollaries: conditional-exact on the three stated residuals.
`GreedyOfResiduals`, `FirstReg`: residual (sketch).

## References

`VariableInductionCM.grade_eq_dim_of_maximal_regular`
(:758), `exists_isSMulRegular_mem_maximal` (:376), `empty_isRegular` (:346).
`CMPositiveDimHasDepth.mem_minimalPrimes_bot_of_mem_associatedPrimes_of_isCM`
(:396). C2 companions/av (`QuotientByRegularIsCM`:64/:80/:403). C1-partial
`isCM_atPrime_of_dim_le_one`/:138. `GradeDepthFragment.DepthEqDimAt` (:957).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace CMQuotientFull

open RingTheory.Sequence

/-! ## §2 definitions: CI quotients, the joint statement, residuals -/

/-- CI quotient of `R_Q`: quotient by the span of a maximal-ideal regular
List. Membership-set span `{x | x ∈ rs}` matches C3-F7
(`DecidableEq`-free). -/
def IsCIQuotient (m : ℕ) (K : Type*) [Field K]
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (S : Type*) [CommRing S] : Prop :=
  ∃ rs₀ : List (Localization.AtPrime Q),
    (∀ r ∈ rs₀, r ∈ IsLocalRing.maximalIdeal (Localization.AtPrime Q)) ∧
    IsRegular (Localization.AtPrime Q) rs₀ ∧
    Nonempty (S ≃+* ((Localization.AtPrime Q) ⧸ Ideal.span {x | x ∈ rs₀}))

/-- Joint induction statement: every CI quotient of every `R_Q` of dim
`≤ ↑n` is CM. `IsCM` is C1-partial's predicate (defeq across lanes). -/
def K (n : ℕ) : Prop :=
  ∀ (m : ℕ) (K : Type*) [Field K]
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (S : Type*) [CommRing S] [IsLocalRing S] [IsNoetherianRing S],
    IsCIQuotient m K Q S →
    ringKrullDim S ≤ ((n : ℕ∞) : WithBot ℕ∞) →
    CMQuotientPartial.IsCM S

/-- `[FirstReg]` residual (sketch, Serre-adjacent): every proper CI
quotient (`rs₀ ≠ []`) of positive dimension carries a regular element in
its maximal ideal. Fires only for proper quotients (`R_Q` itself uses the
domain case). Even in dim 1 this is dim-1 CI unmixedness, unproven. -/
def FirstReg : Prop :=
  ∀ (m : ℕ) (K : Type*) [Field K]
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (S : Type*) [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    (rs₀ : List (Localization.AtPrime Q)),
    rs₀ ≠ [] →
    (∀ r ∈ rs₀, r ∈ IsLocalRing.maximalIdeal (Localization.AtPrime Q)) →
    IsRegular (Localization.AtPrime Q) rs₀ →
    Nonempty (S ≃+* ((Localization.AtPrime Q) ⧸ Ideal.span {x | x ∈ rs₀})) →
    ¬ Ring.KrullDimLE 0 S →
    ∃ z ∈ IsLocalRing.maximalIdeal S, IsSMulRegular S z

/-- `[C3aGap]` residual (inherited from C3): the C3a content, stated over
the C3 `IsCM` copy so it feeds C3-shaped binders directly (defeq with
the C1 copy by `isCM_c1_iff_c3`). Enters only via the C3 close at
smaller dimension. -/
def C3aGapAll : Prop :=
  ∀ (S : Type*) [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    (p : Ideal S) [p.IsPrime],
    ringKrullDim S < ⊤ → -- finite-dim fence (matches GapBaseFin)
    CMPositiveDimHasDepth.IsCM S → CMPositiveDimHasDepth.C3aGap S p

/-- Greedy witness: every CI quotient of dim `≤ ↑n` carries a length-`dim`
regular sequence in `𝔪` (single-cast length equation, C1-mingen style). -/
def GreedyWitness (n : ℕ) : Prop :=
  ∀ (m : ℕ) (K : Type*) [Field K]
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (S : Type*) [CommRing S] [IsLocalRing S] [IsNoetherianRing S],
    IsCIQuotient m K Q S →
    ringKrullDim S ≤ ((n : ℕ∞) : WithBot ℕ∞) →
    ∃ rs : List S,
      (∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal S) ∧
      IsRegular S rs ∧ (rs.length : WithBot ℕ∞) = ringKrullDim S

/-- The greedy construction (§3) as an explicit implication residual
(sketch): `FirstReg` + `C3aGapAll` supply the per-step regular elements
(first element via `FirstReg`/domain case; later elements via the IH,
A2, A3, C2-av, B-reg, C2-mk, exact C2-dim drops), and the C3
double-quotient pattern re-presents each `T_j` as a CI quotient. The
only unproven mathematics is the re-presentation + assembly tower, whose
hard core is `[FirstReg]` (dim-1 CI unmixedness). -/
def GreedyOfResiduals.{u_1, u_2, u_3, u_4, u_5} (n : ℕ) : Prop :=
  FirstReg.{u_1, u_2} → C3aGapAll.{u_3} → GreedyWitness.{u_4, u_5} n

/-- The C1/C3 `IsCM` copies are syntactically identical; conversion is
`rfl` (design note §7). Machine-checked defeq record. -/
theorem isCM_c1_iff_c3 (S : Type*) [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] :
    CMQuotientPartial.IsCM S ↔ CMPositiveDimHasDepth.IsCM S := Iff.rfl

#print axioms isCM_c1_iff_c3

/-- The C1/C2 `IsCM` copies are syntactically identical; conversion is
`rfl` (design note §7). Machine-checked defeq record. -/
theorem isCM_c1_iff_c2 (S : Type*) [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] :
    CMQuotientPartial.IsCM S ↔ QuotientByRegularIsCM.IsCM S := Iff.rfl

#print axioms isCM_c1_iff_c2

/-! ## `K(0)` + the domain first-element case (unconditional) -/

/-- `K(0)`, unconditional: `dim S ≤ 0` with `S` nontrivial forces
`dim S = 0` (C1:200-222 pattern); close by the capstone with `rs = []`. -/
theorem K_zero : K 0 := by
  intro _ _ _ _ _ S _ _ _ _ hdim
  have hne : ringKrullDim S ≠ ⊥ := by
    rw [← Module.supportDim_self_eq_ringKrullDim]
    exact (Module.supportDim_ne_bot_iff_nontrivial _ _).mpr inferInstance
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hne
  rw [← hd, WithBot.coe_le_coe] at hdim
  have hd0 : d = ((0 : ℕ) : ℕ∞) := by
    have htop : d ≠ ⊤ := by
      rintro rfl
      simp at hdim
    obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp htop
    rw [ENat.natCast_le_natCast] at hdim
    have hn0 : n = 0 := Nat.le_zero.mp hdim
    subst hn0
    rfl
  have hdim0 : ringKrullDim S = 0 := by
    rw [← hd, hd0, WithBot.coe_natCast]
    exact Nat.cast_zero
  have hmem : ∀ r ∈ ([] : List S), r ∈ IsLocalRing.maximalIdeal S :=
    fun r hr => (List.not_mem_nil hr).elim
  have hreg : IsRegular S [] := VariableInductionCM.empty_isRegular
  have hdimcast : ((((List.length ([] : List S) : ℕ)) : ℕ∞) : WithBot ℕ∞) =
      ringKrullDim S := by
    simp only [List.length_nil]
    rw [hdim0, WithBot.coe_natCast]
    exact Nat.cast_zero
  exact VariableInductionCM.grade_eq_dim_of_maximal_regular hmem hreg hdimcast

#print axioms K_zero

/-- The nil membership-set spans `⊥` (shared by the nil-CI lemmas). -/
theorem span_memSet_nil (R : Type*) [CommRing R] :
    Ideal.span {x | x ∈ ([] : List R)} = (⊥ : Ideal R) := by
  have hset : ({x | x ∈ ([] : List R)} : Set R) = ∅ := by
    ext r
    simp
  rw [hset]
  exact Ideal.span_empty

#print axioms span_memSet_nil

/-- `IsDomain` transport across the nil-CI identification [R5]:
`S ≃+* R_Q ⧸ span ∅ = R_Q ⧸ ⊥ ≃+* R_Q`, and `R_Q` is a domain
(`IsLocalization.isDomain_of_local_atPrime`, cf. C1:173). -/
theorem isDomain_of_ciQuotient_nil (m : ℕ) (K : Type*) [Field K]
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (S : Type*) [CommRing S]
    (e : S ≃+* ((Localization.AtPrime Q) ⧸
      Ideal.span {x | x ∈ ([] : List (Localization.AtPrime Q))})) :
    IsDomain S := by
  have hdomRQ : IsDomain (Localization.AtPrime Q) :=
    IsLocalization.isDomain_of_local_atPrime (P := Q) inferInstance
  have hspan := span_memSet_nil (Localization.AtPrime Q)
  have e' : S ≃+* Localization.AtPrime Q :=
    e.trans ((Ideal.quotEquivOfEq hspan).trans
      (RingEquiv.quotientBot (Localization.AtPrime Q)))
  exact (MulEquiv.isDomain_iff e'.toMulEquiv).mpr hdomRQ

#print axioms isDomain_of_ciQuotient_nil

/-- First regular element at the top (`rs₀ = []`), unconditional: the
nil-CI ring is a domain of positive dimension, so G-dom applies. -/
theorem firstReg_domain_case (m : ℕ) (K : Type*) [Field K]
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (S : Type*) [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    (e : S ≃+* ((Localization.AtPrime Q) ⧸
      Ideal.span {x | x ∈ ([] : List (Localization.AtPrime Q))}))
    (hpos : ¬ Ring.KrullDimLE 0 S) :
    ∃ z ∈ IsLocalRing.maximalIdeal S, IsSMulRegular S z := by
  have _ : IsDomain S := isDomain_of_ciQuotient_nil m K Q S e
  have hdimne : ringKrullDim S ≠ 0 := by
    intro hcon
    exact hpos (Ring.krullDimLE_iff.mpr (by rw [hcon, Nat.cast_zero]))
  exact VariableInductionCM.exists_isSMulRegular_mem_maximal hdimne

#print axioms firstReg_domain_case

/-! ## Adapters A1/A2/A3 + B-reg + avoidance (unconditional / on `[C3aGap]`) -/

/-- A1 ascent lemma (provable, mirror C2:293-303): CM ascends across a
regular quotient — `IsCM (T ⧸ span{x})` plus `x` regular in `𝔪` gives
`IsCM T`, via the GradeDepthFragment:673 exact grade-drop + the C2-dim exact
dim-drop. Spare for the mingen-descending variant; not on the greedy
path (the greedy closes by the capstone instead). -/
theorem isCM_of_isCM_quotient_span {T : Type*} [CommRing T] [IsLocalRing T]
    [IsNoetherianRing T] {x : T}
    (hx : x ∈ IsLocalRing.maximalIdeal T)
    (hreg : IsSMulRegular T x)
    [IsLocalRing (T ⧸ Ideal.span {x})]
    (hCMquot : CMQuotientPartial.IsCM (T ⧸ Ideal.span {x})) :
    CMQuotientPartial.IsCM T := by
  have hle : Ideal.span {x} ≤ IsLocalRing.maximalIdeal T :=
    (Ideal.span_singleton_le_iff_mem _).mpr hx
  have hfin : Module.Finite T T := QuotientByRegularIsCM.finite_self T
  have hdim : ringKrullDim (T ⧸ Ideal.span {x}) + 1 = ringKrullDim T :=
    ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim hreg hx
  have hIlt : IsLocalRing.maximalIdeal T • (⊤ : Submodule T T) < ⊤ := by
    rw [lt_top_iff_ne_top, QuotientByRegularIsCM.smul_top_eq_self]
    intro hcon
    have h1 : (1 : T) ∈ IsLocalRing.maximalIdeal T := by
      have h1' : (1 : T) ∈ (IsLocalRing.maximalIdeal T : Submodule T T) := by
        rw [hcon]
        exact Submodule.mem_top
      exact h1'
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h1
    exact h1 isUnit_one
  have hgradeR : GradeDepthFragment.grade T (QuotSMulTop x T)
        (IsLocalRing.maximalIdeal T) + 1 =
        GradeDepthFragment.grade T T (IsLocalRing.maximalIdeal T) :=
    @GradeDepthFragment.grade_quotSMulTop_add_one_eq_grade T T inferInstance
      inferInstance inferInstance inferInstance hfin _ x hreg hx hIlt
  have hgradeA : GradeDepthFragment.grade T (QuotSMulTop x T)
        (IsLocalRing.maximalIdeal T) =
        GradeDepthFragment.grade T (T ⧸ Ideal.span {x})
          (IsLocalRing.maximalIdeal T) :=
    QuotientByRegularIsCM.grade_congr_of_equiv
      (QuotientByRegularIsCM.quotSMulTopEquivQuotientSpan x) _
  have hgradeB : GradeDepthFragment.grade T (T ⧸ Ideal.span {x})
        (IsLocalRing.maximalIdeal T) =
        GradeDepthFragment.grade (T ⧸ Ideal.span {x}) (T ⧸ Ideal.span {x})
          (IsLocalRing.maximalIdeal (T ⧸ Ideal.span {x})) := by
    unfold GradeDepthFragment.grade
    rw [QuotientByRegularIsCM.gradeSet_quotient_mk _ hle]
  have hgrade : GradeDepthFragment.grade (T ⧸ Ideal.span {x}) (T ⧸ Ideal.span {x})
          (IsLocalRing.maximalIdeal (T ⧸ Ideal.span {x})) + 1 =
        GradeDepthFragment.grade T T (IsLocalRing.maximalIdeal T) := by
    rw [← hgradeB, ← hgradeA]
    exact hgradeR
  have hgrade' : ((GradeDepthFragment.grade (T ⧸ Ideal.span {x}) (T ⧸ Ideal.span {x})
          (IsLocalRing.maximalIdeal (T ⧸ Ideal.span {x})) : ℕ∞) :
          WithBot ℕ∞) + 1 =
        ((GradeDepthFragment.grade T T (IsLocalRing.maximalIdeal T) : ℕ∞) :
          WithBot ℕ∞) := by
    have h := congrArg (fun g : ℕ∞ => (g : WithBot ℕ∞)) hgrade
    simpa using h
  unfold CMQuotientPartial.IsCM at hCMquot ⊢
  apply QuotientByRegularIsCM.withBot_eNat_add_one_cancel
  rw [← hgrade', ← hdim, hCMquot]

#print axioms isCM_of_isCM_quotient_span

/-- A2 adapter (provable, no new mathematics): the C3 close in direct-`S`
form — a CM local ring of positive dimension has `𝔪 ∉ Ass`. Re-runs
C3-core (:396) + the `:508-545` `mk₀` pattern at `J' := ⊥` (here no
quotient appears, so the close is shorter: every prime `Q` lies over a
minimal prime `q = 𝔪`, forcing `Q = 𝔪`). Fires on `T_j`, CM by the IH,
on `[C3aGapAll]`. -/
theorem maximalIdeal_notMem_associatedPrimes_of_isCM.{u}
    (T : Type u) [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
    (hCM : CMQuotientPartial.IsCM T)
    (hpos : ¬ Ring.KrullDimLE 0 T)
    (hC3a : C3aGapAll.{u})
    (hfinT : ringKrullDim T < ⊤) :
    IsLocalRing.maximalIdeal T ∉ associatedPrimes T T := by
  have hCM3 : CMPositiveDimHasDepth.IsCM T := hCM
  have hC3a' : ∀ (S : Type u) [CommRing S] [IsLocalRing S]
      [IsNoetherianRing S] (p : Ideal S) [p.IsPrime],
      ringKrullDim S < ⊤ →
      CMPositiveDimHasDepth.IsCM S → CMPositiveDimHasDepth.C3aGap S p := hC3a
  intro hmem
  have _ : (IsLocalRing.maximalIdeal T).IsPrime :=
    (inferInstance : (IsLocalRing.maximalIdeal T).IsMaximal).isPrime
  have hunmixed :
      IsLocalRing.maximalIdeal T ∈ (⊥ : Ideal T).minimalPrimes :=
    CMPositiveDimHasDepth.mem_minimalPrimes_bot_of_mem_associatedPrimes_of_isCM
      hCM3 _ hmem hC3a' hfinT
  have hmin' : (⊥ : Ideal T).IsMinimalPrime
      (IsLocalRing.maximalIdeal T) := hunmixed
  have hLE0 : Ring.KrullDimLE 0 T := by
    apply Ring.KrullDimLE.mk₀
    intro Q hQprime
    have _ : Q.IsPrime := hQprime
    obtain ⟨q, hqmin, hqle⟩ :=
      Ideal.exists_minimalPrimes_le (bot_le : (⊥ : Ideal T) ≤ Q)
    have hqmin' : (⊥ : Ideal T).IsMinimalPrime q := hqmin
    have hqm : q ≤ IsLocalRing.maximalIdeal T :=
      IsLocalRing.le_maximalIdeal hqmin'.isPrime.ne_top
    have hqeq : q = IsLocalRing.maximalIdeal T :=
      Minimal.eq_of_le hmin' ⟨hqmin'.isPrime, hqmin'.le⟩ hqm
    have hle : Q ≤ IsLocalRing.maximalIdeal T :=
      IsLocalRing.le_maximalIdeal hQprime.ne_top
    have heq : Q = IsLocalRing.maximalIdeal T :=
      le_antisymm hle (hqeq ▸ hqle)
    rw [heq]
    exact inferInstance
  exact hpos hLE0

#print axioms maximalIdeal_notMem_associatedPrimes_of_isCM

/-- A3 adapter: `Ass` as a `Finset` feeding C2-av — `associatedPrimes.finite`
(Stacks 00LC) + `.toFinset`, with the `Module.Finite` feed from C2-fin. -/
theorem assPrimes_finset (S : Type*) [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] :
    ∃ F : Finset (Ideal S), ∀ p, p ∈ F ↔ p ∈ associatedPrimes S S := by
  have _ : Module.Finite S S := QuotientByRegularIsCM.finite_self S
  have hfin := associatedPrimes.finite S S
  exact ⟨hfin.toFinset, fun p => hfin.mem_toFinset⟩

#print axioms assPrimes_finset

/-- B-reg bridge: avoiding every associated prime gives `IsSMulRegular`,
via `biUnion_associatedPrimes_eq_compl_regular`. -/
theorem isSMulRegular_of_forall_notMem_associatedPrimes
    (S : Type*) [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    (y : S) (_hy : y ∈ IsLocalRing.maximalIdeal S)
    (havoid : ∀ p ∈ associatedPrimes S S, y ∉ p) :
    IsSMulRegular S y := by
  have hbreg := biUnion_associatedPrimes_eq_compl_regular (R := S) (M := S)
  have hnotmem : y ∉ ⋃ p ∈ associatedPrimes S S, (p : Set S) := by
    intro h
    simp only [Set.mem_iUnion] at h
    obtain ⟨p, hpmem, hym⟩ := h
    exact havoid p hpmem hym
  rw [hbreg] at hnotmem
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_not] at hnotmem
  exact hnotmem

#print axioms isSMulRegular_of_forall_notMem_associatedPrimes

/-- Prime avoidance over `Ass`: `𝔪 ∉ Ass` yields `y ∈ 𝔪` avoiding every
`𝔭 ∈ Ass` (C2-av over the A3 finset; each `𝔭 ∈ Ass` satisfies `𝔪 ⊄ 𝔭`
since `𝔭 ≤ 𝔪` and `𝔭 ≠ 𝔪`). The per-step greedy extension input. -/
theorem exists_mem_maximal_avoid_ass
    (S : Type*) [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    (hmax : IsLocalRing.maximalIdeal S ∉ associatedPrimes S S) :
    ∃ y ∈ IsLocalRing.maximalIdeal S,
      ∀ p ∈ associatedPrimes S S, y ∉ p := by
  obtain ⟨F, hF⟩ := assPrimes_finset S
  have hprime : ∀ p ∈ F, p.IsPrime := by
    intro p hp
    rw [hF p] at hp
    exact (AssociatedPrimes.mem_iff.mp hp).isPrime
  have hle : ∀ p ∈ F, ¬ IsLocalRing.maximalIdeal S ≤ p := by
    intro p hp hle
    rw [hF p] at hp
    have hplt : p ≤ IsLocalRing.maximalIdeal S :=
      IsLocalRing.le_maximalIdeal
        (AssociatedPrimes.mem_iff.mp hp).isPrime.ne_top
    have heq : IsLocalRing.maximalIdeal S = p := le_antisymm hle hplt
    rw [heq] at hmax
    exact hmax hp
  obtain ⟨y, hyI, hyavoid⟩ :=
    QuotientByRegularIsCM.exists_mem_notMem_of_forall_not_le
      (IsLocalRing.maximalIdeal S) F hprime hle
  exact ⟨y, hyI, fun p hp => hyavoid p ((hF p).mpr hp)⟩

#print axioms exists_mem_maximal_avoid_ass

/-! ## HilbertFunctionCount close (§3) + top corollary at every `Q` -/

/-- `K(n)` from a greedy witness, via the capstone G-cap (the
single-cast length equation bridges to the double-cast form). -/
theorem K_of_greedy.{uK, uS} (n : ℕ) (hG : GreedyWitness.{uK, uS} n) :
    K.{uK, uS} n := by
  intro m K _ Q _ S _ _ _ hCI hdim
  obtain ⟨rs, hmem, hreg, hlen⟩ := hG m K Q S hCI hdim
  have hdimcast : ((((rs.length : ℕ)) : ℕ∞) : WithBot ℕ∞) =
      ringKrullDim S := by
    rw [← hlen]
    exact WithBot.coe_natCast rs.length
  exact VariableInductionCM.grade_eq_dim_of_maximal_regular hmem hreg hdimcast

#print axioms K_of_greedy

/-- `K(n)` conditional-exact on the three residuals: the sketch
implication supplies the greedy witness, closed by `K_of_greedy`. -/
theorem K_of_residuals.{uK, uS, uC, uGK, uGS} (n : ℕ)
    (hFR : FirstReg.{uK, uS}) (hC3a : C3aGapAll.{uC})
    (hSK : GreedyOfResiduals.{uK, uS, uC, uGK, uGS} n) :
    K.{uGK, uGS} n :=
  K_of_greedy n (hSK hFR hC3a)

#print axioms K_of_residuals

/-- `R_Q` is a CI quotient of itself (`rs₀ = []`): the span is `⊥`
(`span_memSet_nil`), so `R_Q ≃+* R_Q ⧸ span` via `quotEquivOfEq` +
`quotientBot`. -/
theorem ciQuotient_atPrime_self (m : ℕ) (K : Type*) [Field K]
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] :
    IsCIQuotient m K Q (Localization.AtPrime Q) := by
  refine ⟨[], ?_, VariableInductionCM.empty_isRegular, ?_⟩
  · intro r hr
    exact (List.not_mem_nil hr).elim
  · have hspan := span_memSet_nil (Localization.AtPrime Q)
    exact ⟨((Ideal.quotEquivOfEq hspan).trans
      (RingEquiv.quotientBot (Localization.AtPrime Q))).symm⟩

#print axioms ciQuotient_atPrime_self

/-- Top finiteness: `dim R_Q ≤ ↑embdim` (E-bd + the cast bridge). This
fires `K` at `n := spanFinrank`; N-sp/E-eq are not needed. -/
theorem dim_atPrime_le_spanFinrank (m : ℕ) (K : Type*) [Field K]
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] :
    ringKrullDim (Localization.AtPrime Q) ≤
      (((IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank :
        ℕ∞) : WithBot ℕ∞) := by
  have hbd := ringKrullDim_le_spanFinrank_maximalIdeal
    (Localization.AtPrime Q)
  rw [WithBot.coe_natCast]
  exact hbd

#print axioms dim_atPrime_le_spanFinrank

/-- Full C1 conditional on the three residuals: `IsCM R_Q` via `K` at
`rs₀ = []`, with `dim ≤ ↑embdim` supplying the bound. -/
theorem isCM_atPrime_of_residuals.{uK, uS, uC} (m : ℕ) (K : Type uK)
    [Field K]
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hFR : FirstReg.{uK, uS}) (hC3a : C3aGapAll.{uC})
    (hSK : GreedyOfResiduals.{uK, uS, uC, uK, uK}
      (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank) :
    CMQuotientPartial.IsCM (Localization.AtPrime Q) := by
  have hK := K_of_residuals _ hFR hC3a hSK
  exact hK m K Q (Localization.AtPrime Q)
    (ciQuotient_atPrime_self m K Q) (dim_atPrime_le_spanFinrank m K Q)

#print axioms isCM_atPrime_of_residuals

/-- Top corollary: `DepthEqDimAt` at every `Q`, conditional on the three
residuals (via C1-partial:138, `Iff.rfl`). -/
theorem depthEqDimAt_of_residuals.{uK, uS, uC} (m : ℕ) (K : Type uK)
    [Field K]
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hFR : FirstReg.{uK, uS}) (hC3a : C3aGapAll.{uC})
    (hSK : GreedyOfResiduals.{uK, uS, uC, uK, uK}
      (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank) :
    GradeDepthFragment.DepthEqDimAt m K Q :=
  (CMQuotientPartial.isCM_atPrime_iff_depthEqDimAt m K Q).mp
    (isCM_atPrime_of_residuals m K Q hFR hC3a hSK)

#print axioms depthEqDimAt_of_residuals

/-- Unconditional dim-≤-1 slice of the top corollary (via C1-partial). -/
theorem depthEqDimAt_of_dim_le_one (m : ℕ) (K : Type*) [Field K]
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hdim : ringKrullDim (Localization.AtPrime Q) ≤ 1) :
    GradeDepthFragment.DepthEqDimAt m K Q :=
  (CMQuotientPartial.isCM_atPrime_iff_depthEqDimAt m K Q).mp
    (CMQuotientPartial.isCM_atPrime_of_dim_le_one m K Q hdim)

#print axioms depthEqDimAt_of_dim_le_one

/-- SystemOfParameters mingens repackaged (span + `spanFinrank` equation; the dim
equation is E-eq's twin). Documents the N-sp input for the top-`n`. -/
theorem mingens_spanFinrank_atPrime (m : ℕ) (K : Type*) [Field K]
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] :
    ∃ rs : List (Localization.AtPrime Q),
      Ideal.ofList rs = IsLocalRing.maximalIdeal (Localization.AtPrime Q) ∧
        rs.length =
          (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank := by
  obtain ⟨rs, hspan, hlen, _⟩ :=
    SystemOfParameters.exists_list_ofList_maximalIdeal_atPrime Q
  exact ⟨rs, hspan, hlen⟩

#print axioms mingens_spanFinrank_atPrime

end CMQuotientFull
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
