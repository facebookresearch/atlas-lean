/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.Height
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Data.ENat.Monoid
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.PrimeAvoidance
import Appendix_FixedPoint.BezoutChain.Regularity.Grade.GradeDepthFragment
import Appendix_FixedPoint.BezoutChain.Dimension.LocalUnmixed
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Divisibility.Units
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.Algebra.GroupWithZero.Associated
import Mathlib.Algebra.Prime.Defs
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization

/-!
# Variable-subset induction for CM-ness of polynomial localizations

For `R = MvPolynomial (Fin m) K` (`[Field K]`), `P : Ideal R` prime, and
`S = Localization.AtPrime P`, the route to the deep core taken here
(`GradeDepthFragment` ledger G-(iii): `DepthEqDimAt`, grade of `R_P` equals `dim R_P`)
is direct variable-subset induction: build a regular sequence in `S` of length
`ringKrullDim S` by choosing, at each step, an element regular modulo the
previous quotient. No general CM theory is needed.

## §1 HilbertFunctionCount skeleton

Write `d = ringKrullDim S`. The induction is on `d`:

* L1 (base, `d = 0`): `[]` is regular of length `0`. Proved below as
  `empty_isRegular` (one-line apply of Mathlib `IsRegular.nil`).
* L2 (first step, `d ≠ 0 → length-1 sequence`): proved below for every domain
  local `S` (`exists_isSMulRegular_mem_maximal` +
  `singleton_isRegular_of_mem_maximal` + `singleton_regular_of_dim_ne_zero`,
  instantiated at `S = R_P` as `first_rung_atPrime`). Needs no unmixedness:
  in a domain every nonzero element is regular, so any nonzero element of the
  maximal ideal works — it need not be a variable. Mathlib inputs:
  `IsLocalRing.isField_iff_maximalIdeal_eq`,
  `ringKrullDim_eq_zero_of_isField`,
  `Module.Flat.isSMulRegular_of_nonZeroDivisors`,
  `mem_nonZeroDivisors_iff_ne_zero`, plus the `top_ne_smul` properness pattern
  of `RegularityBridge.top_ne_smul_ofList_of_forall_map_zero`.
* L3 (dimension drop across a regular element of the maximal ideal):
  proved below as `dim_drop_quotSMulTop` /
  `dim_drop_quotient_span` (one-line applies of Mathlib
  `ringKrullDim_quotSMulTop_succ_eq_ringKrullDim` /
  `ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim`).
* L4 (cons assembly): proved below as `cons_regular` (apply of Mathlib
  `IsRegular.cons`) and `length_two_of_residual` (apply of Mathlib
  `IsRegular.cons`). The iterated-count vehicle for the full telescope is
  Mathlib `supportDim_add_length_eq_supportDim_of_isRegular`, already consumed
  by `GradeDepthFragment.grade_le_supportDim`; no new work there.
* L5 (second rung: a regular element on the first quotient): assembled below as
  `second_rung_of_residuals` / `length_two_second_rung` (conditional on
  `VarUnmixedOneResidual` only) and instantiated at `P` as `second_rung_atPrime`.
  The content is: (a) associated-prime control for `S ⧸ span {x}` in the
  localization, stated as `VarUnmixedOneResidual` (globally, i.e. for
  `S = MvPolynomial`, this is the proved `k = 1` chain:
  `Unmixedness.mem_minimalPrimes_of_successive_singleton` +
  `HeightDrop.assHeight_le_one_of_successive_singleton`; the
  globalization-to-localization transfer is factored below as
  `transfer_unmixed_of_global`: global chain + Ass-pullback (`hpull`) +
  minimality-pushforward (`hpush`)); plus the height facet, which needs no
  transfer: `height_le_one_of_unmixed` derives `height ≤ 1` for every
  associated prime from `VarUnmixedOneResidual` via Krull's Hauptidealsatz
  (`Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes`); plus
  (b) prime-avoidance selection of the next element inside the maximal ideal,
  provided by the sibling file `Regularity/Avoid/PrimeAvoidance.lean`
  (`exists_isSMulRegular_mem_of_forall_not_le_ass`, thin wraps over Mathlib
  `Ideal.subset_union_prime[_finite]` + `associatedPrimes.finite`) and consumed
  here.
  Note the route-R5 counterexample (`HeightDrop.lean` §1, via
  `LocalUnmixed`: `k[a,b,c] ⧸ (ab, ac)` localized, regular `x = a + b`, an
  embedded associated prime of height `2 ≠ 1`): after the first quotient the
  ring is no longer a UFD, so the `k = 1` UFD argument cannot reapply and a
  naive "pick a variable" step is false in general. Zerodivisor analysis,
  not variable-picking, is the load-bearing content from L5 on.
* L6 (`k ≥ 3` / maximality to length `d`): conditional
  (exact hypothesis list in §4). Proved: (a) list-form uniform bound
  `VarHeightDropResidualList` + its Krull direction
  `heightDropList_of_forall_mem_minimalPrimes` (weakest explicit hypothesis:
  per-prime minimality over `ofList rs`, via Mathlib
  `Ideal.height_le_card_of_mem_minimalPrimes_span_finset` — the local mirror of
  the backward direction of `HeightDrop.heightDrop_iff_forall_mem_minimalPrimes`);
  (b) general-rung PrimeAvoidance selection `nextRung_of_heightDropList`, via the
  avoidance input `maximalIdeal_notLe_of_heightDropList` (height `≤ k < dim`
  keeps the maximal ideal out of every associated prime — the L5 height
  argument generalized from `1` to `rs.length`); (c) the append bridge
  `isRegular_append_singleton_of_quotient_regular` (via Mathlib
  `isWeaklyRegular_append_iff` + `isWeaklyRegular_singleton_iff` +
  `IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal` — no take/get
  manipulation, no quotient-identification gap: the `S ⧸ ↑ofList` vs
  `S ⧸ ofList • ⊤` transport is `Submodule.quotEquivOfEq`); (d) induction
  bookkeeping `exists_regular_of_forall_nextRung` + per-rung feed
  `nextRung_append_of_heightDropList`; (e) AtPrime capstones
  `varHeightDropResidualList_of_fin` (Fin-form `VarHeightDropResidual` feeds the
  list machine on `ofFn` lists) and `varTarget_of_uniformHeightDrop`
  (`VarTarget`: length-`dim` regular sequence from the uniform list bound +
  the finite-dim equation); (f) grade capstones
  `grade_eq_dim_of_maximal_regular` (`GradeDepthFragment.grade_le_ringKrullDim` +
  witness lower bound) and `grade_telescope_of_maximal_regular` (the imported
  `GradeDepthFragment.grade_quotIter_add_eq_grade` telescope).
  residual (exact): per-prefix `VarHeightDropResidualList` (equivalently
  per-prime minimality over each `ofList` prefix) + the finite-dim equation
  `hdim`. The Fin-form `VarHeightDropResidual` (uniform-`k` bound for
  associated primes of successive local quotients; mirrors
  `HeightDrop.HeightDropResidualAt`, whose `k = 2` case is the step-(iv)
  residual) is taken as an explicit hypothesis wherever needed, never assumed.

## §2 Results proved in this file

L1–L4 in full: `empty_isRegular`, `singleton_isRegular_of_mem_maximal`,
`exists_isSMulRegular_mem_maximal`, `singleton_regular_of_dim_ne_zero`,
`cons_regular`, `dim_drop_quotSMulTop`, `dim_drop_quotient_span`,
`length_two_of_residual`, `first_rung_atPrime`, plus the target predicate
`VarTarget`. L5 assembled conditionally: `height_le_one_of_unmixed`
(Hauptidealsatz facet), `transfer_unmixed_of_global` (transfer
factorization), `quotientSingletonResidual_of_mem_maximal` (residual assembly),
`second_rung_of_residuals` / `length_two_second_rung` (conditional on
`VarUnmixedOneResidual` only) and `second_rung_atPrime` at `P`.
L6 proved conditionally (see §4): `VarHeightDropResidualList`,
`heightDropList_of_forall_mem_minimalPrimes`,
`maximalIdeal_notLe_of_heightDropList`, `nextRung_of_heightDropList`,
`isRegular_append_singleton_of_quotient_regular`,
`nextRung_append_of_heightDropList`, `exists_regular_of_forall_nextRung`,
`maximalIdeal_smul_top_lt_top`, `grade_eq_dim_of_maximal_regular`,
`grade_telescope_of_maximal_regular`, `varHeightDropResidualList_of_fin`,
`varTarget_of_uniformHeightDrop` — all conditional on the exact §4
list only.

## §3 Deep residual

Exact missing statement: the globalization-to-localization
transfer inputs `hpull` / `hpush` of `transfer_unmixed_of_global` (i.e. control
of `Ass S (S ⧸ span {x})` from the proved global `k = 1` chain), and
`VarHeightDropResidual` uniformly beyond the second rung. Closed here:
L5(b) prime-avoidance selection (provided by `PrimeAvoidance.lean` as
`exists_isSMulRegular_mem_of_forall_not_le_ass` over Mathlib
`Ideal.subset_union_prime[_finite]` + `associatedPrimes.finite`, consumed by
`second_rung_of_residuals`); the L5 height facet (`height_le_one_of_unmixed`
via Krull's Hauptidealsatz, no transfer needed); the L5 second-rung assembly
itself (`quotientSingletonResidual_of_mem_maximal`, `second_rung_of_residuals`,
`length_two_second_rung`, `second_rung_atPrime`). Evidence on the transfer
(Mathlib v4.34.0): the global→local direction exists as
`Module.associatedPrimes.mem_associatedPrimes_atPrime_of_mem_associatedPrimes`
—but targets `LocalizedModule.AtPrime P M`, not the ring quotient
`S ⧸ span {x}`; quotient-localization commutation exists at `LocalizedModule`
level (`Submodule.localizedQuotientEquiv`, via
`IsLocalizedModule.toLocalizedQuotient`) — but no Mathlib lemma composes it
with Ass-pullback plus minimality-pushforward onto
`Ass (Localization.AtPrime P) (S ⧸ span {x})`, and no `minimalPrimes`
localization-transfer exists anywhere under
`Mathlib/RingTheory/Localization/` (only
`IsLocalization.subsingleton_primeSpectrum_of_mem_minimalPrimes`). The
missing piece (quotient-localization commutation at the ring level
with Ass control) is confirmed missing. No placeholder proofs
are used anywhere in this file.

## §4 L6 ledger

Status: conditional (exact list below); the file checks with
`lake env lean` exit `0`.

Exact hypotheses for `varTarget_of_uniformHeightDrop` (hence for the
length-`dim` regular sequence at `P`):

1. `hdim : ringKrullDim (Localization.AtPrime P) = ((d : ℕ) : WithBot ℕ∞)`
   (finite-dim equation — true with `d ≤ m`, pinned here explicitly).
2. `hdrop: ∀ rs, (∀ r ∈ rs, r ∈ maximal) → rs.length < d →
   VarHeightDropResidualList rs` (uniform list-form height bound at every
   maximal-ideal prefix). By `heightDropList_of_forall_mem_minimalPrimes`
   (Krull direction, proved) this is implied by — and hence weakest as —
   per-prime minimality of every `Q ∈ Ass (S ⧸ ofList rs)` over `ofList rs`.

Everything else (Noetherian/local/domain/`Module.Finite`/`Nontrivial`
instances, PrimeAvoidance selection, append bridge, induction, grade upper bound
`GradeDepthFragment.grade_le_ringKrullDim`, telescope
`GradeDepthFragment.grade_quotIter_add_eq_grade`) is proved or automatic.

Why the uniform bound has no unconditional close here:
per-prefix minimality over `ofList rs` for `rs.length ≥ 2`. Evidence:
(i) the route-R5 killer (`HeightDrop.lean` §1 via `LocalUnmixed`):
`k[a,b,c] ⧸ (ab, ac)` localized carries a regular element whose quotient has
an embedded associated prime of height `2 ≠ 1` — unmixedness does not
propagate across quotients in general, so the `k = 1` UFD argument cannot
reapply and minimality at `k ≥ 2` is genuine CM content, not bookkeeping;
(ii) counterpart reduction: `HeightDrop.heightDrop_iff_forall_mem_minimalPrimes`
shows the global uniform bound is unmixedness-at-`k`, and the local Krull
direction above shows minimality is also sufficient here — so the residual is
pinned from both sides with no weaker address available; (iii) counterexample
search for the residual statement itself: none found (it holds for
successive-regular families) — the block is a missing input (CM-ness of
successive quotients = the `GradeDepthFragment` G-(iii) crux), not a refutation.
Downstream use: feed per-prefix minimality (or the list bound)
as the explicit conditional; nothing in this file assumes it.

Update (rungs 0–1 closed unconditionally; residual narrowed to
length ≥ 2 — status stays conditional, exact list now `hdim` + `hdrop` at
`2 ≤ rs.length` via `varTarget_of_heightDrop_ge_two`). Proved:
(a) `smulRegular_ne_zero`; (b) domain core
`mem_minimalPrimes_bot_of_mem_associatedPrimes_bot` (generic `k = 0` argument)
+ `mem_minimalPrimes_of_ofList_nil` + rung-0 `varHeightDropResidualList_nil`
(Krull direction); (c) UFD argument
`mem_minimalPrimes_of_ufd_span_singleton` (generic `k = 1`; the `pow_succ`
step needs `.symm` + `Nat.succ_eq_add_one` here — the source proof's defeq
goes through concrete `MvPolynomial` instances, unavailable generically) +
`varUnmixedOneResidual_of_ne_zero` (L5 residual direct — the §3
`hpull`/`hpush` transfer is not needed for the L5 height facet) + rung-1
`varHeightDropResidualList_singleton`; (d) AtPrime capstones
`varTarget_of_heightDrop_ge_two` and `length_two_atPrime` (L5
unconditional). Length ≥ 2 (CM-ness of `S ⧸ (x)`) stays open: the UFD
argument cannot reapply, the DVR route bottoms at step-(iv) transfer
(`CohenMacaulayFragment` ledger), and the remaining routes are Koszul/AB or from-scratch
Macaulay-`k = 2` (not developed here). Narrowest next step: per-prefix
minimality at length exactly 2 for successive-regular pairs in `AtPrime`
localizations.

## Related files

* `Regularity/Grade/GradeDepthFragment.lean` (`GradeDepthFragment` namespace): `GradeDropChain`
  pattern
  (iterated drop along a successive family) + deep-core ledger G-(iii) with the
  Koszul/Auslander–Buchsbaum gap analysis and the direct-induction
  recommendation this file implements.
* `Regularity/Unmixed/CohenMacaulayFragment.lean` (bare `Bezout` namespace): U1 DVR machinery
  (`hasUniqueIrreducible_atPrime_height_one`, `u1_dvr_at_height_one`), the U2
  steps (i)–(iii), and the roadblock ledger (free UFD/domain instances,
  missing transfer bridge).
* `Regularity/Unmixed/HeightDrop.lean` (`HeightDrop` namespace): routes R1–R5 report +
  the `k[a,b,c] ⧸ (ab, ac)` counterexample to respect (route R5),
  `HeightDropResidualAt` (mirrored here as `VarHeightDropResidual`),
  `localized_dim_zero_of_height_le`, `minimal_of_height_le`, and the `j = 0, 1`
  prefix instances (last lengths whose height-drop goes through).
* `Dimension/TriangularChain.lean` (bare `Bezout` namespace): normap/shear tools
  (`quotient_dim_of_normap`, `triShear`, `triangular_monic_chain`) — the
  normalization side; not consumed here, cited so the two tracks stay aligned.


## References

Mathlib (v4.34.0):

* `RingTheory/Regular/RegularSequence.lean`: `IsRegular` (`nil`, `cons`, `cons'`,
  anonymous `⟨weak, top_ne_smul⟩` constructor), `isRegular_cons_iff`,
  `isWeaklyRegular_singleton_iff`, `Ideal.ofList_singleton`,
  `Ideal.ofList_cons`, `Submodule.top_eq_ofList_cons_smul_iff`.
* `RingTheory/Regular/IsSMulRegular.lean`:
  `LinearEquiv.isSMulRegular_congr` (transport across the `S`-linear
  `QuotSMulTop`/`S ⧸ span` identification).
* `LinearAlgebra/Quotient/Defs.lean`: `Submodule.quotEquivOfEq`.
* `RingTheory/KrullDimension/Regular.lean`:
  `ringKrullDim_quotSMulTop_succ_eq_ringKrullDim`,
  `ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim`,
  `supportDim_add_length_eq_supportDim_of_isRegular`.
* `RingTheory/KrullDimension/Field.lean`: `ringKrullDim_eq_zero_of_isField`.
* `RingTheory/LocalRing/MaximalIdeal/Basic.lean`:
  `IsLocalRing.maximalIdeal`, `maximalIdeal.isMaximal`,
  `IsLocalRing.isField_iff_maximalIdeal_eq`.
* `RingTheory/Localization/AtPrime/Basic.lean`: `Localization.AtPrime` (abbrev),
  `AtPrime.isLocalRing`, `IsLocalization.isDomain_of_local_atPrime`.
* `RingTheory/Flat/TorsionFree.lean`:
  `Module.Flat.isSMulRegular_of_nonZeroDivisors`.
* `Algebra/GroupWithZero/NonZeroDivisors.lean`:
  `mem_nonZeroDivisors_iff_ne_zero`.
* `RingTheory/Ideal/Operations.lean`: `Submodule.span_smul_eq`,
  `Submodule.set_smul_top_eq_span`, `Submodule.ideal_span_singleton_smul`
  (for `x • ⊤ = span {x}`).
* `RingTheory/Ideal/KrullsHeightTheorem.lean`:
  `Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes` (Hauptidealsatz).
* `RingTheory/Ideal/Span.lean`: `Ideal.span_singleton_le_iff_mem`
  (plus the `(Ideal.span {x}).IsPrincipal` instance).
* `RingTheory/Ideal/AssociatedPrime/Basic.lean`: `associatedPrimes`,
  `AssociatedPrimes.mem_iff`, `IsAssociatedPrime.isPrime`.
* `RingTheory/Ideal/AssociatedPrime/Localization.lean` (evidence only, for the
  transfer residual):
  `Module.associatedPrimes.mem_associatedPrimes_atPrime_of_mem_associatedPrimes`.
* `Algebra/Module/LocalizedModule/Submodule.lean` (evidence only):
  `Submodule.localizedQuotientEquiv`, `IsLocalizedModule.toLocalizedQuotient`.
* `RingTheory/LocalRing/MaximalIdeal/Basic.lean`:
  `IsLocalRing.maximalIdeal.isMaximal`.
* `RingTheory/Ideal/Height.lean`:
  `IsLocalRing.maximalIdeal_height_eq_ringKrullDim`.
* `RingTheory/Regular/RegularSequence.lean` (L6 rung machine):
  `isWeaklyRegular_append_iff`, `isWeaklyRegular_singleton_iff`,
  `RingTheory.Sequence.IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal`.
* `RingTheory/Ideal/KrullsHeightTheorem.lean` (L6 Krull direction):
  `Ideal.height_le_card_of_mem_minimalPrimes_span_finset`.
* `RingTheory/LocalRing/MaximalIdeal/Basic.lean` (L6 nondegeneracy):
  `IsLocalRing.maximalIdeal_le_jacobson`.
* `RingTheory/Nakayama.lean` (L6 nondegeneracy):
  `Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator`.
* `Data/Finset/Card.lean` (L6 Krull direction): `List.toFinset_card_le`.

Project (`Formalization/Appendix_FixedPoint/BezoutChain/Regularity/`):

* `PrimeAvoidance.lean` (`PrimeAvoidance` namespace, imported here):
  `exists_isSMulRegular_mem_of_forall_not_le_ass` (L5(b) feed, wraps
  `Ideal.subset_union_prime[_finite]` + `associatedPrimes.finite`;
  also the L6 general-rung feed via `nextRung_of_heightDropList`).
* `GradeDepthFragment.lean` (`GradeDepthFragment` namespace, imported here):
  `grade`, `quotIter`, `mem_gradeSet_of_isRegular`,
  `le_grade_of_mem_gradeSet`, `grade_le_ringKrullDim` (grade capstone),
  `grade_quotIter_add_eq_grade` (iterated-drop telescope, consumed by
  `grade_telescope_of_maximal_regular`).
-/


local infixl:50 " ~ᵤ " => Associated

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace VariableInductionCM

open RingTheory.Sequence

open scoped Pointwise

variable {S : Type*} [CommRing S]

/-- Base rung L1 (`d = 0`): the empty sequence is regular on any nontrivial
module. One-line apply of Mathlib `IsRegular.nil`. -/
theorem empty_isRegular [Nontrivial S] : IsRegular S ([] : List S) :=
  IsRegular.nil S S

/-- Singleton tool for L2: a regular element in the maximal ideal gives a
length-1 regular sequence. Properness follows the
`RegularityBridge.top_ne_smul_ofList_of_forall_map_zero` pattern
(`ofList` unfolds to the span, then `span_smul_eq` + `set_smul_top_eq_span`),
with the span kept below the maximal ideal instead of an evaluation kernel. -/
theorem singleton_isRegular_of_mem_maximal [IsLocalRing S]
    {x : S} (hmax : x ∈ IsLocalRing.maximalIdeal S) (hsmul : IsSMulRegular S x) :
    IsRegular S [x] := by
  have hset : ({ r | r ∈ [x] } : Set S) = {x} := by
    ext r
    simp only [Set.mem_ofPred_eq, List.mem_singleton, Set.mem_singleton_iff]
  have hspan_le : Ideal.span { r | r ∈ [x] } ≤ IsLocalRing.maximalIdeal S := by
    rw [hset]
    exact (Ideal.span_singleton_le_iff_mem _).mpr hmax
  have hspan : Ideal.span { r | r ∈ [x] } ≠ ⊤ :=
    ne_top_of_le_ne_top (Ideal.IsMaximal.ne_top inferInstance) hspan_le
  have hproper : (⊤ : Submodule S S) ≠ Ideal.ofList [x] • ⊤ := by
    change (⊤ : Submodule S S) ≠ Ideal.span { r | r ∈ [x] } • ⊤
    rw [Submodule.span_smul_eq, Submodule.set_smul_top_eq_span]
    exact Ne.symm hspan
  exact ⟨(isWeaklyRegular_singleton_iff _ x).mpr hsmul, hproper⟩

/-- First-step existence for L2 (domain case): positive Krull dimension supplies
a regular element in the maximal ideal. If the maximal ideal were `⊥`, `S`
would be a field (`isField_iff_maximalIdeal_eq`) hence dimension zero,
against `hdim`; any nonzero member is a non-zerodivisor, hence SMul-regular
via flatness of the self-module. Needs no unmixedness. -/
theorem exists_isSMulRegular_mem_maximal [IsDomain S] [IsLocalRing S]
    (hdim : ringKrullDim S ≠ 0) :
    ∃ x ∈ IsLocalRing.maximalIdeal S, IsSMulRegular S x := by
  have hmax_ne : IsLocalRing.maximalIdeal S ≠ ⊥ := by
    intro hcon
    have hfield : IsField S :=
      IsLocalRing.isField_iff_maximalIdeal_eq.mpr hcon
    exact hdim (ringKrullDim_eq_zero_of_isField hfield)
  obtain ⟨x, hxmem, hx0⟩ := (Submodule.ne_bot_iff _).mp hmax_ne
  exact ⟨x, hxmem, Module.Flat.isSMulRegular_of_nonZeroDivisors
    (mem_nonZeroDivisors_iff_ne_zero.mpr hx0)⟩

/-- First rung L2 (domain case): a length-1 regular sequence inside the maximal
ideal whenever the dimension is nonzero. -/
theorem singleton_regular_of_dim_ne_zero [IsDomain S] [IsLocalRing S]
    (hdim : ringKrullDim S ≠ 0) :
    ∃ x ∈ IsLocalRing.maximalIdeal S, IsRegular S [x] := by
  obtain ⟨x, hxmem, hxreg⟩ := exists_isSMulRegular_mem_maximal hdim
  exact ⟨x, hxmem, singleton_isRegular_of_mem_maximal hxmem hxreg⟩

/-- Cons assembly L4: regularity of the head plus regularity of the tail on the
quotient assembles to regularity of the cons. Apply of Mathlib
`IsRegular.cons`. -/
theorem cons_regular {M : Type*} [AddCommGroup M] [Module S M]
    {x : S} {rs : List S}
    (hhead : IsSMulRegular M x) (htail : IsRegular (QuotSMulTop x M) rs) :
    IsRegular M (x :: rs) :=
  IsRegular.cons hhead htail

/-- Dimension drop L3 (quotient-module form): a regular element of the maximal
ideal drops Krull dimension by exactly one. Apply of Mathlib
`ringKrullDim_quotSMulTop_succ_eq_ringKrullDim`. -/
theorem dim_drop_quotSMulTop [IsNoetherianRing S] [IsLocalRing S]
    {x : S} (hreg : IsSMulRegular S x) (hmax : x ∈ IsLocalRing.maximalIdeal S) :
    ringKrullDim (QuotSMulTop x S) + 1 = ringKrullDim S :=
  ringKrullDim_quotSMulTop_succ_eq_ringKrullDim hreg hmax

/-- Dimension drop L3 (quotient-ring form): same content for `S ⧸ span {x}`.
Apply of Mathlib `ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim`. -/
theorem dim_drop_quotient_span [IsNoetherianRing S] [IsLocalRing S]
    {x : S} (hreg : IsSMulRegular S x) (hmax : x ∈ IsLocalRing.maximalIdeal S) :
    ringKrullDim (S ⧸ Ideal.span {x}) + 1 = ringKrullDim S :=
  ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim hreg hmax

/-- Quotient-singleton residual (the exact statement needed at rung L5):
regularity of the singleton `[y']` (plain `S`-scalars) on `QuotSMulTop x S`,
in the exact shape `IsRegular.cons` consumes. Producing a proof of this needs
zerodivisor-avoidance in `S ⧸ span {x}` controlled by `VarUnmixedOneResidual`,
so this is an explicit hypothesis wherever used, never assumed. -/
def QuotientSingletonResidual (x y' : S) : Prop :=
  IsRegular (QuotSMulTop x S) [y']

/-- Length-two assembly L4, conditional on the L5 residual: one apply of
Mathlib `IsRegular.cons`. -/
theorem length_two_of_residual {x y' : S}
    (hhead : IsSMulRegular S x) (hres : QuotientSingletonResidual x y') :
    IsRegular S [x, y'] :=
  IsRegular.cons hhead hres

/-- Unmixedness residual for L5(a): every associated prime of `S ⧸ span {x}`
is minimal over `span {x}`. For `S = MvPolynomial (Fin m) K` this is the proved
`k = 1` chain (`Unmixedness.mem_minimalPrimes_of_successive_singleton`); for
`S = Localization.AtPrime P` the globalization-to-localization transfer is
open — hence an explicit hypothesis. -/
def VarUnmixedOneResidual (x : S) : Prop :=
  ∀ Q ∈ associatedPrimes S (S ⧸ Ideal.span {x}),
    Q ∈ (Ideal.span {x}).minimalPrimes

/-- Height-drop residual for L6 (mirrors `HeightDrop.HeightDropResidualAt` in
content; restated here so this file stays standalone): associated primes of a
local successive quotient have height at most `k`. The `k = 2` case is the
step-(iv) residual (see the `CohenMacaulayFragment` ledger). Explicit hypothesis only,
never assumed. -/
def VarHeightDropResidual (m : ℕ) (K : Type*) [Field K]
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    {k : ℕ} (q : Fin k → Localization.AtPrime P) : Prop :=
  ∀ (Q : Ideal (Localization.AtPrime P)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (Localization.AtPrime P ⧸ Ideal.span (Set.range q)) →
    Q.height ≤ (k : ℕ∞)

/-- Height control from unmixedness (L5(a) height facet): Krull's
Hauptidealsatz (`Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes`)
turns minimality over the principal ideal `span {x}` into `height ≤ 1` for
every associated prime of `S ⧸ span {x}`. This facet needs no
globalization-to-localization transfer — the transfer residual lives entirely
in `VarUnmixedOneResidual` itself (see `transfer_unmixed_of_global`). -/
theorem height_le_one_of_unmixed [IsNoetherianRing S] {x : S}
    (hunmixed : VarUnmixedOneResidual x) :
    ∀ Q ∈ associatedPrimes S (S ⧸ Ideal.span {x}), Q.height ≤ 1 :=
  fun Q hQ =>
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ Q (hunmixed Q hQ)

/-- Transfer factorization (L5(a) record): `VarUnmixedOneResidual` follows from
the proved global `k = 1` chain (`hglobal`, the exact shape of
`Unmixedness.mem_minimalPrimes_of_successive_singleton` at `a : R`) plus two
localization bookkeeping inputs: Ass-pullback (`hpull`: associated primes of
the local quotient pull back along `f` to associated primes of the global
quotient) and minimality-pushforward (`hpush`: minimality over `span {a}`
pushes forward to minimality over `span {x}`). Both inputs are explicit
hypotheses, never assumed: closing them is the transfer residual. Mathlib
evidence (v4.34.0): the global→local
direction exists as
`Module.associatedPrimes.mem_associatedPrimes_atPrime_of_mem_associatedPrimes`
but targets `LocalizedModule.AtPrime P M`, not the ring quotient
`S ⧸ span {x}`; quotient-localization commutation exists at `LocalizedModule`
level (`Submodule.localizedQuotientEquiv` via
`IsLocalizedModule.toLocalizedQuotient`); no Mathlib lemma composes these
with Ass-pullback plus minimality-pushforward onto
`Ass (Localization.AtPrime P) (S ⧸ span {x})`, and no `minimalPrimes`
localization-transfer exists under `Mathlib/RingTheory/Localization/`. -/
theorem transfer_unmixed_of_global {R : Type*} [CommRing R]
    {f : R →+* S} {a : R} {x : S}
    (hglobal : ∀ Q₀ ∈ associatedPrimes R (R ⧸ Ideal.span {a}),
      Q₀ ∈ (Ideal.span {a}).minimalPrimes)
    (hpull : ∀ Q ∈ associatedPrimes S (S ⧸ Ideal.span {x}),
      Q.comap f ∈ associatedPrimes R (R ⧸ Ideal.span {a}))
    (hpush : ∀ Q ∈ associatedPrimes S (S ⧸ Ideal.span {x}),
      Q.comap f ∈ (Ideal.span {a}).minimalPrimes →
      Q ∈ (Ideal.span {x}).minimalPrimes) :
    VarUnmixedOneResidual x :=
  fun Q hQ => hpush Q hQ (hglobal _ (hpull Q hQ))

/-- Residual assembly (L5 core): a maximal-ideal element that is
SMul-regular on the ring quotient `S ⧸ span {x}` (the `PrimeAvoidance` output)
yields the second-rung residual `QuotientSingletonResidual x y'`, i.e.
regularity + properness of the singleton `[y']` in the exact shape
`IsRegular.cons` consumes. The weak half transports `S`-scalar regularity
across the `S`-linear identification `QuotSMulTop x S ≃ S ⧸ span {x}`
(`Submodule.quotEquivOfEq` over `x • ⊤ = span {x}`,
via `Submodule.ideal_span_singleton_smul`); the properness half reduces,
via `Submodule.top_eq_ofList_cons_smul_iff`, to `span {x, y'} ≠ ⊤`, which
holds since both generators lie in the maximal ideal (same
`span_smul_eq` + `set_smul_top_eq_span` pattern as
`singleton_isRegular_of_mem_maximal`). -/
theorem quotientSingletonResidual_of_mem_maximal [IsLocalRing S]
    {x y' : S} (hmax : x ∈ IsLocalRing.maximalIdeal S)
    (hyMax : y' ∈ IsLocalRing.maximalIdeal S)
    (hreg : IsSMulRegular (S ⧸ Ideal.span {x}) y') :
    QuotientSingletonResidual x y' := by
  have hsub_eq : (Ideal.span {x} : Submodule S S) = x • (⊤ : Submodule S S) := by
    simp [← Submodule.ideal_span_singleton_smul]
  have e : QuotSMulTop x S ≃ₗ[S] (S ⧸ Ideal.span {x}) :=
    Submodule.quotEquivOfEq _ _ hsub_eq.symm
  have hweak_S : IsSMulRegular (QuotSMulTop x S) y' :=
    (e.isSMulRegular_congr y').mpr hreg
  have hweak : IsWeaklyRegular (QuotSMulTop x S) [y'] :=
    (isWeaklyRegular_singleton_iff _ _).mpr hweak_S
  have hle : Ideal.ofList [x, y'] ≤ IsLocalRing.maximalIdeal S := by
    rw [Ideal.ofList_cons, Ideal.ofList_singleton]
    exact sup_le ((Ideal.span_singleton_le_iff_mem _).mpr hmax)
      ((Ideal.span_singleton_le_iff_mem _).mpr hyMax)
  have htop_ne : (⊤ : Submodule S S) ≠ Ideal.ofList [x, y'] • ⊤ := by
    intro hcon
    have hI : Ideal.ofList [x, y'] • (⊤ : Submodule S S)
        = (Ideal.ofList [x, y'] : Submodule S S) := by
      change Ideal.span { r | r ∈ [x, y'] } • ⊤ = _
      rw [Submodule.span_smul_eq, Submodule.set_smul_top_eq_span]
    have htop : (Ideal.ofList [x, y'] : Submodule S S) = ⊤ := by
      rw [← hI, ← hcon]
    exact ne_top_of_le_ne_top
      (Ideal.IsMaximal.ne_top inferInstance) hle htop
  have hproper : (⊤ : Submodule S (QuotSMulTop x S))
      ≠ Ideal.ofList [y'] • ⊤ := by
    intro hcon
    exact htop_ne ((Submodule.top_eq_ofList_cons_smul_iff x [y']).mpr hcon)
  exact ⟨hweak, hproper⟩

/-- Second rung L5 (conditional on `VarUnmixedOneResidual` only): if
`1 < ringKrullDim S`, the maximal ideal contains an element whose quotient
image is regular on the first quotient. Proof: `height_le_one_of_unmixed`
bounds every associated prime by `1`, so none contains the maximal ideal
(maximality + `maximalIdeal_height_eq_ringKrullDim`); `PrimeAvoidance`
(`exists_isSMulRegular_mem_of_forall_not_le_ass`) selects the element; the
residual assembly above concludes. Neither `x`-regularity nor
`VarHeightDropResidual` is needed at this rung — the latter stays the L6
address. -/
theorem second_rung_of_residuals [IsNoetherianRing S] [IsLocalRing S]
    {x : S} (hmax : x ∈ IsLocalRing.maximalIdeal S)
    (hunmixed : VarUnmixedOneResidual x)
    (hdim : 1 < ringKrullDim S) :
    ∃ y' ∈ IsLocalRing.maximalIdeal S, QuotientSingletonResidual x y' := by
  have hle : ∀ P ∈ associatedPrimes S (S ⧸ Ideal.span {x}),
      ¬ IsLocalRing.maximalIdeal S ≤ P := by
    intro P hP hcon
    have hPprime : P.IsPrime := (AssociatedPrimes.mem_iff.mp hP).isPrime
    have heq : IsLocalRing.maximalIdeal S = P :=
      (IsLocalRing.maximalIdeal.isMaximal S).eq_of_le hPprime.ne_top hcon
    have h1 := height_le_one_of_unmixed hunmixed P hP
    have hlt : (1 : WithBot ℕ∞) < ringKrullDim S := hdim
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, heq] at hlt
    have hle1 : ((P.height : ℕ∞) : WithBot ℕ∞) ≤ 1 := by exact_mod_cast h1
    exact absurd (lt_of_lt_of_le hlt hle1) (lt_irrefl _)
  obtain ⟨y', hyMax, hyReg⟩ :=
    PrimeAvoidance.exists_isSMulRegular_mem_of_forall_not_le_ass
      (IsLocalRing.maximalIdeal S) hle
  exact ⟨y', hyMax, quotientSingletonResidual_of_mem_maximal hmax hyMax hyReg⟩

/-- Length-two assembly L4+L5, conditional on the L5(a) residual only: one more
apply of Mathlib `IsRegular.cons` after the second rung. -/
theorem length_two_second_rung [IsNoetherianRing S] [IsLocalRing S]
    {x : S} (hhead : IsSMulRegular S x)
    (hmax : x ∈ IsLocalRing.maximalIdeal S)
    (hunmixed : VarUnmixedOneResidual x)
    (hdim : 1 < ringKrullDim S) :
    ∃ y', IsRegular S [x, y'] := by
  obtain ⟨y', _, hres⟩ := second_rung_of_residuals hmax hunmixed hdim
  exact ⟨y', length_two_of_residual hhead hres⟩

/-- List-form height residual for L6 (general-`k` form of the uniform bound):
every associated prime of `S ⧸ ofList rs` has height at most `rs.length`.
This is the shape the rung machine consumes: `ofList rs` is the ideal spanned
by the regular sequence built so far. The Fin-form `VarHeightDropResidual`
feeds it on `ofFn` lists (`varHeightDropResidualList_of_fin`). Explicit
hypothesis only, never assumed. -/
def VarHeightDropResidualList (rs : List S) : Prop :=
  ∀ Q ∈ associatedPrimes S (S ⧸ Ideal.ofList rs), Q.height ≤ (rs.length : ℕ∞)

/-- Krull direction (L6 weakest-hypothesis pin): per-prime minimality
over `ofList rs` implies the list-form height bound. Via Mathlib
`Ideal.height_le_card_of_mem_minimalPrimes_span_finset` at
`s = rs.toFinset` (whose span is `ofList rs`) plus
`List.toFinset_card_le`. This is the local mirror of the backward direction of
`HeightDrop.heightDrop_iff_forall_mem_minimalPrimes`: minimality over the
built ideal is the weakest explicit hypothesis for the uniform bound. -/
theorem heightDropList_of_forall_mem_minimalPrimes [IsNoetherianRing S]
    {rs : List S}
    (hmin : ∀ Q ∈ associatedPrimes S (S ⧸ Ideal.ofList rs),
      Q ∈ (Ideal.ofList rs).minimalPrimes) :
    VarHeightDropResidualList rs := by
  classical
  intro Q hQ
  have hspan : Ideal.span (↑rs.toFinset : Set S) = Ideal.ofList rs := by
    change Ideal.span (↑rs.toFinset : Set S) = Ideal.span {r | r ∈ rs}
    congr 1
    ext x
    simp
  have hminQ : Q ∈ (Ideal.span (↑rs.toFinset : Set S)).minimalPrimes := by
    rw [hspan]
    exact hmin Q hQ
  have hle := Ideal.height_le_card_of_mem_minimalPrimes_span_finset hminQ
  have hcard : rs.toFinset.card ≤ rs.length := List.toFinset_card_le rs
  calc Q.height ≤ ((rs.toFinset.card : ℕ) : ℕ∞) := hle
    _ ≤ ((rs.length : ℕ) : ℕ∞) := by exact_mod_cast hcard

/-- Avoidance from the list bound (L6 rung input): if every associated
prime of `S ⧸ ofList rs` has height `≤ rs.length < dim S`, the maximal ideal
lies in none of them. Same maximality argument as `second_rung_of_residuals`
(`maximalIdeal_height_eq_ringKrullDim`), generalized from `1` to `rs.length`. -/
theorem maximalIdeal_notLe_of_heightDropList [IsNoetherianRing S] [IsLocalRing S]
    {rs : List S} (hdrop : VarHeightDropResidualList rs)
    (hlt : (((rs.length : ℕ) : ℕ∞) : WithBot ℕ∞) < ringKrullDim S) :
    ∀ Q ∈ associatedPrimes S (S ⧸ Ideal.ofList rs),
      ¬ IsLocalRing.maximalIdeal S ≤ Q := by
  intro Q hQ hcon
  have hQprime : Q.IsPrime := (AssociatedPrimes.mem_iff.mp hQ).isPrime
  have heq : IsLocalRing.maximalIdeal S = Q :=
    (IsLocalRing.maximalIdeal.isMaximal S).eq_of_le hQprime.ne_top hcon
  have h1 := hdrop Q hQ
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, heq] at hlt
  have hle1 : ((Q.height : ℕ∞) : WithBot ℕ∞)
      ≤ (((rs.length : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    exact_mod_cast h1
  exact absurd (lt_of_lt_of_le hlt hle1) (lt_irrefl _)

/-- General-rung PrimeAvoidance selection (L6): the height bound at prefix
`rs` yields an element of the maximal ideal regular on `S ⧸ ofList rs`.
One consume of `PrimeAvoidance.exists_isSMulRegular_mem_of_forall_not_le_ass`
after the avoidance input above. -/
theorem nextRung_of_heightDropList [IsNoetherianRing S] [IsLocalRing S]
    {rs : List S} (hdrop : VarHeightDropResidualList rs)
    (hlt : (((rs.length : ℕ) : ℕ∞) : WithBot ℕ∞) < ringKrullDim S) :
    ∃ y' ∈ IsLocalRing.maximalIdeal S, IsSMulRegular (S ⧸ Ideal.ofList rs) y' := by
  have hle : ∀ Q ∈ associatedPrimes S (S ⧸ Ideal.ofList rs),
      ¬ IsLocalRing.maximalIdeal S ≤ Q :=
    maximalIdeal_notLe_of_heightDropList hdrop hlt
  obtain ⟨y', hyMax, hyReg⟩ :=
    PrimeAvoidance.exists_isSMulRegular_mem_of_forall_not_le_ass
      (IsLocalRing.maximalIdeal S) hle
  exact ⟨y', hyMax, hyReg⟩

/-- Append bridge (L6 rung assembly): weak regularity of `rs` plus
regularity of `y'` on the quotient ring `S ⧸ ofList rs` gives regularity of
`rs ++ [y']`. Proof: `IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal`
upgrades (all entries lie in the maximal ideal); the weak half is Mathlib
`isWeaklyRegular_append_iff` + `isWeaklyRegular_singleton_iff`, with the
`S`-scalar regularity transported across the `S`-linear identification
`S ⧸ ↑ofList rs ≃ S ⧸ ofList rs • ⊤` (`Submodule.quotEquivOfEq` over
`↑ofList rs = ofList rs • ⊤`, via `Submodule.span_smul_eq` +
`Submodule.set_smul_top_eq_span` — the same pattern as
`quotientSingletonResidual_of_mem_maximal`). No take/get manipulation: the
append characterization handles the indexing. -/
theorem isRegular_append_singleton_of_quotient_regular [IsLocalRing S]
    {rs : List S} {y' : S}
    (hmem : ∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal S)
    (hyMax : y' ∈ IsLocalRing.maximalIdeal S)
    (hweak : IsWeaklyRegular S rs)
    (hregQ : IsSMulRegular (S ⧸ Ideal.ofList rs) y') :
    IsRegular S (rs ++ [y']) := by
  have hsub : (Ideal.ofList rs : Submodule S S)
      = Ideal.ofList rs • (⊤ : Submodule S S) := by
    change (Ideal.span {r | r ∈ rs} : Submodule S S)
      = Ideal.span {r | r ∈ rs} • ⊤
    rw [Submodule.span_smul_eq, Submodule.set_smul_top_eq_span]
  have e : (S ⧸ Ideal.ofList rs) ≃ₗ[S]
      (S ⧸ (Ideal.ofList rs • (⊤ : Submodule S S))) :=
    Submodule.quotEquivOfEq _ _ hsub
  have hregQ' : IsSMulRegular (S ⧸ (Ideal.ofList rs • (⊤ : Submodule S S))) y' :=
    (e.isSMulRegular_congr y').mp hregQ
  have hmem' : ∀ r ∈ rs ++ [y'], r ∈ IsLocalRing.maximalIdeal S := by
    intro r hr
    rw [List.mem_append] at hr
    rcases hr with h | h
    · exact hmem r h
    · obtain rfl := List.mem_singleton.mp h
      exact hyMax
  refine IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal _ hmem' ?_
  rw [isWeaklyRegular_append_iff, isWeaklyRegular_singleton_iff]
  exact ⟨hweak, hregQ'⟩

/-- Per-rung feed (L6): a regular sequence `rs` of length `< d` in the
maximal ideal extends by one rung under the list-form bound at `rs` plus the
finite-dim equation. Selection (`nextRung_of_heightDropList`) + bridge
(`isRegular_append_singleton_of_quotient_regular`). -/
theorem nextRung_append_of_heightDropList [IsNoetherianRing S] [IsLocalRing S]
    {rs : List S} {d : ℕ}
    (hreg : IsRegular S rs) (hmem : ∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal S)
    (hdrop : VarHeightDropResidualList rs)
    (hdim : ringKrullDim S = ((d : ℕ) : WithBot ℕ∞))
    (hlt : rs.length < d) :
    ∃ y' ∈ IsLocalRing.maximalIdeal S, IsRegular S (rs ++ [y']) := by
  have hlt' : (((rs.length : ℕ) : ℕ∞) : WithBot ℕ∞) < ringKrullDim S := by
    rw [hdim]
    exact_mod_cast hlt
  obtain ⟨y', hyMax, hyReg⟩ := nextRung_of_heightDropList hdrop hlt'
  exact ⟨y', hyMax,
    isRegular_append_singleton_of_quotient_regular hmem hyMax
      hreg.toIsWeaklyRegular hyReg⟩

/-- HilbertFunctionCount bookkeeping (L6 telescope assembly): a per-rung
extension feed for all lengths `< d` yields a regular sequence of length `d`
in the maximal ideal. HilbertFunctionCount on the target prefix length; the base is
`IsRegular.nil`. This separates the rung content (residuals) from the
telescope. -/
theorem exists_regular_of_forall_nextRung [IsNoetherianRing S] [IsLocalRing S]
    {d : ℕ}
    (hnext : ∀ rs : List S, IsRegular S rs →
      (∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal S) → rs.length < d →
      ∃ y' ∈ IsLocalRing.maximalIdeal S, IsRegular S (rs ++ [y'])) :
    ∃ rs : List S, IsRegular S rs ∧ (∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal S)
      ∧ rs.length = d := by
  suffices h : ∀ k, k ≤ d → ∃ rs : List S, IsRegular S rs ∧
      (∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal S) ∧ rs.length = k from
    h d le_rfl
  intro k hk
  induction k with
  | zero => exact ⟨[], IsRegular.nil S S, by simp, rfl⟩
  | succ n ih =>
    obtain ⟨rs, hreg, hmem, hlen⟩ := ih (by omega)
    obtain ⟨y', hyMax, hreg'⟩ := hnext rs hreg hmem (by omega)
    refine ⟨rs ++ [y'], hreg', ?_, ?_⟩
    · intro r hr
      rw [List.mem_append] at hr
      rcases hr with h | h
      · exact hmem r h
      · obtain rfl := List.mem_singleton.mp h
        exact hyMax
    · rw [List.length_append, List.length_singleton, hlen]

/-- Nondegeneracy for the grade telescope: the maximal ideal satisfies
`I • ⊤ < ⊤`. Via Nakayama
(`Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator`) fed by
`IsLocalRing.maximalIdeal_le_jacobson`. -/
theorem maximalIdeal_smul_top_lt_top [IsLocalRing S] :
    IsLocalRing.maximalIdeal S • (⊤ : Submodule S S) < ⊤ :=
  lt_top_iff_ne_top.mpr (Ne.symm
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (IsLocalRing.maximalIdeal_le_jacobson _)))

/-- Grade equals dimension at a maximal regular sequence (L6 grade capstone):
`GradeDepthFragment.grade_le_ringKrullDim` gives `≤`; the sequence itself is
a `GradeSet` witness (`mem_gradeSet_of_isRegular` + `le_grade_of_mem_gradeSet`)
giving `≥` through the finite-dim equation. -/
theorem grade_eq_dim_of_maximal_regular [IsNoetherianRing S] [IsLocalRing S]
    {rs : List S} (hmem : ∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal S)
    (hreg : IsRegular S rs)
    -- Double cast `ℕ → ℕ∞ → WithBot ℕ∞` matches the telescope-side form
    -- (cf. the `hlt` hypotheses); bridge single-cast equations with
    -- `exact_mod_cast`.
    (hdim : ((((rs.length : ℕ)) : ℕ∞) : WithBot ℕ∞) = ringKrullDim S) :
    ((GradeDepthFragment.grade S S (IsLocalRing.maximalIdeal S) : ℕ∞) : WithBot ℕ∞)
      = ringKrullDim S := by
  have hle := GradeDepthFragment.grade_le_ringKrullDim (R := S)
    (I := IsLocalRing.maximalIdeal S)
  have hmem' := GradeDepthFragment.mem_gradeSet_of_isRegular (R := S) (M := S)
    (IsLocalRing.maximalIdeal S) rs rfl hmem hreg
  have hge0 := GradeDepthFragment.le_grade_of_mem_gradeSet (R := S) (M := S)
    (I := IsLocalRing.maximalIdeal S) hmem'
  have hge : (((rs.length : ℕ) : ℕ∞) : WithBot ℕ∞)
      ≤ ((GradeDepthFragment.grade S S (IsLocalRing.maximalIdeal S) : ℕ∞) :
        WithBot ℕ∞) := by
    exact_mod_cast hge0
  rw [hdim] at hge
  exact le_antisymm hle hge

/-- Iterated-drop telescope at a maximal regular sequence (L6): the
imported `GradeDepthFragment.grade_quotIter_add_eq_grade` equation applied to `rs` in
the maximal ideal (nondegeneracy from `maximalIdeal_smul_top_lt_top`). This is
the (i)×`k` vehicle: the iterated quotient carries exactly the residual grade. -/
theorem grade_telescope_of_maximal_regular [IsNoetherianRing S] [IsLocalRing S]
    {rs : List S} (hmem : ∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal S)
    (hreg : IsRegular S rs) :
    GradeDepthFragment.grade S (GradeDepthFragment.quotIter S rs) (IsLocalRing.maximalIdeal S)
      + ((rs.length : ℕ) : ℕ∞)
      = GradeDepthFragment.grade S S (IsLocalRing.maximalIdeal S) :=
  GradeDepthFragment.grade_quotIter_add_eq_grade (IsLocalRing.maximalIdeal S) rs hmem
    maximalIdeal_smul_top_lt_top hreg

/-! ## Rung closures (unconditional rungs 0–1)

`varTarget_of_uniformHeightDrop` takes the list-form height bound at every
maximal-ideal prefix. The length-0 and length-1 instances close
unconditionally here (domain-quotient core + UFD-colon replay, both generic
over the ambient ring — no `MvPolynomial` input, no transfer needed), so the
residual narrows to prefixes of length `≥ 2` (see
`varTarget_of_heightDrop_ge_two`). Length `≥ 2` is the genuine CM content
(`HeightDrop.lean` §4 R5 killer); see the §4 ledger addendum. -/

/-- A regular scalar on a nontrivial module is nonzero: `0` acts constantly,
against injectivity. -/
theorem smulRegular_ne_zero [Nontrivial S] {x : S} (h : IsSMulRegular S x) :
    x ≠ 0 := by
  rintro rfl
  obtain ⟨a, b, hab⟩ := exists_pair_ne S
  have h0 : (0 : S) • a = (0 : S) • b := by simp
  exact hab (h h0)

/-- Domain core of rung 0 (generic `k = 0` argument): in a domain, the only
associated prime of `S ⧸ ⊥` is `⊥` itself, which is minimal over `⊥`.
Proof mirrors `Unmixedness.mem_minimalPrimes_of_successive_zero` with the
`Fin 0` family setup erased (`J := ⊥` directly); it uses only domain +
associated-prime API. -/
theorem mem_minimalPrimes_bot_of_mem_associatedPrimes_bot [IsDomain S]
    (P : Ideal S)
    (hP : P ∈ associatedPrimes S (S ⧸ (⊥ : Ideal S))) :
    P ∈ (⊥ : Ideal S).minimalPrimes := by
  have _hPprime := (AssociatedPrimes.mem_iff.mp hP).isPrime
  have hmem : IsAssociatedPrime P (_ ⧸ (⊥ : Ideal S)) :=
    AssociatedPrimes.mem_iff.mp hP
  have hsub : (⊥ : Submodule S
      (_ ⧸ (⊥ : Ideal S))).IsAssociatedPrime P := hmem
  obtain ⟨hprime, hx0⟩ := hsub
  obtain ⟨x, hx⟩ := hx0
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  have haJ : a ∉ (⊥ : Ideal S) := by
    intro hmemJ
    have hx0 : Ideal.Quotient.mk (⊥ : Ideal S) a = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hmemJ
    have hcol : (⊥ : Submodule S
        (_ ⧸ (⊥ : Ideal S))).colon
        {Ideal.Quotient.mk ⊥ a} = ⊤ := by
      rw [hx0]
      exact Submodule.colon_singleton_zero
    have hPtop : P = ⊤ := by
      rw [hx, hcol]
      exact Ideal.radical_top _
    exact hprime.ne_top hPtop
  have ha0 : a ≠ 0 := fun h => haJ (Ideal.mem_bot.mpr h)
  have hPbot : P = ⊥ := by
    ext r
    rw [hx, Ideal.mem_radical_iff, Ideal.mem_bot]
    constructor
    · rintro ⟨n, hn⟩
      have hsmul : r ^ n • Ideal.Quotient.mk (⊥ : Ideal S) a =
          Ideal.Quotient.mk ⊥ (r ^ n * a) := by
        rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul]
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot, hsmul,
        Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_bot] at hn
      have key : ∀ t : ℕ, r ^ t * a = 0 → r = 0 := by
        intro t
        induction t with
        | zero => intro h; exact absurd (by simpa using h) ha0
        | succ t ih =>
          intro h
          rw [pow_succ'] at h
          rw [mul_assoc] at h
          rcases mul_eq_zero.mp h with h1 | h2
          · exact h1
          · exact ih h2
      have hr0 : r = 0 := key n hn
      exact Ideal.mem_bot.mpr hr0
    · intro hr
      have hr0 : r = 0 := Ideal.mem_bot.mp hr
      refine ⟨1, ?_⟩
      rw [Submodule.mem_colon_singleton, hr0, pow_one, zero_smul]
      exact Submodule.zero_mem _
  rw [hPbot]
  exact ⟨⟨Ideal.isPrime_bot, bot_le⟩, fun Q _ _ => bot_le⟩

/-- Rung-0 minimality over the empty list: `ofList [] = ⊥`, so the domain
core applies. -/
theorem mem_minimalPrimes_of_ofList_nil [IsDomain S]
    (Q : Ideal S)
    (hQ : Q ∈ associatedPrimes S (S ⧸ Ideal.ofList ([] : List S))) :
    Q ∈ (Ideal.ofList ([] : List S)).minimalPrimes := by
  rw [Ideal.ofList_nil] at hQ ⊢
  exact mem_minimalPrimes_bot_of_mem_associatedPrimes_bot Q hQ

/-- Rung 0, unconditional: the list-form height bound at the empty prefix.
Minimality (above) through the Krull direction. -/
theorem varHeightDropResidualList_nil [IsDomain S] [IsNoetherianRing S] :
    VarHeightDropResidualList ([] : List S) :=
  heightDropList_of_forall_mem_minimalPrimes
    (fun Q hQ => mem_minimalPrimes_of_ofList_nil Q hQ)

/-- Length-one minimality in any UFD (generic `k = 1` argument): for nonzero
`x` in a UFD domain, every associated prime of `S ⧸ (x)` is minimal over
`(x)`. Proof mirrors
`Unmixedness.mem_minimalPrimes_of_successive_singleton` with the `Fin 1`
family setup erased (generator `f := x`, nonvanishing `hx` taken as
hypothesis); the annihilator-principal + prime-factor argument is fully
generic over the UFD. At `S = Localization.AtPrime P` the UFD instance is
free (`instUniqueFactorizationMonoidLocalization`), so this closes
`VarUnmixedOneResidual` unconditionally — superseding the §3 transfer
(`hpull`/`hpush`) for the L5 height facet. -/
theorem mem_minimalPrimes_of_ufd_span_singleton [IsDomain S]
    [UniqueFactorizationMonoid S] {x : S} (hx : x ≠ 0)
    (P : Ideal S)
    (hP : P ∈ associatedPrimes S (S ⧸ Ideal.span {x})) :
    P ∈ (Ideal.span {x}).minimalPrimes := by
  set f : S := x with hf
  have hf_ne : f ≠ 0 := hx
  have _hPprime := (AssociatedPrimes.mem_iff.mp hP).isPrime
  have hmem : IsAssociatedPrime P (_ ⧸ Ideal.span {f}) :=
    AssociatedPrimes.mem_iff.mp hP
  have hsub : (⊥ : Submodule _ (_ ⧸ Ideal.span {f})).IsAssociatedPrime P := hmem
  obtain ⟨hprime, hx0⟩ := hsub
  obtain ⟨x, hx⟩ := hx0
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  have : GCDMonoid S := UniqueFactorizationMonoid.toGCDMonoid _
  obtain ⟨f₁, hf₁⟩ := gcd_dvd_left f a
  obtain ⟨a₁, ha₁⟩ := gcd_dvd_right f a
  set g : S := GCDMonoid.gcd f a with hg
  have hg0 : g ≠ 0 := by
    intro hcon
    rw [hcon, zero_mul] at hf₁
    exact hf_ne hf₁
  have hrel : IsRelPrime f₁ a₁ := by
    intro d hd1 hda1
    have hgdvd_f : g * d ∣ f := by
      rw [hf₁]
      exact mul_dvd_mul_left g hd1
    have hgdvd_a : g * d ∣ a := by
      rw [ha₁]
      exact mul_dvd_mul_left g hda1
    have hgdvd_g : g * d ∣ g := by
      rw [hg] at hgdvd_f hgdvd_a ⊢
      exact dvd_gcd hgdvd_f hgdvd_a
    obtain ⟨c, hc⟩ := hgdvd_g
    have hdc : d * c = 1 := by
      apply mul_left_cancel₀ hg0
      calc g * (d * c) = (g * d) * c := by ring
        _ = g := hc.symm
        _ = g * 1 := by ring
    exact isUnit_of_dvd_one ⟨c, hdc.symm⟩
  have hcolon : (⊥ : Submodule _ (_ ⧸ Ideal.span {f})).colon
      {Ideal.Quotient.mk (Ideal.span {f}) a} = Ideal.span {f₁} := by
    have hsmul : ∀ c : S, c • Ideal.Quotient.mk (Ideal.span {f}) a =
        Ideal.Quotient.mk (Ideal.span {f}) (c * a) := by
      intro c
      have e := Algebra.smul_def c (Ideal.Quotient.mk (Ideal.span {f}) a)
      rw [Ideal.Quotient.algebraMap_eq] at e
      rw [← map_mul] at e
      exact e
    ext r
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, hsmul,
      Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton, Ideal.mem_span_singleton]
    constructor
    · intro hdiv
      obtain ⟨c, hc⟩ := hdiv
      have hcan : r * a₁ = f₁ * c := by
        apply mul_left_cancel₀ hg0
        calc g * (r * a₁) = r * (g * a₁) := by ring
          _ = r * a := by rw [← ha₁]
          _ = f * c := hc
          _ = (g * f₁) * c := by rw [hf₁]
          _ = g * (f₁ * c) := by ring
      have hdiv2 : f₁ ∣ r * a₁ := ⟨c, hcan⟩
      obtain ⟨r', a₁', hr'r, ha₁'a, hfa⟩ := exists_dvd_and_dvd_of_dvd_mul hdiv2
      have ha₁'f₁ : a₁' ∣ f₁ := by
        rw [hfa]
        exact dvd_mul_left a₁' r'
      have hunit : IsUnit a₁' := hrel ha₁'f₁ ha₁'a
      obtain ⟨s, hs⟩ := hr'r
      have hfr : f₁ ∣ r := by
        rw [hfa, hs]
        exact mul_dvd_mul_left r' ((isUnit_iff_forall_dvd.mp hunit) s)
      exact hfr
    · intro hdiv
      obtain ⟨c, hc⟩ := hdiv
      exact ⟨c * a₁, by rw [hc, ha₁, hf₁]; ring⟩
  have hf₁ne : f₁ ≠ 0 := by
    intro hcon
    rw [hcon, mul_zero] at hf₁
    exact hf_ne hf₁
  have hJP : Ideal.span {f} ≤ P :=
    LocalUnmixed.assPrime_contains_span _ _ hP
  refine ⟨⟨hprime, hJP⟩, fun Q hQ hQP => ?_⟩
  obtain ⟨hQprime, hQJ⟩ := hQ
  have hfQ : f ∈ Q := hQJ (Ideal.mem_span_singleton_self f)
  obtain ⟨Fs, hFsprime, hFsprod⟩ :=
    UniqueFactorizationMonoid.exists_prime_factors f hf_ne
  have hprodQ : Fs.prod ∈ Q := by
    obtain ⟨u, hu⟩ := hFsprod
    have hmemU : Fs.prod * (↑u : S) ∈ Q := by
      rw [hu]
      exact hfQ
    rw [mul_comm] at hmemU
    exact (Ideal.unit_mul_mem_iff_mem _ (Units.isUnit u)).mp hmemU
  have key : ∀ T : Multiset S, T.prod ∈ Q → ∃ π ∈ T, π ∈ Q := by
    intro T
    induction T using Multiset.induction with
    | empty =>
      intro h
      simp only [Multiset.prod_zero] at h
      have hQtop : Q = ⊤ := by
        have h1 : Ideal.span {(1 : S)} ≤ Q :=
          Ideal.span_le.mpr (Set.singleton_subset_iff.mpr h)
        rw [Ideal.span_singleton_one] at h1
        exact top_le_iff.mp h1
      exact (hQprime.ne_top hQtop).elim
    | cons b U ih =>
      intro h
      rw [Multiset.prod_cons] at h
      rcases hQprime.mem_or_mem h with hb | hU
      · exact ⟨b, Multiset.mem_cons_self _ _, hb⟩
      · obtain ⟨π, hπ, hπQ⟩ := ih hU
        exact ⟨π, Multiset.mem_cons_of_mem hπ, hπQ⟩
  obtain ⟨π₀, hπ₀Fs, hπ₀Q⟩ := key Fs hprodQ
  have hπ₀prime : Prime π₀ := hFsprime π₀ hπ₀Fs
  have hπ₀dvd : π₀ ∣ f :=
    dvd_trans (Multiset.dvd_prod hπ₀Fs) hFsprod.dvd_dvd.1
  have hπ₀ne : π₀ ≠ 0 := by
    intro hcon
    rw [hcon] at hπ₀dvd
    exact hf_ne (zero_dvd_iff.mp hπ₀dvd)
  have hπ₀P : π₀ ∈ P := hQP hπ₀Q
  rw [hx, hcolon] at hπ₀P
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hπ₀P
  rw [Ideal.mem_span_singleton] at hn
  obtain ⟨T, hTprime, hTprod⟩ :=
    UniqueFactorizationMonoid.exists_prime_factors f₁ hf₁ne
  have hTprime_all : ∀ τ ∈ T, τ ~ᵤ π₀ := by
    intro τ hτ
    have hτdvd : τ ∣ π₀ ^ n :=
      dvd_trans (dvd_trans (Multiset.dvd_prod hτ) hTprod.dvd_dvd.1) hn
    have hτπ : τ ∣ π₀ := (hTprime τ hτ).dvd_of_dvd_pow hτdvd
    have hτirr : Irreducible τ := (hTprime τ hτ).irreducible
    have hπirr : Irreducible π₀ := hπ₀prime.irreducible
    have hback : π₀ ∣ τ := hτirr.dvd_symm hπirr hτπ
    exact associated_of_dvd_dvd hτπ hback
  have hpassoc : ∀ U : Multiset S, (∀ τ ∈ U, τ ~ᵤ π₀) →
      U.prod ~ᵤ π₀ ^ U.card := by
    intro U
    induction U using Multiset.induction with
    | empty =>
      intro _
      rw [Multiset.prod_zero, Multiset.card_zero, pow_zero]
    | cons b U ih =>
      intro hall
      rw [Multiset.prod_cons, Multiset.card_cons, pow_succ']
      exact (hall b (Multiset.mem_cons_self _ _)).mul_mul
        (ih (fun τ hτ => hall τ (Multiset.mem_cons_of_mem hτ)))
  have hfall : f₁ ~ᵤ π₀ ^ T.card := hTprod.symm.trans (hpassoc T hTprime_all)
  have hspan : Ideal.span {f₁} = Ideal.span {π₀ ^ T.card} :=
    Ideal.span_singleton_eq_span_singleton.mpr hfall
  have htpos : 0 < T.card := by
    rcases Nat.eq_zero_or_pos T.card with h0 | hpos
    · have hTe : T = 0 := Multiset.card_eq_zero.mp h0
      rw [hTe] at hTprod
      simp only [Multiset.prod_zero] at hTprod
      have hunitf : IsUnit f₁ := isUnit_of_dvd_one hTprod.dvd'
      have htop : Ideal.span {f₁} = ⊤ := Ideal.span_singleton_eq_top.mpr hunitf
      have hPtop : P = ⊤ := by
        rw [hx, hcolon, htop]
        exact Ideal.radical_top _
      exact absurd hPtop hprime.ne_top
    · exact hpos
  have hle : Ideal.span {π₀ ^ T.card} ≤ Ideal.span {π₀} := by
    obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : T.card ≠ 0)
    rw [Ideal.span_le]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    rw [hs, Nat.succ_eq_add_one]
    exact Ideal.mem_span_singleton'.mpr ⟨π₀ ^ s, (pow_succ π₀ s).symm⟩
  have hπ₀span_prime : (Ideal.span {π₀}).IsPrime :=
    (Ideal.span_singleton_prime hπ₀ne).mpr hπ₀prime
  have hPeq : P = Ideal.span {π₀} := by
    rw [hx, hcolon, hspan]
    apply le_antisymm
    · calc (Ideal.span {π₀ ^ T.card}).radical
          ≤ (Ideal.span {π₀}).radical := Ideal.radical_mono hle
        _ = Ideal.span {π₀} := hπ₀span_prime.radical
    · rw [Ideal.span_le]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      rw [SetLike.mem_coe, Ideal.mem_radical_iff]
      exact ⟨T.card, Ideal.mem_span_singleton_self _⟩
  have hPQ : P ≤ Q := by
    rw [hPeq]
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hπ₀Q)
  exact hPQ

/-- L5 residual, unconditional for nonzero `x` in a UFD: every associated
prime of `S ⧸ span {x}` is minimal over `span {x}`. This discharges
`VarUnmixedOneResidual` directly — the §3 globalization-to-localization
transfer (`hpull`/`hpush`) is no longer needed for the L5 height facet. -/
theorem varUnmixedOneResidual_of_ne_zero [IsDomain S]
    [UniqueFactorizationMonoid S] {x : S} (hx : x ≠ 0) :
    VarUnmixedOneResidual x :=
  fun Q hQ => mem_minimalPrimes_of_ufd_span_singleton hx Q hQ

/-- Rung 1, unconditional in a UFD: the list-form height bound at any
singleton prefix. For `x = 0` the quotient is `S ⧸ ⊥` (domain core); for
`x ≠ 0` it is the UFD argument — in both cases minimality through the
Krull direction. -/
theorem varHeightDropResidualList_singleton [IsDomain S]
    [UniqueFactorizationMonoid S] [IsNoetherianRing S] (x : S) :
    VarHeightDropResidualList [x] := by
  apply heightDropList_of_forall_mem_minimalPrimes
  intro Q hQ
  by_cases hx0 : x = 0
  · subst hx0
    have h0 : Ideal.span ({0} : Set S) = ⊥ :=
      Ideal.span_singleton_eq_bot.mpr rfl
    rw [Ideal.ofList_singleton, h0] at hQ ⊢
    exact mem_minimalPrimes_bot_of_mem_associatedPrimes_bot Q hQ
  · rw [Ideal.ofList_singleton] at hQ ⊢
    exact mem_minimalPrimes_of_ufd_span_singleton hx0 Q hQ

section AtPrimeTarget

variable (m : ℕ) (K : Type*) [Field K] (P : Ideal (MvPolynomial (Fin m) K))
  [P.IsPrime]

/-- The induction target at `P`: a regular sequence in `R_P` whose length is
`ringKrullDim R_P`. -/
def VarTarget : Prop :=
  ∃ rs : List (Localization.AtPrime P),
    IsRegular (Localization.AtPrime P) rs ∧
    (rs.length : WithBot ℕ∞) = ringKrullDim (Localization.AtPrime P)

/-- First rung at `P`: positive-dimensional `R_P` carries a length-1 regular
sequence in its maximal ideal. The domain instance is supplied by hand from
`IsLocalization.isDomain_of_local_atPrime` (free in principle; see the
`CohenMacaulayFragment` ledger); local + nontrivial structure is automatic for `AtPrime`. -/
theorem first_rung_atPrime (hdim : ringKrullDim (Localization.AtPrime P) ≠ 0) :
    ∃ x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime P),
      IsRegular (Localization.AtPrime P) [x] :=
  @singleton_regular_of_dim_ne_zero _ _ (IsLocalization.isDomain_of_local_atPrime
    ‹P.IsPrime›) inferInstance hdim

/-- Second rung at `P` (conditional on `VarUnmixedOneResidual` only): if
`1 < ringKrullDim R_P`, the maximal ideal carries a second-rung residual over
any of its members. Needs no `VarHeightDropResidual` — the `k = 1` height
bound comes from `height_le_one_of_unmixed` (Hauptidealsatz); the L6 residual
stays the address for `k ≥ 2`. -/
theorem second_rung_atPrime (hdim : 1 < ringKrullDim (Localization.AtPrime P))
    {x : Localization.AtPrime P} (hmax : x ∈ IsLocalRing.maximalIdeal _)
    (hunmixed : VarUnmixedOneResidual x) :
    ∃ y' ∈ IsLocalRing.maximalIdeal (Localization.AtPrime P),
      QuotientSingletonResidual x y' :=
  second_rung_of_residuals hmax hunmixed hdim

/-- Fin-form feeds list-form (L6 wiring): `VarHeightDropResidual` at
`q` gives `VarHeightDropResidualList` at `List.ofFn q` (whose span is
`Set.range q` and whose length is `k`). -/
theorem varHeightDropResidualList_of_fin {k : ℕ}
    {q : Fin k → Localization.AtPrime P}
    (hdrop : VarHeightDropResidual m K P q) :
    VarHeightDropResidualList (List.ofFn q) := by
  intro Q hQ
  have hspan : Ideal.span (Set.range q) = Ideal.ofList (List.ofFn q) := by
    change Ideal.span (Set.range q) = Ideal.span {r | r ∈ List.ofFn q}
    congr 1
    ext x
    simp [List.mem_ofFn]
  have hmem : Q ∈ associatedPrimes _ (_ ⧸ Ideal.span (Set.range q)) := by
    rw [hspan]
    exact hQ
  have := (AssociatedPrimes.mem_iff.mp hQ).isPrime
  have hle := hdrop Q hmem
  rw [List.length_ofFn]
  exact hle

/-- Maximal regular sequence at `P` (L6 capstone, conditional): the
uniform list-form bound at every maximal-ideal prefix of length `< d`, plus
the finite-dim equation, yields `VarTarget` — a regular sequence of length
`dim R_P`. HilbertFunctionCount (`exists_regular_of_forall_nextRung`) fed per-rung by
selection + bridge (`nextRung_append_of_heightDropList`). -/
theorem varTarget_of_uniformHeightDrop {d : ℕ}
    (hdim : ringKrullDim (Localization.AtPrime P) = ((d : ℕ) : WithBot ℕ∞))
    (hdrop : ∀ rs : List (Localization.AtPrime P),
      (∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal _) → rs.length < d →
      VarHeightDropResidualList rs) :
    VarTarget m K P := by
  obtain ⟨rs, hreg, _, hlen⟩ :=
    exists_regular_of_forall_nextRung (S := Localization.AtPrime P) (d := d)
      (fun rs hreg hmem hlt =>
        nextRung_append_of_heightDropList hreg hmem (hdrop rs hmem hlt) hdim hlt)
  exact ⟨rs, hreg, by rw [hlen, hdim]⟩

/-- Maximal regular sequence at `P`, narrowed residual: the
uniform list-form bound is needed only at prefixes of length `≥ 2`.
Lengths 0 (`varHeightDropResidualList_nil`: `R_P` is a domain) and 1
(`varHeightDropResidualList_singleton`: `R_P` is a UFD — free instance
`instUniqueFactorizationMonoidLocalization`) close unconditionally, so
`varTarget_of_uniformHeightDrop` applies with the low rungs discharged by
list-shape case split. All instances (`IsDomain`, `UniqueFactorizationMonoid`,
`IsNoetherianRing`, `IsLocalRing`) synthesize automatically at `AtPrime P`. -/
theorem varTarget_of_heightDrop_ge_two {d : ℕ}
    (hdim : ringKrullDim (Localization.AtPrime P) = ((d : ℕ) : WithBot ℕ∞))
    (hdrop : ∀ rs : List (Localization.AtPrime P),
      (∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal _) → 2 ≤ rs.length →
      rs.length < d → VarHeightDropResidualList rs) :
    VarTarget m K P := by
  refine varTarget_of_uniformHeightDrop m K P hdim
    (fun rs hmem hlt => ?_)
  cases rs with
  | nil => exact varHeightDropResidualList_nil
  | cons a tl =>
    cases tl with
    | nil => exact varHeightDropResidualList_singleton a
    | cons b tl =>
      exact hdrop _ hmem (by rw [List.length_cons, List.length_cons]; omega) hlt

/-- L5 at `P`, unconditional: positive-dimensional `R_P` carries a
length-2 regular sequence once `1 < dim`. The first rung (`first_rung_atPrime`)
is nonzero by `smulRegular_ne_zero`, hence unmixed by
`varUnmixedOneResidual_of_ne_zero` (UFD argument — no transfer); the second
rung and cons assembly are the L4/L5 machine above. -/
theorem length_two_atPrime (hdim : 1 < ringKrullDim (Localization.AtPrime P)) :
    ∃ (x y' : Localization.AtPrime P), IsRegular (Localization.AtPrime P) [x, y'] := by
  have hdim0 : ringKrullDim (Localization.AtPrime P) ≠ 0 :=
    ne_of_gt (lt_trans zero_lt_one hdim)
  obtain ⟨x, hxmax, hxreg⟩ := first_rung_atPrime m K P hdim0
  have hhead : IsSMulRegular (Localization.AtPrime P) x :=
    (isWeaklyRegular_singleton_iff _ _).mp hxreg.toIsWeaklyRegular
  have hx0 : x ≠ 0 := smulRegular_ne_zero hhead
  have hunmixed : VarUnmixedOneResidual x := varUnmixedOneResidual_of_ne_zero hx0
  obtain ⟨y', _, hres⟩ := second_rung_atPrime m K P hdim hxmax hunmixed
  exact ⟨x, y', length_two_of_residual hhead hres⟩

end AtPrimeTarget

end VariableInductionCM
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
