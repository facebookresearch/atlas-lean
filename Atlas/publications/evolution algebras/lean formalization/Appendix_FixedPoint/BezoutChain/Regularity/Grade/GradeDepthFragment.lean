/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.RegularityBridge
import Appendix_FixedPoint.BezoutChain.Regularity.Unmixed.HeightDrop
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.Depth.Rees
import Mathlib.Data.ENat.Basic
import Mathlib.Order.WithBot
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
/-!
# Grade and depth fragment for the unmixedness theorem

For `R = MvPolynomial (Fin m) K` (`[Field K]`), `q : Fin k → R` carrying
successive SMul-regularity data (`RegularityBridge.SuccessiveSMulRegular`), and
`J = Ideal.span (Set.range q)`, the load-bearing grade content is:

* (i) grade (depth) drops by exactly 1 across a regular element, hence by
  exactly `k` across a length-`k` regular sequence
  (`grade_quotIter_add_eq_grade`, proved);
* (ii) associated primes have grade zero;
* (iii) regular-local equality depth = dim at the relevant primes
  (the deep core — careful scoping in the ledger below).

## SPEC (the most valuable result; stands even if proofs stall)

Definitions (this file, `namespace
EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradeDepthFragment`):

* `GradeSet R M I : Set ℕ` — lengths of `M`-regular sequences
  (`RingTheory.Sequence.IsRegular`) with all entries in `I`.
* `grade R M I : ℕ∞` — regular-sequence-length supremum
  (`sSup` of the cast image of `GradeSet`). No general homological algebra:
  no `Ext`, no Koszul complex, no projective dimension anywhere in the
  definition — only `IsRegular` lists.
* `GradeDropOne R M I x : Prop` — supremum-level drop-by-one across `x`,
  the formal address of (i) at supremum level (residual: maximality of grade
  needs the Rees bridge; see ledger).
* `quotIter M' rs : Type u` — iterated `QuotSMulTop` quotient along a list
  (same universe `u`), with `quotIterAddCommGroup` / `quotIterModule`
  instances: the type-level telescope the iterated drop chain is stated over.
* `GradeDropChain m K q hsucc : Prop` — the iterated drop along a successive
  family: every prime containing `span (Set.range q)` carries local grade at
  least `k` (closed as `gradeDropChain_of_successive`; the `hJP` hypothesis is
  essential — see the sharpness note at `le_grade_atPrime_of_span_of_successive`).
* `DepthEqDimAt m K P : Prop` — the formal address of (iii): grade of the
  localization at `P` w.r.t. its maximal ideal equals `ringKrullDim`.
* `GradeUnmixedBridge m K q hsucc J hJ : Prop` — the exact bridge implication
  `GradeDropChain → (∀ Ass, DepthEqDimAt) → HeightDropResidualAt`.

Theorem statements:

* `isRegular_tail_of_cons` / `isRegular_cons_of_head_tail` — (i) proved at
  sequence level: both directions of `isRegular_cons_iff`.
* `not_isSMulRegular_of_mem_associatedPrimes` — (ii) core, proved: no element
  of an associated prime is SMul-regular (radical-of-colon argument; needs no
  Noetherian hypothesis).
* `grade_eq_zero_of_mem_associatedPrimes` — (ii) proved at grade level:
  `grade R M P = 0` for `P ∈ associatedPrimes R M`.
* `no_smulRegular_of_ass_localized_maximal` — (ii) proved in local form via
  `mem_associatedPrimes_atPrime_of_mem_associatedPrimes`
  (`Ideal/AssociatedPrime/Localization.lean`): nothing in the maximal ideal of
  `R_P` is regular on the localized module.
* `mem_gradeSet_of_isRegular` / `le_grade_of_mem_gradeSet` — proved tooling
  (membership constructor + `le_sSup` lower bound).
* `grade_le_supportDim` / `grade_le_ringKrullDim` — deep-core step (1), proved:
  grade is bounded by support dimension / Krull dimension (via the iterated
  dim-drop `supportDim_add_length_eq_supportDim_of_isRegular`).
* `sSup_add_one_le_of_forall_add_one_le` — order-theory shift helper (proved).
* `grade_quotSMulTop_add_one_le_grade` — (i) at supremum level, `≥` half,
  proved (needs `x • ⊤ < ⊤`).
* `withBot_coe_sSup` — coercion-supremum bridge (proved; `S.Nonempty` is sharp:
  for `S = ∅`, LHS is `↑⊥ ≠ ⊥ = RHS`).
* `exists_isRegular_quotSMulTop_of_isRegular_succ` — Rees-bridge crux (proved):
  a length-`m+1` regular sequence yields a length-`m` one on the quotient, via
  `Ext`-vanishing + LES shift + `Ext`-to-sequence (public `Depth/Rees.lean`
  lemmas only; same-universe `R' M'`, see universe note in G-(i)).
* `grade_le_quotSMulTop_add_one` — (i) `≤` half (proved).
* `grade_quotSMulTop_add_one_eq_grade` — (i) full supremum equation (proved).
* `grade_quotIter_add_le_grade` / `grade_le_quotIter_add` — iterated (i)×`k`
  le+ge pair (proved): `grade (quotIter M' rs) + length = grade`
  halves by induction on `rs` via the single-step trio + `isRegular_cons_iff`
  surgery (`smulTop_lt_top_quotSMulTop` carries `I • ⊤ < ⊤` down each rung;
  `Module.Finite` descends via `of_surjective` + `mkQ_surjective`).
* `grade_quotIter_add_eq_grade` — iterated full equation (proved this
  session): assembly of the pair; the telescope vehicle for VariableInductionCM L6 /
  maximal-regular-sequence arguments.
* `grade_two_step_eq` — length-2 application (proved): grade of
  the nested quotient `QuotSMulTop y (QuotSMulTop x M')` plus `2` equals the
  grade; the u2-shape consumer for `CohenMacaulayFragment` / L6 telescope input.
* `unmixed_of_grade_of_depthEq` — assembly, proved conditionally: the bridge
  plus its two inputs imply minimality over `J`, via
  `HeightDrop.minimal_of_height_le` (which itself routes through
  `mem_minimalPrimes_of_localized_quotient_dim_zero`).

## Mathlib-gap analysis (Mathlib v4.34.0; all `grep` run in
`.lake/packages/mathlib`, `lean-toolchain` pins `v4.34.0`)

exists (module + name):

* `RingTheory.Sequence.IsWeaklyRegular` / `IsRegular` for `List R` on `M` —
  `Mathlib/RingTheory/Regular/RegularSequence.lean,146`.
* `isWeaklyRegular_cons_iff` (:228) and `isRegular_cons_iff` (:247):
  `IsRegular M (r :: rs) ↔ IsSMulRegular M r ∧ IsRegular (QuotSMulTop r M) rs`
  (both `@[simp]`). This is the entire (i) proof.
* `IsSMulRegular.pow` — `Mathlib/Algebra/Regular/SMul.lean`:
  `IsSMulRegular M a → IsSMulRegular M (a ^ n)`. This is the (ii) engine
  (power of a regular element stays regular).
* `Submodule.IsAssociatedPrime.eq_radical_colon` —
  `Mathlib/RingTheory/Ideal/AssociatedPrime/Basic.lean`:
  `∃ x, I = (colon N {x}).radical`. The (ii) witness.
* `Ideal.mem_radical_iff` (`Ideal/Operations.lean`) +
  `Submodule.mem_colon_singleton` (`Ideal/Colon.lean`) +
  `Submodule.colon_singleton_zero` (`Ideal/Colon.lean`) +
  `Ideal.radical_top` (`Ideal/Operations.lean`). The (ii) bookkeeping.
* `mem_associatedPrimes_atPrime_of_mem_associatedPrimes` —
  `Mathlib/RingTheory/Ideal/AssociatedPrime/Localization.lean`: the maximal
  ideal of `R_P` is associated to the localized module. The (ii)-local bridge.
* `ModuleCat.exists_isRegular_tfae` (Rees theorem) —
  `Mathlib/RingTheory/Depth/Rees.lean`: regular-sequence existence iff
  `Ext` vanishing. Existence direction only; no grade maximality, no depth.
* `supportDim_add_length_eq_supportDim_of_isRegular` /
  `ringKrullDim_add_length_eq_ringKrullDim_of_isRegular` —
  `Mathlib/RingTheory/KrullDimension/Regular.lean,195`: dimension counts
  along full regular sequences (already consumed in-tree via
  `AssHeightBound.height_eq_add_of_span`).
* `ModuleCat.projectiveDimension_quotSMulTop_eq_succ_of_isSMulRegular` —
  `Mathlib/RingTheory/Regular/ProjectiveDimension.lean`: projective
  dimension shifts by one across a regular element (no Auslander–Buchsbaum
  around it).

absent (with evidence):

* No grade/depth definition: `grep -rln "def grade" Mathlib/RingTheory/`
  is empty (only `GradedAlgebra` false positives); `Depth/` holds exactly one
  file (`Rees.lean`, only `ModuleCat.exists_isRegular_tfae`); the deprecated
  stub `Regular/Depth.lean` is 15 lines with no content.
* No Koszul API in commutative algebra: `grep -rn "Koszul" Mathlib/` has zero
  commutative-algebra hits (only the Levi-Civita formula, a limit remark in
  `Algebra/Homology/LocalCohomology.lean`, and the todo at
  `RegularSequence.lean`: "todo: Koszul regular sequences, `H_1`-regular
  sequences, quasi-regular sequences, depth").
* No Auslander–Buchsbaum shape: `grep -rni "auslander\|buchsbaum"
  Mathlib/RingTheory/` is empty (the only `ProjectiveDimension` consumer is
  the one-step shift above).
* No Cohen–Macaulay / unmixed API (see SPEC in `Regularity/Unmixed/CohenMacaulayFragment.lean`).

## roadblock ledger (first-class result)

* G-(i) (supremum-level drop): fully proved. Sequence level was already proved
  (both directions one-line applies of `isRegular_cons_iff`). At supremum level:
  `≥` half as `grade_quotSMulTop_add_one_le_grade` (cons direction + the
  `sSup`-shift helper; needs `x • ⊤ < ⊤`); `≤` half as
  `grade_le_quotSMulTop_add_one` via the Rees-bridge crux
  `exists_isRegular_quotSMulTop_of_isRegular_succ`
  (`subsingleton_ext_of_exists_isRegular` + LES shift via
  `Ext.covariant_sequence_exact₃'` + `exists_isRegular_of_exists_subsingleton_ext`);
  full equation as `grade_quotSMulTop_add_one_eq_grade` under `I • ⊤ < ⊤`
  (which implies `x • ⊤ < ⊤`). Sharpness: `GradeDropOne` as stated (no
  properness) is false — field + unit gives both grades `0` with `0 + 1 ≠ 0` —
  so the `I • ⊤ < ⊤` hypothesis is essential. Universe note: the crux/`≤`/equation
  use fresh same-universe `R' M' : Type u`, leaving the file's two-universe
  `R M` contracts byte-identical — the Rees bridge needs both modules in one
  `ModuleCat.{u}` (`Ext` needs a single category) and `Small` cannot bridge
  independent universes; all in-project applications are single-universe, so
  nothing is lost. No residual.
  iterated chain (proved): `quotIter` (iterated `QuotSMulTop`
  fold along a list, same universe `u`, with `AddCommGroup` / `Module`
  instances by list recursion) with the le+ge pair
  `grade_quotIter_add_le_grade` / `grade_le_quotIter_add` assembling to
  `grade_quotIter_add_eq_grade` (`grade iter + length = grade`, induction on
  the list via the single-step trio + `isRegular_cons_iff` surgery;
  `I • ⊤ < ⊤` descends each rung via `smulTop_lt_top_quotSMulTop`,
  `Module.Finite` via `Module.Finite.of_surjective` +
  `Submodule.mkQ_surjective`). Immediate application `grade_two_step_eq`
  (length-2 nested quotient drops by exactly 2 — u2-shape consumer for
  `CohenMacaulayFragment` / L6 telescope input). No residual.
* G-(ii): proved fully (core + grade-zero equation + localized maximal-ideal
  form). No residual.
* G-(iii) (deep core): re-assessed after (1), (2), G-(i) all proved — not
  begun here (out of scope for this file). The wanted statement `DepthEqDimAt`
  (grade of `R_P` =
  `dim R_P`) for localizations of polynomial rings now decomposes as follows.
  proved inputs: (1) grade ≤ dim (`grade_le_supportDim` /
  `grade_le_ringKrullDim`, WithBot-valued); the Rees-bridge assembly pattern
  (forward + LES shift + backward, in the G-(i) crux) — the "vanishing ⟹
  sequence" step is proven reusable, so no Koszul complex is needed to exhibit
  the maximal sequence. Exact remainder for `P` with `d = dim R_P`:
  (a) regular-local API for `R_P`: `R_P` is regular local — free.
  Instance chain, all `inferInstance`-checked for
  `P : Ideal (MvPolynomial (Fin m) K)` prime with `[Field K]`:
  `IsRegularRing K` via `instance (priority:= low) [IsDedekindDomain R]:
  IsRegularRing R` (`Mathlib/RingTheory/RegularLocalRing/Defs.lean`,
  fields are Dedekind); `MvPolynomial.isRegularRing_of_isRegularRing`
  (`Mathlib/RingTheory/RegularLocalRing/Polynomial.lean`, needs
  `[Finite ι]` — `Fin m` qualifies);
  `IsRegularRing.isRegularLocalRing_localization`
  (`Mathlib/RingTheory/RegularLocalRing/Defs.lean`,
  `attribute [instance low]`). Hence
  `IsRegularLocalRing (Localization.AtPrime P)` is automatic — zero new code
  needed. (Dimension-`d` bookkeeping and the absent CM class are unchanged
  and need no new work for the input itself.)
  (b) the crux: `Ext^i_{R_P}(k_P, R_P) = 0` for `i < d` (`k_P` = residue field)
  — needs the Koszul complex of a regular system of parameters + self-duality,
  or Auslander–Buchsbaum (finite projective dimension); all absent from
  Mathlib commutative algebra (see gap analysis: no Koszul API, no AB, and
  regular ⟹ finite global dimension itself absent);
  (c) one application of `exists_isRegular_of_exists_subsingleton_ext` to (b)
  gives the length-`d` regular sequence (no new work beyond the application);
  (d) assemble `↑grade = dim` from (1) + (c).
  Cost: (a) is free (see above); (c)/(d) are routine
  given (b). What remains is the vanishing input (b) + maximal-sequence
  existence: (b) is out of scope here — no Koszul/AB content is attempted in
  this file (the conditional Koszul/self-duality development
in `Regularity/Koszul/SelfDuality.lean`);
  maximality routes through
  VariableInductionCM L5/L6 (explicit residuals, see standing below).
  recommendation: direct variable-subset induction (concrete zerodivisor
  analysis in `MvPolynomial` localizations — the R5 route noted in
  `HeightDrop.lean` — avoids building Koszul machinery; consumes the proved
  successive-regularity data and the Rees-backward pattern for assembly).
  Caveat: both routes need currently-absent infrastructure
  (normalization/maximal-subset analysis vs Koszul/self-duality).
  precision: `DepthEqDimAt`'s `=` is across the
  `ℕ∞ → WithBot ℕ∞` coercion — `grade` is `ℕ∞`-valued while `ringKrullDim`
  (like `supportDim`) is `WithBot`-valued.
  iterated chain (proved):
  `grade_quotIter_add_eq_grade` + `grade_two_step_eq` supply the (i)×`k`
  telescope. Standing for G-(iii): grade ≤ dim (proved:
  `grade_le_supportDim` / `grade_le_ringKrullDim`) + drop chain (proved this
  session) + maximal-sequence existence to length `d` (residual:
  `VariableInductionCM` L5 `QuotientSingletonResidual` / `VarUnmixedOneResidual`
  and L6 `VarHeightDropResidual`, taken as explicit hypotheses wherever
  used, never assumed). Feeding the localized successive family
  (`RegularSequenceDimDrop.successiveSMulRegular_map_atPrime` +
  `RegularityBridge.isRegular_ofFn_of_successive` + properness from `J ≤ P ≠ ⊤`)
  into the iterated equation is the remaining localization-stability step of
  `GradeDropChain` proper.
* Bridge (`GradeUnmixedBridge`): SPEC with a five-step skeleton in the
  docstring below. Note the parallel landing `unmixed_two_of_catenary_upper`
  in `CohenMacaulayFragment.lean` rests on a bridge since proved false in general — nothing
  here builds on it; the true residual remains `P.height ≤ k` for Ass primes
  (`HeightDrop.HeightDropResidualAt`), which this bridge targets directly.

## References

Project (read-only; never edited here):

* `Regularity/Avoid/RegularityBridge.lean` (`RegularityBridge` namespace):
  `RegularityBridge.SuccessiveSMulRegular` (consumed by `GradeDropChain` and the
  assembly).
* `Regularity/Unmixed/HeightDrop.lean` (`HeightDrop` namespace):
  `HeightDrop.HeightDropResidualAt` (the true residual this serves),
  `HeightDrop.minimal_of_height_le`, `HeightDrop.localized_dim_zero_of_height_le`
  (consumed by the assembly).
* `Regularity/Unmixed/Unmixedness.lean` (bare `Bezout` namespace):
  `mem_minimalPrimes_of_localized_quotient_dim_zero` (the endgame the assembly
  routes through, via `HeightDrop.minimal_of_height_le`).
* `Regularity/Avoid/AssHeightBound.lean` (`AssHeightBound` namespace):
  `height_eq_add_of_span` (orientation: `↑height P = dim (R_P ⧸ J_P) + k`).
* `Regularity/Unmixed/CohenMacaulayFragment.lean` (bare `Bezout` namespace): roadblock ledger
  (U1/U2/CM); `unmixed_two_of_catenary_upper` explicitly not consumed
  (bridge proved false in general).

Mathlib: see the exists list above.
-/

universe u

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace GradeDepthFragment

open RingTheory.Sequence
open scoped Pointwise

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Lengths of `M`-regular sequences with all entries in `I`: the raw set
whose supremum is grade. -/
def GradeSet (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) : Set ℕ :=
  { n | ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ I) ∧ IsRegular M rs }

/-- Grade (depth) of `M` w.r.t. `I`: supremum of lengths of `M`-regular
sequences contained in `I`. Stated with `IsRegular` lists only — no `Ext`,
no Koszul, no projective dimension. -/
noncomputable def grade (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) : ℕ∞ :=
  sSup ((Nat.cast : ℕ → ℕ∞) '' GradeSet R M I)

/-- Supremum-level grade drop across one regular element (address for (i) at
supremum level, now proved as `grade_quotSMulTop_add_one_eq_grade` under
`I • ⊤ < ⊤`): quotienting by a regular `x ∈ I` drops grade by exactly one.
The sequence-level content is proved below
(`isRegular_tail_of_cons`, `isRegular_cons_of_head_tail`); the `≥` half at
supremum level is `grade_quotSMulTop_add_one_le_grade` (needs `x • ⊤ < ⊤`);
the `≤` half is `grade_le_quotSMulTop_add_one` via the Rees bridge. -/
def GradeDropOne (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (x : R) : Prop :=
  IsSMulRegular M x → x ∈ I →
    grade R (QuotSMulTop x M) I + 1 = grade R M I

/-- (i), forward, proved: the tail of a regular sequence is regular on the
quotient. One-line apply of `isRegular_cons_iff`
(`Regular/RegularSequence.lean`). -/
theorem isRegular_tail_of_cons {r : R} {rs : List R}
    (h : IsRegular M (r :: rs)) :
    IsRegular (QuotSMulTop r M) rs :=
  ((isRegular_cons_iff M r rs).mp h).2

/-- (i), backward, proved: regularity of head + tail assembles to regularity
of the cons (properness is inside `IsRegular` and handled by the iff).
One-line apply of `isRegular_cons_iff`. -/
theorem isRegular_cons_of_head_tail {r : R} {rs : List R}
    (h1 : IsSMulRegular M r) (h2 : IsRegular (QuotSMulTop r M) rs) :
    IsRegular M (r :: rs) :=
  (isRegular_cons_iff M r rs).mpr ⟨h1, h2⟩

/-- Membership constructor for `GradeSet` (proved tooling). -/
theorem mem_gradeSet_of_isRegular (I : Ideal R) {n : ℕ} (rs : List R)
    (hlen : rs.length = n) (hmem : ∀ r ∈ rs, r ∈ I)
    (hreg : IsRegular M rs) :
    n ∈ GradeSet R M I :=
  ⟨rs, hlen, hmem, hreg⟩

/-- Grade lower bound from a witness sequence (proved tooling, `le_sSup`). -/
theorem le_grade_of_mem_gradeSet (I : Ideal R) {n : ℕ}
    (hn : n ∈ GradeSet R M I) :
    (n : ℕ∞) ≤ grade R M I :=
  le_sSup ⟨n, hn, rfl⟩

/-- Coercion `ℕ∞ → WithBot ℕ∞` preserves suprema of nonempty sets (bridge
between `grade`, which is `ℕ∞`-valued, and `Module.supportDim` /
`ringKrullDim`, which are `WithBot ℕ∞`-valued). Nonemptiness is sharp: for
`S = ∅`, LHS is `↑⊥ ≠ ⊥ = RHS`. -/
theorem withBot_coe_sSup (S : Set ℕ∞) (hS : S.Nonempty) :
    ((sSup S : ℕ∞) : WithBot ℕ∞) = sSup (((↑) : ℕ∞ → WithBot ℕ∞) '' S) := by
  apply le_antisymm
  · cases hB : sSup (((↑) : ℕ∞ → WithBot ℕ∞) '' S) with
    | bot =>
      have hB' : sSup (((↑) : ℕ∞ → WithBot ℕ∞) '' S) = ⊥ := hB
      have hSe : S = ∅ := by
        by_contra hne
        obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.mpr hne
        have hle : ((y : ℕ∞) : WithBot ℕ∞) ≤
            sSup (((↑) : ℕ∞ → WithBot ℕ∞) '' S) :=
          le_sSup ⟨y, hy, rfl⟩
        rw [hB'] at hle
        exact absurd (le_bot_iff.mp hle) WithBot.coe_ne_bot
      exact False.elim ((Set.nonempty_iff_ne_empty.mp hS) hSe)
    | coe b =>
      have hbdd : ∀ y ∈ S, y ≤ b := by
        intro y hy
        have hle : ((y : ℕ∞) : WithBot ℕ∞) ≤
            sSup (((↑) : ℕ∞ → WithBot ℕ∞) '' S) :=
          le_sSup ⟨y, hy, rfl⟩
        rw [hB] at hle
        exact WithBot.coe_le_coe.mp hle
      have hle : sSup S ≤ b := sSup_le hbdd
      exact WithBot.coe_le_coe.mpr hle
  · refine sSup_le ?_
    rintro _ ⟨y, hyS, rfl⟩
    exact WithBot.coe_le_coe.mpr (le_sSup hyS)

/-- Grade is bounded by support dimension (deep-core step (1), proved): every
`M`-regular sequence has length at most `Module.supportDim R M`. The per-step
content is `Module.supportDim_quotSMulTop_succ_eq_supportDim` (maximal-ideal
form); the iterated form `Module.supportDim_add_length_eq_supportDim_of_isRegular`
(`KrullDimension/Regular.lean`) gives the bound directly, since every
`IsRegular` witness sequence qualifies (regularity forces each entry into the
maximal ideal). The grade set is always nonempty under `Nontrivial M` (the
empty sequence is regular), which is also exactly what rules out the trivial
counterexample (`grade = ⊥`, `↑⊥ ≰ ⊥`). Note `Module.supportDim` is
`WithBot ℕ∞`-valued, so the statement coerces `grade` (via `withBot_coe_sSup`). -/
theorem grade_le_supportDim [IsNoetherianRing R] [Module.Finite R M] [IsLocalRing R]
    [Nontrivial M] (I : Ideal R) :
    (grade R M I : WithBot ℕ∞) ≤ Module.supportDim R M := by
  have mem0 : 0 ∈ GradeSet R M I :=
    ⟨[], rfl, by simp, IsRegular.nil R M⟩
  have hneI : ((Nat.cast : ℕ → ℕ∞) '' GradeSet R M I).Nonempty :=
    ⟨_, 0, mem0, rfl⟩
  change ((sSup ((Nat.cast : ℕ → ℕ∞) '' GradeSet R M I) : ℕ∞) : WithBot ℕ∞) ≤
    Module.supportDim R M
  rw [withBot_coe_sSup _ hneI]
  refine sSup_le ?_
  rintro _ ⟨z, hzS, rfl⟩
  obtain ⟨n, hnmem, rfl⟩ := hzS
  obtain ⟨rs, hlen, _hmem, hreg⟩ := hnmem
  subst hlen
  have h := Module.supportDim_add_length_eq_supportDim_of_isRegular rs hreg
  have hD : Module.supportDim R M ≠ ⊥ :=
    (Module.supportDim_ne_bot_iff_nontrivial R M).mpr inferInstance
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hD
  have hD' : Module.supportDim R (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M)) ≠ ⊥ := by
    rintro hcon
    rw [hcon] at h
    simp at h
    exact hD h.symm
  obtain ⟨d', hd'⟩ := WithBot.ne_bot_iff_exists.mp hD'
  rw [← hd', ← hd] at h
  have h' : (↑d' : WithBot ℕ∞) + (↑(((List.length rs : ℕ)) : ℕ∞)) =
      (↑d : WithBot ℕ∞) := h
  rw [← WithBot.coe_add] at h'
  have heq : d' + ((List.length rs : ℕ) : ℕ∞) = d := WithBot.coe_eq_coe.mp h'
  have hle : ((List.length rs : ℕ) : ℕ∞) ≤ d :=
    calc ((List.length rs : ℕ) : ℕ∞) ≤ d' + _ := le_add_left le_rfl
      _ = d := heq
  rw [← hd]
  exact WithBot.coe_le_coe.mpr hle

/-- Grade of the ring in itself is bounded by Krull dimension (proved). -/
theorem grade_le_ringKrullDim [IsNoetherianRing R] [IsLocalRing R]
    (I : Ideal R) : (grade R R I : WithBot ℕ∞) ≤ ringKrullDim R := by
  have mem0 : 0 ∈ GradeSet R R I :=
    ⟨[], rfl, by simp, IsRegular.nil R R⟩
  have hneI : ((Nat.cast : ℕ → ℕ∞) '' GradeSet R R I).Nonempty :=
    ⟨_, 0, mem0, rfl⟩
  change ((sSup ((Nat.cast : ℕ → ℕ∞) '' GradeSet R R I) : ℕ∞) : WithBot ℕ∞) ≤
    ringKrullDim R
  rw [withBot_coe_sSup _ hneI]
  refine sSup_le ?_
  rintro _ ⟨z, hzS, rfl⟩
  obtain ⟨n, hnmem, rfl⟩ := hzS
  obtain ⟨rs, hlen, _hmem, hreg⟩ := hnmem
  subst hlen
  have h := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular rs hreg
  have hD : ringKrullDim R ≠ ⊥ := by
    rw [← Module.supportDim_self_eq_ringKrullDim]
    exact (Module.supportDim_ne_bot_iff_nontrivial R R).mpr inferInstance
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hD
  have hD' : ringKrullDim (R ⧸ Ideal.ofList rs) ≠ ⊥ := by
    rintro hcon
    rw [hcon] at h
    simp at h
    exact hD h.symm
  obtain ⟨d', hd'⟩ := WithBot.ne_bot_iff_exists.mp hD'
  rw [← hd', ← hd] at h
  have h' : (↑d' : WithBot ℕ∞) + (↑(((List.length rs : ℕ)) : ℕ∞)) =
      (↑d : WithBot ℕ∞) := h
  rw [← WithBot.coe_add] at h'
  have heq : d' + ((List.length rs : ℕ) : ℕ∞) = d := WithBot.coe_eq_coe.mp h'
  have hle : ((List.length rs : ℕ) : ℕ∞) ≤ d :=
    calc ((List.length rs : ℕ) : ℕ∞) ≤ d' + _ := le_add_left le_rfl
      _ = d := heq
  rw [← hd]
  exact WithBot.coe_le_coe.mpr hle

/-- Supremum-shift helper (pure order theory): if every element of
`S ⊆ Set.range Nat.cast` satisfies `y + 1 ≤ G` and `1 ≤ G`, then
`sSup S + 1 ≤ G`. The empty case chains `sSup ∅ ≤ 0` with `1 ≤ G`; the `⊤`
case uses unboundedness (`∀ k, ↑k ≤ G` forces `G = ⊤`); the finite case uses
attainment of the supremum in `S` (a finite supremum of naturals is attained). -/
theorem sSup_add_one_le_of_forall_add_one_le {S : Set ℕ∞}
    (hS : S ⊆ Set.range (Nat.cast : ℕ → ℕ∞))
    {G : ℕ∞} (h1 : ∀ y ∈ S, y + 1 ≤ G) (hone : 1 ≤ G) :
    sSup S + 1 ≤ G := by
  by_cases hSe : S = ∅
  · subst hSe
    have h0 : sSup (∅ : Set ℕ∞) ≤ 0 := by
      refine sSup_le ?_
      intro y hy
      exact absurd hy (Set.notMem_empty y)
    have hle : sSup (∅ : Set ℕ∞) + 1 ≤ 0 + 1 := add_le_add h0 le_rfl
    rw [zero_add] at hle
    exact le_trans hle hone
  · by_cases htop : sSup S = ⊤
    · have hGe : G = ⊤ := by
        by_contra hGne
        obtain ⟨j, hj⟩ := WithTop.ne_top_iff_exists.mp hGne
        have hlt : ((j + 1 : ℕ) : ℕ∞) < sSup S := by
          rw [htop]
          exact WithTop.coe_lt_top _
        have hex : ∃ y ∈ S, ((j + 1 : ℕ) : ℕ∞) < y := by
          by_contra hcon
          have hle : sSup S ≤ ((j + 1 : ℕ) : ℕ∞) := by
            refine sSup_le ?_
            intro y hy
            by_contra hle'
            exact hcon ⟨y, hy, lt_of_not_ge hle'⟩
          rw [htop] at hle
          exact absurd hle (by simp)
        obtain ⟨y, hyS, hy⟩ := hex
        obtain ⟨m, rfl⟩ := hS hyS
        have hjm : j + 1 ≤ m := by
          have h' : j + 1 < m := by exact_mod_cast hy
          omega
        have hmG : ((m : ℕ) : ℕ∞) + 1 ≤ G := h1 _ hyS
        rw [← hj] at hmG
        have hle : ((j + 1 : ℕ) : ℕ∞) ≤ ((j : ℕ) : ℕ∞) :=
          le_trans (by exact_mod_cast hjm) (le_trans (le_add_right le_rfl) hmG)
        have hcon : j + 1 ≤ j := by exact_mod_cast hle
        omega
      rw [htop, hGe]
      exact le_top
    · obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp htop
      have hatt : ((t : ℕ) : ℕ∞) ∈ S := by
        by_contra hcon
        have hbdd : ∀ y ∈ S, y ≤ (((t - 1 : ℕ)) : ℕ∞) := by
          intro y hy
          obtain ⟨m, rfl⟩ := hS hy
          have hle : ((m : ℕ) : ℕ∞) ≤ ((t : ℕ) : ℕ∞) :=
            le_trans (le_sSup hy) ht.ge
          have hmt : m ≤ t := by exact_mod_cast hle
          have hne : m ≠ t := by
            rintro rfl
            exact hcon hy
          have hmlt : m < t := lt_of_le_of_ne hmt hne
          have hsub : m ≤ t - 1 := by omega
          exact_mod_cast hsub
        have hle : ((t : ℕ) : ℕ∞) ≤ (((t - 1 : ℕ)) : ℕ∞) :=
          le_trans ht.le (sSup_le hbdd)
        have htt : t ≤ t - 1 := by exact_mod_cast hle
        have ht0 : t = 0 := by omega
        subst ht0
        obtain ⟨y0, hy0⟩ := Set.nonempty_iff_ne_empty.mpr hSe
        obtain ⟨m0, _hm0, rfl⟩ := hS hy0
        have h0le := hbdd _ hy0
        have hm00 : m0 = 0 := by
          have h' : ((m0 : ℕ) : ℕ∞) ≤ ((0 : ℕ) : ℕ∞) := by simpa using h0le
          have h'' : m0 ≤ 0 := by exact_mod_cast h'
          exact Nat.le_zero.mp h''
        subst hm00
        exact hcon hy0
      have h3 : ((t : ℕ) : ℕ∞) + 1 ≤ G := h1 _ hatt
      have heq : sSup S + 1 = ((t : ℕ) : ℕ∞) + 1 :=
        congrArg (· + 1 : ℕ∞ → ℕ∞) ht.symm
      rw [heq]
      exact h3

/-- (i) at supremum level, `≥` half, proved: quotienting by a regular
`x ∈ I` (with `x • ⊤ < ⊤`, so `[x]` is regular) drops grade by at least one.
Every `QuotSMulTop`-regular sequence conses with `x` (proved cons direction),
and the `sSup`-shift helper assembles the bound. The `≤` half needs grade
maximality via the Rees bridge (see ledger G-(i)). -/
theorem grade_quotSMulTop_add_one_le_grade (I : Ideal R) (x : R)
    (hxreg : IsSMulRegular M x) (hxI : x ∈ I)
    (hxprop : x • (⊤ : Submodule R M) < ⊤) :
    grade R (QuotSMulTop x M) I + 1 ≤ grade R M I := by
  refine sSup_add_one_le_of_forall_add_one_le (Set.image_subset_range _ _) ?_ ?_
  · intro y hy
    obtain ⟨n, hnmem, rfl⟩ := hy
    obtain ⟨ts, hlen, hmem, hreg⟩ := hnmem
    have hcons : IsRegular M (x :: ts) := isRegular_cons_of_head_tail hxreg hreg
    have hmem' : ∀ r ∈ x :: ts, r ∈ I := by
      intro r hr
      rcases List.mem_cons.mp hr with rfl | h
      · exact hxI
      · exact hmem r h
    have hlen' : (x :: ts).length = n + 1 := by rw [List.length_cons, hlen]
    have hle : (((n + 1 : ℕ)) : ℕ∞) ≤ grade R M I :=
      le_grade_of_mem_gradeSet I (mem_gradeSet_of_isRegular I (x :: ts) hlen' hmem' hcons)
    have hcast : ((n : ℕ) : ℕ∞) + 1 = (((n + 1 : ℕ)) : ℕ∞) := by push_cast; ring
    rw [hcast]
    exact hle
  · have hproper : (⊤ : Submodule R M) ≠ Ideal.ofList [x] • ⊤ := by
      rw [Ideal.ofList_singleton, Submodule.ideal_span_singleton_smul]
      exact Ne.symm (lt_top_iff_ne_top.mp hxprop)
    have hsingle : IsRegular M [x] :=
      ⟨(isWeaklyRegular_singleton_iff _ x).mpr hxreg, hproper⟩
    have h1mem := le_grade_of_mem_gradeSet I
      (mem_gradeSet_of_isRegular I [x] rfl (by simpa using hxI) hsingle)
    simpa using h1mem

/-- Rees-bridge crux for the `≤` half: a length-`m+1` `M'`-regular sequence in
`I` yields a length-`m` regular sequence on `QuotSMulTop x M'` in `I`.
Proof: `subsingleton_ext_of_exists_isRegular` turns the sequence into
`Ext`-vanishing below `m+1`; the LES dimension shift
(`Ext.covariant_sequence_exact₃'` along `smulShortComplex`) moves it to the
quotient below `m`; `exists_isRegular_of_exists_subsingleton_ext` turns it
back into a sequence. All three are public in `Depth/Rees.lean`.

Universe note: `R' M'` share one universe `u` (fresh names, leaving the
file's two-universe `R M` contracts untouched) — the Rees bridge needs both
modules in a single `ModuleCat.{u}`, and all in-project applications are
single-universe anyway. -/
theorem exists_isRegular_quotSMulTop_of_isRegular_succ {R' M' : Type u}
    [CommRing R'] [AddCommGroup M'] [Module R' M'] [IsNoetherianRing R']
    [Module.Finite R' M'] (I : Ideal R') (x : R') (hxreg : IsSMulRegular M' x)
    (hxI : x ∈ I) (hIlt : I • (⊤ : Submodule R' M') < ⊤)
    {m : ℕ} {rs : List R'} (hlen : rs.length = m + 1)
    (hmem : ∀ r ∈ rs, r ∈ I) (hreg : IsRegular M' rs) :
    ∃ ss : List R', ss.length = m ∧ (∀ r ∈ ss, r ∈ I) ∧
      IsRegular (QuotSMulTop x M') ss := by
  have hsupp : Module.support R' (R' ⧸ I) = PrimeSpectrum.zeroLocus I := by
    rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
  have hsuppN : Module.support R' ↥(ModuleCat.of R' (R' ⧸ I)) =
      PrimeSpectrum.zeroLocus I := hsupp
  have hreg' : IsRegular ↥(ModuleCat.of R' M') rs := hreg
  have hIlt' : I • (⊤ : Submodule R' ↥(ModuleCat.of R' M')) < ⊤ := hIlt
  have hxreg' : IsSMulRegular ↥(ModuleCat.of R' M') x := hxreg
  have hfwd : ∀ i < rs.length,
      Subsingleton (CategoryTheory.Abelian.Ext (ModuleCat.of R' (R' ⧸ I))
        (ModuleCat.of R' M') i) :=
    ModuleCat.subsingleton_ext_of_exists_isRegular I _ hsuppN.subset _ hIlt' rs
      hmem hreg'
  have hsex : (ModuleCat.smulShortComplex (ModuleCat.of R' M') x).ShortExact :=
    IsSMulRegular.smulShortComplex_shortExact hxreg'
  have h_ext' : ∀ i < m, Subsingleton (CategoryTheory.Abelian.Ext
      (ModuleCat.of R' (R' ⧸ I))
      (ModuleCat.smulShortComplex (ModuleCat.of R' M') x).X₃ i) := by
    intro i hi
    have zero1 := AddCommGrpCat.isZero_of_iff_subsingleton.mpr (hfwd i (by omega))
    have zero2 :=
      AddCommGrpCat.isZero_of_iff_subsingleton.mpr (hfwd (i + 1) (by omega))
    exact AddCommGrpCat.subsingleton_of_isZero <|
      CategoryTheory.ShortComplex.Exact.isZero_of_both_zeros
        ((CategoryTheory.Abelian.Ext.covariant_sequence_exact₃' _ hsex) i (i + 1)
          rfl)
        (zero1.eq_zero_of_src _) (zero2.eq_zero_of_tgt _)
  have hQlt : I • (⊤ : Submodule R'
      ↥(ModuleCat.smulShortComplex (ModuleCat.of R' M') x).X₃) < ⊤ := by
    change I • (⊤ : Submodule R' (QuotSMulTop x M')) < ⊤
    rw [lt_top_iff_ne_top]
    intro hcon
    have hsurj : Function.Surjective (Submodule.mkQ (x • (⊤ : Submodule R' M'))) :=
      Submodule.mkQ_surjective _
    have h2 : I • (⊤ : Submodule R' M') ⊔ x • (⊤ : Submodule R' M') = ⊤ := by
      have hcc := congrArg
        (Submodule.comap (Submodule.mkQ (x • (⊤ : Submodule R' M')))) hcon
      rw [Submodule.comap_top,
        Submodule.comap_smul_top_of_surjective I _ hsurj] at hcc
      rwa [Submodule.ker_mkQ] at hcc
    have hle : x • (⊤ : Submodule R' M') ≤ I • (⊤ : Submodule R' M') := by
      have hspan : Ideal.span {x} ≤ I := (Ideal.span_singleton_le_iff_mem I).mpr hxI
      calc x • (⊤ : Submodule R' M') = Ideal.span {x} • (⊤ : Submodule R' M') := by
            rw [Submodule.ideal_span_singleton_smul]
        _ ≤ I • (⊤ : Submodule R' M') := Submodule.smul_mono_left hspan
    rw [sup_eq_left.mpr hle] at h2
    exact hIlt.ne h2
  have hfin : Module.Finite R'
      ↥(ModuleCat.smulShortComplex (ModuleCat.of R' M') x).X₃ :=
    Module.Finite.of_surjective
      (Submodule.mkQ (x • (⊤ : Submodule R' M')) :
        M' →ₗ[R'] ↥(ModuleCat.smulShortComplex (ModuleCat.of R' M') x).X₃)
      (Submodule.mkQ_surjective _)
  obtain ⟨ss, hslen, hsmem, hsreg⟩ :=
    @ModuleCat.exists_isRegular_of_exists_subsingleton_ext _ inferInstance
      inferInstance inferInstance I m _ hfin hQlt _ inferInstance hsuppN h_ext'
  exact ⟨ss, hslen, hsmem, hsreg⟩

/-- (i) at supremum level, `≤` half, proved via the Rees bridge: every
`M'`-regular sequence in `I` is at most one longer than the grade of the
quotient. The `m+1` case is the crux above; the `0` case is `zero_le`. -/
theorem grade_le_quotSMulTop_add_one {R' M' : Type u}
    [CommRing R'] [AddCommGroup M'] [Module R' M'] [IsNoetherianRing R']
    [Module.Finite R' M'] (I : Ideal R') (x : R') (hxreg : IsSMulRegular M' x)
    (hxI : x ∈ I) (hIlt : I • (⊤ : Submodule R' M') < ⊤) :
    grade R' M' I ≤ grade R' (QuotSMulTop x M') I + 1 := by
  refine sSup_le ?_
  rintro _ ⟨n, hnmem, rfl⟩
  obtain ⟨rs, hlen, hmem, hreg⟩ := hnmem
  rcases n with _ | m
  · simp
  · obtain ⟨ss, hslen, hsmem, hsreg⟩ :=
      exists_isRegular_quotSMulTop_of_isRegular_succ I x hxreg hxI hIlt hlen hmem
        hreg
    have hle : ((m : ℕ) : ℕ∞) ≤ grade R' (QuotSMulTop x M') I :=
      le_grade_of_mem_gradeSet I (mem_gradeSet_of_isRegular I ss hslen hsmem hsreg)
    calc (((m + 1 : ℕ)) : ℕ∞) = ((m : ℕ) : ℕ∞) + 1 := by push_cast; ring
      _ ≤ grade R' (QuotSMulTop x M') I + 1 := by gcongr

/-- (i) at supremum level, full equation, proved: quotienting by a regular
`x ∈ I` (with `I • ⊤ < ⊤`, which implies `x • ⊤ < ⊤`) drops grade by exactly
one. Assembles the `≥` half (`grade_quotSMulTop_add_one_le_grade`) and the
`≤` half (`grade_le_quotSMulTop_add_one`). This is the `GradeDropOne` promise
under its sharp nondegeneracy hypothesis (same-universe `R' M'`, covering all
in-project applications). -/
theorem grade_quotSMulTop_add_one_eq_grade {R' M' : Type u}
    [CommRing R'] [AddCommGroup M'] [Module R' M'] [IsNoetherianRing R']
    [Module.Finite R' M'] (I : Ideal R') (x : R') (hxreg : IsSMulRegular M' x)
    (hxI : x ∈ I) (hIlt : I • (⊤ : Submodule R' M') < ⊤) :
    grade R' (QuotSMulTop x M') I + 1 = grade R' M' I := by
  have hxprop : x • (⊤ : Submodule R' M') < ⊤ := by
    calc x • (⊤ : Submodule R' M') = Ideal.span {x} • (⊤ : Submodule R' M') := by
          rw [Submodule.ideal_span_singleton_smul]
      _ ≤ I • (⊤ : Submodule R' M') :=
          Submodule.smul_mono_left ((Ideal.span_singleton_le_iff_mem I).mpr hxI)
      _ < ⊤ := hIlt
  apply le_antisymm
  · exact grade_quotSMulTop_add_one_le_grade I x hxreg hxI hxprop
  · exact grade_le_quotSMulTop_add_one I x hxreg hxI hIlt

/-- Iterated `QuotSMulTop` quotient along a list: `quotIter M' [x₁, …, xₖ]`
is `(…((M' ⧸ x₁) ⧸ x₂) … ⧸ xₖ)`. Each quotient stays in the same universe `u`
(submodule quotient), so the Rees-bridge `≤` half (same-universe `R' M'`, as
in `koszul_grade_drop_le`) applies at every rung. The telescope vehicle for
VariableInductionCM L6 / maximal-regular-sequence arguments: combined with
`IsRegular M' rs`, grade drops by exactly `rs.length`
(`grade_quotIter_add_eq_grade`). -/
def quotIter {R' : Type u} [CommRing R'] (M' : Type u) [AddCommGroup M']
    [Module R' M'] : List R' → Type u
  | [] => M'
  | x :: xs => quotIter (QuotSMulTop x M') xs

/-- `AddCommGroup` structure on the iterated quotient (recursion on the list;
the cons case is the submodule-quotient instance). -/
instance quotIterAddCommGroup {R' : Type u} [CommRing R'] (M' : Type u)
    [AddCommGroup M'] [Module R' M'] (rs : List R') :
    AddCommGroup (quotIter M' rs) := by
  match rs with
  | [] => change AddCommGroup M'; infer_instance
  | x :: xs => exact quotIterAddCommGroup (QuotSMulTop x M') xs

/-- `Module` structure on the iterated quotient (recursion on the list). -/
instance quotIterModule {R' : Type u} [CommRing R'] (M' : Type u)
    [AddCommGroup M'] [Module R' M'] (rs : List R') :
    Module R' (quotIter M' rs) := by
  match rs with
  | [] => change Module R' M'; infer_instance
  | x :: xs => exact quotIterModule (QuotSMulTop x M') xs

/-- Nondegeneracy descends to the quotient: `I • ⊤ < ⊤` on `M'` plus `x ∈ I`
gives `I • ⊤ < ⊤` on `QuotSMulTop x M'`. Same argument as the `hQlt` step of
`exists_isRegular_quotSMulTop_of_isRegular_succ` (comap along the `mkQ`
surjection, then `sup_eq_left` from `x • ⊤ ≤ I • ⊤`); factored out for the
iterated-chain induction, which needs it at every rung. -/
private theorem smulTop_lt_top_quotSMulTop {R' M' : Type u}
    [CommRing R'] [AddCommGroup M'] [Module R' M']
    (I : Ideal R') (x : R') (hxI : x ∈ I)
    (hIlt : I • (⊤ : Submodule R' M') < ⊤) :
    I • (⊤ : Submodule R' (QuotSMulTop x M')) < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro hcon
  have hsurj : Function.Surjective (Submodule.mkQ (x • (⊤ : Submodule R' M'))) :=
    Submodule.mkQ_surjective _
  have h2 : I • (⊤ : Submodule R' M') ⊔ x • (⊤ : Submodule R' M') = ⊤ := by
    have hcc := congrArg
      (Submodule.comap (Submodule.mkQ (x • (⊤ : Submodule R' M')))) hcon
    rw [Submodule.comap_top,
      Submodule.comap_smul_top_of_surjective I _ hsurj] at hcc
    rwa [Submodule.ker_mkQ] at hcc
  have hle : x • (⊤ : Submodule R' M') ≤ I • (⊤ : Submodule R' M') := by
    have hspan : Ideal.span {x} ≤ I := (Ideal.span_singleton_le_iff_mem I).mpr hxI
    calc x • (⊤ : Submodule R' M') = Ideal.span {x} • (⊤ : Submodule R' M') := by
          rw [Submodule.ideal_span_singleton_smul]
      _ ≤ I • (⊤ : Submodule R' M') := Submodule.smul_mono_left hspan
  rw [sup_eq_left.mpr hle] at h2
  exact hIlt.ne h2

/-- Iterated drop, `≥` half: across a regular sequence `rs` in `I` (with
`I • ⊤ < ⊤`), the iterated-quotient grade plus `rs.length` is at most the
grade. HilbertFunctionCount on `rs` via the single-step `≥` half
(`grade_quotSMulTop_add_one_le_grade`) + `isRegular_cons_iff` surgery; needs
neither Noetherian nor finiteness (mirroring the single-step `≥` half). -/
theorem grade_quotIter_add_le_grade {R' M' : Type u}
    [CommRing R'] [AddCommGroup M'] [Module R' M']
    (I : Ideal R') (rs : List R')
    (hmem : ∀ r ∈ rs, r ∈ I)
    (hIlt : I • (⊤ : Submodule R' M') < ⊤)
    (hreg : IsRegular M' rs) :
    grade R' (quotIter M' rs) I + ((rs.length : ℕ) : ℕ∞) ≤ grade R' M' I := by
  induction rs generalizing M' with
  | nil =>
    change grade R' M' I + (((0 : ℕ)) : ℕ∞) ≤ grade R' M' I
    simp
  | cons x xs ih =>
    have hxreg : IsSMulRegular M' x := ((isRegular_cons_iff M' x xs).mp hreg).1
    have htail : IsRegular (QuotSMulTop x M') xs :=
      ((isRegular_cons_iff M' x xs).mp hreg).2
    have hxI : x ∈ I := hmem x List.mem_cons_self
    have hmem' : ∀ r ∈ xs, r ∈ I := fun r hr => hmem r (List.mem_cons_of_mem _ hr)
    have hIlt' := smulTop_lt_top_quotSMulTop I x hxI hIlt
    have hxprop : x • (⊤ : Submodule R' M') < ⊤ := by
      calc x • (⊤ : Submodule R' M') = Ideal.span {x} • (⊤ : Submodule R' M') := by
            rw [Submodule.ideal_span_singleton_smul]
        _ ≤ I • (⊤ : Submodule R' M') :=
            Submodule.smul_mono_left ((Ideal.span_singleton_le_iff_mem I).mpr hxI)
        _ < ⊤ := hIlt
    have hstep := grade_quotSMulTop_add_one_le_grade I x hxreg hxI hxprop
    have hIH := ih (M' := QuotSMulTop x M') hmem' hIlt' htail
    change grade R' (quotIter (QuotSMulTop x M') xs) I +
        ((((xs.length + 1 : ℕ))) : ℕ∞) ≤ _
    have hcast : ((((xs.length + 1 : ℕ))) : ℕ∞) = ((xs.length : ℕ) : ℕ∞) + 1 := by
      push_cast; ring
    rw [hcast, ← add_assoc]
    calc grade R' (quotIter (QuotSMulTop x M') xs) I +
            (((xs.length : ℕ)) : ℕ∞) + 1
        ≤ grade R' (QuotSMulTop x M') I + 1 := by gcongr
      _ ≤ grade R' M' I := hstep

/-- Iterated drop, `≤` half, via the Rees bridge: the grade is at most the
iterated-quotient grade plus `rs.length`. HilbertFunctionCount on `rs` via the
single-step `≤` half (`grade_le_quotSMulTop_add_one`) + `isRegular_cons_iff`
surgery; `Module.Finite` descends to each quotient via
`Module.Finite.of_surjective` + `Submodule.mkQ_surjective` (same pattern as
`exists_isRegular_quotSMulTop_of_isRegular_succ`). Same-universe `R' M'`. -/
theorem grade_le_quotIter_add {R' M' : Type u}
    [CommRing R'] [AddCommGroup M'] [Module R' M'] [IsNoetherianRing R']
    [Module.Finite R' M'] (I : Ideal R') (rs : List R')
    (hmem : ∀ r ∈ rs, r ∈ I)
    (hIlt : I • (⊤ : Submodule R' M') < ⊤)
    (hreg : IsRegular M' rs) :
    grade R' M' I ≤
      grade R' (quotIter M' rs) I + ((rs.length : ℕ) : ℕ∞) := by
  induction rs generalizing M' with
  | nil =>
    change grade R' M' I ≤ grade R' M' I + (((0 : ℕ)) : ℕ∞)
    simp
  | cons x xs ih =>
    have hxreg : IsSMulRegular M' x := ((isRegular_cons_iff M' x xs).mp hreg).1
    have htail : IsRegular (QuotSMulTop x M') xs :=
      ((isRegular_cons_iff M' x xs).mp hreg).2
    have hxI : x ∈ I := hmem x List.mem_cons_self
    have hmem' : ∀ r ∈ xs, r ∈ I := fun r hr => hmem r (List.mem_cons_of_mem _ hr)
    have hIlt' := smulTop_lt_top_quotSMulTop I x hxI hIlt
    have hfin : Module.Finite R' (QuotSMulTop x M') :=
      Module.Finite.of_surjective (Submodule.mkQ (x • (⊤ : Submodule R' M')))
        (Submodule.mkQ_surjective _)
    have hstep := grade_le_quotSMulTop_add_one I x hxreg hxI hIlt
    have hIH := ih (M' := QuotSMulTop x M') hmem' hIlt' htail
    change grade R' M' I ≤ grade R' (quotIter (QuotSMulTop x M') xs) I +
        ((((xs.length + 1 : ℕ))) : ℕ∞)
    have hcast : ((((xs.length + 1 : ℕ))) : ℕ∞) = ((xs.length : ℕ) : ℕ∞) + 1 := by
      push_cast; ring
    rw [hcast, ← add_assoc]
    calc grade R' M' I ≤ grade R' (QuotSMulTop x M') I + 1 := hstep
      _ ≤ grade R' (quotIter (QuotSMulTop x M') xs) I +
            (((xs.length : ℕ)) : ℕ∞) + 1 := by gcongr

/-- Iterated drop, full equation: across a regular sequence `rs` in `I` (with
`I • ⊤ < ⊤`), the iterated-quotient grade plus `rs.length` equals the grade.
Assembles the `≥` half (`grade_quotIter_add_le_grade`) and the `≤` half
(`grade_le_quotIter_add`). This is the (i)×`k` telescope vehicle for
VariableInductionCM L6 / maximal-regular-sequence arguments (same-universe `R' M'`,
covering all in-project applications). -/
theorem grade_quotIter_add_eq_grade {R' M' : Type u}
    [CommRing R'] [AddCommGroup M'] [Module R' M'] [IsNoetherianRing R']
    [Module.Finite R' M'] (I : Ideal R') (rs : List R')
    (hmem : ∀ r ∈ rs, r ∈ I)
    (hIlt : I • (⊤ : Submodule R' M') < ⊤)
    (hreg : IsRegular M' rs) :
    grade R' (quotIter M' rs) I + ((rs.length : ℕ) : ℕ∞) = grade R' M' I :=
  le_antisymm (grade_quotIter_add_le_grade I rs hmem hIlt hreg)
    (grade_le_quotIter_add I rs hmem hIlt hreg)

/-- Length-2 application (u2-shape consumer for `CohenMacaulayFragment` / L6 telescope input):
across a length-2 regular sequence, grade drops by exactly 2. Immediate from
the iterated equation at `rs = [x, y]` (`quotIter` unfolds definitionally to
the nested quotient; `([x, y].length : ℕ) = 2` by `rfl`,
`Nat.cast_ofNat` by `simp`). -/
theorem grade_two_step_eq {R' M' : Type u}
    [CommRing R'] [AddCommGroup M'] [Module R' M'] [IsNoetherianRing R']
    [Module.Finite R' M'] (I : Ideal R') (x y : R')
    (hxI : x ∈ I) (hyI : y ∈ I)
    (hIlt : I • (⊤ : Submodule R' M') < ⊤)
    (hreg : IsRegular M' [x, y]) :
    grade R' (QuotSMulTop y (QuotSMulTop x M')) I + 2 = grade R' M' I := by
  have hmem : ∀ r ∈ [x, y], r ∈ I := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hxI
    · exact hyI
  have h := grade_quotIter_add_eq_grade I [x, y] hmem hIlt hreg
  have hL : ((([x, y].length : ℕ)) : ℕ∞) = 2 := by simp
  rw [hL] at h
  exact h

/-- (ii) core, proved: no element of an associated prime is SMul-regular.
Proof: `P` is the radical of `colon ⊥ {x}` for some `x`; `y ∈ P` gives
`y ^ n • x = 0` with `x ≠ 0` (else `P = ⊤` against primeness), while
regularity of `y` passes to `y ^ n` (`IsSMulRegular.pow`), forcing `x = 0`.
Needs no Noetherian hypothesis. -/
theorem not_isSMulRegular_of_mem_associatedPrimes
    {P : Ideal R} (hP : P ∈ associatedPrimes R M) {y : R} (hy : y ∈ P) :
    ¬ IsSMulRegular M y := by
  intro hreg
  have hprime : P.IsPrime := (AssociatedPrimes.mem_iff.mp hP).isPrime
  have hmem : IsAssociatedPrime P M := AssociatedPrimes.mem_iff.mp hP
  have hsub : (⊥ : Submodule R M).IsAssociatedPrime P := hmem
  obtain ⟨x, hx⟩ := hsub.eq_radical_colon
  have hyrad : y ∈ (Submodule.colon (⊥ : Submodule R M) {x}).radical := by
    rw [← hx]
    exact hy
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hyrad
  rw [Submodule.mem_colon_singleton, Submodule.mem_bot] at hn
  have hpow : IsSMulRegular M (y ^ n) := hreg.pow n
  have hcon : ((y ^ n • ·) : M → M) x = ((y ^ n • ·) : M → M) 0 := by
    change y ^ n • x = y ^ n • (0 : M)
    rw [hn, smul_zero]
  have hx0 : x = 0 := hpow hcon
  have htop : P = ⊤ := by
    rw [hx, hx0, Submodule.colon_singleton_zero]
    exact Ideal.radical_top _
  exact hprime.ne_top htop

/-- (ii) at grade level, proved: the grade of `M` w.r.t. an associated prime
is zero. Every positive-length witness sequence would have a regular head in
`P`, against the core lemma; hence `GradeSet ⊆ {0}` and the `sSup` is `0`. -/
theorem grade_eq_zero_of_mem_associatedPrimes
    {P : Ideal R} (hP : P ∈ associatedPrimes R M) :
    grade R M P = 0 := by
  apply le_antisymm _ zero_le
  refine sSup_le ?_
  rintro _ ⟨n, hnmem, rfl⟩
  obtain ⟨rs, hlen, hmem, hreg⟩ := hnmem
  by_cases hn0 : n = 0
  · subst hn0
    simp
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    have hne : rs ≠ [] := by
      intro hcon
      subst hcon
      simp at hlen
    obtain ⟨y, tl, rfl⟩ := List.exists_cons_of_ne_nil hne
    have hyP : y ∈ P := hmem y List.mem_cons_self
    have hregy : IsSMulRegular M y :=
      ((isRegular_cons_iff M y tl).mp hreg).1
    exact absurd hregy (not_isSMulRegular_of_mem_associatedPrimes hP hyP)

/-- (ii) in local form, proved: nothing in the maximal ideal of `R_P` is
regular on the localized module. Routes the core lemma through
`mem_associatedPrimes_atPrime_of_mem_associatedPrimes`
(`Ideal/AssociatedPrime/Localization.lean`). This is the exact shape the
depth side of the bridge consumes. -/
theorem no_smulRegular_of_ass_localized_maximal
    {P : Ideal R} [P.IsPrime] (hP : P ∈ associatedPrimes R M) :
    ∀ y ∈ IsLocalRing.maximalIdeal (Localization.AtPrime P),
      ¬ IsSMulRegular (LocalizedModule.AtPrime P M) y := by
  intro y hy
  have hA := Module.associatedPrimes.mem_associatedPrimes_atPrime_of_mem_associatedPrimes hP
  exact not_isSMulRegular_of_mem_associatedPrimes hA hy

/-- Iterated grade drop along a successive family (bridge input address):
every prime containing `Ideal.span (Set.range q)` carries local grade at
least `k`. Supplying this needs (i)×`k` (the proved iterated equation
`grade_quotIter_add_eq_grade` applied to `List.ofFn` of the localized family)
plus localization-stability of regularity
(`RegularSequenceDimDrop.successiveSMulRegular_map_atPrime` gives the localized
successive data; turning it into `IsRegular` lists goes through
`RegularityBridge.isRegular_ofFn_of_successive` + properness from `J ≤ P ≠ ⊤`).
closed by `gradeDropChain_of_successive` below (via
`le_grade_atPrime_of_span_of_successive`).

The containment hypothesis `hJP` is essential and must never be dropped:
the unconditioned `∀ P` version is false. Counterexample: at
`P = ⊥` (prime in the domain `MvPolynomial (Fin m) K`) the localization is
the fraction field, the maximal ideal is `⊥`, and grade w.r.t. `⊥` is `0`
(any positive-length witness would need `IsSMulRegular` of `0`), so
`(k : ℕ∞) ≤ grade` fails for `k ≥ 1`. -/
def GradeDropChain {k : ℕ} (m : ℕ) (K : Type*) [Field K]
    (q : Fin k → MvPolynomial (Fin m) K)
    (_hsucc : RegularityBridge.SuccessiveSMulRegular q) : Prop :=
  ∀ (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime],
    Ideal.span (Set.range q) ≤ P →
    (k : ℕ∞) ≤ grade (Localization.AtPrime P) (Localization.AtPrime P)
      (IsLocalRing.maximalIdeal (Localization.AtPrime P))

/-- Deep-core address (iii): grade of the localization at `P` w.r.t. its
maximal ideal equals its Krull dimension. See the ledger for the careful
scoping (Koszul/AB or a direct maximal-sequence induction). -/
def DepthEqDimAt (m : ℕ) (K : Type*) [Field K]
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime] : Prop :=
  ((grade (Localization.AtPrime P) (Localization.AtPrime P)
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) : ℕ∞) :
      WithBot ℕ∞) =
    ringKrullDim (Localization.AtPrime P)

/-- Bridge implication (SPEC address): the iterated drop plus depth = dim at
every associated prime supply the true residual `HeightDropResidualAt`
(`P.height ≤ k` for Ass primes).

Proof skeleton (not formalized — this is the SPEC): localize at
`P ∈ Ass(R ⧸ J)`; `GradeDropChain` gives local grade `≥ k`;
`DepthEqDimAt` turns this into `dim (R_P) ≥ k`... but that is the lower
bound, already proved. The upper bound needs one more step: `M_P = R_P ⧸ J_P`
has depth `0` (proved local (ii) above), and in the CM local ring `R_P`
(depth = dim by (iii)) the length-`k` regular sequence generating `J_P`
forces `dim M_P = 0` (quotient-of-CM-by-regular + CM-implies-unmixed at the
specific rings — the CM content of `CohenMacaulayFragment`, also residual). Then
`HeightDrop.localized_dim_zero_of_height_le` read backwards through
`AssHeightBound.height_eq_add_of_span` gives `P.height ≤ k`. -/
def GradeUnmixedBridge {k : ℕ} (m : ℕ) (K : Type*) [Field K]
    (q : Fin k → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q)) : Prop :=
  GradeDropChain m K q hsucc →
    (∀ (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime],
      P ∈ associatedPrimes _ (_ ⧸ J) → DepthEqDimAt m K P) →
    HeightDrop.HeightDropResidualAt m K q hsucc J hJ

/-- Assembly, proved conditionally: Ass + grade bridge inputs imply
minimality over `J`, via `HeightDrop.minimal_of_height_le` (which routes
through `mem_minimalPrimes_of_localized_quotient_dim_zero`,
`Regularity/Unmixed/Unmixedness.lean`). Nothing here touches the disproved catenary
bridge. -/
theorem unmixed_of_grade_of_depthEq {k : ℕ} (m : ℕ) (K : Type*) [Field K]
    (q : Fin k → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K)) (hJ : J = Ideal.span (Set.range q))
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (hP : P ∈ associatedPrimes _ (_ ⧸ J))
    (hbridge : GradeUnmixedBridge m K q hsucc J hJ)
    (hchain : GradeDropChain m K q hsucc)
    (hdepth : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) → DepthEqDimAt m K Q) :
    P ∈ J.minimalPrimes :=
  HeightDrop.minimal_of_height_le m K q hsucc J hJ P hP ((hbridge hchain hdepth) P hP)

/-- Localization-stability grade bound (L1 GradeDropChain remainder, closed in
conditional form): at a prime `P` containing `J = span (Set.range q)`, local
grade is at least `k`.

Proof: `RegularSequenceDimDrop.successiveSMulRegular_map_atPrime` localizes the
successive data (no hypothesis on `P` needed); `J ≤ P` puts every localized
generator in the maximal ideal
(`IsLocalization.AtPrime.to_map_mem_maximal_iff`), which yields properness
(`ofList • ⊤ ≤ maximalIdeal < ⊤`, mirroring `RegularSequenceDimDrop`) and hence
`IsRegular` via `RegularityBridge.isRegular_ofFn_of_successive`; the length-`k` list
is then a `GradeSet` witness (`List.length_ofFn`), and
`le_grade_of_mem_gradeSet` reads off `(k : ℕ∞) ≤ grade`. The proved drop
equations (`grade_quotSMulTop_add_one_eq_grade`,
`grade_quotIter_add_eq_grade`) are not needed for this lower bound — a direct
witness suffices; they serve the upper/equality direction.

Sharpness: `hJP` is essential — `GradeDropChain` as stated (`∀ P`, no `J ≤ P`)
is false: at `P = ⊥` (prime in the domain `MvPolynomial (Fin m) K`) the
localization is the fraction field, the maximal ideal is `⊥`, and grade
w.r.t. `⊥` is `0` (any positive-length witness would need `IsSMulRegular` of
`0`), so `(k : ℕ∞) ≤ grade` fails for `k ≥ 1`. `GradeDropChain` proper is now
closed with the `hJP` hypothesis in the definition (`gradeDropChain_of_successive`). -/
theorem le_grade_atPrime_of_span_of_successive {k : ℕ} (m : ℕ) (K : Type*) [Field K]
    (q : Fin k → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (hJP : Ideal.span (Set.range q) ≤ P) :
    (k : ℕ∞) ≤ grade (Localization.AtPrime P) (Localization.AtPrime P)
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) := by
  have hsuccS := RegularSequenceDimDrop.successiveSMulRegular_map_atPrime (P := P)
    (Localization.AtPrime P) q hsucc
  have hmem : ∀ i, algebraMap (MvPolynomial (Fin m) K) (Localization.AtPrime P) (q i)
      ∈ IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
    intro i
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P]
    exact hJP (Ideal.subset_span (Set.mem_range_self i))
  have hle : Ideal.ofList (List.ofFn
        (algebraMap (MvPolynomial (Fin m) K) (Localization.AtPrime P) ∘ q)) •
        (⊤ : Submodule (Localization.AtPrime P) (Localization.AtPrime P))
      ≤ ((IsLocalRing.maximalIdeal (Localization.AtPrime P) :
        Ideal (Localization.AtPrime P)) :
        Submodule (Localization.AtPrime P) (Localization.AtPrime P)) := by
    rw [← RegularityBridge.span_range_eq_ofList_ofFn, RegularSequenceDimDrop.span_smul_top]
    exact_mod_cast Ideal.span_le.mpr (Set.range_subset_iff.mpr hmem)
  have hproperS : (⊤ : Submodule (Localization.AtPrime P) (Localization.AtPrime P))
      ≠ Ideal.ofList (List.ofFn
        (algebraMap (MvPolynomial (Fin m) K) (Localization.AtPrime P) ∘ q)) • ⊤ := by
    intro hcon
    have hmem1 : (1 : Localization.AtPrime P)
        ∈ Ideal.ofList (List.ofFn
          (algebraMap (MvPolynomial (Fin m) K) (Localization.AtPrime P) ∘ q)) •
          (⊤ : Submodule (Localization.AtPrime P) (Localization.AtPrime P)) := by
      rw [← hcon]
      exact Submodule.mem_top
    have h1mem : (1 : Localization.AtPrime P)
        ∈ IsLocalRing.maximalIdeal (Localization.AtPrime P) := hle hmem1
    have htop : IsLocalRing.maximalIdeal (Localization.AtPrime P) = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ h1mem isUnit_one
    exact Ideal.IsMaximal.ne_top inferInstance htop
  have hregS := RegularityBridge.isRegular_ofFn_of_successive _ hsuccS hproperS
  have hlen : (List.ofFn
      (algebraMap (MvPolynomial (Fin m) K) (Localization.AtPrime P) ∘ q)).length = k :=
    List.length_ofFn
  have hmemList : ∀ r ∈ List.ofFn
      (algebraMap (MvPolynomial (Fin m) K) (Localization.AtPrime P) ∘ q),
      r ∈ IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
    intro r hr
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
    exact hmem i
  have hwit : k ∈ GradeSet (Localization.AtPrime P) (Localization.AtPrime P)
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) :=
    mem_gradeSet_of_isRegular _ _ hlen hmemList hregS
  exact le_grade_of_mem_gradeSet _ hwit

/-- FiniteDimDischarge of the (fixed) `GradeDropChain`: the conditional
remainder `le_grade_atPrime_of_span_of_successive` is exactly the conditioned
statement, so the chain closes unconditionally from successive data. -/
theorem gradeDropChain_of_successive {k : ℕ} (m : ℕ) (K : Type*) [Field K]
    (q : Fin k → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q) :
    GradeDropChain m K q hsucc := by
  intro P _ hJP
  exact le_grade_atPrime_of_span_of_successive m K q hsucc P hJP

end GradeDepthFragment
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

/-!
# GapBase grade bridge: grade bounds feed regular-sequence existence (D4+D5)

Proves GapGradeSeq:
the sSup grade bridge (D4) and the `IsCM` unfold + casts (D5) feeding IschebeckAssembly
(L-ischebeck).

## Content

* D4 (`exists_isRegular_of_le_grade`): `↑n ≤ grade R M I` yields a regular
  sequence in `I` of length `≥ n`, by contradiction on the sSup: if every
  `m ∈ GradeSet` had `m < n`, the cast image would be bounded by `↑(n-1)`,
  forcing `grade ≤ ↑(n-1) < ↑n`. The surviving `m ≥ n` unpacks to the
  witness. `exists_isRegular_of_grade_eq_top` is the `⊤`-case corollary.
* D5 (`grade_ne_top_of_isCM_of_dim_lt_top`,
  `coe_grade_lt_top_of_isCM_of_dim_lt_top`, `natCast_le_grade_of_coe_le`):
  the unfolded-`IsCM` finiteness facts plus the downward `WithBot` cast
  feeder for D4.

## Interface deviation (forced, load-bearing)

Both D4 lemmas carry `[Nontrivial M]`, which the design note's exact shapes omit:
without it the main lemma is false. Counterexample: `M` trivial, `n = 0`.
Every `IsRegular M rs` is `False` (the `top_ne_smul` field fails since
`Submodule R M` is subsingleton), so `GradeSet = ∅` and
`grade = sSup ∅ = ⊥ = ↑(0 : ℕ)`; the hypothesis holds by `le_rfl` while the
conclusion is uninhabited. The `n = 0` witness `[]` needs
`IsRegular.nil`, which requires `[Nontrivial M]`. For `n ≥ 1` the design note
shape holds vacuously at trivial `M` (`↑n ≤ ⊥` is uninhabited), but the
uniform instance is the correct statement. Downstream (IschebeckAssembly): case-split on
`Nontrivial N`; at trivial `N` the `Ext`-vanishing goal closes directly
since the target module is zero.

## Dependencies and proof constraints

* Dependencies: `FirstReg`-downstream; GapBase (`AssociatedPrimes`) is the
  target, never a hypothesis. Proves all five conclusions; no `∀J'`-depth
  vehicle, no tower/E7/`halloc`, no `repDepth`/`quotExact`.
* Wall-2: sequence-existence only. D4 runs grade-as-supremum ⟹ existence
  (the definitional direction); D5 unfolds assumed `IsCM` and pushes
  `< ⊤` through a coercion. No `grade = height`, `grade = ringKrullDim`,
  or `length = height` content anywhere.
-/

namespace EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GapGradeSeq

open RingTheory.Sequence

/-- D4 grade bridge: a lower bound `↑n ≤ grade` yields an `M`-regular
sequence in `I` of length at least `n` (sSup contrapositive; no maximality,
no truncation — Rees takes any length). Needs `[Nontrivial M]`: at trivial
`M` and `n = 0` the statement is false (`GradeSet = ∅`, `grade = ⊥ = ↑0`
while no sequence is regular). -/
theorem exists_isRegular_of_le_grade {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Nontrivial M] (I : Ideal R) {n : ℕ}
    (h : (n : ℕ∞) ≤ GradeDepthFragment.grade R M I) :
    ∃ rs : List R, n ≤ rs.length ∧ (∀ r ∈ rs, r ∈ I) ∧ IsRegular M rs := by
  cases n with
  | zero =>
    refine ⟨[], Nat.zero_le _, by simp, ?_⟩
    exact IsRegular.nil R M
  | succ n =>
    by_contra hcon
    push Not at hcon
    have hbound : GradeDepthFragment.grade R M I ≤ (n : ℕ∞) := by
      unfold GradeDepthFragment.grade
      apply sSup_le
      rintro _ ⟨m, hm, rfl⟩
      obtain ⟨rs, hlen, hmem, hreg⟩ := hm
      have hlt : m < n + 1 := by
        by_contra hle
        push Not at hle
        rw [← hlen] at hle
        exact hcon rs hle hmem hreg
      have hmn : m ≤ n := Nat.lt_succ_iff.mp hlt
      exact_mod_cast hmn
    have hlt : (n : ℕ∞) < ((n + 1 : ℕ) : ℕ∞) := by
      exact_mod_cast Nat.lt_succ_self n
    have hle : n + 1 ≤ n := by
      have h' : (((n + 1 : ℕ)) : ℕ∞) ≤ (n : ℕ∞) := le_trans h hbound
      exact_mod_cast h'
    omega

/-- D4 `⊤`-case corollary: at `grade = ⊤`, regular sequences in `I` exist
of every length. This is what IschebeckAssembly calls when `k = grade = ⊤`. -/
theorem exists_isRegular_of_grade_eq_top {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Nontrivial M] (I : Ideal R)
    (h : GradeDepthFragment.grade R M I = ⊤) (n : ℕ) :
    ∃ rs : List R, n ≤ rs.length ∧ (∀ r ∈ rs, r ∈ I) ∧ IsRegular M rs :=
  exists_isRegular_of_le_grade I (by rw [h]; exact le_top)

/-- D5 finiteness (`ℕ∞`-level): from unfolded `IsCM` plus the finite-dim
fence, grade is finite. `IsCM` is the assumed hypothesis being unfolded
(GapBase assumes CM); no `grade = _` equation is proved. -/
theorem grade_ne_top_of_isCM_of_dim_lt_top (S : Type*) [CommRing S]
    [IsLocalRing S] [IsNoetherianRing S]
    (hCM : ((GradeDepthFragment.grade S S (IsLocalRing.maximalIdeal S) : ℕ∞) : WithBot ℕ∞)
      = ringKrullDim S)
    (hfin : ringKrullDim S < ⊤) :
    GradeDepthFragment.grade S S (IsLocalRing.maximalIdeal S) ≠ ⊤ := by
  intro hcon
  rw [← hCM, hcon, WithBot.coe_top] at hfin
  exact absurd hfin (lt_irrefl _)

/-- D5 finiteness (`WithBot`-level companion): the coerced grade is `< ⊤`. -/
theorem coe_grade_lt_top_of_isCM_of_dim_lt_top (S : Type*) [CommRing S]
    [IsLocalRing S] [IsNoetherianRing S]
    (hCM : ((GradeDepthFragment.grade S S (IsLocalRing.maximalIdeal S) : ℕ∞) : WithBot ℕ∞)
      = ringKrullDim S)
    (hfin : ringKrullDim S < ⊤) :
    ((GradeDepthFragment.grade S S (IsLocalRing.maximalIdeal S) : ℕ∞) : WithBot ℕ∞) < ⊤ := by
  rw [hCM]
  exact hfin

/-- D5 downward cast-feeder for D4: a `WithBot`-level lower bound on grade
descends to the `ℕ∞` level (`WithBot.coe_le_coe`). -/
theorem natCast_le_grade_of_coe_le {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (I : Ideal R) {n : ℕ}
    (h : (((n : ℕ∞)) : WithBot ℕ∞) ≤ ((GradeDepthFragment.grade R M I : ℕ∞) : WithBot ℕ∞)) :
    (n : ℕ∞) ≤ GradeDepthFragment.grade R M I :=
  WithBot.coe_le_coe.mp h

end EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GapGradeSeq
