/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.Unmixed.Unmixedness
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.AssHeightBound
import Appendix_FixedPoint.BezoutChain.Dimension.LocalUnmixed
import Appendix_FixedPoint.BezoutChain.Dimension.RegularSequenceDimDrop
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Data.ENat.Monoid
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.KrullDimension.LocalRing
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Cohen–Macaulay fragment for unmixedness at `k ≥ 2`

For `R = MvPolynomial (Fin m) K` (`[Field K]`), `q : Fin k → R` carrying
successive SMul-regularity data (`RegularityBridge.SuccessiveSMulRegular`), and
`J = Ideal.span (Set.range q)`, the frozen downstream contract is:

```
theorem unmixed_of_successive_regular (m k: ℕ) (K: Type*) [Field K]
    (q: Fin k → MvPolynomial (Fin m) K)
    (hsucc: RegularityBridge.SuccessiveSMulRegular q)
    (J: Ideal (MvPolynomial (Fin m) K))
    (hJ: J = Ideal.span (Set.range q))
    (P: Ideal (MvPolynomial (Fin m) K))
    (hP: P ∈ associatedPrimes _ (_ ⧸ J)):
    P ∈ J.minimalPrimes
```

`k = 0` and `k = 1` are proved in `Regularity/Unmixed/Unmixedness.lean`
(`mem_minimalPrimes_of_successive_zero`,
`mem_minimalPrimes_of_successive_singleton`); the conditional endgame
(`mem_minimalPrimes_of_localized_quotient_dim_zero`: localized dimension zero
implies minimality) is also proved there. This file is the first
theory-building step toward goal (b) — proving unmixedness for `k ≥ 2` —
and its most valuable result is the SPEC below, which stands even if all
proofs stall.

## SPEC (minimal fragment sufficient to close `k ≥ 2`)

Definitions (this file, `namespace EvolutionAlgebras.Appendix_FixedPoint.BezoutChain`):

* `IsHunmixed R J : Prop` — the target predicate: every `P ∈ Ass(R ⧸ J)` is
  minimal over `J`. This is exactly the frozen conclusion, repackaged so the
  induction-step statement can be written without CM vocabulary.
* `HasUniqueIrreducible R : Prop` — the U1 residual predicate: `(∃ p,
  Irreducible p) ∧ ∀ ⦃p q⦄, Irreducible p → Irreducible q → Associated p q`,
  i.e. precisely the hypothesis pair of
  `IsDiscreteValuationRing.of_ufd_of_unique_irreducible`.
* `U2DimZeroInput m K q P : Prop` — the U2 residual predicate: the localized
  dimension-zero equation `ringKrullDim (R_P ⧸ J_P) = 0` for the `k = 2` case,
  named so the roadblock has a formal address.
* `RegularQuotientPreservesHunmixed R J x : Prop` — the minimal CM-like
  induction-step statement: `IsHunmixed R J → IsHunmixed (R ⧸ J) (span {x})`.
  No general CM theory is formalized; this is only as much as `k ≥ 3` demands
  (quotient-of-CM-by-regular + CM-implies-unmixed for the specific rings
  involved, with the content left as the documented residual).

Theorem statements (proofs are thin wrappers or applications):

* `dvr_of_ufd_of_unique_irreducible` — U1 last step, proved.
* `u1_dvr_at_height_one_of_unique` — U1 shape at a height-1 prime `Q`,
  conditional on `HasUniqueIrreducible (Localization.AtPrime Q)`, proved
  conditionally (the discharged U1 residual).
* `hasUniqueIrreducible_atPrime_height_one` — U1 itself, proved: the
  height-1 localization has unique irreducibles.
* `u1_dvr_at_height_one` — U1 discharge, proved: the height-1 localization
  is a DVR unconditionally.
* `unmixed_two_of_u2` — `k = 2` assembly: U2 input implies minimality,
  proved conditionally (the hypothesis is the U2 residual).
* `exists_height_one_minimal_le_of_successive_pair` — U2 step (i), proved:
  height-1 `Q ≤ P` minimal over the first generator, assembled in-tree.
* `dvr_at_height_one_le_of_successive_pair` — U2 step (ii), proved: one-line
  apply of `u1_dvr_at_height_one`.
* `ringKrullDim_quotient_span_le_zero_of_dvr` +
  `dim_dvr_quotient_le_zero_of_successive_pair` — U2 step (iii), proved:
  DVR-quotient dim-drop, general plus applied to the `q₁`-image.
* `u2_dim_zero_of_height_le_two` — height reduction, proved: `P.height ≤ 2`
  implies `U2DimZeroInput`, so U2 step (iv) is exactly that inequality.
* `unmixed_of_cm_step` — CM-step application shape, proved conditionally
  (the hypothesis is the CM residual).
* `successiveSMulRegular_prefix` — Route-A prefix combinatorics, proved:
  every `Fin j` prefix (`prefixFun`) of a successive family is successive
  (pure `Fin`/previous-value-set combinatorics, proved from scratch).
* `PrefixDimZeroInput` — the HDimZeroPrefix-style residual predicate:
  per-prefix (`∀ j ≤ k`) localized dimension-zero inputs, the exact
  conditional hypothesis of the Route-A assembly.
* `unmixed_of_successive_regular_of_prefix_dim_zero` — Route-A assembly,
  proved conditionally: induction on `k` routing each step through
  `mem_minimalPrimes_of_localized_quotient_dim_zero`; `k = 0` closes
  unconditionally, every successor step via its full-length prefix input
  (identified with `q` by `prefixFun_full`).
* `unmixed_closed_zero` / `unmixed_closed_one` — `k ≤ 1` closed end-to-end
  (thin aliases of the proved zero/singleton lemmas).
* `unmixed_two_of_height_le_two_closed` — `k = 2` through the proved u2 chain
  (`u2_dim_zero_of_height_le_two` + `unmixed_two_of_u2`), conditional on
  exactly `P.height ≤ 2` (the `HeightDrop` residual).
* `unmixed_two_of_catenary_upper` — `k = 2` endgame, proved conditionally on
  exactly the catenary-upper bridge `CatenaryUpperInput` (at height-1 primes
  below `P`: `P.height ≤ Q.height + dim R_Q`); `height_le_two_of_catenary_upper`
  turns the bridge at step-(i)'s `Q` into `P.height ≤ 2`. Route tag
  `k2-of-catenary-upper`.
* `height_le_prefix_staircase` — proved lower-bound staircase
  (`(j : ℕ∞) ≤ P.height` for all `j ≤ k`), genuine consumer of the prefix
  lemma; the per-prefix upper half is not attempted (owned by the `HeightDrop` work).
* `prefixDimZeroInput_restrict` — prefix inputs restrict to prefixes
  (prefix-of-prefix is a prefix), so induction levels thread.

Attempt order: (i) U1; (ii) U2; (iii) CM-lite only as far as `k ≥ 3`
demands.

## Mathlib-gap analysis (Mathlib v4.34.0; all `grep` run in
`.lake/packages/mathlib`, `lean-toolchain` pins `v4.34.0`)

exists (module + name):

* `IsDiscreteValuationRing.of_ufd_of_unique_irreducible` —
  `Mathlib/RingTheory/DiscreteValuationRing/Basic.lean` (~line 270, inside
  `namespace IsDiscreteValuationRing`, lines 62–646). Direction: UFD +
  unique-irreducible ⟹ DVR (used by `dvr_of_ufd_of_unique_irreducible`).
* `UniqueFactorizationMonoid (Localization S)` instance —
  `Mathlib/GroupTheory/MonoidLocalization/UniqueFactorization.lean`, plus
  `UniqueFactorizationMonoid.of_isLocalization`. The UFD half of U1 is therefore
  free in principle; what remains is the unique-irreducible half (U1).
* `IsDomain (Localization.AtPrime P)` —
  `Mathlib/RingTheory/Localization/AtPrime/Basic.lean`. The domain half of
  U1 is free.
* `IsPrincipalIdealRing.ringKrullDim_eq_one` (line 37) and
  `IsPrincipalIdealRing.height_eq_one_of_isMaximal` (line 47) —
  `Mathlib/RingTheory/KrullDimension/PID.lean` (earmarked for the U1
  argument).
* `MvPolynomial.uniqueFactorizationMonoid` —
  `Mathlib/RingTheory/Polynomial/UniqueFactorization.lean` (UFD base for `R`).
* `exists_integral_inj_algHom_of_quotient` —
  `Mathlib/RingTheory/NoetherNormalization.lean` (normalization exists for
  global quotients `R ⧸ P`; cf. the U2 gap: nothing for `R_P ⧸ J_P`).

absent (with evidence):

* No Cohen–Macaulay API: `grep -rn "CohenMacaulay" Mathlib/ --include="*.lean"
  | wc -l` ⟹ `0`.
* No unmixed API: `grep -rln "IsUnmixed" Mathlib/ --include="*.lean"` hits only
  `Mathlib/NumberTheory/NumberField/InfinitePlace/Embeddings.lean` (and
  `Ramification.lean`), i.e. `ComplexEmbedding.IsUnmixed` about number fields,
  unrelated.
* No UFD-to-DVR bridge file: `grep -rn "IsDiscreteValuationRing"
  Mathlib/RingTheory/UniqueFactorizationDomain/ --include="*.lean" | wc -l`
  ⟹ `0`.
* DVR-localization results are Dedekind-only:
  `Mathlib/RingTheory/DedekindDomain/Dvr.lean,131`,
  `Mathlib/RingTheory/DedekindDomain/PID.lean`,
  `Mathlib/RingTheory/Unramified/Dedekind.lean`. `MvPolynomial (Fin m) K`
  with `m ≥ 2` is not Dedekind, so none applies at a height-1 prime `Q`.
* No AtPrime-height-1 specialization: `grep -rn
  "UniqueFactorizationMonoid (Localization" Mathlib/` hits only the general
  monoid-localization instance above and the principal case
  `Mathlib/RingTheory/Ideal/UFD.lean`
  (`UniqueFactorizationMonoid (Localization.Away x)`).
* No grade API: `Mathlib/RingTheory/Depth/` holds only the Rees theorem
  (`ModuleCat.exists_isRegular_tfae`); regular sequences exist
  (`RingTheory.Sequence.IsRegular` in
  `Mathlib/RingTheory/Regular/RegularSequence.lean`) but no grade/depth-to-CM
  ladder.
* U2 normalization gap in-tree: `grep -rn "AtPrime"
  Formalization/Appendix_FixedPoint/BezoutChain/Dimension/TriangularChain.lean`
  is empty (those
  files normalize only global quotients `R ⧸ P` via `quotient_dim_of_normap`),
  and `grep -rn "→ₐ.*Localization.AtPrime" Formalization/` is empty: no
  normalization map for `R_P ⧸ J_P` is constructed anywhere.

## roadblock ledger (first-class result)

* U1 (blocks `u1_dvr_at_height_one_of_unique`, hypothesis `h`): wanted
  `∀ (Q: Ideal (MvPolynomial (Fin m) K)), Q.IsPrime → Q.height = 1 →
    HasUniqueIrreducible (Localization.AtPrime Q)`. The UFD and domain
  instances are free (see exists); the unique-irreducible half has no Mathlib
  API (see absent: UFD dir has zero `IsDiscreteValuationRing` hits; only
  Dedekind localization exists). Stop here per sub-piece: do not build ega
  from scratch. Cost to close: one lemma — irreducibles of a height-1
  localization of a Noetherian UFD are all associate (equivalently, the maximal
  ideal of `Localization.AtPrime Q` is principal generated by any prime
  element residual).
  proved: `hasUniqueIrreducible_atPrime_height_one` proves exactly
  the wanted statement, via `IsLocalization.AtPrime.ringKrullDim_eq_height`
  (`Mathlib/RingTheory/Ideal/Height.lean`) plus
  `ringKrullDim_eq_one_iff_of_isLocalRing_isDomain`
  (`Mathlib/RingTheory/KrullDimension/LocalRing.lean`); `u1_dvr_at_height_one`
  feeds it into `u1_dvr_at_height_one_of_unique`, discharging `h`. Both check
  cleanly with axioms exactly `propext / Classical.choice / Quot.sound`.
* U2 (blocks `unmixed_two_of_u2`, hypothesis `hu2`): wanted — from the DVR
  at a height-1 prime `Q ≤ P` minimal over the first generator plus the
  pushed-forward image data, produce `U2DimZeroInput m K q P`, i.e.
  `ringKrullDim (R_P ⧸ J_P) = 0`. Needs the normalization map for `R_P ⧸ J_P`
  plus going-up bookkeeping; that map is not constructed in-tree (see absent:
  U2 gap). Stop here: scoped to SPEC + U1 attempt first; U2 work starts
  only once U1 proves or is precisely mapped (it now is: U1 proved above).
  Recon (bounded, no-spiral): the residual refines to
  four steps — (i) height-1 `Q ≤ P` minimal over the first generator
  (assemblable: in-tree Krull
  `height_le_card_of_mem_minimalPrimes_span_finset` + nonzero from regularity);
  (ii) DVR at `Q` (proved above); (iii) dim-drop in the DVR quotient (likely
  via `ringKrullDim_quotient_succ_le_of_nonZeroDivisor`, exact statement and
  side-conditions unverified); (iv) transfer to `R_P ⧸ J_P` (blocked:
  no `R_P ⧸ J_P ≃` further-localization construction in-tree —
  `TriangularChain` has zero `AtPrime` lines, reverified —
  and no quotient-localization or dim-monotonicity bridge found under
  `Mathlib/RingTheory/Localization/`). Step (iv) is the precise residual.
  Per steps (i)–(iv): (i) proved as
  `exists_height_one_minimal_le_of_successive_pair` (assembled in-tree, no
  reproof: `Ideal.exists_minimalPrimes_le` at `(q₀) ≤ J ≤ P` plus
  `AssHeightBound.height_le_of_mem_minimalPrimes` /
  `le_height_of_span_of_successive` at the extracted `Fin 1` family
  `singleton_successive_of_successive_pair`; nonzero helpers
  `fst/snd_ne_zero_of_successive_pair` mirror `Unmixedness.lean`). (ii) proved
  as `dvr_at_height_one_le_of_successive_pair` (one-line apply of
  `u1_dvr_at_height_one`; UFD/domain instances are the free SPEC ones).
  (iii) proved as `ringKrullDim_quotient_span_le_zero_of_dvr` (general DVR
  drop; the named lemma is now verified:
  `Mathlib/RingTheory/KrullDimension/NonZeroDivisors.lean`,
  `{r : R} (hr : r ∈ R⁰) ⊢ dim (R ⧸ span {r}) + 1 ≤ dim R`, cancelled by
  `IsPrincipalIdealRing.ringKrullDim_eq_one` through
  `ENat.WithBot.add_le_add_one_right_iff`) plus the applied
  `dim_dvr_quotient_le_zero_of_successive_pair` (the `q₁`-image in `R_Q` is
  nonzero via `IsLocalization.injective` on the domain). Height reduction
  proved as `u2_dim_zero_of_height_le_two`: the in-tree equation
  `AssHeightBound.height_eq_add_of_span` (`↑height P = dim (R_P ⧸ J_P) + 2`)
  plus the in-tree lower bound reduce `U2DimZeroInput` to `P.height ≤ 2`.
  (iv) blocked with exact residual `P.height ≤ 2` (upper height bound for an
  Ass prime over a length-2 regular sequence), grep evidence: `grep -rn
  ringKrullDim Mathlib/RingTheory/Localization/` is empty (no
  quotient-localization or dim-monotonicity bridge there); the only nearby iso
  (`IsLocalization.AtPrime.equivQuotientMapOfIsMaximal`,
  `Localization/AtPrime/Extension.lean`) needs `P` maximal above `p`
  (residue-field case — inapplicable since `J_P` maximal is the goal); the
  only available dim-drop direction (`ringKrullDim_le_of_surjective`,
  `KrullDimension/Basic.lean`) runs `R_P ⧸ J_P → R_Q ⧸ J_Q` (localization
  maps go from bigger to smaller primes), i.e. against the needed bound —
  indeed `Spec (R_Q ⧸ J_Q) ↪ Spec (R_P ⧸ J_P)`, so pure monotonicity can never
  transfer a zero from the DVR side. In-tree Ass API is lower-bounds-only and
  Krull upper bounds need `minimalPrimes`. The missing content is the
  regular-element height-drop in the non-UFD quotient `R ⧸ (q₀)` (cf.
  `Unmixedness.lean`), i.e. grade/Koszul content (grade API absent per
  SPEC). `U2DimZeroInput` production is therefore exactly one inequality away
  from closing; no localization theory was built from scratch.
  DVR-route verdict (links (1)–(4)): (1) ✓
  step (i) proved and verified; (2) ✓ step (ii) proved and verified; (3) ✗ —
  the inequality `P.height ≤ Q.height + dim R_Q` for `Q ≤ P` is false in
  general (counterexample: `MvPolynomial (Fin 3) K`, `Q = (x)` of height 1,
  `P = (x, y, z)` of height 3: `3 ≰ 1 + 1`) and absent from Mathlib
  (case-insensitive `catenary` grep over Mathlib: zero hits). Nearest true
  lemmas surveyed and rejected:
  `Ideal.height_le_height_add_of_liesOver`
  (`KrullsHeightTheorem.lean`) carries a fiber term that trivializes for
  localizations (primes of `R_Q` lie over primes `≤ Q`, never above `Q`), and
  `Ideal.height_le_height_add_one_of_mem` (`KrullsHeightTheorem.lean`)
  applied twice (`q₀`, then `q₁`) reduces to `P.height ≤ ht (P-image) + 2`
  where the fiber vanishes iff `P` is minimal over `J` — the goal itself.
  The DVR data therefore cannot bound `P.height`; no hunt for link (3) as
  stated can succeed (it conflates the DVR's dimension with the catenary
  fiber). (4) ✓ the `u2` chain is intact. Fallback:
  `CatenaryUpperInput` (the exact missing statement as a named `Prop`) +
  `height_le_two_of_catenary_upper` + `unmixed_two_of_catenary_upper`, so the
  `k = 2` residual is exactly one named bridge; the true residual remains
  `P.height ≤ 2` (the `HeightDrop` work), which this conditional discharges
  from the bridge.
* CM (blocks `unmixed_of_cm_step`, hypothesis `hstep`): wanted —
  `RegularQuotientPreservesHunmixed R J x` for the specific successive
  quotients `R = MvPolynomial`, `J = span` of an initial segment, `x` the next
  regular generator (quotient-of-CM-by-regular + CM-implies-unmixed at those
  rings only; general CM theory explicitly out of scope). Blocked on the absent
  CM/unmixed/grade API above. `k ≥ 3` work starts only after U1 proves.

Nearest closable milestone: `k = 2`, costing exactly U1 + U2. `k ≥ 3`
additionally costs CM. Nothing in this file claims more.

Route-A update, O-strategy, no CM vocabulary): `k ≥ 3` is
additionally conditional on exactly the per-prefix height-drop residual whose
formal address is `HeightDrop.HeightDropResidualAt` (∀ `P ∈ Ass`, `P.height ≤
k` at each prefix length; upper-bound proofs live elsewhere — nothing in
this file attempts them). Delivered: `successiveSMulRegular_prefix` proved
from scratch (no content copied); the assembly
`unmixed_of_successive_regular_of_prefix_dim_zero` proved conditionally on
`PrefixDimZeroInput` (per-prefix `∀ j ≤ k` dim-zero); `k = 0,1` closed
(`unmixed_closed_zero/one`); `k = 2` through the proved u2 chain
(`unmixed_two_of_height_le_two_closed`) conditional on exactly `P.height ≤ 2`.
The `k ≥ 3` endgame is therefore one named residual away from closing, with
no CM content anywhere on the route.

## References

Project (read-only; never edited here):

* `Regularity/Unmixed/Unmixedness.lean` (bare `BezoutChain` namespace):
  `mem_minimalPrimes_of_successive_zero`,
  `mem_minimalPrimes_of_successive_singleton`,
  `assPrime_quotient_dim_eq_normalization_index`,
  `mem_minimalPrimes_of_localized_quotient_dim_zero` (consumed by
  `unmixed_two_of_u2`).
* `Regularity/Avoid/AssHeightBound.lean`: `height_eq_add_of_span`,
  `le_height_of_span_of_successive`, `height_le_of_mem_minimalPrimes`,
  `le_height_of_mem_associatedPrimes_of_successive` (all four consumed in this file).
* `Dimension/LocalUnmixed.lean`: `assPrime_contains_span`.
* `Dimension/RegularSequenceDimDrop.lean`: `span_smul_top` (empty-previous-value
  rewrites used here).
* `Regularity/Avoid/RegularityBridge.lean`: `RegularityBridge.SuccessiveSMulRegular`.
* `Regularity/Unmixed/HeightDrop.lean` (read-only; maintained elsewhere — never edited here):
  `HeightDrop.HeightDropResidualAt` (the exact per-prefix
  height-drop residual address consumed by the Route-A assembly),
  `HeightDrop.localized_dim_zero_of_height_le`,
  `HeightDrop.minimal_of_height_le`, `HeightDrop.unmixed_of_heightDrop`,
  `HeightDrop.assHeight_le_zero_of_successive_zero`,
  `HeightDrop.assHeight_le_one_of_successive_singleton`.

Mathlib: see the exists list above, plus (all grep-verified):
`RingTheory/KrullDimension/NonZeroDivisors.lean`
(`ringKrullDim_quotient_succ_le_of_nonZeroDivisor`),
`RingTheory/KrullDimension/PID.lean`
  (`IsPrincipalIdealRing.ringKrullDim_eq_one`), `Data/ENat/Monoid.lean`
  (`ENat.WithBot.add_le_add_one_right_iff`),
  `RingTheory/Ideal/KrullsHeightTheorem.lean,450`
  (`Ideal.height_le_height_add_one_of_mem`,
  `Ideal.height_le_height_add_of_liesOver` — surveyed for link (3),
  inapplicable as recorded in the ledger).
-/

open scoped nonZeroDivisors

namespace EvolutionAlgebras.Appendix_FixedPoint.BezoutChain

/-- Hunmixed target predicate: every associated prime of `R ⧸ J` is minimal
over `J`. This is the frozen `unmixed_of_successive_regular` conclusion,
repackaged so the CM induction step can be stated without CM vocabulary. -/
def IsHunmixed (R : Type*) [CommRing R] (J : Ideal R) : Prop :=
  ∀ P ∈ associatedPrimes R (R ⧸ J), P ∈ J.minimalPrimes

/-- U1 residual predicate: existence of an irreducible plus uniqueness up to
associates — exactly the hypothesis pair of
`IsDiscreteValuationRing.of_ufd_of_unique_irreducible`. -/
def HasUniqueIrreducible (R : Type*) [CommRing R] : Prop :=
  (∃ p : R, Irreducible p) ∧
    ∀ ⦃p q : R⦄, Irreducible p → Irreducible q → Associated p q

/-- U1 last step, proved: a domain UFD with a unique irreducible (up to
associates) is a DVR, via
`IsDiscreteValuationRing.of_ufd_of_unique_irreducible`
(`Mathlib/RingTheory/DiscreteValuationRing/Basic.lean`). -/
theorem dvr_of_ufd_of_unique_irreducible {D : Type*} [CommRing D] [IsDomain D]
    [UniqueFactorizationMonoid D] (h : HasUniqueIrreducible D) :
    IsDiscreteValuationRing D :=
  IsDiscreteValuationRing.of_ufd_of_unique_irreducible h.1 h.2

/-- U1 shape at a height-1 prime, conditional: once the localization carries
a UFD + domain structure (both free in principle — see SPEC exists) and the
U1 residual `h`, it is a DVR. The height hypothesis `_hht` records where
this instantiates (a height-1 prime `Q`, e.g. minimal over the first
generator); the proof uses only the free instances plus `h`. -/
theorem u1_dvr_at_height_one_of_unique (m : ℕ) (K : Type*) [Field K]
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (_hht : Q.height = 1)
    [UniqueFactorizationMonoid (Localization.AtPrime Q)]
    (h : HasUniqueIrreducible (Localization.AtPrime Q)) :
    IsDiscreteValuationRing (Localization.AtPrime Q) :=
  dvr_of_ufd_of_unique_irreducible h

/-- U1, proved: at a height-1 prime `Q` the localization has unique irreducibles.

Proof idea: `IsLocalization.AtPrime.ringKrullDim_eq_height` with `hht` gives
`ringKrullDim (Localization.AtPrime Q) = 1`; then
`ringKrullDim_eq_one_iff_of_isLocalRing_isDomain` says every nonzero element's
principal ideal has radical containing the maximal ideal. For irreducible `a`,
`span {a}` is prime (UFD: irreducible ⟺ prime, via
`Ideal.isPrime_span_singleton_of_prime`), hence radical, hence equal to the
maximal ideal; so any two irreducibles generate the same ideal and are
associated (`Ideal.span_singleton_eq_span_singleton`). Existence comes from
`maximalIdeal ≠ ⊥` (else a field, against dimension one) factored via
`WfDvdMonoid.exists_irreducible_factor`. -/
theorem hasUniqueIrreducible_atPrime_height_one (m : ℕ) (K : Type*) [Field K]
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hht : Q.height = 1)
    [UniqueFactorizationMonoid (Localization.AtPrime Q)] :
    HasUniqueIrreducible (Localization.AtPrime Q) := by
  have hdim : ringKrullDim (Localization.AtPrime Q) = 1 := by
    have h := IsLocalization.AtPrime.ringKrullDim_eq_height Q (Localization.AtPrime Q)
    rw [hht] at h
    simpa using h
  obtain ⟨hnfield, hrad⟩ := ringKrullDim_eq_one_iff_of_isLocalRing_isDomain.mp hdim
  have hmax_ne : IsLocalRing.maximalIdeal (Localization.AtPrime Q) ≠ ⊥ := by
    intro hcon
    exact hnfield (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hcon)
  obtain ⟨x, hxmem, hx0⟩ := (Submodule.ne_bot_iff _).mp hmax_ne
  have hxnu : ¬ IsUnit x :=
    fun hu => IsLocalRing.notMem_maximalIdeal.mpr hu hxmem
  obtain ⟨p, hp_irr, _⟩ := WfDvdMonoid.exists_irreducible_factor hxnu hx0
  refine ⟨⟨p, hp_irr⟩, fun {a b} ha hb => ?_⟩
  have hpa : (Ideal.span ({a} : Set (Localization.AtPrime Q))).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime
      ((UniqueFactorizationMonoid.irreducible_iff_prime).mp ha)
  have hpb : (Ideal.span ({b} : Set (Localization.AtPrime Q))).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime
      ((UniqueFactorizationMonoid.irreducible_iff_prime).mp hb)
  have hamem : a ∈ IsLocalRing.maximalIdeal (Localization.AtPrime Q) :=
    (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr ha.not_isUnit)
  have hbmem : b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime Q) :=
    (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hb.not_isUnit)
  have hle_a : Ideal.span ({a} : Set (Localization.AtPrime Q)) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime Q) :=
    (Ideal.span_singleton_le_iff_mem _).mpr hamem
  have hle_b : Ideal.span ({b} : Set (Localization.AtPrime Q)) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime Q) :=
    (Ideal.span_singleton_le_iff_mem _).mpr hbmem
  have hge_a : IsLocalRing.maximalIdeal (Localization.AtPrime Q) ≤
      Ideal.span ({a} : Set (Localization.AtPrime Q)) := by
    have h := hrad a ha.ne_zero
    rwa [hpa.isRadical.radical] at h
  have hge_b : IsLocalRing.maximalIdeal (Localization.AtPrime Q) ≤
      Ideal.span ({b} : Set (Localization.AtPrime Q)) := by
    have h := hrad b hb.ne_zero
    rwa [hpb.isRadical.radical] at h
  have hea : IsLocalRing.maximalIdeal (Localization.AtPrime Q) =
      Ideal.span ({a} : Set (Localization.AtPrime Q)) := le_antisymm hge_a hle_a
  have heb : IsLocalRing.maximalIdeal (Localization.AtPrime Q) =
      Ideal.span ({b} : Set (Localization.AtPrime Q)) := le_antisymm hge_b hle_b
  have heq : Ideal.span ({a} : Set (Localization.AtPrime Q)) =
      Ideal.span ({b} : Set (Localization.AtPrime Q)) := by
    rw [← hea, heb]
  exact (Ideal.span_singleton_eq_span_singleton).mp heq

/-- U1 discharge: the height-1 localization is a DVR unconditionally (the
residual `h` of `u1_dvr_at_height_one_of_unique` is supplied by
`hasUniqueIrreducible_atPrime_height_one`). -/
theorem u1_dvr_at_height_one (m : ℕ) (K : Type*) [Field K]
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hht : Q.height = 1)
    [UniqueFactorizationMonoid (Localization.AtPrime Q)] :
    IsDiscreteValuationRing (Localization.AtPrime Q) :=
  u1_dvr_at_height_one_of_unique m K Q hht
    (hasUniqueIrreducible_atPrime_height_one m K Q hht)

/-- U2 residual as a named predicate: the localized dimension-zero equation
for the `k = 2` case. Producing a proof of this from the DVR at a height-1
prime plus pushed-forward image data is the U2 roadblock. -/
def U2DimZeroInput (m : ℕ) (K : Type*) [Field K]
    (q : Fin 2 → MvPolynomial (Fin m) K)
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime] : Prop :=
  ringKrullDim (Localization.AtPrime P ⧸
    Ideal.span (Set.range (algebraMap (MvPolynomial (Fin m) K)
      (Localization.AtPrime P) ∘ q))) = 0

/-- `k = 2` assembly scaffolding, conditional: the U2 input implies minimality
over `J`, via `mem_minimalPrimes_of_localized_quotient_dim_zero`
(`Regularity/Unmixed/Unmixedness.lean`). U1 enters only as the (unverified) producer
of `hu2`, together with the missing normalization bookkeeping. -/
theorem unmixed_two_of_u2 (m : ℕ) (K : Type*) [Field K]
    (q : Fin 2 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K)) (hJ : J = Ideal.span (Set.range q))
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (hP : P ∈ associatedPrimes _ (_ ⧸ J))
    (hu2 : U2DimZeroInput m K q P) :
    P ∈ J.minimalPrimes := by
  have hdim : ringKrullDim (Localization.AtPrime P ⧸
      Ideal.span (Set.range (algebraMap (MvPolynomial (Fin m) K)
        (Localization.AtPrime P) ∘ q))) = 0 := hu2
  exact mem_minimalPrimes_of_localized_quotient_dim_zero m 2 K q hsucc J hJ P hP hdim

/-- U2 step (i), proved: the first generator alone is successive-regular
(as a `Fin 1` family), by restricting `hsucc` to index `0` (the previous-value
set is empty there). Mirrors the `hempty`/`hJ00` rewrite in
`mem_minimalPrimes_of_successive_singleton`
(`Regularity/Unmixed/Unmixedness.lean`). -/
theorem singleton_successive_of_successive_pair (m : ℕ) (K : Type*) [Field K]
    (q : Fin 2 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q) :
    RegularityBridge.SuccessiveSMulRegular (fun _ : Fin 1 => q ⟨0, by omega⟩) := by
  intro i
  have hii : i = ⟨0, by omega⟩ := Fin.eq_zero i
  subst hii
  have hempty : Set.image (fun _ : Fin 1 => q (⟨0, by omega⟩ : Fin 2))
      {j : Fin 1 | j.val < (⟨0, by omega⟩ : Fin 1).val} = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro r ⟨j, hj, rfl⟩
    exact (Nat.not_lt_zero _) hj
  rw [RegularSequenceDimDrop.span_smul_top, hempty, Ideal.span_empty]
  have h0 := hsucc (⟨0, by omega⟩ : Fin 2)
  have hempty2 : Set.image q
      {j : Fin 2 | j.val < ((⟨0, by omega⟩ : Fin 2)).val} = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro r ⟨j, hj, rfl⟩
    exact (Nat.not_lt_zero _) hj
  rw [RegularSequenceDimDrop.span_smul_top, hempty2, Ideal.span_empty] at h0
  exact h0

/-- U2 step (i) helper, proved: the second generator is nonzero. If it were
`0`, smul-regularity at index `1` would make the (nontrivial, since it sits
below the proper prime `P`) quotient `R ⧸ span{q₀}` a subsingleton. -/
theorem snd_ne_zero_of_successive_pair (m : ℕ) (K : Type*) [Field K]
    (q : Fin 2 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K)) (hJ : J = Ideal.span (Set.range q))
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (hP : P ∈ associatedPrimes _ (_ ⧸ J)) :
    q ⟨1, by omega⟩ ≠ 0 := by
  have h1 := hsucc (⟨1, by omega⟩ : Fin 2)
  rw [RegularSequenceDimDrop.span_smul_top] at h1
  have hprime : P.IsPrime := inferInstance
  have hJP : J ≤ P := LocalUnmixed.assPrime_contains_span J P hP
  have hprev : Set.image q
      {j : Fin 2 | j.val < ((⟨1, by omega⟩ : Fin 2)).val} =
      {q ⟨0, by omega⟩} := by
    ext r
    simp only [Set.mem_image, Set.mem_singleton_iff]
    constructor
    · rintro ⟨j, hj, rfl⟩
      rw [Set.mem_ofPred_eq] at hj
      have hj0 : j.val = 0 := by omega
      have hjj : j = (⟨0, by omega⟩ : Fin 2) := Fin.ext hj0
      rw [hjj]
    · intro hr
      exact ⟨⟨0, by omega⟩, by decide, hr.symm⟩
  have hJP' : Ideal.span (Set.range q) ≤ P := by
    rw [← hJ]
    exact hJP
  have hle : Ideal.span (Set.image q
      {j : Fin 2 | j.val < ((⟨1, by omega⟩ : Fin 2)).val}) ≤ P := by
    rw [hprev]
    exact le_trans (Ideal.span_le.mpr
      (Set.singleton_subset_iff.mpr
        (Ideal.subset_span (Set.mem_range_self _)))) hJP'
  intro hcon
  have hsub : Subsingleton (MvPolynomial (Fin m) K ⧸
      ((Ideal.span (Set.image q
        {j : Fin 2 | j.val < ((⟨1, by omega⟩ : Fin 2)).val}) :
        Ideal (MvPolynomial (Fin m) K)) : Submodule _ _)) :=
    ⟨fun x y => h1 (by simp only [hcon, zero_smul])⟩
  have hne : Ideal.span (Set.image q
      {j : Fin 2 | j.val < ((⟨1, by omega⟩ : Fin 2)).val}) ≠ ⊤ := by
    intro htop
    rw [htop] at hle
    exact hprime.ne_top (top_le_iff.mp hle)
  have hnt : Nontrivial (MvPolynomial (Fin m) K ⧸
      ((Ideal.span (Set.image q
        {j : Fin 2 | j.val < ((⟨1, by omega⟩ : Fin 2)).val}) :
        Ideal (MvPolynomial (Fin m) K)) : Submodule _ _)) :=
    Ideal.Quotient.nontrivial_iff.mpr hne
  exact @not_nontrivial _ hsub hnt

/-- U2 step (i), proved: a height-1 prime `Q ≤ P` minimal over the first
generator. Assembled in-tree with no reproof: existence via
`Ideal.exists_minimalPrimes_le` (at `(q₀) ≤ J ≤ P`), the upper bound via
Krull (`AssHeightBound.height_le_of_mem_minimalPrimes` at the `Fin 1`
family), the lower bound via successive regularity
(`AssHeightBound.le_height_of_span_of_successive` at the `Fin 1` family). -/
theorem exists_height_one_minimal_le_of_successive_pair (m : ℕ) (K : Type*)
    [Field K]
    (q : Fin 2 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K)) (hJ : J = Ideal.span (Set.range q))
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (hP : P ∈ associatedPrimes _ (_ ⧸ J)) :
    ∃ Q : Ideal (MvPolynomial (Fin m) K), Q.IsPrime ∧ Q.height = 1 ∧ Q ≤ P ∧
      Ideal.span ({q ⟨0, by omega⟩} : Set _) ≤ Q ∧
      Q ∈ (Ideal.span ({q ⟨0, by omega⟩} : Set _)).minimalPrimes := by
  have hsing := singleton_successive_of_successive_pair m K q hsucc
  have hJP : J ≤ P := LocalUnmixed.assPrime_contains_span J P hP
  have hrange : Set.range (fun _ : Fin 1 => q (⟨0, by omega⟩ : Fin 2)) =
      {q ⟨0, by omega⟩} := by
    ext r
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      rfl
    · intro hr
      exact ⟨⟨0, by omega⟩, hr.symm⟩
  have hJ1J : Ideal.span ({q (⟨0, by omega⟩ : Fin 2)} :
      Set (MvPolynomial (Fin m) K)) ≤ J := by
    rw [hJ]
    apply Ideal.span_le.mpr
    intro r hr
    rw [Set.mem_singleton_iff] at hr
    rw [hr]
    exact Ideal.subset_span (Set.mem_range_self _)
  have hJ1P : Ideal.span ({q (⟨0, by omega⟩ : Fin 2)} :
      Set (MvPolynomial (Fin m) K)) ≤ P := le_trans hJ1J hJP
  obtain ⟨Q, hQmin, hQP⟩ := Ideal.exists_minimalPrimes_le hJ1P
  have hmin : (Ideal.span ({q (⟨0, by omega⟩ : Fin 2)} :
      Set (MvPolynomial (Fin m) K))).IsMinimalPrime Q := hQmin
  have hQprime : Q.IsPrime := hmin.isPrime
  refine ⟨Q, hQprime, ?_, hQP, hmin.le, hQmin⟩
  have hupper : Q.height ≤ ((1 : ℕ) : ℕ∞) :=
    @AssHeightBound.height_le_of_mem_minimalPrimes _ _ _ _
      (fun _ : Fin 1 => q (⟨0, by omega⟩ : Fin 2))
      (Ideal.span ({q (⟨0, by omega⟩ : Fin 2)} :
        Set (MvPolynomial (Fin m) K)))
      (by rw [hrange]) Q hQprime hQmin
  have hleQ : Ideal.span (Set.range
      (fun _ : Fin 1 => q (⟨0, by omega⟩ : Fin 2))) ≤ Q := by
    rw [hrange]
    exact hmin.le
  have hlower : ((1 : ℕ) : ℕ∞) ≤ Q.height :=
    @AssHeightBound.le_height_of_span_of_successive _ _ _ _ _ hsing Q hQprime hleQ
  have heq : Q.height = ((1 : ℕ) : ℕ∞) := le_antisymm hupper hlower
  simpa using heq

/-- U2 step (ii), proved: thin application of `u1_dvr_at_height_one` — pins
the interface through which the height-1 prime from step (i) feeds the
dimension drop in step (iii). The UFD and domain instances on the localization
are the free ones from the SPEC exists list
(`MonoidLocalization/UniqueFactorization.lean`,
`Localization/AtPrime/Basic.lean`). -/
theorem dvr_at_height_one_le_of_successive_pair (m : ℕ) (K : Type*) [Field K]
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hht : Q.height = 1)
    [UniqueFactorizationMonoid (Localization.AtPrime Q)] :
    IsDiscreteValuationRing (Localization.AtPrime Q) :=
  u1_dvr_at_height_one m K Q hht

/-- U2 step (iii), general drop, proved: quotienting a DVR by a nonzero
element drops dimension to (at most) zero, via
`ringKrullDim_quotient_succ_le_of_nonZeroDivisor`
(`Mathlib/RingTheory/KrullDimension/NonZeroDivisors.lean`, name and
signature verified by Bash grep: `{r: R} (hr: r ∈ R⁰) ⊢
ringKrullDim (R ⧸ Ideal.span {r}) + 1 ≤ ringKrullDim R`) cancelled against
`IsPrincipalIdealRing.ringKrullDim_eq_one`
(`Mathlib/RingTheory/KrullDimension/PID.lean`, verified by grep) through
`ENat.WithBot.add_le_add_one_right_iff`
(`Mathlib/Data/ENat/Monoid.lean`, verified by grep). Stated as `≤ 0`
rather than `= 0` to cover the unit case, where the quotient is trivial
(`ringKrullDim_eq_bot_of_subsingleton`). -/
theorem ringKrullDim_quotient_span_le_zero_of_dvr {D : Type*} [CommRing D]
    [IsDomain D] [IsDiscreteValuationRing D] {r : D} (hr : r ∈ D⁰) :
    ringKrullDim (D ⧸ Ideal.span {r}) ≤ 0 := by
  have hr0 : r ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hr
  have hdrop := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (R := D) hr
  by_cases hunit : IsUnit r
  · have htop : Ideal.span ({r} : Set D) = ⊤ :=
      Ideal.span_singleton_eq_top.mpr hunit
    have hbot : ringKrullDim (D ⧸ Ideal.span ({r} : Set D)) = ⊥ :=
      @ringKrullDim_eq_bot_of_subsingleton (D ⧸ Ideal.span ({r} : Set D)) _
        (Ideal.Quotient.subsingleton_iff.mpr htop)
    rw [hbot]
    exact bot_le
  · have hrmem : r ∈ IsLocalRing.maximalIdeal D :=
      (IsLocalRing.mem_maximalIdeal r).mpr (mem_nonunits_iff.mpr hunit)
    have hmax_ne : IsLocalRing.maximalIdeal D ≠ ⊥ := by
      intro hcon
      rw [hcon, Ideal.mem_bot] at hrmem
      exact hr0 hrmem
    have hD : ¬IsField D := by
      intro hfield
      exact hmax_ne (IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield)
    have hdim : ringKrullDim D = 1 :=
      IsPrincipalIdealRing.ringKrullDim_eq_one D hD
    have hle : ringKrullDim (D ⧸ Ideal.span {r}) + 1 ≤ 0 + 1 := by
      rw [zero_add]
      exact hdrop.trans_eq hdim
    exact ENat.WithBot.add_le_add_one_right_iff.mp hle

/-- U2 step (iii), applied, proved: the second generator survives in the DVR
`R_Q` — its vanishing would force `q₁ = 0` in the domain `R` (localization maps
are injective on domains: `IsLocalization.injective`), against
`snd_ne_zero_of_successive_pair` — hence the DVR quotient by its span has
dimension at most zero by the general drop. -/
theorem dim_dvr_quotient_le_zero_of_successive_pair (m : ℕ) (K : Type*)
    [Field K]
    (q : Fin 2 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K)) (hJ : J = Ideal.span (Set.range q))
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (hP : P ∈ associatedPrimes _ (_ ⧸ J))
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    [UniqueFactorizationMonoid (Localization.AtPrime Q)]
    [IsDiscreteValuationRing (Localization.AtPrime Q)] :
    ringKrullDim (Localization.AtPrime Q ⧸
      Ideal.span {(algebraMap (MvPolynomial (Fin m) K)
        (Localization.AtPrime Q) (q ⟨1, by omega⟩))}) ≤ 0 := by
  have h1 := snd_ne_zero_of_successive_pair m K q hsucc J hJ P hP
  have hne : algebraMap (MvPolynomial (Fin m) K)
      (Localization.AtPrime Q) (q ⟨1, by omega⟩) ≠ 0 := by
    intro hcon
    apply h1
    have hsub : Q.primeCompl ≤ nonZeroDivisors (MvPolynomial (Fin m) K) := by
      intro s hs
      rw [mem_nonZeroDivisors_iff_ne_zero]
      intro h0
      subst h0
      exact hs (Ideal.zero_mem Q)
    have hinj : Function.Injective (algebraMap (MvPolynomial (Fin m) K)
        (Localization.AtPrime Q)) :=
      IsLocalization.injective (Localization.AtPrime Q) hsub
    exact hinj (by simpa using hcon)
  exact ringKrullDim_quotient_span_le_zero_of_dvr
    (mem_nonZeroDivisors_iff_ne_zero.mpr hne)

/-- Height reduction for U2, proved: the in-tree dimension equation
(`AssHeightBound.height_eq_add_of_span`: `↑height P = dim (R_P ⧸ J_P) + 2`)
plus the in-tree lower bound
(`AssHeightBound.le_height_of_mem_associatedPrimes_of_successive`) reduce
`U2DimZeroInput` to the single inequality `P.height ≤ 2`. The lower bound on
`dim` is free (`ringKrullDim_nonneg_of_nontrivial`, since `J_P` sits below the
maximal ideal); the cancellation is `ENat.WithBot.add_le_add_natCast_right_iff`.
This is what makes the step-(iv) residual exact: only the height upper bound
is missing. -/
theorem u2_dim_zero_of_height_le_two (m : ℕ) (K : Type*) [Field K]
    (q : Fin 2 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K)) (hJ : J = Ideal.span (Set.range q))
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (hP : P ∈ associatedPrimes _ (_ ⧸ J))
    (hle2 : P.height ≤ 2) :
    U2DimZeroInput m K q P := by
  have hJP : Ideal.span (Set.range q) ≤ P := by
    rw [← hJ]
    exact LocalUnmixed.assPrime_contains_span J P hP
  have hH := AssHeightBound.height_eq_add_of_span q hsucc P hJP
  have hge : ((2 : ℕ) : ℕ∞) ≤ P.height :=
    AssHeightBound.le_height_of_mem_associatedPrimes_of_successive
      q hsucc J hJ P hP
  have h2 : P.height = 2 := le_antisymm hle2 (by exact_mod_cast hge)
  have hle : ringKrullDim (Localization.AtPrime P ⧸
      Ideal.span (Set.range (algebraMap (MvPolynomial (Fin m) K)
        (Localization.AtPrime P) ∘ q))) + ((2 : ℕ) : WithBot ℕ∞) ≤
      0 + ((2 : ℕ) : WithBot ℕ∞) := by
    rw [zero_add]
    have h1 : ((P.height : ℕ∞) : WithBot ℕ∞) ≤ ((2 : ℕ) : WithBot ℕ∞) := by
      rw [h2]
      norm_cast
    rw [hH] at h1
    exact h1
  have hle0 : ringKrullDim (Localization.AtPrime P ⧸
      Ideal.span (Set.range (algebraMap (MvPolynomial (Fin m) K)
        (Localization.AtPrime P) ∘ q))) ≤ 0 :=
    ENat.WithBot.add_le_add_natCast_right_iff.mp hle
  have hJPne : Ideal.span (Set.range (algebraMap (MvPolynomial (Fin m) K)
      (Localization.AtPrime P) ∘ q)) ≠ ⊤ := by
    intro hcon
    have hmem : ∀ i, algebraMap (MvPolynomial (Fin m) K)
        (Localization.AtPrime P) (q i) ∈
        IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
      intro i
      rw [IsLocalization.AtPrime.to_map_mem_maximal_iff
        (Localization.AtPrime P) P]
      exact hJP (Ideal.subset_span (Set.mem_range_self i))
    have hleM : Ideal.span (Set.range (algebraMap (MvPolynomial (Fin m) K)
        (Localization.AtPrime P) ∘ q)) ≤
        IsLocalRing.maximalIdeal (Localization.AtPrime P) :=
      Ideal.span_le.mpr (Set.range_subset_iff.mpr hmem)
    rw [hcon] at hleM
    exact Ideal.IsMaximal.ne_top inferInstance (top_le_iff.mp hleM)
  have hge0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime P ⧸
      Ideal.span (Set.range (algebraMap (MvPolynomial (Fin m) K)
        (Localization.AtPrime P) ∘ q))) :=
    @ringKrullDim_nonneg_of_nontrivial _ _
      (Ideal.Quotient.nontrivial_iff.mpr hJPne)
  change ringKrullDim (Localization.AtPrime P ⧸
    Ideal.span (Set.range (algebraMap (MvPolynomial (Fin m) K)
      (Localization.AtPrime P) ∘ q))) = 0
  exact le_antisymm hle0 hge0

/-- Catenary-upper bridge input for the `k = 2` DVR route (route tag
`k2-of-catenary-upper`): the exact missing inequality
`P.height ≤ Q.height + dim R_Q` as an explicit hypothesis, for primes
`Q ≤ P` with `R_Q = Localization.AtPrime Q`. In a catenary ring the true
inequality carries a fiber term
(`Ideal.height_le_height_add_of_liesOver`); this shape identifies the fiber
with `dim R_Q`, which is what the DVR route must supply. Kept as a `Prop` so
the residual has a formal address. -/
def CatenaryUpperInput (m : ℕ) (K : Type*) [Field K]
    (Q P : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] : Prop :=
  ((P.height : ℕ∞) : WithBot ℕ∞) ≤ ((Q.height : ℕ∞) : WithBot ℕ∞) +
    ringKrullDim (Localization.AtPrime Q)

/-- Height bound from the catenary-upper bridge: with `Q.height = 1` and
`dim R_Q = 1` (the latter from `IsLocalization.AtPrime.ringKrullDim_eq_height`,
as in `hasUniqueIrreducible_atPrime_height_one`), the bridge inequality forces
`P.height ≤ 2` — exactly the hypothesis of `u2_dim_zero_of_height_le_two`. -/
theorem height_le_two_of_catenary_upper (m : ℕ) (K : Type*) [Field K]
    (P Q : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime] [Q.IsPrime]
    (hht : Q.height = 1)
    (hup : CatenaryUpperInput m K Q P) :
    P.height ≤ 2 := by
  have hdim : ringKrullDim (Localization.AtPrime Q) = 1 := by
    have h := IsLocalization.AtPrime.ringKrullDim_eq_height Q (Localization.AtPrime Q)
    rw [hht] at h
    simpa using h
  unfold CatenaryUpperInput at hup
  rw [hht, hdim] at hup
  have h2 : ((P.height : ℕ∞) : WithBot ℕ∞) ≤ (((2 : ℕ∞)) : WithBot ℕ∞) := by
    refine hup.trans ?_
    decide
  exact_mod_cast h2

/-- `k = 2` endgame through the catenary-upper bridge (route tag
`k2-of-catenary-upper`), conditional: the height-1 prime from U2 step (i)
(`exists_height_one_minimal_le_of_successive_pair`) feeds the single bridge
hypothesis `hcat` (the catenary-upper inequality at height-1 primes below `P`);
the resulting `P.height ≤ 2` closes through the proved chain
(`height_le_two_of_catenary_upper` + `u2_dim_zero_of_height_le_two` +
`unmixed_two_of_u2`).
The `k = 2` residual is therefore exactly one named bridge: `hcat`. -/
theorem unmixed_two_of_catenary_upper (m : ℕ) (K : Type*) [Field K]
    (q : Fin 2 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K)) (hJ : J = Ideal.span (Set.range q))
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (hP : P ∈ associatedPrimes _ (_ ⧸ J))
    (hcat : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q.height = 1 → Q ≤ P → CatenaryUpperInput m K Q P) :
    P ∈ J.minimalPrimes := by
  obtain ⟨Q, hQp, hht, hle, _, _⟩ :=
    exists_height_one_minimal_le_of_successive_pair m K q hsucc J hJ P hP
  have hup := @hcat Q hQp hht hle
  have hle2 := @height_le_two_of_catenary_upper m K inferInstance P Q
    inferInstance hQp hht hup
  exact unmixed_two_of_u2 m K q hsucc J hJ P hP
    (u2_dim_zero_of_height_le_two m K q hsucc J hJ P hP hle2)

/-- Minimal CM-like induction-step statement: hunmixedness of `R ⧸ J` lifts
across a regular generator `x` to hunmixedness of `(R ⧸ J) ⧸ span {x}`.
Proving this for the specific successive quotients (quotient-of-CM-by-regular
+ CM-implies-unmixed at those rings only) is the CM roadblock for `k ≥ 3`;
no general CM theory is formalized here by design. -/
def RegularQuotientPreservesHunmixed (R : Type*) [CommRing R] (J : Ideal R)
    (x : R ⧸ J) : Prop :=
  IsHunmixed R J → IsHunmixed (R ⧸ J) (Ideal.span {x})

/-- CM-step application shape, conditional: the step hypothesis applied to the
base. Trivial as a proof; its value is architectural — it pins the exact
interface CM must supply so `k ≥ 3` induction has a formal address. -/
theorem unmixed_of_cm_step {R : Type*} [CommRing R] (J : Ideal R) (x : R ⧸ J)
    (hJ : IsHunmixed R J) (hstep : RegularQuotientPreservesHunmixed R J x) :
    IsHunmixed (R ⧸ J) (Ideal.span {x}) :=
  hstep hJ

/-- Finite prefix of a `Fin k`-indexed family as a `Fin j`-indexed family
(`hj : j ≤ k`), by truncating indices. Route-A combinatorics: prefixes of a
successive family stay successive (`successiveSMulRegular_prefix` below). -/
def prefixFun {R : Type*} [CommRing R] {k : ℕ} (q : Fin k → R) {j : ℕ}
    (hj : j ≤ k) : Fin j → R :=
  fun i => q ⟨i.val, lt_of_lt_of_le i.isLt hj⟩

/-- Route-A prefix combinatorics, proved: a prefix of a successive family is
successive — pure `Fin`/previous-value-set combinatorics. For `i : Fin j` the
previous-value set `{t | t.val < i.val}` re-embeds bijectively into
`{s : Fin k | s.val < i.val}`, so the two spans coincide and `hsucc` at the
embedded index transfers verbatim (written from scratch). -/
theorem successiveSMulRegular_prefix {R : Type*} [CommRing R] {k j : ℕ}
    (q : Fin k → R) (hsucc : RegularityBridge.SuccessiveSMulRegular q) (hj : j ≤ k) :
    RegularityBridge.SuccessiveSMulRegular (prefixFun q hj) := by
  intro i
  have h := hsucc ⟨i.val, lt_of_lt_of_le i.isLt hj⟩
  have hset : Set.image (prefixFun q hj) {t : Fin j | t.val < i.val} =
      Set.image q
        {s : Fin k | s.val < (⟨i.val, lt_of_lt_of_le i.isLt hj⟩ : Fin k).val} := by
    ext r
    simp only [Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t.val, lt_of_lt_of_le (lt_trans ht i.isLt) hj⟩, ht, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      refine ⟨⟨s.val, lt_trans hs i.isLt⟩, hs, ?_⟩
      exact congrArg q (Fin.ext rfl)
  rw [hset]
  exact h

/-- The full-length prefix is the family itself. Feeds the `j = k` prefix
input into the length-`k` proved lemmas. -/
theorem prefixFun_full {R : Type*} [CommRing R] {k : ℕ} (q : Fin k → R) :
    prefixFun q (le_refl k) = q := by
  funext i
  exact congrArg q (Fin.ext rfl)

/-- Per-prefix localized dimension-zero inputs (HDimZeroPrefix-style
scaffolding-toward-(b)): at every prefix length `j ≤ k`, the localized
quotient by the prefix span has Krull dimension zero. The `j = k` instance is
the exact input of `mem_minimalPrimes_of_localized_quotient_dim_zero`; the
strict prefixes are the addresses where the height-drop residual
(`HeightDrop.HeightDropResidualAt`, proved elsewhere) must be proved. -/
def PrefixDimZeroInput (m : ℕ) (K : Type*) [Field K] {k : ℕ}
    (q : Fin k → MvPolynomial (Fin m) K)
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime] : Prop :=
  ∀ (j : ℕ) (hj : j ≤ k),
    ringKrullDim (Localization.AtPrime P ⧸
      Ideal.span (Set.range (algebraMap (MvPolynomial (Fin m) K)
        (Localization.AtPrime P) ∘ prefixFun q hj))) = 0

/-- Route-A assembly (O-strategy: localized-dim-zero induction, no CM
vocabulary), proved conditionally: induction on `k` routing each step through
the proved `mem_minimalPrimes_of_localized_quotient_dim_zero`
(`Regularity/Unmixed/Unmixedness.lean`). The `k = 0` case closes unconditionally via
the proved `mem_minimalPrimes_of_successive_zero`; every successor case feeds
its full-length (`j = k + 1`) prefix input — identified with `q` by
`prefixFun_full` — into the proved conditional lemma. (`ih` is not consumed:
the per-prefix hypothesis already carries each level's content, so this is a
case-threading induction rather than a proof by induction — `k ≤ 2` closes
through the separate aliases below (`unmixed_closed_zero/one`,
`unmixed_two_of_height_le_two_closed`), while `k ≥ 3` stays conditional on
exactly the height-drop residual.) -/
theorem unmixed_of_successive_regular_of_prefix_dim_zero
    (m : ℕ) (K : Type*) [Field K] (k : ℕ) :
    ∀ (q : Fin k → MvPolynomial (Fin m) K)
    (_hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K)) (_hJ : J = Ideal.span (Set.range q))
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (_hP : P ∈ associatedPrimes _ (_ ⧸ J))
    (_hpre : PrefixDimZeroInput m K q P),
    P ∈ J.minimalPrimes := by
  induction k with
  | zero =>
    intro q hsucc J hJ P _ hP _
    exact mem_minimalPrimes_of_successive_zero m K q hsucc J hJ P hP
  | succ k _ih =>
    intro q hsucc J hJ P _ hP hpre
    have h0 := hpre (k + 1) le_rfl
    rw [prefixFun_full] at h0
    exact mem_minimalPrimes_of_localized_quotient_dim_zero m (k + 1) K q hsucc J
      hJ P hP h0

/-- `k = 0` closed end-to-end: thin alias of the proved length-zero lemma, so
the assembly covers `k = 0` unconditionally. -/
theorem unmixed_closed_zero (m : ℕ) (K : Type*) [Field K]
    (q : Fin 0 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K)) (hJ : J = Ideal.span (Set.range q))
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (hP : P ∈ associatedPrimes _ (_ ⧸ J)) :
    P ∈ J.minimalPrimes :=
  mem_minimalPrimes_of_successive_zero m K q hsucc J hJ P hP

/-- `k = 1` closed end-to-end: thin alias of the proved UFD singleton lemma. -/
theorem unmixed_closed_one (m : ℕ) (K : Type*) [Field K]
    (q : Fin 1 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K)) (hJ : J = Ideal.span (Set.range q))
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (hP : P ∈ associatedPrimes _ (_ ⧸ J)) :
    P ∈ J.minimalPrimes :=
  mem_minimalPrimes_of_successive_singleton m K q hsucc J hJ P hP

/-- `k = 2` closed through the proved u2 chain: the height inequality
(`P.height ≤ 2`, the `HeightDrop` residual) feeds `u2_dim_zero_of_height_le_two`,
whose output feeds `unmixed_two_of_u2`. No other hypothesis remains. -/
theorem unmixed_two_of_height_le_two_closed (m : ℕ) (K : Type*) [Field K]
    (q : Fin 2 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K)) (hJ : J = Ideal.span (Set.range q))
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (hP : P ∈ associatedPrimes _ (_ ⧸ J))
    (hle2 : P.height ≤ 2) :
    P ∈ J.minimalPrimes :=
  unmixed_two_of_u2 m K q hsucc J hJ P hP
    (u2_dim_zero_of_height_le_two m K q hsucc J hJ P hP hle2)

/-- Prefix lower-bound staircase, proved: every prefix length `j ≤ k`
contributes `(j : ℕ∞) ≤ P.height`, via `successiveSMulRegular_prefix` fed
into the in-tree global lower bound
(`AssHeightBound.le_height_of_span_of_successive`). This is the lower half of
the height endgame; the upper half (`P.height ≤ j` per prefix) is the `HeightDrop`
residual and is not attempted here. -/
theorem height_le_prefix_staircase (m : ℕ) (K : Type*) [Field K] {k : ℕ}
    (q : Fin k → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K)) (hJ : J = Ideal.span (Set.range q))
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (hP : P ∈ associatedPrimes _ (_ ⧸ J))
    (j : ℕ) (hj : j ≤ k) :
    (j : ℕ∞) ≤ P.height := by
  have hJP : Ideal.span (Set.range q) ≤ P := by
    rw [← hJ]
    exact LocalUnmixed.assPrime_contains_span J P hP
  apply AssHeightBound.le_height_of_span_of_successive (prefixFun q hj)
    (successiveSMulRegular_prefix q hsucc hj) P
  apply le_trans _ hJP
  apply Ideal.span_le.mpr
  intro r hr
  obtain ⟨i, rfl⟩ := hr
  exact Ideal.subset_span
    (Set.mem_range_self (⟨i.val, lt_of_lt_of_le i.isLt hj⟩ : Fin k))

/-- Restriction of the per-prefix inputs to a prefix length: the inputs for
`q` (length `k`) restrict to inputs for any prefix (length `j ≤ k`), since a
prefix of a prefix is pointwise a prefix (by `Fin.ext`). This is what lets
induction levels thread: each level's inputs contain every shorter level's. -/
theorem prefixDimZeroInput_restrict (m : ℕ) (K : Type*) [Field K] {k : ℕ}
    (q : Fin k → MvPolynomial (Fin m) K)
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (hpre : PrefixDimZeroInput m K q P)
    {j : ℕ} (hj : j ≤ k) :
    PrefixDimZeroInput m K (prefixFun q hj) P := by
  intro j' hj'
  have h := hpre j' (le_trans hj' hj)
  have heq : prefixFun (prefixFun q hj) hj' = prefixFun q (le_trans hj' hj) := by
    funext i
    exact congrArg q (Fin.ext rfl)
  rw [heq]
  exact h

end EvolutionAlgebras.Appendix_FixedPoint.BezoutChain
