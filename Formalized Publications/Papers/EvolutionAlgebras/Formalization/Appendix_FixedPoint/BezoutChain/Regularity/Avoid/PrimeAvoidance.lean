/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# Prime-avoidance selection lemmas

This file packages Mathlib's prime-avoidance theorems
(`Ideal.subset_union_prime`, `Ideal.subset_union_prime_finite`) as
element-selection lemmas in the exact shapes consumed in-tree. No avoidance
result is reproved: every proof below is a contrapositive or
finiteness-instantiation of a Mathlib statement.

## Main results

* (a) `VariableInductionCM` L5(b): in a local ring
  `S = Localization.AtPrime P`, pick an element of an ideal `I`
  (typically the maximal ideal) outside a finite family of primes, none of
  which contains `I`. Provided here as `exists_mem_notMem_of_forall_isPrime`
  (general finite family) and `exists_mem_maximal_notMem` (maximal-ideal
  specialization: the per-prime hypothesis collapses to `f i ≠ maximalIdeal`;
  no Noetherian hypothesis is needed — only `[IsLocalRing S]`).
* (b) R2 avoidance (`AvoidanceStep` / `AvoidanceApply` /
  `ResultantLemmas`): from per-prime non-containment
  `∀ P ∈ Ass, ¬ I ≤ P` (the conclusion of
  `AvoidanceStep.noAssPrime_contains_span_of_height_bounds` at
  `I = span G`, `M = R ⧸ J`), select one element of `I` outside every
  associated prime — hence SMul-regular on `M`
  (`exists_isSMulRegular_mem_of_forall_not_le_ass`). The regularity half has
  the same content as in-tree `ResultantLemmas.regular_of_avoid`; it is
  restated here only to give consumers a single one-step feed, proved from
  Mathlib's `biUnion_associatedPrimes_eq_compl_regular`, not copied.

## References

Mathlib (v4.34.0, all names verified against `.lake/packages/mathlib`):

* `Mathlib/RingTheory/Ideal/Operations.lean`: `Ideal.subset_union_prime`,
  `Ideal.subset_union_prime_finite`.
* `Mathlib/RingTheory/Ideal/AssociatedPrime/Basic.lean`:
  `associatedPrimes`, `AssociatedPrimes.mem_iff`,
  `IsAssociatedPrime.isPrime`.
* `Mathlib/RingTheory/Ideal/AssociatedPrime/Finiteness.lean`:
  `associatedPrimes.finite`.
* `Mathlib/RingTheory/Regular/IsSMulRegular.lean`:
  `biUnion_associatedPrimes_eq_compl_regular`.
* `Mathlib/RingTheory/Ideal/Prime.lean`: `Ideal.IsPrime.ne_top`.
* `Mathlib/RingTheory/Ideal/Maximal.lean`: `Ideal.IsMaximal.eq_of_le`.
* `Mathlib/RingTheory/LocalRing/MaximalIdeal/Basic.lean`:
  `IsLocalRing.maximalIdeal`, `IsLocalRing.maximalIdeal.isMaximal`.
* `Mathlib/Data/Finset/Empty.lean`: `Finset.eq_empty_or_nonempty`,
  `Finset.notMem_empty`.
* `Mathlib/Data/Set/Lattice/Indexed.lean`: `Set.mem_iUnion₂`.
* `Mathlib/Data/Set/Operations.lean`: `Set.mem_compl_iff` (via `simpa`).

Project (`Formalization/Appendix_FixedPoint/BezoutChain/Regularity/`):

* `VariableInductionCM.lean` L5(b): consumer (a); the selection inside the
  maximal ideal is supplied here (`exists_mem_maximal_notMem`), conditional
  on `VarUnmixedOneResidual`-style control of `Ass (S ⧸ span {x})`.
* `AvoidanceStep.lean`, `noAssPrime_contains_span_of_height_bounds`:
  supplies the per-prime `¬ span G ≤ P` inputs for consumer (b).
* `AvoidanceApply.lean`, `span_le_of_comap_comboLin_eq_top`:
  the `comap`-to-`span` bridge downstream of consumer (b).
* `ResultantLemmas.lean`, `regular_of_avoid`, `exists_avoiding_coeff`:
  parallel selection shapes (regularity-from-avoidance; coefficient
  avoidance over an infinite field via
  `Submodule.exists_forall_notMem_of_forall_ne_top`).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace PrimeAvoidance

/-! ## Element selection over finite families of ideals

Contrapositives of Mathlib's prime-avoidance theorems, in `Finset` and
`Set.Finite` forms plus the ergonomic all-prime specialization. These are the
raw selection tools; the sections below instantiate them at the maximal ideal
and at the associated primes. -/

/-- Element selection from prime avoidance (Finset form, in Mathlib's exact
two-exception shape): if no member of a finite family of ideals contains `I`,
some element of `I` lies outside every member. This is the contrapositive of
`Ideal.subset_union_prime` via `Set.not_subset`.

## References

* `Ideal.subset_union_prime`. -/
theorem exists_mem_notMem_of_forall_not_le {R : Type*} [CommRing R] {ι : Type*}
    {s : Finset ι} {f : ι → Ideal R} (a b : ι)
    (hp : ∀ i ∈ s, i ≠ a → i ≠ b → (f i).IsPrime)
    (I : Ideal R) (hle : ∀ i ∈ s, ¬ I ≤ f i) :
    ∃ x ∈ I, ∀ i ∈ s, x ∉ f i := by
  by_contra hcon
  push Not at hcon
  have hsub : (I : Set R) ⊆ ⋃ i ∈ (↑s : Set ι), (f i : Set R) := by
    intro x hx
    obtain ⟨i, hi, hmem⟩ := hcon x hx
    exact Set.mem_iUnion₂.mpr ⟨i, Finset.mem_coe.mpr hi, hmem⟩
  obtain ⟨i, hi, hle'⟩ := (Ideal.subset_union_prime a b hp).mp hsub
  exact hle i hi hle'

/-- Element selection from prime avoidance (`Set.Finite` form): the same content
via `Ideal.subset_union_prime_finite`. This is the form fed by
`associatedPrimes.finite` below.

## References

* `Ideal.subset_union_prime_finite`. -/
theorem exists_mem_notMem_of_forall_not_le_finite {R ι : Type*} [CommRing R]
    {s : Set ι} (hs : s.Finite) {f : ι → Ideal R} (a b : ι)
    (hp : ∀ i ∈ s, i ≠ a → i ≠ b → (f i).IsPrime)
    (I : Ideal R) (hle : ∀ i ∈ s, ¬ I ≤ f i) :
    ∃ x ∈ I, ∀ i ∈ s, x ∉ f i := by
  by_contra hcon
  push Not at hcon
  have hsub : (I : Set R) ⊆ ⋃ i ∈ s, (f i : Set R) := by
    intro x hx
    obtain ⟨i, hi, hmem⟩ := hcon x hx
    exact Set.mem_iUnion₂.mpr ⟨i, hi, hmem⟩
  obtain ⟨i, hi, hle'⟩ := (Ideal.subset_union_prime_finite hs a b hp).mp hsub
  exact hle i hi hle'

/-- Element selection over an all-prime finite family (ergonomic form with no
exception indices): the empty case is witnessed by `0`, while the nonempty
case reuses the two-exception lemma with both exceptions placed at one member.

## References

* `exists_mem_notMem_of_forall_not_le` above.
* `Finset.eq_empty_or_nonempty`, `Finset.notMem_empty`, `Ideal.zero_mem`. -/
theorem exists_mem_notMem_of_forall_isPrime {R : Type*} [CommRing R] {ι : Type*}
    {s : Finset ι} {f : ι → Ideal R}
    (hp : ∀ i ∈ s, (f i).IsPrime)
    (I : Ideal R) (hle : ∀ i ∈ s, ¬ I ≤ f i) :
    ∃ x ∈ I, ∀ i ∈ s, x ∉ f i := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨a₀, ha₀⟩
  · exact ⟨0, Ideal.zero_mem I, fun i hi => (Finset.notMem_empty i hi).elim⟩
  · exact exists_mem_notMem_of_forall_not_le a₀ a₀
      (fun i hi _ _ => hp i hi) I hle

/-! ## Local selection inside the maximal ideal

The `VariableInductionCM` L5(b) shape: maximality collapses the per-prime
non-containment hypothesis to a single inequality. -/

/-- Local selection inside the maximal ideal (VariableInductionCM L5(b) shape): in a
local ring, a finite family of primes each strictly below the maximal ideal
misses some element of the maximal ideal. The per-prime hypothesis is just
`f i ≠ maximalIdeal` — maximality (`Ideal.IsMaximal.eq_of_le`) turns
`maximalIdeal ≤ f i` into equality, since a prime is never `⊤`.

## References

* `exists_mem_notMem_of_forall_isPrime` above.
* `Ideal.IsPrime.ne_top`, `Ideal.IsMaximal.eq_of_le`,
  `IsLocalRing.maximalIdeal.isMaximal`. -/
theorem exists_mem_maximal_notMem {S : Type*} [CommRing S] [IsLocalRing S]
    {ι : Type*} {s : Finset ι} {f : ι → Ideal S}
    (hp : ∀ i ∈ s, (f i).IsPrime)
    (hne : ∀ i ∈ s, f i ≠ IsLocalRing.maximalIdeal S) :
    ∃ x ∈ IsLocalRing.maximalIdeal S, ∀ i ∈ s, x ∉ f i := by
  apply exists_mem_notMem_of_forall_isPrime hp
  intro i hi hle
  exact hne i hi (((IsLocalRing.maximalIdeal.isMaximal S).eq_of_le
    ((hp i hi).ne_top) hle).symm)

/-! ## Selection outside associated primes, and regularity

The R2 avoidance shape: `associatedPrimes.finite` feeds the `Set.Finite`
lemma, and Mathlib's union description turns avoidance into `IsSMulRegular`.
The final lemma combines both halves into the one-step feed consumers call. -/

/-- Selection outside all associated primes (Noetherian + finite module):
`associatedPrimes.finite` feeds the `Set.Finite` lemma with `a = b = ⊥`
(`Ideal R` is always inhabited); every associated prime is prime via
`AssociatedPrimes.mem_iff` + `IsAssociatedPrime.isPrime`.

## References

* `exists_mem_notMem_of_forall_not_le_finite` above.
* `associatedPrimes.finite`, `AssociatedPrimes.mem_iff`,
  `IsAssociatedPrime.isPrime`. -/
theorem exists_mem_notMem_associatedPrimes {R : Type*} [CommRing R]
    [IsNoetherianRing R] {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Finite R M]
    (I : Ideal R) (hle : ∀ P ∈ associatedPrimes R M, ¬ I ≤ P) :
    ∃ x ∈ I, ∀ P ∈ associatedPrimes R M, x ∉ P :=
  exists_mem_notMem_of_forall_not_le_finite (s := associatedPrimes R M)
    (f := id) (associatedPrimes.finite R M) ⊥ ⊥
    (fun _P hP _ _ => (AssociatedPrimes.mem_iff.mp hP).isPrime) I
    (fun P hP => hle P hP)

/-- Regularity from avoiding every associated prime: an element outside `⋃ Ass`
is SMul-regular. This has the same content as in-tree
`ResultantLemmas.regular_of_avoid`, proved here directly from Mathlib's union
description so that this file stays self-contained.

## References

* `biUnion_associatedPrimes_eq_compl_regular`, `Set.mem_iUnion₂`. -/
theorem isSMulRegular_of_forall_notMem_associatedPrimes {R : Type*} [CommRing R]
    [IsNoetherianRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (x : R) (hav : ∀ P ∈ associatedPrimes R M, x ∉ P) :
    IsSMulRegular M x := by
  have hU := biUnion_associatedPrimes_eq_compl_regular R M
  have hx : x ∉ ⋃ P ∈ associatedPrimes R M, (P : Set R) := by
    intro hmem
    obtain ⟨P, hP, hm⟩ := Set.mem_iUnion₂.mp hmem
    exact hav P hP hm
  rw [hU] at hx
  simpa using hx

/-- One-step regular selection (combined R2 / L5(b) feed): if the ideal `I` is
contained in no associated prime of `M`, some element of `I` is regular on
`M`. Instantiate at `I = Ideal.span (Set.range G)`, `M = R ⧸ J` (R2, with
per-prime inputs from
`AvoidanceStep.noAssPrime_contains_span_of_height_bounds`) or at
`I = IsLocalRing.maximalIdeal S`, `M = S ⧸ Ideal.span {x}` (L5(b), with
per-prime inputs from `VarUnmixedOneResidual`-style control of the
localization quotient).

## References

* `exists_mem_notMem_associatedPrimes`,
  `isSMulRegular_of_forall_notMem_associatedPrimes` above. -/
theorem exists_isSMulRegular_mem_of_forall_not_le_ass {R : Type*} [CommRing R]
    [IsNoetherianRing R] {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Finite R M]
    (I : Ideal R) (hle : ∀ P ∈ associatedPrimes R M, ¬ I ≤ P) :
    ∃ x ∈ I, IsSMulRegular M x := by
  obtain ⟨x, hxI, hx⟩ := exists_mem_notMem_associatedPrimes I hle
  exact ⟨x, hxI, isSMulRegular_of_forall_notMem_associatedPrimes x hx⟩

end PrimeAvoidance
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

/-!
## Obstruction / Residual (what remains open after this file)

This file closes only the prime-avoidance selection step (direct Mathlib
wraps). Everything below is still open and lives with the consumers; none of
it is assumed here:

1. L5(a) associated-prime control (`VarUnmixedOneResidual`): for
   `S = Localization.AtPrime P` and `x` regular, every `Q ∈ Ass (S ⧸ span {x})`
   is minimal over `span {x}` (plus the globalization-to-localization transfer
   of the proved global `k = 1` chain). Without it there is no proof that the
   maximal ideal — or any candidate `I` — avoids containing an associated
   prime of the quotient, so the per-prime hypotheses `hle`/`hne` above have no
   in-tree source at the localization.
2. Height-drop residuals (`VarHeightDropResidual` / `HeightDropResidualAt`,
   U2 step-(iv)): the uniform-`k` bound making the per-prime inputs available
   beyond the second rung.
3. `minimalPrimes`-specialized wrappers: consumers working with
   `J.minimalPrimes` (rather than `Ass`) assemble their own finset and feed
   `exists_mem_notMem_of_forall_isPrime`; no dedicated wrapper is provided
   here until a consumer fixes the exact finset shape.
4. R1 chart-form avoidance stays out of scope: `havoid` over
   `S = coneQuotient n K G` (linear forms in `S`) does not follow from
   `R`-side ideal avoidance; see the R1 gap statement in
   `AvoidanceApply.lean`.

Absent Mathlib API found during development: none — every needed statement
exists in Mathlib v4.34.0 (`Ideal.subset_union_prime`,
`Ideal.subset_union_prime_finite`, `associatedPrimes.finite`,
`biUnion_associatedPrimes_eq_compl_regular`, `Ideal.IsMaximal.eq_of_le`,
`IsLocalRing.maximalIdeal.isMaximal`). The "absent API shape" noted in
`VariableInductionCM.lean` L5(b) referred to the in-tree selection packaging, which
this file now supplies as thin wraps.
-/
