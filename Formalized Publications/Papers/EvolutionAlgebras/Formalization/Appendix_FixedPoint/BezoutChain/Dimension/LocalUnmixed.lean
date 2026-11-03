/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.RegularityBridge
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Regular.Flat

/-!
# Local height bounds for quotients by regular sequences
Noetherian local `(R, 𝔪)`, regular sequence `rs` of length `k` in the
`RingTheory.Sequence.IsRegular` list API (reached from `Fin k`-indexed
successive data through the A1 bridge `RegularityBridge.isRegular_ofFn_of_successive`):
every `P ∈ Ass(R ⧸ J)` (`J = Ideal.ofList rs`) contains `J` and has height
**at least** `k`; minimal primes over `J` have height **exactly** `k`.

## Status: maximal partial result + precise obstruction

The full chunk-A3 goal "`P.height = k` for every `P ∈ Ass(R ⧸ J)`" is **false**
as stated for general Noetherian local rings — the upper bound `P.height ≤ k`
fails. Counterexample (verified by hand): `R = k[a,b,c] ⧸ (ab, ac)` localized
at `𝔪 = (a, b, c)`, regular element `x = a + b` (it avoids both minimal primes
`(a)` and `(b, c)`). Then `R ⧸ (x) ≃ k[b,c] ⧸ (b², bc)`, whose associated
primes are `(b)` (height 1) and `(b, c) = ann(b̄)` (height 2, embedded). So
`𝔪 ∈ Ass(R ⧸ (x))` has height `2 ≠ 1 = k`. In particular the `k = 1`
"regular-element height-drop lemma" does not exist in this generality, and no
induction through `isRegular_cons_iff` can produce it: the missing ingredient
is Cohen–Macaulay-ness of `R` (quotients of a CM ring by a regular sequence
are unmixed), for which Mathlib has no API (no CM / grade / Ext-depth). The
intended Bezout application takes `R` a polynomial ring (regular, hence CM),
so the fix is to add that hypothesis once a CM API exists.

What is proved here:
* `assPrime_contains_span`: `P ∈ Ass(R ⧸ J)` implies `J ≤ P`.
* `length_le_height_of_isRegular`: `J = ofList rs ≤ P` prime implies
  `k ≤ P.height` (localize at `P`, descend regularity with
  `IsWeaklyRegular.isRegular_of_isLocalization_of_mem`, then the Mathlib
  dim-drop `ringKrullDim_add_length_eq_ringKrullDim_of_isRegular` on `R_P`).
* `height_eq_length_of_mem_minimalPrimes`: minimal primes over `J` have
  height exactly `k` (Krull Hauptidealsatz
  `height_le_card_of_mem_minimalPrimes_span_finset` + the lower bound).
* `length_le_height_of_mem_associatedPrimes`: `P ∈ Ass` implies `k ≤ height`.
* `length_le_height_of_successive`: the `Fin k` A1-facing wrapper.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace LocalUnmixed

variable {R : Type*} [CommRing R]

/-- Every associated prime of `R ⧸ J` contains `J`: associated primes contain
the annihilator (`IsAssociatedPrime.annihilator_le`), and `J` annihilates the
whole quotient. -/
theorem assPrime_contains_span (J : Ideal R) (P : Ideal R)
    (hP : P ∈ associatedPrimes R (R ⧸ J)) : J ≤ P := by
  have hA : IsAssociatedPrime P (R ⧸ J) := hP
  have hle := IsAssociatedPrime.annihilator_le hA
  rw [Submodule.annihilator_top] at hle
  refine le_trans ?_ hle
  intro r hr
  rw [Module.mem_annihilator]
  intro q
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  change r • Ideal.Quotient.mk J a = (0 : R ⧸ J)
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem, mul_comm r a, ← smul_eq_mul]
  exact J.smul_mem a hr

/-- Lower height bound: a prime containing a regular sequence of length `k`
has height at least `k`. Proof: localize at `P` (so `height P = dim R_P`),
the sequence stays regular on `R_P`
(`IsWeaklyRegular.isRegular_of_isLocalization_of_mem`), and the Mathlib
local dim-drop gives `dim R_P ≥ k`. -/
theorem length_le_height_of_isRegular [IsNoetherianRing R] [IsLocalRing R]
    (rs : List R) (reg : RingTheory.Sequence.IsRegular R rs)
    (P : Ideal R) [P.IsPrime] (hle : Ideal.ofList rs ≤ P) :
    (rs.length : WithBot ℕ∞) ≤ P.height := by
  have hmem : ∀ r ∈ rs, r ∈ P := fun r hr => hle (Ideal.subset_span hr)
  have regS : RingTheory.Sequence.IsRegular (Localization.AtPrime P)
      (rs.map (algebraMap R (Localization.AtPrime P))) :=
    reg.toIsWeaklyRegular.isRegular_of_isLocalization_of_mem _ P hmem
  have hdrop := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular
    (rs.map (algebraMap R (Localization.AtPrime P))) regS
  rw [List.length_map] at hdrop
  have hne : Ideal.ofList (rs.map (algebraMap R (Localization.AtPrime P))) ≠ ⊤ := by
    intro hcon
    apply regS.2
    rw [hcon]
    simp
  have hnontriv : Nontrivial
      (Localization.AtPrime P ⧸ Ideal.ofList (rs.map (algebraMap R (Localization.AtPrime P)))) :=
    Ideal.Quotient.nontrivial_iff.mpr hne
  have hne2 : Nonempty
      (PrimeSpectrum
        (Localization.AtPrime P ⧸
          Ideal.ofList (rs.map (algebraMap R (Localization.AtPrime P))))) :=
    PrimeSpectrum.nonempty_iff_nontrivial.mpr hnontriv
  have h0 : (0 : WithBot ℕ∞) ≤
      ringKrullDim
        (Localization.AtPrime P ⧸
          Ideal.ofList (rs.map (algebraMap R (Localization.AtPrime P)))) :=
    @Order.krullDim_nonneg _ _ hne2
  have hle2 : (rs.length : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime P) := by
    calc (rs.length : WithBot ℕ∞) = 0 + (rs.length : WithBot ℕ∞) := by simp
      _ ≤ ringKrullDim _ + (rs.length : WithBot ℕ∞) := add_le_add_left h0 _
      _ = ringKrullDim (Localization.AtPrime P) := hdrop
  have hH : P.height = ringKrullDim (Localization.AtPrime P) :=
    (IsLocalization.AtPrime.ringKrullDim_eq_height P (Localization.AtPrime P)).symm
  rwa [hH]

/-- Minimal primes over a `k`-element regular span have height exactly `k`:
at most `k` by Krull's Hauptidealsatz
(`height_le_card_of_mem_minimalPrimes_span_finset`), at least `k` by the
lower bound. -/
theorem height_eq_length_of_mem_minimalPrimes [IsNoetherianRing R] [IsLocalRing R]
    (rs : List R) (reg : RingTheory.Sequence.IsRegular R rs)
    (P : Ideal R) [P.IsPrime] (hP : P ∈ (Ideal.ofList rs).minimalPrimes) :
    P.height = rs.length := by
  classical
  have hmin : (Ideal.ofList rs).IsMinimalPrime P := hP
  apply le_antisymm
  · have hset : ({ x | x ∈ rs } : Set R) = ↑rs.toFinset := by
      ext x
      simp only [Set.mem_ofPred_eq, Finset.mem_coe, List.mem_toFinset]
    have hspan : Ideal.ofList rs = Ideal.span (↑rs.toFinset : Set R) := by
      change Ideal.span { x | x ∈ rs } = _
      rw [hset]
    rw [hspan] at hP
    have hKrull := Ideal.height_le_card_of_mem_minimalPrimes_span_finset hP
    calc P.height ≤ (rs.toFinset.card : ℕ∞) := hKrull
      _ ≤ (rs.length : ℕ∞) := by exact_mod_cast List.toFinset_card_le rs
  · exact_mod_cast length_le_height_of_isRegular rs reg P hmin.le

/-- Associated primes of `R ⧸ ofList rs` have height at least `k`
(`assPrime_contains_span` + the lower bound). The reverse inequality is false
in general (see the module docstring); it needs CM-ness. -/
theorem length_le_height_of_mem_associatedPrimes [IsNoetherianRing R] [IsLocalRing R]
    (rs : List R) (reg : RingTheory.Sequence.IsRegular R rs)
    (P : Ideal R) [P.IsPrime]
    (hP : P ∈ associatedPrimes R (R ⧸ Ideal.ofList rs)) :
    (rs.length : WithBot ℕ∞) ≤ P.height :=
  length_le_height_of_isRegular rs reg P (assPrime_contains_span _ _ hP)

/-- `Fin k` wrapper through the A1 bridge: successive SMul-regularity plus
properness gives the lower height bound for `Ass(R ⧸ span (range q))`. -/
theorem length_le_height_of_successive [IsNoetherianRing R] [IsLocalRing R]
    {k : ℕ} (q : Fin k → R)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (hproper : (⊤ : Submodule R R) ≠ Ideal.ofList (List.ofFn q) • ⊤)
    (P : Ideal R) [P.IsPrime]
    (hP : P ∈ associatedPrimes R (R ⧸ Ideal.span (Set.range q))) :
    (k : WithBot ℕ∞) ≤ P.height := by
  have hreg := RegularityBridge.isRegular_ofFn_of_successive q hsucc hproper
  rw [RegularityBridge.span_range_eq_ofList_ofFn] at hP
  have h := length_le_height_of_mem_associatedPrimes (List.ofFn q) hreg P hP
  have hlen : (List.ofFn q).length = k := List.length_ofFn
  rw [hlen] at h
  exact h

/-! ## References

Mathlib (`Mathlib/RingTheory/Ideal/AssociatedPrime/Basic.lean`):
* `associatedPrimes`, `IsAssociatedPrime`,
  `IsAssociatedPrime.annihilator_le` (all root namespace).
Mathlib (`Mathlib/RingTheory/Ideal/Maps.lean`):
* `Submodule.annihilator_top`, `Module.mem_annihilator`.
Mathlib (`Mathlib/RingTheory/Regular/Flat.lean`):
* `RingTheory.Sequence.IsWeaklyRegular.isRegular_of_isLocalization_of_mem`.
Mathlib (`Mathlib/RingTheory/KrullDimension/Regular.lean`):
* `ringKrullDim_add_length_eq_ringKrullDim_of_isRegular`.
Mathlib (`Mathlib/RingTheory/Ideal/Height.lean`):
* `IsLocalization.AtPrime.ringKrullDim_eq_height`.
Mathlib (`Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean`):
* `Ideal.height_le_card_of_mem_minimalPrimes_span_finset`.
Mathlib (`Mathlib/RingTheory/Ideal/MinimalPrime/Basic.lean`):
* `Ideal.IsMinimalPrime.le`.
Mathlib (`Mathlib/RingTheory/Ideal/Quotient/Defs.lean`):
* `Ideal.Quotient.mk_surjective`, `Ideal.Quotient.eq_zero_iff_mem`.
Mathlib (`Mathlib/RingTheory/Ideal/Quotient/Operations.lean`):
* `Ideal.Quotient.algebraMap_eq`.
Mathlib (`Mathlib/Order/KrullDimension.lean`):
* `Order.krullDim_nonneg` (needs `Nonempty (PrimeSpectrum _)`).
Mathlib (`Mathlib/RingTheory/Spectrum/Prime/Basic.lean`):
* `PrimeSpectrum.nonempty_iff_nontrivial`.
Mathlib (quotient nontriviality, used via `Ideal.Quotient.nontrivial_iff`).
Mathlib (`Mathlib/RingTheory/Ideal/Span.lean`): `Ideal.subset_span`.
Lean core / Batteries (`List`): `List.length_ofFn`, `List.mem_toFinset`,
`List.toFinset_card_le`, `List.length_map`.
Project
(`Formalization/Appendix_FixedPoint/BezoutChain/
Regularity/Avoid/RegularityBridge.lean`, chunk A1):
* `RegularityBridge.SuccessiveSMulRegular`,
  `RegularityBridge.isRegular_ofFn_of_successive`,
  `RegularityBridge.span_range_eq_ofList_ofFn`.
-/

end LocalUnmixed
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
