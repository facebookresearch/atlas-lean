/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.RegularityBridge
import Mathlib.RingTheory.Ideal.Lattice
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# Localized dimension drop for regular sequences
For a commutative ring `R`, a family `q : Fin k → R` carrying successive
SMul-regularity data (`RegularityBridge.SuccessiveSMulRegular`, chunk A1), and a prime
`P` containing `Ideal.span (Set.range q)`, the images of `q` in the localization
at `P` still form a successive-regular family
(`successiveSMulRegular_map_atPrime`), and Krull dimension drops by exactly `k`
there (`ringKrullDim_atPrime_quotient_span_add_of_successive`), via Mathlib's
local lemma `ringKrullDim_add_length_eq_ringKrullDim_of_isRegular`.

## Scope note: why localized, not global

The full global equality `ringKrullDim (R ⧸ span) + k = ringKrullDim R` for a
general Noetherian `R` is false, so no sup-over-localizations argument can prove
it. Counterexample: `R = k[u,v,w] × k[t]` (for a field `k`), `x = (1, t)`. Then `x`
is regular (`(1,t) * (a,b) = 0` forces `a = 0`, `b = 0`), `R ⧸ span {x} ≅ k`
has dimension `0`, but `dim R = 3`. The dimension-achieving maximal ideal
`(u,v,w) × k[t]` avoids `x`. (A "sup over minimal primes" formulation cannot see
it either: localizing at minimal primes of `R` gives dimension `0` rings.)

Chunk A4 only ever needs the localized form: it localizes at `P ∈ Ass(R ⧸ J)`
with `J = span (Set.range q) ⊆ P` and works inside `R_P`, where Mathlib's local
lemma fires. That is exactly what this file delivers:
`successiveSMulRegular_map_atPrime` feeds A1's bridge
(`RegularityBridge.isRegular_ofFn_of_successive`) inside `R_P`, and
`ringKrullDim_atPrime_quotient_span_add_of_successive` records the resulting
dimension equation for A4's use.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace RegularSequenceDimDrop

variable {R : Type*} [CommRing R]

/-- An ideal times `⊤` is the ideal itself, as submodules. -/
theorem span_smul_top (s : Set R) :
    Ideal.span s • (⊤ : Submodule R R) = ((Ideal.span s : Ideal R) : Submodule R R) := by
  rw [Submodule.span_smul_eq, Submodule.set_smul_top_eq_span]

variable {P : Ideal R} [P.IsPrime]

/-- Regularity on `R ⧸ I` implies regularity of the image on `S ⧸ I.map f` for
a localization `f : R → S` at (the complement of) a prime. The proof is by
fractions: writing `s = a / t`, `(f c) * s ∈ I.map f` unfolds (via
`IsLocalization.algebraMap_mem_map_algebraMap_iff`) to `m * (c * a) ∈ I` for
some `m` in the submonoid, regularity on `R ⧸ I` gives `m * a ∈ I`, and the
denominators `m`, `t` are units in `S`. -/
private theorem isSMulRegular_quotient_map_atPrime
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.AtPrime S P]
    (I : Ideal R) (c : R)
    (hreg : IsSMulRegular (R ⧸ ((I : Submodule R R))) c) :
    IsSMulRegular (S ⧸ (((I.map (algebraMap R S)) : Ideal S) : Submodule S S))
      (algebraMap R S c) := by
  rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
  intro s hs
  have hs' : (algebraMap R S c) * s ∈ I.map (algebraMap R S) := hs
  obtain ⟨⟨a, t⟩, hst⟩ := IsLocalization.surj P.primeCompl s
  have hxa : (algebraMap R S) (c * a) ∈ I.map (algebraMap R S) := by
    have h1 : ((algebraMap R S c) * s) * (algebraMap R S (t : R)) ∈
        I.map (algebraMap R S) :=
      Ideal.mul_mem_right _ _ hs'
    rw [mul_assoc, hst, ← map_mul] at h1
    exact h1
  obtain ⟨m, hm, hmem⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff P.primeCompl S I (c * a)).mp hxa
  have hma : m * a ∈ I := by
    have hsmul : c • (m * a) ∈ ((I : Submodule R R)) := by
      rw [smul_eq_mul]
      have hcalc : c * (m * a) = m * (c * a) := by ring
      rw [hcalc]
      exact hmem
    exact mem_of_isSMulRegular_quotient_of_smul_mem hreg hsmul
  have hfin : (algebraMap R S m) * ((algebraMap R S (t : R)) * s) ∈
      I.map (algebraMap R S) := by
    have hts : (algebraMap R S (t : R)) * s = (algebraMap R S) a := by
      rw [mul_comm]
      exact hst
    rw [hts, ← map_mul]
    exact Ideal.mem_map_of_mem _ hma
  have hunit_m : IsUnit (algebraMap R S m) := IsLocalization.map_units S ⟨m, hm⟩
  have hunit_t : IsUnit (algebraMap R S (t : R)) := IsLocalization.map_units S t
  exact (Ideal.unit_mul_mem_iff_mem _ hunit_t).mp
    ((Ideal.unit_mul_mem_iff_mem _ hunit_m).mp hfin)

/-- Successive SMul-regularity (chunk A1's bridge input) is preserved under
localization at a prime: no hypothesis on the prime is needed. -/
theorem successiveSMulRegular_map_atPrime
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.AtPrime S P]
    {k : ℕ} (q : Fin k → R)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q) :
    RegularityBridge.SuccessiveSMulRegular (algebraMap R S ∘ q) := by
  intro i
  have h := hsucc i
  rw [span_smul_top] at h
  have hmap : (Ideal.span (Set.image q { j | j.val < i.val })).map (algebraMap R S)
      = Ideal.span (Set.image (algebraMap R S ∘ q) { j | j.val < i.val }) := by
    rw [Ideal.map_span]
    exact congrArg Ideal.span (Set.image_image _ _ _)
  have hJ : (((Ideal.span (Set.image q { j | j.val < i.val })).map
      (algebraMap R S)) : Submodule S S)
      = Ideal.span (Set.image (algebraMap R S ∘ q) { j | j.val < i.val }) • ⊤ := by
    rw [hmap, span_smul_top]
  have hregS := isSMulRegular_quotient_map_atPrime (P := P) S _ (q i) h
  rwa [hJ] at hregS

/-- Localized dimension drop: for a successive-regular family `q` whose span
lies in `P`, dimension drops by exactly `k` in `Localization.AtPrime P`.
This is the exact consequence chunk A4 needs: it localizes at
`P ∈ Ass(R ⧸ J)` and applies Mathlib's local lemma inside `R_P`.
The `[IsNoetherianRing R]` instance keeps `R_P` Noetherian for that
lemma (`IsLocalization.isNoetherianRing`). -/
theorem ringKrullDim_atPrime_quotient_span_add_of_successive
    [IsNoetherianRing R]
    {k : ℕ} (q : Fin k → R)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (hJP : Ideal.span (Set.range q) ≤ P) :
    ringKrullDim (Localization.AtPrime P ⧸
        Ideal.span (Set.range (algebraMap R (Localization.AtPrime P) ∘ q))) + k
      = ringKrullDim (Localization.AtPrime P) := by
  have hsuccS :=
    successiveSMulRegular_map_atPrime (P := P) (Localization.AtPrime P) q hsucc
  have hmem : ∀ i, algebraMap R (Localization.AtPrime P) (q i)
      ∈ IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
    intro i
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P]
    exact hJP (Ideal.subset_span (Set.mem_range_self i))
  have hle : Ideal.ofList (List.ofFn (algebraMap R (Localization.AtPrime P) ∘ q)) •
        (⊤ : Submodule (Localization.AtPrime P) (Localization.AtPrime P))
      ≤ ((IsLocalRing.maximalIdeal (Localization.AtPrime P) :
        Ideal (Localization.AtPrime P)) :
        Submodule (Localization.AtPrime P) (Localization.AtPrime P)) := by
    rw [← RegularityBridge.span_range_eq_ofList_ofFn, span_smul_top]
    exact_mod_cast Ideal.span_le.mpr (Set.range_subset_iff.mpr hmem)
  have hproperS : (⊤ : Submodule (Localization.AtPrime P) (Localization.AtPrime P))
      ≠ Ideal.ofList (List.ofFn (algebraMap R (Localization.AtPrime P) ∘ q)) • ⊤ := by
    intro hcon
    have hmem1 : (1 : Localization.AtPrime P)
        ∈ Ideal.ofList (List.ofFn (algebraMap R (Localization.AtPrime P) ∘ q)) •
          (⊤ : Submodule (Localization.AtPrime P) (Localization.AtPrime P)) := by
      rw [← hcon]
      exact Submodule.mem_top
    have h1mem : (1 : Localization.AtPrime P)
        ∈ IsLocalRing.maximalIdeal (Localization.AtPrime P) := hle hmem1
    have htop : IsLocalRing.maximalIdeal (Localization.AtPrime P) = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ h1mem isUnit_one
    exact Ideal.IsMaximal.ne_top inferInstance htop
  have hregS := RegularityBridge.isRegular_ofFn_of_successive _ hsuccS hproperS
  have hdim := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular _ hregS
  rw [← RegularityBridge.span_range_eq_ofList_ofFn, List.length_ofFn] at hdim
  exact hdim

/-! ## References

Mathlib (`Mathlib/RingTheory/KrullDimension/Regular.lean`):
* `ringKrullDim_add_length_eq_ringKrullDim_of_isRegular` (needs
  `[IsLocalRing R]` — the reason this file localizes before applying it).

Mathlib (`Mathlib/RingTheory/Regular/RegularSequence.lean`):
* `RingTheory.Sequence.IsRegular`, `Ideal.ofList` (consumed via chunk A1).

Mathlib (`Mathlib/RingTheory/Regular/IsSMulRegular.lean`):
* `isSMulRegular_quotient_iff_mem_of_smul_mem`,
  `mem_of_isSMulRegular_quotient_of_smul_mem`.

Mathlib (`Mathlib/RingTheory/Localization/Defs.lean`):
* `IsLocalization.surj`, `IsLocalization.map_units`.

Mathlib (`Mathlib/RingTheory/Localization/Ideal.lean`):
* `IsLocalization.algebraMap_mem_map_algebraMap_iff`.

Mathlib (`Mathlib/RingTheory/Localization/AtPrime/Basic.lean`):
* `Localization.AtPrime`, `IsLocalization.AtPrime.to_map_mem_maximal_iff`,
  instances `IsLocalization.AtPrime.isLocalRing`,
  `IsLocalization.isNoetherianRing` (for `Localization.AtPrime P`).

Mathlib (`Mathlib/RingTheory/Ideal/Maps.lean`):
* `Ideal.map_span`, `Ideal.mem_map_of_mem`.

Mathlib (`Mathlib/RingTheory/Ideal/Span.lean`):
* `Ideal.subset_span`, `Ideal.span_le`.

Mathlib (`Mathlib/RingTheory/Ideal/Defs.lean`):
* `Ideal.unit_mul_mem_iff_mem`.

Mathlib (`Mathlib/RingTheory/Ideal/Operations.lean`):
* `Submodule.span_smul_eq`, `Submodule.set_smul_top_eq_span`.

Local
(`Formalization/Appendix_FixedPoint/BezoutChain/
Regularity/Avoid/RegularityBridge.lean`, chunk A1):
* `RegularityBridge.SuccessiveSMulRegular`,
  `RegularityBridge.isRegular_ofFn_of_successive`,
  `RegularityBridge.span_range_eq_ofList_ofFn`.
-/

end RegularSequenceDimDrop
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
