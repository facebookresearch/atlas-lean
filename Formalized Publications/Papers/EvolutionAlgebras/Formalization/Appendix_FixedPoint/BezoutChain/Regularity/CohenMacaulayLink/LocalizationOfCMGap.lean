/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Appendix_FixedPoint.BezoutChain.Regularity.Grade.GradeDepthFragment
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.RegularityBridge
import Appendix_FixedPoint.BezoutChain.Dimension.RegularSequenceDimDrop
import Appendix_FixedPoint.BezoutChain.Regularity.Unmixed.BabyAuslanderBuchsbaum
import Appendix_FixedPoint.BezoutChain.Regularity.CohenMacaulayLink.QuotientByRegularIsCM
import Appendix_FixedPoint.BezoutChain.Regularity.CohenMacaulayLink.CMPositiveDimHasDepth
import Appendix_FixedPoint.BezoutChain.Regularity.CohenMacaulayLink.CMDepthSubstitution
import Appendix_FixedPoint.BezoutChain.Regularity.CohenMacaulayLink.CMQuotientFull

/-!
# C3a gap: localization-of-CM content
`GapBase` finite-dim is closed (`AssociatedPrimes.FiniteDimDischarge`) — the
`[GapBase]`-endgame below is discharged end-to-end by
`c3aGapAll_of_gapBaseFin`.

Proves the `C3aGapAll` block: in a Noetherian local ring `S`
with `C3.IsCM S`, regular sequences of every length `≤ height p` exist inside
the maximal ideal of `S_p`, for every prime `p`. Route: maximal regular
sequence in `p` + localize + `[GapBase]` endgame + prefixes (no
induction, no finite-dim hypothesis).

## Status: partial (exact residual stated)

* Proved (unconditional): `localized_ofFn_isRegular` (L2, via BabyAuslanderBuchsbaum),
  `length_le_height_of_localized` (L3, GradeSet + grade ≤ dim + GHT),
  `isCM_quotient_of_successive` (Step-3 `T`-is-CM via F7-subst),
  `prime_map_quotient_of_le` (`p'`-is-prime via C3 comap helpers),
  `c3aGap_of_maximalLength` (L6 prefixes), and the L0 assembly.
* Conditional: `maximalLength_eq_height` (L5 endgame) and `c3aGapAll_of_residuals`
  (L0) on `[GapBase] + [MaximalRegularSequenceExists] + [LocQuotDimEq]`.
* Residual: `GapBase` (sole mathematical residual — general CM
  theory); `MaximalRegularSequenceExists` (implementer fallback,
  provable ~100-200 lines); `LocQuotDimEq` (iso block,
  follows from the standard `(S/J)_{P̄} ≃ S_P/J_P` ring iso + GHT).

## Restricted identifiers

This file uses no graded machinery and no crux-ring members: it consumes
only mathlib + `GradeDepthFragment` + `RegularityBridge` + `RegularSequenceDimDrop` +
`BabyAuslanderBuchsbaum` +
C2-loc + F7-subst + the C3/C1Full target shapes (a grep for
the restricted identifiers is empty here and in each consumed file).
Consumed files are import-clean. Verification:
forbidden-identifier grep empty + `#print axioms` on every theorem.

## Status

`GapBase`, `MaximalRegularSequenceExists`, `LocQuotDimEq`: residual (explicit binders).
All lemmas: unconditional. `maximalLength_eq_height`, `c3aGapAll_of_residuals`:
conditional-exact on the three stated residuals.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace LocalizationOfCMGap

open RingTheory.Sequence

universe u

/-! ## Residual register (explicit binders only) -/

/-- `[GapBase]` (design note §7, sole mathematical residual): in a CM local ring, a
prime of all-zerodivisors has height 0. Equivalent to CM-unmixedness (design note
§5). C3-`IsCM` copy feeds C3-shaped binders. -/
def GapBase : Prop :=
  ∀ (S : Type*) [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    (p : Ideal S) [p.IsPrime],
    ringKrullDim S < ⊤ → -- finite-dim fence (GapBaseFin)
    CMPositiveDimHasDepth.IsCM S →
    (∀ y ∈ p, ¬ IsSMulRegular S y) → p.height = 0

/-- `[MaximalRegularSequenceExists]` (design note §7 implementer fallback, provable ~100-200 lines):
a maximal successive-regular sequence exists inside every prime `p`
(bounded lengths via L2+L3+GHT + classical max + snoc-extension). -/
def MaximalRegularSequenceExists : Prop :=
  ∀ (S : Type*) [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    (p : Ideal S) [p.IsPrime],
    ∃ (r : ℕ) (x : Fin r → S),
      RegularityBridge.SuccessiveSMulRegular x ∧ (∀ i, x i ∈ p) ∧
      ∀ z ∈ p, ¬ IsSMulRegular (S ⧸ Ideal.span (Set.range x))
        (Ideal.Quotient.mk (Ideal.span (Set.range x)) z)

/-- `[LocQuotDimEq]` (iso block): the Krull dimension of the
quotient of `S_p` by a localized `ofFn` family equals the height of the
pushed-forward prime `map mk p` in `T = S ⧸ span(range x)`. Follows from the
standard localized-quotient ring isomorphism `(S/J)_{P̄} ≃ S_P/J_P` (whose
`LinearEquiv`-to-`RingEquiv` upgrade plus submonoid correspondence is the
underpriced block) + GHT on both sides. -/
def LocQuotDimEq : Prop :=
  ∀ (S : Type*) [CommRing S] [IsNoetherianRing S]
    (p : Ideal S) [p.IsPrime] {r : ℕ} (x : Fin r → S),
    (∀ i, x i ∈ p) →
    ringKrullDim (Localization.AtPrime p ⧸
        Ideal.ofList (List.ofFn (algebraMap S (Localization.AtPrime p) ∘ x)))
      = ((Ideal.map (Ideal.Quotient.mk (Ideal.span (Set.range x))) p).height :
        WithBot ℕ∞)

/-! ## Small helpers: primes vs the maximal ideal, properness -/

/-- A prime is contained in the maximal ideal of a local ring (its elements
are nonunits, else the prime is top). -/
theorem prime_le_maximalIdeal {S : Type u} [CommRing S] [IsLocalRing S]
    (p : Ideal S) [p.IsPrime] : p ≤ IsLocalRing.maximalIdeal S := by
  intro y hy
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  exact (inferInstance : p.IsPrime).ne_top (Ideal.eq_top_of_isUnit_mem _ hy hu)

#print axioms prime_le_maximalIdeal

/-- An ideal inside the maximal ideal is proper as a submodule (`1` would
otherwise land in the maximal ideal, forcing it to top). -/
theorem top_ne_coe_of_le_maximal {S : Type u} [CommRing S] [IsLocalRing S]
    (J : Ideal S) (hle : J ≤ IsLocalRing.maximalIdeal S) :
    (⊤ : Submodule S S) ≠ (J : Submodule S S) := by
  intro hcon
  have h1 : (1 : S) ∈ (J : Submodule S S) := hcon ▸ Submodule.mem_top
  have h1m : (1 : S) ∈ IsLocalRing.maximalIdeal S := hle h1
  have htop : IsLocalRing.maximalIdeal S = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ h1m isUnit_one
  exact Ideal.IsMaximal.ne_top inferInstance htop

#print axioms top_ne_coe_of_le_maximal

/-! ## L2 (localize) + L3 (length bound) -/

/-- L2 (provable, ~5 lines): the successive-regular family localizes to a
length-`r` regular `ofFn` family inside `𝔪(S_p)`. Direct invocation of
`BabyAuslanderBuchsbaum.localized_isRegular_ofFn` via span-monotonicity. -/
theorem localized_ofFn_isRegular {S : Type u} [CommRing S] [IsNoetherianRing S]
    (p : Ideal S) [p.IsPrime] {r : ℕ} (x : Fin r → S)
    (hsucc : RegularityBridge.SuccessiveSMulRegular x)
    (hmem : ∀ i, x i ∈ p) :
    IsRegular (Localization.AtPrime p)
        (List.ofFn (algebraMap S (Localization.AtPrime p) ∘ x)) ∧
    ∀ y ∈ List.ofFn (algebraMap S (Localization.AtPrime p) ∘ x),
      y ∈ IsLocalRing.maximalIdeal (Localization.AtPrime p) := by
  apply BabyAuslanderBuchsbaum.localized_isRegular_ofFn p x hsucc
  exact Ideal.span_le.mpr (Set.range_subset_iff.mpr hmem)

#print axioms localized_ofFn_isRegular

/-- L3 (provable): the localized length-`r` sequence witnesses
`(r : ℕ∞) ≤ height p` via `GradeSet` (`mem_gradeSet_of_isRegular` +
`le_grade_of_mem_gradeSet`) + `grade_le_ringKrullDim` + GHT. -/
theorem length_le_height_of_localized {S : Type u} [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] (p : Ideal S) [p.IsPrime] {r : ℕ} (x : Fin r → S)
    (hsucc : RegularityBridge.SuccessiveSMulRegular x)
    (hmem : ∀ i, x i ∈ p) :
    (r : ℕ∞) ≤ p.height := by
  obtain ⟨hreg, hmemloc⟩ := localized_ofFn_isRegular p x hsucc hmem
  have hlen : (List.ofFn (algebraMap S (Localization.AtPrime p) ∘ x)).length = r :=
    List.length_ofFn
  have hgrade : ((r : ℕ) : ℕ∞)
      ≤ GradeDepthFragment.grade _ _ (IsLocalRing.maximalIdeal _) :=
    GradeDepthFragment.le_grade_of_mem_gradeSet _
      (GradeDepthFragment.mem_gradeSet_of_isRegular _ _ hlen hmemloc hreg)
  have hGHT : ringKrullDim (Localization.AtPrime p)
      = ((p.height : ℕ∞) : WithBot ℕ∞) :=
    IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p)
  have hle : ((((r : ℕ) : ℕ∞)) : WithBot ℕ∞)
      ≤ ringKrullDim (Localization.AtPrime p) :=
    calc ((((r : ℕ) : ℕ∞)) : WithBot ℕ∞)
        ≤ ((GradeDepthFragment.grade _ _ (IsLocalRing.maximalIdeal _) : ℕ∞) :
          WithBot ℕ∞) :=
          WithBot.coe_le_coe.mpr hgrade
      _ ≤ ringKrullDim (Localization.AtPrime p) :=
          GradeDepthFragment.grade_le_ringKrullDim _
  rw [hGHT] at hle
  exact WithBot.coe_le_coe.mp hle

#print axioms length_le_height_of_localized

/-! ## Step-3 setup: `T` is local Noetherian CM, `p'` is prime -/

/-- Properness descends along `ofList` inclusion: if the big span is proper,
so is the small one (used for L6 take-prefixes). -/
theorem top_ne_smul_of_le_of_top_ne {M : Type u} [CommRing M] {a b : List M}
    (hle : Ideal.ofList a ≤ Ideal.ofList b)
    (h : (⊤ : Submodule M M) ≠ Ideal.ofList b • ⊤) :
    (⊤ : Submodule M M) ≠ Ideal.ofList a • ⊤ := by
  intro hcon
  apply h
  have hle2 : Ideal.ofList a • (⊤ : Submodule M M) ≤ Ideal.ofList b • ⊤ :=
    Submodule.smul_mono_left hle
  rw [← hcon] at hle2
  exact (top_le_iff.mp hle2).symm

#print axioms top_ne_smul_of_le_of_top_ne

/-- Step-3 `T` setup (provable): the quotient `T = S ⧸ J` by a
maximal-ideal successive-regular family is CM, for any `J` equal to
`span(range x)` (generalized so `subst` transports across the
`span-ofList`-vs-`span-range` identification). Feeds F7-subst
(`isCM_quotient_span_of_isRegular_subst`, unconditional) with the `ofFn`
regular sequence + properness, then the C2/C3 `IsCM` bridge. -/
theorem isCM_quotient_of_successive {S : Type u} [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] (p : Ideal S) [p.IsPrime]
    (hCM : CMPositiveDimHasDepth.IsCM S) {r : ℕ} {x : Fin r → S}
    (hsucc : RegularityBridge.SuccessiveSMulRegular x)
    (hmem : ∀ i, x i ∈ p)
    (J : Ideal S) (hJJ : J = Ideal.span (Set.range x))
    [IsLocalRing (S ⧸ J)] :
    CMPositiveDimHasDepth.IsCM (S ⧸ J) := by
  have hmemS : ∀ y ∈ List.ofFn x, y ∈ IsLocalRing.maximalIdeal S := by
    intro y hy
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
    exact (prime_le_maximalIdeal p) (hmem i)
  have hle' : Ideal.span {x_ | x_ ∈ List.ofFn x} ≤ IsLocalRing.maximalIdeal S :=
    Ideal.span_le.mpr (fun y hy => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
      exact (prime_le_maximalIdeal p) (hmem i))
  have hproper : (⊤ : Submodule S S) ≠ Ideal.ofList (List.ofFn x) • ⊤ := by
    change (⊤ : Submodule S S) ≠ Ideal.span {x_ | x_ ∈ List.ofFn x} • ⊤
    rw [RegularSequenceDimDrop.span_smul_top]
    exact top_ne_coe_of_le_maximal _ hle'
  have hregS : IsRegular S (List.ofFn x) :=
    RegularityBridge.isRegular_ofFn_of_successive x hsucc hproper
  have : IsLocalRing (S ⧸ Ideal.span {x_ | x_ ∈ List.ofFn x}) :=
    QuotientByRegularIsCM.isLocalRing_quotient_of_le_maximal _ hle'
  have hCM2 : QuotientByRegularIsCM.IsCM (S ⧸ Ideal.span {x_ | x_ ∈ List.ofFn x}) :=
    CMDepthSubstitution.isCM_quotient_span_of_isRegular_subst
      (List.ofFn x) hmemS hregS
      (CMDepthSubstitution.isCM_c2_of_c3 hCM)
  have hJold : Ideal.span {x_ | x_ ∈ List.ofFn x}
      = Ideal.span (Set.range x) := by
    congr 1
    ext y
    exact List.mem_ofFn
  have hJ : Ideal.span {x_ | x_ ∈ List.ofFn x} = J := hJold.trans hJJ.symm
  subst hJ
  exact CMDepthSubstitution.isCM_c3_of_c2 hCM2

#print axioms isCM_quotient_of_successive

/-- Step-3 `p'`-is-prime (provable, ~15 lines): pushing a prime forward along
a quotient by an ideal it contains stays prime, via the C3 comap-collapse
helpers (`comap_map_quotient_mk_eq_self` +
`isPrime_of_comap_isPrime_of_surjective`). -/
theorem prime_map_quotient_of_le {S : Type u} [CommRing S]
    (J : Ideal S) (p : Ideal S) [p.IsPrime] (hle : J ≤ p) :
    (Ideal.map (Ideal.Quotient.mk J) p).IsPrime := by
  apply CMPositiveDimHasDepth.isPrime_of_comap_isPrime_of_surjective
    (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  rw [CMPositiveDimHasDepth.comap_map_quotient_mk_eq_self J p hle]
  exact inferInstance

#print axioms prime_map_quotient_of_le

/-! ## L5 endgame: maximal length = height (on `[GapBase]` + `[LocQuotDimEq]`) -/

/-- L5-endgame (conditional on `[GapBase]` + `[LocQuotDimEq]`): a maximal
successive-regular sequence in `p` has length exactly `height p`. Maximality
says every element of `p' = map mk p` is a zerodivisor on `T`, so `[GapBase]`
at `(T, p')` gives `height_T(p') = 0`; the drop chain
`h = dim S_p = dim(S_p/(x/1)) + r = height_T(p') + r = r` closes via the
one-shot `ringKrullDim_add_length_eq_ringKrullDim_of_isRegular` (verdict
finding 6), `[LocQuotDimEq]` for the localized-quotient step, and GHT. -/
theorem maximalLength_eq_height {S : Type u} [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] (p : Ideal S) [p.IsPrime]
    (hCM : CMPositiveDimHasDepth.IsCM S)
    {r : ℕ} {x : Fin r → S}
    (hsucc : RegularityBridge.SuccessiveSMulRegular x)
    (hmem : ∀ i, x i ∈ p)
    (hmax : ∀ z ∈ p, ¬ IsSMulRegular (S ⧸ Ideal.span (Set.range x))
      (Ideal.Quotient.mk (Ideal.span (Set.range x)) z))
    (hfinS : ringKrullDim S < ⊤) -- threaded fence
    (hGB : GapBase.{u}) (hLQ : LocQuotDimEq.{u}) :
    (r : ℕ∞) = p.height := by
  have hleS : Ideal.span (Set.range x) ≤ IsLocalRing.maximalIdeal S :=
    (Ideal.span_le.mpr (Set.range_subset_iff.mpr hmem)).trans
      (prime_le_maximalIdeal p)
  have : IsLocalRing (S ⧸ Ideal.span (Set.range x)) :=
    QuotientByRegularIsCM.isLocalRing_quotient_of_le_maximal _ hleS
  have hCMT : CMPositiveDimHasDepth.IsCM (S ⧸ Ideal.span (Set.range x)) :=
    isCM_quotient_of_successive p hCM hsucc hmem _ rfl
  have hleP : Ideal.span (Set.range x) ≤ p :=
    Ideal.span_le.mpr (Set.range_subset_iff.mpr hmem)
  have : (Ideal.map (Ideal.Quotient.mk (Ideal.span (Set.range x))) p).IsPrime :=
    prime_map_quotient_of_le _ p hleP
  have hall : ∀ y ∈ Ideal.map (Ideal.Quotient.mk (Ideal.span (Set.range x))) p,
      ¬ IsSMulRegular (S ⧸ Ideal.span (Set.range x)) y := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := (Ideal.mem_map_iff_of_surjective _
      Ideal.Quotient.mk_surjective).mp hy
    exact hmax z hz
  have hfinT : ringKrullDim (S ⧸ Ideal.span (Set.range x)) < ⊤ :=
    lt_of_le_of_lt (ringKrullDim_quotient_le _) hfinS
  have hGB0 : (Ideal.map (Ideal.Quotient.mk (Ideal.span (Set.range x)))
      p).height = 0 :=
    hGB _ _ hfinT hCMT hall
  obtain ⟨hreg, _⟩ := localized_ofFn_isRegular p x hsucc hmem
  have hdrop := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular
    (List.ofFn (algebraMap S (Localization.AtPrime p) ∘ x)) hreg
  rw [List.length_ofFn] at hdrop
  have hGHT : ringKrullDim (Localization.AtPrime p)
      = ((p.height : ℕ∞) : WithBot ℕ∞) :=
    IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p)
  have hLQe := hLQ S p x hmem
  have hcalc : ((p.height : ℕ∞) : WithBot ℕ∞) =
      ((((r : ℕ) : ℕ∞)) : WithBot ℕ∞) := by
    rw [← hGHT, ← hdrop, hLQe, hGB0]
    simp
  exact (WithBot.coe_eq_coe.mp hcalc).symm

#print axioms maximalLength_eq_height

/-! ## L6 (prefixes) + L0 assembly -/

/-- L6 (provable): prefixes give every length `≤ height`. The length-`n` take
of the maximal localized sequence is regular (append-split of weak regularity
+ properness monotonicity) in `𝔪(S_p)` — exactly `C3aGap S p`. -/
theorem c3aGap_of_maximalLength {S : Type u} [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] (p : Ideal S) [p.IsPrime]
    {r : ℕ} (rs : List (Localization.AtPrime p))
    (hreg : IsRegular (Localization.AtPrime p) rs)
    (hmem : ∀ y ∈ rs, y ∈ IsLocalRing.maximalIdeal (Localization.AtPrime p))
    (hlen : rs.length = r) (heq : (r : ℕ∞) = p.height) :
    CMPositiveDimHasDepth.C3aGap S p := by
  intro n hn
  have hnr : n ≤ r := by
    have h1 : (n : ℕ∞) ≤ (r : ℕ∞) := by
      rw [heq]
      exact hn
    exact ENat.natCast_le_natCast.mp h1
  have happ : rs.take n ++ rs.drop n = rs := List.take_append_drop n rs
  have hweak : IsWeaklyRegular (Localization.AtPrime p) (rs.take n) := by
    have h2 : IsWeaklyRegular (Localization.AtPrime p) (rs.take n ++ rs.drop n) := by
      rw [happ]
      exact hreg.toIsWeaklyRegular
    exact ((isWeaklyRegular_append_iff _ _ _).mp h2).1
  have hleI : Ideal.ofList (rs.take n) ≤ Ideal.ofList rs := by
    apply Ideal.span_le.mpr
    intro y hy
    exact Ideal.subset_span (List.mem_of_mem_take hy)
  have hproper : (⊤ : Submodule (Localization.AtPrime p) (Localization.AtPrime p))
      ≠ Ideal.ofList (rs.take n) • ⊤ :=
    top_ne_smul_of_le_of_top_ne hleI hreg.top_ne_smul
  refine ⟨rs.take n, ⟨hweak, hproper⟩, ?_, ?_⟩
  · intro y hy
    exact hmem y (List.mem_of_mem_take hy)
  · rw [List.length_take, hlen, Nat.min_eq_left hnr]

#print axioms c3aGap_of_maximalLength

/-- L0 (target, conditional-exact on `[GapBase] + [MaximalRegularSequenceExists] +
[LocQuotDimEq]`): `C3aGapAll`. Discharges C3a, unmixedness, and C3-close
mechanically (design note §2/§11); the whole chain becomes conditional on the three
stated residuals. -/
theorem c3aGapAll_of_residuals (hGB : GapBase.{u}) (hMax : MaximalRegularSequenceExists.{u})
    (hLQ : LocQuotDimEq.{u}) :
    CMQuotientFull.C3aGapAll.{u} := by
  intro S _ _ _ p _ hfin hCM
  obtain ⟨r, x, hsucc, hmem, hmax⟩ := hMax S p
  have heq : (r : ℕ∞) = p.height :=
    maximalLength_eq_height p hCM hsucc hmem hmax hfin hGB hLQ
  obtain ⟨hreg, hmemloc⟩ := localized_ofFn_isRegular p x hsucc hmem
  have hlen : (List.ofFn (algebraMap S (Localization.AtPrime p) ∘ x)).length = r :=
    List.length_ofFn
  exact c3aGap_of_maximalLength p _ hreg hmemloc hlen heq

#print axioms c3aGapAll_of_residuals

end LocalizationOfCMGap
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
