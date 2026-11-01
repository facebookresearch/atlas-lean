/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.RegularityBridge
import Appendix_FixedPoint.BezoutChain.Regularity.Unmixed.HeightDrop
import Appendix_FixedPoint.BezoutChain.Regularity.Grade.GradeDepthFragment
import Appendix_FixedPoint.BezoutChain.Dimension.RegularSequenceDimDrop
import Appendix_FixedPoint.BezoutChain.Dimension.LocalUnmixed
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Regular.ProjectiveDimension
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Ideal.Height
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Baby Auslander–Buchsbaum for length-2 quotients (spike)

For a length-2 regular sequence `[x, y]` (single universe, Noetherian local
ring), this file proves the Auslander–Buchsbaum equation
`pd(M) + grade(M) = grade(R)` for `M = R ⧸ ofList [x, y]`, then assembles the
`k = 2` case of `GradeDepthFragment.GradeUnmixedBridge` from it.

## Proof shape (Matsumura, Commutative Ring Theory, §19, Theorem 19.1 steps)

Matsumura's proof of Auslander–Buchsbaum is an induction on projective
dimension: each syzygy step shifts `Ext`-vanishing by exactly one along the
long exact sequence of a short exact sequence, and the Rees theorem translates
between `Ext`-vanishing and regular sequences. For `pd ≤ 2` there are exactly
two such steps, and each step is the already-proved Rees-forward + LES-shift +
Rees-backward consumption pattern
(`GradeDepthFragment.exists_isRegular_quotSMulTop_of_isRegular_succ`, templated in
`GradeDepthFragment.lean`). The `pd ≤ 2` input itself comes directly from
`ModuleCat.projectiveDimension_quotient_eq_length` (`pd = length` from
`IsRegular`, no syzygy construction needed).

## Contents

* `exists_isRegular_nestedQuot_of_isRegular_add2` — the two-step shift: a
  length-`m+2` regular sequence on `M'` yields a length-`m` one on the nested
  quotient, via two applications of the GradeDepthFragment crux (Matsumura steps 1–2).
* `grade_nestedQuot_add_two_eq_grade` — the pair-drop equation on the nested
  quotient (`≤` half from the two-step shift, `≥` half by telescoping the
  proved single-step halves).
* `spanPairNestedEquiv` / `grade_congr_of_linearEquiv` — transport to the
  span quotient `R ⧸ ofList [x, y] • ⊤` (the form `pd` and the assembly need).
* `pd_spanPair_eq_two` — `pd = 2` from `projectiveDimension_quotient_eq_length`.
* `babyAB_pair` — the length-2 AB equation `pd + grade(M) = grade(R)`.
* `localized_isRegular_pair` — the localized successive family at `P ∈ Ass`
  is a regular pair in the maximal ideal (localization-stability +
  properness, mirroring `RegularSequenceDimDrop`).
* `locQuotEquivPair` — `LocalizedModule.AtPrime P (R ⧸ J)` is the localized
  span quotient (localization commutes with quotients +
  `LocalizedModule p R ≃ Localization p`).
* `grade_spanPair_eq_zero_of_mem_ass` — grade zero on the localized pair
  quotient from `Ass` (via the equiv above).
* `gradeUnmixedBridge_pair` — the exact `GradeUnmixedBridge` shape for
  `k = 2` that `GradeDepthFragment.unmixed_of_grade_of_depthEq` consumes: from
  `DepthEqDimAt` at `P`, baby-AB forces `dim R_P = 2`, hence `height ≤ 2`.

## References

Project (read-only):
* `Regularity/Grade/GradeDepthFragment.lean`: `grade`, `GradeSet`,
  `exists_isRegular_quotSMulTop_of_isRegular_succ` (the crux template),
  `grade_quotSMulTop_add_one_le_grade`, `grade_eq_zero_of_mem_associatedPrimes`,
  `GradeUnmixedBridge`, `DepthEqDimAt`, `unmixed_of_grade_of_depthEq`.
* `Regularity/Avoid/RegularityBridge.lean`: `SuccessiveSMulRegular`,
  `isRegular_ofFn_of_successive`, `span_range_eq_ofList_ofFn`.
* `Regularity/Unmixed/HeightDrop.lean`: `HeightDropResidualAt`.
* `Dimension/RegularSequenceDimDrop.lean`: `successiveSMulRegular_map_atPrime`,
  `span_smul_top` (plus the properness pattern for `hproperS`).
* `Dimension/LocalUnmixed.lean`: `assPrime_contains_span`.

Mathlib: `ModuleCat.projectiveDimension_quotient_eq_length`,
`ModuleCat.subsingleton_ext_of_exists_isRegular` /
`ModuleCat.exists_isRegular_of_exists_subsingleton_ext` (behind the crux),
`CategoryTheory.Abelian.Ext.covariant_sequence_exact₃'` (behind the crux),
`LinearEquiv.isRegular_congr`,
`Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner`,
`Submodule.localizedQuotientEquiv`, `IsLocalizedModule.linearEquiv`,
`Module.associatedPrimes.mem_associatedPrimes_atPrime_of_mem_associatedPrimes`,
`IsLocalization.AtPrime.ringKrullDim_eq_height`.
-/

universe u

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace BabyAuslanderBuchsbaum

open RingTheory.Sequence
open scoped Pointwise

/-! ## §1. The two-step Rees–LES shift (Matsumura steps 1–2) -/

/-- Nondegeneracy descends to the quotient: `I • ⊤ < ⊤` on `M'` plus `x ∈ I`
gives `I • ⊤ < ⊤` on `QuotSMulTop x M'`. Same comap-along-`mkQ` argument as
the `hQlt` step of the GradeDepthFragment crux (needed here for the second rung). -/
private theorem smulTop_lt_top_quotSMulTop_aux {R' M' : Type u}
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

/-- Two-step Rees–LES shift (Matsumura §19 steps 1–2 for `pd ≤ 2`): a
length-`m+2` `M'`-regular sequence in `I` yields a length-`m` regular sequence
on the nested quotient `QuotSMulTop y (QuotSMulTop x M')` in `I`. Each rung is
one application of the GradeDepthFragment crux (Rees-forward, LES dimension shift along
`smulShortComplex`, Rees-backward); the second rung additionally needs
`Module.Finite` (via `of_surjective`) and nondegeneracy descent for the
intermediate quotient. -/
theorem exists_isRegular_nestedQuot_of_isRegular_add2 {R' M' : Type u}
    [CommRing R'] [AddCommGroup M'] [Module R' M'] [IsNoetherianRing R']
    [Module.Finite R' M'] (I : Ideal R') (x y : R')
    (hxreg : IsSMulRegular M' x) (hxI : x ∈ I)
    (hyreg : IsSMulRegular (QuotSMulTop x M') y) (hyI : y ∈ I)
    (hIlt : I • (⊤ : Submodule R' M') < ⊤)
    {m : ℕ} {rs : List R'} (hlen : rs.length = m + 2)
    (hmem : ∀ r ∈ rs, r ∈ I) (hreg : IsRegular M' rs) :
    ∃ ss : List R', ss.length = m ∧ (∀ r ∈ ss, r ∈ I) ∧
      IsRegular (QuotSMulTop y (QuotSMulTop x M')) ss := by
  have hlen1 : rs.length = (m + 1) + 1 := by omega
  obtain ⟨ts, htslen, htsmem, htsreg⟩ :=
    GradeDepthFragment.exists_isRegular_quotSMulTop_of_isRegular_succ I x hxreg hxI hIlt
      hlen1 hmem hreg
  have hfinQ : Module.Finite R' (QuotSMulTop x M') :=
    Module.Finite.of_surjective (Submodule.mkQ (x • (⊤ : Submodule R' M')))
      (Submodule.mkQ_surjective _)
  have hIltQ := smulTop_lt_top_quotSMulTop_aux I x hxI hIlt
  obtain ⟨ss, hslen, hsmem, hsreg⟩ :=
    @GradeDepthFragment.exists_isRegular_quotSMulTop_of_isRegular_succ R'
      (QuotSMulTop x M') _ _ _ _ hfinQ I y hyreg hyI hIltQ _ _ htslen htsmem
      htsreg
  exact ⟨ss, hslen, hsmem, hsreg⟩

/-! ## §2. The pair-drop equation on the nested quotient -/

/-- Pair drop, `≤` half, from the two-step shift: every `M'`-regular sequence
in `I` is at most two longer than the grade of the nested quotient. Lengths
`0`/`1` are by direct bounds; length `m+2` is the shift above. -/
theorem grade_le_nestedQuot_add_two {R' M' : Type u}
    [CommRing R'] [AddCommGroup M'] [Module R' M'] [IsNoetherianRing R']
    [Module.Finite R' M'] (I : Ideal R') (x y : R')
    (hxI : x ∈ I) (hyI : y ∈ I)
    (hIlt : I • (⊤ : Submodule R' M') < ⊤)
    (hreg : IsRegular M' [x, y]) :
    GradeDepthFragment.grade R' M' I ≤
      GradeDepthFragment.grade R' (QuotSMulTop y (QuotSMulTop x M')) I + 2 := by
  have hxreg : IsSMulRegular M' x := ((isRegular_cons_iff M' x [y]).mp hreg).1
  have htail : IsRegular (QuotSMulTop x M') [y] :=
    ((isRegular_cons_iff M' x [y]).mp hreg).2
  have hyreg : IsSMulRegular (QuotSMulTop x M') y :=
    ((isRegular_cons_iff (QuotSMulTop x M') y []).mp htail).1
  refine sSup_le ?_
  rintro _ ⟨n, hnmem, rfl⟩
  obtain ⟨rs, hlen, hmem, hreg'⟩ := hnmem
  rcases n with _ | _ | m
  · simp
  · change ((1 : ℕ) : ℕ∞) ≤
        GradeDepthFragment.grade R' (QuotSMulTop y (QuotSMulTop x M')) I + 2
    calc ((1 : ℕ) : ℕ∞) ≤ (2 : ℕ∞) := by
          exact_mod_cast (by omega : (1 : ℕ) ≤ 2)
      _ ≤ GradeDepthFragment.grade R' (QuotSMulTop y (QuotSMulTop x M')) I + 2 :=
        le_add_left le_rfl
  · change (((m + 2 : ℕ)) : ℕ∞) ≤
        GradeDepthFragment.grade R' (QuotSMulTop y (QuotSMulTop x M')) I + 2
    have hlen' : rs.length = m + 2 := hlen
    obtain ⟨ss, hslen, hsmem, hsreg⟩ :=
      exists_isRegular_nestedQuot_of_isRegular_add2 I x y hxreg hxI hyreg hyI
        hIlt hlen' hmem hreg'
    have hle : ((m : ℕ) : ℕ∞) ≤
        GradeDepthFragment.grade R' (QuotSMulTop y (QuotSMulTop x M')) I :=
      GradeDepthFragment.le_grade_of_mem_gradeSet I
        (GradeDepthFragment.mem_gradeSet_of_isRegular I ss hslen hsmem hsreg)
    calc (((m + 2 : ℕ)) : ℕ∞) = ((m : ℕ) : ℕ∞) + 2 := by push_cast; ring
      _ ≤ GradeDepthFragment.grade R' (QuotSMulTop y (QuotSMulTop x M')) I + 2 := by
        gcongr

/-- Pair drop, `≥` half, by telescoping the proved single-step halves: the
nested-quotient grade plus two is at most the grade. -/
theorem nestedQuot_add_two_le_grade {R' M' : Type u}
    [CommRing R'] [AddCommGroup M'] [Module R' M'] [IsNoetherianRing R']
    [Module.Finite R' M'] (I : Ideal R') (x y : R')
    (hxI : x ∈ I) (hyI : y ∈ I)
    (hIlt : I • (⊤ : Submodule R' M') < ⊤)
    (hreg : IsRegular M' [x, y]) :
    GradeDepthFragment.grade R' (QuotSMulTop y (QuotSMulTop x M')) I + 2 ≤
      GradeDepthFragment.grade R' M' I := by
  have hxreg : IsSMulRegular M' x := ((isRegular_cons_iff M' x [y]).mp hreg).1
  have htail : IsRegular (QuotSMulTop x M') [y] :=
    ((isRegular_cons_iff M' x [y]).mp hreg).2
  have hyreg : IsSMulRegular (QuotSMulTop x M') y :=
    ((isRegular_cons_iff (QuotSMulTop x M') y []).mp htail).1
  have hIltQ := smulTop_lt_top_quotSMulTop_aux I x hxI hIlt
  have hxprop : x • (⊤ : Submodule R' M') < ⊤ := by
    calc x • (⊤ : Submodule R' M') = Ideal.span {x} • (⊤ : Submodule R' M') := by
          rw [Submodule.ideal_span_singleton_smul]
      _ ≤ I • (⊤ : Submodule R' M') :=
          Submodule.smul_mono_left ((Ideal.span_singleton_le_iff_mem I).mpr hxI)
      _ < ⊤ := hIlt
  have hyprop : y • (⊤ : Submodule R' (QuotSMulTop x M')) < ⊤ := by
    calc y • (⊤ : Submodule R' (QuotSMulTop x M')) =
          Ideal.span {y} • (⊤ : Submodule R' (QuotSMulTop x M')) := by
          rw [Submodule.ideal_span_singleton_smul]
      _ ≤ I • (⊤ : Submodule R' (QuotSMulTop x M')) :=
          Submodule.smul_mono_left ((Ideal.span_singleton_le_iff_mem I).mpr hyI)
      _ < ⊤ := hIltQ
  have hstep1 :=
    GradeDepthFragment.grade_quotSMulTop_add_one_le_grade (M := QuotSMulTop x M') I y
      hyreg hyI hyprop
  have hstep2 :=
    GradeDepthFragment.grade_quotSMulTop_add_one_le_grade (M := M') I x hxreg hxI hxprop
  calc GradeDepthFragment.grade R' (QuotSMulTop y (QuotSMulTop x M')) I + 2
      = (GradeDepthFragment.grade R' (QuotSMulTop y (QuotSMulTop x M')) I + 1) + 1 := by
        ring
    _ ≤ GradeDepthFragment.grade R' (QuotSMulTop x M') I + 1 := by gcongr
    _ ≤ GradeDepthFragment.grade R' M' I := hstep2

/-- Pair drop, full equation on the nested quotient. -/
theorem grade_nestedQuot_add_two_eq_grade {R' M' : Type u}
    [CommRing R'] [AddCommGroup M'] [Module R' M'] [IsNoetherianRing R']
    [Module.Finite R' M'] (I : Ideal R') (x y : R')
    (hxI : x ∈ I) (hyI : y ∈ I)
    (hIlt : I • (⊤ : Submodule R' M') < ⊤)
    (hreg : IsRegular M' [x, y]) :
    GradeDepthFragment.grade R' (QuotSMulTop y (QuotSMulTop x M')) I + 2 =
      GradeDepthFragment.grade R' M' I :=
  le_antisymm (nestedQuot_add_two_le_grade I x y hxI hyI hIlt hreg)
    (grade_le_nestedQuot_add_two I x y hxI hyI hIlt hreg)

/-! ## §3. Span form and the length-2 AB equation -/

/-- The span quotient by a pair is the nested `QuotSMulTop` quotient: first
peel off `x` with `quotOfListConsSMulTopEquivQuotSMulTopInner`, then identify
the singleton `ofList [y]` quotient with `QuotSMulTop y`. -/
def spanPairNestedEquiv {R' : Type u} [CommRing R'] (x y : R') :
    (R' ⧸ (Ideal.ofList [x, y] • ⊤ : Submodule R' R')) ≃ₗ[R']
      QuotSMulTop y (QuotSMulTop x R') := by
  have hsing : (Ideal.ofList [y] • ⊤ :
      Submodule R' (QuotSMulTop x R')) = y • ⊤ := by
    rw [Ideal.ofList_singleton, Submodule.ideal_span_singleton_smul]
  exact (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner R' x [y]).trans
    (Submodule.quotEquivOfEq _ _ hsing)

/-- Grade is invariant under linear equivalence, via `IsRegular` congruence
(`LinearEquiv.isRegular_congr` — membership in `I` is unchanged). -/
theorem grade_congr_of_linearEquiv {R M M₂ : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup M₂] [Module R M₂]
    (e : M ≃ₗ[R] M₂) (I : Ideal R) :
    GradeDepthFragment.grade R M I = GradeDepthFragment.grade R M₂ I := by
  have hGS : GradeDepthFragment.GradeSet R M I = GradeDepthFragment.GradeSet R M₂ I := by
    ext n
    constructor
    · rintro ⟨rs, hlen, hmem, hreg⟩
      exact ⟨rs, hlen, hmem, (e.isRegular_congr rs).mp hreg⟩
    · rintro ⟨rs, hlen, hmem, hreg⟩
      exact ⟨rs, hlen, hmem, (e.isRegular_congr rs).mpr hreg⟩
  unfold GradeDepthFragment.grade
  rw [hGS]

/-- Length-2 grade drop on the span quotient (the form `pd` and the assembly
need), transported from the nested equation. -/
theorem grade_spanPair_add_two_eq_grade {R' : Type u} [CommRing R']
    [IsNoetherianRing R'] [Module.Finite R' R'] (I : Ideal R') (x y : R')
    (hxI : x ∈ I) (hyI : y ∈ I)
    (hIlt : I • (⊤ : Submodule R' R') < ⊤) (hreg : IsRegular R' [x, y]) :
    GradeDepthFragment.grade R'
        (R' ⧸ (Ideal.ofList [x, y] • ⊤ : Submodule R' R')) I + 2 =
      GradeDepthFragment.grade R' R' I := by
  rw [grade_congr_of_linearEquiv (spanPairNestedEquiv x y) I]
  exact grade_nestedQuot_add_two_eq_grade I x y hxI hyI hIlt hreg

/-- Projective dimension of the pair quotient is exactly `2`, from
`projectiveDimension_quotient_eq_length` (`pd = length` from `IsRegular`
directly), transported across the `Shrink` and `↑ofList = ofList • ⊤`
identifications. -/
theorem pd_spanPair_eq_two {R' : Type u} [CommRing R'] [IsNoetherianRing R']
    [IsLocalRing R'] (x y : R') (hreg : IsRegular R' [x, y]) :
    CategoryTheory.projectiveDimension
        (ModuleCat.of R'
          (R' ⧸ (Ideal.ofList [x, y] • ⊤ : Submodule R' R'))) = 2 := by
  have hsmall : Small.{u} R' := small_self R'
  have hpd := ModuleCat.projectiveDimension_quotient_eq_length (R := R') [x, y] hreg
  have hsub : ((Ideal.ofList [x, y] : Ideal R') : Submodule R' R') =
      Ideal.ofList [x, y] • ⊤ :=
    (RegularSequenceDimDrop.span_smul_top _).symm
  let e : Shrink.{u} (R' ⧸ Ideal.ofList [x, y]) ≃ₗ[R']
      (R' ⧸ (Ideal.ofList [x, y] • ⊤ : Submodule R' R')) :=
    (Shrink.linearEquiv R' _).trans (Submodule.quotEquivOfEq _ _ hsub)
  rw [← CategoryTheory.projectiveDimension_eq_of_iso e.toModuleIso]
  have hlen : [x, y].length = 2 := rfl
  rw [hlen] at hpd
  exact_mod_cast hpd

/-- Baby Auslander–Buchsbaum for a length-2 quotient: with `pd = 2` (above)
and grade dropping by exactly `2` (the two Matsumura rungs), `pd` plus the
grade of the quotient equals the grade of the ring. -/
theorem babyAB_pair {R' : Type u} [CommRing R'] [IsNoetherianRing R']
    [IsLocalRing R'] [Module.Finite R' R'] (I : Ideal R') (x y : R')
    (hxI : x ∈ I) (hyI : y ∈ I)
    (hIlt : I • (⊤ : Submodule R' R') < ⊤) (hreg : IsRegular R' [x, y]) :
    CategoryTheory.projectiveDimension (ModuleCat.of R'
          (R' ⧸ (Ideal.ofList [x, y] • ⊤ : Submodule R' R'))) +
        ((GradeDepthFragment.grade R'
            (R' ⧸ (Ideal.ofList [x, y] • ⊤ : Submodule R' R')) I : ℕ∞) :
          WithBot ℕ∞) =
      ((GradeDepthFragment.grade R' R' I : ℕ∞) : WithBot ℕ∞) := by
  rw [pd_spanPair_eq_two x y hreg]
  have hdrop := grade_spanPair_add_two_eq_grade I x y hxI hyI hIlt hreg
  have hdropW :
      (((GradeDepthFragment.grade R'
            (R' ⧸ (Ideal.ofList [x, y] • ⊤ : Submodule R' R')) I + 2 :
          ℕ∞)) : WithBot ℕ∞) =
      ((GradeDepthFragment.grade R' R' I : ℕ∞) : WithBot ℕ∞) := by
    exact_mod_cast hdrop
  rw [← hdropW]
  push_cast
  rw [show ((2 : ℕ∞) : WithBot ℕ∞) = 2 from by norm_cast, add_comm]

/-! ## §4. The localized pair is regular in the maximal ideal -/

/-- The localized successive pair at `P` is a regular pair in the maximal
ideal: regularity survives localization
(`successiveSMulRegular_map_atPrime`), the maps land in the maximal ideal
since `J ≤ P`, and properness follows (mirroring `RegularSequenceDimDrop`). The
`List.ofFn` family destructures to an explicit pair via `length_eq_two`. -/
theorem localized_isRegular_pair {R : Type*} [CommRing R] [IsNoetherianRing R]
    (P : Ideal R) [P.IsPrime] (q : Fin 2 → R)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (hJP : Ideal.span (Set.range q) ≤ P) :
    ∃ x y : Localization.AtPrime P,
      List.ofFn (algebraMap R (Localization.AtPrime P) ∘ q) = [x, y] ∧
      IsRegular (Localization.AtPrime P) [x, y] ∧
      x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime P) ∧
      y ∈ IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
  have hsuccS :=
    RegularSequenceDimDrop.successiveSMulRegular_map_atPrime (P := P)
      (Localization.AtPrime P) q hsucc
  have hmem : ∀ i, algebraMap R (Localization.AtPrime P) (q i) ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
    intro i
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P]
    exact hJP (Ideal.subset_span (Set.mem_range_self i))
  have hle : Ideal.ofList (List.ofFn (algebraMap R (Localization.AtPrime P) ∘ q)) •
        (⊤ : Submodule (Localization.AtPrime P) (Localization.AtPrime P))
      ≤ ((IsLocalRing.maximalIdeal (Localization.AtPrime P) :
        Ideal (Localization.AtPrime P)) :
        Submodule (Localization.AtPrime P) (Localization.AtPrime P)) := by
    rw [← RegularityBridge.span_range_eq_ofList_ofFn, RegularSequenceDimDrop.span_smul_top]
    exact_mod_cast Ideal.span_le.mpr (Set.range_subset_iff.mpr hmem)
  have hproperS : (⊤ : Submodule (Localization.AtPrime P) (Localization.AtPrime P))
      ≠ Ideal.ofList (List.ofFn (algebraMap R (Localization.AtPrime P) ∘ q)) •
        ⊤ := by
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
  have hlen : (List.ofFn (algebraMap R (Localization.AtPrime P) ∘ q)).length = 2 :=
    List.length_ofFn
  obtain ⟨x, y, hpair⟩ := List.length_eq_two.mp hlen
  have hsub2 : Ideal.ofList (List.ofFn (algebraMap R (Localization.AtPrime P) ∘ q)) •
        (⊤ : Submodule (Localization.AtPrime P) (Localization.AtPrime P)) =
      ((Ideal.ofList (List.ofFn (algebraMap R (Localization.AtPrime P) ∘ q)) :
        Ideal (Localization.AtPrime P)) :
        Submodule (Localization.AtPrime P) (Localization.AtPrime P)) :=
    RegularSequenceDimDrop.span_smul_top _
  refine ⟨x, y, hpair, ?_, ?_, ?_⟩
  · rw [← hpair]
    exact hregS
  · have hxspan : x ∈ Ideal.ofList [x, y] := Ideal.subset_span (by simp)
    rw [← hpair] at hxspan
    have hxsmul : x ∈ Ideal.ofList
        (List.ofFn (algebraMap R (Localization.AtPrime P) ∘ q)) •
        (⊤ : Submodule (Localization.AtPrime P) (Localization.AtPrime P)) := by
      rw [hsub2]
      exact hxspan
    exact hle hxsmul
  · have hyspan : y ∈ Ideal.ofList [x, y] := Ideal.subset_span (by simp)
    rw [← hpair] at hyspan
    have hysmul : y ∈ Ideal.ofList
        (List.ofFn (algebraMap R (Localization.AtPrime P) ∘ q)) •
        (⊤ : Submodule (Localization.AtPrime P) (Localization.AtPrime P)) := by
      rw [hsub2]
      exact hyspan
    exact hle hysmul

/-! ## §5. Grade zero on the localized pair quotient from `Ass` -/

/-- The localized module of the ring is the localization ring (both satisfy
the same universal property). -/
noncomputable def locSelfEquiv (R : Type*) [CommRing R] (p : Submonoid R) :
    LocalizedModule p R ≃ₗ[Localization p] Localization p :=
  (IsLocalizedModule.linearEquiv p (LocalizedModule.mkLinearMap p R)
    (Algebra.linearMap R (Localization p))).restrictScalars (Localization p)

/-- `locSelfEquiv` sends `mkLinearMap x` to `algebraMap x`. -/
theorem locSelfEquiv_mkLinearMap (R : Type*) [CommRing R] (p : Submonoid R)
    (x : R) :
    locSelfEquiv R p (LocalizedModule.mkLinearMap p R x) =
      algebraMap R (Localization p) x := by
  simp [locSelfEquiv, Algebra.linearMap_apply,
    -LocalizedModule.mkLinearMap_apply]

/-- The localized submodule `J.localized` maps along `locSelfEquiv` to the
span of the mapped generators: unfolding via `localized'_span`, the images
are the `algebraMap`-images, which span `ofList [x, y]` since `J` is spanned
by `q` and `ofFn` destructures to `[x, y]`. Stated with the semilinear-map
coercion so it feeds `Submodule.Quotient.equiv` directly. -/
theorem locMap_localized_eq_spanPair {R : Type*} [CommRing R] (P : Ideal R)
    [P.IsPrime] (q : Fin 2 → R) (J : Ideal R)
    (hJ : J = Ideal.span (Set.range q)) (x y : Localization P.primeCompl)
    (hpair : List.ofFn (algebraMap R (Localization P.primeCompl) ∘ q) = [x, y]) :
    Submodule.map
      (↑(locSelfEquiv R P.primeCompl) :
        LocalizedModule P.primeCompl R →ₛₗ[RingHom.id (Localization P.primeCompl)]
          Localization P.primeCompl)
      ((↑J : Submodule R R).localized P.primeCompl) =
      (Ideal.ofList [x, y] • ⊤ :
        Submodule (Localization P.primeCompl) (Localization P.primeCompl)) := by
  have hJspan : (↑J : Submodule R R) = Submodule.span R (↑J : Set R) :=
    le_antisymm Submodule.subset_span
      (Submodule.span_le.mpr fun x hx => hx)
  have hloc : ((↑J : Submodule R R).localized P.primeCompl) =
      Submodule.span (Localization P.primeCompl)
        (LocalizedModule.mkLinearMap P.primeCompl R '' (↑J : Set R)) := by
    conv_lhs => rw [hJspan]
    exact Submodule.localized'_span (Localization P.primeCompl) P.primeCompl
      (LocalizedModule.mkLinearMap P.primeCompl R) _
  rw [hloc, Submodule.map_span]
  have him : ((↑(locSelfEquiv R P.primeCompl) :
        LocalizedModule P.primeCompl R →ₛₗ[RingHom.id (Localization P.primeCompl)]
          Localization P.primeCompl) ''
        (LocalizedModule.mkLinearMap P.primeCompl R '' (↑J : Set R))) =
      algebraMap R (Localization P.primeCompl) '' (↑J : Set R) := by
    ext z
    simp only [Set.mem_image]
    constructor
    · rintro ⟨w, ⟨v, hvJ, rfl⟩, rfl⟩
      exact ⟨v, hvJ, (locSelfEquiv_mkLinearMap R P.primeCompl v).symm⟩
    · rintro ⟨v, hvJ, rfl⟩
      exact ⟨_, ⟨v, hvJ, rfl⟩, locSelfEquiv_mkLinearMap R P.primeCompl v⟩
  rw [him]
  have hspan_eq : Ideal.ofList [x, y] =
      Ideal.span (Set.range (algebraMap R (Localization P.primeCompl) ∘ q)) := by
    rw [← hpair, RegularityBridge.span_range_eq_ofList_ofFn]
  have hmapJ : Ideal.map (algebraMap R (Localization P.primeCompl)) J =
      Ideal.ofList [x, y] := by
    rw [hJ, Ideal.map_span, ← Set.range_comp,
      RegularityBridge.span_range_eq_ofList_ofFn, hpair]
  have hgoal : Submodule.span (Localization P.primeCompl)
        (algebraMap R (Localization P.primeCompl) '' (↑J : Set R)) =
      ((Ideal.ofList [x, y] : Ideal (Localization P.primeCompl)) :
        Submodule (Localization P.primeCompl) (Localization P.primeCompl)) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨j, hjJ, rfl⟩
      have hmem : algebraMap R (Localization P.primeCompl) j ∈
          Ideal.map (algebraMap R (Localization P.primeCompl)) J :=
        Ideal.mem_map_of_mem _ hjJ
      rw [hmapJ] at hmem
      exact hmem
    · rw [hspan_eq, ← Ideal.submodule_span_eq]
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      apply Submodule.subset_span
      refine ⟨q i, ?_, rfl⟩
      have hqJ : q i ∈ J := by
        rw [hJ]
        exact Ideal.subset_span (Set.mem_range_self i)
      exact hqJ
  rw [hgoal]
  exact (RegularSequenceDimDrop.span_smul_top _).symm

/-- Localization commutes with the pair quotient: the localized module
`LocalizedModule.AtPrime P (R ⧸ J)` is the span quotient by the destructured
localized pair. -/
noncomputable def locQuotEquivPair {R : Type*} [CommRing R] (P : Ideal R)
    [P.IsPrime] (q : Fin 2 → R) (J : Ideal R)
    (hJ : J = Ideal.span (Set.range q)) (x y : Localization.AtPrime P)
    (hpair : List.ofFn (algebraMap R (Localization.AtPrime P) ∘ q) = [x, y]) :
    LocalizedModule.AtPrime P (R ⧸ J) ≃ₗ[Localization.AtPrime P]
      (Localization.AtPrime P ⧸ (Ideal.ofList [x, y] • ⊤ :
        Submodule (Localization.AtPrime P) (Localization.AtPrime P))) := by
  have hpair' : List.ofFn (algebraMap R (Localization P.primeCompl) ∘ q) =
      [x, y] := hpair
  have hf := locMap_localized_eq_spanPair P q J hJ x y hpair'
  exact (localizedQuotientEquiv P.primeCompl (↑J : Submodule R R)).symm.trans
    (Submodule.Quotient.equiv _ _ (locSelfEquiv R P.primeCompl) hf)

/-- Grade zero on the localized pair quotient from `Ass`: the maximal ideal
is associated to the localized module (proved local (ii) input), hence grade
zero there, transported across `locQuotEquivPair`. -/
theorem grade_spanPair_eq_zero_of_mem_ass {R : Type*} [CommRing R] (P : Ideal R)
    [P.IsPrime] (q : Fin 2 → R) (J : Ideal R)
    (hJ : J = Ideal.span (Set.range q)) (x y : Localization.AtPrime P)
    (hpair : List.ofFn (algebraMap R (Localization.AtPrime P) ∘ q) = [x, y])
    (hP : P ∈ associatedPrimes R (R ⧸ J)) :
    GradeDepthFragment.grade (Localization.AtPrime P)
      (Localization.AtPrime P ⧸ (Ideal.ofList [x, y] • ⊤ :
        Submodule (Localization.AtPrime P) (Localization.AtPrime P)))
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) = 0 := by
  have hA :=
    Module.associatedPrimes.mem_associatedPrimes_atPrime_of_mem_associatedPrimes
      hP
  have h0 := GradeDepthFragment.grade_eq_zero_of_mem_associatedPrimes hA
  have hcongr := grade_congr_of_linearEquiv
    (locQuotEquivPair P q J hJ x y hpair)
    (IsLocalRing.maximalIdeal (Localization.AtPrime P))
  rw [hcongr] at h0
  exact h0

/-! ## §6. Assembly: the `k = 2` bridge -/

/-- The `GradeUnmixedBridge` at `k = 2`, in the exact shape
`GradeDepthFragment.unmixed_of_grade_of_depthEq` consumes: from `DepthEqDimAt` at
`P ∈ Ass(R ⧸ J)`, baby-AB forces `grade R_P = 2` (grade zero on the pair
quotient plus the length-2 drop), hence `dim R_P = 2`, hence
`P.height ≤ 2`. -/
theorem gradeUnmixedBridge_pair (m : ℕ) (K : Type*) [Field K]
    (q : Fin 2 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q)) :
    GradeDepthFragment.GradeUnmixedBridge m K q hsucc J hJ := by
  intro _hchain hdepth P hPI hP
  have hJP : Ideal.span (Set.range q) ≤ P := by
    rw [← hJ]
    exact LocalUnmixed.assPrime_contains_span J P hP
  obtain ⟨x, y, hpair, hreg, hxI, hyI⟩ :=
    localized_isRegular_pair P q hsucc hJP
  have hmaxne : IsLocalRing.maximalIdeal (Localization.AtPrime P) ≠ ⊤ :=
    Ideal.IsMaximal.ne_top inferInstance
  have hspanM : IsLocalRing.maximalIdeal (Localization.AtPrime P) =
      Ideal.span (↑(IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
        Set (Localization.AtPrime P)) :=
    (le_antisymm (Ideal.span_le.mpr fun x hx => hx)
      (fun x hx => Ideal.subset_span hx)).symm
  have hIlt : IsLocalRing.maximalIdeal (Localization.AtPrime P) •
      (⊤ : Submodule (Localization.AtPrime P) (Localization.AtPrime P)) < ⊤ := by
    rw [hspanM, RegularSequenceDimDrop.span_smul_top, ← hspanM, lt_top_iff_ne_top]
    intro hcon
    have h1 : (1 : Localization.AtPrime P) ∈
        ((IsLocalRing.maximalIdeal (Localization.AtPrime P) :
          Ideal (Localization.AtPrime P)) :
          Submodule (Localization.AtPrime P) (Localization.AtPrime P)) := by
      rw [hcon]
      exact Submodule.mem_top
    have h1' : (1 : Localization.AtPrime P) ∈
        IsLocalRing.maximalIdeal (Localization.AtPrime P) := h1
    exact hmaxne (Ideal.eq_top_of_isUnit_mem _ h1' isUnit_one)
  have hAB :=
    babyAB_pair (R' := Localization.AtPrime P)
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) x y hxI hyI hIlt hreg
  have hg0 := grade_spanPair_eq_zero_of_mem_ass P q J hJ x y hpair hP
  have hdepthP : ((GradeDepthFragment.grade (Localization.AtPrime P)
        (Localization.AtPrime P)
        (IsLocalRing.maximalIdeal (Localization.AtPrime P)) : ℕ∞) :
        WithBot ℕ∞) =
      ringKrullDim (Localization.AtPrime P) := hdepth P hP
  have hpd2 :=
    pd_spanPair_eq_two (R' := Localization.AtPrime P) x y hreg
  rw [hpd2, hg0] at hAB
  have hAB' : (2 : WithBot ℕ∞) = ((GradeDepthFragment.grade (Localization.AtPrime P)
      (Localization.AtPrime P)
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) : ℕ∞) :
      WithBot ℕ∞) := by
    calc (2 : WithBot ℕ∞) = 2 + (((0 : ℕ∞)) : WithBot ℕ∞) := by simp
      _ = _ := hAB
  have hdim : ringKrullDim (Localization.AtPrime P) = 2 := by
    rw [← hdepthP]
    exact hAB'.symm
  have hH :=
    IsLocalization.AtPrime.ringKrullDim_eq_height P (Localization.AtPrime P)
  rw [hdim] at hH
  have h2 : (2 : WithBot ℕ∞) = (((2 : ℕ) : ℕ∞) : WithBot ℕ∞) := by simp
  rw [h2] at hH
  have hheight : P.height = ((2 : ℕ) : ℕ∞) := WithBot.coe_eq_coe.mp hH.symm
  rw [hheight]

end BabyAuslanderBuchsbaum
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

/-! ## §7. General-k baby Auslander–Buchsbaum (length-k AB equation)

The `k = 2` spike (§§1–6) generalizes to arbitrary `k`: Mathlib's
`projectiveDimension_quotient_eq_length` is already general-k, and the grade
side is the proved iterated equation `GradeDepthFragment.grade_quotIter_add_eq_grade`.
The only new vehicle is `spanQuotIterEquiv` (span quotient `≃` iterated
quotient); everything else mirrors §§3–6 with `[x, y]` replaced by the
`List.ofFn` family (no `length_eq_two` destructure needed).

* `spanQuotIterEquiv` — `(M' ⧸ ofList rs • ⊤) ≃ quotIter M' rs`.
* `grade_spanQuot_add_length_eq_grade` — grade drop by `rs.length` on the span
  quotient.
* `pd_spanQuot_eq_length` — `pd = rs.length` from
  `projectiveDimension_quotient_eq_length`.
* `babyAB_quot` — the length-`k` AB equation `pd + grade(M) = grade(R)`.
* `localized_isRegular_ofFn` / `locMap_localized_eq_spanOfFn` /
  `locQuotEquivOfFn` / `grade_spanOfFn_eq_zero_of_mem_ass` — the §4–5 inputs
  for the `ofFn` family.
* `gradeUnmixedBridge_general` — `GradeDepthFragment.GradeUnmixedBridge` for general
  `k` (same `hdepth`-only inputs as `gradeUnmixedBridge_pair`).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace BabyAuslanderBuchsbaum

open RingTheory.Sequence

/-- The span quotient by a list is the iterated `QuotSMulTop` quotient
(`GradeDepthFragment.quotIter`): peel off the head with
`quotOfListConsSMulTopEquivQuotSMulTopInner`, then recurse. -/
def spanQuotIterEquiv {R' : Type u} [CommRing R'] (M' : Type u)
    [AddCommGroup M'] [Module R' M'] (rs : List R') :
    (M' ⧸ (Ideal.ofList rs • ⊤ : Submodule R' M')) ≃ₗ[R']
      GradeDepthFragment.quotIter M' rs := by
  induction rs generalizing M' with
  | nil =>
    have hbot : (Ideal.ofList ([] : List R') • ⊤ : Submodule R' M') = ⊥ := by
      rw [Ideal.ofList_nil, Submodule.bot_smul]
    exact Submodule.quotEquivOfEqBot _ hbot
  | cons x xs ih =>
    exact (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M' x xs).trans
      (ih (QuotSMulTop x M'))

/-- Length-`k` grade drop on the span quotient (the form `pd` and the assembly
need), transported from the proved iterated equation
`GradeDepthFragment.grade_quotIter_add_eq_grade` across `spanQuotIterEquiv`.
Generalizes `grade_spanPair_add_two_eq_grade`. -/
theorem grade_spanQuot_add_length_eq_grade {R' : Type u} [CommRing R']
    [IsNoetherianRing R'] [Module.Finite R' R'] (I : Ideal R') (rs : List R')
    (hmem : ∀ r ∈ rs, r ∈ I)
    (hIlt : I • (⊤ : Submodule R' R') < ⊤) (hreg : IsRegular R' rs) :
    GradeDepthFragment.grade R'
        (R' ⧸ (Ideal.ofList rs • ⊤ : Submodule R' R')) I +
        ((rs.length : ℕ) : ℕ∞) =
      GradeDepthFragment.grade R' R' I := by
  rw [grade_congr_of_linearEquiv (spanQuotIterEquiv R' rs) I]
  exact GradeDepthFragment.grade_quotIter_add_eq_grade I rs hmem hIlt hreg

/-- Projective dimension of the span quotient is exactly `rs.length`, from
`projectiveDimension_quotient_eq_length` (`pd = length` from `IsRegular`
directly), transported across the `Shrink` and `↑ofList = ofList • ⊤`
identifications. Generalizes `pd_spanPair_eq_two`. -/
theorem pd_spanQuot_eq_length {R' : Type u} [CommRing R'] [IsNoetherianRing R']
    [IsLocalRing R'] (rs : List R') (hreg : IsRegular R' rs) :
    CategoryTheory.projectiveDimension
        (ModuleCat.of R'
          (R' ⧸ (Ideal.ofList rs • ⊤ : Submodule R' R'))) = rs.length := by
  have hsmall : Small.{u} R' := small_self R'
  have hpd := ModuleCat.projectiveDimension_quotient_eq_length (R := R') rs hreg
  have hsub : ((Ideal.ofList rs : Ideal R') : Submodule R' R') =
      Ideal.ofList rs • ⊤ :=
    (RegularSequenceDimDrop.span_smul_top _).symm
  let e : Shrink.{u} (R' ⧸ Ideal.ofList rs) ≃ₗ[R']
      (R' ⧸ (Ideal.ofList rs • ⊤ : Submodule R' R')) :=
    (Shrink.linearEquiv R' _).trans (Submodule.quotEquivOfEq _ _ hsub)
  rw [← CategoryTheory.projectiveDimension_eq_of_iso e.toModuleIso]
  exact_mod_cast hpd

/-- Baby Auslander–Buchsbaum for a length-`k` quotient: with `pd = length`
(above) and grade dropping by exactly `length` (the proved iterated Rees–LES
rungs), `pd` plus the grade of the quotient equals the grade of the ring.
Generalizes `babyAB_pair`. -/
theorem babyAB_quot {R' : Type u} [CommRing R'] [IsNoetherianRing R']
    [IsLocalRing R'] [Module.Finite R' R'] (I : Ideal R') (rs : List R')
    (hmem : ∀ r ∈ rs, r ∈ I)
    (hIlt : I • (⊤ : Submodule R' R') < ⊤) (hreg : IsRegular R' rs) :
    CategoryTheory.projectiveDimension (ModuleCat.of R'
          (R' ⧸ (Ideal.ofList rs • ⊤ : Submodule R' R'))) +
        ((GradeDepthFragment.grade R'
            (R' ⧸ (Ideal.ofList rs • ⊤ : Submodule R' R')) I : ℕ∞) :
          WithBot ℕ∞) =
      ((GradeDepthFragment.grade R' R' I : ℕ∞) : WithBot ℕ∞) := by
  rw [pd_spanQuot_eq_length rs hreg]
  have hdrop := grade_spanQuot_add_length_eq_grade I rs hmem hIlt hreg
  have hdropW :
      (((GradeDepthFragment.grade R'
            (R' ⧸ (Ideal.ofList rs • ⊤ : Submodule R' R')) I + rs.length :
          ℕ∞)) : WithBot ℕ∞) =
      ((GradeDepthFragment.grade R' R' I : ℕ∞) : WithBot ℕ∞) := by
    exact_mod_cast hdrop
  rw [← hdropW, WithBot.coe_add, WithBot.coe_natCast, add_comm]

/-- The localized successive family at `P` is a regular `ofFn` family in the
maximal ideal: regularity survives localization
(`successiveSMulRegular_map_atPrime`), the maps land in the maximal ideal
since `J ≤ P`, and properness follows (mirroring `RegularSequenceDimDrop`).
Generalizes `localized_isRegular_pair` (no pair destructure needed). -/
theorem localized_isRegular_ofFn {R : Type*} [CommRing R] [IsNoetherianRing R]
    {k : ℕ} (P : Ideal R) [P.IsPrime] (q : Fin k → R)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (hJP : Ideal.span (Set.range q) ≤ P) :
    IsRegular (Localization.AtPrime P)
      (List.ofFn (algebraMap R (Localization.AtPrime P) ∘ q)) ∧
      ∀ r ∈ List.ofFn (algebraMap R (Localization.AtPrime P) ∘ q),
        r ∈ IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
  have hsuccS :=
    RegularSequenceDimDrop.successiveSMulRegular_map_atPrime (P := P)
      (Localization.AtPrime P) q hsucc
  have hmem : ∀ i, algebraMap R (Localization.AtPrime P) (q i) ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
    intro i
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P]
    exact hJP (Ideal.subset_span (Set.mem_range_self i))
  have hle : Ideal.ofList (List.ofFn (algebraMap R (Localization.AtPrime P) ∘ q)) •
        (⊤ : Submodule (Localization.AtPrime P) (Localization.AtPrime P))
      ≤ ((IsLocalRing.maximalIdeal (Localization.AtPrime P) :
        Ideal (Localization.AtPrime P)) :
        Submodule (Localization.AtPrime P) (Localization.AtPrime P)) := by
    rw [← RegularityBridge.span_range_eq_ofList_ofFn, RegularSequenceDimDrop.span_smul_top]
    exact_mod_cast Ideal.span_le.mpr (Set.range_subset_iff.mpr hmem)
  have hproperS : (⊤ : Submodule (Localization.AtPrime P) (Localization.AtPrime P))
      ≠ Ideal.ofList (List.ofFn (algebraMap R (Localization.AtPrime P) ∘ q)) •
        ⊤ := by
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
  refine ⟨hregS, ?_⟩
  intro r hr
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
  exact hmem i

/-- The localized submodule `J.localized` maps along `locSelfEquiv` to the
span of the mapped `ofFn` family. Same proof as `locMap_localized_eq_spanPair`
with `span_range_eq_ofList_ofFn` used directly (no pair equation). -/
theorem locMap_localized_eq_spanOfFn {R : Type*} [CommRing R] (P : Ideal R)
    [P.IsPrime] {k : ℕ} (q : Fin k → R) (J : Ideal R)
    (hJ : J = Ideal.span (Set.range q)) :
    Submodule.map
      (↑(locSelfEquiv R P.primeCompl) :
        LocalizedModule P.primeCompl R →ₛₗ[RingHom.id (Localization P.primeCompl)]
          Localization P.primeCompl)
      ((↑J : Submodule R R).localized P.primeCompl) =
      (Ideal.ofList (List.ofFn (algebraMap R (Localization P.primeCompl) ∘ q)) • ⊤ :
        Submodule (Localization P.primeCompl) (Localization P.primeCompl)) := by
  have hJspan : (↑J : Submodule R R) = Submodule.span R (↑J : Set R) :=
    le_antisymm Submodule.subset_span
      (Submodule.span_le.mpr fun x hx => hx)
  have hloc : ((↑J : Submodule R R).localized P.primeCompl) =
      Submodule.span (Localization P.primeCompl)
        (LocalizedModule.mkLinearMap P.primeCompl R '' (↑J : Set R)) := by
    conv_lhs => rw [hJspan]
    exact Submodule.localized'_span (Localization P.primeCompl) P.primeCompl
      (LocalizedModule.mkLinearMap P.primeCompl R) _
  rw [hloc, Submodule.map_span]
  have him : ((↑(locSelfEquiv R P.primeCompl) :
        LocalizedModule P.primeCompl R →ₛₗ[RingHom.id (Localization P.primeCompl)]
          Localization P.primeCompl) ''
        (LocalizedModule.mkLinearMap P.primeCompl R '' (↑J : Set R))) =
      algebraMap R (Localization P.primeCompl) '' (↑J : Set R) := by
    ext z
    simp only [Set.mem_image]
    constructor
    · rintro ⟨w, ⟨v, hvJ, rfl⟩, rfl⟩
      exact ⟨v, hvJ, (locSelfEquiv_mkLinearMap R P.primeCompl v).symm⟩
    · rintro ⟨v, hvJ, rfl⟩
      exact ⟨_, ⟨v, hvJ, rfl⟩, locSelfEquiv_mkLinearMap R P.primeCompl v⟩
  rw [him]
  have hspan_eq :
      Ideal.ofList (List.ofFn (algebraMap R (Localization P.primeCompl) ∘ q)) =
      Ideal.span (Set.range (algebraMap R (Localization P.primeCompl) ∘ q)) :=
    (RegularityBridge.span_range_eq_ofList_ofFn _).symm
  have hmapJ : Ideal.map (algebraMap R (Localization P.primeCompl)) J =
      Ideal.ofList (List.ofFn (algebraMap R (Localization P.primeCompl) ∘ q)) := by
    rw [hJ, Ideal.map_span, ← Set.range_comp,
      RegularityBridge.span_range_eq_ofList_ofFn]
  have hgoal : Submodule.span (Localization P.primeCompl)
        (algebraMap R (Localization P.primeCompl) '' (↑J : Set R)) =
      ((Ideal.ofList (List.ofFn (algebraMap R (Localization P.primeCompl) ∘ q)) :
        Ideal (Localization P.primeCompl)) :
        Submodule (Localization P.primeCompl) (Localization P.primeCompl)) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨j, hjJ, rfl⟩
      have hmem : algebraMap R (Localization P.primeCompl) j ∈
          Ideal.map (algebraMap R (Localization P.primeCompl)) J :=
        Ideal.mem_map_of_mem _ hjJ
      rw [hmapJ] at hmem
      exact hmem
    · rw [hspan_eq, ← Ideal.submodule_span_eq]
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      apply Submodule.subset_span
      refine ⟨q i, ?_, rfl⟩
      have hqJ : q i ∈ J := by
        rw [hJ]
        exact Ideal.subset_span (Set.mem_range_self i)
      exact hqJ
  rw [hgoal]
  exact (RegularSequenceDimDrop.span_smul_top _).symm

/-- Localization commutes with the span quotient: the localized module
`LocalizedModule.AtPrime P (R ⧸ J)` is the span quotient by the localized
`ofFn` family. Generalizes `locQuotEquivPair`. -/
noncomputable def locQuotEquivOfFn {R : Type*} [CommRing R] (P : Ideal R)
    [P.IsPrime] {k : ℕ} (q : Fin k → R) (J : Ideal R)
    (hJ : J = Ideal.span (Set.range q)) :
    LocalizedModule.AtPrime P (R ⧸ J) ≃ₗ[Localization.AtPrime P]
      (Localization.AtPrime P ⧸ (Ideal.ofList
        (List.ofFn (algebraMap R (Localization.AtPrime P) ∘ q)) • ⊤ :
        Submodule (Localization.AtPrime P) (Localization.AtPrime P))) := by
  have hf := locMap_localized_eq_spanOfFn P q J hJ
  exact (localizedQuotientEquiv P.primeCompl (↑J : Submodule R R)).symm.trans
    (Submodule.Quotient.equiv _ _ (locSelfEquiv R P.primeCompl) hf)

/-- Grade zero on the localized span quotient from `Ass`: the maximal ideal
is associated to the localized module (proved local (ii) input), hence grade
zero there, transported across `locQuotEquivOfFn`.
Generalizes `grade_spanPair_eq_zero_of_mem_ass`. -/
theorem grade_spanOfFn_eq_zero_of_mem_ass {R : Type*} [CommRing R] (P : Ideal R)
    [P.IsPrime] {k : ℕ} (q : Fin k → R) (J : Ideal R)
    (hJ : J = Ideal.span (Set.range q))
    (hP : P ∈ associatedPrimes R (R ⧸ J)) :
    GradeDepthFragment.grade (Localization.AtPrime P)
      (Localization.AtPrime P ⧸ (Ideal.ofList
        (List.ofFn (algebraMap R (Localization.AtPrime P) ∘ q)) • ⊤ :
        Submodule (Localization.AtPrime P) (Localization.AtPrime P)))
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) = 0 := by
  have hA :=
    Module.associatedPrimes.mem_associatedPrimes_atPrime_of_mem_associatedPrimes
      hP
  have h0 := GradeDepthFragment.grade_eq_zero_of_mem_associatedPrimes hA
  have hcongr := grade_congr_of_linearEquiv
    (locQuotEquivOfFn P q J hJ)
    (IsLocalRing.maximalIdeal (Localization.AtPrime P))
  rw [hcongr] at h0
  exact h0

/-- The `GradeUnmixedBridge` for general `k`, in the exact shape
`GradeDepthFragment.unmixed_of_grade_of_depthEq` consumes: from `DepthEqDimAt` at
`P ∈ Ass(R ⧸ J)`, baby-AB forces `grade R_P = k` (grade zero on the span
quotient plus the length-`k` drop), hence `dim R_P = k`, hence
`P.height ≤ k`. Generalizes `gradeUnmixedBridge_pair`. -/
theorem gradeUnmixedBridge_general (m : ℕ) (K : Type*) [Field K]
    {k : ℕ} (q : Fin k → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q)) :
    GradeDepthFragment.GradeUnmixedBridge m K q hsucc J hJ := by
  intro _hchain hdepth P hPI hP
  have hJP : Ideal.span (Set.range q) ≤ P := by
    rw [← hJ]
    exact LocalUnmixed.assPrime_contains_span J P hP
  obtain ⟨hreg, hmem⟩ := localized_isRegular_ofFn P q hsucc hJP
  have hmaxne : IsLocalRing.maximalIdeal (Localization.AtPrime P) ≠ ⊤ :=
    Ideal.IsMaximal.ne_top inferInstance
  have hspanM : IsLocalRing.maximalIdeal (Localization.AtPrime P) =
      Ideal.span (↑(IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
        Set (Localization.AtPrime P)) :=
    (le_antisymm (Ideal.span_le.mpr fun x hx => hx)
      (fun x hx => Ideal.subset_span hx)).symm
  have hIlt : IsLocalRing.maximalIdeal (Localization.AtPrime P) •
      (⊤ : Submodule (Localization.AtPrime P) (Localization.AtPrime P)) < ⊤ := by
    rw [hspanM, RegularSequenceDimDrop.span_smul_top, ← hspanM, lt_top_iff_ne_top]
    intro hcon
    have h1 : (1 : Localization.AtPrime P) ∈
        ((IsLocalRing.maximalIdeal (Localization.AtPrime P) :
          Ideal (Localization.AtPrime P)) :
          Submodule (Localization.AtPrime P) (Localization.AtPrime P)) := by
      rw [hcon]
      exact Submodule.mem_top
    have h1' : (1 : Localization.AtPrime P) ∈
        IsLocalRing.maximalIdeal (Localization.AtPrime P) := h1
    exact hmaxne (Ideal.eq_top_of_isUnit_mem _ h1' isUnit_one)
  have hAB :=
    babyAB_quot (R' := Localization.AtPrime P)
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) _ hmem hIlt hreg
  have hg0 := grade_spanOfFn_eq_zero_of_mem_ass P q J hJ hP
  have hdepthP : ((GradeDepthFragment.grade (Localization.AtPrime P)
        (Localization.AtPrime P)
        (IsLocalRing.maximalIdeal (Localization.AtPrime P)) : ℕ∞) :
        WithBot ℕ∞) =
      ringKrullDim (Localization.AtPrime P) := hdepth P hP
  have hpd :=
    pd_spanQuot_eq_length (R' := Localization.AtPrime P) _ hreg
  rw [hpd, hg0] at hAB
  rw [List.length_ofFn] at hAB
  have hAB' : (((k : ℕ)) : WithBot ℕ∞) = ((GradeDepthFragment.grade (Localization.AtPrime P)
      (Localization.AtPrime P)
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) : ℕ∞) :
      WithBot ℕ∞) := by
    calc (((k : ℕ)) : WithBot ℕ∞)
        = ((k : ℕ) : WithBot ℕ∞) + (((0 : ℕ∞)) : WithBot ℕ∞) := by simp
      _ = _ := hAB
  have hdim : ringKrullDim (Localization.AtPrime P) = ((k : ℕ) : WithBot ℕ∞) := by
    rw [← hdepthP]
    exact hAB'.symm
  have hH :=
    IsLocalization.AtPrime.ringKrullDim_eq_height P (Localization.AtPrime P)
  rw [hdim] at hH
  have hk : ((k : ℕ) : WithBot ℕ∞) = ((((k : ℕ)) : ℕ∞) : WithBot ℕ∞) :=
    (WithBot.coe_natCast k).symm
  rw [hk] at hH
  have hheight : P.height = ((k : ℕ) : ℕ∞) := WithBot.coe_eq_coe.mp hH.symm
  rw [hheight]

end BabyAuslanderBuchsbaum
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
