/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.DirectSum.Ring
import Mathlib.Algebra.Algebra.Operations
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Regular.IsSMulRegular
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.AssociatedGradedRing
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedNakayamaBank
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.ColonDimDrop
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.PositiveDimTower
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.ColonTransfer
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.QuotientKernelAvoidance
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.ValabregaVallaSingle

/-!
# Order-one trace from quotient-side graded avoidance, repaired
This file addresses the M1 residual `SupT1TraceOfGrAvoidQuot`
(QuotAvoid §7:566): the order-one trace from quotient-side graded
avoidance. Its main results are:

* (§6) `SupT1TraceOfGrAvoidQuot` **as stated is false**: the
  `S = k⟦u,v⟧`, `J' = (u²,uv)`, `y = v` counterexample below. The
  defect is the `J'`-component: `z = uv ∈ J' ∩ (v)` needs the quotient
  `u ∉ 𝔪ⁿ⁺¹ ⊔ J'`, and no re-choosing is possible (domain, unique
  quotient). Graded avoidance + positivity both hold there while the
  trace fails. So M1 needs the ungraded-avoidance hypothesis — exactly
  the hypothesis the §7 kernel `SupT1OfGrAvoidQuotRep` already carries.
* (§1–§5) The **repaired** trace `supT1Trace_of_quotAvoid_repaired`:
  graded + ungraded avoidance imply the order-one trace, proved
  unconditionally (given Noetherian `R`): filter-regularity kills the
  `(0 : y*)`-torsion in high degree (§1–§3, via associated primes of
  the torsion submodule), initial-form induction + per-degree
  Artin–Rees give the quotient-side trace (§4), and regularity
  reshapes it to the `𝔪ⁿ ⊔ J'` form (§5, the `supColon_of_t1Data`
  correction pattern).

## The M1-as-stated counterexample (why the repair is needed)

Take `R = k⟦u,v⟧` (Noetherian local domain), `J' = (u², uv)`,
`y = v`. Then `R ⧸ J' = k⟦u,v⟧/(u²,uv)` has dimension 1 (minimal
prime `(u)`, quotient `k⟦v⟧`), so positivity holds. The associated
graded is `gr(R ⧸ J') = k[U,V]/(U²,UV)` with
`Ass = {(U), (U,V)}` (ann`(V) = (U)`, ann`(U) = (U,V)`, and every
other annihilator is `(0)` or `(U)`); the only relevant prime is
`(U)`, avoided by `V = y*`. So both M1 hypotheses hold. But
`z = uv ∈ J' ⊆ 𝔪ⁿ⁺² ⊔ J'` for every `n`, `z = u·v ∈ span{v}`,
while `a·v = u·v` forces `a = u` (domain), and
`u ∉ 𝔪ⁿ⁺¹ ⊔ J'` for `n ≥ 1` (reduce mod `𝔪²`: `ū ≠ 0` but
`𝔪ⁿ⁺¹ ⊔ J' ⊆ 𝔪²`). Hence the trace conclusion fails at
`n = max c 1`. The classical "filter-regular ⟹ superficial" theorem
behind M1 is a statement in the quotient `R ⧸ J'` (where it holds:
`z̄ = 0`, quotient `0`); its `R`-side `𝔪ⁿ ⊔ J'` formulation needs
regularity to control the `J'`-component. Formalizing the `¬`-form
would need `Ass(gr)` computation over the project's
`associatedGraded` (no such API in tree) and is not attempted; the
repair below is the actionable content.

## What this file proves

* (§1) `vvTorsion` (the `(0 : y*)` ideal), its membership lemma, and
  homogeneity: `vvTorsion_hom_comp` (homogeneous components stay in
  `K`), `vvTorsion_hom_gens` (finite homogeneous spanning set with a
  degree bound).
* (§2) Uniform torsion: `vvTorsion_pow_mul_eq_zero` (`gr₊ᴺ·K = 0`).
  Via: minimal primes over `ann(K)` lie in `Ass(K) ⊆ Ass(gr)`
  (`minimalPrimes_annihilator_subset_associatedPrimes` +
  `IsAssociatedPrime.map_of_injective`), avoidability forces each to
  contain `gr₊`, hence `gr₊ ≤ √(ann K)` (`radical_eq_sInf`), hence a
  power lies in `ann(K)` (`exists_pow_le_of_le_radical_of_fg`).
* (§3) `vvTorsion_vanishes`: `K_m = 0` for `m ≥ D + N` (finite
  homogeneous generation + torsion + generation in degree 1).
* (§4) `vv_trace_of_filterRegular`: the quotient-side eventual trace
  from filter-regularity + regularity. Large-order quotients die by
  §3; small-order quotients die by per-degree Artin–Rees
  (`Ideal.exists_pow_inf_eq_pow_smul`) + regularity cancellation.
* (§5) Quotient/maximal-ideal correspondence (`𝔫 = 𝔪_S`,
  membership lifting) and the `R`-side reshape.
* (§6) `SupT1TraceOfGrAvoidQuotRep` (M1 + ungraded avoidance) and
  `supT1Trace_of_quotAvoid_repaired`, plus `supT1QuotRep_of_traceRep`
  re-plugging the §7 kernel. The §7 assembly
  `supT1Data_of_quotAvoid_repaired` fires unchanged with the repaired
  M1 (it already derives `hungr` via M2).

## Status

unconditional (given `IsNoetherianRing R`): everything in §§1–§6.
The M1-as-stated false verdict is prose (verified by hand against the
`associatedGraded` definitions; no Lean `¬`-theorem attempted).

## Residual register

closed this lane: [M1 trace kernel, repaired with ungraded
avoidance]. Open (exact, unchanged): [M2 `SupJointUnhgradedRefine`],
[`φ` construction], [per-stage `depth ≥ 1`]. M1-as-stated is false,
not open (see above); `supT1QuotRep_of_trace` (QuotAvoid:614) is
valid but inapplicable — use `supT1QuotRep_of_traceRep` (§6) instead.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace OrderOneTrace

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AssociatedGradedRing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedNakayamaBank
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.PositiveDimTower
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.ColonTransfer
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.QuotientKernelAvoidance
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.ValabregaVallaSingle

/-! ## §1. The `(0 : y*)`-torsion ideal and its homogeneity -/

/-- The `(0 : y*)`-torsion ideal of the associated graded ring: all
elements killed by `w`. The filter-regularity hypothesis says `w`
avoids the relevant associated primes; §2 shows this forces `K` to be
`gr₊`-torsion, and §3 that it vanishes in high degree.
-/
def vvTorsion (S : Type*) [CommRing S] (𝔫 : Ideal S)
    (w : associatedGraded S 𝔫) : Ideal (associatedGraded S 𝔫) :=
  Submodule.colon (⊥ : Submodule (associatedGraded S 𝔫) (associatedGraded S 𝔫)) {w}

#print axioms vvTorsion

/-- Membership in `K` is vanishing of the product with `w`.
-/
theorem vvTorsion_mem_iff {S : Type*} [CommRing S] (𝔫 : Ideal S)
    (w : associatedGraded S 𝔫) (β : associatedGraded S 𝔫) :
    β ∈ vvTorsion S 𝔫 w ↔ β * w = 0 := by
  rw [vvTorsion, Submodule.mem_colon_singleton, Submodule.mem_bot, smul_eq_mul]

#print axioms vvTorsion_mem_iff

/-- Graded multiplication kills `0` on the left (linearity in the
first argument of the double lift).
-/
theorem vv_grMul_zero_left {S : Type*} [CommRing S] (𝔫 : Ideal S)
    (i j : ℕ) (b : grPiece S 𝔫 j) :
    GradedMonoid.GMul.mul (0 : grPiece S 𝔫 i) b = 0 := by
  change (grMulQ2 S 𝔫 i j) 0 b = 0
  simp

#print axioms vv_grMul_zero_left

/-- The degree-`n` component of a finite sum is the sum of components
(by `grCoeff_add` induction).
-/
theorem vv_grCoeff_sum {S : Type*} [CommRing S] (𝔫 : Ideal S)
    {ι : Type*} (s : Finset ι) (f : ι → associatedGraded S 𝔫) (n : ℕ) :
    grCoeff S 𝔫 (∑ j ∈ s, f j) n = ∑ j ∈ s, grCoeff S 𝔫 (f j) n := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [grCoeff_zero S 𝔫 n]
  · intro a s has IH
    rw [Finset.sum_insert has, Finset.sum_insert has, grCoeff_add, IH]

#print axioms vv_grCoeff_sum

/-- Homogeneous components of a `K`-element stay in `K` (for
homogeneous `w`): from `x * w = 0`, the degree-`(i+d)` component of
the homogeneous expansion `x = Σⱼ xⱼ` is `(xᵢ)·c = 0`.
-/
theorem vvTorsion_hom_comp {S : Type*} [CommRing S] (𝔫 : Ideal S)
    (d : ℕ) (c : grPiece S 𝔫 d)
    {x : associatedGraded S 𝔫}
    (hx : x ∈ vvTorsion S 𝔫 (grOf S 𝔫 d c)) (i : ℕ) :
    grOf S 𝔫 i (grCoeff S 𝔫 x i) ∈ vvTorsion S 𝔫 (grOf S 𝔫 d c) := by
  classical
  rw [vvTorsion_mem_iff, grOf_mul]
  have hxw : x * grOf S 𝔫 d c = 0 := (vvTorsion_mem_iff 𝔫 _ _).mp hx
  have hsup := gr_sum_support S 𝔫 x
  have hexpand : x * grOf S 𝔫 d c = ∑ j ∈ (toDirectSum S 𝔫 x).support,
      grOf S 𝔫 (j + d) (GradedMonoid.GMul.mul (grCoeff S 𝔫 x j) c) := by
    conv_lhs => rw [← hsup]
    -- Term-mode: `rw [Finset.sum_mul]` fails to match since the goal's `*`
    -- instance (from our `CommRing`) differs syntactically from the lemma's
    -- (same as `gr_mul_coeff_zero_of_right` in the Nakayama bank).
    have hexpand2 : ((∑ i ∈ (toDirectSum S 𝔫 x).support,
          grOf S 𝔫 i (grCoeff S 𝔫 x i)) * grOf S 𝔫 d c) =
        ∑ i ∈ (toDirectSum S 𝔫 x).support,
          (grOf S 𝔫 i (grCoeff S 𝔫 x i) * grOf S 𝔫 d c) :=
      Finset.sum_mul _ _ _
    rw [hexpand2]
    apply Finset.sum_congr rfl
    intro j _
    rw [grOf_mul]
  have h0 : grCoeff S 𝔫 (x * grOf S 𝔫 d c) (i + d) = 0 := by
    rw [hxw]
    exact grCoeff_zero S 𝔫 _
  rw [hexpand, vv_grCoeff_sum] at h0
  have hterm : ∀ j ∈ (toDirectSum S 𝔫 x).support,
      grCoeff S 𝔫 (grOf S 𝔫 (j + d)
        (GradedMonoid.GMul.mul (grCoeff S 𝔫 x j) c)) (i + d) =
        (if j = i then GradedMonoid.GMul.mul (grCoeff S 𝔫 x i) c else 0) := by
    intro j _
    by_cases hji : j = i
    · subst hji
      rw [ite_eq_left rfl, grCoeff_of]
    · rw [ite_eq_right hji]
      apply grCoeff_of_ne
      omega
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq'] at h0
  by_cases hi : (toDirectSum S 𝔫 x) i ≠ 0
  · rw [ite_eq_left (DFinsupp.mem_support_iff.mpr hi)] at h0
    rw [h0, grOf_zero]
  · rw [ite_eq_right (fun h => hi (DFinsupp.mem_support_iff.mp h))] at h0
    have hcoeff : grCoeff S 𝔫 x i = 0 := not_not.mp hi
    rw [hcoeff, vv_grMul_zero_left, grOf_zero]

#print axioms vvTorsion_hom_comp

/-! ## §1 (cont.). FG bridges and finite homogeneous generation -/

/-- `Submodule.FG` implies `Ideal.FG` (via `Ideal.submodule_span_eq`).
Feeds the Noetherian inputs of §2 (`exists_pow_le_of_le_radical_of_fg`
wants `Ideal.FG`).
-/
theorem vv_ideal_fg_of_submodule_fg {R : Type*} [CommRing R] (I : Ideal R)
    (h : Submodule.FG (R := R) (M := R) I) : I.FG := by
  obtain ⟨s, hsfin, hspan⟩ := Submodule.fg_def.mp h
  obtain ⟨Sd, rfl⟩ := hsfin.exists_finset_coe
  exact ⟨Sd, hspan⟩

#print axioms vv_ideal_fg_of_submodule_fg

/-- Every `K`-generator's homogeneous components stay in `K` and span it:
from explicit finite generation, `K` has a finite homogeneous spanning
set with a degree bound (the max support degree). The spanning direction
is `gr_sum_support`; the membership direction is `vvTorsion_hom_comp`.
-/
theorem vvTorsion_hom_gens {S : Type*} [CommRing S] (𝔫 : Ideal S)
    (d : ℕ) (c : grPiece S 𝔫 d)
    (hfin : (vvTorsion S 𝔫 (grOf S 𝔫 d c)).FG) :
    ∃ (G : Finset (associatedGraded S 𝔫)) (D : ℕ),
      (∀ g ∈ G, g ∈ vvTorsion S 𝔫 (grOf S 𝔫 d c)) ∧
      (∀ g ∈ G, ∃ i : ℕ, i ≤ D ∧ grOf S 𝔫 i (grCoeff S 𝔫 g i) = g) ∧
      Ideal.span (↑G : Set (associatedGraded S 𝔫)) =
        vvTorsion S 𝔫 (grOf S 𝔫 d c) := by
  classical
  obtain ⟨S₀, hS₀⟩ := hfin
  have hmemK : ∀ x ∈ S₀, x ∈ vvTorsion S 𝔫 (grOf S 𝔫 d c) := by
    intro x hx
    rw [← hS₀]
    exact Ideal.subset_span (Finset.mem_coe.mpr hx)
  refine ⟨S₀.biUnion (fun x => (toDirectSum S 𝔫 x).support.image
      (fun i => grOf S 𝔫 i (grCoeff S 𝔫 x i))),
    S₀.sup (fun x => (toDirectSum S 𝔫 x).support.sup id), ?_, ?_, ?_⟩
  · intro g hg
    rw [Finset.mem_biUnion] at hg
    obtain ⟨x, hxS, hmem⟩ := hg
    rw [Finset.mem_image] at hmem
    obtain ⟨i, _, rfl⟩ := hmem
    exact vvTorsion_hom_comp 𝔫 d c (hmemK x hxS) i
  · intro g hg
    rw [Finset.mem_biUnion] at hg
    obtain ⟨x, hxS, hmem⟩ := hg
    rw [Finset.mem_image] at hmem
    obtain ⟨i, hi, rfl⟩ := hmem
    refine ⟨i, ?_, ?_⟩
    · have h1 : i ≤ (toDirectSum S 𝔫 x).support.sup id :=
        Finset.le_sup (f := id) hi
      have h2 : (toDirectSum S 𝔫 x).support.sup id ≤
          S₀.sup (fun x => (toDirectSum S 𝔫 x).support.sup id) :=
        Finset.le_sup (f := fun x => (toDirectSum S 𝔫 x).support.sup id) hxS
      exact h1.trans h2
    · rw [grCoeff_of]
  · apply le_antisymm
    · rw [Ideal.span_le]
      intro g hg
      rw [Finset.mem_coe] at hg
      rw [Finset.mem_biUnion] at hg
      obtain ⟨x, hxS, hmem⟩ := hg
      rw [Finset.mem_image] at hmem
      obtain ⟨i, _, rfl⟩ := hmem
      exact vvTorsion_hom_comp 𝔫 d c (hmemK x hxS) i
    · rw [← hS₀, Ideal.span_le]
      intro x hx
      rw [Finset.mem_coe] at hx
      have hsup := gr_sum_support S 𝔫 x
      rw [← hsup]
      refine Submodule.sum_mem _ fun i hi => ?_
      apply Ideal.subset_span
      rw [Finset.mem_coe, Finset.mem_biUnion]
      exact ⟨x, hx, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩

#print axioms vvTorsion_hom_gens

/-- `w` annihilates `K` (definitionally: `K = (0 : w)`). The fact §2 uses
to force every minimal prime over `ann(K)` to carry `gr₊`.
-/
theorem vvTorsion_ann_mem {S : Type*} [CommRing S] (𝔫 : Ideal S)
    (d : ℕ) (c : grPiece S 𝔫 d) :
    grOf S 𝔫 d c ∈ Module.annihilator (associatedGraded S 𝔫)
      ↥(vvTorsion S 𝔫 (grOf S 𝔫 d c)) := by
  rw [Module.mem_annihilator]
  intro k
  have hk : (k.val * grOf S 𝔫 d c) = 0 :=
    (vvTorsion_mem_iff 𝔫 _ _).mp k.2
  apply Subtype.ext
  change grOf S 𝔫 d c • k.val = 0
  rw [smul_eq_mul, mul_comm]
  exact hk

#print axioms vvTorsion_ann_mem

/-! ## §2. Uniform torsion: `gr₊ᴺ·K = 0` -/

/-- `grPlus` is the `SupIrrelevantIdeal` (same generators: `grOf` unfolds
to `DirectSum.of`).
-/
theorem vv_grPlus_eq_irrelevant {S : Type*} [CommRing S] (𝔫 : Ideal S) :
    grPlus S 𝔫 = SupIrrelevantIdeal S 𝔫 := by
  unfold grPlus grHomSet SupIrrelevantIdeal
  congr 1
  ext x
  constructor
  · rintro ⟨m, z, hm, rfl⟩
    exact ⟨m, hm, z, rfl⟩
  · rintro ⟨m, hm, z, rfl⟩
    exact ⟨m, z, hm, rfl⟩

#print axioms vv_grPlus_eq_irrelevant

/-- Uniform torsion (§2): filter-regularity forces `gr₊ᴺ·K = 0` for some `N`.
Minimal primes over `ann(K)` lie in `Ass(K) ⊆ Ass(gr)`
(`minimalPrimes_annihilator_subset_associatedPrimes` +
`IsAssociatedPrime.map_of_injective`); relevance would contradict
avoidance since `w ∈ ann(K)` (`vvTorsion_ann_mem`); hence
`gr₊ ≤ √(ann K)` (`Ideal.sInf_minimalPrimes`) and a power lies in
`ann(K)` (`Ideal.exists_pow_le_of_le_radical_of_fg`).
-/
theorem vvTorsion_pow_mul_eq_zero {S : Type*} [CommRing S] (𝔫 : Ideal S)
    [IsNoetherianRing (associatedGraded S 𝔫)]
    (d : ℕ) (c : grPiece S 𝔫 d)
    (hfilter : ∀ Q ∈ associatedPrimes (associatedGraded S 𝔫)
        (associatedGraded S 𝔫),
      ¬ SupIrrelevantIdeal S 𝔫 ≤ Q → grOf S 𝔫 d c ∉ Q) :
    ∃ N : ℕ, ∀ β ∈ vvTorsion S 𝔫 (grOf S 𝔫 d c),
      ∀ g ∈ (grPlus S 𝔫) ^N, g * β = 0 := by
  have hbridge : grPlus S 𝔫 = SupIrrelevantIdeal S 𝔫 :=
    vv_grPlus_eq_irrelevant 𝔫
  have hKFG : ((vvTorsion S 𝔫 (grOf S 𝔫 d c)) : Submodule _ _).FG :=
    IsNoetherian.noetherian _
  have hFinK : Module.Finite (associatedGraded S 𝔫)
      ↥((vvTorsion S 𝔫 (grOf S 𝔫 d c)) : Submodule _ _) :=
    Module.Finite.of_fg hKFG
  have hle : grPlus S 𝔫 ≤ (Module.annihilator (associatedGraded S 𝔫)
      ↥(vvTorsion S 𝔫 (grOf S 𝔫 d c))).radical := by
    rw [← Ideal.sInf_minimalPrimes]
    apply le_sInf
    intro P hP
    have hPmin : (Module.annihilator (associatedGraded S 𝔫)
        ↥(vvTorsion S 𝔫 (grOf S 𝔫 d c))).IsMinimalPrime P := hP
    by_contra hcon
    have hrel : ¬ SupIrrelevantIdeal S 𝔫 ≤ P := by
      rw [← hbridge]
      exact hcon
    have hAss : P ∈ associatedPrimes (associatedGraded S 𝔫)
        ↥((vvTorsion S 𝔫 (grOf S 𝔫 d c)) : Submodule _ _) :=
      Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes
        _ _ hP
    have hAssG : P ∈ associatedPrimes (associatedGraded S 𝔫)
        (associatedGraded S 𝔫) := by
      rw [AssociatedPrimes.mem_iff] at hAss ⊢
      exact hAss.map_of_injective
        ((vvTorsion S 𝔫 (grOf S 𝔫 d c) : Submodule _ _).subtype)
        (fun a b h => Subtype.ext h)
    exact hfilter P hAssG hrel (hPmin.le (vvTorsion_ann_mem 𝔫 d c))
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hle
    (Ideal.fg_of_isNoetherianRing _)
  refine ⟨N, fun β hβ g hg => ?_⟩
  have hsmul := Module.mem_annihilator.mp (hN hg) ⟨β, hβ⟩
  have hval : g • β = (0 : associatedGraded S 𝔫) := congrArg Subtype.val hsmul
  rw [smul_eq_mul] at hval
  exact hval

#print axioms vvTorsion_pow_mul_eq_zero

/-! ## §3. Vanishing in high degree -/

/-- Every homogeneous element of degree `j ≥ N` lies in `grPlus^N`
(generation in degree 1, via `gr_of_mem_grPlus_pow`).
-/
theorem vv_grOf_mem_grPlus_pow {S : Type*} [CommRing S] (𝔫 : Ideal S)
    (N j : ℕ) (a : grPiece S 𝔫 j) (h : N ≤ j) :
    grOf S 𝔫 j a ∈ (grPlus S 𝔫) ^N := by
  obtain ⟨r, rfl⟩ := grPiece_mk_surjective S 𝔫 j a
  exact Ideal.pow_le_pow_right h (gr_of_mem_grPlus_pow S 𝔫 j (r : S) r.2)

#print axioms vv_grOf_mem_grPlus_pow

/-- Vanishing (§3): every `K`-element has zero homogeneous components past
`D + N` — finite homogeneous generation (§1) plus uniform torsion (§2)
plus generation in degree 1.
-/
theorem vvTorsion_vanishes {S : Type*} [CommRing S] (𝔫 : Ideal S)
    [IsNoetherianRing (associatedGraded S 𝔫)]
    (d : ℕ) (c : grPiece S 𝔫 d)
    (N : ℕ)
    (hN : ∀ β ∈ vvTorsion S 𝔫 (grOf S 𝔫 d c),
      ∀ g ∈ (grPlus S 𝔫) ^ N, g * β = 0) :
    ∃ M₀ : ℕ, ∀ (m : ℕ), M₀ ≤ m →
      ∀ β ∈ vvTorsion S 𝔫 (grOf S 𝔫 d c), grCoeff S 𝔫 β m = 0 := by
  classical
  obtain ⟨G, D, hmem, hhom, hspan⟩ :=
    vvTorsion_hom_gens 𝔫 d c (Ideal.fg_of_isNoetherianRing _)
  refine ⟨D + N, fun m hm β hβ => ?_⟩
  have hβspan : β ∈ Ideal.span (↑G : Set (associatedGraded S 𝔫)) := by
    rw [hspan]
    exact hβ
  have key : ∀ x ∈ Ideal.span (↑G : Set (associatedGraded S 𝔫)),
      ∀ r : associatedGraded S 𝔫, grCoeff S 𝔫 (r * x) m = 0 := by
    intro x hx
    refine Submodule.span_induction
      (p := fun x _ => ∀ r : associatedGraded S 𝔫, grCoeff S 𝔫 (r * x) m = 0)
      ?_ ?_ ?_ ?_ hx
    · intro g hg r
      rw [Finset.mem_coe] at hg
      obtain ⟨i, hiD, hgi⟩ := hhom g hg
      rw [← gr_sum_support S 𝔫 r]
      have hexpand : ((∑ j ∈ (toDirectSum S 𝔫 r).support,
            grOf S 𝔫 j (grCoeff S 𝔫 r j)) * g) =
          ∑ j ∈ (toDirectSum S 𝔫 r).support,
            (grOf S 𝔫 j (grCoeff S 𝔫 r j) * g) :=
        Finset.sum_mul _ _ _
      rw [hexpand, vv_grCoeff_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hji : j + i = m
      · have hdeg : N ≤ j := by omega
        have h0 : grOf S 𝔫 j (grCoeff S 𝔫 r j) * g = 0 :=
          hN g (hmem g hg) _ (vv_grOf_mem_grPlus_pow 𝔫 N j _ hdeg)
        rw [h0]
        exact grCoeff_zero S 𝔫 m
      · rw [← hgi, grOf_mul]
        exact grCoeff_of_ne S 𝔫 _ _ _ (Ne.symm hji)
    · intro r
      rw [mul_zero]
      exact grCoeff_zero S 𝔫 m
    · intro x1 x2 _ _ ih1 ih2 r
      rw [mul_add, grCoeff_add, ih1 r, ih2 r, add_zero]
    · intro a x _ ih r
      rw [smul_eq_mul, ← mul_assoc]
      exact ih (r * a)
  have h1 := key β hβspan 1
  rwa [one_mul] at h1

#print axioms vvTorsion_vanishes

/-! ## §4. The quotient-side eventual trace from filter-regularity -/

/-- Every nonzero element has an `𝔫`-adic order, from an explicit Krull
hypothesis (generalizes `vv_order_of_ne_zero`, which bakes in locality).
-/
theorem vv_order_of_ne_zero_of_krull {S : Type*} [CommRing S] (𝔫 : Ideal S)
    (hkrull : ⨅ i : ℕ, 𝔫 ^ i = ⊥) {z : S} (hz : z ≠ 0) :
    ∃ t : ℕ, z ∈ 𝔫 ^t ∧ z ∉ 𝔫 ^(t+1) := by
  classical
  have hbot : z ∉ (⊥ : Ideal S) := by
    rw [Submodule.mem_bot]
    exact hz
  have hex : ∃ n : ℕ, z ∉ 𝔫 ^n := by
    by_contra hcon
    have hcon' : ∀ n : ℕ, z ∈ 𝔫 ^n := by
      intro n
      by_contra h
      exact hcon ⟨n, h⟩
    have hmem : z ∈ ⨅ i : ℕ, 𝔫 ^i := (Submodule.mem_iInf _).mpr hcon'
    rw [hkrull] at hmem
    exact hbot hmem
  have hn0 : Nat.find hex ≠ 0 := by
    intro hcon
    have hspec := Nat.find_spec hex
    rw [hcon] at hspec
    exact hspec (by simp)
  obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  rw [Nat.succ_eq_add_one] at ht
  have hspec : z ∉ 𝔫 ^(t+1) := by
    rw [← ht]
    exact Nat.find_spec hex
  refine ⟨t, ?_, hspec⟩
  by_contra hcon
  have hle : Nat.find hex ≤ t := Nat.find_min' hex hcon
  omega

#print axioms vv_order_of_ne_zero_of_krull

/-- The quotient-side eventual trace (§4): filter-regularity + regularity
imply the order-one trace. Large-order quotients die by §3 (vanishing);
small-order quotients die by per-degree Artin–Rees
(`Ideal.exists_pow_inf_eq_pow_smul`) + regularity cancellation.
-/
theorem vv_trace_of_filterRegular {S : Type*} [CommRing S] [IsNoetherianRing S]
    (𝔫 : Ideal S) [IsNoetherianRing (associatedGraded S 𝔫)]
    (hkrull : ⨅ i : ℕ, 𝔫 ^ i = ⊥)
    (y : S) (hy1 : y ∈ 𝔫 ^ 1)
    (hreg : IsSMulRegular S y)
    (hfilter : ∀ Q ∈ associatedPrimes (associatedGraded S 𝔫)
        (associatedGraded S 𝔫),
      ¬ SupIrrelevantIdeal S 𝔫 ≤ Q →
        supDegOneLift S 𝔫 y hy1 ∉ Q) :
    ∃ c : ℕ, ∀ n : ℕ, c ≤ n → ∀ z : S,
      z ∈ 𝔫 ^(n+1) →
      z ∈ Ideal.span {y} →
      ∃ a : S, a ∈ 𝔫 ^n ∧ a * y = z := by
  classical
  have hFinS : Module.Finite S S := Module.Finite.self _
  have hw : supDegOneLift S 𝔫 y hy1
      = grOf S 𝔫 1 (supInitForm S 𝔫 y hy1) := rfl
  have hfilter' : ∀ Q ∈ associatedPrimes (associatedGraded S 𝔫)
      (associatedGraded S 𝔫),
      ¬ SupIrrelevantIdeal S 𝔫 ≤ Q →
        grOf S 𝔫 1 (supInitForm S 𝔫 y hy1) ∉ Q := by
    intro Q hQ hirr
    rw [← hw]
    exact hfilter Q hQ hirr
  obtain ⟨N, hN⟩ :=
    vvTorsion_pow_mul_eq_zero 𝔫 1 (supInitForm S 𝔫 y hy1) hfilter'
  obtain ⟨M₀, hvan⟩ := vvTorsion_vanishes 𝔫 1 _ N hN
  have hsup : supInitForm S 𝔫 y hy1
      = Submodule.Quotient.mk (⟨y, hy1⟩ : ↥(𝔫 ^1)) := rfl
  have hboost : ∀ t : ℕ, ∃ k : ℕ, ∀ n : ℕ, ∀ b : S,
      n + 1 ≥ k → b ∈ 𝔫 ^t → b * y ∈ 𝔫 ^(n+1) → b ∈ 𝔫 ^(n+1-k+t) := by
    intro t
    obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul 𝔫
      (Submodule.span S {y} * 𝔫 ^t)
    refine ⟨k, fun n b hn hb hby => ?_⟩
    have hmemL : b * y ∈ (((𝔫 ^(n+1) : Ideal S)) : Submodule S S) • (⊤ : Submodule S S) := by
      have h1 : (b * y) • (1 : S)
          ∈ (((𝔫 ^(n+1) : Ideal S)) : Submodule S S) • (⊤ : Submodule S S) :=
        Submodule.smul_mem_smul hby
          (show (1 : S) ∈ (⊤ : Submodule S S) from Submodule.mem_top)
      have hmul1 : (b * y) • (1 : S) = b * y := by rw [smul_eq_mul, mul_one]
      rwa [hmul1] at h1
    have hmemR : b * y ∈ Submodule.span S {y} * ↑(𝔫 ^t) :=
      Submodule.mem_span_singleton_mul.mpr ⟨b, hb, mul_comm y b⟩
    have hmem' : b * y ∈ (((𝔫 ^(n+1) : Ideal S)) : Submodule S S) • (⊤ : Submodule S S)
        ⊓ (Submodule.span S {y} * ↑(𝔫 ^t)) :=
      Submodule.mem_inf.mpr ⟨hmemL, hmemR⟩
    rw [hk (n+1) hn] at hmem'
    have hex : ∃ e ∈ 𝔫 ^(n+1-k+t), b * y = y * e := by
      refine Submodule.smul_induction_on hmem' ?_ ?_
      · intro u hu v hv
        have hvN : v ∈ Submodule.span S {y} * ↑(𝔫 ^t) :=
          (Submodule.mem_inf.mp hv).2
        obtain ⟨e_v, he_v, hve⟩ :=
          Submodule.mem_span_singleton_mul.mp hvN
        have hmemue : u * e_v ∈ 𝔫 ^(n+1-k+t) := by
          rw [pow_add]
          exact Ideal.mul_mem_mul hu he_v
        refine ⟨u * e_v, hmemue, ?_⟩
        rw [smul_eq_mul, ← hve]
        ring
      · intro z1 z2 h1 h2
        obtain ⟨e1, he1, heq1⟩ := h1
        obtain ⟨e2, he2, heq2⟩ := h2
        exact ⟨e1 + e2, add_mem he1 he2, by rw [heq1, heq2, mul_add]⟩
    obtain ⟨e, he, hbe⟩ := hex
    have hsmul : y • b = y • e := by
      rw [smul_eq_mul, smul_eq_mul, mul_comm y b]
      exact hbe
    have hbeq : b = e := hreg hsmul
    rw [hbeq]
    exact he
  obtain ⟨kAR, hkAR⟩ := Classical.skolem.mp hboost
  refine ⟨M₀ + Finset.sup (Finset.range M₀) kAR, fun n hn z hz hmem => ?_⟩
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hmem
  have hz' : b * y ∈ 𝔫 ^(n+1) := by
    rw [hb]
    exact hz
  refine ⟨b, ?_, hb⟩
  by_cases hb0 : b = 0
  · subst hb0
    exact Ideal.zero_mem _
  · obtain ⟨t₀, ht₀mem, ht₀nmem⟩ :=
      vv_order_of_ne_zero_of_krull 𝔫 hkrull hb0
    by_cases htn : t₀ < n
    · have htM : t₀ < M₀ := by
        by_contra hcon
        have hcon' : M₀ ≤ t₀ := not_lt.mp hcon
        have hby : b * y ∈ 𝔫 ^(t₀+1+1) :=
          Ideal.pow_le_pow_right (by omega : t₀+1+1 ≤ n+1) hz'
        have hβK : grOf S 𝔫 t₀ (Submodule.Quotient.mk
              (⟨b, ht₀mem⟩ : ↥(𝔫 ^t₀)))
            ∈ vvTorsion S 𝔫 (grOf S 𝔫 1 (supInitForm S 𝔫 y hy1)) := by
          rw [vvTorsion_mem_iff, hsup, grOf_mul, grMul_mk_mk]
          have hmk : (Submodule.Quotient.mk
                (((grMulRep S 𝔫 t₀ 1) ⟨b, ht₀mem⟩ ⟨y, hy1⟩)) :
              grPiece S 𝔫 (t₀+1)) = 0 := by
            rw [grPiece_mk_eq_zero_iff]
            change b * y ∈ 𝔫 ^(t₀+1+1)
            exact hby
          rw [hmk, grOf_zero]
        have hcoeff := hvan t₀ hcon' _ hβK
        rw [grCoeff_of] at hcoeff
        have hmem : b ∈ 𝔫 ^(t₀+1) :=
          (grPiece_mk_eq_zero_iff S 𝔫 t₀ _).mp hcoeff
        exact ht₀nmem hmem
      have hksup : kAR t₀ ≤ Finset.sup (Finset.range M₀) kAR :=
        Finset.le_sup (f := kAR) (Finset.mem_range.mpr htM)
      have hn_k : n + 1 ≥ kAR t₀ := by omega
      have hD : b ∈ 𝔫 ^(n+1-kAR t₀+t₀) := hkAR t₀ n b hn_k ht₀mem hz'
      have hle : n + 1 - kAR t₀ + t₀ ≤ t₀ := by
        by_contra hcon
        have hlt : t₀ < n + 1 - kAR t₀ + t₀ := not_le.mp hcon
        exact ht₀nmem
          (Ideal.pow_le_pow_right (by omega : t₀ + 1 ≤ n + 1 - kAR t₀ + t₀) hD)
      omega
    · have htn' : n ≤ t₀ := not_lt.mp htn
      exact Ideal.pow_le_pow_right htn' ht₀mem

#print axioms vv_trace_of_filterRegular

/-! ## §5–§6. The repaired M1: R-side trace + kernel re-plug -/

/-- SPEC (the repaired M1): the order-one trace from quotient-side graded
avoidance plus ungraded avoidance. Verbatim the §7 `SupT1TraceOfGrAvoidQuot`
binders with the ungraded-avoidance hypothesis added — the hypothesis §4
shows is exactly regularity.

Specification address (closed by `supT1Trace_of_quotAvoid_repaired`). -/
def SupT1TraceOfGrAvoidQuotRep (R : Type*) [CommRing R] [IsLocalRing R] :
    Prop :=
  ∀ (J' : Ideal R) (y : R) (hym : y ∈ IsLocalRing.maximalIdeal R),
    ¬ Ring.KrullDimLE 0 (R ⧸ J') →
    (∀ P ∈ associatedPrimes R (R ⧸ J'), y ∉ P) →
    (∀ Q ∈ associatedPrimes
        (associatedGraded (R ⧸ J') (supQuotAdicIdeal J'))
        (associatedGraded (R ⧸ J') (supQuotAdicIdeal J')),
      ¬ SupIrrelevantIdeal (R ⧸ J') (supQuotAdicIdeal J') ≤ Q →
        supDegOneLift (R ⧸ J') (supQuotAdicIdeal J')
          (Ideal.Quotient.mk J' y)
          (supQuot_mk_mem_powOne J' y hym) ∉ Q) →
    ∃ c : ℕ, ∀ n : ℕ, c ≤ n → ∀ z : R,
      z ∈ IsLocalRing.maximalIdeal R ^ (n + 2) ⊔ J' →
      z ∈ Ideal.span {y} →
      ∃ a : R, a ∈ IsLocalRing.maximalIdeal R ^ (n + 1) ⊔ J' ∧ a * y = z

#print axioms SupT1TraceOfGrAvoidQuotRep

/-- The repaired M1 (§§5–6): graded + ungraded avoidance imply the
order-one trace, unconditionally (given Noetherian `R`). Ungraded
avoidance is regularity (QuotAvoid §4); §4 gives the quotient-side trace
over `(R ⧸ J', supQuotAdicIdeal J')`; §5 reshapes it to the `𝔪ⁿ ⊔ J'`
form via the quotient correspondence + the regularity correction
(`supT1_reg_mem_of_mul_mem`, the `supColon_of_t1Data` pattern).
-/
theorem supT1Trace_of_quotAvoid_repaired {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] :
    SupT1TraceOfGrAvoidQuotRep (R := R) := by
  intro J' y hym hpos hungr hgr
  have hne : J' ≠ ⊤ := by
    rintro rfl
    apply hpos
    rw [Ring.krullDimLE_iff]
    have hsub : Subsingleton (R ⧸ (⊤ : Ideal R)) := by
      rw [← not_nontrivial_iff_subsingleton, Ideal.Quotient.nontrivial_iff]
      exact not_not_intro rfl
    have hbot : ringKrullDim (R ⧸ (⊤ : Ideal R)) = ⊥ :=
      ringKrullDim_eq_bot_iff_subsingleton.mpr hsub
    rw [hbot]
    exact bot_le
  have hnt : Nontrivial (R ⧸ J') := Ideal.Quotient.nontrivial_iff.mpr hne
  have hloc : IsLocalRing (R ⧸ J') :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J')
      Ideal.Quotient.mk_surjective
  have hhom : IsLocalHom (Ideal.Quotient.mk J') :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk J')
      Ideal.Quotient.mk_surjective
  have hneTop : supQuotAdicIdeal J' ≠ ⊤ :=
    ne_top_of_lt
      (IsLocalRing.map_maximalIdeal_lt_top (Ideal.Quotient.mk J'))
  have hkrull : ⨅ i : ℕ, (supQuotAdicIdeal J') ^i = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing _ hneTop
  have hgrNoeth : IsNoetherianRing
      (associatedGraded (R ⧸ J') (supQuotAdicIdeal J')) :=
    supAssNoethGrQuot J'
  have hregR : IsSMulRegular (R ⧸ J') y :=
    supRegular_of_avoidAss J' y hungr
  have hregS : IsSMulRegular (R ⧸ J') (Ideal.Quotient.mk J' y) :=
    EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.ColonDimDrop.supMk_regular_of_t1
      J' y hregR
  obtain ⟨c, hc⟩ := vv_trace_of_filterRegular (S := R ⧸ J')
    (supQuotAdicIdeal J') hkrull (Ideal.Quotient.mk J' y)
    (supQuot_mk_mem_powOne J' y hym) hregS hgr
  have hsup : ∀ n : ℕ, (IsLocalRing.maximalIdeal R ^ (n+2) ⊔ J').map
      (Ideal.Quotient.mk J') = (supQuotAdicIdeal J') ^(n+1+1) := by
    intro n
    have h1 : (IsLocalRing.maximalIdeal R ^ (n+2)).map
        (Ideal.Quotient.mk J') = (supQuotAdicIdeal J') ^(n+1+1) := by
      rw [Ideal.map_pow]
      rfl
    have h2 : (J').map (Ideal.Quotient.mk J') = ⊥ :=
      Ideal.map_quotient_self J'
    rw [Ideal.map_sup, h1, h2, sup_bot_eq]
  have hpre : ∀ (m : ℕ) (a₀ : R), Ideal.Quotient.mk J' a₀
      ∈ (supQuotAdicIdeal J') ^(m+1) →
      a₀ ∈ IsLocalRing.maximalIdeal R ^ (m+1) ⊔ J' := by
    intro m a₀ ha₀
    have hmap : Ideal.Quotient.mk J' a₀ ∈
        (IsLocalRing.maximalIdeal R ^ (m+1)).map
          (Ideal.Quotient.mk J') := by
      have heq : (supQuotAdicIdeal J') ^(m+1)
          = (IsLocalRing.maximalIdeal R ^ (m+1)).map
            (Ideal.Quotient.mk J') := by
        rw [Ideal.map_pow]
        rfl
      rw [heq] at ha₀
      exact ha₀
    have hmem : a₀ ∈ Ideal.comap (Ideal.Quotient.mk J')
        ((IsLocalRing.maximalIdeal R ^ (m+1)).map
          (Ideal.Quotient.mk J')) :=
      Ideal.mem_comap.mpr hmap
    rw [Ideal.comap_map_of_surjective (Ideal.Quotient.mk J')
      Ideal.Quotient.mk_surjective _, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker] at hmem
    exact hmem
  refine ⟨c, fun n hn z hz hmem => ?_⟩
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hmem
  have hmkz : Ideal.Quotient.mk J' z ∈ (supQuotAdicIdeal J') ^(n+1+1) := by
    have hmap : Ideal.Quotient.mk J' z ∈
        (IsLocalRing.maximalIdeal R ^ (n+2) ⊔ J').map
          (Ideal.Quotient.mk J') :=
      Ideal.mem_map_of_mem _ hz
    rw [hsup n] at hmap
    exact hmap
  have hspanQ : Ideal.Quotient.mk J' z
      ∈ Ideal.span {Ideal.Quotient.mk J' y} :=
    Ideal.mem_span_singleton'.mpr
      ⟨Ideal.Quotient.mk J' b, by rw [← map_mul, hb]⟩
  obtain ⟨a', ha'mem, ha'eq⟩ := hc (n+1) (by omega : c ≤ n+1) _ hmkz hspanQ
  obtain ⟨a₀, ha₀⟩ := Ideal.Quotient.mk_surjective a'
  have ha₀mem : a₀ ∈ IsLocalRing.maximalIdeal R ^ (n+1) ⊔ J' :=
    hpre n a₀ (by rw [ha₀]; exact ha'mem)
  have hbbz : Ideal.Quotient.mk J' b * Ideal.Quotient.mk J' y
      = Ideal.Quotient.mk J' z := by rw [← map_mul, hb]
  have hcorr : (a₀ - b) * y ∈ J' := by
    have h0 : Ideal.Quotient.mk J' ((a₀ - b) * y) = 0 := by
      rw [sub_mul, map_sub, map_mul, map_mul, ha₀, ha'eq, hbbz, sub_self]
    exact Ideal.Quotient.eq_zero_iff_mem.mp h0
  have hdiff : a₀ - b ∈ J' := supT1_reg_mem_of_mul_mem J' y hregR hcorr
  have hbmem : b ∈ IsLocalRing.maximalIdeal R ^ (n+1) ⊔ J' := by
    have heq : b = a₀ - (a₀ - b) := by ring
    have hleR : J' ≤ IsLocalRing.maximalIdeal R ^ (n+1) ⊔ J' := le_sup_right
    rw [heq]
    exact sub_mem ha₀mem (hleR hdiff)
  exact ⟨b, hbmem, hb⟩

#print axioms supT1Trace_of_quotAvoid_repaired

/-- The fully repaired kernel from the repaired trace: regularity is
`supRegular_of_avoidAss`, the trace is the repaired M1. (Fires; cf. the
valid but inapplicable `supT1QuotRep_of_trace`.)
-/
theorem supT1QuotRep_of_traceRep {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R]
    (htraceRep : SupT1TraceOfGrAvoidQuotRep (R := R)) :
    SupT1OfGrAvoidQuotRep (R := R) := by
  intro J' y hym hpos hungr hgr
  exact ⟨supRegular_of_avoidAss J' y hungr,
    htraceRep J' y hym hpos hungr hgr⟩

#print axioms supT1QuotRep_of_traceRep

end OrderOneTrace
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
