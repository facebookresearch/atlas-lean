/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Regular.IsSMulRegular
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.AssociatedGradedRing
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.PositiveDimTower
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.ColonTransfer
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.ColonDimDrop

/-!
# Single-element Valabrega–Valla
Proves the single-element Valabrega–Valla core over a Noetherian local
ring `S`: if the degree-1 initial form `y*` is regular on the
associated graded ring `gr(S)`, then `y` is regular on `S`
(`vv_regular_of_gr_regular`) and the order-one trace holds with
constant `c = 0` (`vv_trace_of_gr_regular`). Both go through the
Krull-intersection order argument (the textbook Artin–Rees /
Valabrega–Valla route): a minimal counterexample has an adic order `t`
(`vv_order_of_ne_zero`), and its nonzero homogeneous lift is killed by
`y*`, contradicting regularity.

## What this file proves

* (§1) `vv_order_of_ne_zero`: every nonzero element of a Noetherian
  local ring has an adic order (unconditional, via Mathlib Krull
  `Ideal.iInf_pow_eq_bot_of_isLocalRing`).
* (§2) `vv_lift_ne_zero_of_not_mem`: the homogeneous lift of an
  order-`t` element is nonzero (unconditional).
* (§3) `vv_regular_of_gr_regular`: `y*` regular on `gr(S)` implies `y`
  regular on `S` (unconditional).
* (§4) `vv_trace_of_gr_regular`: `y*` regular on `gr(S)` implies the
  `c = 0` order-one trace on `S` (unconditional).
* (§5) `vv_t1Regular_of_mkRegular`: converse of `supMk_regular_of_t1`
  — quotient-action regularity implies `R`-action regularity
  (unconditional).
* (§6) Roadblock SPECs + assembly: `VVQuotGrRegular` (graded avoidance
  on `gr(R)` implies regularity of the initial-form image on
  `gr(R ⧸ J')`), `VVQuotTraceTransfer` (quotient trace reshapes to
  `SupT1Data`), and `supT1Data_of_vvQuot` (`SupT1OfGrAvoid` from the two
  SPECs, conditional).

## Status

unconditional: `vv_maximalIdeal_ne_top`, `vv_order_of_ne_zero`,
`vv_lift_ne_zero_of_not_mem`, `vv_regular_of_gr_regular`,
`vv_trace_of_gr_regular`, `vv_t1Regular_of_mkRegular`.
SPEC (open, exact, true classically): `VVQuotGrRegular`,
`VVQuotTraceTransfer`.
conditional: `supT1Data_of_vvQuot` on the two SPECs.

## Residual register (verbatim)

closed this lane: [single-element VV regularity
`vv_regular_of_gr_regular`], [order-one trace `vv_trace_of_gr_regular`],
[R/S-action regularity bridge `vv_t1Regular_of_mkRegular`].
open (exact): [`VVQuotGrRegular` — graded avoidance on `gr(R)` implies
regularity of the initial-form image on `gr(R ⧸ J')`
lines: graded surjection + associated-prime pullback],
[`VVQuotTraceTransfer` — quotient trace reshapes to `SupT1Data`; price
~60–100 lines: maximal-ideal quotient correspondence + regularity
correction as in `supColon_of_t1Data`]. K1a fires `supT1Data_of_vvQuot`
once both land.

## References

Project (read-only): `AssociatedGradedRing.lean` (`grPiece`, `associatedGraded`,
`grMul_mk_mk`, `associatedGraded_of_mul_of`, `grPiece_mk_eq_zero_iff`),
`PositiveDimTower.lean` (`supMem_powOne`, `supInitForm`,
`supDegOneLift`), `ColonTransfer.lean` (`SupT1Data`,
`supT1_reg_mem_of_mul_mem`), `ColonDimDrop.lean`
(`SupT1OfGrAvoid`, `supMk_regular_of_t1`).

Mathlib (`lean-toolchain` pins `v4.34.0`), all read-only, all
probe-verified present: `Ideal.iInf_pow_eq_bot_of_isLocalRing`
(`RingTheory/Filtration.lean`), `DirectSum.of_injective`
(`Algebra/DirectSum/Basic.lean`),
`isSMulRegular_quotient_iff_mem_of_smul_mem`
(`RingTheory/Regular/IsSMulRegular.lean`),
`Ideal.pow_le_pow_right` (`RingTheory/Ideal/Operations.lean`),
`Ideal.mem_span_singleton'` (`RingTheory/Ideal/Span.lean`).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace ValabregaVallaSingle

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AssociatedGradedRing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.PositiveDimTower
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.ColonTransfer
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.ColonDimDrop

/-! ## §1. Adic order from Krull intersection -/

/-- The maximal ideal of a local ring is proper (via the `IsMaximal`
instance). Feeds the Krull-intersection input.
-/
theorem vv_maximalIdeal_ne_top {S : Type*} [CommRing S] [IsLocalRing S] :
    IsLocalRing.maximalIdeal S ≠ ⊤ :=
  (IsLocalRing.maximalIdeal.isMaximal S).ne_top

#print axioms vv_maximalIdeal_ne_top

/-- Every nonzero element of a Noetherian local ring has an adic order:
`z ∈ 𝔫^t` but `z ∉ 𝔫^(t+1)`. From Krull
(`Ideal.iInf_pow_eq_bot_of_isLocalRing`): `z` misses some power, and
the least such power is a successor.
-/
theorem vv_order_of_ne_zero {S : Type*} [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] {z : S} (hz : z ≠ 0) :
    ∃ t : ℕ, z ∈ IsLocalRing.maximalIdeal S ^ t ∧
      z ∉ IsLocalRing.maximalIdeal S ^ (t + 1) := by
  classical
  have hkrull : ⨅ i : ℕ, IsLocalRing.maximalIdeal S ^ i = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing _ vv_maximalIdeal_ne_top
  have hbot : z ∉ (⊥ : Ideal S) := by
    rw [Submodule.mem_bot]
    exact hz
  have hex : ∃ n : ℕ, z ∉ IsLocalRing.maximalIdeal S ^ n := by
    by_contra hcon
    push Not at hcon
    have hmem : z ∈ ⨅ i : ℕ, IsLocalRing.maximalIdeal S ^ i :=
      (Submodule.mem_iInf _).mpr hcon
    rw [hkrull] at hmem
    exact hbot hmem
  have hn0 : Nat.find hex ≠ 0 := by
    intro hcon
    have hspec := Nat.find_spec hex
    rw [hcon] at hspec
    exact hspec (by simp)
  obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  rw [Nat.succ_eq_add_one] at ht
  have hspec : z ∉ IsLocalRing.maximalIdeal S ^ (t + 1) := by
    rw [← ht]
    exact Nat.find_spec hex
  refine ⟨t, ?_, hspec⟩
  by_contra hcon
  have hle : Nat.find hex ≤ t := Nat.find_min' hex hcon
  omega

#print axioms vv_order_of_ne_zero

/-! ## §2. Nonzero homogeneous lifts -/

/-- The homogeneous lift of an order-`t` element is nonzero: from
`DirectSum.of_injective` plus `grPiece_mk_eq_zero_iff`.
-/
theorem vv_lift_ne_zero_of_not_mem {S : Type*} [CommRing S] (I : Ideal S)
    (t : ℕ) (z : S) (hz : z ∈ I ^ t) (hzm : z ∉ I ^ (t + 1)) :
    DirectSum.of (grPiece S I) t
        (Submodule.Quotient.mk (⟨z, hz⟩ : ↥(I ^ t))) ≠ 0 := by
  intro hcon
  have hinj : Function.Injective (DirectSum.of (grPiece S I) t) :=
    DirectSum.of_injective t
  have h0 : (Submodule.Quotient.mk (⟨z, hz⟩ : ↥(I ^ t)) :
      grPiece S I t) = 0 :=
    hinj (hcon.trans (map_zero _).symm)
  rw [grPiece_mk_eq_zero_iff] at h0
  exact hzm h0

#print axioms vv_lift_ne_zero_of_not_mem

/-! ## §3. Regularity from graded regularity -/

/-- Single-element Valabrega–Valla, regularity half: if the initial
form `y*` is regular on `gr(S)`, then `y` is regular on `S`. From
`vv_order_of_ne_zero`: a relation `y * z = 0` with `z ≠ 0` gives an
order-`t` lift killed by `y*`, contradicting `hreg`.
-/
theorem vv_regular_of_gr_regular {S : Type*} [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] (y : S) (hym : y ∈ IsLocalRing.maximalIdeal S)
    (hreg : IsSMulRegular (associatedGraded S (IsLocalRing.maximalIdeal S))
      (supDegOneLift S (IsLocalRing.maximalIdeal S) y
        (supMem_powOne _ _ hym))) :
    IsSMulRegular S y := by
  apply IsSMulRegular.of_right_eq_zero_of_smul
  intro z hz
  rw [smul_eq_mul] at hz
  by_contra hz0
  obtain ⟨t, htmem, htnmem⟩ := vv_order_of_ne_zero hz0
  have hg0 : DirectSum.of (grPiece S (IsLocalRing.maximalIdeal S)) t
      (Submodule.Quotient.mk
        (⟨z, htmem⟩ : ↥(IsLocalRing.maximalIdeal S ^ t))) ≠ 0 :=
    vv_lift_ne_zero_of_not_mem _ t z htmem htnmem
  have hsmul : (DirectSum.of (grPiece S (IsLocalRing.maximalIdeal S)) 1
        (Submodule.Quotient.mk
          (⟨y, supMem_powOne _ _ hym⟩ :
            ↥(IsLocalRing.maximalIdeal S ^ 1)))) •
      (DirectSum.of (grPiece S (IsLocalRing.maximalIdeal S)) t
        (Submodule.Quotient.mk
          (⟨z, htmem⟩ : ↥(IsLocalRing.maximalIdeal S ^ t)))) = 0 := by
    rw [smul_eq_mul, associatedGraded_of_mul_of, grMul_mk_mk]
    have hmk0 : (Submodule.Quotient.mk (((grMulRep S
        (IsLocalRing.maximalIdeal S) 1 t)
        ⟨y, supMem_powOne _ _ hym⟩ ⟨z, htmem⟩)) :
        grPiece S (IsLocalRing.maximalIdeal S) (1 + t)) = 0 := by
      rw [grPiece_mk_eq_zero_iff]
      change y * z ∈ IsLocalRing.maximalIdeal S ^ (1 + t + 1)
      rw [hz]
      exact Ideal.zero_mem _
    rw [hmk0, map_zero]
  exact hg0 (hreg.right_eq_zero_of_smul hsmul)

#print axioms vv_regular_of_gr_regular

/-! ## §4. Order-one trace from graded regularity -/

/-- Single-element Valabrega–Valla, trace half: if `y*` is regular on
`gr(S)`, the order-one trace holds with constant `c = 0` — every
`z ∈ 𝔫^(n+1)` divisible by `y` has a quotient in `𝔫^n`. From
`vv_order_of_ne_zero`: a quotient outside `𝔫^n` has order `t < n`,
and its lift times `y*` (via commutativity) vanishes since
`z ∈ 𝔫^(t+1+1)`, contradicting `hreg`.
-/
theorem vv_trace_of_gr_regular {S : Type*} [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] (y : S) (hym : y ∈ IsLocalRing.maximalIdeal S)
    (hreg : IsSMulRegular (associatedGraded S (IsLocalRing.maximalIdeal S))
      (supDegOneLift S (IsLocalRing.maximalIdeal S) y
        (supMem_powOne _ _ hym)))
    (n : ℕ) (z : S) (hz : z ∈ IsLocalRing.maximalIdeal S ^ (n + 1))
    (hmem : z ∈ Ideal.span {y}) :
    ∃ a : S, a ∈ IsLocalRing.maximalIdeal S ^ n ∧ a * y = z := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hmem
  refine ⟨a, ?_, ha⟩
  by_contra hcon
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hcon (Ideal.zero_mem _)
  obtain ⟨t, htmem, htnmem⟩ := vv_order_of_ne_zero ha0
  have hle : t + 1 ≤ n := by
    by_contra hcon2
    push Not at hcon2
    exact hcon (Ideal.pow_le_pow_right (by omega : n ≤ t) htmem)
  have hsub2 : IsLocalRing.maximalIdeal S ^ (n + 1)
      ≤ IsLocalRing.maximalIdeal S ^ (t + 1 + 1) :=
    Ideal.pow_le_pow_right (by omega)
  have hz2 : a * y ∈ IsLocalRing.maximalIdeal S ^ (t + 1 + 1) := by
    rw [ha]
    exact hsub2 hz
  have hg0 : DirectSum.of (grPiece S (IsLocalRing.maximalIdeal S)) t
      (Submodule.Quotient.mk
        (⟨a, htmem⟩ : ↥(IsLocalRing.maximalIdeal S ^ t))) ≠ 0 :=
    vv_lift_ne_zero_of_not_mem _ t a htmem htnmem
  have hsmul : (DirectSum.of (grPiece S (IsLocalRing.maximalIdeal S)) 1
        (Submodule.Quotient.mk
          (⟨y, supMem_powOne _ _ hym⟩ :
            ↥(IsLocalRing.maximalIdeal S ^ 1)))) •
      (DirectSum.of (grPiece S (IsLocalRing.maximalIdeal S)) t
        (Submodule.Quotient.mk
          (⟨a, htmem⟩ : ↥(IsLocalRing.maximalIdeal S ^ t)))) = 0 := by
    rw [smul_eq_mul, mul_comm, associatedGraded_of_mul_of, grMul_mk_mk]
    have hmk0 : (Submodule.Quotient.mk (((grMulRep S
        (IsLocalRing.maximalIdeal S) t 1)
        ⟨a, htmem⟩ ⟨y, supMem_powOne _ _ hym⟩)) :
        grPiece S (IsLocalRing.maximalIdeal S) (t + 1)) = 0 := by
      rw [grPiece_mk_eq_zero_iff]
      change a * y ∈ IsLocalRing.maximalIdeal S ^ (t + 1 + 1)
      exact hz2
    rw [hmk0, map_zero]
  exact hg0 (hreg.right_eq_zero_of_smul hsmul)

#print axioms vv_trace_of_gr_regular

/-! ## §5. Quotient-action versus `R`-action regularity -/

/-- Converse of `supMk_regular_of_t1` (DimDrop §1): regularity of
`mk y` for the quotient's own action gives regularity of `y` for the
`R`-action, via `isSMulRegular_quotient_iff_mem_of_smul_mem`.
Together they identify the two regularity shapes over `R ⧸ J'`.
-/
theorem vv_t1Regular_of_mkRegular {R : Type*} [CommRing R] (J' : Ideal R)
    (y : R) (hreg : IsSMulRegular (R ⧸ J') (Ideal.Quotient.mk J' y)) :
    IsSMulRegular (R ⧸ J') y := by
  refine (isSMulRegular_quotient_iff_mem_of_smul_mem _ _).mpr ?_
  intro x hx
  rw [smul_eq_mul] at hx
  have h0 : Ideal.Quotient.mk J' (y * x) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hx
  rw [map_mul] at h0
  have hS : (Ideal.Quotient.mk J' y) • (Ideal.Quotient.mk J' x) = 0 := by
    rw [smul_eq_mul]
    exact h0
  have hmx : Ideal.Quotient.mk J' x = 0 := hreg.right_eq_zero_of_smul hS
  exact Ideal.Quotient.eq_zero_iff_mem.mp hmx

#print axioms vv_t1Regular_of_mkRegular

/-! ## §6. Quotient roadblocks and the K1a assembly -/

/-- SPEC (residual K1b→K1a bridge, graded side): graded avoidance of
`y*` on `gr(R)` implies regularity of the initial-form image `(mk y)*`
on `gr(R ⧸ J')`. True classically; the scoped proof pushes avoidance
through the graded surjection `gr(R) ↠ gr(R ⧸ J')` and pulls
associated primes back.

Status: open (exact residual; true classically). -/
def VVQuotGrRegular (R : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] : Prop :=
  ∀ (J' : Ideal R) [IsLocalRing (R ⧸ J')] (y : R)
    (hym : y ∈ IsLocalRing.maximalIdeal R)
    (hymS : Ideal.Quotient.mk J' y
      ∈ IsLocalRing.maximalIdeal (R ⧸ J')),
    (∀ P ∈ associatedPrimes
        (associatedGraded R (IsLocalRing.maximalIdeal R))
        (associatedGraded R (IsLocalRing.maximalIdeal R)),
      ¬ SupIrrelevantIdeal R (IsLocalRing.maximalIdeal R) ≤ P →
        supDegOneLift R (IsLocalRing.maximalIdeal R) y
          (supMem_powOne _ _ hym) ∉ P) →
    IsSMulRegular
      (associatedGraded (R ⧸ J') (IsLocalRing.maximalIdeal (R ⧸ J')))
      (supDegOneLift (R ⧸ J') (IsLocalRing.maximalIdeal (R ⧸ J'))
        (Ideal.Quotient.mk J' y) (supMem_powOne _ _ hymS))

#print axioms VVQuotGrRegular

/-- SPEC (residual K1b→K1a bridge, trace side): quotient regularity
plus the `c = 0` quotient trace reshape to `SupT1Data J' y`.
true classically; the scoped proof is the maximal-ideal quotient
correspondence (`𝔫^n` vs `𝔪^n ⊔ J'`) plus the regularity correction
(`(x - a) * y = 0` forces `x - a ∈ J'`, as in `supColon_of_t1Data`),
using `vv_t1Regular_of_mkRegular` for the regularity half.

Status: open (exact residual; true classically). -/
def VVQuotTraceTransfer (R : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] : Prop :=
  ∀ (J' : Ideal R) [IsLocalRing (R ⧸ J')] (y : R),
    IsSMulRegular (R ⧸ J') (Ideal.Quotient.mk J' y) →
    (∀ n : ℕ, ∀ z' : R ⧸ J',
      z' ∈ IsLocalRing.maximalIdeal (R ⧸ J') ^ (n + 1) →
      z' ∈ Ideal.span {Ideal.Quotient.mk J' y} →
      ∃ a' : R ⧸ J', a' ∈ IsLocalRing.maximalIdeal (R ⧸ J') ^ n ∧
        a' * Ideal.Quotient.mk J' y = z') →
    SupT1Data J' y

#print axioms VVQuotTraceTransfer

/-- K1a assembly: the one-kernel `SupT1OfGrAvoid` (DimDrop §2) from the
two quotient bridges — graded avoidance gives `(mk y)*` regularity on
`gr(R ⧸ J')` (`VVQuotGrRegular`), single-element VV gives quotient
regularity (`vv_regular_of_gr_regular`) plus the quotient trace
(`vv_trace_of_gr_regular`), and the trace reshapes to `SupT1Data`
(`VVQuotTraceTransfer`). Positivity is consumed for properness
(`J' ≠ ⊤`), mirroring `sup_exactDim_ne_top`.

Conditional on the two SPECs. -/
theorem supT1Data_of_vvQuot {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R]
    (hgr : VVQuotGrRegular (R := R)) (htr : VVQuotTraceTransfer (R := R)) :
    SupT1OfGrAvoid (R := R) := by
  intro J' y hym hpos hav
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
  have hymS : Ideal.Quotient.mk J' y ∈ IsLocalRing.maximalIdeal (R ⧸ J') :=
    map_nonunit (Ideal.Quotient.mk J') y hym
  have hgrS : IsSMulRegular
      (associatedGraded (R ⧸ J') (IsLocalRing.maximalIdeal (R ⧸ J')))
      (supDegOneLift (R ⧸ J') (IsLocalRing.maximalIdeal (R ⧸ J'))
        (Ideal.Quotient.mk J' y) (supMem_powOne _ _ hymS)) :=
    hgr J' y hym hymS hav
  have hregS : IsSMulRegular (R ⧸ J') (Ideal.Quotient.mk J' y) :=
    vv_regular_of_gr_regular (Ideal.Quotient.mk J' y) hymS hgrS
  have htrS : ∀ n : ℕ, ∀ z' : R ⧸ J',
      z' ∈ IsLocalRing.maximalIdeal (R ⧸ J') ^ (n + 1) →
      z' ∈ Ideal.span {Ideal.Quotient.mk J' y} →
      ∃ a' : R ⧸ J', a' ∈ IsLocalRing.maximalIdeal (R ⧸ J') ^ n ∧
        a' * Ideal.Quotient.mk J' y = z' :=
    vv_trace_of_gr_regular (Ideal.Quotient.mk J' y) hymS hgrS
  exact htr J' y hregS htrS

#print axioms supT1Data_of_vvQuot

end ValabregaVallaSingle
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
