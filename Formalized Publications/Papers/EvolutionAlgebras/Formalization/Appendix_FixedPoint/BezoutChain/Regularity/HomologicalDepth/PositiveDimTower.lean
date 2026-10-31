/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.ChiDegreeMaster
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.AssociatedGradedRing
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.HilbertSamuelDegree
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.NewtonDifferences
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.SuperficialReduction
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.SesClosure
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.TowerClosure

/-!
# Positive-dimension sup-tower + H5 plug for `dimN ≥ 1`
This file discharges the G2 reshape scoped in `TowerClosure.lean`
§5: the selection-colon tower restricted to positive-dimensional ideals
(`SupTowerPosDim`, SupTowerClose:330) plus the superficial/order-one
element existence through prime avoidance on the associated graded, with
an H5-shaped conclusion (`HchiReduceAtAss`) for `dimN ≥ 1`.

## What this file proves

* (§0) Graded infrastructure (unconditional): `supMem_powOne`,
  `supInitForm` (the initial form `y ↦ y* ∈ gr¹`), `supDegOneLift`
  (its image in `associatedGraded`), `supInitForm_eq_zero_iff`,
  `SupIrrelevantIdeal` (the span of positive-degree homogeneous
  elements), `supDegOne_span_le_irrelevant`.
* (§1) Exact residual SPECs (open, scoped below, all true classically):
  `SupAssFiniteGr` (R0: `Ass(gr)` finite),
  `SupJointHomAvoid` (R1: joint minimal-prime + homogeneous degree-1
  avoidance under infinite residue field),
  `SupColonOfGrAvoid` (R2: graded avoidance + positive dimension imply
  `SupColonStabFor`),
  `SupExactDimDrop` (R3: the tower step drops exact dimension by one).
* (§2) Masters:
  `supTowerPosDim_of_graded` (conditional-exact on `[R0, R1, R2]`:
  the reshaped tower from graded inputs),
  `supTowerPosDim_select_proj` (unconditional from the tower: the tower
  extends proved `supSopSelect`'s output shape on positive-dimensional
  ideals),
  `supPosDim_of_pin_succ` (unconditional: exact pin `k+1` gives
  `¬ KrullDimLE 0`),
  `supProper_sup_span_of_mem_maximal` (unconditional: properness
  propagates inside `𝔪`),
  `supNonvanishing_one_of_tower` (conditional on `[tower]` only: the
  `dimN = 1` nonvanishing step, no exact-drop needed),
  `supNonvanishing_posDim_of_towerExact` (conditional-exact on
  `[tower, R3]`: the full positive-dimension nonvanishing induction),
  `hChiReduceAtAss_leOne_of_tower` (conditional on `[tower]`: the H5
  conclusion when every per-`Q` pin is `≤ 1`),
  `hChiReduceAtAss_posDim_of_tower` (conditional-exact on
  `[tower, R3]`: the H5 conclusion in general).

## Status

* §0: all unconditional.
* §1: all open (exact residuals, true classically; prices below).
* §2: `supTowerPosDim_of_graded` conditional-exact on
  `[SupAssFiniteGr, SupJointHomAvoid, SupColonOfGrAvoid]`;
  `supNonvanishing_one_of_tower` conditional on `[SupTowerPosDim]`;
  `supNonvanishing_posDim_of_towerExact` conditional-exact on
  `[SupTowerPosDim, SupExactDimDrop]`;
  `hChiReduceAtAss_leOne_of_tower` conditional on per-`Q`
  `[SupTowerPosDim]`; `hChiReduceAtAss_posDim_of_tower`
  conditional-exact on per-`Q` `[SupTowerPosDim, SupExactDimDrop]`.
* Overall: partial. The infinite-residue-field chain is closed
  modulo the exact residuals `[R0, R1, R2, R3]`. The finite-residue
  case needs the `R(X)` faithfully-flat base-change descent (R4,
  prose-scoped ~80–120 lines, no Lean address yet since it needs the
  transcendental base-change construction). The tower step at `dimN = 0`
  is unconditional (the `sup_dimZero_seed`, no tower needed); at
  `dimN = 1` it needs only the tower; exact-drop (R3) is needed only
  for `dimN ≥ 2`.

## Residual register with prices

* R0 `SupAssFiniteGr`: `Ass(gr_𝔪(R))` finite. Discharges from
  `IsNoetherianRing (associatedGraded R 𝔪)` via Mathlib
  `associatedPrimes.finite` (`Finiteness.lean`, grep-verified
  present). Price ~80–150 lines, all in the Noetherian transfer
  (`gr` finite over `R ⧸ 𝔪`; generation in degree 1 is partially
  proved via `grPiece_span_mul_eq_top`, Graded:581).
* R1 `SupJointHomAvoid`: joint homogeneous degree-1 avoidance.
  Price ~150–250 lines: the homogeneous prime-avoidance lemma
  (Mathlib has only inhomogeneous avoidance,
  `Ideal.subset_union_prime`, `Operations.lean`, grep-verified;
  zero homogeneous-avoidance API — `grep -ri
  "homogeneous.*avoid|avoid.*homogeneous"` over Mathlib returns
  nothing) plus the minimal-prime trace family and the
  infinite-field combinatorics.
* R2 `SupColonOfGrAvoid`: order-one transfer to `SupColonStabFor`.
  Price ~100–150 lines via the quotient `R ⧸ J'` (image of the
  initial form, associated-prime pullback). The `¬ KrullDimLE 0`
  hypothesis is load-bearing: without it the transfer is false by
  the TowerClose refutation (`supColonStabFor_maximalIdeal_false`).
* R3 `SupExactDimDrop`: exact dimension drop. Upper bound is proved
  (SopExist §3); the lower bound is a prime-chain argument needing
  catenary facts — Mathlib has no catenary API (`grep -rli
  "catenary"` returns nothing, verified) and Krull's height theorem
  (`Ideal/KrullsHeightTheorem.lean`, verified present) gives only
  upper bounds. Mathlib's exact-drop lemma
  `ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim`
  (`KrullDimension/Regular.lean`, verified present) needs a
  regular element, but tower `y` is only minimal-prime-avoiding.
  Price ~100–200 lines. Assumed only at `R_Q` (localizations of
  polynomial rings, hence catenary, so true there).
* R4 (prose-only): finite-residue-field `R(X)` descent. ~80–120 lines.

## Grep-verified Mathlib-absence claims (v4.34.0, all checked this lane)

* `grep -ri "superficial"` → one prose comment only
  (`Topology/Semicontinuity/Defs.lean`); zero superficial-element API.
* `grep -ri "associatedGraded"` → zero hits; `grep -rni
  "associated_graded|associated graded"` → only the unrelated
  homological-bicomplex functor (`HomologicalBicomplex.lean`).
* `grep -rni "order-one|order one element|superficial element"` →
  zero hits.
* `grep -rni "homogeneous.*avoid|avoid.*homogeneous"` → zero hits.
* `grep -rli "catenary"` → zero hits.
* Present (used or cited, not claimed absent): `Ideal.subset_union_prime`
  (`Ideal/Operations.lean`), `associatedPrimes.finite`
  (`AssociatedPrime/Finiteness.lean`), Krull height theorem
  (`Ideal/KrullsHeightTheorem.lean`), regular-case exact drop
  (`KrullDimension/Regular.lean`).

## References

Project (read-only): `SuperficialReduction.lean` (`SupSelectData`:165,
`supSopSelect`:380, `supChi`, `IsSupSes`, `sup_lengthFin_supChi`,
`supChi_bot`), `SesClosure.lean` (`SupColonStabFor`:290,
`supSes_of_colonStab`, `sup_tower_nonvanishing`, `sup_dimZero_seed`,
`sup_nonvanishing_lift`, `sup_nonvanishing_shift`, `supBot_ne_top`,
`hChiReduceAtAss_of_towers`:757), `TowerClosure.lean`
(`SupTowerPosDim`:330, `supColonStabFor_maximalIdeal_false`),
`AssociatedGradedRing.lean` (`grPiece`:110, `associatedGraded`:548,
`grPiece_mk_eq_zero_iff`:124), `ChiDegreeMaster.lean` (`chiFunQ`
:121, `HchiReduceAtAss`:153).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace PositiveDimTower

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.NewtonDifferences
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.SuperficialReduction
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.SesClosure
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.TowerClosure
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.ChiDegreeMaster
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AssociatedGradedRing

/-! ## §0. Graded infrastructure: initial forms and the irrelevant ideal -/

/-- Membership in `I` unfolds to membership in `I ^ 1` (feeds the
initial-form map).
-/
theorem supMem_powOne {R : Type*} [CommRing R] (I : Ideal R) (y : R)
    (h : y ∈ I) : y ∈ I ^ 1 := by
  rwa [pow_one]

#print axioms supMem_powOne

/-- The initial form of `y ∈ I ^ 1`: its class in the degree-1 graded
piece `I ^ 1 ⧸ I ^ (1 + 1)`. Order-one elements are those with nonzero
initial form (`supInitForm_eq_zero_iff`).
-/
def supInitForm (R : Type*) [CommRing R] (I : Ideal R) (y : R)
    (h : y ∈ I ^ 1) : grPiece R I 1 :=
  Submodule.Quotient.mk (⟨y, h⟩ : ↥(I ^ 1))

#print axioms supInitForm

/-- The initial form vanishes iff `y ∈ I ^ (1 + 1)`: direct
instantiation of `grPiece_mk_eq_zero_iff` (Graded:124).
-/
theorem supInitForm_eq_zero_iff {R : Type*} [CommRing R] (I : Ideal R)
    (y : R) (h : y ∈ I ^ 1) :
    supInitForm R I y h = 0 ↔ y ∈ I ^ (1 + 1) :=
  grPiece_mk_eq_zero_iff R I 1 ⟨y, h⟩

#print axioms supInitForm_eq_zero_iff

/-- The degree-1 lift of `y` into the associated graded ring: the
homogeneous degree-1 element `y*`. This is the element on which prime
avoidance is performed (R1) and whose avoidance implies the colon
condition (R2).
-/
def supDegOneLift (R : Type*) [CommRing R] (I : Ideal R) (y : R)
    (h : y ∈ I ^ 1) : associatedGraded R I :=
  DirectSum.of (grPiece R I) 1 (supInitForm R I y h)

#print axioms supDegOneLift

/-- The irrelevant ideal of the associated graded ring: the span of
all positive-degree homogeneous elements. Avoidance (R1) is performed
only at primes not containing it (the classical `gr₊`-avoidance).
-/
def SupIrrelevantIdeal (R : Type*) [CommRing R] (I : Ideal R) :
    Ideal (associatedGraded R I) :=
  Ideal.span {x : associatedGraded R I |
    ∃ i : ℕ, ∃ _ : 1 ≤ i, ∃ a : grPiece R I i,
      DirectSum.of (grPiece R I) i a = x}

#print axioms SupIrrelevantIdeal

/-- The degree-1 homogeneous span lies inside the irrelevant ideal:
every degree-1 homogeneous element is a positive-degree generator.
-/
theorem supDegOne_span_le_irrelevant {R : Type*} [CommRing R]
    (I : Ideal R) :
    Ideal.span {x : associatedGraded R I |
        ∃ a : grPiece R I 1, DirectSum.of (grPiece R I) 1 a = x}
      ≤ SupIrrelevantIdeal R I := by
  apply Ideal.span_le.mpr
  intro x hx
  obtain ⟨a, rfl⟩ := hx
  exact Ideal.subset_span ⟨1, le_rfl, a, rfl⟩

#print axioms supDegOne_span_le_irrelevant

/-! ## §1. Exact residual SPECs -/

/-- SPEC (residual R0): the associated primes of the associated graded
ring (as a module over itself) are finite. Discharges from
`IsNoetherianRing (associatedGraded R 𝔪)` via Mathlib
`associatedPrimes.finite`. The `S.Finite` input of R1 is instantiated
with the below-irrelevant part of this family in
`supTowerPosDim_of_graded`.

Status: open (exact residual; true classically
the Noetherian transfer). -/
def SupAssFiniteGr (R : Type*) [CommRing R] [IsLocalRing R] : Prop :=
  (associatedPrimes (associatedGraded R (IsLocalRing.maximalIdeal R))
    (associatedGraded R (IsLocalRing.maximalIdeal R))).Finite

#print axioms SupAssFiniteGr

/-- SPEC (residual R1): joint homogeneous degree-1 avoidance. Under
infinite residue field, for every ideal `J'` and every finite family
`S` of primes of `gr_𝔪(R)` none of which contains the irrelevant
ideal, some `y ∈ 𝔪` satisfies both the s.o.p.-selection datum
(`SupSelectData`, the exact `supSopSelect` output shape) and graded
avoidance of `S` by its degree-1 lift. Jointness (one `y` for both
halves) is the point: the select half alone is proved
(`supSopSelect`), the graded half alone is homogeneous avoidance, but
the tower needs a single element. No positivity hypothesis is needed:
pure avoidance is satisfiable at every `J'`.

Status: open (exact residual; true classically under the infinite-residue
hypothesis
family). Finite-residue fields need the R4 descent (prose-scoped). -/
def SupJointHomAvoid (R : Type*) [CommRing R] [IsLocalRing R] : Prop :=
  Infinite (R ⧸ IsLocalRing.maximalIdeal R) →
    ∀ (J' : Ideal R)
      (S : Set (Ideal (associatedGraded R (IsLocalRing.maximalIdeal R)))),
      S.Finite →
      (∀ P ∈ S, P.IsPrime) →
      (∀ P ∈ S,
        ¬ SupIrrelevantIdeal R (IsLocalRing.maximalIdeal R) ≤ P) →
      ∃ y : R, ∃ hym : y ∈ IsLocalRing.maximalIdeal R,
        SupSelectData J' y ∧
          ∀ P ∈ S, supDegOneLift R (IsLocalRing.maximalIdeal R) y
            (supMem_powOne _ _ hym) ∉ P

#print axioms SupJointHomAvoid

/-- SPEC (residual R2): the order-one transfer. If the degree-1 lift
of `y ∈ 𝔪` avoids every associated prime of `gr_𝔪(R)` not containing
the irrelevant ideal, then `y` satisfies the colon-stabilization
condition `SupColonStabFor J' y` — the exact SES input. The
`¬ Ring.KrullDimLE 0 (R ⧸ J')` hypothesis is load-bearing: without it
this transfer is false (at `J' = 𝔪` the conclusion fails for every
`y ∈ 𝔪` by `supColonStabFor_maximalIdeal_false`, while the avoidance
hypothesis is satisfiable there). The scoped proof passes through the
quotient `R ⧸ J'`.

Status: open (exact residual; true classically with positivity; price
~100–150 lines). -/
def SupColonOfGrAvoid (R : Type*) [CommRing R] [IsLocalRing R] : Prop :=
  ∀ (J' : Ideal R) (y : R) (hym : y ∈ IsLocalRing.maximalIdeal R),
    ¬ Ring.KrullDimLE 0 (R ⧸ J') →
    (∀ P ∈ associatedPrimes (associatedGraded R
        (IsLocalRing.maximalIdeal R))
        (associatedGraded R (IsLocalRing.maximalIdeal R)),
      ¬ SupIrrelevantIdeal R (IsLocalRing.maximalIdeal R) ≤ P →
        supDegOneLift R (IsLocalRing.maximalIdeal R) y
          (supMem_powOne _ _ hym) ∉ P) →
    SupColonStabFor J' y

#print axioms SupColonOfGrAvoid

/-- SPEC (residual R3): exact dimension drop along the tower step.
From the selection datum and the exact pin `dim (R ⧸ J') = k + 1`,
the quotient by `J' ⊔ span {y}` has exact dimension `k`. The upper
bound is proved (SopExist §3); this residual is the lower bound.
Assumed only at localizations `R_Q` (catenary, so true there); needed
only for `dimN ≥ 2` (the `dimN = 1` step closes without it via
`supNonvanishing_one_of_tower`).

Status: open (exact residual; true classically at `R_Q`; price
~100–200 lines: prime-chain lower bound). -/
def SupExactDimDrop (R : Type*) [CommRing R] [IsLocalRing R] : Prop :=
  ∀ (J' : Ideal R) (y : R) (k : ℕ),
    SupSelectData J' y →
    ringKrullDim (R ⧸ J') = ((((k + 1 : ℕ)) : ℕ∞) : WithBot ℕ∞) →
    ringKrullDim (R ⧸ (J' ⊔ Ideal.span {y}))
      = ((((k : ℕ)) : ℕ∞) : WithBot ℕ∞)

#print axioms SupExactDimDrop

/-! ## §2. Masters: the tower from graded inputs, and the H5 plug -/

/-- The reshaped tower from graded inputs: R0 supplies the finite
family (restricted to primes below the irrelevant ideal), R1 the joint
select-plus-avoid element, R2 the colon conclusion. The positivity
hypothesis `hpos` is consumed by R2 (where it is load-bearing).

Conditional on exactly
`[SupAssFiniteGr, SupJointHomAvoid, SupColonOfGrAvoid]`. -/
theorem supTowerPosDim_of_graded {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R]
    (hInf : Infinite (R ⧸ IsLocalRing.maximalIdeal R))
    (hfin : SupAssFiniteGr (R := R))
    (havoid : SupJointHomAvoid (R := R))
    (htrans : SupColonOfGrAvoid (R := R)) :
    SupTowerPosDim (R := R) := by
  intro J' hne hpos
  have hfin' : (associatedPrimes
      (associatedGraded R (IsLocalRing.maximalIdeal R))
      (associatedGraded R (IsLocalRing.maximalIdeal R))).Finite := hfin
  have hSfin : {P : Ideal (associatedGraded R
      (IsLocalRing.maximalIdeal R)) |
      P ∈ associatedPrimes (associatedGraded R (IsLocalRing.maximalIdeal R))
        (associatedGraded R (IsLocalRing.maximalIdeal R)) ∧
        ¬ SupIrrelevantIdeal R (IsLocalRing.maximalIdeal R) ≤ P}.Finite :=
    hfin'.subset (fun P hP => hP.1)
  obtain ⟨y, hym, hsel, hgr⟩ :=
    havoid hInf J' _ hSfin
      (fun P hP => IsAssociatedPrime.isPrime hP.1)
      (fun P hP => hP.2)
  exact ⟨y, hsel,
    htrans J' y hym hpos (fun P hPmem hPirr => hgr P ⟨hPmem, hPirr⟩)⟩

#print axioms supTowerPosDim_of_graded

/-- The tower extends proved `supSopSelect`: projecting the tower
conclusion to its selection half recovers the exact `supSopSelect`
output shape (`∃ y, SupSelectData J' y`) on positive-dimensional
ideals. This is the reuse point: any R1 proof must produce selection
data compatible with SopExist §2, and the tower packages it with the
colon half that `supSopSelect` cannot supply.
-/
theorem supTowerPosDim_select_proj {R : Type*} [CommRing R]
    [IsLocalRing R]
    (htower : SupTowerPosDim (R := R)) (J' : Ideal R) (hne : J' ≠ ⊤)
    (hpos : ¬ Ring.KrullDimLE 0 (R ⧸ J')) :
    ∃ y : R, SupSelectData J' y := by
  obtain ⟨y, hsel, _⟩ := htower J' hne hpos
  exact ⟨y, hsel⟩

#print axioms supTowerPosDim_select_proj

/-- An exact dimension pin `k + 1` gives positive dimension. The
`exact_mod_cast` step mirrors the proved pattern in
`not_krullDimLE_zero_mvPolynomial`
(`Geometry/CurveMeetsHyperplane.lean`).
-/
theorem supPosDim_of_pin_succ {T : Type*} [CommRing T] (k : ℕ)
    (hpin : ringKrullDim T = ((((k + 1 : ℕ)) : ℕ∞) : WithBot ℕ∞)) :
    ¬ Ring.KrullDimLE 0 T := by
  rw [Ring.krullDimLE_iff, hpin]
  intro hle
  have hN : k + 1 ≤ 0 := by exact_mod_cast hle
  omega

#print axioms supPosDim_of_pin_succ

/-- Properness propagates along the tower step: adjoining a generator
from the maximal ideal keeps the ideal proper. (Extracts the argument
used inside `sup_tower_nonvanishing`.)
-/
theorem supProper_sup_span_of_mem_maximal {R : Type*} [CommRing R]
    [IsLocalRing R] (J : Ideal R) (y : R) (hne : J ≠ ⊤)
    (hym : y ∈ IsLocalRing.maximalIdeal R) :
    J ⊔ Ideal.span {y} ≠ ⊤ := by
  have hJm : J ≤ IsLocalRing.maximalIdeal R :=
    IsLocalRing.le_maximalIdeal hne
  have hym' : Ideal.span {y} ≤ IsLocalRing.maximalIdeal R :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hym)
  have hle : J ⊔ Ideal.span {y} ≤ IsLocalRing.maximalIdeal R :=
    sup_le hJm hym'
  intro hcon
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top
    (top_le_iff.mp (hcon ▸ hle))

#print axioms supProper_sup_span_of_mem_maximal

/-- The `dimN = 1` nonvanishing step from the tower alone (no
exact-drop needed): fire the tower once at the positive-dimensional
`J`, seed nonvanishing at the stepped ideal (`sup_dimZero_seed` needs
no pin), shift, and lift across the SES equation
(`supSes_of_colonStab`).

Conditional on `[SupTowerPosDim]`. -/
theorem supNonvanishing_one_of_tower {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (J : Ideal R)
    (hpin : ringKrullDim (R ⧸ J) = ((((1 : ℕ)) : ℕ∞) : WithBot ℕ∞))
    (hne : J ≠ ⊤)
    (htower : SupTowerPosDim (R := R)) :
    ¬ seqDiff 1 (fun n : ℕ => ((supChi (R := R) J n : ℕ) : ℚ))
      =ᶠ[Filter.atTop] 0 := by
  have hpos : ¬ Ring.KrullDimLE 0 (R ⧸ J) :=
    supPosDim_of_pin_succ 0 hpin
  obtain ⟨y, hsel, hcol⟩ := htower J hne hpos
  have hne' : J ⊔ Ideal.span {y} ≠ ⊤ :=
    supProper_sup_span_of_mem_maximal J y hne hsel.1
  have hIH : ¬ seqDiff 0
      (fun n : ℕ => ((supChi (R := R) (J ⊔ Ideal.span {y}) n : ℕ) : ℚ))
      =ᶠ[Filter.atTop] 0 := by
    rw [seqDiff_zero]
    exact sup_dimZero_seed _ hne'
  have hshift : ¬ seqDiff 0
      (fun n : ℕ => ((supChi (R := R) (J ⊔ Ideal.span {y}) (n + 1) :
        ℕ) : ℚ)) =ᶠ[Filter.atTop] 0 :=
    sup_nonvanishing_shift _ 0 hIH
  have hsesJy : IsSupSes (supChi (R := R) J)
      (supChi (R := R) (J ⊔ Ideal.span {y})) :=
    supSes_of_colonStab J y hsel.1 hcol (sup_lengthFin_supChi J)
      (sup_lengthFin_supChi (J ⊔ Ideal.span {y}))
  exact sup_nonvanishing_lift (supChi (R := R) J)
    (supChi (R := R) (J ⊔ Ideal.span {y})) 0 hsesJy hshift

#print axioms supNonvanishing_one_of_tower

/-- The positive-dimension nonvanishing induction: from the exact pin
`dim (R ⧸ J) = dimN`, the `dimN`-th difference of `χ` does not
vanish. HilbertFunctionCount on `dimN`: the seed (`sup_dimZero_seed`) at `0`;
at each step positivity comes from the pin
(`supPosDim_of_pin_succ`), the tower fires, exact-drop (R3) re-pins
the stepped ideal, and nonvanishing lifts across the SES equation.
This is the `sup_tower_nonvanishing` shape with the uninhabitable
full tower replaced by `[SupTowerPosDim, SupExactDimDrop]`.

Conditional on exactly `[SupTowerPosDim, SupExactDimDrop]`. -/
theorem supNonvanishing_posDim_of_towerExact {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (dimN : ℕ) (J : Ideal R)
    (hpin : ringKrullDim (R ⧸ J) = ((((dimN : ℕ)) : ℕ∞) : WithBot ℕ∞))
    (hne : J ≠ ⊤)
    (htower : SupTowerPosDim (R := R))
    (hexact : SupExactDimDrop (R := R)) :
    ¬ seqDiff dimN (fun n : ℕ => ((supChi (R := R) J n : ℕ) : ℚ))
      =ᶠ[Filter.atTop] 0 := by
  revert J hpin hne
  induction dimN with
  | zero =>
    intro J _ hne
    rw [seqDiff_zero]
    exact sup_dimZero_seed J hne
  | succ k ih =>
    intro J hpin hne
    have hpos : ¬ Ring.KrullDimLE 0 (R ⧸ J) :=
      supPosDim_of_pin_succ k hpin
    obtain ⟨y, hsel, hcol⟩ := htower J hne hpos
    have hdrop : ringKrullDim (R ⧸ (J ⊔ Ideal.span {y}))
        = ((((k : ℕ)) : ℕ∞) : WithBot ℕ∞) :=
      hexact J y k hsel hpin
    have hne' : J ⊔ Ideal.span {y} ≠ ⊤ :=
      supProper_sup_span_of_mem_maximal J y hne hsel.1
    have hIH := ih (J ⊔ Ideal.span {y}) hdrop hne'
    have hshift : ¬ seqDiff k
        (fun n : ℕ => ((supChi (R := R) (J ⊔ Ideal.span {y}) (n + 1) :
          ℕ) : ℚ)) =ᶠ[Filter.atTop] 0 :=
      sup_nonvanishing_shift _ k hIH
    have hsesJy : IsSupSes (supChi (R := R) J)
        (supChi (R := R) (J ⊔ Ideal.span {y})) :=
      supSes_of_colonStab J y hsel.1 hcol (sup_lengthFin_supChi J)
        (sup_lengthFin_supChi (J ⊔ Ideal.span {y}))
    exact sup_nonvanishing_lift (supChi (R := R) J)
      (supChi (R := R) (J ⊔ Ideal.span {y})) k hsesJy hshift

#print axioms supNonvanishing_posDim_of_towerExact

/-- The low-dimension H5 plug: the verbatim `HchiReduceAtAss`
conclusion when every per-`Q` pin is `≤ 1`, from the reshaped tower
alone (no exact-drop). At `dimN = 0` the seed fires (no tower step);
at `dimN = 1` the one-step master fires. The `chiFunQ = cast ∘
supChi ⊥` bridge is `supChi_bot`.

Conditional on per-`Q` `[SupTowerPosDim]`. -/
theorem hChiReduceAtAss_leOne_of_tower (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (htower : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) →
      ∃ dimN : ℕ,
        ringKrullDim (Localization.AtPrime Q)
          = ((((dimN : ℕ)) : ℕ∞) : WithBot ℕ∞) ∧
        dimN ≤ 1 ∧ SupTowerPosDim (R := Localization.AtPrime Q)) :
    HchiReduceAtAss m K J := by
  intro Q _ hQ
  obtain ⟨dimN, hpin, hle, htow⟩ := htower Q hQ
  refine ⟨dimN, hpin, ?_⟩
  have hlink : chiFunQ m K Q = fun n : ℕ =>
      ((supChi (R := Localization.AtPrime Q) ⊥ n : ℕ) : ℚ) := by
    funext n
    change ((HilbertSamuelDegree.hsSamuel (R := Localization.AtPrime Q) n :
      ℕ) : ℚ) = _
    rw [← supChi_bot]
  obtain rfl | rfl : dimN = 0 ∨ dimN = 1 := by omega
  · rw [hlink, seqDiff_zero]
    exact sup_dimZero_seed ⊥ supBot_ne_top
  · rw [hlink]
    have hpinBot : ringKrullDim
        (Localization.AtPrime Q ⧸ (⊥ : Ideal (Localization.AtPrime Q)))
        = ((((1 : ℕ)) : ℕ∞) : WithBot ℕ∞) := by
      have heq : ringKrullDim
          (Localization.AtPrime Q ⧸ (⊥ : Ideal (Localization.AtPrime Q)))
          = ringKrullDim (Localization.AtPrime Q) :=
        RingEquiv.ringKrullDim
          (RingEquiv.quotientBot (Localization.AtPrime Q))
      rw [heq, hpin]
    exact supNonvanishing_one_of_tower ⊥ hpinBot supBot_ne_top htow

#print axioms hChiReduceAtAss_leOne_of_tower

/-- The general H5 plug: the verbatim `HchiReduceAtAss` conclusion
(the exact `hChiReduceAtAss_of_towers` shape, SupSesClose:757) with
the uninhabitable full tower replaced by the reshaped per-`Q`
`[SupTowerPosDim, SupExactDimDrop]`. The pin transports to `⧸ ⊥` via
`RingEquiv.quotientBot`; nonvanishing is the §2 induction. This is the
input H6 fires into `hdimEqMinAtAss_of_chi_specs` for `dimN ≥ 1`
ideals (at `dimN = 0` the induction base is the seed).

Conditional on exactly per-`Q`
`[SupTowerPosDim, SupExactDimDrop]`. -/
theorem hChiReduceAtAss_posDim_of_tower (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (htower : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) →
      ∃ dimN : ℕ,
        ringKrullDim (Localization.AtPrime Q)
          = ((((dimN : ℕ)) : ℕ∞) : WithBot ℕ∞) ∧
        SupTowerPosDim (R := Localization.AtPrime Q) ∧
          SupExactDimDrop (R := Localization.AtPrime Q)) :
    HchiReduceAtAss m K J := by
  intro Q _ hQ
  obtain ⟨dimN, hpin, htow, hex⟩ := htower Q hQ
  refine ⟨dimN, hpin, ?_⟩
  have hlink : chiFunQ m K Q = fun n : ℕ =>
      ((supChi (R := Localization.AtPrime Q) ⊥ n : ℕ) : ℚ) := by
    funext n
    change ((HilbertSamuelDegree.hsSamuel (R := Localization.AtPrime Q) n :
      ℕ) : ℚ) = _
    rw [← supChi_bot]
  rw [hlink]
  have hpinBot : ringKrullDim
      (Localization.AtPrime Q ⧸ (⊥ : Ideal (Localization.AtPrime Q)))
      = ((((dimN : ℕ)) : ℕ∞) : WithBot ℕ∞) := by
    have heq : ringKrullDim
        (Localization.AtPrime Q ⧸ (⊥ : Ideal (Localization.AtPrime Q)))
        = ringKrullDim (Localization.AtPrime Q) :=
      RingEquiv.ringKrullDim
        (RingEquiv.quotientBot (Localization.AtPrime Q))
    rw [heq, hpin]
  have hbot : (⊥ : Ideal (Localization.AtPrime Q)) ≠ ⊤ :=
    supBot_ne_top
  exact supNonvanishing_posDim_of_towerExact dimN ⊥ hpinBot hbot
    htow hex

#print axioms hChiReduceAtAss_posDim_of_tower

end PositiveDimTower
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
