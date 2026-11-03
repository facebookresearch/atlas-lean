/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.AssociatedGradedRing
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedSurjection
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.SuperficialReduction
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.PositiveDimTower

/-!
# Joint homogeneous degree-1 avoidance
Target: `SupJointHomAvoid` (`PositiveDimTower.lean`:273) — under
infinite residue field, for every ideal `J'` and every finite family `S`
of graded primes none containing the irrelevant ideal, one `y ∈ 𝔪`
satisfies both `SupSelectData J' y` and graded avoidance of `S` by its
degree-1 lift. This file proves R1 with no residual hypotheses beyond
`[IsNoetherianRing R]` (already in the master's context) and the
`Infinite κ` hypothesis R1 itself carries. R0 (`SupAssFiniteGr`) is not
needed: R1 takes `S.Finite` as an explicit input.

## Proof architecture (classical: homogeneous avoidance + line trick)

* (§0) `κ = R ⧸ 𝔪` acts on `gr¹`: `𝔪` annihilates the degree-1 piece
  (`supGrOne_torsion`), so `Module.IsTorsionBySet.module` descends the
  `R`-action (`supGrOne_resModule`, with `supResMk_smul` computation).
* (§1) Degree-1 traces: `supDegOneTrace P = {a : gr¹ | of₁ a ∈ P}` is a
  `κ`-subspace (scalar closure via `of_smul_eq`, PolySurj:198).
* (§2) Trace properness (`supDegOneTrace_ne_top`): if the trace were
  everything, generation in degree 1 (`grPiece_span_mul_eq_top`,
  Graded:581) would put every positive-degree homogeneous element in
  `P`, i.e. `gr₊ ≤ P` — contrapositive of the R1 input.
* (§3) Pure homogeneous avoidance (`supHomAvoid_degreeOne`): Mathlib
  `Submodule.exists_forall_notMem_of_forall_ne_top` over the finite
  family of proper traces (needs `Field κ` from `Ideal.Quotient.field`
  + `Infinite κ`).
* (§4) Joint step (`supJointHomAvoid_of_seeds`): given select-seed `y₀`
  (proved `supSopSelect`) and homogeneous-seed `w` (`w* ≠ 0`, `w*`
  avoids `S`), the affine line `y₀ + t • w` has at most one bad residue
  per minimal prime (quotient-by-`Q` domain argument, `Q ≤ 𝔪`) and at
  most one bad residue per `P ∈ S` (trace-subspace argument); `κ`
  infinite supplies a good residue. The `S = ∅` case bypasses the line
  (`supSopSelect` + vacuous graded half).
* (§5) `supJointHomAvoid`: the exact `SupJointHomAvoid` def, no R0.
* (§6) Plugs: `supTowerPosDim_of_graded_narrow` (the:341 master with
  R1 filled — tower conditional on `[R0, R2]` only),
  `supTowerPosDim_select_proj_narrow` (the:375 shape),
  `hChiReduceAtAss_of_gradedNarrow` (the:559 H5 shape from per-`Q`
  `[Infinite, R0, R2, R3]`).

## Status

* All §0–§6: unconditional (given `[IsNoetherianRing R]` + `Infinite κ`
  where stated; both already present at the:341 use site).
* Overall: R1 closed. Residual register: empty for this file. The
  remaining tower inputs are R0/R2/R3/R4 (owned by sibling lanes).

## Grep-verified Mathlib claims (v4.34.0, checked this lane)

* Present: `Submodule.exists_forall_notMem_of_forall_ne_top`
  (`Algebra/Module/Submodule/Union.lean`),
  `Module.IsTorsionBySet.module`
  (`Algebra/Module/Torsion/Basic.lean`),
  `Ideal.Quotient.field` (`RingTheory/Ideal/Quotient/Basic.lean`),
  `Ideal.Quotient.isDomain` (`RingTheory/Ideal/Quotient/Basic.lean`),
  `Ideal.finite_minimalPrimes_of_isNoetherianRing`
  (`RingTheory/Ideal/MinimalPrime/Noetherian.lean`).
* No Mathlib-absence claim is made here: homogeneous avoidance over
  `gr¹` is built below (§§0–3) rather than cited.

## References

Project (read-only): `PositiveDimTower.lean` (`SupJointHomAvoid`
:273, `supTowerPosDim_of_graded`:341, `supTowerPosDim_select_proj`
:375, `hChiReduceAtAss_posDim_of_tower`:559, `supMem_powOne`,
`supDegOneLift`, `SupIrrelevantIdeal`), `SuperficialReduction.lean`
(`SupSelectData`:165, `supSopSelect`:380), `AssociatedGradedRing.lean`
(`grPiece`:110, `associatedGraded`:548, `grPiece_span_mul_eq_top`
:581), `GradedSurjection.lean` (`of_smul_eq`:198),
`TowerClosure.lean` (`SupTowerPosDim`:330).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace JointAvoidance

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.ChiDegreeMaster
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AssociatedGradedRing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjection
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.SuperficialReduction
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.TowerClosure
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.PositiveDimTower

/-! ## §0. The residue-field action on `gr¹` -/

/-- `𝔪` annihilates the degree-1 graded piece: for `m ∈ 𝔪` and
`x = [a]`, `m • x = [m * a] = 0` since
`m * a ∈ 𝔪 ^ 1 * 𝔪 ^ 1 = 𝔪 ^ (1 + 1)`.
-/
theorem supGrOne_torsion {R : Type*} [CommRing R] [IsLocalRing R] :
    Module.IsTorsionBySet R (grPiece R (IsLocalRing.maximalIdeal R) 1)
      (IsLocalRing.maximalIdeal R) := by
  intro x a
  obtain ⟨r, rfl⟩ := grPiece_mk_surjective R (IsLocalRing.maximalIdeal R) 1 x
  rw [grPiece_mk_smul, grPiece_mk_eq_zero_iff, pow_add]
  have ha1 : (a : R) ∈ IsLocalRing.maximalIdeal R ^ 1 := by
    rw [pow_one]
    exact SetLike.mem_coe.mp a.2
  exact Ideal.mul_mem_mul ha1 r.2

#print axioms supGrOne_torsion

/-- The residue-field action on `gr¹`: the `R`-action descends since
`𝔪` annihilates (`supGrOne_torsion`), via
`Module.IsTorsionBySet.module`.
-/
instance supGrOne_resModule {R : Type*} [CommRing R] [IsLocalRing R] :
    Module (R ⧸ IsLocalRing.maximalIdeal R)
      (grPiece R (IsLocalRing.maximalIdeal R) 1) :=
  Module.IsTorsionBySet.module supGrOne_torsion

#print axioms supGrOne_resModule

/-- Computation rule for the residue action: `mk b • x = b • x`.
-/
@[simp]
theorem supResMk_smul {R : Type*} [CommRing R] [IsLocalRing R] (b : R)
    (x : grPiece R (IsLocalRing.maximalIdeal R) 1) :
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) b • x = b • x :=
  rfl

#print axioms supResMk_smul

/-! ## §1. Degree-1 traces -/

/-- The degree-1 trace of a graded ideal: `{a : gr¹ | of₁ a ∈ P}`, as a
`κ`-subspace. Scalar closure: `of₁ (r • a) = of₀ [r]₀ * of₁ a ∈ P`
(`of_smul_eq`, PolySurj:198).
-/
def supDegOneTrace {R : Type*} [CommRing R] [IsLocalRing R]
    (P : Ideal (associatedGraded R (IsLocalRing.maximalIdeal R))) :
    Submodule (R ⧸ IsLocalRing.maximalIdeal R)
      (grPiece R (IsLocalRing.maximalIdeal R) 1) where
  carrier := {a | DirectSum.of (grPiece R (IsLocalRing.maximalIdeal R)) 1 a ∈ P}
  zero_mem' := by
    change DirectSum.of (grPiece R (IsLocalRing.maximalIdeal R)) 1
      (0 : grPiece R (IsLocalRing.maximalIdeal R) 1) ∈ P
    rw [map_zero]
    exact Submodule.zero_mem _
  add_mem' := by
    intro a b ha hb
    change DirectSum.of (grPiece R (IsLocalRing.maximalIdeal R)) 1 (a + b) ∈ P
    rw [map_add]
    exact add_mem ha hb
  smul_mem' := by
    intro c a ha
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
    change DirectSum.of (grPiece R (IsLocalRing.maximalIdeal R)) 1
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) r • a) ∈ P
    rw [supResMk_smul, of_smul_eq]
    exact P.mul_mem_left _ ha

#print axioms supDegOneTrace

/-- The degree-1 lift lies in `P` iff its class lies in the trace.
-/
theorem supDegOneLift_mem_trace_iff {R : Type*} [CommRing R] [IsLocalRing R]
    (y : R) (h : y ∈ IsLocalRing.maximalIdeal R ^ 1)
    (P : Ideal (associatedGraded R (IsLocalRing.maximalIdeal R))) :
    supDegOneLift R (IsLocalRing.maximalIdeal R) y h ∈ P ↔
      Submodule.Quotient.mk (⟨y, h⟩ : ↥(IsLocalRing.maximalIdeal R ^ 1)) ∈
        supDegOneTrace (R := R) P :=
  Iff.rfl

#print axioms supDegOneLift_mem_trace_iff

/-! ## §2. Trace properness from `gr₊ ⊄ P` -/

/-- The degree-1 trace of `P` is proper when `P` does not contain the
irrelevant ideal: if the trace were everything, generation in degree 1
(`grPiece_span_mul_eq_top`) would put every positive-degree
homogeneous element in `P`.
-/
theorem supDegOneTrace_ne_top {R : Type*} [CommRing R] [IsLocalRing R]
    (P : Ideal (associatedGraded R (IsLocalRing.maximalIdeal R)))
    (hP : ¬ SupIrrelevantIdeal R (IsLocalRing.maximalIdeal R) ≤ P) :
    supDegOneTrace (R := R) P ≠ ⊤ := by
  intro htop
  apply hP
  have hdeg1 : ∀ a : grPiece R (IsLocalRing.maximalIdeal R) 1,
      DirectSum.of (grPiece R (IsLocalRing.maximalIdeal R)) 1 a ∈ P := by
    intro a
    have hmem : a ∈ (⊤ : Submodule (R ⧸ IsLocalRing.maximalIdeal R)
      (grPiece R (IsLocalRing.maximalIdeal R) 1)) := Submodule.mem_top
    rw [← htop] at hmem
    exact hmem
  have hstep : ∀ m : ℕ, ∀ a : grPiece R (IsLocalRing.maximalIdeal R) (1 + m),
      DirectSum.of (grPiece R (IsLocalRing.maximalIdeal R)) (1 + m) a ∈ P := by
    intro m a
    have hspan :=
      grPiece_span_mul_eq_top R (IsLocalRing.maximalIdeal R) m
    have htop' : a ∈ (⊤ : Submodule R
        (grPiece R (IsLocalRing.maximalIdeal R) (1 + m))) :=
      Submodule.mem_top
    rw [← hspan] at htop'
    refine Submodule.span_induction (p := fun x _ =>
      DirectSum.of (grPiece R (IsLocalRing.maximalIdeal R)) (1 + m) x
        ∈ P) ?_ ?_ ?_ ?_ htop'
    · intro x hx
      obtain ⟨b, c, rfl⟩ := hx
      rw [← associatedGraded_of_mul_of]
      exact P.mul_mem_right _ (hdeg1 b)
    · rw [map_zero]
      exact Submodule.zero_mem _
    · intro x y _ _ ihx ihy
      rw [map_add]
      exact add_mem ihx ihy
    · intro r x _ ihx
      rw [of_smul_eq]
      exact P.mul_mem_left _ ihx
  apply Ideal.span_le.mpr
  intro x hx
  obtain ⟨i, hi, a, rfl⟩ := hx
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = 1 + k := ⟨i - 1, by omega⟩
  exact hstep k a

#print axioms supDegOneTrace_ne_top

/-! ## §3. Pure homogeneous degree-1 avoidance -/

/-- Pure homogeneous avoidance: over infinite `κ`, some `gr¹` class
avoids every member of a finite family of graded ideals below the
irrelevant ideal. This is Mathlib subspace avoidance
(`Submodule.exists_forall_notMem_of_forall_ne_top`) over the proper
traces (§2). Primality of `S` is not needed.
-/
theorem supHomAvoid_degreeOne {R : Type*} [CommRing R] [IsLocalRing R]
    (hInf : Infinite (R ⧸ IsLocalRing.maximalIdeal R))
    (S : Set (Ideal (associatedGraded R (IsLocalRing.maximalIdeal R))))
    (hS : S.Finite)
    (hirr : ∀ P ∈ S,
      ¬ SupIrrelevantIdeal R (IsLocalRing.maximalIdeal R) ≤ P) :
    ∃ v : grPiece R (IsLocalRing.maximalIdeal R) 1,
      ∀ P ∈ S, DirectSum.of (grPiece R (IsLocalRing.maximalIdeal R)) 1 v
        ∉ P := by
  classical
  let : Field (R ⧸ IsLocalRing.maximalIdeal R) :=
    Ideal.Quotient.field (IsLocalRing.maximalIdeal R)
  let _ := hInf
  have : Finite ↥S := Set.finite_coe_iff.mpr hS
  obtain ⟨v, hv⟩ := Submodule.exists_forall_notMem_of_forall_ne_top
    (fun P : ↥S => supDegOneTrace (R := R) P.val)
    (fun P => supDegOneTrace_ne_top (R := R) P.val (hirr P.val P.property))
  exact ⟨v, fun P hPm => hv ⟨P, hPm⟩⟩

#print axioms supHomAvoid_degreeOne

/-! ## §4. The joint step: affine-line combination of seeds -/

/-- Joint step from seeds: given a select-seed `y₀`
(`SupSelectData J' y₀`) and a homogeneous-seed `w` (`w* ≠ 0` avoiding
`S`), the affine line `y₀ + t • w` has at most one bad residue `c ∈ κ`
per minimal prime `≠ 𝔪` (quotient-by-`Q` domain argument, using
`Q ≤ 𝔪`) and at most one per `P ∈ S` (trace-subspace argument); `κ`
infinite supplies a residue that is good for all.
-/
theorem supJointHomAvoid_of_seeds {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R]
    (hInf : Infinite (R ⧸ IsLocalRing.maximalIdeal R))
    (J' : Ideal R)
    (S : Set (Ideal (associatedGraded R (IsLocalRing.maximalIdeal R))))
    (hS : S.Finite)
    (y₀ : R) (hsel : SupSelectData J' y₀)
    (w : R) (hym_w : w ∈ IsLocalRing.maximalIdeal R)
    (hw_ne : (Submodule.Quotient.mk
      (⟨w, supMem_powOne _ _ hym_w⟩ : ↥(IsLocalRing.maximalIdeal R ^ 1)) :
        grPiece R (IsLocalRing.maximalIdeal R) 1) ≠ 0)
    (hw : ∀ P ∈ S, supDegOneLift R (IsLocalRing.maximalIdeal R) w
      (supMem_powOne _ _ hym_w) ∉ P) :
    ∃ y : R, ∃ hym : y ∈ IsLocalRing.maximalIdeal R,
      SupSelectData J' y ∧
        ∀ P ∈ S, supDegOneLift R (IsLocalRing.maximalIdeal R) y
          (supMem_powOne _ _ hym) ∉ P := by
  classical
  let : Field (R ⧸ IsLocalRing.maximalIdeal R) :=
    Ideal.Quotient.field (IsLocalRing.maximalIdeal R)
  have hym_line : ∀ t : R, y₀ + t • w ∈ IsLocalRing.maximalIdeal R := by
    intro t
    have htw : t • w ∈ IsLocalRing.maximalIdeal R := by
      rw [smul_eq_mul]
      exact (IsLocalRing.maximalIdeal R).mul_mem_left _ hym_w
    exact add_mem hsel.1 htw
  set v₀ : grPiece R (IsLocalRing.maximalIdeal R) 1 :=
    Submodule.Quotient.mk
      (⟨y₀, supMem_powOne _ _ hsel.1⟩ :
        ↥(IsLocalRing.maximalIdeal R ^ 1)) with hv₀
  set v_w : grPiece R (IsLocalRing.maximalIdeal R) 1 :=
    Submodule.Quotient.mk
      (⟨w, supMem_powOne _ _ hym_w⟩ :
        ↥(IsLocalRing.maximalIdeal R ^ 1)) with hv_w
  have hw_ne' : v_w ≠ 0 := hw_ne
  have hw_mem : ∀ P ∈ S, DirectSum.of
      (grPiece R (IsLocalRing.maximalIdeal R)) 1 v_w ∉ P := by
    intro P hPm
    exact hw P hPm
  have mk_line : ∀ t : R,
      (Submodule.Quotient.mk
        (⟨y₀ + t • w, supMem_powOne _ _ (hym_line t)⟩ :
          ↥(IsLocalRing.maximalIdeal R ^ 1)) :
        grPiece R (IsLocalRing.maximalIdeal R) 1) = v₀ + t • v_w := by
    intro t
    have hsub : (⟨y₀ + t • w, supMem_powOne _ _ (hym_line t)⟩ :
        ↥(IsLocalRing.maximalIdeal R ^ 1))
        = ⟨y₀, supMem_powOne _ _ hsel.1⟩ +
          t • ⟨w, supMem_powOne _ _ hym_w⟩ :=
      Subtype.ext rfl
    rw [hsub, ← grPiece_mk_add, ← grPiece_mk_smul, ← hv₀, ← hv_w]
  have hmin : {Q : Ideal R |
      Q ∈ J'.minimalPrimes ∧ Q ≠ IsLocalRing.maximalIdeal R}.Finite :=
    (Ideal.finite_minimalPrimes_of_isNoetherianRing R J').subset
      (fun Q hQ => hQ.1)
  have hTsub : ∀ Q : Ideal R, Q ∈ J'.minimalPrimes →
      Q ≠ IsLocalRing.maximalIdeal R →
      {c : R ⧸ IsLocalRing.maximalIdeal R | ∃ t : R,
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) t = c ∧
          y₀ + t • w ∈ Q}.Subsingleton := by
    intro Q hQ hQm c₁ hc₁ c₂ hc₂
    obtain ⟨t₁, ht₁, h₁⟩ := hc₁
    obtain ⟨t₂, ht₂, h₂⟩ := hc₂
    have hQprime : Q.IsPrime := Ideal.IsMinimalPrime.isPrime hQ
    have hQle : Q ≤ IsLocalRing.maximalIdeal R :=
      IsLocalRing.le_maximalIdeal hQprime.ne_top
    have hmem : (t₁ - t₂) • w ∈ Q := by
      have hsubm := sub_mem h₁ h₂
      have heq : (y₀ + t₁ • w) - (y₀ + t₂ • w) = (t₁ - t₂) • w := by
        rw [sub_smul]
        abel
      rwa [heq] at hsubm
    have : Q.IsPrime := hQprime
    have hzero : Ideal.Quotient.mk Q (t₁ - t₂) * Ideal.Quotient.mk Q w = 0 := by
      have h0 : Ideal.Quotient.mk Q ((t₁ - t₂) • w) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr hmem
      rwa [smul_eq_mul, map_mul] at h0
    rcases mul_eq_zero.mp hzero with htz | hwz
    · have hmemQ : t₁ - t₂ ∈ Q := Ideal.Quotient.eq_zero_iff_mem.mp htz
      have hmemM : t₁ - t₂ ∈ IsLocalRing.maximalIdeal R := hQle hmemQ
      have hmk : Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) t₁ =
          Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) t₂ :=
        Ideal.Quotient.eq.mpr hmemM
      exact ht₁.symm.trans (hmk.trans ht₂)
    · have hwQ : w ∈ Q := Ideal.Quotient.eq_zero_iff_mem.mp hwz
      have htw : t₁ • w ∈ Q := by
        rw [smul_eq_mul]
        exact Q.mul_mem_left _ hwQ
      have hyQ : y₀ ∈ Q := by
        have hsubm := sub_mem h₁ htw
        have heq : (y₀ + t₁ • w) - t₁ • w = y₀ := by abel
        rwa [heq] at hsubm
      exact absurd hyQ (hsel.2 Q hQ hQm)
  have hUsub : ∀ P : Ideal (associatedGraded R (IsLocalRing.maximalIdeal R)),
      P ∈ S →
      {c : R ⧸ IsLocalRing.maximalIdeal R | ∃ t : R,
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) t = c ∧
          DirectSum.of (grPiece R (IsLocalRing.maximalIdeal R)) 1
            (Submodule.Quotient.mk (⟨y₀ + t • w,
              supMem_powOne _ _ (hym_line t)⟩ :
              ↥(IsLocalRing.maximalIdeal R ^ 1))) ∈ P}.Subsingleton := by
    intro P hPm c₁ hc₁ c₂ hc₂
    obtain ⟨t₁, ht₁, h₁⟩ := hc₁
    obtain ⟨t₂, ht₂, h₂⟩ := hc₂
    rw [mk_line] at h₁ h₂
    have e₁ : v₀ + t₁ • v_w = v₀ + c₁ • v_w := by
      rw [← ht₁, supResMk_smul]
    have e₂ : v₀ + t₂ • v_w = v₀ + c₂ • v_w := by
      rw [← ht₂, supResMk_smul]
    rw [e₁] at h₁
    rw [e₂] at h₂
    have g₁ : v₀ + c₁ • v_w ∈ supDegOneTrace (R := R) P := h₁
    have g₂ : v₀ + c₂ • v_w ∈ supDegOneTrace (R := R) P := h₂
    have hsubm := sub_mem g₁ g₂
    have heq : (v₀ + c₁ • v_w) - (v₀ + c₂ • v_w) = (c₁ - c₂) • v_w := by
      rw [sub_smul]
      abel
    rw [heq] at hsubm
    have hvw : v_w ∉ supDegOneTrace (R := R) P := hw_mem P hPm
    have hzero : c₁ - c₂ = 0 := by
      by_contra hc
      exact hvw (((supDegOneTrace (R := R) P).smul_mem_iff hc).mp hsubm)
    exact sub_eq_zero.mp hzero
  have hB₁ : (⋃ Q ∈ {Q : Ideal R |
      Q ∈ J'.minimalPrimes ∧ Q ≠ IsLocalRing.maximalIdeal R},
      {c : R ⧸ IsLocalRing.maximalIdeal R | ∃ t : R,
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) t = c ∧
          y₀ + t • w ∈ Q}).Finite :=
    hmin.biUnion (fun Q hQ => (hTsub Q hQ.1 hQ.2).finite)
  have hB₂ : (⋃ P ∈ S, {c : R ⧸ IsLocalRing.maximalIdeal R | ∃ t : R,
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) t = c ∧
        DirectSum.of (grPiece R (IsLocalRing.maximalIdeal R)) 1
          (Submodule.Quotient.mk (⟨y₀ + t • w,
            supMem_powOne _ _ (hym_line t)⟩ :
            ↥(IsLocalRing.maximalIdeal R ^ 1))) ∈ P}).Finite :=
    hS.biUnion (fun P hPm => (hUsub P hPm).finite)
  have hBfin : ((⋃ Q ∈ {Q : Ideal R |
      Q ∈ J'.minimalPrimes ∧ Q ≠ IsLocalRing.maximalIdeal R},
      {c : R ⧸ IsLocalRing.maximalIdeal R | ∃ t : R,
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) t = c ∧
          y₀ + t • w ∈ Q}) ∪
      (⋃ P ∈ S, {c : R ⧸ IsLocalRing.maximalIdeal R | ∃ t : R,
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) t = c ∧
          DirectSum.of (grPiece R (IsLocalRing.maximalIdeal R)) 1
            (Submodule.Quotient.mk (⟨y₀ + t • w,
              supMem_powOne _ _ (hym_line t)⟩ :
              ↥(IsLocalRing.maximalIdeal R ^ 1))) ∈ P})).Finite :=
    hB₁.union hB₂
  have hex : ∃ c : R ⧸ IsLocalRing.maximalIdeal R,
      c ∉ ((⋃ Q ∈ {Q : Ideal R |
        Q ∈ J'.minimalPrimes ∧ Q ≠ IsLocalRing.maximalIdeal R},
        {c : R ⧸ IsLocalRing.maximalIdeal R | ∃ t : R,
          Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) t = c ∧
            y₀ + t • w ∈ Q}) ∪
        (⋃ P ∈ S, {c : R ⧸ IsLocalRing.maximalIdeal R | ∃ t : R,
          Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) t = c ∧
            DirectSum.of (grPiece R (IsLocalRing.maximalIdeal R)) 1
              (Submodule.Quotient.mk (⟨y₀ + t • w,
                supMem_powOne _ _ (hym_line t)⟩ :
                ↥(IsLocalRing.maximalIdeal R ^ 1))) ∈ P})) := by
    by_contra hcon
    have hall : ∀ c : R ⧸ IsLocalRing.maximalIdeal R,
        c ∈ ((⋃ Q ∈ {Q : Ideal R |
          Q ∈ J'.minimalPrimes ∧ Q ≠ IsLocalRing.maximalIdeal R},
          {c : R ⧸ IsLocalRing.maximalIdeal R | ∃ t : R,
            Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) t = c ∧
              y₀ + t • w ∈ Q}) ∪
          (⋃ P ∈ S, {c : R ⧸ IsLocalRing.maximalIdeal R | ∃ t : R,
            Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) t = c ∧
              DirectSum.of (grPiece R (IsLocalRing.maximalIdeal R)) 1
                (Submodule.Quotient.mk (⟨y₀ + t • w,
                  supMem_powOne _ _ (hym_line t)⟩ :
                  ↥(IsLocalRing.maximalIdeal R ^ 1))) ∈ P})) :=
      fun c => by_contra (fun hc => hcon ⟨c, hc⟩)
    have hBeq : ((⋃ Q ∈ {Q : Ideal R |
        Q ∈ J'.minimalPrimes ∧ Q ≠ IsLocalRing.maximalIdeal R},
        {c : R ⧸ IsLocalRing.maximalIdeal R | ∃ t : R,
          Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) t = c ∧
            y₀ + t • w ∈ Q}) ∪
        (⋃ P ∈ S, {c : R ⧸ IsLocalRing.maximalIdeal R | ∃ t : R,
          Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) t = c ∧
            DirectSum.of (grPiece R (IsLocalRing.maximalIdeal R)) 1
              (Submodule.Quotient.mk (⟨y₀ + t • w,
                supMem_powOne _ _ (hym_line t)⟩ :
                ↥(IsLocalRing.maximalIdeal R ^ 1))) ∈ P})) = Set.univ :=
      Set.eq_univ_of_forall hall
    have hfinU : (Set.univ : Set (R ⧸ IsLocalRing.maximalIdeal R)).Finite := by
      rw [← hBeq]
      exact hBfin
    exact (not_finite_iff_infinite.mpr hInf) (Set.finite_univ_iff.mp hfinU)
  obtain ⟨c, hcB⟩ := hex
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective c
  refine ⟨y₀ + t • w, hym_line t, ?_, ?_⟩
  · refine ⟨hym_line t, ?_⟩
    intro Q hQ hQm hyQ
    exact hcB (Set.mem_union_left _
      (Set.mem_biUnion ⟨hQ, hQm⟩ ⟨t, ht, hyQ⟩))
  · intro P hPm hmemP
    exact hcB (Set.mem_union_right _
      (Set.mem_biUnion hPm ⟨t, ht, hmemP⟩))

#print axioms supJointHomAvoid_of_seeds

/-! ## §5. R1: joint homogeneous degree-1 avoidance -/

/-- R1 (`SupJointHomAvoid`, PosDim:273): joint homogeneous degree-1
avoidance. At `S = ∅` this is `supSopSelect` with vacuous graded half;
at `S ≠ ∅`, homogeneous avoidance (§3) gives a nonzero avoiding class,
lifted to the homogeneous-seed `w` for the joint step (§4). No R0
(`SupAssFiniteGr`) is needed: `S.Finite` is an explicit R1 input.
Primality of `S` is not needed.

both present at the:341 use site). -/
theorem supJointHomAvoid {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] :
    SupJointHomAvoid (R := R) := by
  intro hInf J' S hS _hprime hirr
  by_cases hSe : S = ∅
  · subst hSe
    obtain ⟨y, hsel⟩ := supSopSelect J'
    exact ⟨y, hsel.1, hsel, fun P hP => (Set.notMem_empty P hP).elim⟩
  · obtain ⟨v, hv⟩ := supHomAvoid_degreeOne (R := R) hInf S hS hirr
    have hv0 : v ≠ 0 := by
      intro h0
      obtain ⟨P, hPm⟩ := Set.nonempty_iff_ne_empty.mpr hSe
      have hmem : DirectSum.of (grPiece R (IsLocalRing.maximalIdeal R)) 1 v
          ∈ P := by
        rw [h0, map_zero]
        exact Submodule.zero_mem _
      exact hv P hPm hmem
    obtain ⟨r, hr⟩ := grPiece_mk_surjective R (IsLocalRing.maximalIdeal R) 1 v
    have hym_w : (r : R) ∈ IsLocalRing.maximalIdeal R := by
      simpa using r.2
    have hrr : (⟨(r : R), supMem_powOne _ _ hym_w⟩ :
        ↥(IsLocalRing.maximalIdeal R ^ 1)) = r := Subtype.ext rfl
    have hw_ne : (Submodule.Quotient.mk
        (⟨(r : R), supMem_powOne _ _ hym_w⟩ :
          ↥(IsLocalRing.maximalIdeal R ^ 1)) :
          grPiece R (IsLocalRing.maximalIdeal R) 1) ≠ 0 := by
      rw [hrr, hr]
      exact hv0
    have hw : ∀ P ∈ S, supDegOneLift R (IsLocalRing.maximalIdeal R) (r : R)
        (supMem_powOne _ _ hym_w) ∉ P := by
      intro P hPm
      have heq : supDegOneLift R (IsLocalRing.maximalIdeal R) (r : R)
          (supMem_powOne _ _ hym_w)
          = DirectSum.of (grPiece R (IsLocalRing.maximalIdeal R)) 1 v := by
        change DirectSum.of (grPiece R (IsLocalRing.maximalIdeal R)) 1
          (Submodule.Quotient.mk (⟨(r : R), supMem_powOne _ _ hym_w⟩ :
            ↥(IsLocalRing.maximalIdeal R ^ 1))) = _
        rw [hrr, hr]
      rw [heq]
      exact hv P hPm
    obtain ⟨y₀, hsel⟩ := supSopSelect J'
    exact supJointHomAvoid_of_seeds (R := R) hInf J' S hS y₀ hsel (r : R)
      hym_w hw_ne hw

#print axioms supJointHomAvoid

/-! ## §6. Plugs into the:341/:375/:559 shapes -/

/-- The:341 master with R1 filled by §5: the reshaped tower from
`[R0, R2]` only.

Conditional on exactly `[SupAssFiniteGr, SupColonOfGrAvoid]`. -/
theorem supTowerPosDim_of_graded_narrow {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R]
    (hInf : Infinite (R ⧸ IsLocalRing.maximalIdeal R))
    (hfin : SupAssFiniteGr (R := R))
    (htrans : SupColonOfGrAvoid (R := R)) :
    SupTowerPosDim (R := R) :=
  supTowerPosDim_of_graded (R := R) hInf hfin
    (supJointHomAvoid (R := R)) htrans

#print axioms supTowerPosDim_of_graded_narrow

/-- The:375 select-projection from the narrowed tower.

Conditional on exactly `[SupAssFiniteGr, SupColonOfGrAvoid]`. -/
theorem supTowerPosDim_select_proj_narrow {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R]
    (hInf : Infinite (R ⧸ IsLocalRing.maximalIdeal R))
    (hfin : SupAssFiniteGr (R := R))
    (htrans : SupColonOfGrAvoid (R := R))
    (J' : Ideal R) (hne : J' ≠ ⊤)
    (hpos : ¬ Ring.KrullDimLE 0 (R ⧸ J')) :
    ∃ y : R, SupSelectData J' y :=
  supTowerPosDim_select_proj (R := R)
    (supTowerPosDim_of_graded_narrow (R := R) hInf hfin htrans) J' hne hpos

#print axioms supTowerPosDim_select_proj_narrow

/-- The:559 H5 plug from per-`Q` narrowed towers: the verbatim
`HchiReduceAtAss` conclusion from per-`Q`
`[Infinite, R0, R2, R3]` (R1 filled by §5).

Conditional on exactly per-`Q`
`[Infinite, SupAssFiniteGr, SupColonOfGrAvoid, SupExactDimDrop]`. -/
theorem hChiReduceAtAss_of_gradedNarrow (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (htower : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) →
      ∃ dimN : ℕ,
        ringKrullDim (Localization.AtPrime Q)
          = ((((dimN : ℕ)) : ℕ∞) : WithBot ℕ∞) ∧
        Infinite (Localization.AtPrime Q ⧸
          IsLocalRing.maximalIdeal (Localization.AtPrime Q)) ∧
        SupAssFiniteGr (R := Localization.AtPrime Q) ∧
        SupColonOfGrAvoid (R := Localization.AtPrime Q) ∧
          SupExactDimDrop (R := Localization.AtPrime Q)) :
    HchiReduceAtAss m K J := by
  apply hChiReduceAtAss_posDim_of_tower m K J
  intro Q _ hQ
  obtain ⟨dimN, hpin, hInf, hfin, htrans, hexact⟩ := htower Q hQ
  exact ⟨dimN, hpin,
    supTowerPosDim_of_graded_narrow (R := Localization.AtPrime Q)
      hInf hfin htrans, hexact⟩

#print axioms hChiReduceAtAss_of_gradedNarrow

end JointAvoidance
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
