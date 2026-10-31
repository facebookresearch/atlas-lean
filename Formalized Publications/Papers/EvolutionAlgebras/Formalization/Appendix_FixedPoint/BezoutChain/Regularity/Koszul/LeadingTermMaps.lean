/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.FiltrationLift
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.AssociatedGradedRing
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedSurjection
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.KoszulComplex
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.AugmentedConeStep
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedLift
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.StdBasis

/-!
# Homogeneous leading-term maps for the Koszul filtration (FiltrLeadData bridge)

The file-7 residual `FiltrLeadData` (`FiltrationLift.lean`:262: leading-term
maps `F(t,k) → ⋀^k(gr)` intertwining `d` with `grlift_phiGr`, with kernel
control and lift-back surjectivity) is not discharged by the generator
recipe: the lift-back clause asks for surjectivity onto the *whole* exterior
power `⋀^k(gr)` (all graded degrees at once), while the "define on `c •
ιMulti` generators, extend by linearity" recipe produces a map homogeneous
of a single degree — the coefficient of `gᵢ • w` must go to `[gᵢ]₁ • [w]`,
so the image of `F(t,k)` sits in a single graded piece (for `t > k`,
positive degree; the unit `1` is never hit), hence misses literal
surjectivity. (A6 info: this rules out the recipe, not every map.)

This file builds the exact minimal bridge instead: the *homogeneous*
leading-term theory, which is both true and sufficient (the single-step lift
only ever needs to lift the homogeneous component of the gr-preimage `W`,
since `d` raises gr-degree by exactly one and `LT z` is homogeneous).

* (§1) Coefficient class maps `leadCoeffMk` / `leadHomog` with additivity,
  kernel-iff (`= 0 ↔ ∈ I^(a+1)`), surjectivity onto each graded piece, and
  multiplicativity. Unconditional.
* (§2) Filtration-piece coordinate characterization: `x ∈ 𝔪^a • ⊤ ↔` all
  exterior-power basis coordinates lie in `𝔪^a`. Unconditional.
* (§3) The homogeneous leading-term map `leadTerm t k`, with zero, additivity
  on pieces, kernel control (`LT x = 0 → x ∈ F(t+1,k)`), and homogeneous
  lift-back surjectivity (onto the degree-`t-k` submodule). Unconditional.
* (§4) The contraction-value formula on decomposable wedges (generic,
  both rings at once) and the generator formula for `leadTerm`, giving
  intertwining `LT (d x) = d_gr (LT x)` on pieces. Unconditional.
* (§5) The corrected data `FiltrLeadDataHomog` (homogeneous lift-back in place
  of literal surjectivity): unconditional; plus the corrected single-step lift
  `filtr_homog_single_lift`:1693 (projecting `W` to its homogeneous part) and
  the pipeline to `GrLiftFiltrationConseq`. Conditional-exact on
  `[FiltrLeadDataHomog]` (= unconditional once §4 proves).

## References

Project (all read-only): `Regularity/Koszul/FiltrationLift.lean` (`FiltrLeadData`
:262, `filtrPiece`:112, `filtr_extend_of_iotaMulti`:232,
`filtr_single_of_lead`:287, `filtr_phi_mem`:150),
`Regularity/Koszul/AssociatedGradedRing.lean` (`grPiece_mk_surjective`:119,
`grPiece_mk_eq_zero_iff`:125, `grMul_mk_mk`:323,
`associatedGraded_of_mul_of`:558, `grRegular`:663),
`Regularity/Koszul/GradedSurjection.lean` (`genClass`:166, `degZeroHom`:104),
`Regularity/Koszul/KoszulComplex.lean` (`contractLeft_ιMulti_mem`:303,
`koszulContract_mem`:329, `koszulContract`:346),
`Regularity/Koszul/AugmentedConeStep.lean` (`contractExactAt`:61),
`Regularity/Koszul/GradedLift.lean` (`grlift_phiGr`:224, `grlift_grClass`:213).

Mathlib (`lean-toolchain` pins `v4.34.0`), all read-only:
* `LinearAlgebra/ExteriorPower/Basis.lean`: `Module.Basis.exteriorPower`,
  `exteriorPower.basis_repr_apply`, `basis_repr_self`, `ιMultiDual_apply_ιMulti`.
* `LinearAlgebra/CliffordAlgebra/Contraction.lean`: `contractLeft_ι_mul`,
  `contractLeft_ι`, `contractLeft_one`.
* `LinearAlgebra/ExteriorAlgebra/Basic.lean`: `ιMulti_succ_apply`,
  `ιMulti_zero_apply`.
* `LinearAlgebra/StdBasis.lean`: `Pi.basisFun`, `Pi.basisFun_repr`.
* `Algebra/DirectSum/Basic.lean`: `DirectSum.of`, `of_eq_same`.
* `LinearAlgebra/Matrix/Determinant/Basic.lean`: `RingHom.map_det`.

## Status

* §1 + §2 + §3: unconditional.
* §4 contraction formula + generator formula + intertwining: unconditional.
* §5 corrected data + lift + pipeline: unconditional (data) /
  conditional-exact on `[FiltrGenBound]` for the `d`-preservation input
  (same hypothesis as `filtr_d_preshift`, reused, not re-proved).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace LeadingTermMaps

open ExteriorAlgebra
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AssociatedGradedRing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.KoszulComplex
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AugmentedConeStep
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.FiltrationLift
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjection
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedLift

open scoped DirectSum

/-! ## §1. Coefficient class maps (general ring) -/

section Coeff

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- The coefficient class map: `c ↦ [c]` in degree `a`. -/
noncomputable def leadCoeffMk (a : ℕ) (c : ↥(I ^ a)) : grPiece R I a :=
  Submodule.Quotient.mk c

/-- Classes are additive. Proved. -/
theorem leadCoeffMk_add (a : ℕ) (c d : ↥(I ^ a)) :
    leadCoeffMk I a (c + d) = leadCoeffMk I a c + leadCoeffMk I a d := by
  change Submodule.Quotient.mk (c + d) =
    Submodule.Quotient.mk c + Submodule.Quotient.mk d
  exact (grPiece_mk_add R I a c d).symm

/-- The class of `0` is `0`. Proved. -/
theorem leadCoeffMk_zero (a : ℕ) : leadCoeffMk I a 0 = 0 := by
  change (Submodule.Quotient.mk (0 : ↥(I ^ a)) : grPiece R I a) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  exact Submodule.zero_mem _

/-- Kernel-iff: `[c] = 0 ↔ c ∈ I^(a+1)`. Proved. -/
theorem leadCoeffMk_eq_zero_iff (a : ℕ) (c : ↥(I ^ a)) :
    leadCoeffMk I a c = 0 ↔ (c : R) ∈ I ^ (a + 1) := by
  change (Submodule.Quotient.mk c : grPiece R I a) = 0 ↔ _
  exact grPiece_mk_eq_zero_iff R I a c

/-- Every class has a representative. Proved. -/
theorem leadCoeffMk_surjective (a : ℕ) (z : grPiece R I a) :
    ∃ c : ↥(I ^ a), leadCoeffMk I a c = z := by
  change ∃ c : ↥(I ^ a), Submodule.Quotient.mk c = z
  exact grPiece_mk_surjective R I a z

/-- The homogeneous element of `gr`: `c ↦ ofₐ [c]ₐ`. -/
noncomputable def leadHomog (a : ℕ) (c : ↥(I ^ a)) : associatedGraded R I :=
  DirectSum.of (grPiece R I) a (leadCoeffMk I a c)

/-- Homogeneous elements are additive. Proved. -/
theorem leadHomog_add (a : ℕ) (c d : ↥(I ^ a)) :
    leadHomog I a (c + d) = leadHomog I a c + leadHomog I a d := by
  change DirectSum.of (grPiece R I) a (leadCoeffMk I a (c + d)) =
    DirectSum.of (grPiece R I) a (leadCoeffMk I a c) +
      DirectSum.of (grPiece R I) a (leadCoeffMk I a d)
  rw [leadCoeffMk_add, map_add]

/-- The homogeneous element of `0` is `0`. Proved. -/
theorem leadHomog_zero (a : ℕ) : leadHomog I a 0 = 0 := by
  change DirectSum.of (grPiece R I) a (leadCoeffMk I a 0) = 0
  rw [leadCoeffMk_zero, map_zero]

/-- `DirectSum.of` is injective in each degree. Proved. -/
theorem directSum_of_injective (a : ℕ) :
    Function.Injective (DirectSum.of (grPiece R I) a) := by
  intro x y h
  have hcongr := congrArg (fun w : (⨁ n, grPiece R I n) => w a) h
  rwa [DirectSum.of_eq_same, DirectSum.of_eq_same] at hcongr

/-- Vanishing-iff for homogeneous elements. Proved. -/
theorem leadHomog_eq_zero_iff (a : ℕ) (c : ↥(I ^ a)) :
    leadHomog I a c = 0 ↔ (c : R) ∈ I ^ (a + 1) := by
  constructor
  · intro h
    have h' : DirectSum.of (grPiece R I) a (leadCoeffMk I a c) =
        DirectSum.of (grPiece R I) a 0 := by
      rw [map_zero]
      exact h
    have h2 : leadCoeffMk I a c = 0 := directSum_of_injective I a h'
    exact (leadCoeffMk_eq_zero_iff I a c).mp h2
  · intro h
    have h2 : leadCoeffMk I a c = 0 :=
      (leadCoeffMk_eq_zero_iff I a c).mpr h
    change DirectSum.of (grPiece R I) a (leadCoeffMk I a c) = 0
    rw [h2, map_zero]

/-- Multiplicativity: `[c • x]ₐ₊b = [c]ₐ • [x]_b`. Proved. This is the
computation behind intertwining (`[gᵢ • w] = [gᵢ]₁ • [w]`). -/
theorem leadHomog_mul (a b : ℕ) (c : ↥(I ^ a)) (x : ↥(I ^ b)) :
    leadHomog I (a + b) ⟨(c : R) * (x : R), by
        rw [pow_add]
        exact Ideal.mul_mem_mul c.2 x.2⟩ =
      leadHomog I a c * leadHomog I b x := by
  change DirectSum.of (grPiece R I) (a + b) _ =
    DirectSum.of (grPiece R I) a _ * DirectSum.of (grPiece R I) b _
  rw [associatedGraded_of_mul_of]
  congr 1

end Coeff

/-! ## §2. Filtration pieces via exterior-power coordinates -/

section Coords

variable {R : Type*} [CommRing R] (d : ℕ)

/-- The exterior-power basis from the standard basis of `Fin d → R`. -/
noncomputable def extBasis (k : ℕ) :
    Module.Basis (Set.powersetCard (Fin d) k) R ↥(⋀[R]^k (Fin d → R)) :=
  Module.Basis.exteriorPower k (Pi.basisFun R (Fin d))

/-- Membership in `J • ⊤` is coordinate-wise membership in `J`. Proved. -/
theorem mem_smul_top_iff_coords (J : Ideal R) (k : ℕ)
    (x : ↥(⋀[R]^k (Fin d → R))) :
    x ∈ J • (⊤ : Submodule R ↥(⋀[R]^k (Fin d → R))) ↔
      ∀ s, (extBasis d k).repr x s ∈ J := by
  constructor
  · intro hx s
    let S : Submodule R ↥(⋀[R]^k (Fin d → R)) :=
      { carrier := {y | ∀ s, (extBasis d k).repr y s ∈ J}
        zero_mem' := by simp
        add_mem' := by
          intro a b ha hb t
          rw [map_add, Finsupp.add_apply]
          exact add_mem (ha t) (hb t)
        smul_mem' := by
          intro c a ha t
          rw [map_smul, Finsupp.smul_apply]
          exact Submodule.smul_mem _ _ (ha t) }
    have hle : J • (⊤ : Submodule R ↥(⋀[R]^k (Fin d → R))) ≤ S := by
      rw [Submodule.smul_le]
      intro c hc y _ t
      change (extBasis d k).repr (c • y) t ∈ J
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm, ← smul_eq_mul]
      exact Submodule.smul_mem _ _ hc
    exact hle hx s
  · intro h
    rw [← (extBasis d k).sum_repr x]
    exact Submodule.sum_mem _ fun s _ =>
      Submodule.smul_mem_smul (h s) Submodule.mem_top

end Coords

section FiltrCoords

variable {K : Type*} [Field K] {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K))
  [P.IsPrime] (d : ℕ)

/-- Membership in `filtrPiece` is coordinate-wise membership in `𝔪^(t-k)`.
proved. -/
theorem mem_filtrPiece_iff_coords (t k : ℕ)
    (x : ↥(⋀[FRL P]^k (Fin d → FRL P))) :
    x ∈ filtrPiece P d t k ↔
      ∀ s, (extBasis d k).repr x s ∈
        IsLocalRing.maximalIdeal (FRL P) ^ (t - k) := by
  rw [filtrPiece_def]
  exact mem_smul_top_iff_coords d _ _ _

end FiltrCoords

/-! ## §3. The homogeneous leading-term map -/

section LeadTerm

variable {K : Type*} [Field K] {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K))
  [P.IsPrime] (d : ℕ)

open Classical in
/-- The gr-side exterior-power basis. -/
noncomputable def extBasisGr (k : ℕ) : Module.Basis (Set.powersetCard (Fin d) k)
    (grRegular P) ↥(⋀[grRegular P]^k (Fin d → grRegular P)) :=
  extBasis d k

/-- The homogeneous element of `grRegular`: `c ↦ ofₐ [c]ₐ`. -/
noncomputable def leadGr (a : ℕ)
    (c : ↥((IsLocalRing.maximalIdeal (FRL P)) ^ a)) : grRegular P :=
  leadHomog _ a c

/-- `leadGr` is additive. Proved. -/
theorem leadGr_add (a : ℕ)
    (c e : ↥((IsLocalRing.maximalIdeal (FRL P)) ^ a)) :
    leadGr P a (c + e) = leadGr P a c + leadGr P a e :=
  leadHomog_add _ a c e

/-- `leadGr` of `0` is `0`. Proved. -/
theorem leadGr_zero (a : ℕ) : leadGr P a 0 = 0 :=
  leadHomog_zero _ a

/-- Vanishing-iff for `leadGr`. Proved. -/
theorem leadGr_eq_zero_iff (a : ℕ)
    (c : ↥((IsLocalRing.maximalIdeal (FRL P)) ^ a)) :
    leadGr P a c = 0 ↔
      (c : FRL P) ∈ IsLocalRing.maximalIdeal (FRL P) ^ (a + 1) :=
  leadHomog_eq_zero_iff _ a c

/-- `leadGr` vanishes on representatives of `0`. Proved. -/
theorem leadGr_eq_zero_of_coe (a : ℕ)
    (c : ↥((IsLocalRing.maximalIdeal (FRL P)) ^ a))
    (hc : (c : FRL P) = 0) : leadGr P a c = 0 := by
  have hsub : c = 0 := Subtype.ext hc
  rw [hsub]
  exact leadGr_zero P a

/-- Homogeneous inclusion into `grRegular`: `z ↦ ofₐ z`. -/
noncomputable def leadOf (a : ℕ)
    (z : grPiece (FRL P) (IsLocalRing.maximalIdeal (FRL P)) a) : grRegular P :=
  DirectSum.of _ a z

/-- Dual computation: coordinates of a basis expansion. Proved (generic, both
rings at once). -/
theorem basis_repr_sum_smul {S : Type*} [CommRing S] (k : ℕ)
    (c : Set.powersetCard (Fin d) k → S)
    (s : Set.powersetCard (Fin d) k) :
    (extBasis (R := S) d k).repr (∑ s', c s' • (extBasis (R := S) d k) s') s =
      c s := by
  rw [map_sum]
  simp only [Finsupp.finsetSum_apply, map_smul, Finsupp.smul_apply,
    Module.Basis.repr_self]
  rw [Finset.sum_eq_single s]
  · rw [Finsupp.single_eq_same, smul_eq_mul, mul_one]
  · intro s' _ hs'
    rw [Finsupp.single_eq_of_ne hs'.symm, smul_zero]
  · intro hs
    exact absurd (Finset.mem_univ s) hs

open Classical in
/-- The homogeneous leading-term map: coordinates go to their classes.
Off-piece values are junk (`0`); every lemma carries the membership
hypothesis. -/
noncomputable def leadTerm (t k : ℕ)
    (x : ↥(⋀[FRL P]^k (Fin d → FRL P))) :
    ↥(⋀[grRegular P]^k (Fin d → grRegular P)) :=
  if hx : x ∈ filtrPiece P d t k then
    ∑ s, leadGr P (t - k)
      ⟨(extBasis d k).repr x s,
        (mem_filtrPiece_iff_coords P d t k x).mp hx s⟩ •
      (extBasisGr P d k) s
  else 0

/-- `LT 0 = 0`. Proved. -/
theorem leadTerm_zero (t k : ℕ) : leadTerm P d t k 0 = 0 := by
  have h0 : ∀ s : Set.powersetCard (Fin d) k,
      (extBasis d k).repr (0 : ↥(⋀[FRL P]^k (Fin d → FRL P))) s = 0 := by
    intro s
    simp
  unfold leadTerm
  rw [dite_eq_left (Submodule.zero_mem _), Finset.sum_eq_zero]
  intro s _
  rw [leadGr_eq_zero_of_coe P (t - k) _ (h0 s), zero_smul]

/-- `LT` is additive on pieces. Proved. -/
theorem leadTerm_add (t k : ℕ)
    (x y : ↥(⋀[FRL P]^k (Fin d → FRL P)))
    (hx : x ∈ filtrPiece P d t k) (hy : y ∈ filtrPiece P d t k) :
    leadTerm P d t k (x + y) =
      leadTerm P d t k x + leadTerm P d t k y := by
  have hre : ∀ s : Set.powersetCard (Fin d) k,
      (extBasis d k).repr (x + y) s =
        (extBasis d k).repr x s + (extBasis d k).repr y s := by
    intro s
    rw [map_add, Finsupp.add_apply]
  unfold leadTerm
  rw [dite_eq_left (Submodule.add_mem _ hx hy), dite_eq_left hx, dite_eq_left hy,
    ← Finset.sum_add_distrib]
  have hlead : ∀ (u v w : ↥((IsLocalRing.maximalIdeal (FRL P)) ^ (t - k))),
      (u : FRL P) = (v : FRL P) + (w : FRL P) →
        leadGr P (t - k) u = leadGr P (t - k) v + leadGr P (t - k) w := by
    intro u v w huv
    have hsub : u = v + w := Subtype.ext huv
    rw [hsub, leadGr_add]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← add_smul]
  congr 1
  exact hlead _ _ _ (hre s)

/-- Kernel control: `LT x = 0` pushes one step deeper. Proved. -/
theorem leadTerm_kernel (t k : ℕ)
    (x : ↥(⋀[FRL P]^k (Fin d → FRL P)))
    (hx : x ∈ filtrPiece P d t k) (h0 : leadTerm P d t k x = 0) :
    x ∈ filtrPiece P d (t + 1) k := by
  unfold leadTerm at h0
  rw [dite_eq_left hx] at h0
  rw [mem_filtrPiece_iff_coords]
  intro s
  have hsum := basis_repr_sum_smul (S := grRegular P) (d := d) k
    (fun s' => leadGr P (t - k)
      ⟨(extBasis d k).repr x s',
        (mem_filtrPiece_iff_coords P d t k x).mp hx s'⟩) s
  have h2 := congrArg (fun w => (extBasisGr P d k).repr w s) h0
  have hrepr0 : (extBasisGr P d k).repr
      (0 : ↥(⋀[grRegular P]^k (Fin d → grRegular P))) s = 0 := by simp
  rw [hrepr0] at h2
  have hcs : leadGr P (t - k)
      ⟨(extBasis d k).repr x s,
        (mem_filtrPiece_iff_coords P d t k x).mp hx s⟩ = 0 :=
    hsum.symm.trans h2
  have hmem := (leadGr_eq_zero_iff P (t - k) _).mp hcs
  have hle : t + 1 - k ≤ (t - k) + 1 := by omega
  exact Ideal.pow_le_pow_right hle hmem

/-- Homogeneous lift-back: every degree-`t-k` combination is hit. Proved. -/
theorem leadTerm_homog_surjective (t k : ℕ)
    (w : Set.powersetCard (Fin d) k →
      grPiece (FRL P) (IsLocalRing.maximalIdeal (FRL P)) (t - k)) :
    ∃ x : ↥(⋀[FRL P]^k (Fin d → FRL P)),
      x ∈ filtrPiece P d t k ∧
        leadTerm P d t k x =
          ∑ s, leadOf P (t - k) (w s) • (extBasisGr P d k) s := by
  choose c hc using fun s => leadCoeffMk_surjective _ (t - k) (w s)
  refine ⟨∑ s', (c s' : FRL P) • (extBasis d k) s', ?_, ?_⟩
  · rw [filtrPiece_def]
    exact Submodule.sum_mem _ fun s _ =>
      Submodule.smul_mem_smul (c s).2 Submodule.mem_top
  · have hx : (∑ s', (c s' : FRL P) • (extBasis d k) s') ∈
        filtrPiece P d t k := by
      rw [filtrPiece_def]
      exact Submodule.sum_mem _ fun s _ =>
        Submodule.smul_mem_smul (c s).2 Submodule.mem_top
    unfold leadTerm
    rw [dite_eq_left hx]
    refine Finset.sum_congr rfl fun s _ => ?_
    have hrepr : (extBasis d k).repr
        (∑ s', (c s' : FRL P) • (extBasis d k) s') s = (c s : FRL P) :=
      basis_repr_sum_smul (d := d) k (fun s' => (c s' : FRL P)) s
    have hlead2 : ∀ (u : ↥((IsLocalRing.maximalIdeal (FRL P)) ^ (t - k))),
        (u : FRL P) = (c s : FRL P) →
          leadGr P (t - k) u = leadGr P (t - k) (c s) := by
      intro u huv
      have hsub : u = c s := Subtype.ext huv
      rw [hsub]
    rw [hlead2 _ hrepr]
    change leadGr P (t - k) (c s) • _ = _
    have hcw : leadGr P (t - k) (c s) = leadOf P (t - k) (w s) := by
      change leadHomog _ (t - k) (c s) = _
      change DirectSum.of _ (t - k) (leadCoeffMk _ (t - k) (c s)) = _
      exact congrArg _ (hc s)
    rw [hcw]

end LeadTerm

/-! ## §4. Intertwining: the contraction formula and the generator formula -/

section ContractFormula

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- The contraction-value formula on decomposable wedges: `d` of an
`ιMulti` wedge is the alternating sum of single contractions. Proved by
induction via `contractLeft_ι_mul`. Generic: instantiated on both rings at
once (signs match automatically). -/
theorem contract_ιMulti_eq (φ : M →ₗ[R] R) (n : ℕ) (v : Fin (n.succ) → M) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) φ
        (ExteriorAlgebra.ιMulti R (n.succ) v) =
      ∑ j : Fin (n.succ), ((-1 : R) ^ (j : ℕ)) • (φ (v j)) •
        ExteriorAlgebra.ιMulti R n (v ∘ Fin.succAbove j) := by
  induction n with
  | zero =>
    have hsplit := ExteriorAlgebra.ιMulti_succ_apply (R := R) v
    rw [hsplit, CliffordAlgebra.contractLeft_ι_mul,
      ExteriorAlgebra.ιMulti_zero_apply, CliffordAlgebra.contractLeft_one,
      mul_zero, sub_zero]
    have h1 : ∀ (f : Fin (Nat.succ 0) → ExteriorAlgebra R M),
        ∑ j, f j = f 0 := fun f => Fin.sum_univ_one f
    rw [h1, ExteriorAlgebra.ιMulti_zero_apply]
    have hval : ((0 : Fin (Nat.succ 0)) : ℕ) = 0 := Fin.val_zero _
    rw [hval, pow_zero, one_smul]
  | succ n ih =>
    have hsplit := ExteriorAlgebra.ιMulti_succ_apply (R := R) v
    rw [hsplit, CliffordAlgebra.contractLeft_ι_mul, ih (Matrix.vecTail v)]
    have hssum : ∀ (f : Fin (n.succ.succ) → ExteriorAlgebra R M),
        ∑ j, f j = f 0 + ∑ i : Fin (n.succ), f i.succ :=
      fun f => Fin.sum_univ_succ f
    rw [hssum]
    have htail : Matrix.vecTail v = v ∘ Fin.succAbove 0 := by
      funext i
      change (Matrix.vecTail v) i = v (Fin.succAbove (0 : Fin (n.succ.succ)) i)
      rw [Fin.succAbove_of_le_castSucc _ _ (Fin.zero_le _)]
      rfl
    have hcons : ∀ j : Fin (n.succ),
        Fin.cons (v 0) (Matrix.vecTail v ∘ Fin.succAbove j) =
          v ∘ Fin.succAbove j.succ := by
      intro j
      funext k
      obtain (rfl | ⟨i, rfl⟩) := Fin.eq_zero_or_eq_succ k
      · rw [Fin.cons_zero]
        change v 0 = v (Fin.succAbove j.succ 0)
        rw [Fin.succAbove_succ_of_le j 0 (Fin.zero_le _), Fin.castSucc_zero]
      · rw [Fin.cons_succ]
        change (Matrix.vecTail v) (Fin.succAbove j i) =
          v (Fin.succAbove j.succ i.succ)
        by_cases h : i.succ ≤ j
        · rw [Fin.succAbove_succ_of_le j i.succ h]
          have h2 : Fin.castSucc i < j := Fin.castSucc_lt_iff_succ_le.mpr h
          rw [Fin.succAbove_of_castSucc_lt j i h2]
          have harg : (Fin.castSucc i).succ = (i.succ).castSucc := by
            apply Fin.ext
            simp
          have hvt : (Matrix.vecTail v) (Fin.castSucc i) =
              v ((Fin.castSucc i).succ) := rfl
          rw [hvt, harg]
        · push Not at h
          rw [Fin.succAbove_succ_of_lt j i.succ h]
          have h2 : j ≤ Fin.castSucc i := Fin.le_castSucc_iff.mpr h
          rw [Fin.succAbove_of_le_castSucc j i h2]
          rfl
    have hcons_mul : ∀ (w : Fin n → M),
        ExteriorAlgebra.ι R (v 0) * ExteriorAlgebra.ιMulti R n w =
          ExteriorAlgebra.ιMulti R (n.succ) (Fin.cons (v 0) w) := by
      intro w
      have h := ExteriorAlgebra.ιMulti_succ_apply (R := R) (Fin.cons (v 0) w)
      have hvt0 : ∀ (u : Fin (n.succ) → M),
          Matrix.vecTail u = Fin.tail u := fun u => funext fun i => rfl
      rw [hvt0, Fin.tail_cons, Fin.cons_zero] at h
      exact h.symm
    have hterm : ∀ j : Fin (n.succ),
        ExteriorAlgebra.ι R (v 0) *
            (((-1 : R) ^ (j : ℕ)) • (φ ((Matrix.vecTail v) j)) •
              ExteriorAlgebra.ιMulti R n
                ((Matrix.vecTail v) ∘ Fin.succAbove j)) =
          -(((-1 : R) ^ ((j.succ : Fin (n.succ.succ)) : ℕ)) • (φ (v j.succ)) •
            ExteriorAlgebra.ιMulti R (n.succ)
              (v ∘ Fin.succAbove j.succ)) := by
      intro j
      rw [mul_smul_comm, mul_smul_comm, hcons_mul, hcons j]
      change ((-1 : R) ^ (j : ℕ)) • (φ (v j.succ)) • _ = _
      rw [Fin.val_succ, pow_succ, mul_smul, neg_smul, one_smul, smul_neg,
        neg_neg]
    have hF0 : ((-1 : R) ^ ((0 : Fin (n.succ.succ)) : ℕ)) • (φ (v 0)) •
          ExteriorAlgebra.ιMulti R (n.succ) (v ∘ Fin.succAbove 0) =
        φ (v 0) • ExteriorAlgebra.ιMulti R (n.succ) (Matrix.vecTail v) := by
      rw [htail]
      have hval : ((0 : Fin (n.succ.succ)) : ℕ) = 0 := Fin.val_zero _
      rw [hval, pow_zero, one_smul]
    rw [Finset.mul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib, hF0,
      add_left_cancel_iff]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hterm j, neg_neg]

end ContractFormula

/-! ## §4b. The generator formula -/

section GenFormula

variable {K : Type*} [Field K] {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K))
  [P.IsPrime] (d : ℕ)

/-- The degree-0 map into `grRegular`. -/
noncomputable def degZeroGrHom : FRL P →+* grRegular P := degZeroHom _ _

/-- Degree-0 reduction of a vector. -/
noncomputable def degZeroVec (v : Fin d → FRL P) : Fin d → grRegular P :=
  fun i => degZeroGrHom P (v i)

/-- Coefficients factor: `[c • r]ₐ = [c]ₐ • [r]₀`. Proved. -/
theorem leadGr_mul_coeff (a : ℕ) (c : ↥((IsLocalRing.maximalIdeal (FRL P)) ^ a))
    (r : FRL P) (h : (c : FRL P) * r ∈ (IsLocalRing.maximalIdeal (FRL P)) ^ a) :
    leadGr P a ⟨(c : FRL P) * r, h⟩ = leadGr P a c * degZeroGrHom P r := by
  have hmul := leadHomog_mul (IsLocalRing.maximalIdeal (FRL P)) a 0 c
    ⟨r, by rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top⟩
  exact hmul

/-- Coordinates of a decomposable wedge are determinants. Proved (generic,
both rings at once). -/
theorem extBasis_repr_ιMulti_gen {S : Type*} [CommRing S] (k : ℕ)
    (v : Fin k → (Fin d → S)) (s : Set.powersetCard (Fin d) k) :
    (extBasis (R := S) d k).repr (exteriorPower.ιMulti S k v) s =
      (Matrix.of fun i j =>
        (v i) ((Set.powersetCard.ofFinEmbEquiv.symm s) j)).det := by
  unfold extBasis
  rw [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
  congr 1

/-- Determinants commute with the degree-0 map. Proved. -/
theorem det_degZeroGrHom (k : ℕ) (e : Fin k → Fin k → FRL P) :
    (Matrix.of fun i j => degZeroGrHom P (e i j)).det =
      degZeroGrHom P (Matrix.of fun i j => e i j).det := by
  have hmap : (Matrix.of fun i j => degZeroGrHom P (e i j)) =
      (degZeroGrHom P).mapMatrix (Matrix.of fun i j => e i j) := by
    ext i j
    rfl
  rw [hmap, ← RingHom.map_det]

/-- The generator formula: `LT` on `c • ιMulti v`. Proved. -/
theorem leadTerm_gen (t k : ℕ)
    (c : ↥((IsLocalRing.maximalIdeal (FRL P)) ^ (t - k)))
    (v : Fin k → (Fin d → FRL P)) :
    leadTerm P d t k ((c : FRL P) • exteriorPower.ιMulti (FRL P) k v) =
      leadGr P (t - k) c • exteriorPower.ιMulti (grRegular P) k
        (fun j => degZeroVec P d (v j)) := by
  have hx : (c : FRL P) • exteriorPower.ιMulti (FRL P) k v ∈
      filtrPiece P d t k := by
    rw [filtrPiece_def]
    exact Submodule.smul_mem_smul c.2 Submodule.mem_top
  unfold leadTerm
  rw [dite_eq_left hx]
  have hrepr : ∀ s : Set.powersetCard (Fin d) k,
      (extBasis d k).repr
          ((c : FRL P) • exteriorPower.ιMulti (FRL P) k v) s =
        (c : FRL P) *
          (extBasis d k).repr (exteriorPower.ιMulti (FRL P) k v) s := by
    intro s
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
  have hexpand : exteriorPower.ιMulti (grRegular P) k
      (fun j => degZeroVec P d (v j)) =
      ∑ s, ((extBasisGr P d k).repr (exteriorPower.ιMulti (grRegular P) k
        (fun j => degZeroVec P d (v j)))) s • (extBasisGr P d k) s :=
    ((extBasisGr P d k).sum_repr (exteriorPower.ιMulti (grRegular P) k
      (fun j => degZeroVec P d (v j)))).symm
  rw [hexpand, Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hmem : (c : FRL P) *
      (extBasis d k).repr (exteriorPower.ιMulti (FRL P) k v) s ∈
      (IsLocalRing.maximalIdeal (FRL P)) ^ (t - k) := by
    simpa [smul_eq_mul, mul_comm] using Submodule.smul_mem
      ((IsLocalRing.maximalIdeal (FRL P)) ^ (t - k))
      ((extBasis d k).repr (exteriorPower.ιMulti (FRL P) k v) s) c.2
  have hleadc : ∀ (u : ↥((IsLocalRing.maximalIdeal (FRL P)) ^ (t - k))),
      (u : FRL P) = (c : FRL P) *
          (extBasis d k).repr (exteriorPower.ιMulti (FRL P) k v) s →
        leadGr P (t - k) u = leadGr P (t - k) c *
          degZeroGrHom P
            ((extBasis d k).repr (exteriorPower.ιMulti (FRL P) k v) s) := by
    intro u huv
    have hsub : u = ⟨(c : FRL P) *
      (extBasis d k).repr (exteriorPower.ιMulti (FRL P) k v) s, hmem⟩ :=
      Subtype.ext huv
    rw [hsub]
    exact leadGr_mul_coeff P (t - k) c _ hmem
  rw [hleadc _ (hrepr s)]
  have hdet : (extBasisGr P d k).repr (exteriorPower.ιMulti (grRegular P) k
      (fun j => degZeroVec P d (v j))) s =
      degZeroGrHom P
        ((extBasis d k).repr (exteriorPower.ιMulti (FRL P) k v) s) := by
    change (extBasis (R := grRegular P) d k).repr _ s = _
    rw [extBasis_repr_ιMulti_gen, extBasis_repr_ιMulti_gen]
    exact det_degZeroGrHom P k
      (fun i j => (v i) ((Set.powersetCard.ofFinEmbEquiv.symm s) j))
  rw [hdet, ← mul_smul]

end GenFormula

/-! ## §4c. Intertwining ingredients -/

section ContractApply

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- The contraction formula at exterior-power level. Proved (subtype form of
`contract_ιMulti_eq`). -/
theorem koszulContract_ιMulti (φ : M →ₗ[R] R) (n : ℕ) (v : Fin (n.succ) → M) :
    koszulContract φ n
        ⟨ExteriorAlgebra.ιMulti R (n.succ) v,
          mem_ιMulti_piece (n.succ) v⟩ =
      ∑ j : Fin (n.succ), ((-1 : R) ^ (j : ℕ)) • (φ (v j)) •
        (⟨ExteriorAlgebra.ιMulti R n (v ∘ Fin.succAbove j),
          mem_ιMulti_piece n (v ∘ Fin.succAbove j)⟩ : ↥(⋀[R]^n M)) := by
  apply Subtype.ext
  simp only [koszulContract_apply]
  change CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) φ
      (ExteriorAlgebra.ιMulti R (n.succ) v) = _
  rw [contract_ιMulti_eq]
  simp

/-- `exteriorPower.ιMulti` is the subtype form. Proved. -/
theorem extPow_ιMulti_eq (n : ℕ) (v : Fin n → M) :
    exteriorPower.ιMulti R n v =
      (⟨ExteriorAlgebra.ιMulti R n v, mem_ιMulti_piece n v⟩ :
        ↥(⋀[R]^n M)) := by
  apply Subtype.ext
  exact exteriorPower.ιMulti_apply_coe R n v

/-- The contraction formula in `k+1` form. Proved (defeq variant). -/
theorem koszulContract_ιMulti_succ (φ : M →ₗ[R] R) (k : ℕ)
    (v : Fin (k + 1) → M) :
    koszulContract φ k
        ⟨ExteriorAlgebra.ιMulti R (k + 1) v, mem_ιMulti_piece (k + 1) v⟩ =
      ∑ j : Fin (k + 1), ((-1 : R) ^ (j : ℕ)) • (φ (v j)) •
        (⟨ExteriorAlgebra.ιMulti R k (v ∘ Fin.succAbove j),
          mem_ιMulti_piece k (v ∘ Fin.succAbove j)⟩ : ↥(⋀[R]^k M)) :=
  koszulContract_ιMulti φ k v

/-- The sequence functional evaluates by coordinates. Proved. -/
theorem contractOfSequence_apply {S : Type*} [CommRing S] (d : ℕ)
    (g v : Fin d → S) :
    koszulContractOfSequence g v = ∑ i, (v i) • (g i) := by
  unfold koszulContractOfSequence
  conv_lhs => rw [← (Pi.basisFun S (Fin d)).sum_repr v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Module.Basis.constr_basis, Pi.basisFun_repr]

end ContractApply

section Intertwine

variable {K : Type*} [Field K] {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K))
  [P.IsPrime] (d : ℕ) (g : Fin d → FRL P)

/-- Multiplicativity into `grRegular`. Proved. -/
theorem leadGr_mul (a b : ℕ) (c : ↥((IsLocalRing.maximalIdeal (FRL P)) ^ a))
    (x : ↥((IsLocalRing.maximalIdeal (FRL P)) ^ b)) :
    leadGr P (a + b) ⟨(c : FRL P) * (x : FRL P), by
        rw [pow_add]
        exact Ideal.mul_mem_mul c.2 x.2⟩ =
      leadGr P a c * leadGr P b x :=
  leadHomog_mul _ a b c x

/-- The Koszul functional lies in `𝔪^1`. Proved. -/
theorem phi_mem_pow_one
    (hgen : Ideal.span (Set.range g) = IsLocalRing.maximalIdeal (FRL P))
    (v : Fin d → FRL P) :
    koszulContractOfSequence g v ∈ (IsLocalRing.maximalIdeal (FRL P)) ^ 1 := by
  rw [pow_one]
  exact filtr_phi_mem P d g hgen v

/-- `leadOf` of a sum is the sum. Proved. -/
theorem leadOf_sum (a : ℕ) {ι : Type*} (s : Finset ι)
    (f : ι → ↥((IsLocalRing.maximalIdeal (FRL P)) ^ a)) :
    ∑ i ∈ s, leadOf P a (leadCoeffMk _ a (f i)) =
      leadOf P a (leadCoeffMk _ a (∑ i ∈ s, f i)) := by
  change ∑ i ∈ s, DirectSum.of
      (grPiece (FRL P) (IsLocalRing.maximalIdeal (FRL P))) a
      (Submodule.Quotient.mk (f i)) = _
  rw [← map_sum]
  congr 1
  change ∑ i ∈ s, Submodule.Quotient.mk (f i) =
    Submodule.Quotient.mk (∑ i ∈ s, f i)
  simp only [← grPiece_mkQ_eq_mk]
  rw [← map_sum]

/-- The gr-functional on degree-0 vectors is the class of the functional.
proved. -/
theorem phiGr_degZeroVec
    (hgen : Ideal.span (Set.range g) = IsLocalRing.maximalIdeal (FRL P))
    (v : Fin d → FRL P) :
    grlift_phiGr P d g hgen (degZeroVec P d v) =
      leadOf P 1 (leadCoeffMk _ 1 ⟨koszulContractOfSequence g v,
        phi_mem_pow_one P d g hgen v⟩) := by
  have hgr := contractOfSequence_apply (S := grRegular P) d
    (fun i => grlift_grClass P d g hgen i) (degZeroVec P d v)
  have hR := contractOfSequence_apply (S := FRL P) d g v
  have hg1 : ∀ i : Fin d,
      g i ∈ (IsLocalRing.maximalIdeal (FRL P)) ^ 1 := by
    intro i
    rw [pow_one]
    have h : g i ∈ Ideal.span (Set.range g) :=
      Submodule.subset_span (Set.mem_range_self i)
    rwa [hgen] at h
  have hmul : ∀ i : Fin d,
      leadHomog (IsLocalRing.maximalIdeal (FRL P)) (0 + 1)
        ⟨(v i) * (g i), by
          rw [pow_add]
          exact Ideal.mul_mem_mul
            (by rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top)
            (hg1 i)⟩ =
        leadHomog _ 0 ⟨(v i), by
            rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top⟩ *
        leadHomog _ 1 ⟨(g i), hg1 i⟩ :=
    fun i => leadHomog_mul (IsLocalRing.maximalIdeal (FRL P)) 0 1
      ⟨(v i), by
        rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top⟩
      ⟨(g i), hg1 i⟩
  set f : Fin d → ↥((IsLocalRing.maximalIdeal (FRL P)) ^ 1) :=
    fun i => ⟨(v i) * (g i), by
      have hsm := Submodule.smul_mem
        ((IsLocalRing.maximalIdeal (FRL P)) ^ 1) (v i) (hg1 i)
      rwa [smul_eq_mul] at hsm⟩ with hf
  have hper : ∀ i : Fin d, ((degZeroVec P d v) i) •
      (grlift_grClass P d g hgen i) =
      leadOf P 1 (leadCoeffMk _ 1 (f i)) := fun i => (hmul i).symm
  have hsum := leadOf_sum P 1 Finset.univ f
  have hsum_coe : ∀ (s : Finset (Fin d)),
      ((∑ i ∈ s, f i : ↥((IsLocalRing.maximalIdeal (FRL P)) ^ 1)) : FRL P) =
        ∑ i ∈ s, ((f i : ↥((IsLocalRing.maximalIdeal (FRL P)) ^ 1)) :
          FRL P) := by
    intro s
    induction s using Finset.induction with
    | empty => rw [Finset.sum_empty, Finset.sum_empty]; rfl
    | insert a s' has ih =>
      rw [Finset.sum_insert has, Finset.sum_insert has, Submodule.coe_add, ih]
  have hval : ((∑ i ∈ Finset.univ, f i :
      ↥((IsLocalRing.maximalIdeal (FRL P)) ^ 1)) : FRL P) =
      koszulContractOfSequence g v := by
    rw [hsum_coe]
    change ∑ i ∈ Finset.univ, (v i) * (g i) = _
    rw [hR]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (smul_eq_mul _ _).symm
  change koszulContractOfSequence (fun i => grlift_grClass P d g hgen i)
    (degZeroVec P d v) = _
  rw [hgr]
  simp only [hper]
  rw [hsum]
  have hsub : (∑ i ∈ Finset.univ, f i) =
      ⟨koszulContractOfSequence g v, phi_mem_pow_one P d g hgen v⟩ :=
    Subtype.ext hval
  rw [hsub]

/-- Generator preservation: `d` of a `c • ιMulti` generator stays in the
piece. Proved (formula + `φ ∈ 𝔪`); needs no `t` restriction. -/
theorem leadGen_preservation
    (hgen : Ideal.span (Set.range g) = IsLocalRing.maximalIdeal (FRL P))
    (t k : ℕ)
    (c : ↥((IsLocalRing.maximalIdeal (FRL P)) ^ (t - (k + 1))))
    (v : Fin (k + 1) → (Fin d → FRL P)) :
    koszulContract (koszulContractOfSequence g) k
        ((c : FRL P) • exteriorPower.ιMulti (FRL P) (k + 1) v) ∈
      filtrPiece P d t k := by
  have hdx : koszulContract (koszulContractOfSequence g) k
        ((c : FRL P) • exteriorPower.ιMulti (FRL P) (k + 1) v) =
      ∑ j : Fin (k + 1), ((-1 : FRL P) ^ (j : ℕ)) •
        (((c : FRL P) * koszulContractOfSequence g (v j)) •
          (⟨ExteriorAlgebra.ιMulti (FRL P) k (v ∘ Fin.succAbove j),
            mem_ιMulti_piece k (v ∘ Fin.succAbove j)⟩ :
            ↥(⋀[FRL P]^k (Fin d → FRL P)))) := by
    rw [map_smul]
    conv_lhs => rw [extPow_ιMulti_eq]
    rw [koszulContract_ιMulti_succ, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_comm _ _, ← mul_smul (c : FRL P) _ _]
  rw [hdx]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [filtrPiece_def]
  refine Submodule.smul_mem _ _ (Submodule.smul_mem_smul ?_ Submodule.mem_top)
  have h1 : (c : FRL P) ∈ (IsLocalRing.maximalIdeal (FRL P)) ^ (t - (k + 1)) :=
    c.2
  have h2 : koszulContractOfSequence g (v j) ∈
      (IsLocalRing.maximalIdeal (FRL P)) ^ 1 :=
    phi_mem_pow_one P d g hgen (v j)
  have hcmem : (c : FRL P) * koszulContractOfSequence g (v j) ∈
      (IsLocalRing.maximalIdeal (FRL P)) ^ (t - (k + 1) + 1) := by
    rw [pow_add]
    exact Ideal.mul_mem_mul h1 h2
  have hle : t - k ≤ t - (k + 1) + 1 := by omega
  exact Ideal.pow_le_pow_right hle hcmem

/-- `LT` of a sum on pieces. Proved. -/
theorem leadTerm_sum (t k : ℕ) {ι : Type*} (s : Finset ι)
    (f : ι → ↥(⋀[FRL P]^k (Fin d → FRL P)))
    (h : ∀ i ∈ s, f i ∈ filtrPiece P d t k) :
    leadTerm P d t k (∑ i ∈ s, f i) = ∑ i ∈ s, leadTerm P d t k (f i) := by classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, leadTerm_zero]
  | insert a s' has ih =>
    rw [Finset.sum_insert has, Finset.sum_insert has,
      leadTerm_add P d t k _ _ (h a (Finset.mem_insert_self a s'))
        (Submodule.sum_mem _ fun i hi => h i (Finset.mem_insert_of_mem hi)),
      ih (fun i hi => h i (Finset.mem_insert_of_mem hi))]

/-- Generator intertwining (the bridge): `LT (d x) = d_gr (LT x)` for
`x = c • ιMulti v`, restricted to `t ≥ k+1` (unrestricted intertwining is
false for homogeneous maps: `d` raises degree by one while `LT` has fixed
degree). Proved via the contraction formula on both sides. -/
theorem leadTerm_intertwine_gen
    (hgen : Ideal.span (Set.range g) = IsLocalRing.maximalIdeal (FRL P))
    (t k : ℕ) (htk : k + 1 ≤ t)
    (c : ↥((IsLocalRing.maximalIdeal (FRL P)) ^ (t - (k + 1))))
    (v : Fin (k + 1) → (Fin d → FRL P)) :
    leadTerm P d t k (koszulContract (koszulContractOfSequence g) k
        ((c : FRL P) • exteriorPower.ιMulti (FRL P) (k + 1) v)) =
      koszulContract (grlift_phiGr P d g hgen) k (leadTerm P d t (k + 1)
        ((c : FRL P) • exteriorPower.ιMulti (FRL P) (k + 1) v)) := by
  have ha : t - (k + 1) + 1 = t - k := by omega
  have hmem : ∀ j : Fin (k + 1), ((-1 : FRL P) ^ ((j : ℕ))) *
        ((c : FRL P) * koszulContractOfSequence g (v j)) ∈
        (IsLocalRing.maximalIdeal (FRL P)) ^ (t - k) := by
    intro j
    have h1 : (c : FRL P) ∈
        (IsLocalRing.maximalIdeal (FRL P)) ^ (t - (k + 1)) := c.2
    have h2 : koszulContractOfSequence g (v j) ∈
        (IsLocalRing.maximalIdeal (FRL P)) ^ 1 :=
      phi_mem_pow_one P d g hgen (v j)
    have hcmem : (c : FRL P) * koszulContractOfSequence g (v j) ∈
        (IsLocalRing.maximalIdeal (FRL P)) ^ (t - (k + 1) + 1) := by
      rw [pow_add]
      exact Ideal.mul_mem_mul h1 h2
    rw [ha] at hcmem
    have hsm := Submodule.smul_mem
      ((IsLocalRing.maximalIdeal (FRL P)) ^ (t - k))
      (((-1 : FRL P) ^ ((j : ℕ)))) hcmem
    rwa [smul_eq_mul] at hsm
  have hdx : koszulContract (koszulContractOfSequence g) k
        ((c : FRL P) • exteriorPower.ιMulti (FRL P) (k + 1) v) =
      ∑ j : Fin (k + 1), (((-1 : FRL P) ^ ((j : ℕ))) *
          ((c : FRL P) * koszulContractOfSequence g (v j))) •
        exteriorPower.ιMulti (FRL P) k (v ∘ Fin.succAbove j) := by
    rw [map_smul]
    conv_lhs => rw [extPow_ιMulti_eq]
    rw [koszulContract_ιMulti_succ, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_comm _ _, ← mul_smul (c : FRL P) _ _, ← mul_smul _ _ _,
      ← extPow_ιMulti_eq]
  have hLTdx : leadTerm P d t k (koszulContract (koszulContractOfSequence g) k
        ((c : FRL P) • exteriorPower.ιMulti (FRL P) (k + 1) v)) =
      ∑ j : Fin (k + 1), leadGr P (t - k)
          ⟨((-1 : FRL P) ^ ((j : ℕ))) *
            ((c : FRL P) * koszulContractOfSequence g (v j)), hmem j⟩ •
        exteriorPower.ιMulti (grRegular P) k
          ((fun j => degZeroVec P d (v j)) ∘ Fin.succAbove j) := by
    rw [hdx, leadTerm_sum P d t k Finset.univ _
      (fun j _ => Submodule.smul_mem_smul (hmem j) Submodule.mem_top)]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact leadTerm_gen P d t k
      ⟨((-1 : FRL P) ^ ((j : ℕ))) *
        ((c : FRL P) * koszulContractOfSequence g (v j)), hmem j⟩
      (v ∘ Fin.succAbove j)
  have hgr : koszulContract (grlift_phiGr P d g hgen) k
        (exteriorPower.ιMulti (grRegular P) (k + 1)
          (fun j => degZeroVec P d (v j))) =
      ∑ j : Fin (k + 1), ((-1 : grRegular P) ^ ((j : ℕ))) •
        ((grlift_phiGr P d g hgen ((fun j => degZeroVec P d (v j)) j)) •
          exteriorPower.ιMulti (grRegular P) k
            ((fun j => degZeroVec P d (v j)) ∘ Fin.succAbove j)) := by
    conv_lhs => rw [extPow_ιMulti_eq]
    rw [koszulContract_ιMulti_succ]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← extPow_ιMulti_eq]
  have hRHS : koszulContract (grlift_phiGr P d g hgen) k
        (leadTerm P d t (k + 1)
          ((c : FRL P) • exteriorPower.ιMulti (FRL P) (k + 1) v)) =
      ∑ j : Fin (k + 1), ((-1 : grRegular P) ^ ((j : ℕ))) •
        ((leadGr P (t - (k + 1)) c *
          grlift_phiGr P d g hgen (degZeroVec P d (v j))) •
          exteriorPower.ιMulti (grRegular P) k
            ((fun j => degZeroVec P d (v j)) ∘ Fin.succAbove j)) := by
    rw [leadTerm_gen P d t (k + 1) c v, map_smul, hgr, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_comm _ _, ← mul_smul (leadGr P (t - (k + 1)) c) _ _]
  have hcoeff : ∀ j : Fin (k + 1), leadGr P (t - k)
        ⟨((-1 : FRL P) ^ ((j : ℕ))) *
          ((c : FRL P) * koszulContractOfSequence g (v j)), hmem j⟩ =
      (-1 : grRegular P) ^ ((j : ℕ)) * (leadGr P (t - (k + 1)) c *
        grlift_phiGr P d g hgen (degZeroVec P d (v j))) := by
    intro j
    set sgn : FRL P := (-1 : FRL P) ^ ((j : ℕ)) with hsgn
    set cx : FRL P := (c : FRL P) * koszulContractOfSequence g (v j) with hcx
    have hx : cx ∈ (IsLocalRing.maximalIdeal (FRL P)) ^ (t - k) := by
      rw [hcx]
      have hcmem : (c : FRL P) * koszulContractOfSequence g (v j) ∈
          (IsLocalRing.maximalIdeal (FRL P)) ^ (t - (k + 1) + 1) := by
        rw [pow_add]
        exact Ideal.mul_mem_mul c.2 (phi_mem_pow_one P d g hgen (v j))
      rwa [ha] at hcmem
    have hs0mem : sgn ∈ (IsLocalRing.maximalIdeal (FRL P)) ^ 0 := by
      rw [pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
    have hmem' : cx * sgn ∈ (IsLocalRing.maximalIdeal (FRL P)) ^ (t - k) := by
      rw [mul_comm cx sgn]
      exact hmem j
    have hcomm : (⟨sgn * cx, hmem j⟩ :
        ↥((IsLocalRing.maximalIdeal (FRL P)) ^ (t - k))) =
        ⟨cx * sgn, hmem'⟩ := Subtype.ext (mul_comm _ _)
    have h0 : leadGr P (t - k) ⟨sgn * cx, hmem j⟩ =
        leadGr P (t - k) ⟨cx, hx⟩ * leadGr P 0 ⟨sgn, hs0mem⟩ := by
      rw [hcomm]
      exact leadHomog_mul (IsLocalRing.maximalIdeal (FRL P)) (t - k) 0
        ⟨cx, hx⟩ ⟨sgn, hs0mem⟩
    have hs0 : leadGr P 0 ⟨sgn, hs0mem⟩ =
        (-1 : grRegular P) ^ ((j : ℕ)) := by
      have hmap : degZeroGrHom P sgn = (-1 : grRegular P) ^ ((j : ℕ)) := by
        rw [hsgn, map_pow, map_neg, map_one]
      exact hmap
    have h1 : leadGr P (t - k) ⟨cx, hx⟩ =
        leadGr P (t - (k + 1)) c * leadGr P 1
          ⟨koszulContractOfSequence g (v j),
            phi_mem_pow_one P d g hgen (v j)⟩ := by
      have hmul : ∀ (nn : ℕ) (hm : t - (k + 1) + 1 = nn)
          (e : ↥((IsLocalRing.maximalIdeal (FRL P)) ^ nn))
          (_ : (e : FRL P) = (c : FRL P) *
            koszulContractOfSequence g (v j)),
          leadGr P nn e = leadGr P (t - (k + 1)) c * leadGr P 1
            ⟨koszulContractOfSequence g (v j),
              phi_mem_pow_one P d g hgen (v j)⟩ := by
        intro nn hm e he
        subst hm
        have h := leadGr_mul P (t - (k + 1)) 1 c
          ⟨koszulContractOfSequence g (v j),
            phi_mem_pow_one P d g hgen (v j)⟩
        have hmemN : (c : FRL P) * koszulContractOfSequence g (v j) ∈
            (IsLocalRing.maximalIdeal (FRL P)) ^ (t - (k + 1) + 1) := by
          rw [pow_add]
          exact Ideal.mul_mem_mul c.2 (phi_mem_pow_one P d g hgen (v j))
        have heq : e = ⟨(c : FRL P) * koszulContractOfSequence g (v j),
            hmemN⟩ := Subtype.ext he
        rw [heq]
        exact h
      exact hmul (t - k) ha ⟨cx, hx⟩ rfl
    have hphi : leadGr P 1 ⟨koszulContractOfSequence g (v j),
        phi_mem_pow_one P d g hgen (v j)⟩ =
        grlift_phiGr P d g hgen (degZeroVec P d (v j)) :=
      (phiGr_degZeroVec P d g hgen (v j)).symm
    rw [h0, hs0, h1, hphi]
    exact mul_comm _ _
  rw [hLTdx, hRHS]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hcoeff j, ← mul_smul ((-1 : grRegular P) ^ ((j : ℕ))) _ _]

end Intertwine

/-! ## §5. Linearity extension and homogeneous leading-term data -/

section HomogData

variable {K : Type*} [Field K] {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K))
  [P.IsPrime] (d : ℕ) (g : Fin d → FRL P)

/-- Basis elements are decomposable wedges. Proved (Mathlib exterior-power
basis API: `Module.Basis.exteriorPower` is built from `ιMulti_family`). -/
theorem extBasis_eq_ιMulti (k : ℕ) (s : Set.powersetCard (Fin d) k) :
    (extBasis d k) s = exteriorPower.ιMulti (FRL P) k
      (fun j => (Pi.basisFun (FRL P) (Fin d))
        ((Set.powersetCard.ofFinEmbEquiv.symm s) j)) := by
  unfold extBasis
  rw [exteriorPower.basis_apply]
  rfl

/-- Intertwining for explicit restricted-generator sums. Proved by `Finset`
induction (generator bridge + additivity + `d`-linearity; every membership
side-condition discharged explicitly via `leadGen_preservation`). -/
theorem leadTerm_intertwine_sum
    (hgen : Ideal.span (Set.range g) = IsLocalRing.maximalIdeal (FRL P))
    (t k : ℕ) (htk : k + 1 ≤ t)
    {ι : Type*} (s : Finset ι) (c : ι → FRL P)
    (v : ι → (Fin (k + 1) → (Fin d → FRL P))) :
    (∀ i ∈ s, c i ∈ (IsLocalRing.maximalIdeal (FRL P)) ^ (t - (k + 1))) →
      leadTerm P d t k (koszulContract (koszulContractOfSequence g) k
        (∑ i ∈ s, (c i) • exteriorPower.ιMulti (FRL P) (k + 1) (v i))) =
        koszulContract (grlift_phiGr P d g hgen) k (leadTerm P d t (k + 1)
          (∑ i ∈ s, (c i) • exteriorPower.ιMulti (FRL P) (k + 1) (v i))) := by classical
  induction s using Finset.induction with
  | empty =>
    intro _
    rw [Finset.sum_empty, map_zero, leadTerm_zero, leadTerm_zero, map_zero]
  | insert a s' has ih =>
    intro hc
    have hc_a : c a ∈ (IsLocalRing.maximalIdeal (FRL P)) ^ (t - (k + 1)) :=
      hc a (Finset.mem_insert_self a s')
    have hc_s' : ∀ i ∈ s',
        c i ∈ (IsLocalRing.maximalIdeal (FRL P)) ^ (t - (k + 1)) :=
      fun i hi => hc i (Finset.mem_insert_of_mem hi)
    have e3 : leadTerm P d t k (koszulContract (koszulContractOfSequence g) k
          ((c a) • exteriorPower.ιMulti (FRL P) (k + 1) (v a))) =
        koszulContract (grlift_phiGr P d g hgen) k (leadTerm P d t (k + 1)
          ((c a) • exteriorPower.ιMulti (FRL P) (k + 1) (v a))) :=
      leadTerm_intertwine_gen P d g hgen t k htk ⟨c a, hc_a⟩ (v a)
    have e4 := ih hc_s'
    rw [Finset.sum_insert has, map_add]
    have hd_a : koszulContract (koszulContractOfSequence g) k
          ((c a) • exteriorPower.ιMulti (FRL P) (k + 1) (v a)) ∈
        filtrPiece P d t k :=
      leadGen_preservation P d g hgen t k ⟨c a, hc_a⟩ (v a)
    have hd_s' : koszulContract (koszulContractOfSequence g) k
          (∑ i ∈ s', (c i) • exteriorPower.ιMulti (FRL P) (k + 1) (v i)) ∈
        filtrPiece P d t k := by
      rw [map_sum]
      exact Submodule.sum_mem _ fun i hi =>
        leadGen_preservation P d g hgen t k ⟨c i, hc_s' i hi⟩ (v i)
    rw [leadTerm_add P d t k _ _ hd_a hd_s', e3, e4]
    have ht_a : (c a) • exteriorPower.ιMulti (FRL P) (k + 1) (v a) ∈
        filtrPiece P d t (k + 1) := by
      rw [filtrPiece_def]
      exact Submodule.smul_mem_smul hc_a Submodule.mem_top
    have ht_s' : (∑ i ∈ s', (c i) •
        exteriorPower.ιMulti (FRL P) (k + 1) (v i)) ∈
        filtrPiece P d t (k + 1) :=
      Submodule.sum_mem _ fun i hi => by
        rw [filtrPiece_def]
        exact Submodule.smul_mem_smul (hc_s' i hi) Submodule.mem_top
    rw [leadTerm_add P d t (k + 1) _ _ ht_a ht_s', map_add]

/-- Intertwining for all piece elements. Proved (coordinate expansion into
restricted generators + `leadTerm_intertwine_sum`). Needs `k + 1 ≤ t`:
unrestricted intertwining is false (LHS/RHS live in different gr-degrees). -/
theorem leadTerm_intertwine_all
    (hgen : Ideal.span (Set.range g) = IsLocalRing.maximalIdeal (FRL P))
    (t k : ℕ) (htk : k + 1 ≤ t)
    (x : ↥(⋀[FRL P]^(k + 1) (Fin d → FRL P)))
    (hx : x ∈ filtrPiece P d t (k + 1)) :
    leadTerm P d t k (koszulContract (koszulContractOfSequence g) k x) =
      koszulContract (grlift_phiGr P d g hgen) k
        (leadTerm P d t (k + 1) x) := by
  have hexp : x = ∑ s, ((extBasis d (k + 1)).repr x s) •
      (extBasis d (k + 1)) s :=
    ((extBasis d (k + 1)).sum_repr x).symm
  have hcoords : ∀ s, (extBasis d (k + 1)).repr x s ∈
      (IsLocalRing.maximalIdeal (FRL P)) ^ (t - (k + 1)) :=
    (mem_filtrPiece_iff_coords P d t (k + 1) x).mp hx
  have hι : ∀ s : Set.powersetCard (Fin d) (k + 1),
      (extBasis d (k + 1)) s = exteriorPower.ιMulti (FRL P) (k + 1)
        (fun j => (Pi.basisFun (FRL P) (Fin d))
          ((Set.powersetCard.ofFinEmbEquiv.symm s) j)) :=
    fun s => extBasis_eq_ιMulti P d (k + 1) s
  rw [hexp]
  simp only [hι]
  exact leadTerm_intertwine_sum P d g hgen t k htk Finset.univ
    (fun i => (extBasis d (k + 1)).repr x i)
    (fun i j => (Pi.basisFun (FRL P) (Fin d))
      ((Set.powersetCard.ofFinEmbEquiv.symm i) j))
    (fun i _ => hcoords i)

/-- `LT`-outputs are homogeneous combinations. Proved (the coordinate
definition: `leadGr = leadOf ∘ leadCoeffMk`). Feeds homogeneous exactness.
The degree is a bound variable with a proof-position equation (this keeps
all `grPiece` indices defeq-clean in the projection argument). -/
theorem leadTerm_homog_form (t k : ℕ)
    (x : ↥(⋀[FRL P]^k (Fin d → FRL P))) (hx : x ∈ filtrPiece P d t k) :
    ∃ (e : ℕ) (_he : e = t - k) (w : Set.powersetCard (Fin d) k →
      grPiece (FRL P) (IsLocalRing.maximalIdeal (FRL P)) e),
      leadTerm P d t k x =
        ∑ s, leadOf P e (w s) • (extBasisGr P d k) s := by
  refine ⟨t - k, rfl, fun s => leadCoeffMk _ (t - k)
    ⟨(extBasis d k).repr x s,
      (mem_filtrPiece_iff_coords P d t k x).mp hx s⟩, ?_⟩
  unfold leadTerm
  rw [dite_eq_left hx]
  rfl

/-- Homogeneous leading-term data: the exact restriction of `FiltrLeadData`
(`FiltrationLift.lean`) to what single-degree maps satisfy. Narrowings
(each forced: the literal clause is false for `leadTerm`):
* intertwining carries `k + 1 ≤ t` (without it, LHS/RHS sit in different
  gr-degrees: `(t - (k+1)) + 1 ≠ t - k`);
* lift-back is onto homogeneous (single-degree-coefficient) combinations
  only (the image of a single-degree map is homogeneous).
Kernel control is unchanged. The `hdx` hypothesis of the literal
intertwining clause is dropped (strengthening): `d`-preservation is proved
inside, per generator. A sixth clause records that `LT`-outputs are
homogeneous combinations (feeds homogeneous exactness in the lift). -/
def FiltrLeadDataHomog
    (hgen : Ideal.span (Set.range g) = IsLocalRing.maximalIdeal (FRL P)) :
    Prop :=
  ∃ LT : ∀ (_t k : ℕ), ↥(⋀[FRL P]^k (Fin d → FRL P)) →
      ↥(⋀[grRegular P]^k (Fin d → grRegular P)),
    (∀ (t k : ℕ), LT t k 0 = 0) ∧
    (∀ (t k : ℕ) (x y : ↥(⋀[FRL P]^k (Fin d → FRL P)))
      (_hx : x ∈ filtrPiece P d t k) (_hy : y ∈ filtrPiece P d t k),
      LT t k (x + y) = LT t k x + LT t k y) ∧
    (∀ (t k : ℕ) (_htk : k + 1 ≤ t)
      (x : ↥(⋀[FRL P]^(k + 1) (Fin d → FRL P)))
      (_hx : x ∈ filtrPiece P d t (k + 1)),
      LT t k (koszulContract (koszulContractOfSequence g) k x) =
        koszulContract (grlift_phiGr P d g hgen) k (LT t (k + 1) x)) ∧
    (∀ (t k : ℕ) (x : ↥(⋀[FRL P]^(k + 1) (Fin d → FRL P)))
      (_hx : x ∈ filtrPiece P d t (k + 1)),
      LT t (k + 1) x = 0 → x ∈ filtrPiece P d (t + 1) (k + 1)) ∧
    (∀ (t k : ℕ) (x : ↥(⋀[FRL P]^k (Fin d → FRL P)))
      (_hx : x ∈ filtrPiece P d t k),
      ∃ (e : ℕ) (_he : e = t - k) (w : Set.powersetCard (Fin d) k →
        grPiece (FRL P) (IsLocalRing.maximalIdeal (FRL P)) e),
        LT t k x = ∑ s, leadOf P e (w s) • (extBasisGr P d k) s) ∧
    ∀ (t k : ℕ) (e : ℕ) (_he : e = t - k)
      (w : Set.powersetCard (Fin d) k →
        grPiece (FRL P) (IsLocalRing.maximalIdeal (FRL P)) e),
      ∃ x : ↥(⋀[FRL P]^k (Fin d → FRL P)),
        x ∈ filtrPiece P d t k ∧ LT t k x =
          ∑ s, leadOf P e (w s) • (extBasisGr P d k) s

/-- The homogeneous data, constructed. Proved (all six clauses). -/
theorem filtrLeadDataHomog
    (hgen : Ideal.span (Set.range g) = IsLocalRing.maximalIdeal (FRL P)) :
    FiltrLeadDataHomog P d g hgen :=
  ⟨leadTerm P d, leadTerm_zero P d, leadTerm_add P d,
    fun t k htk x hx => leadTerm_intertwine_all P d g hgen t k htk x hx,
    fun t k x hx h0 => leadTerm_kernel P d t (k + 1) x hx h0,
    fun t k x hx => leadTerm_homog_form P d t k x hx,
    fun t k e he w => by
      subst he
      exact leadTerm_homog_surjective P d t k w⟩

end HomogData

/-! ## §6. Homogeneous projection for the gr-side complex -/

section HomogProject

variable {K : Type*} [Field K] {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K))
  [P.IsPrime] (d : ℕ) (g : Fin d → FRL P)

/-- Gr-generator classes are homogeneous of degree 1, by construction. -/
theorem grlift_grClass_eq_leadOf
    (hgen : Ideal.span (Set.range g) = IsLocalRing.maximalIdeal (FRL P))
    (i : Fin d) :
    grlift_grClass P d g hgen i = leadOf P 1
      (genClass (FRL P) (IsLocalRing.maximalIdeal (FRL P)) d g i hgen) := rfl

/-- Gr-side basis elements are decomposable wedges. Proved (same API as
`extBasis_eq_ιMulti`, over `grRegular`). -/
theorem extBasisGr_eq_ιMulti (k : ℕ) (s : Set.powersetCard (Fin d) k) :
    (extBasisGr P d k) s = exteriorPower.ιMulti (grRegular P) k
      (fun j => (Pi.basisFun (grRegular P) (Fin d))
        ((Set.powersetCard.ofFinEmbEquiv.symm s) j)) := by
  unfold extBasisGr extBasis
  rw [exteriorPower.basis_apply]
  rfl

/-- The gr-functional on std-basis vectors is homogeneous of degree 1.
proved (`Basis.constr` evaluates on basis vectors). -/
theorem phiGr_std_homog_one
    (hgen : Ideal.span (Set.range g) = IsLocalRing.maximalIdeal (FRL P))
    (idx : Fin d) :
    grlift_phiGr P d g hgen ((Pi.basisFun (grRegular P) (Fin d)) idx) =
      leadOf P 1 (genClass (FRL P) (IsLocalRing.maximalIdeal (FRL P)) d g
        idx hgen) := by
  unfold grlift_phiGr koszulContractOfSequence
  rw [Module.Basis.constr_basis, grlift_grClass_eq_leadOf]

/-- Wedge-of-std-vectors coordinates sit in degree 0. Proved (`det` of a
0/1-matrix is `degZero` of the same `det` over `FRL`, hence `of_0`). -/
theorem wedge_std_coord_homog_zero (k : ℕ)
    (a : Fin k → Fin d) (t : Set.powersetCard (Fin d) k) :
    (extBasisGr P d k).repr
        (exteriorPower.ιMulti (grRegular P) k
          (fun i => (Pi.basisFun (grRegular P) (Fin d)) (a i))) t =
      leadOf P 0 (leadCoeffMk _ 0
        ⟨Matrix.det (Matrix.of fun i j' =>
          ((Pi.basisFun (FRL P) (Fin d)) (a i))
            ((Set.powersetCard.ofFinEmbEquiv.symm t) j')), by
          rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top⟩) := by
  unfold extBasisGr
  rw [extBasis_repr_ιMulti_gen]
  have hmat : (Matrix.of fun i j' =>
        (((Pi.basisFun (grRegular P) (Fin d)) (a i))
          ((Set.powersetCard.ofFinEmbEquiv.symm t) j'))) =
      Matrix.of fun i j' => degZeroGrHom P
        (((Pi.basisFun (FRL P) (Fin d)) (a i))
          ((Set.powersetCard.ofFinEmbEquiv.symm t) j')) := by
    congr 1
    funext i j'
    simp only [Pi.basisFun_apply]
    by_cases h : ((Set.powersetCard.ofFinEmbEquiv.symm t) j') = (a i)
    · simp_all
    · have h' : (a i) ≠ ((Set.powersetCard.ofFinEmbEquiv.symm t) j') :=
        Ne.symm h
      simp_all
  rw [hmat, det_degZeroGrHom]
  rfl

set_option maxHeartbeats 2000000 in -- per-coordinate `gr`-contraction assembly exceeds default.
/-- `d_gr` of a gr-basis wedge is homogeneous of degree 1. Proved
(contraction formula + `phiGr`-on-std is degree 1 + wedge coords degree 0,
assembled per-coordinate). -/
theorem dgr_basis_homog_one
    (hgen : Ideal.span (Set.range g) = IsLocalRing.maximalIdeal (FRL P))
    (k : ℕ) (s : Set.powersetCard (Fin d) (k + 1)) :
    ∃ q : Set.powersetCard (Fin d) k →
      grPiece (FRL P) (IsLocalRing.maximalIdeal (FRL P)) 1,
      koszulContract (grlift_phiGr P d g hgen) k
        ((extBasisGr P d (k + 1)) s) =
        ∑ t, leadOf P 1 (q t) • (extBasisGr P d k) t := by
  have hsgn : ∀ j : Fin (k + 1), ((-1 : grRegular P) ^ ((j : ℕ))) =
      leadOf P 0 (leadCoeffMk _ 0
        ⟨(-1 : FRL P) ^ ((j : ℕ)), by
          rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top⟩) := by
    intro j
    have h1 : degZeroGrHom P ((-1 : FRL P) ^ ((j : ℕ))) =
        (-1 : grRegular P) ^ ((j : ℕ)) := by
      rw [map_pow, map_neg, map_one]
    have h2 : leadOf P 0 (leadCoeffMk _ 0
        ⟨(-1 : FRL P) ^ ((j : ℕ)), by
          rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top⟩) =
        degZeroGrHom P ((-1 : FRL P) ^ ((j : ℕ))) := rfl
    exact (h2.trans h1).symm
  have hwedge : ∀ (j : Fin (k + 1)) (t : Set.powersetCard (Fin d) k),
      (extBasisGr P d k).repr
        (exteriorPower.ιMulti (grRegular P) k
          (((fun j => (Pi.basisFun (grRegular P) (Fin d))
            ((Set.powersetCard.ofFinEmbEquiv.symm s) j)) ∘
            Fin.succAbove j))) t =
        leadOf P 0 (leadCoeffMk _ 0
          ⟨Matrix.det (Matrix.of fun i j' =>
            ((Pi.basisFun (FRL P) (Fin d))
              (((Set.powersetCard.ofFinEmbEquiv.symm s) ∘ Fin.succAbove j) i))
              ((Set.powersetCard.ofFinEmbEquiv.symm t) j')), by
            rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top⟩) :=
    fun j t => wedge_std_coord_homog_zero P d k
      (fun i => ((Set.powersetCard.ofFinEmbEquiv.symm s) ∘ Fin.succAbove j) i) t
  have ofmul : ∀ (i j : ℕ) (a : grPiece (FRL P)
      (IsLocalRing.maximalIdeal (FRL P)) i)
      (b : grPiece (FRL P) (IsLocalRing.maximalIdeal (FRL P)) j),
      leadOf P i a * leadOf P j b = leadOf P (i + j)
        (GradedMonoid.GMul.mul
          (A := grPiece (FRL P) (IsLocalRing.maximalIdeal (FRL P))) a b) :=
    fun i j a b => associatedGraded_of_mul_of (R := FRL P)
      (I := IsLocalRing.maximalIdeal (FRL P)) i j a b
  have key : ∀ t : Set.powersetCard (Fin d) k,
      (extBasisGr P d k).repr
        (koszulContract (grlift_phiGr P d g hgen) k
          ((extBasisGr P d (k + 1)) s)) t =
        leadOf P 1 (∑ j : Fin (k + 1), GradedMonoid.GMul.mul
          (A := grPiece (FRL P) (IsLocalRing.maximalIdeal (FRL P)))
          (leadCoeffMk _ 0 ⟨(-1 : FRL P) ^ ((j : ℕ)), by
            rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top⟩)
          (GradedMonoid.GMul.mul
            (A := grPiece (FRL P) (IsLocalRing.maximalIdeal (FRL P)))
            (genClass (FRL P) (IsLocalRing.maximalIdeal (FRL P)) d g
              ((Set.powersetCard.ofFinEmbEquiv.symm s) j) hgen)
            (leadCoeffMk _ 0
              ⟨Matrix.det (Matrix.of fun i j' =>
                ((Pi.basisFun (FRL P) (Fin d))
                  (((Set.powersetCard.ofFinEmbEquiv.symm s) ∘
                    Fin.succAbove j) i))
                  ((Set.powersetCard.ofFinEmbEquiv.symm t) j')), by
                rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top⟩))) := by
    intro t
    rw [extBasisGr_eq_ιMulti, extPow_ιMulti_eq, koszulContract_ιMulti_succ]
    simp only [← extPow_ιMulti_eq, map_sum, Finsupp.finsetSum_apply,
      map_smul, Finsupp.smul_apply]
    unfold leadOf
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_eq_mul, smul_eq_mul, phiGr_std_homog_one, hwedge j t, hsgn j,
      ofmul, ofmul]
    rfl
  refine ⟨fun t => ∑ j : Fin (k + 1), GradedMonoid.GMul.mul
    (A := grPiece (FRL P) (IsLocalRing.maximalIdeal (FRL P)))
    (leadCoeffMk _ 0 ⟨(-1 : FRL P) ^ ((j : ℕ)), by
      rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top⟩)
    (GradedMonoid.GMul.mul
      (A := grPiece (FRL P) (IsLocalRing.maximalIdeal (FRL P)))
      (genClass (FRL P) (IsLocalRing.maximalIdeal (FRL P)) d g
        ((Set.powersetCard.ofFinEmbEquiv.symm s) j) hgen)
      (leadCoeffMk _ 0
        ⟨Matrix.det (Matrix.of fun i j' =>
          ((Pi.basisFun (FRL P) (Fin d))
            (((Set.powersetCard.ofFinEmbEquiv.symm s) ∘ Fin.succAbove j) i))
            ((Set.powersetCard.ofFinEmbEquiv.symm t) j')), by
          rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top⟩)), ?_⟩
  apply (extBasisGr P d k).repr.injective
  ext t
  unfold extBasisGr
  rw [basis_repr_sum_smul]
  exact key t

/-- Graded piece-mul kills zero. Proved (via `of`-injectivity). -/
theorem grPiece_gMul_zero_left (a b : ℕ)
    (y : grPiece (FRL P) (IsLocalRing.maximalIdeal (FRL P)) b) :
    GradedMonoid.GMul.mul (A := grPiece (FRL P) (IsLocalRing.maximalIdeal (FRL P)))
      (0 : grPiece (FRL P) (IsLocalRing.maximalIdeal (FRL P)) a) y = 0 := by
  have hmul := associatedGraded_of_mul_of (R := FRL P)
    (I := IsLocalRing.maximalIdeal (FRL P)) a b
    (0 : grPiece (FRL P) (IsLocalRing.maximalIdeal (FRL P)) a) y
  rw [map_zero, zero_mul] at hmul
  have h0 : DirectSum.of (grPiece (FRL P) (IsLocalRing.maximalIdeal (FRL P)))
      (a + b) (GradedMonoid.GMul.mul
        (A := grPiece (FRL P) (IsLocalRing.maximalIdeal (FRL P)))
        (0 : grPiece (FRL P) (IsLocalRing.maximalIdeal (FRL P)) a) y) =
      DirectSum.of (grPiece (FRL P) (IsLocalRing.maximalIdeal (FRL P))) (a + b) 0 := by
    rw [← hmul, map_zero]
  exact DirectSum.of_injective _ h0

/-- Graded-mul component law: `(w * of_1)` at `f+1` sees only `w f`. Proved
(support expansion + graded-mul + component extraction). -/
theorem grMul_component_succ
    (w : ⨁ a, grPiece (FRL P) (IsLocalRing.maximalIdeal (FRL P)) a)
    (dd : grPiece (FRL P) (IsLocalRing.maximalIdeal (FRL P)) 1) (f : ℕ) :
    (w * DirectSum.of _ 1 dd) (f + 1) =
      GradedMonoid.GMul.mul (A := grPiece (FRL P) (IsLocalRing.maximalIdeal (FRL P)))
        (w f) dd := by
  have : CommRing (⨁ a, grPiece (FRL P) (IsLocalRing.maximalIdeal (FRL P)) a) :=
    inferInstanceAs (CommRing (grRegular P))
  classical
  have ofmul : ∀ (i j : ℕ) (a : grPiece (FRL P)
      (IsLocalRing.maximalIdeal (FRL P)) i)
      (b : grPiece (FRL P) (IsLocalRing.maximalIdeal (FRL P)) j),
      DirectSum.of _ i a * DirectSum.of _ j b =
        DirectSum.of _ (i + j) (GradedMonoid.GMul.mul
          (A := grPiece (FRL P) (IsLocalRing.maximalIdeal (FRL P))) a b) :=
    fun i j a b => associatedGraded_of_mul_of (R := FRL P)
      (I := IsLocalRing.maximalIdeal (FRL P)) i j a b
  have hexp : w * DirectSum.of _ 1 dd =
      (∑ g ∈ w.support, DirectSum.of _ g (w g)) * DirectSum.of _ 1 dd := by
    congr 1
    exact (DirectSum.sum_support_of w).symm
  rw [hexp, Finset.sum_mul]
  simp only [ofmul]
  have hsa : (∑ g ∈ w.support, DirectSum.of _ (g + 1)
      (GradedMonoid.GMul.mul (A := grPiece (FRL P)
        (IsLocalRing.maximalIdeal (FRL P))) (w g) dd)) (f + 1) =
      ∑ g ∈ w.support, (DirectSum.of _ (g + 1)
        (GradedMonoid.GMul.mul (A := grPiece (FRL P)
          (IsLocalRing.maximalIdeal (FRL P))) (w g) dd)) (f + 1) :=
    DirectSum.sum_apply _ _ _
  rw [hsa, Finset.sum_eq_single f]
  · rw [DirectSum.of_eq_same]
  · intro g _ hg
    have hne : f + 1 ≠ g + 1 := by omega
    rw [DirectSum.of_eq_of_ne _ _ _ hne]
  · intro hf
    have hw0 : w f = 0 :=
      of_not_not fun hn => hf (DFinsupp.mem_support_iff.mpr hn)
    have hG0 : GradedMonoid.GMul.mul
        (A := grPiece (FRL P) (IsLocalRing.maximalIdeal (FRL P))) (w f) dd = 0 := by
      rw [hw0]
      exact grPiece_gMul_zero_left P f 1 dd
    rw [hG0, DirectSum.of_eq_same]

/-- Graded-mul has no degree-0 part against `of_1`. Proved (support
expansion: every term lies in degree `≥ 1`). -/
theorem grMul_component_zero
    (w : ⨁ a, grPiece (FRL P) (IsLocalRing.maximalIdeal (FRL P)) a)
    (dd : grPiece (FRL P) (IsLocalRing.maximalIdeal (FRL P)) 1) :
    (w * DirectSum.of _ 1 dd) 0 = 0 := by
  have : CommRing (⨁ a, grPiece (FRL P) (IsLocalRing.maximalIdeal (FRL P)) a) :=
    inferInstanceAs (CommRing (grRegular P))
  classical
  have ofmul : ∀ (i j : ℕ) (a : grPiece (FRL P)
      (IsLocalRing.maximalIdeal (FRL P)) i)
      (b : grPiece (FRL P) (IsLocalRing.maximalIdeal (FRL P)) j),
      DirectSum.of _ i a * DirectSum.of _ j b =
        DirectSum.of _ (i + j) (GradedMonoid.GMul.mul
          (A := grPiece (FRL P) (IsLocalRing.maximalIdeal (FRL P))) a b) :=
    fun i j a b => associatedGraded_of_mul_of (R := FRL P)
      (I := IsLocalRing.maximalIdeal (FRL P)) i j a b
  have hexp : w * DirectSum.of _ 1 dd =
      (∑ g ∈ w.support, DirectSum.of _ g (w g)) * DirectSum.of _ 1 dd := by
    congr 1
    exact (DirectSum.sum_support_of w).symm
  rw [hexp, Finset.sum_mul]
  simp only [ofmul]
  have hsa : (∑ g ∈ w.support, DirectSum.of _ (g + 1)
      (GradedMonoid.GMul.mul (A := grPiece (FRL P)
        (IsLocalRing.maximalIdeal (FRL P))) (w g) dd)) 0 =
      ∑ g ∈ w.support, (DirectSum.of _ (g + 1)
        (GradedMonoid.GMul.mul (A := grPiece (FRL P)
          (IsLocalRing.maximalIdeal (FRL P))) (w g) dd)) 0 :=
    DirectSum.sum_apply _ _ _
  rw [hsa]
  have h0 : ∀ (g : ℕ) (y : grPiece (FRL P)
      (IsLocalRing.maximalIdeal (FRL P)) (g + 1)),
      (DirectSum.of _ (g + 1) y) 0 = 0 :=
    fun g y => DirectSum.of_eq_of_ne _ _ _ (by omega)
  simp only [h0, Finset.sum_const_zero]

/-- Homogeneous component access (plain-def `grRegular` admits no direct
application, so this `⨁`-typed wrapper is applied to `grRegular` terms by
defeq). -/
noncomputable def grComp
    (x : ⨁ a, grPiece (FRL P) (IsLocalRing.maximalIdeal (FRL P)) a)
    (f : ℕ) : grPiece (FRL P) (IsLocalRing.maximalIdeal (FRL P)) f := x f

/-- Component laws in `grComp` form (syntactic matching). -/
theorem grMul_component_succ_grComp
    (w : ⨁ a, grPiece (FRL P) (IsLocalRing.maximalIdeal (FRL P)) a)
    (dd : grPiece (FRL P) (IsLocalRing.maximalIdeal (FRL P)) 1) (f : ℕ) :
    grComp P (w * DirectSum.of _ 1 dd) (f + 1) =
      GradedMonoid.GMul.mul (A := grPiece (FRL P) (IsLocalRing.maximalIdeal (FRL P)))
        (grComp P w f) dd := by
  unfold grComp
  exact grMul_component_succ P w dd f

/-- Degree-`0` component law in `grComp` form: right-multiplication by a
degree-`1` element kills the `0`-component. -/
theorem grMul_component_zero_grComp
    (w : ⨁ a, grPiece (FRL P) (IsLocalRing.maximalIdeal (FRL P)) a)
    (dd : grPiece (FRL P) (IsLocalRing.maximalIdeal (FRL P)) 1) :
    grComp P (w * DirectSum.of _ 1 dd) 0 = 0 := by
  unfold grComp
  exact grMul_component_zero P w dd

end HomogProject

/-! ## §7. Uniform projection lift + homogeneous single-step pipeline -/

section HomogLift

variable {K : Type*} [Field K] {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K))
  [P.IsPrime] (d : ℕ) (g : Fin d → FRL P)

/-- `grComp` extracts `leadOf`-inclusions. Proved. -/
theorem grComp_leadOf (a : ℕ)
    (z : grPiece (FRL P) (IsLocalRing.maximalIdeal (FRL P)) a) :
    grComp P (leadOf P a z) a = z := by
  unfold grComp leadOf
  rw [DirectSum.of_eq_same]

/-- `grComp` commutes with sums. Proved. -/
theorem grComp_sum {ι : Type*} (s : Finset ι) (f : ι → grRegular P) (e : ℕ) :
    grComp P (∑ i ∈ s, f i) e = ∑ i ∈ s, grComp P (f i) e := by
  unfold grComp
  exact DirectSum.sum_apply _ _ _

/-- Graded-mul component law in `leadOf` form (matches call-site syntax).
proved (unfold + `grComp` corollary). -/
theorem grMul_component_succ_grComp_leadOf (w : grRegular P)
    (dd : grPiece (FRL P) (IsLocalRing.maximalIdeal (FRL P)) 1) (f : ℕ) :
    grComp P (w * leadOf P 1 dd) (f + 1) =
      GradedMonoid.GMul.mul (A := grPiece (FRL P) (IsLocalRing.maximalIdeal (FRL P)))
        (grComp P w f) dd := by
  exact grMul_component_succ_grComp P w dd f

/-- `leadOf` of a sum is the sum. Proved (direct `map_sum`). -/
theorem leadOf_sum_direct (a : ℕ) {ι : Type*} (s : Finset ι)
    (f : ι → grPiece (FRL P) (IsLocalRing.maximalIdeal (FRL P)) a) :
    ∑ i ∈ s, leadOf P a (f i) = leadOf P a (∑ i ∈ s, f i) := by
  unfold leadOf
  exact (map_sum _ _ _).symm

/-- Gr-differential on basis expansions, with explicit coefficients. Proved
(linearity + basis values + `sum_comm`). -/
theorem dgr_sum_expand
    (hgen : Ideal.span (Set.range g) = IsLocalRing.maximalIdeal (FRL P))
    (k : ℕ) (c : Set.powersetCard (Fin d) ((k + 1) + 1) → grRegular P)
    (q : Set.powersetCard (Fin d) ((k + 1) + 1) →
      Set.powersetCard (Fin d) (k + 1) →
      grPiece (FRL P) (IsLocalRing.maximalIdeal (FRL P)) 1)
    (hq : ∀ s, koszulContract (grlift_phiGr P d g hgen) (k + 1)
        ((extBasisGr P d ((k + 1) + 1)) s) =
        ∑ t, leadOf P 1 (q s t) • (extBasisGr P d (k + 1)) t) :
    koszulContract (grlift_phiGr P d g hgen) (k + 1)
        (∑ s, c s • (extBasisGr P d ((k + 1) + 1)) s) =
      ∑ t, (∑ s, c s * leadOf P 1 (q s t)) •
        (extBasisGr P d (k + 1)) t := by
  rw [map_sum]
  simp only [map_smul, hq, Finset.smul_sum]
  rw [Finset.sum_comm]
  simp only [← mul_smul, ← Finset.sum_smul]

/-- `d` preserves filtration pieces. Proved (coordinate expansion into
restricted generators + `leadGen_preservation`; no degree restriction). -/
theorem filtr_d_preserve
    (hgen : Ideal.span (Set.range g) = IsLocalRing.maximalIdeal (FRL P))
    (t k : ℕ) (x : ↥(⋀[FRL P]^(k + 1) (Fin d → FRL P)))
    (hx : x ∈ filtrPiece P d t (k + 1)) :
    koszulContract (koszulContractOfSequence g) k x ∈ filtrPiece P d t k := by
  have hexp : x = ∑ s, ((extBasis d (k + 1)).repr x s) •
      (extBasis d (k + 1)) s :=
    ((extBasis d (k + 1)).sum_repr x).symm
  have hcoords : ∀ s, (extBasis d (k + 1)).repr x s ∈
      (IsLocalRing.maximalIdeal (FRL P)) ^ (t - (k + 1)) :=
    (mem_filtrPiece_iff_coords P d t (k + 1) x).mp hx
  rw [hexp, map_sum]
  refine Submodule.sum_mem _ fun s _ => ?_
  rw [extBasis_eq_ιMulti P d (k + 1) s]
  exact leadGen_preservation P d g hgen t k
    ⟨(extBasis d (k + 1)).repr x s, hcoords s⟩ _

/-- Uniform projection lift: a gr-side primitive of a homogeneous target
projects to a homogeneous primitive of the same target. Proved (coefficient
extraction via the basis + graded-mul component laws: only the degree-`e'`
slice survives `grComp` at `e' + 1`). -/
theorem dgr_homog_project
    (hgen : Ideal.span (Set.range g) = IsLocalRing.maximalIdeal (FRL P))
    (k e' : ℕ)
    (U : ↥(⋀[grRegular P]^((k + 1) + 1) (Fin d → grRegular P)))
    (w : Set.powersetCard (Fin d) (k + 1) →
      grPiece (FRL P) (IsLocalRing.maximalIdeal (FRL P)) (e' + 1))
    (hUW : koszulContract (grlift_phiGr P d g hgen) (k + 1) U =
      ∑ t, leadOf P (e' + 1) (w t) • (extBasisGr P d (k + 1)) t) :
    ∃ U' : ↥(⋀[grRegular P]^((k + 1) + 1) (Fin d → grRegular P)),
      (∃ w' : Set.powersetCard (Fin d) ((k + 1) + 1) →
          grPiece (FRL P) (IsLocalRing.maximalIdeal (FRL P)) e',
        U' = ∑ s, leadOf P e' (w' s) •
          (extBasisGr P d ((k + 1) + 1)) s) ∧
      koszulContract (grlift_phiGr P d g hgen) (k + 1) U' =
        ∑ t, leadOf P (e' + 1) (w t) • (extBasisGr P d (k + 1)) t := by
  choose q hq using fun s => dgr_basis_homog_one P d g hgen (k + 1) s
  have hU : U = ∑ s, (extBasisGr P d ((k + 1) + 1)).repr U s •
      (extBasisGr P d ((k + 1) + 1)) s :=
    ((extBasisGr P d ((k + 1) + 1)).sum_repr U).symm
  rw [hU, dgr_sum_expand P d g hgen k _ q hq] at hUW
  have hcoeff : ∀ t, (∑ s, (extBasisGr P d ((k + 1) + 1)).repr U s *
      leadOf P 1 (q s t)) = leadOf P (e' + 1) (w t) := by
    intro t
    have h := congrArg
      (fun W => (extBasis (R := grRegular P) d (k + 1)).repr W t) hUW
    simp only [extBasisGr] at h
    simp only [basis_repr_sum_smul d (k + 1)] at h
    exact h
  have hG : ∀ t, (∑ s, GradedMonoid.GMul.mul
      (A := grPiece (FRL P) (IsLocalRing.maximalIdeal (FRL P)))
      (grComp P ((extBasisGr P d ((k + 1) + 1)).repr U s) e') (q s t)) =
      w t := by
    intro t
    calc (∑ s, GradedMonoid.GMul.mul
            (A := grPiece (FRL P) (IsLocalRing.maximalIdeal (FRL P)))
            (grComp P ((extBasisGr P d ((k + 1) + 1)).repr U s) e') (q s t))
        = ∑ s, grComp P
            (((extBasisGr P d ((k + 1) + 1)).repr U s) *
              leadOf P 1 (q s t)) (e' + 1) :=
          Finset.sum_congr rfl fun s _ =>
            (grMul_component_succ_grComp_leadOf P _ _ _).symm
      _ = grComp P
            (∑ s, ((extBasisGr P d ((k + 1) + 1)).repr U s) *
              leadOf P 1 (q s t)) (e' + 1) := (grComp_sum P _ _ _).symm
      _ = grComp P (leadOf P (e' + 1) (w t)) (e' + 1) :=
          congrArg (fun y : grRegular P => grComp P y (e' + 1)) (hcoeff t)
      _ = w t := grComp_leadOf P _ _
  have hCt : ∀ t, (∑ s, leadOf P e'
        (grComp P ((extBasisGr P d ((k + 1) + 1)).repr U s) e') *
        leadOf P 1 (q s t)) = leadOf P (e' + 1) (w t) := by
    intro t
    have ofmul : ∀ (a : grPiece (FRL P)
        (IsLocalRing.maximalIdeal (FRL P)) e')
        (b : grPiece (FRL P) (IsLocalRing.maximalIdeal (FRL P)) 1),
        leadOf P e' a * leadOf P 1 b = leadOf P (e' + 1)
          (GradedMonoid.GMul.mul
            (A := grPiece (FRL P) (IsLocalRing.maximalIdeal (FRL P))) a b) :=
      fun a b => associatedGraded_of_mul_of (R := FRL P)
        (I := IsLocalRing.maximalIdeal (FRL P)) e' 1 a b
    simp only [ofmul]
    rw [leadOf_sum_direct P (e' + 1) Finset.univ]
    congr 1
    exact hG t
  refine ⟨∑ s, leadOf P e'
      (grComp P ((extBasisGr P d ((k + 1) + 1)).repr U s) e') •
      (extBasisGr P d ((k + 1) + 1)) s,
    ⟨fun s => grComp P ((extBasisGr P d ((k + 1) + 1)).repr U s) e',
      rfl⟩, ?_⟩
  rw [dgr_sum_expand P d g hgen k _ q hq]
  simp only [hCt]

/-- Homogeneous single-step lift: a cycle in `F(t)` is a boundary plus a
strictly deeper cycle, for `j + 2 ≤ t`. Proved from the homogeneous data +
gr-exactness (the `j + 2 ≤ t` hypothesis is exactly what makes the
intertwining and the degree-`(e' + 1)` projection go through). This is the
minimal bridge downstream needs: it replaces both `FiltrGenBound` (via
`filtr_d_preserve`) and full `FiltrLeadData` (via projection + homogeneous
lift-back) for the large-`t` steps. -/
theorem filtr_homog_single_lift
    (hgen : Ideal.span (Set.range g) = IsLocalRing.maximalIdeal (FRL P))
    (hlead : FiltrLeadDataHomog P d g hgen)
    (hgr : ∀ j', contractExactAt (grlift_phiGr P d g hgen) j')
    (t j : ℕ) (hdeg : j + 2 ≤ t)
    (z : ↥(⋀[FRL P]^(j + 1) (Fin d → FRL P)))
    (hz : koszulContract (koszulContractOfSequence g) j z = 0)
    (hzF : z ∈ filtrPiece P d t (j + 1)) :
    ∃ w : ↥(⋀[FRL P]^((j + 1) + 1) (Fin d → FRL P)),
    ∃ z' : ↥(⋀[FRL P]^(j + 1) (Fin d → FRL P)),
      koszulContract (koszulContractOfSequence g) (j + 1) w + z' = z ∧
      koszulContract (koszulContractOfSequence g) j z' = 0 ∧
      z' ∈ filtrPiece P d (t + 1) (j + 1) := by
  obtain ⟨LT, LT_zero, LT_add, hinter, hker, hhomog, hlift⟩ := hlead
  have hjt1 : j + 1 ≤ t := by omega
  have hLTcyc : koszulContract (grlift_phiGr P d g hgen) j
      (LT t (j + 1) z) = 0 := by
    have h := hinter t j hjt1 z hzF
    rw [hz, LT_zero] at h
    exact h.symm
  obtain ⟨U, hU⟩ := hgr j _ hLTcyc
  obtain ⟨e, he, w, hW⟩ := hhomog t (j + 1) z hzF
  obtain ⟨e', he'⟩ : ∃ e', e = e' + 1 := ⟨t - (j + 2), by omega⟩
  subst he'
  have hUW : koszulContract (grlift_phiGr P d g hgen) (j + 1) U =
      ∑ s, leadOf P (e' + 1) (w s) •
        (extBasisGr P d (j + 1)) s := hU.trans hW
  obtain ⟨U', ⟨w', hw'⟩, hU'⟩ :=
    dgr_homog_project P d g hgen j e' U w hUW
  obtain ⟨x, hx, hxU'⟩ := hlift t ((j + 1) + 1) e' (by omega) w'
  have hxU'U' : LT t ((j + 1) + 1) x = U' := hxU'.trans hw'.symm
  have hinter_x : LT t (j + 1)
        (koszulContract (koszulContractOfSequence g) (j + 1) x) =
      koszulContract (grlift_phiGr P d g hgen) (j + 1)
        (LT t ((j + 1) + 1) x) :=
    hinter t (j + 1) (by omega) x hx
  have hdwF : koszulContract (koszulContractOfSequence g) (j + 1) x ∈
      filtrPiece P d t (j + 1) :=
    filtr_d_preserve P d g hgen t (j + 1) x hx
  refine ⟨x, z - koszulContract (koszulContractOfSequence g) (j + 1) x,
    ?_, ?_, ?_⟩
  · rw [add_sub_cancel]
  · rw [map_sub, hz]
    have h2 : koszulContract (koszulContractOfSequence g) j
        (koszulContract (koszulContractOfSequence g) (j + 1) x) = 0 := by
      have hcomp := congrArg (fun f => f x)
        (koszulContract_comp (koszulContractOfSequence g) j)
      simpa using hcomp
    rw [h2, sub_zero]
  · have hz'F : z - koszulContract (koszulContractOfSequence g) (j + 1) x ∈
        filtrPiece P d t (j + 1) :=
      Submodule.sub_mem _ hzF hdwF
    have hLTsub : LT t (j + 1)
          (z - koszulContract (koszulContractOfSequence g) (j + 1) x) =
        LT t (j + 1) z -
          LT t (j + 1) (koszulContract (koszulContractOfSequence g)
            (j + 1) x) := by
      have h1 := LT_add t (j + 1)
        (z - koszulContract (koszulContractOfSequence g) (j + 1) x)
        (koszulContract (koszulContractOfSequence g) (j + 1) x) hz'F hdwF
      rw [sub_add_cancel] at h1
      rw [h1, add_sub_cancel_right]
    have hinter_x2 : LT t (j + 1)
          (koszulContract (koszulContractOfSequence g) (j + 1) x) =
        LT t (j + 1) z :=
      hinter_x.trans (by rw [hxU'U', hU', hW])
    have h0 : LT t (j + 1)
        (z - koszulContract (koszulContractOfSequence g) (j + 1) x) = 0 := by
      rw [hLTsub, hinter_x2, sub_self]
    exact hker t j _ hz'F h0

end HomogLift

/-! ## §8. Homogeneous single-step for all `t` + pipeline to `GrLiftFiltrationConseq` -/

section HomogConseq

variable {K : Type*} [Field K] {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K))
  [P.IsPrime] (d : ℕ) (g : Fin d → FRL P)

/-- Graded-mul component law at degree 0, in `leadOf` form (matches call-site
syntax). Proved (the `grComp` corollary; `leadOf` is `DirectSum.of`). -/
theorem grMul_component_zero_grComp_leadOf (w : grRegular P)
    (dd : grPiece (FRL P) (IsLocalRing.maximalIdeal (FRL P)) 1) :
    grComp P (w * leadOf P 1 dd) 0 = 0 :=
  grMul_component_zero_grComp P w dd

/-- Diagonal single-step (`t = j + 1`): here the leading term is homogeneous
of degree `0`, while `d_gr` raises degree by one — so extracting the
degree-`0` component of the gr-side primitive shows `LT z = 0`, and kernel
control finishes. Proved. -/
theorem filtr_homog_single_diag
    (hgen : Ideal.span (Set.range g) = IsLocalRing.maximalIdeal (FRL P))
    (hlead : FiltrLeadDataHomog P d g hgen)
    (hgr : ∀ j', contractExactAt (grlift_phiGr P d g hgen) j')
    (j : ℕ) (z : ↥(⋀[FRL P]^(j + 1) (Fin d → FRL P)))
    (hz : koszulContract (koszulContractOfSequence g) j z = 0)
    (hzF : z ∈ filtrPiece P d (j + 1) (j + 1)) :
    ∃ w : ↥(⋀[FRL P]^((j + 1) + 1) (Fin d → FRL P)),
    ∃ z' : ↥(⋀[FRL P]^(j + 1) (Fin d → FRL P)),
      koszulContract (koszulContractOfSequence g) (j + 1) w + z' = z ∧
      koszulContract (koszulContractOfSequence g) j z' = 0 ∧
      z' ∈ filtrPiece P d ((j + 1) + 1) (j + 1) := by
  obtain ⟨LT, LT_zero, LT_add, hinter, hker, hhomog, hlift⟩ := hlead
  obtain ⟨e, he, w, hW⟩ := hhomog (j + 1) (j + 1) z hzF
  have he0 : e = 0 := by omega
  subst he0
  have hLTcyc : koszulContract (grlift_phiGr P d g hgen) j
      (LT (j + 1) (j + 1) z) = 0 := by
    have h := hinter (j + 1) j (le_refl _) z hzF
    rw [hz, LT_zero] at h
    exact h.symm
  obtain ⟨U, hU⟩ := hgr j _ hLTcyc
  have hUW : koszulContract (grlift_phiGr P d g hgen) (j + 1) U =
      ∑ s, leadOf P 0 (w s) • (extBasisGr P d (j + 1)) s := hU.trans hW
  choose q hq using fun s => dgr_basis_homog_one P d g hgen (j + 1) s
  have hUexp : U = ∑ s, (extBasisGr P d ((j + 1) + 1)).repr U s •
      (extBasisGr P d ((j + 1) + 1)) s :=
    ((extBasisGr P d ((j + 1) + 1)).sum_repr U).symm
  rw [hUexp, dgr_sum_expand P d g hgen j _ q hq] at hUW
  have hcoeff : ∀ t, (∑ s, (extBasisGr P d ((j + 1) + 1)).repr U s *
      leadOf P 1 (q s t)) = leadOf P 0 (w t) := by
    intro t
    have h := congrArg
      (fun W => (extBasis (R := grRegular P) d (j + 1)).repr W t) hUW
    simp only [extBasisGr] at h
    simp only [basis_repr_sum_smul d (j + 1)] at h
    exact h
  have hw0 : ∀ t, w t = 0 := by
    intro t
    have hcalc : (∑ s, grComp P
            ((extBasisGr P d ((j + 1) + 1)).repr U s * leadOf P 1 (q s t)) 0) =
            w t := by
      calc (∑ s, grComp P
                ((extBasisGr P d ((j + 1) + 1)).repr U s * leadOf P 1 (q s t)) 0)
          = grComp P (∑ s, (extBasisGr P d ((j + 1) + 1)).repr U s *
              leadOf P 1 (q s t)) 0 := (grComp_sum P _ _ _).symm
        _ = grComp P (leadOf P 0 (w t)) 0 :=
          congrArg (fun y : grRegular P => grComp P y 0) (hcoeff t)
        _ = w t := grComp_leadOf P _ _
    have h0 : (∑ s, grComp P
            ((extBasisGr P d ((j + 1) + 1)).repr U s * leadOf P 1 (q s t)) 0) =
            0 :=
      Finset.sum_eq_zero (fun s _ => grMul_component_zero_grComp_leadOf P _ _)
    exact hcalc.symm.trans h0
  have hLT0 : LT (j + 1) (j + 1) z = 0 := by
    rw [hW]
    simp only [hw0]
    have h0 : leadOf P 0
        (0 : grPiece (FRL P) (IsLocalRing.maximalIdeal (FRL P)) 0) = 0 :=
      map_zero (DirectSum.of _ 0)
    have hz' : ∀ s, leadOf P 0
        (0 : grPiece (FRL P) (IsLocalRing.maximalIdeal (FRL P)) 0) •
        (extBasisGr P d (j + 1)) s = 0 := by
      intro s
      rw [h0, zero_smul]
    refine Finset.sum_eq_zero ?_
    intro s _
    exact hz' s
  refine ⟨0, z, ?_, hz, ?_⟩
  · rw [map_zero, zero_add]
  · exact hker (j + 1) j z hzF hLT0

/-- Below-diagonal single-step (`t ≤ j + 1`): for `t ≤ j` both pieces are `⊤`
(trivial step); at `t = j + 1` the diagonal argument applies. Proved. -/
theorem filtr_homog_single_small
    (hgen : Ideal.span (Set.range g) = IsLocalRing.maximalIdeal (FRL P))
    (hlead : FiltrLeadDataHomog P d g hgen)
    (hgr : ∀ j', contractExactAt (grlift_phiGr P d g hgen) j')
    (t j : ℕ) (hle : t ≤ j + 1)
    (z : ↥(⋀[FRL P]^(j + 1) (Fin d → FRL P)))
    (hz : koszulContract (koszulContractOfSequence g) j z = 0)
    (hzF : z ∈ filtrPiece P d t (j + 1)) :
    ∃ w : ↥(⋀[FRL P]^((j + 1) + 1) (Fin d → FRL P)),
    ∃ z' : ↥(⋀[FRL P]^(j + 1) (Fin d → FRL P)),
      koszulContract (koszulContractOfSequence g) (j + 1) w + z' = z ∧
      koszulContract (koszulContractOfSequence g) j z' = 0 ∧
      z' ∈ filtrPiece P d (t + 1) (j + 1) := by
  by_cases htj : t ≤ j
  · refine ⟨0, z, ?_, hz, ?_⟩
    · rw [map_zero, zero_add]
    · have htop : filtrPiece P d (t + 1) (j + 1) = ⊤ :=
        filtrPiece_eq_top_of_le P d (t + 1) (j + 1) (by omega)
      rw [htop]
      exact Submodule.mem_top
  · have htjj : t = j + 1 := by omega
    subst htjj
    exact filtr_homog_single_diag P d g hgen hlead hgr j z hz hzF

/-- Single-step lift for all `t`: the large-`t` homogeneous lift plus the
below-diagonal case. Proved from the homogeneous data + gr-exactness. -/
theorem filtr_homog_single_all
    (hgen : Ideal.span (Set.range g) = IsLocalRing.maximalIdeal (FRL P))
    (hlead : FiltrLeadDataHomog P d g hgen)
    (hgr : ∀ j', contractExactAt (grlift_phiGr P d g hgen) j')
    (t j : ℕ) (z : ↥(⋀[FRL P]^(j + 1) (Fin d → FRL P)))
    (hz : koszulContract (koszulContractOfSequence g) j z = 0)
    (hzF : z ∈ filtrPiece P d t (j + 1)) :
    ∃ w : ↥(⋀[FRL P]^((j + 1) + 1) (Fin d → FRL P)),
    ∃ z' : ↥(⋀[FRL P]^(j + 1) (Fin d → FRL P)),
      koszulContract (koszulContractOfSequence g) (j + 1) w + z' = z ∧
      koszulContract (koszulContractOfSequence g) j z' = 0 ∧
      z' ∈ filtrPiece P d (t + 1) (j + 1) := by
  by_cases hdeg : j + 2 ≤ t
  · exact filtr_homog_single_lift P d g hgen hlead hgr t j hdeg z hz hzF
  · exact filtr_homog_single_small P d g hgen hlead hgr t j (by omega) z hz hzF

/-- Iteration: every cycle is a boundary plus a cycle arbitrarily deep in
the filtration. Proved; conditional-exact on `[FiltrLeadDataHomog]` +
gr-exactness (same induction as `filtr_iterate`, over the all-`t`
homogeneous single-step). -/
theorem filtr_homog_iterate
    (hgen : Ideal.span (Set.range g) = IsLocalRing.maximalIdeal (FRL P))
    (hlead : FiltrLeadDataHomog P d g hgen)
    (hgr : ∀ j', contractExactAt (grlift_phiGr P d g hgen) j')
    (j N : ℕ) (z : ↥(⋀[FRL P]^(j + 1) (Fin d → FRL P)))
    (hz : koszulContract (koszulContractOfSequence g) j z = 0) :
    ∃ W : ↥(⋀[FRL P]^((j + 1) + 1) (Fin d → FRL P)),
    ∃ zN : ↥(⋀[FRL P]^(j + 1) (Fin d → FRL P)),
      koszulContract (koszulContractOfSequence g) (j + 1) W + zN = z ∧
      koszulContract (koszulContractOfSequence g) j zN = 0 ∧
      zN ∈ filtrPiece P d N (j + 1) := by
  induction N with
  | zero =>
      refine ⟨0, z, ?_, hz, ?_⟩
      · rw [map_zero, zero_add]
      · rw [filtrPiece_eq_top_of_le P d 0 (j + 1) (Nat.zero_le _)]
        exact Submodule.mem_top
  | succ n ih =>
      obtain ⟨Wn, zn, hWn, hzn, hznF⟩ := ih
      obtain ⟨w, z', hw, hz', hz'F⟩ :=
        filtr_homog_single_all P d g hgen hlead hgr n j zn hzn hznF
      refine ⟨Wn + w, z', ?_, hz', hz'F⟩
      rw [map_add]
      have hstep : koszulContract (koszulContractOfSequence g) (j + 1) Wn +
          koszulContract (koszulContractOfSequence g) (j + 1) w + z' =
          koszulContract (koszulContractOfSequence g) (j + 1) Wn + zn := by
        rw [add_assoc, hw]
      rw [hstep]
      exact hWn

set_option maxSynthPendingDepth 4 in -- `grlift_homology` quotient TC depth (as in file 6).
set_option maxHeartbeats 2000000 in -- ~25-tactic homology chase exceeds the default budget.
/-- The homology consequence `𝔪 • H = H` from gr-exactness, via iteration
to one past the Artin–Rees index. Proved from the homogeneous data;
conditional-exact on `[FiltrLeadDataHomog]` (same chase as
`filtr_hconseq_of_lead`, over the homogeneous iterate). -/
theorem filtr_homog_hconseq
    (hgen : Ideal.span (Set.range g) = IsLocalRing.maximalIdeal (FRL P))
    (hlead : FiltrLeadDataHomog P d g hgen)
    (hgr : ∀ j', contractExactAt (grlift_phiGr P d g hgen) j') (j : ℕ) :
    IsLocalRing.maximalIdeal (FRL P) •
        (⊤ : Submodule (FRL P)
          (grlift_homology (koszulContractOfSequence g) j)) = ⊤ := by
  refine le_antisymm Submodule.smul_le_right ?_
  intro h _
  obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective
    (grlift_boundaries (koszulContractOfSequence g) j) h
  change (grlift_boundaries (koszulContractOfSequence g) j).mkQ q ∈
    IsLocalRing.maximalIdeal (FRL P) • (⊤ : Submodule (FRL P)
      (grlift_homology (koszulContractOfSequence g) j))
  obtain ⟨kAR, hkAR⟩ := filtr_ar_index P d g j
  have hexp : (j + 1) + kAR + 1 - (j + 1) = kAR + 1 := by omega
  have hz : koszulContract (koszulContractOfSequence g) j
      (q : ↥(⋀[FRL P]^(j + 1) (Fin d → FRL P))) = 0 :=
    LinearMap.mem_ker.mp q.2
  have hiter := filtr_homog_iterate P d g hgen hlead hgr j ((j + 1) + kAR + 1)
    (q : ↥(⋀[FRL P]^(j + 1) (Fin d → FRL P))) hz
  obtain ⟨W, zN, hW, hzN, hzNF⟩ := hiter
  have hzNmem : zN ∈ IsLocalRing.maximalIdeal (FRL P) ^ (kAR + 1) • ⊤ ⊓
      grlift_cycles (koszulContractOfSequence g) j := by
    constructor
    · rw [filtrPiece_def, hexp] at hzNF
      exact hzNF
    · exact LinearMap.mem_ker.mpr hzN
  rw [hkAR (kAR + 1) (Nat.le_succ _)] at hzNmem
  have hsub : kAR + 1 - kAR = 1 := by omega
  rw [hsub, pow_one] at hzNmem
  have hzNZ : zN ∈ IsLocalRing.maximalIdeal (FRL P) •
      grlift_cycles (koszulContractOfSequence g) j :=
    Submodule.smul_mono le_rfl inf_le_right hzNmem
  have hmap : Submodule.map (grlift_cycles (koszulContractOfSequence g) j).subtype
        (IsLocalRing.maximalIdeal (FRL P) •
          (⊤ : Submodule (FRL P)
            ↥(grlift_cycles (koszulContractOfSequence g) j))) =
        IsLocalRing.maximalIdeal (FRL P) •
          grlift_cycles (koszulContractOfSequence g) j := by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]
  have hzNZ' : (⟨zN, LinearMap.mem_ker.mpr hzN⟩ :
      ↥(grlift_cycles (koszulContractOfSequence g) j)) ∈
      IsLocalRing.maximalIdeal (FRL P) •
        (⊤ : Submodule (FRL P)
          ↥(grlift_cycles (koszulContractOfSequence g) j)) := by
    have hmem : zN ∈ Submodule.map
        (grlift_cycles (koszulContractOfSequence g) j).subtype
        (IsLocalRing.maximalIdeal (FRL P) •
          (⊤ : Submodule (FRL P)
            ↥(grlift_cycles (koszulContractOfSequence g) j))) := by
      rw [hmap]
      exact hzNZ
    obtain ⟨w, hw, hwx⟩ := hmem
    have heq : w = ⟨zN, LinearMap.mem_ker.mpr hzN⟩ := Subtype.ext hwx
    rwa [heq] at hw
  have hle : Submodule.map
        (grlift_boundaries (koszulContractOfSequence g) j).mkQ
        (IsLocalRing.maximalIdeal (FRL P) •
          (⊤ : Submodule (FRL P)
            ↥(grlift_cycles (koszulContractOfSequence g) j))) ≤
        IsLocalRing.maximalIdeal (FRL P) •
          (⊤ : Submodule (FRL P)
            (grlift_homology (koszulContractOfSequence g) j)) :=
    Submodule.map_le_iff_le_comap.mpr
      (Submodule.smul_top_le_comap_smul_top _ _)
  have hfin : (grlift_boundaries (koszulContractOfSequence g) j).mkQ
        (⟨zN, LinearMap.mem_ker.mpr hzN⟩ :
          ↥(grlift_cycles (koszulContractOfSequence g) j)) ∈
      IsLocalRing.maximalIdeal (FRL P) •
        (⊤ : Submodule (FRL P)
          (grlift_homology (koszulContractOfSequence g) j)) :=
    hle (Submodule.mem_map_of_mem hzNZ')
  have hdW : koszulContract (koszulContractOfSequence g) j
      (koszulContract (koszulContractOfSequence g) (j + 1) W) = 0 := by
    have hcomp := congrArg (fun f => f W)
      (koszulContract_comp (koszulContractOfSequence g) j)
    simpa using hcomp
  have hqeq : (grlift_boundaries (koszulContractOfSequence g) j).mkQ q =
      (grlift_boundaries (koszulContractOfSequence g) j).mkQ
        (⟨zN, LinearMap.mem_ker.mpr hzN⟩ :
          ↥(grlift_cycles (koszulContractOfSequence g) j)) := by
    have hsplit : q =
        (⟨koszulContract (koszulContractOfSequence g) (j + 1) W,
            LinearMap.mem_ker.mpr hdW⟩ :
          ↥(grlift_cycles (koszulContractOfSequence g) j)) +
        ⟨zN, LinearMap.mem_ker.mpr hzN⟩ := by
      apply Subtype.ext
      change (q : ↥(⋀[FRL P]^(j + 1) (Fin d → FRL P))) =
        koszulContract (koszulContractOfSequence g) (j + 1) W + zN
      exact hW.symm
    rw [hsplit, map_add]
    have hbdry : (grlift_boundaries (koszulContractOfSequence g) j).mkQ
          (⟨koszulContract (koszulContractOfSequence g) (j + 1) W,
            LinearMap.mem_ker.mpr hdW⟩ :
            ↥(grlift_cycles (koszulContractOfSequence g) j)) = 0 := by
      change Submodule.Quotient.mk
          (⟨koszulContract (koszulContractOfSequence g) (j + 1) W,
            LinearMap.mem_ker.mpr hdW⟩ :
            ↥(grlift_cycles (koszulContractOfSequence g) j)) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      rw [Submodule.mem_comap]
      exact ⟨W, rfl⟩
    simp only [hbdry, zero_add]
  rw [hqeq]
  exact hfin

set_option maxSynthPendingDepth 4 in -- `grlift_homology` quotient TC depth (as in file 6).
/-- File-6 residual discharged modulo the homogeneous leading-term data:
`GrLiftFiltrationConseq` from `[FiltrLeadDataHomog]`. Conditional-exact. -/
theorem filtr_homog_grlift_conseq
    (hgen : Ideal.span (Set.range g) = IsLocalRing.maximalIdeal (FRL P))
    (hlead : FiltrLeadDataHomog P d g hgen) :
    GrLiftFiltrationConseq P d g hgen := by
  intro hgr j
  exact filtr_homog_hconseq P d g hgen hlead hgr j

set_option maxSynthPendingDepth 4 in -- `grlift_homology` quotient TC depth (as in file 6).
/-- The file-6 filtration consequence, unconditionally: the homogeneous
leading-term data (`filtrLeadDataHomog`) feeds the homogeneous pipeline.
unconditional (modulo the explicit spanning hypothesis `hgen`). -/
theorem filtr_grlift_conseq_unconditional
    (hgen : Ideal.span (Set.range g) = IsLocalRing.maximalIdeal (FRL P)) :
    GrLiftFiltrationConseq P d g hgen :=
  filtr_homog_grlift_conseq P d g hgen (filtrLeadDataHomog P d g hgen)

#print axioms filtr_homog_single_diag
#print axioms filtr_homog_single_small
#print axioms filtr_homog_single_all
#print axioms filtr_homog_iterate
#print axioms filtr_homog_hconseq
#print axioms filtr_homog_grlift_conseq
#print axioms filtr_grlift_conseq_unconditional

end HomogConseq

end LeadingTermMaps
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
