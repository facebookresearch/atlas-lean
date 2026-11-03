/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.AssociatedGradedRing
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.LengthFramework
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.NewtonDifferences
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedSurjection
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.GradedSurjectionInjective

/-!
# Single-drop regularity: nonzero kernel drops the gr growth degree (R3')

Sub-plan R3' of M4c-ii (the Hilbert–Samuel bypass): if
`ker (polySurjResidue P d g hgen) ≠ ⊥`, the associated-graded Hilbert
function has growth degree `≤ d - 2`
(`singleDrop_deg_le_of_ker_ne_bot`), in the exact shape the §6
`hsAssemble_ker_eq_bot` assembly consumes (see the
`singleDrop_ker_eq_bot` corollary). This re-scoped R3' replaces the
abandoned single-step-`Hq`/`hses` abstraction, which machine-checked as inconsistent (shift-`t` vs
shift-`1`): no `Hq`-about-`gr` hypotheses appear
anywhere here — the only quotient Hilbert function is the concrete
`P ⧸ yP` one (`singleDrop_quotHilbert`).

## Sections

* (§1) `ker ∩ P₀ = 0` from M4a (`hsAssemble_coeffHom_injective`), so every
  nonzero homogeneous `y ∈ ker` has degree `t ≥ 1`
  (`singleDrop_homogeneous_mem_ker_pos`).
* (§2) `×y` is injective on `P` (`singleDrop_mul_injective`): `P` is a
  domain (an `MvPolynomial` over a field).
* (§3) The graded SES `0 → P_{n-t} → P_n → (P/yP)_n → 0`
  (`singleDrop_mulMap`, `singleDrop_mulMap_injective`) and its length
  equation (`singleDrop_hSES`) via `finLength_add_of_submodule`.
* (§4) `P ⧸ yP ↠ gr` (`singleDrop_quotSurj`, surjective) and the abstract
  same-ring comparison lemma (`singleDrop_finLength_le_of_surjective`).
* (§5) Newton drop: the difference function has growth `≤ d - 2`
  (`singleDrop_isPolyGrowth_sub`), via the difference polynomial
  (`singleDrop_natDegree_comp_add_sub_le`), telescoping
  (`singleDrop_telescope_add`), and backward shift
  (`singleDrop_isPolyGrowth_of_comp_add`).
* (§6) Exactness: `deg H_{P/yP} = d - 2` (`singleDrop_quot_exact`), via
  the abstract nonvanishing transfer (`singleDrop_not_vanishing_of_sub`)
  and the concrete domain nonvanishing
  (`singleDrop_domain_not_vanishing`).
* (§7) Master assembly: `singleDrop_deg_le_of_step` (per-`y`),
  `singleDrop_deg_le_of_ker_ne_bot` (the §6-consumption shape), and
  `singleDrop_ker_eq_bot` (the §6-style contrapositive).
* (§8) Residue-field scalars on `grPiece`
  (`singleDrop_grPiece_smul_mk`, `singleDrop_grPiece_mk_smul`).
* (§9) Piece-level surjection `P_n ↠ gr_n`
  (`singleDrop_pieceMap_surjective`).
* (§9b) Quotient-piece comparison over a local ring: `hcomp` closed
  (`singleDrop_hcomp_concrete`).
* (§10) Polynomial domination: `hdom` closed (`singleDrop_hdom`).
* (§11) Discharged masters conditional only on `hag_gr`
  (`singleDrop_deg_le_of_ker_ne_bot_of_hag`,
  `singleDrop_ker_eq_bot_of_hag`).

## References

Mathlib (`lean-toolchain` pins `v4.34.0`), all read-only:
* `Algebra/MvPolynomial/Degrees.lean`: `totalDegree_eq_zero_iff_eq_C`.
* `Algebra/Polynomial/Degree/Defs.lean`: `natDegree_add_le`,
  `natDegree_sub_le`, `coeff_natDegree`.
* `Algebra/Polynomial/Degree/Lemmas.lean`: `natDegree_comp`,
  `leadingCoeff_comp`.
* `Algebra/Polynomial/Degree/Operations.lean`: `natDegree_X_add_C`,
  `natDegree_X_sub_C`.
* `Algebra/Polynomial/Monic.lean`: `monic_X_add_C`.
* `Algebra/Polynomial/Eval/Defs.lean`: `eval_comp`.
* `RingTheory/MvPolynomial/Homogeneous.lean`:
  `totalDegree_zero_iff_isHomogeneous`, `IsHomogeneous.mul`,
  `homogeneousSubmodule`, `mem_homogeneousSubmodule`,
  `homogeneousSubmodule_fg`.
* `RingTheory/HopkinsLevitzki.lean`: `IsArtinianRing.tfae` (finite
  modules over a field have finite length).
* `RingTheory/Length.lean`: `LinearEquiv.length_eq`.
* `Logic/Function/Iterate.lean`: `Function.iterate_add_apply`.

Project (read-only):
* `Regularity/Koszul/AssociatedGradedRing.lean` (step A4(i): `grPiece`,
  `associatedGraded`, M4a via `hsAssemble_coeffHom_injective`).
* `Regularity/Koszul/GradedSurjection.lean` (M4b: `polySurj`, `polySurjResidue`,
  `polySurj_surjective`).
* `Regularity/Multiplicity/NewtonDifferences.lean` (`seqDiff`, `IsPolyGrowth`, `evalFun`,
  `chooseFun`, shift commutation, top-coefficient extraction).
* `Regularity/Koszul/LengthFramework.lean` (`finLength`, SES additivity,
  `length_quot_le`).
* `Regularity/Multiplicity/GradedSurjectionInjective.lean` (§11
  `hsAssemble_exists_homogeneous_mem_ker`,
  `hsAssemble_polySurj_of_homogeneous`, §13 domain Hilbert function,
  `hsAssemble_domainHilbert_eq_choose` and `hsAssemble_hF`, §1
  `growth_exact_of_not_vanishing`, §9 `isPolyGrowth_comp_add`).

## Status

* §§1–6, §§8–10: unconditional.
* §7 masters: conditional-explicit on `hstep` (per-`y` SES equation +
  pointwise comparison), `hag_gr` (eventual-polynomiality of `H_gr`),
  `hdom` (polynomial dominance), and `hdimEq` (corollary only;
  exact-degree reading for `H_gr`, sibling R2' content). FiniteDimDischarge
  status: the SES half of `hstep` is proved as `singleDrop_hSES` (§3);
  the comparison half (`hcomp`) is closed as `singleDrop_hcomp_concrete`
  (§9b); `hdom` is closed as `singleDrop_hdom` (§10); `hag_gr` is
  proved as `hsQuotHilbert_hag_gr`
  (`Regularity/Multiplicity/HilbertSerre.lean`, unconditional).
* §11 discharged masters: conditional-explicit on `hag_gr` only
  (`singleDrop_deg_le_of_ker_ne_bot_of_hag`; plus `hdimEq` for
  `singleDrop_ker_eq_bot_of_hag`).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace SingleDropRegularity

open scoped Polynomial

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.NewtonDifferences
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.LengthFramework
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjection
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AssociatedGradedRing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjectionInjective

/-! ## §1. `ker ∩ P₀ = 0`, so homogeneous kernel elements have degree `≥ 1` -/

section KerCapDegZero

variable {R : Type*} [CommRing R] (I : Ideal R) (d : ℕ) (g : Fin d → R)
  (hgen : Ideal.span (Set.range g) = I)

/-- Constants in the kernel are zero: `polySurj` sends `C a` through the
injective coefficient map (`hsAssemble_coeffHom_injective`, whose proof is
M4a `grPiece_zero_equiv_quotient`).
-/
theorem singleDrop_C_mem_ker_iff (a : R ⧸ I) :
    MvPolynomial.C a ∈ RingHom.ker (polySurj R I d g hgen) ↔ a = 0 := by
  constructor
  · intro h
    have h0 : polySurj R I d g hgen (MvPolynomial.C a) = 0 :=
      RingHom.mem_ker.mp h
    rw [polySurj_C] at h0
    apply hsAssemble_coeffHom_injective I
    rw [h0, map_zero]
  · intro h
    subst h
    exact RingHom.mem_ker.mpr (by simp)

/-- A nonzero homogeneous kernel element has positive degree: degree `0`
would make it a constant, contradicting `ker ∩ P₀ = 0`.
-/
theorem singleDrop_homogeneous_mem_ker_pos
    {y : MvPolynomial (Fin d) (R ⧸ I)} {t : ℕ}
    (hym : y ∈ RingHom.ker (polySurj R I d g hgen)) (hyne : y ≠ 0)
    (hyhom : y.IsHomogeneous t) : 1 ≤ t := by
  by_contra hcon
  have ht0 : t = 0 := by omega
  subst ht0
  have hdeg : y.totalDegree = 0 :=
    Iff.mpr (MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin d)) hyhom
  have hC : y = MvPolynomial.C (y.coeff 0) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdeg
  have hc : y.coeff 0 = 0 :=
    (singleDrop_C_mem_ker_iff I d g hgen _).mp (by rwa [hC] at hym)
  exact hyne (by rw [hC, hc, map_zero])

end KerCapDegZero

/-! ## §2. `×y` is injective on `P` (a domain) -/

section MulInjective

variable {κ : Type*} [Field κ] {σ : Type*}

/-- Multiplication by a nonzero `y` is injective on `P`: an
`MvPolynomial` over a field has no zero divisors.
-/
theorem singleDrop_mul_injective (y : MvPolynomial σ κ) (hyne : y ≠ 0) :
    Function.Injective (y * ·) :=
  mul_right_injective₀ hyne

end MulInjective

/-! ## §3. The graded SES and its length equation -/

section GradedSES

variable (κ : Type*) [Field κ] (d t : ℕ) (y : MvPolynomial (Fin d) κ)
  (hyhom : y.IsHomogeneous t)

/-- Multiplication by the homogeneous `y` as a graded map
`P_{n-t} →ₗ P_n` (needs `t ≤ n` for the degree equation).
-/
noncomputable def singleDrop_mulMap (n : ℕ) (h : t ≤ n) :
    ↥(MvPolynomial.homogeneousSubmodule (Fin d) κ (n - t)) →ₗ[κ]
      ↥(MvPolynomial.homogeneousSubmodule (Fin d) κ n) where
  toFun p := ⟨y * p.val, by
    rw [MvPolynomial.mem_homogeneousSubmodule]
    have hp : p.val.IsHomogeneous (n - t) := p.property
    have hmul := hyhom.mul hp
    have hn : t + (n - t) = n := by omega
    rwa [hn] at hmul⟩
  map_add' a b := Subtype.ext (mul_add _ _ _)
  map_smul' c p := Subtype.ext (Algebra.mul_smul_comm _ _ _)

/-- The graded mul-by-`y` map is injective (from §2 injectivity on `P`).
-/
theorem singleDrop_mulMap_injective (hyne : y ≠ 0) (n : ℕ) (h : t ≤ n) :
    Function.Injective (singleDrop_mulMap κ d t y hyhom n h) := by
  intro a b hab
  have hval : y * a.val = y * b.val := congrArg Subtype.val hab
  have hba : a.val = b.val := mul_left_cancel₀ hyne hval
  exact Subtype.ext hba

/-- The degree-`n` homogeneous piece is finite over `κ` (the §13
finiteness pattern: `homogeneousSubmodule_fg` through `fg_top`).
-/
theorem singleDrop_finite (n : ℕ) :
    Module.Finite κ ↥(MvPolynomial.homogeneousSubmodule (Fin d) κ n) :=
  Module.finite_def.mpr ((Submodule.fg_top _).mpr
    (MvPolynomial.homogeneousSubmodule_fg (Fin d) κ n))

/-- The degree-`n` homogeneous piece has finite length over `κ`: a field
is Artinian, so finite implies finite length (Hopkins–Levitzki TFAE).
-/
theorem singleDrop_isFiniteLength (n : ℕ) :
    IsFiniteLength κ ↥(MvPolynomial.homogeneousSubmodule (Fin d) κ n) := by
  have hfin := singleDrop_finite κ d n
  have hiff : Module.Finite κ
      ↥(MvPolynomial.homogeneousSubmodule (Fin d) κ n) ↔
      IsFiniteLength κ ↥(MvPolynomial.homogeneousSubmodule (Fin d) κ n) :=
    List.TFAE.out
      (IsArtinianRing.tfae κ ↥(MvPolynomial.homogeneousSubmodule (Fin d) κ n))
      1 4
  exact hiff.mp hfin

/-- The `P ⧸ yP` Hilbert function: `κ`-lengths of the degree-`n`
quotient pieces `(P_n ⧸ y·P_{n-t})` (junk domain values below `t`,
which eventual statements ignore).
-/
noncomputable def singleDrop_quotHilbert (n : ℕ) : ℕ :=
  if h : t ≤ n then
    finLength κ (↥(MvPolynomial.homogeneousSubmodule (Fin d) κ n) ⧸
      LinearMap.range (singleDrop_mulMap κ d t y hyhom n h))
  else hsAssemble_domainHilbert κ d n

/-- The graded SES length equation: for `n ≥ t`,
`H_{P/yP}(n) + H_P(n-t) = H_P(n)`.
-/
theorem singleDrop_hSES (hyne : y ≠ 0) (n : ℕ) (h : t ≤ n) :
    singleDrop_quotHilbert κ d t y hyhom n
        + hsAssemble_domainHilbert κ d (n - t)
      = hsAssemble_domainHilbert κ d n := by
  have hM := singleDrop_isFiniteLength κ d n
  have hadd := finLength_add_of_submodule hM
    (LinearMap.range (singleDrop_mulMap κ d t y hyhom n h))
  have hcongr : finLength κ
        ↥(LinearMap.range (singleDrop_mulMap κ d t y hyhom n h))
      = finLength κ ↥(MvPolynomial.homogeneousSubmodule (Fin d) κ (n - t)) := by
    have e : ↥(MvPolynomial.homogeneousSubmodule (Fin d) κ (n - t)) ≃ₗ[κ]
        ↥(LinearMap.range (singleDrop_mulMap κ d t y hyhom n h)) :=
      LinearEquiv.ofInjective (singleDrop_mulMap κ d t y hyhom n h)
        (singleDrop_mulMap_injective κ d t y hyhom hyne n h)
    have heq : Module.length κ
          ↥(MvPolynomial.homogeneousSubmodule (Fin d) κ (n - t))
        = Module.length κ
          ↥(LinearMap.range (singleDrop_mulMap κ d t y hyhom n h)) :=
      e.length_eq
    unfold finLength
    rw [heq]
  unfold singleDrop_quotHilbert hsAssemble_domainHilbert
  rw [dite_eq_left h]
  omega

/-- The SES equation in `ℚ`-cast form (the shape §5 consumes).
-/
theorem singleDrop_quot_cast_sub (hyne : y ≠ 0) (n : ℕ) (hn : t ≤ n) :
    ((singleDrop_quotHilbert κ d t y hyhom n : ℕ) : ℚ)
      = ((hsAssemble_domainHilbert κ d n : ℕ) : ℚ)
        - ((hsAssemble_domainHilbert κ d (n - t) : ℕ) : ℚ) := by
  have hSES := singleDrop_hSES κ d t y hyhom hyne n hn
  have hcast : ((singleDrop_quotHilbert κ d t y hyhom n : ℕ) : ℚ)
        + ((hsAssemble_domainHilbert κ d (n - t) : ℕ) : ℚ)
      = ((hsAssemble_domainHilbert κ d n : ℕ) : ℚ) := by
    have h2 := congrArg (fun m : ℕ => (m : ℚ)) hSES
    rwa [Nat.cast_add] at h2
  calc ((singleDrop_quotHilbert κ d t y hyhom n : ℕ) : ℚ)
        = ((singleDrop_quotHilbert κ d t y hyhom n : ℕ) : ℚ)
          + ((hsAssemble_domainHilbert κ d (n - t) : ℕ) : ℚ)
          - ((hsAssemble_domainHilbert κ d (n - t) : ℕ) : ℚ) := by abel
      _ = ((hsAssemble_domainHilbert κ d n : ℕ) : ℚ)
          - ((hsAssemble_domainHilbert κ d (n - t) : ℕ) : ℚ) := by rw [hcast]

end GradedSES

/-! ## §4. `P ⧸ yP ↠ gr` and the abstract comparison lemma -/

section QuotSurj

variable {R : Type*} [CommRing R] (I : Ideal R) (d : ℕ) (g : Fin d → R)
  (hgen : Ideal.span (Set.range g) = I)

/-- Since `y ∈ ker polySurj`, the surjection factors through `P ⧸ yP`.
-/
noncomputable def singleDrop_quotSurj (y : MvPolynomial (Fin d) (R ⧸ I))
    (hym : y ∈ RingHom.ker (polySurj R I d g hgen)) :
    MvPolynomial (Fin d) (R ⧸ I) ⧸ Ideal.span ({y} : Set _) →+*
      associatedGraded R I :=
  Ideal.Quotient.lift _ (polySurj R I d g hgen) (fun a ha => by
    have hle : Ideal.span ({y} : Set (MvPolynomial (Fin d) (R ⧸ I)))
        ≤ RingHom.ker (polySurj R I d g hgen) := by
      apply Submodule.span_le.mpr
      intro a ha
      simp only [Set.mem_singleton_iff] at ha
      rw [ha]
      exact hym
    exact RingHom.mem_ker.mp (hle ha))

/-- Finite length drops along surjective linear maps (same-ring form of
`length_quot_le` through the first isomorphism theorem).
-/
theorem singleDrop_finLength_le_of_surjective {A M N : Type*} [Ring A]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (f : M →ₗ[A] N) (hf : Function.Surjective f)
    (hM : IsFiniteLength A M) :
    finLength A N ≤ finLength A M := by
  have e := LinearMap.quotKerEquivOfSurjective f hf
  have hle : Module.length A N ≤ Module.length A M := by
    rw [← e.length_eq]
    exact length_quot_le (LinearMap.ker f)
  have hN : IsFiniteLength A N := hM.of_surjective hf
  have cN := coe_finLength hN
  have cM := coe_finLength hM
  rw [← cN, ← cM] at hle
  exact Nat.cast_le.mp hle

end QuotSurj

/-! ## §5. Newton drop: the difference function has growth `≤ d - 2` -/

section NewtonDrop

/-- Polynomial growth is stable under addition (interpolating polynomial
`P + Q`).
-/
theorem singleDrop_isPolyGrowth_add {F G : ℕ → ℚ} {e : ℕ}
    (hF : IsPolyGrowth F e) (hG : IsPolyGrowth G e) :
    IsPolyGrowth (fun n => F n + G n) e := by
  obtain ⟨P, hdP, hP⟩ := hF
  obtain ⟨Q, hdQ, hQ⟩ := hG
  refine ⟨P + Q, ?_, ?_⟩
  · calc (P + Q).natDegree
        ≤ max P.natDegree Q.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ e := max_le hdP hdQ
  · filter_upwards [hP, hQ] with n hn1 hn2
    simp only [evalFun] at hn1 hn2 ⊢
    rw [hn1, hn2, Polynomial.eval_add]

/-- Polynomial growth is stable under finite sums.
-/
theorem singleDrop_isPolyGrowth_sum {ι : Type*} (s : Finset ι)
    {F : ι → ℕ → ℚ} {e : ℕ} (h : ∀ i ∈ s, IsPolyGrowth (F i) e) :
    IsPolyGrowth (fun n => ∑ i ∈ s, F i n) e := by
  classical
  revert h
  induction s using Finset.induction with
  | empty =>
    intro h
    refine ⟨0, by simp [Polynomial.natDegree_zero], ?_⟩
    have hempty : (fun n => ∑ i ∈ (∅ : Finset ι), F i n) = fun _ => 0 := by
      funext n
      simp
    rw [hempty]
    exact Filter.Eventually.of_forall (fun n => by simp [evalFun])
  | @insert a s has ih =>
    intro h
    have hadd := singleDrop_isPolyGrowth_add (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))
    have heq : (fun n => ∑ i ∈ insert a s, F i n)
        = (fun n => F a n + ∑ i ∈ s, F i n) := by
      funext n
      rw [Finset.sum_insert has]
    rwa [heq]

/-- The difference polynomial drops the degree: `P(X+1) - P(X)` has
degree `< deg P` (leading coefficients cancel), hence `≤ d - 2` when
`deg P ≤ d - 1`.
-/
theorem singleDrop_natDegree_comp_add_sub_le (P : ℚ[X]) (d : ℕ)
    (hP : P.natDegree ≤ d - 1) :
    (P.comp (Polynomial.X + Polynomial.C 1) - P).natDegree ≤ d - 2 := by
  have hcomp : (P.comp (Polynomial.X + Polynomial.C 1)).natDegree
      = P.natDegree := by
    rw [Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, Nat.mul_one]
  have hle : (P.comp (Polynomial.X + Polynomial.C 1) - P).natDegree
      ≤ P.natDegree := by
    calc (P.comp (Polynomial.X + Polynomial.C 1) - P).natDegree
        ≤ max (P.comp (Polynomial.X + Polynomial.C 1)).natDegree P.natDegree :=
          Polynomial.natDegree_sub_le _ _
      _ = P.natDegree := by rw [hcomp, max_self]
  rcases eq_or_ne P 0 with rfl | _
  · rw [Polynomial.natDegree_zero] at hle
    omega
  · by_cases he : P.natDegree = 0
    · rw [he] at hle
      omega
    · have hlt : (P.comp (Polynomial.X + Polynomial.C 1) - P).natDegree
          < P.natDegree := by
        have hne' : (P.comp (Polynomial.X + Polynomial.C 1) - P).natDegree
            ≠ P.natDegree := by
          intro hcon
          have hcoeff : (P.comp (Polynomial.X + Polynomial.C 1)
              - P).coeff P.natDegree = 0 := by
            have hq : (Polynomial.X + Polynomial.C (1 : ℚ)).natDegree ≠ 0 := by
              rw [Polynomial.natDegree_X_add_C]
              exact one_ne_zero
            have h1 : (P.comp (Polynomial.X + Polynomial.C 1)).coeff
                P.natDegree = P.leadingCoeff := by
              have h2 : P.natDegree
                  = (P.comp (Polynomial.X + Polynomial.C 1)).natDegree :=
                hcomp.symm
              rw [h2, Polynomial.coeff_natDegree]
              have hlc1 : (Polynomial.X + Polynomial.C (1 : ℚ)).leadingCoeff
                  = 1 :=
                Polynomial.monic_X_add_C 1
              rw [Polynomial.leadingCoeff_comp hq, hlc1, one_pow, mul_one]
            rw [Polynomial.coeff_sub, h1]
            rw [Polynomial.coeff_natDegree, sub_self]
          by_cases hD0 : P.comp (Polynomial.X + Polynomial.C 1) - P = 0
          · rw [hD0, Polynomial.natDegree_zero] at hcon
            omega
          · have hlc : (P.comp (Polynomial.X + Polynomial.C 1)
                - P).coeff
                (P.comp (Polynomial.X + Polynomial.C 1) - P).natDegree ≠ 0 := by
              rw [Polynomial.coeff_natDegree]
              exact Polynomial.leadingCoeff_ne_zero.mpr hD0
            rw [hcon] at hlc
            exact hlc hcoeff
        omega
      omega

/-- First differences drop polynomial growth by one: `ΔF` agrees with
the difference polynomial eventually.
-/
theorem singleDrop_isPolyGrowth_seqDiff_one {F : ℕ → ℚ} {d : ℕ}
    (hF : IsPolyGrowth F (d - 1)) :
    IsPolyGrowth (seqDiff 1 F) (d - 2) := by
  obtain ⟨P, hdP, hP⟩ := hF
  refine ⟨P.comp (Polynomial.X + Polynomial.C 1) - P,
    singleDrop_natDegree_comp_add_sub_le P d hdP, ?_⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hP
  refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
  have e1 : F (n + 1) = P.eval ((n + 1 : ℕ) : ℚ) := hN (n + 1) (by omega)
  have e0 : F n = P.eval (n : ℚ) := hN n hn
  have eD : (P.comp (Polynomial.X + Polynomial.C 1) - P).eval (n : ℚ)
      = P.eval ((n + 1 : ℕ) : ℚ) - P.eval (n : ℚ) := by
    rw [Polynomial.eval_sub, Polynomial.eval_comp]
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
      Nat.cast_add, Nat.cast_one]
  rw [seqDiff_one_apply, e1, e0]
  simp only [evalFun]
  rw [← eD]

/-- Shifted telescoping: `S(m+t) - S(m)` is the sum of `t` consecutive
first differences.
-/
theorem singleDrop_telescope_add (S : ℕ → ℚ) (m t : ℕ) :
    S (m + t) - S m = ∑ j ∈ Finset.range t, seqDiff 1 S (m + j) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ, ← ih, seqDiff_one_apply]
    have hmt : m + (t + 1) = m + t + 1 := by omega
    rw [hmt]
    abel

/-- Polynomial growth is stable under backward shift (interpolating
polynomial `Q.comp (X - C t)`).
-/
theorem singleDrop_isPolyGrowth_of_comp_add {G : ℕ → ℚ} {e t : ℕ}
    (h : IsPolyGrowth (fun n => G (n + t)) e) : IsPolyGrowth G e := by
  obtain ⟨Q, hdQ, hQ⟩ := h
  refine ⟨Q.comp (Polynomial.X - Polynomial.C (t : ℚ)), ?_, ?_⟩
  · calc (Q.comp (Polynomial.X - Polynomial.C (t : ℚ))).natDegree
        = Q.natDegree * (Polynomial.X - Polynomial.C (t : ℚ)).natDegree :=
          Polynomial.natDegree_comp
      _ = Q.natDegree := by
          rw [Polynomial.natDegree_X_sub_C, Nat.mul_one]
      _ ≤ e := hdQ
  · obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hQ
    refine Filter.eventually_atTop.mpr ⟨N + t, fun n hn => ?_⟩
    have htn : t ≤ n := by omega
    have hNt : N ≤ n - t := by omega
    have e1 : G (n - t + t) = Q.eval ((n - t : ℕ) : ℚ) := hN (n - t) hNt
    have e2 : n - t + t = n := by omega
    have eD : (Q.comp (Polynomial.X - Polynomial.C (t : ℚ))).eval (n : ℚ)
        = Q.eval ((n - t : ℕ) : ℚ) := by
      rw [Polynomial.eval_comp]
      congr 1
      simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      rw [Nat.cast_sub htn]
    have hshift : G n = G (n - t + t) := by rw [e2]
    rw [hshift, e1]
    simp only [evalFun]
    rw [← eD]

/-- The Newton drop: if `G(n) = F(n) - F(n-t)` for `n ≥ t` with `t ≥ 1`
and `F` has growth `≤ d - 1`, then `G` has growth `≤ d - 2`. (The upper
bound holds for `t = 0` too; `t ≥ 1` is needed only for exactness in
§6, and is kept here for a uniform per-`y` interface.)
-/
theorem singleDrop_isPolyGrowth_sub {F G : ℕ → ℚ} (d t : ℕ) (_ht : 1 ≤ t)
    (hF : IsPolyGrowth F (d - 1))
    (hG : ∀ n, t ≤ n → G n = F n - F (n - t)) :
    IsPolyGrowth G (d - 2) := by
  have hΔ : IsPolyGrowth (seqDiff 1 F) (d - 2) :=
    singleDrop_isPolyGrowth_seqDiff_one hF
  have hsum : IsPolyGrowth
      (fun n => ∑ j ∈ Finset.range t, seqDiff 1 F (n + j)) (d - 2) :=
    singleDrop_isPolyGrowth_sum _ (fun j _ => isPolyGrowth_comp_add hΔ j)
  have heq : (fun n => G (n + t))
      = (fun n => ∑ j ∈ Finset.range t, seqDiff 1 F (n + j)) := by
    funext n
    have hGn : G (n + t) = F (n + t) - F (n + t - t) := hG (n + t) (by omega)
    have htt : n + t - t = n := by omega
    have htel := singleDrop_telescope_add F n t
    rw [htt] at hGn
    rw [hGn]
    exact htel
  rw [← heq] at hsum
  exact singleDrop_isPolyGrowth_of_comp_add hsum

end NewtonDrop

/-! ## §6. Exactness: `deg H_{P/yP} = d - 2` -/

section Exactness

/-- Iterated differences distribute over subtraction.
-/
theorem singleDrop_seqDiff_sub (k : ℕ) (F G : ℕ → ℚ) :
    seqDiff k (F - G) = seqDiff k F - seqDiff k G := by
  induction k with
  | zero => simp [seqDiff_zero]
  | succ k ih =>
    simp only [seqDiff_succ]
    rw [ih]
    funext n
    change ((seqDiff k F - seqDiff k G) (n + 1) - (seqDiff k F - seqDiff k G) n)
      = ((seqDiff k F (n + 1) - seqDiff k F n)
        - (seqDiff k G (n + 1) - seqDiff k G n))
    simp only [Pi.sub_apply]
    abel

/-- Iterated differences split over addition of iteration counts.
-/
theorem singleDrop_seqDiff_add (a b : ℕ) (F : ℕ → ℚ) :
    seqDiff (a + b) F = seqDiff a (seqDiff b F) := by
  unfold seqDiff
  rw [Function.iterate_add_apply]

/-- Eventual equality is stable under forward shift of the index.
-/
theorem singleDrop_eventuallyEq_comp_add {F G : ℕ → ℚ} {N : ℕ}
    (h : F =ᶠ[Filter.atTop] G) :
    (fun n => F (n + N)) =ᶠ[Filter.atTop] (fun n => G (n + N)) := by
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp h
  exact Filter.eventually_atTop.mpr ⟨M, fun n hn => hM (n + N) (by omega)⟩

/-- Eventual agreement with a nonzero constant rules out eventual
vanishing.
-/
theorem singleDrop_not_eventuallyEq_zero_of_const {F : ℕ → ℚ} {c : ℚ}
    (h : F =ᶠ[Filter.atTop] fun _ => c) (hc : c ≠ 0) :
    ¬ F =ᶠ[Filter.atTop] 0 := by
  intro h0
  have h00 : (fun _ : ℕ => c) =ᶠ[Filter.atTop] (0 : ℕ → ℚ) :=
    h.symm.trans h0
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h00
  have hNN := hN N le_rfl
  simp only [Pi.zero_apply] at hNN
  exact hc hNN

/-- Eventual equality is stable under finite sums.
-/
theorem singleDrop_eventuallyEq_finset_sum {ι : Type*} (s : Finset ι)
    {F G : ι → ℕ → ℚ} (h : ∀ i ∈ s, F i =ᶠ[Filter.atTop] G i) :
    (fun n => ∑ i ∈ s, F i n) =ᶠ[Filter.atTop]
      (fun n => ∑ i ∈ s, G i n) := by
  classical
  revert h
  induction s using Finset.induction with
  | empty =>
    intro h
    exact Filter.Eventually.of_forall (fun _ => by simp)
  | @insert a s has ih =>
    intro h
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have eF : (fun n => ∑ i ∈ insert a s, F i n)
        = (fun n => F a n + ∑ i ∈ s, F i n) := by
      funext n
      rw [Finset.sum_insert has]
    have eG : (fun n => ∑ i ∈ insert a s, G i n)
        = (fun n => G a n + ∑ i ∈ s, G i n) := by
      funext n
      rw [Finset.sum_insert has]
    rw [eF, eG]
    filter_upwards [h1, h2] with n hn1 hn2
    rw [hn1, hn2]

/-- Abstract nonvanishing transfer: if `G(n) = F(n) - F(n-t)` uniformly
with `t ≥ 1` and the `(d-1)`-st difference of `F` does not vanish, then
neither does the `(d-2)`-nd difference of `G` (the `t ≥ 1`
nonvanishing: `t • K ≠ 0`).
-/
theorem singleDrop_not_vanishing_of_sub {F G : ℕ → ℚ} (d t : ℕ) (hd : 2 ≤ d)
    (ht : 1 ≤ t) (hF : IsPolyGrowth F (d - 1))
    (hG : ∀ n, G n = F n - F (n - t))
    (hne : ¬ seqDiff (d - 1) F =ᶠ[Filter.atTop] 0) :
    ¬ seqDiff (d - 2) G =ᶠ[Filter.atTop] 0 := by
  obtain ⟨c, hc⟩ := exists_topCoeff_of_isPolyGrowth hF
  have hcne : (Nat.factorial (d - 1) : ℚ) * c ≠ 0 := by
    intro hzero
    apply hne
    have hrewrite : (fun _ : ℕ => (Nat.factorial (d - 1) : ℚ) * c)
        = (0 : ℕ → ℚ) := by
      funext n
      simp only [hzero, Pi.zero_apply]
    rwa [hrewrite] at hc
  have hdecomp : d - 1 = (d - 2) + 1 := by omega
  have hΔS : seqDiff 1 (seqDiff (d - 2) F) = seqDiff (d - 1) F := by
    rw [hdecomp, seqDiff_one, seqDiff_succ]
  have hK : seqDiff 1 (seqDiff (d - 2) F) =ᶠ[Filter.atTop]
      fun _ => (Nat.factorial (d - 1) : ℚ) * c := by
    rw [hΔS]
    exact hc
  have hG' : ∀ n, seqDiff (d - 2) (fun m => G (m + t)) n
      = seqDiff (d - 2) F (n + t) - seqDiff (d - 2) F n := by
    intro n
    have hsub : (fun m => G (m + t))
        = (fun m => F (m + t)) - (fun m => F m) := by
      funext m
      change G (m + t) = F (m + t) - F m
      rw [hG (m + t)]
      have htt : m + t - t = m := by omega
      rw [htt]
    rw [hsub, singleDrop_seqDiff_sub]
    simp only [seqDiff_comp_add, Pi.sub_apply]
  have hsum : (fun n => ∑ j ∈ Finset.range t,
        seqDiff 1 (seqDiff (d - 2) F) (n + j))
      =ᶠ[Filter.atTop]
        fun _ => (t : ℚ) * ((Nat.factorial (d - 1) : ℚ) * c) := by
    have heach : ∀ j ∈ Finset.range t,
        (fun n => seqDiff 1 (seqDiff (d - 2) F) (n + j))
          =ᶠ[Filter.atTop] fun _ => (Nat.factorial (d - 1) : ℚ) * c :=
      fun j _ => singleDrop_eventuallyEq_comp_add hK
    have hfin := singleDrop_eventuallyEq_finset_sum (Finset.range t) heach
    simpa using hfin
  have htel : ∀ n, seqDiff (d - 2) F (n + t) - seqDiff (d - 2) F n
      = ∑ j ∈ Finset.range t, seqDiff 1 (seqDiff (d - 2) F) (n + j) :=
    fun n => singleDrop_telescope_add _ n t
  have hG'ev : seqDiff (d - 2) (fun n => G (n + t))
      =ᶠ[Filter.atTop]
        fun _ => (t : ℚ) * ((Nat.factorial (d - 1) : ℚ) * c) := by
    have hpoint : seqDiff (d - 2) (fun n => G (n + t))
        = (fun n => ∑ j ∈ Finset.range t,
          seqDiff 1 (seqDiff (d - 2) F) (n + j)) := by
      funext n
      rw [hG' n]
      exact htel n
    rw [hpoint]
    exact hsum
  have htK : (t : ℚ) * ((Nat.factorial (d - 1) : ℚ) * c) ≠ 0 := by
    apply mul_ne_zero
    · exact_mod_cast (by omega : t ≠ 0)
    · exact hcne
  have hG'ne : ¬ seqDiff (d - 2) (fun n => G (n + t))
      =ᶠ[Filter.atTop] 0 :=
    singleDrop_not_eventuallyEq_zero_of_const hG'ev htK
  intro hvan
  apply hG'ne
  have hcomp := singleDrop_eventuallyEq_comp_add hvan (N := t)
  have hshift : seqDiff (d - 2) (fun n => G (n + t))
      = fun n => seqDiff (d - 2) G (n + t) :=
    seqDiff_comp_add _ _ _
  rw [hshift]
  have h0 : (fun n => (0 : ℕ → ℚ) (n + t)) = (0 : ℕ → ℚ) := by
    funext n
    rfl
  rwa [h0] at hcomp

/-- The binomial basis differentiates to one: the `k`-th difference of
`n ↦ C(n, k)` is the constant `1`.
-/
theorem singleDrop_seqDiff_chooseFun_self (k : ℕ) :
    seqDiff k (chooseFun (R := ℚ) k) = fun _ => 1 := by
  induction k with
  | zero =>
    have h0 : chooseFun (R := ℚ) 0 = fun _ => 1 := by
      funext n
      change ((Nat.choose n 0 : ℕ) : ℚ) = 1
      rw [Nat.choose_zero_right, Nat.cast_one]
    rw [seqDiff_zero, h0]
  | succ k ih =>
    have hstep : seqDiff (k + 1) (chooseFun (R := ℚ) (k + 1))
        = seqDiff k (chooseFun (R := ℚ) k) := by
      rw [singleDrop_seqDiff_add, seqDiff_chooseFun_succ]
    rw [hstep]
    exact ih

/-- The domain Hilbert function does not vanish at top degree: its
`(d-1)`-st difference is eventually the constant `1`.
-/
theorem singleDrop_domain_not_vanishing (κ : Type*) [Field κ] (d : ℕ)
    (hd : 1 ≤ d) :
    ¬ seqDiff (d - 1) (fun n => ((hsAssemble_domainHilbert κ d n : ℕ) : ℚ))
      =ᶠ[Filter.atTop] 0 := by
  have hSB : ∀ n, hsAssemble_domainHilbert κ d n
      = Nat.choose (n + d - 1) (d - 1) :=
    fun n => hsAssemble_domainHilbert_eq_choose κ d hd n
  have heq : (fun n => ((hsAssemble_domainHilbert κ d n : ℕ) : ℚ))
      = (fun n => chooseFun (R := ℚ) (d - 1) (n + (d - 1))) := by
    funext n
    have hN : n + d - 1 = n + (d - 1) := by omega
    change ((hsAssemble_domainHilbert κ d n : ℕ) : ℚ)
      = ((Nat.choose (n + (d - 1)) (d - 1) : ℕ) : ℚ)
    rw [hSB n, hN]
  have hdiff : seqDiff (d - 1)
        (fun n => ((hsAssemble_domainHilbert κ d n : ℕ) : ℚ))
      = fun _ => (1 : ℚ) := by
    rw [heq, seqDiff_comp_add, singleDrop_seqDiff_chooseFun_self]
  rw [hdiff]
  intro h0
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h0
  have hNN := hN N le_rfl
  simp only [Pi.zero_apply] at hNN
  exact one_ne_zero hNN

/-- Concrete quotient nonvanishing: the `(d-2)`-nd difference of
`H_{P/yP}` does not vanish (transfer from the uniform difference
function, which agrees with `H_{P/yP}` above `t`).
-/
theorem singleDrop_quot_not_vanishing (κ : Type*) [Field κ] (d t : ℕ)
    (hd : 2 ≤ d) (y : MvPolynomial (Fin d) κ) (hyhom : y.IsHomogeneous t)
    (hyne : y ≠ 0) (ht : 1 ≤ t) :
    ¬ seqDiff (d - 2)
        (fun n => ((singleDrop_quotHilbert κ d t y hyhom n : ℕ) : ℚ))
      =ᶠ[Filter.atTop] 0 := by
  set G : ℕ → ℚ := fun n => ((hsAssemble_domainHilbert κ d n : ℕ) : ℚ)
    - ((hsAssemble_domainHilbert κ d (n - t) : ℕ) : ℚ) with hGdef
  have hGunif : ∀ n, G n = ((hsAssemble_domainHilbert κ d n : ℕ) : ℚ)
      - ((hsAssemble_domainHilbert κ d (n - t) : ℕ) : ℚ) :=
    fun n => rfl
  have hGne : ¬ seqDiff (d - 2) G =ᶠ[Filter.atTop] 0 :=
    singleDrop_not_vanishing_of_sub d t hd ht
      (hsAssemble_hF κ d (by omega)) hGunif
      (singleDrop_domain_not_vanishing κ d (by omega))
  have hag : (fun n => ((singleDrop_quotHilbert κ d t y hyhom n : ℕ) : ℚ))
      =ᶠ[Filter.atTop] G := by
    refine Filter.eventually_atTop.mpr ⟨t, fun n hn => ?_⟩
    change ((singleDrop_quotHilbert κ d t y hyhom n : ℕ) : ℚ)
      = ((hsAssemble_domainHilbert κ d n : ℕ) : ℚ)
        - ((hsAssemble_domainHilbert κ d (n - t) : ℕ) : ℚ)
    exact singleDrop_quot_cast_sub κ d t y hyhom hyne n hn
  have htrans := seqDiff_eventuallyEq_of_eventuallyEq hag (d - 2)
  intro hvan
  exact hGne (htrans.symm.trans hvan)

/-- Exactness: `H_{P/yP}` has growth degree exactly `d - 2`.
-/
theorem singleDrop_quot_exact (κ : Type*) [Field κ] (d t : ℕ) (hd : 2 ≤ d)
    (y : MvPolynomial (Fin d) κ) (hyhom : y.IsHomogeneous t) (hyne : y ≠ 0)
    (ht : 1 ≤ t) :
    ∃ P : ℚ[X], P.natDegree = d - 2 ∧
      (fun n => ((singleDrop_quotHilbert κ d t y hyhom n : ℕ) : ℚ))
        =ᶠ[Filter.atTop] evalFun P := by
  have hQ : IsPolyGrowth
      (fun n => ((singleDrop_quotHilbert κ d t y hyhom n : ℕ) : ℚ)) (d - 2) :=
    singleDrop_isPolyGrowth_sub d t ht (hsAssemble_hF κ d (by omega))
      (fun n hn => singleDrop_quot_cast_sub κ d t y hyhom hyne n hn)
  exact growth_exact_of_not_vanishing hQ
    (singleDrop_quot_not_vanishing κ d t hd y hyhom hyne ht)

end Exactness

/-! ## §7. Master assembly: `ker ≠ ⊥` drops the gr growth degree -/

section Master

variable {K : Type*} [Field K] {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K))
  [P.IsPrime]

/-- Per-`y` drop: a nonzero homogeneous `y ∈ ker` (whose degree is
`≥ 1` by §1), plus the SES equation and the pointwise comparison,
forces every eventually-agreeing `gr` polynomial to have degree
`≤ d - 2`.

Explicitly conditional on `hSES`, `hcomp`, `hag_gr`, `hdom` (see
the module docstring for discharge routes). -/
theorem singleDrop_deg_le_of_step (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hd : 2 ≤ d)
    (y : MvPolynomial (Fin d)
      (IsLocalRing.ResidueField (Localization.AtPrime P))) (t : ℕ)
    (hym : y ∈ RingHom.ker (polySurjResidue P d g hgen)) (hyne : y ≠ 0)
    (hyhom : y.IsHomogeneous t)
    (Hgr Hq : ℕ → ℕ)
    (hSES : ∀ n, t ≤ n →
      Hq n + hsAssemble_domainHilbert
        (IsLocalRing.ResidueField (Localization.AtPrime P)) d (n - t)
        = hsAssemble_domainHilbert
          (IsLocalRing.ResidueField (Localization.AtPrime P)) d n)
    (hcomp : ∀ n, Hgr n ≤ Hq n)
    (Pgr : ℚ[X])
    (hag_gr : (fun n => ((Hgr n : ℕ) : ℚ)) =ᶠ[Filter.atTop] evalFun Pgr)
    (hdom : ∀ P Q : ℚ[X], (∀ᶠ (n : ℕ) in Filter.atTop, 0 ≤ P.eval (n : ℚ)) →
      (∀ᶠ (n : ℕ) in Filter.atTop, P.eval (n : ℚ) ≤ Q.eval (n : ℚ)) →
      Q.natDegree ≤ d - 2 → P.natDegree ≤ d - 2) :
    Pgr.natDegree ≤ d - 2 := by
  have ht : 1 ≤ t :=
    singleDrop_homogeneous_mem_ker_pos _ d g hgen hym hyne hyhom
  have hQ : IsPolyGrowth (fun n => ((Hq n : ℕ) : ℚ)) (d - 2) :=
    singleDrop_isPolyGrowth_sub d t ht
      (hsAssemble_hF _ d (by omega)) (fun n hn => by
        have hSES' := hSES n hn
        have hcast : ((Hq n : ℕ) : ℚ)
              + ((hsAssemble_domainHilbert
                (IsLocalRing.ResidueField (Localization.AtPrime P)) d (n - t)
                : ℕ) : ℚ)
            = ((hsAssemble_domainHilbert
              (IsLocalRing.ResidueField (Localization.AtPrime P)) d n
              : ℕ) : ℚ) := by
          have h2 := congrArg (fun m : ℕ => (m : ℚ)) hSES'
          rwa [Nat.cast_add] at h2
        calc ((Hq n : ℕ) : ℚ)
              = ((Hq n : ℕ) : ℚ)
                + ((hsAssemble_domainHilbert
                  (IsLocalRing.ResidueField (Localization.AtPrime P)) d (n - t)
                  : ℕ) : ℚ)
                - ((hsAssemble_domainHilbert
                  (IsLocalRing.ResidueField (Localization.AtPrime P)) d (n - t)
                  : ℕ) : ℚ) := by abel
            _ = ((hsAssemble_domainHilbert
                (IsLocalRing.ResidueField (Localization.AtPrime P)) d n
                : ℕ) : ℚ)
              - ((hsAssemble_domainHilbert
                (IsLocalRing.ResidueField (Localization.AtPrime P)) d (n - t)
                : ℕ) : ℚ) := by rw [hcast])
  obtain ⟨Q, hQd, hQag⟩ := hQ
  apply hdom Pgr Q _ _ hQd
  · obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp hag_gr
    refine Filter.eventually_atTop.mpr ⟨N1, fun n hn => ?_⟩
    have hnn : (0 : ℚ) ≤ ((Hgr n : ℕ) : ℚ) := Nat.cast_nonneg _
    have hn' : ((Hgr n : ℕ) : ℚ) = evalFun Pgr n := hN1 n hn
    rw [hn'] at hnn
    exact hnn
  · obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp hag_gr
    obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.mp hQag
    refine Filter.eventually_atTop.mpr ⟨max N1 N2, fun n hn => ?_⟩
    have hn1 : ((Hgr n : ℕ) : ℚ) = evalFun Pgr n :=
      hN1 n (le_trans (Nat.le_max_left _ _) hn)
    have hn2 : ((Hq n : ℕ) : ℚ) = evalFun Q n :=
      hN2 n (le_trans (Nat.le_max_right _ _) hn)
    have hle : ((Hgr n : ℕ) : ℚ) ≤ ((Hq n : ℕ) : ℚ) :=
      Nat.cast_le.mpr (hcomp n)
    rw [hn1, hn2] at hle
    exact hle

/-- Master (the exact shape the §6 `hsAssemble_ker_eq_bot` assembly
consumes after the R3' re-scope): `ker ≠ ⊥` supplies the homogeneous
`y` (§11 + §1), and the per-`y` step forces `deg H_gr ≤ d - 2`.

Explicitly conditional on `hstep`, `hag_gr`, `hdom` (see the module
docstring for discharge routes). -/
theorem singleDrop_deg_le_of_ker_ne_bot (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hd : 2 ≤ d) (Hgr Hq : ℕ → ℕ) (Pgr : ℚ[X])
    (hag_gr : (fun n => ((Hgr n : ℕ) : ℚ)) =ᶠ[Filter.atTop] evalFun Pgr)
    (hdom : ∀ P Q : ℚ[X], (∀ᶠ (n : ℕ) in Filter.atTop, 0 ≤ P.eval (n : ℚ)) →
      (∀ᶠ (n : ℕ) in Filter.atTop, P.eval (n : ℚ) ≤ Q.eval (n : ℚ)) →
      Q.natDegree ≤ d - 2 → P.natDegree ≤ d - 2)
    (hstep : ∀ (y : MvPolynomial (Fin d)
          (IsLocalRing.ResidueField (Localization.AtPrime P))) (t : ℕ),
        y ∈ RingHom.ker (polySurjResidue P d g hgen) → y ≠ 0 →
          y.IsHomogeneous t →
        (∀ n, t ≤ n →
          Hq n + hsAssemble_domainHilbert
            (IsLocalRing.ResidueField (Localization.AtPrime P)) d (n - t)
            = hsAssemble_domainHilbert
              (IsLocalRing.ResidueField (Localization.AtPrime P)) d n)
        ∧ (∀ n, Hgr n ≤ Hq n))
    (hker : RingHom.ker (polySurjResidue P d g hgen) ≠ ⊥) :
    Pgr.natDegree ≤ d - 2 := by
  obtain ⟨t, y, hym, hyne, hyhom⟩ :=
    hsAssemble_exists_homogeneous_mem_ker _ d g hgen hker
  obtain ⟨hSES, hcomp⟩ := hstep y t hym hyne hyhom
  exact singleDrop_deg_le_of_step P d g hgen hd y t hym hyne hyhom
    Hgr Hq hSES hcomp Pgr hag_gr hdom

/-- The §6-style contrapositive: dim-equality (`hdimEq`, exact degree
`d - 1` for `H_gr`) plus the R3' drop (`≤ d - 2`) forces `ker = ⊥`.

Explicitly conditional on `hstep`, `hag_gr`, `hdom`, `hdimEq` (see
the module docstring for discharge routes). -/
theorem singleDrop_ker_eq_bot (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hd : 2 ≤ d) (Hgr Hq : ℕ → ℕ) (Pgr : ℚ[X])
    (hag_gr : (fun n => ((Hgr n : ℕ) : ℚ)) =ᶠ[Filter.atTop] evalFun Pgr)
    (hdom : ∀ P Q : ℚ[X], (∀ᶠ (n : ℕ) in Filter.atTop, 0 ≤ P.eval (n : ℚ)) →
      (∀ᶠ (n : ℕ) in Filter.atTop, P.eval (n : ℚ) ≤ Q.eval (n : ℚ)) →
      Q.natDegree ≤ d - 2 → P.natDegree ≤ d - 2)
    (hstep : ∀ (y : MvPolynomial (Fin d)
          (IsLocalRing.ResidueField (Localization.AtPrime P))) (t : ℕ),
        y ∈ RingHom.ker (polySurjResidue P d g hgen) → y ≠ 0 →
          y.IsHomogeneous t →
        (∀ n, t ≤ n →
          Hq n + hsAssemble_domainHilbert
            (IsLocalRing.ResidueField (Localization.AtPrime P)) d (n - t)
            = hsAssemble_domainHilbert
              (IsLocalRing.ResidueField (Localization.AtPrime P)) d n)
        ∧ (∀ n, Hgr n ≤ Hq n))
    (hdimEq : ∀ Q : ℚ[X], Q.natDegree ≤ d - 1 →
      (fun n => ((Hgr n : ℕ) : ℚ)) =ᶠ[Filter.atTop] evalFun Q →
      Q.natDegree = d - 1) :
    RingHom.ker (polySurjResidue P d g hgen) = ⊥ := by
  by_contra hker
  have hle :=
    singleDrop_deg_le_of_ker_ne_bot P d g hgen hd Hgr Hq Pgr hag_gr hdom
      hstep hker
  have hle' : Pgr.natDegree ≤ d - 1 := le_trans hle (by omega)
  have heq := hdimEq Pgr hle' hag_gr
  omega

end Master

/-! ## §8. Residue-field scalars on `grPiece` -/

section GrPieceResidueModule

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- `I` annihilates each graded piece: for `c ∈ I`, `c • x = 0` on
`grPiece R I n`, since `c * r ∈ I ^ (n + 1)` for `r ∈ I ^ n`.
-/
theorem singleDrop_grPiece_annihilated (n : ℕ) (c : R) (hc : c ∈ I)
    (x : grPiece R I n) : c • x = 0 := by
  obtain ⟨r, rfl⟩ := grPiece_mk_surjective R I n x
  rw [grPiece_mk_smul]
  apply (grPiece_mk_eq_zero_iff R I n _).mpr
  change c * (r : R) ∈ I ^ (n + 1)
  rw [pow_succ, mul_comm c (r : R)]
  exact Submodule.mul_mem_mul r.2 hc

/-- Auxiliary scalar action: lift `R`-scaling through the quotient
(well-defined by annihilation).
-/
noncomputable def singleDrop_grPiece_smulFun (n : ℕ) (q : R ⧸ I)
    (x : grPiece R I n) : grPiece R I n :=
  Quotient.liftOn q (fun r => r • x) (fun a b h => by
    have hmem : a - b ∈ I := (Submodule.quotientRel_def I).mp h
    have hann : (a - b) • x = 0 :=
      singleDrop_grPiece_annihilated I n (a - b) hmem x
    rw [sub_smul] at hann
    exact sub_eq_zero.mp hann)

/-- Computation for the auxiliary action.
-/
theorem singleDrop_grPiece_smul_mk (n : ℕ) (r : R) (x : grPiece R I n) :
    singleDrop_grPiece_smulFun I n (Ideal.Quotient.mk I r) x = r • x := rfl

/-- The residue-field module structure on `grPiece`: `R`-scaling descends
through the quotient by annihilation (§8).
-/
noncomputable instance singleDrop_grPiece_module (n : ℕ) :
    Module (R ⧸ I) (grPiece R I n) where
  smul := singleDrop_grPiece_smulFun I n
  smul_zero := fun q => Quotient.inductionOn' q (fun r => by
    change singleDrop_grPiece_smulFun I n (Ideal.Quotient.mk I r) 0 = 0
    rw [singleDrop_grPiece_smul_mk]
    exact smul_zero r)
  smul_add := fun q x y => Quotient.inductionOn' q (fun r => by
    change singleDrop_grPiece_smulFun I n (Ideal.Quotient.mk I r) (x + y)
      = singleDrop_grPiece_smulFun I n (Ideal.Quotient.mk I r) x
        + singleDrop_grPiece_smulFun I n (Ideal.Quotient.mk I r) y
    rw [singleDrop_grPiece_smul_mk, singleDrop_grPiece_smul_mk,
      singleDrop_grPiece_smul_mk]
    exact smul_add r x y)
  add_smul := fun p q x => Quotient.inductionOn' p (fun r =>
    Quotient.inductionOn' q (fun s => by
      change singleDrop_grPiece_smulFun I n
          (Ideal.Quotient.mk I r + Ideal.Quotient.mk I s) x
        = singleDrop_grPiece_smulFun I n (Ideal.Quotient.mk I r) x
          + singleDrop_grPiece_smulFun I n (Ideal.Quotient.mk I s) x
      rw [← map_add (Ideal.Quotient.mk I), singleDrop_grPiece_smul_mk,
        singleDrop_grPiece_smul_mk, singleDrop_grPiece_smul_mk]
      exact add_smul r s x))
  zero_smul := fun x => by
    change singleDrop_grPiece_smulFun I n (0 : R ⧸ I) x = 0
    rw [← map_zero (Ideal.Quotient.mk I), singleDrop_grPiece_smul_mk]
    exact zero_smul _ _
  one_smul := fun x => by
    change singleDrop_grPiece_smulFun I n (1 : R ⧸ I) x = x
    rw [← map_one (Ideal.Quotient.mk I), singleDrop_grPiece_smul_mk]
    exact one_smul _ _
  mul_smul := fun p q x => Quotient.inductionOn' p (fun r =>
    Quotient.inductionOn' q (fun s => by
      change singleDrop_grPiece_smulFun I n
          (Ideal.Quotient.mk I r * Ideal.Quotient.mk I s) x
        = singleDrop_grPiece_smulFun I n (Ideal.Quotient.mk I r)
          (singleDrop_grPiece_smulFun I n (Ideal.Quotient.mk I s) x)
      rw [← map_mul (Ideal.Quotient.mk I), singleDrop_grPiece_smul_mk,
        singleDrop_grPiece_smul_mk, singleDrop_grPiece_smul_mk]
      exact mul_smul r s x))

/-- Computation: quotient scalars act through representatives.
-/
theorem singleDrop_grPiece_mk_smul (n : ℕ) (r : R) (x : grPiece R I n) :
    (Ideal.Quotient.mk I r) • x = r • x :=
  singleDrop_grPiece_smul_mk I n r x

/-- The `gr` Hilbert function: residue-field lengths of the graded pieces.
-/
noncomputable def singleDrop_grHilbert (n : ℕ) : ℕ :=
  finLength (R ⧸ I) (grPiece R I n)

end GrPieceResidueModule

/-! ## §9. Piece-level surjection onto `gr` -/

section PieceSurj

variable {R : Type*} [CommRing R] (I : Ideal R) (d : ℕ) (g : Fin d → R)
  (hgen : Ideal.span (Set.range g) = I)

/-- `DirectSum.of` at a fixed degree is injective.
-/
theorem singleDrop_of_injective (n : ℕ) :
    Function.Injective (DirectSum.of (grPiece R I) n) := by
  intro x y h
  have h2 := congrArg (fun s : DirectSum ℕ (grPiece R I) => s n) h
  rw [DirectSum.of_eq_same, DirectSum.of_eq_same] at h2
  exact h2

/-- Components of a finite homogeneous sum read back the summands.
-/
theorem singleDrop_component_of_sum (y : ∀ i, grPiece R I i) (N n : ℕ)
    (hn : n < N) :
    (∑ i ∈ Finset.range N, DirectSum.of (grPiece R I) i (y i)) n = y n := by
  rw [DFinsupp.finsetSum_apply]
  rw [Finset.sum_eq_single n
    (fun j _ hji => DirectSum.of_eq_of_ne j n (y j) (Ne.symm hji))
    (fun hi' => absurd (Finset.mem_range.mpr hn) hi')]
  rw [DirectSum.of_eq_same]

/-- Per-element existence for the piece function.
-/
theorem singleDrop_pieceFun_exists (n : ℕ)
    (p : ↥(MvPolynomial.homogeneousSubmodule (Fin d) (R ⧸ I) n)) :
    ∃ w : grPiece R I n,
      polySurj R I d g hgen p.val = DirectSum.of (grPiece R I) n w :=
  hsAssemble_polySurj_of_homogeneous I d g hgen
    ((MvPolynomial.mem_homogeneousSubmodule n p.val).mp p.property)

/-- The degree-`n` piece function: `polySurj` lies in degree `n` on
homogeneous inputs (`hsAssemble_polySurj_of_homogeneous`).
-/
noncomputable def singleDrop_pieceFun (n : ℕ)
    (p : ↥(MvPolynomial.homogeneousSubmodule (Fin d) (R ⧸ I) n)) :
    grPiece R I n :=
  Classical.choose
    (Classical.axiomOfChoice (singleDrop_pieceFun_exists I d g hgen n)) p

/-- The piece function computes `polySurj` followed by degree projection.
-/
theorem singleDrop_pieceFun_spec (n : ℕ)
    (p : ↥(MvPolynomial.homogeneousSubmodule (Fin d) (R ⧸ I) n)) :
    polySurj R I d g hgen p.val
      = DirectSum.of (grPiece R I) n (singleDrop_pieceFun I d g hgen n p) := by
  unfold singleDrop_pieceFun
  exact Classical.choose_spec
    (Classical.axiomOfChoice (singleDrop_pieceFun_exists I d g hgen n)) p

/-- The degree-`n` piece map as a residue-field linear map.
-/
noncomputable def singleDrop_pieceMap (n : ℕ) :
    ↥(MvPolynomial.homogeneousSubmodule (Fin d) (R ⧸ I) n) →ₗ[R ⧸ I]
      grPiece R I n where
  toFun := singleDrop_pieceFun I d g hgen n
  map_add' a b := by
    apply singleDrop_of_injective I n
    have e1 : polySurj R I d g hgen (a + b).val
        = DirectSum.of (grPiece R I) n
          (singleDrop_pieceFun I d g hgen n (a + b)) :=
      singleDrop_pieceFun_spec I d g hgen n (a + b)
    have e2 : polySurj R I d g hgen a.val
        = DirectSum.of (grPiece R I) n
          (singleDrop_pieceFun I d g hgen n a) :=
      singleDrop_pieceFun_spec I d g hgen n a
    have e3 : polySurj R I d g hgen b.val
        = DirectSum.of (grPiece R I) n
          (singleDrop_pieceFun I d g hgen n b) :=
      singleDrop_pieceFun_spec I d g hgen n b
    have hadd : ((a + b).val : MvPolynomial (Fin d) (R ⧸ I)) = a.val + b.val :=
      rfl
    change DirectSum.of (grPiece R I) n
        (singleDrop_pieceFun I d g hgen n (a + b))
      = DirectSum.of (grPiece R I) n
        (singleDrop_pieceFun I d g hgen n a + singleDrop_pieceFun I d g hgen n b)
    rw [← e1, hadd, map_add, e2, e3]
    exact (map_add (DirectSum.of (grPiece R I) n) _ _).symm
  map_smul' c p := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
    apply singleDrop_of_injective I n
    change DirectSum.of (grPiece R I) n
        (singleDrop_pieceFun I d g hgen n ((Ideal.Quotient.mk I r) • p))
      = DirectSum.of (grPiece R I) n
        ((Ideal.Quotient.mk I r) • singleDrop_pieceFun I d g hgen n p)
    have e1 : polySurj R I d g hgen (((Ideal.Quotient.mk I r) • p).val)
        = DirectSum.of (grPiece R I) n
          (singleDrop_pieceFun I d g hgen n ((Ideal.Quotient.mk I r) • p)) :=
      singleDrop_pieceFun_spec I d g hgen n _
    have e2 : polySurj R I d g hgen p.val
        = DirectSum.of (grPiece R I) n
          (singleDrop_pieceFun I d g hgen n p) :=
      singleDrop_pieceFun_spec I d g hgen n p
    have hsmul : ((((Ideal.Quotient.mk I r) • p).val :
        MvPolynomial (Fin d) (R ⧸ I)))
        = (Ideal.Quotient.mk I r) • p.val := rfl
    rw [← e1, hsmul, MvPolynomial.smul_eq_C_mul, map_mul, polySurj_C, e2,
      coeffHom_mk, singleDrop_grPiece_mk_smul]
    exact (of_smul_eq R I n r _).symm

/-- Every `gr` class has a homogeneous preimage under `polySurj` (take the
degree-`n` homogeneous component of any preimage).
-/
theorem singleDrop_homogeneous_preimage (n : ℕ) (z : grPiece R I n) :
    ∃ q : MvPolynomial (Fin d) (R ⧸ I), q.IsHomogeneous n ∧
      polySurj R I d g hgen q = DirectSum.of (grPiece R I) n z := by
  obtain ⟨p, hp⟩ := polySurj_surjective R I d g hgen
    (DirectSum.of (grPiece R I) n z)
  have hmap : polySurj R I d g hgen p =
      ∑ i ∈ Finset.range (p.totalDegree + 1),
        polySurj R I d g hgen ((MvPolynomial.homogeneousComponent i) p) := by
    conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent p]
    rw [map_sum]
  have hmono : ∀ i : ℕ, ∃ w : grPiece R I i,
      polySurj R I d g hgen ((MvPolynomial.homogeneousComponent i) p) =
        DirectSum.of (grPiece R I) i w := fun i =>
    hsAssemble_polySurj_of_homogeneous I d g hgen
      (MvPolynomial.homogeneousComponent_isHomogeneous i p)
  obtain ⟨w, hw⟩ := Classical.axiomOfChoice hmono
  have hsum : (∑ i ∈ Finset.range (p.totalDegree + 1),
        DirectSum.of (grPiece R I) i (w i))
      = DirectSum.of (grPiece R I) n z := by
    have hcongr : (∑ i ∈ Finset.range (p.totalDegree + 1),
          DirectSum.of (grPiece R I) i (w i))
        = ∑ i ∈ Finset.range (p.totalDegree + 1),
          polySurj R I d g hgen ((MvPolynomial.homogeneousComponent i) p) :=
      Finset.sum_congr rfl (fun i _ => (hw i).symm)
    rw [hcongr, ← hmap, hp]
  by_cases hn : n < p.totalDegree + 1
  · have hcomp := singleDrop_component_of_sum I (fun i => w i)
      (p.totalDegree + 1) n hn
    rw [hsum, DirectSum.of_eq_same] at hcomp
    refine ⟨(MvPolynomial.homogeneousComponent n) p,
      MvPolynomial.homogeneousComponent_isHomogeneous n p, ?_⟩
    rw [hw n]
    congr 1
    exact hcomp.symm
  · have h0 : (∑ i ∈ Finset.range (p.totalDegree + 1),
        DirectSum.of (grPiece R I) i (w i)) n = 0 := by
      rw [DFinsupp.finsetSum_apply]
      refine Finset.sum_eq_zero (fun i hi => ?_)
      rw [Finset.mem_range] at hi
      exact DirectSum.of_eq_of_ne i n (w i) (by omega)
    rw [hsum, DirectSum.of_eq_same] at h0
    have hq0 : (MvPolynomial.homogeneousComponent n) p = 0 :=
      MvPolynomial.homogeneousComponent_eq_zero n p (by omega)
    refine ⟨(MvPolynomial.homogeneousComponent n) p,
      MvPolynomial.homogeneousComponent_isHomogeneous n p, ?_⟩
    rw [hq0, map_zero, h0]
    exact (map_zero _).symm

/-- The piece map is surjective.
-/
theorem singleDrop_pieceMap_surjective (n : ℕ) :
    Function.Surjective (singleDrop_pieceMap I d g hgen n) := by
  intro z
  obtain ⟨q, hqhom, hq⟩ := singleDrop_homogeneous_preimage I d g hgen n z
  have hqmem : q ∈ MvPolynomial.homogeneousSubmodule (Fin d) (R ⧸ I) n :=
    (MvPolynomial.mem_homogeneousSubmodule n q).mpr hqhom
  refine ⟨⟨q, hqmem⟩, ?_⟩
  have espec : polySurj R I d g hgen q
      = DirectSum.of (grPiece R I) n
        (singleDrop_pieceMap I d g hgen n ⟨q, hqmem⟩) :=
    singleDrop_pieceFun_spec I d g hgen n ⟨q, hqmem⟩
  rw [hq] at espec
  exact (singleDrop_of_injective I n espec).symm

end PieceSurj

/-! ## §9b. Quotient-piece comparison over a local ring -/

section QuotPieceLocal

variable {R : Type*} [CommRing R] [IsLocalRing R] (d : ℕ) (g : Fin d → R)
  (hgen : Ideal.span (Set.range g) = IsLocalRing.maximalIdeal R)
  (t : ℕ) (y : MvPolynomial (Fin d) (IsLocalRing.ResidueField R))
  (hyhom : y.IsHomogeneous t)

/-- Residue-field-facing copy of the §8 instance: stated with
`IsLocalRing.ResidueField` so typeclass search fires for residue-field goals
(the quotient form is invisible to TC through the semireducible
`ResidueField`).
-/
noncomputable instance singleDrop_grPiece_module_residue (n : ℕ) :
    Module (IsLocalRing.ResidueField R)
      (grPiece R (IsLocalRing.maximalIdeal R) n) :=
  singleDrop_grPiece_module (IsLocalRing.maximalIdeal R) n

/-- The piece map kills `y • P_{n-t}` since `y ∈ ker`.
-/
theorem singleDrop_pieceMap_range_le_ker_residue (n : ℕ) (h : t ≤ n)
    (hym : y ∈ RingHom.ker
      (polySurj R (IsLocalRing.maximalIdeal R) d g hgen)) :
    LinearMap.range
        (singleDrop_mulMap (IsLocalRing.ResidueField R) d t y hyhom n h)
      ≤ LinearMap.ker
        (singleDrop_pieceMap (IsLocalRing.maximalIdeal R) d g hgen n) := by
  intro m hm
  obtain ⟨p', hp'⟩ := hm
  subst hp'
  change singleDrop_pieceMap (IsLocalRing.maximalIdeal R) d g hgen n
      ((singleDrop_mulMap (IsLocalRing.ResidueField R) d t y hyhom n h) p')
    = 0
  have hval : (((singleDrop_mulMap (IsLocalRing.ResidueField R) d t y hyhom n h)
        p').val : MvPolynomial (Fin d) (IsLocalRing.ResidueField R))
      = y * p'.val := rfl
  have espec : polySurj R (IsLocalRing.maximalIdeal R) d g hgen
        (((singleDrop_mulMap (IsLocalRing.ResidueField R) d t y hyhom n h)
          p').val)
      = DirectSum.of (grPiece R (IsLocalRing.maximalIdeal R)) n
        (singleDrop_pieceMap (IsLocalRing.maximalIdeal R) d g hgen n
          ((singleDrop_mulMap (IsLocalRing.ResidueField R) d t y hyhom n h)
            p')) :=
    singleDrop_pieceFun_spec (IsLocalRing.maximalIdeal R) d g hgen n _
  have e_mul : polySurj R (IsLocalRing.maximalIdeal R) d g hgen (y * p'.val)
      = polySurj R (IsLocalRing.maximalIdeal R) d g hgen y
        * polySurj R (IsLocalRing.maximalIdeal R) d g hgen p'.val :=
    map_mul _ _ _
  have hy0 : polySurj R (IsLocalRing.maximalIdeal R) d g hgen y = 0 :=
    RingHom.mem_ker.mp hym
  have step1 : (0 : associatedGraded R (IsLocalRing.maximalIdeal R))
      = polySurj R (IsLocalRing.maximalIdeal R) d g hgen y
        * polySurj R (IsLocalRing.maximalIdeal R) d g hgen p'.val := by
    rw [hy0, zero_mul]
  have step3 : polySurj R (IsLocalRing.maximalIdeal R) d g hgen (y * p'.val)
      = DirectSum.of (grPiece R (IsLocalRing.maximalIdeal R)) n
        (singleDrop_pieceMap (IsLocalRing.maximalIdeal R) d g hgen n
          ((singleDrop_mulMap (IsLocalRing.ResidueField R) d t y hyhom n h)
            p')) := by
    rw [← hval]
    exact espec
  have espec0 : (0 : associatedGraded R (IsLocalRing.maximalIdeal R))
      = DirectSum.of (grPiece R (IsLocalRing.maximalIdeal R)) n
        (singleDrop_pieceMap (IsLocalRing.maximalIdeal R) d g hgen n
          ((singleDrop_mulMap (IsLocalRing.ResidueField R) d t y hyhom n h)
            p')) :=
    step1.trans (e_mul.symm.trans step3)
  apply singleDrop_of_injective (IsLocalRing.maximalIdeal R) n
  rw [← espec0]
  exact (map_zero _).symm

/-- The factored quotient-piece map `(P_n ⧸ y·P_{n-t}) →ₗ gr_n`.
-/
noncomputable def singleDrop_quotPieceMap_residue (n : ℕ) (h : t ≤ n)
    (hym : y ∈ RingHom.ker
      (polySurj R (IsLocalRing.maximalIdeal R) d g hgen)) :
    (↥(MvPolynomial.homogeneousSubmodule (Fin d)
        (IsLocalRing.ResidueField R) n) ⧸
      LinearMap.range (singleDrop_mulMap (IsLocalRing.ResidueField R) d t y
        hyhom n h)) →ₗ[IsLocalRing.ResidueField R]
      grPiece R (IsLocalRing.maximalIdeal R) n :=
  (LinearMap.range (singleDrop_mulMap (IsLocalRing.ResidueField R) d t y
    hyhom n h)).liftQ
    (singleDrop_pieceMap (IsLocalRing.maximalIdeal R) d g hgen n)
    (singleDrop_pieceMap_range_le_ker_residue d g hgen t y hyhom n h hym)

/-- The factored quotient-piece map is surjective.
-/
theorem singleDrop_quotPieceMap_surjective_residue (n : ℕ) (h : t ≤ n)
    (hym : y ∈ RingHom.ker
      (polySurj R (IsLocalRing.maximalIdeal R) d g hgen)) :
    Function.Surjective
      (singleDrop_quotPieceMap_residue d g hgen t y hyhom n h hym) := by
  have hcomp : singleDrop_quotPieceMap_residue d g hgen t y hyhom n h hym
        ∘ Submodule.mkQ (LinearMap.range
          (singleDrop_mulMap (IsLocalRing.ResidueField R) d t y hyhom n h))
      = singleDrop_pieceMap (IsLocalRing.maximalIdeal R) d g hgen n := by
    funext x
    exact Submodule.liftQ_apply _ _ _
  have hsurj : Function.Surjective
      (singleDrop_quotPieceMap_residue d g hgen t y hyhom n h hym
        ∘ Submodule.mkQ (LinearMap.range
          (singleDrop_mulMap (IsLocalRing.ResidueField R) d t y hyhom n h))) := by
    rw [hcomp]
    exact singleDrop_pieceMap_surjective (IsLocalRing.maximalIdeal R) d g hgen n
  exact Function.Surjective.of_comp hsurj

/-- Pointwise comparison: the `gr` Hilbert function is bounded by the
`P ⧸ yP` one (discharges `hcomp`).
-/
theorem singleDrop_hcomp_concrete (n : ℕ)
    (hym : y ∈ RingHom.ker
      (polySurj R (IsLocalRing.maximalIdeal R) d g hgen)) :
    singleDrop_grHilbert (IsLocalRing.maximalIdeal R) n
      ≤ singleDrop_quotHilbert (IsLocalRing.ResidueField R) d t y hyhom n := by
  by_cases h : t ≤ n
  · have hQ : singleDrop_quotHilbert (IsLocalRing.ResidueField R) d t y hyhom n =
        finLength (IsLocalRing.ResidueField R)
          (↥(MvPolynomial.homogeneousSubmodule (Fin d)
            (IsLocalRing.ResidueField R) n) ⧸
          LinearMap.range (singleDrop_mulMap (IsLocalRing.ResidueField R) d t y
            hyhom n h)) := by
      unfold singleDrop_quotHilbert
      rw [dite_eq_left h]
    have hgr : singleDrop_grHilbert (IsLocalRing.maximalIdeal R) n
        = finLength (IsLocalRing.ResidueField R)
          (grPiece R (IsLocalRing.maximalIdeal R) n) := rfl
    rw [hQ, hgr]
    exact singleDrop_finLength_le_of_surjective
      (singleDrop_quotPieceMap_residue d g hgen t y hyhom n h hym)
      (singleDrop_quotPieceMap_surjective_residue d g hgen t y hyhom n h hym)
      (isFiniteLength_quotient
        (singleDrop_isFiniteLength (IsLocalRing.ResidueField R) d n) _)
  · have hQ : singleDrop_quotHilbert (IsLocalRing.ResidueField R) d t y hyhom n =
        hsAssemble_domainHilbert (IsLocalRing.ResidueField R) d n := by
      unfold singleDrop_quotHilbert
      rw [dite_eq_right h]
    have hdom : hsAssemble_domainHilbert (IsLocalRing.ResidueField R) d n
        = finLength (R ⧸ IsLocalRing.maximalIdeal R)
          ↥(MvPolynomial.homogeneousSubmodule (Fin d)
            (R ⧸ IsLocalRing.maximalIdeal R) n) := rfl
    rw [hQ, hdom]
    exact singleDrop_finLength_le_of_surjective
      (singleDrop_pieceMap (IsLocalRing.maximalIdeal R) d g hgen n)
      (singleDrop_pieceMap_surjective (IsLocalRing.maximalIdeal R) d g hgen n)
      (@singleDrop_isFiniteLength (R ⧸ IsLocalRing.maximalIdeal R)
        (IsLocalRing.ResidueField.field R) d n)

end QuotPieceLocal

/-! ## §10. Polynomial domination -/

section PolyDomination

/-- Split eval into the top term plus the lower sum.
-/
theorem singleDrop_eval_eq_top_add_lower (D : ℚ[X]) (x : ℚ) :
    D.eval x = D.leadingCoeff * x ^ D.natDegree +
      ∑ i ∈ Finset.range D.natDegree, D.coeff i * x ^ i := by
  conv_lhs => rw [Polynomial.eval_eq_sum_range]
  rw [Finset.sum_range_succ, Polynomial.coeff_natDegree]
  exact add_comm _ _

/-- Lower-sum bound: for `(n:ℚ) ≥ 1` and `1 ≤ natDegree`, the lower part is
at most `C * n ^ (k - 1)`.
-/
theorem singleDrop_eval_lower_abs_le (D : ℚ[X]) (n : ℕ) (hn : 1 ≤ (n : ℚ))
    (hk : 1 ≤ D.natDegree) :
    |∑ i ∈ Finset.range D.natDegree, D.coeff i * (n : ℚ) ^ i|
      ≤ (∑ i ∈ Finset.range D.natDegree, |D.coeff i|)
        * (n : ℚ) ^ (D.natDegree - 1) := by
  calc |∑ i ∈ Finset.range D.natDegree, D.coeff i * (n : ℚ) ^ i|
      ≤ ∑ i ∈ Finset.range D.natDegree, |D.coeff i * (n : ℚ) ^ i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ Finset.range D.natDegree, |D.coeff i| * (n : ℚ) ^ i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [abs_mul, abs_pow, abs_of_nonneg (by positivity : (0:ℚ) ≤ (n:ℚ))]
    _ ≤ ∑ i ∈ Finset.range D.natDegree,
          |D.coeff i| * (n : ℚ) ^ (D.natDegree - 1) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [Finset.mem_range] at hi
        have hpow : (n : ℚ) ^ i ≤ (n : ℚ) ^ (D.natDegree - 1) :=
          pow_le_pow_right₀ hn (by omega)
        exact mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
    _ = (∑ i ∈ Finset.range D.natDegree, |D.coeff i|)
        * (n : ℚ) ^ (D.natDegree - 1) :=
        (Finset.sum_mul _ _ _).symm

/-- A nonzero rational polynomial eventually takes the sign of its leading
coefficient (positive case): the top term dominates the lower sum.
-/
theorem singleDrop_eval_pos_of_leadingCoeff_pos (D : ℚ[X]) (_hD : D ≠ 0)
    (hlc : 0 < D.leadingCoeff) :
    ∀ᶠ n : ℕ in Filter.atTop, 0 < D.eval (n : ℚ) := by
  by_cases hk0 : D.natDegree = 0
  · have heval : ∀ n : ℕ, D.eval (n : ℚ) = D.leadingCoeff := by
      intro n
      have h1 : D.natDegree < 1 := by omega
      rw [Polynomial.eval_eq_sum_range' h1, Finset.sum_range_one]
      have hcoeff : D.coeff 0 = D.coeff D.natDegree := by rw [hk0]
      rw [pow_zero, mul_one, hcoeff, Polynomial.coeff_natDegree]
    exact Filter.Eventually.of_forall (fun n => by rw [heval n]; exact hlc)
  · have hk : 1 ≤ D.natDegree := by omega
    set C : ℚ := ∑ i ∈ Finset.range D.natDegree, |D.coeff i| with hCdef
    obtain ⟨N0, hN0⟩ := exists_nat_gt (C / D.leadingCoeff)
    refine Filter.eventually_atTop.mpr ⟨N0 + 1, fun n hn => ?_⟩
    have hnR : ((N0 + 1 : ℕ) : ℚ) ≤ (n : ℚ) := Nat.cast_le.mpr hn
    rw [Nat.cast_add, Nat.cast_one] at hnR
    have hN0nn : (0:ℚ) ≤ (N0 : ℚ) := Nat.cast_nonneg _
    have hn1 : (1:ℚ) ≤ (n : ℚ) := by linarith
    have hnN0 : (N0 : ℚ) < (n : ℚ) := by linarith
    have hlt : C < D.leadingCoeff * (n : ℚ) := by
      have h1 : C / D.leadingCoeff < (n : ℚ) := lt_trans hN0 hnN0
      have h2 : C < (n : ℚ) * D.leadingCoeff := (div_lt_iff₀ hlc).mp h1
      calc C < (n : ℚ) * D.leadingCoeff := h2
        _ = D.leadingCoeff * (n : ℚ) := mul_comm _ _
    have hnpos : (0:ℚ) < (n : ℚ) := by linarith
    have hpowpos : (0:ℚ) < (n : ℚ) ^ (D.natDegree - 1) := by positivity
    have hdecomp := singleDrop_eval_eq_top_add_lower D (n : ℚ)
    have hbound := singleDrop_eval_lower_abs_le D n hn1 hk
    rw [← hCdef] at hbound
    have htop : D.leadingCoeff * (n : ℚ) ^ D.natDegree
        = (D.leadingCoeff * (n : ℚ)) * (n : ℚ) ^ (D.natDegree - 1) := by
      have hk' : D.natDegree = (D.natDegree - 1) + 1 := by omega
      conv_lhs => rw [hk', pow_succ]
      ring
    rw [hdecomp, htop]
    have hgap : (0:ℚ) ≤ ((D.leadingCoeff * (n : ℚ))
          * (n : ℚ) ^ (D.natDegree - 1)
          + ∑ i ∈ Finset.range D.natDegree, D.coeff i * (n : ℚ) ^ i)
        - ((D.leadingCoeff * (n : ℚ) - C) * (n : ℚ) ^ (D.natDegree - 1)) := by
      have hnn : (0:ℚ) ≤ (∑ i ∈ Finset.range D.natDegree,
            D.coeff i * (n : ℚ) ^ i) + C * (n : ℚ) ^ (D.natDegree - 1) := by
        have hna := neg_abs_le
          (∑ i ∈ Finset.range D.natDegree, D.coeff i * (n : ℚ) ^ i)
        linarith [hbound, hna]
      have hexpand : (D.leadingCoeff * (n : ℚ) - C) * (n : ℚ) ^ (D.natDegree - 1)
          = (D.leadingCoeff * (n : ℚ)) * (n : ℚ) ^ (D.natDegree - 1)
            - C * (n : ℚ) ^ (D.natDegree - 1) := by ring
      rw [hexpand]
      linarith [hnn]
    have hmulpos : (0:ℚ) < (D.leadingCoeff * (n : ℚ) - C)
        * (n : ℚ) ^ (D.natDegree - 1) :=
      mul_pos (by linarith [hlt]) hpowpos
    linarith [hgap, hmulpos]

/-- Negative case via negation.
-/
theorem singleDrop_eval_neg_of_leadingCoeff_neg (D : ℚ[X]) (hD : D ≠ 0)
    (hlc : D.leadingCoeff < 0) :
    ∀ᶠ n : ℕ in Filter.atTop, D.eval (n : ℚ) < 0 := by
  have hneg : (-D).leadingCoeff = -D.leadingCoeff := Polynomial.leadingCoeff_neg D
  have hD' : -D ≠ 0 := neg_ne_zero.mpr hD
  have hlc' : 0 < (-D).leadingCoeff := by rw [hneg]; linarith
  have hev := singleDrop_eval_pos_of_leadingCoeff_pos (-D) hD' hlc'
  filter_upwards [hev] with n hn
  rw [Polynomial.eval_neg] at hn
  linarith [hn]

/-- Polynomial domination (discharges `hdom`): an eventually-nonnegative
polynomial eventually bounded above by `Q` has degree at most `Q`'s.
-/
theorem singleDrop_hdom (d : ℕ) (P Q : ℚ[X])
    (hP : ∀ᶠ (n : ℕ) in Filter.atTop, 0 ≤ P.eval (n : ℚ))
    (hle : ∀ᶠ (n : ℕ) in Filter.atTop, P.eval (n : ℚ) ≤ Q.eval (n : ℚ))
    (hQ : Q.natDegree ≤ d - 2) : P.natDegree ≤ d - 2 := by
  by_contra hcon
  have hlt : Q.natDegree < P.natDegree :=
    lt_of_le_of_lt hQ (lt_of_not_ge hcon)
  have hP0 : P ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.natDegree_zero] at hlt
    exact absurd hlt (not_lt_of_ge (Nat.zero_le _))
  have hlcP : 0 < P.leadingCoeff := by
    by_contra hc
    have hne : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP0
    have hneg : P.leadingCoeff < 0 := lt_of_le_of_ne (le_of_not_gt hc) hne
    have hev := singleDrop_eval_neg_of_leadingCoeff_neg P hP0 hneg
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hev.and hP)
    obtain ⟨hltN, hleN⟩ := hN N le_rfl
    linarith [hltN, hleN]
  have hDk : (P - Q).natDegree = P.natDegree := by
    apply le_antisymm
    · calc (P - Q).natDegree ≤ max P.natDegree Q.natDegree :=
          Polynomial.natDegree_sub_le _ _
        _ = P.natDegree := max_eq_left (le_of_lt hlt)
    · apply Polynomial.le_natDegree_of_ne_zero
      rw [Polynomial.coeff_sub, Polynomial.coeff_eq_zero_of_natDegree_lt hlt,
        sub_zero]
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hP0
  have hD0 : P - Q ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.natDegree_zero] at hDk
    omega
  have h1 : (P - Q).coeff P.natDegree = P.coeff P.natDegree := by
    rw [Polynomial.coeff_sub, Polynomial.coeff_eq_zero_of_natDegree_lt hlt,
      sub_zero]
  have hlcD : (P - Q).leadingCoeff = P.leadingCoeff := by
    rw [← Polynomial.coeff_natDegree, hDk, h1, Polynomial.coeff_natDegree]
  have hlcDpos : 0 < (P - Q).leadingCoeff := by rw [hlcD]; exact hlcP
  have hev := singleDrop_eval_pos_of_leadingCoeff_pos (P - Q) hD0 hlcDpos
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hev.and hle)
  obtain ⟨hposN, hleN⟩ := hN N le_rfl
  rw [Polynomial.eval_sub] at hposN
  linarith [hposN, hleN]

end PolyDomination

/-! ## §11. Discharged masters (conditional only on `hag_gr`) -/

section DischargedMaster

variable {K : Type*} [Field K] {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K))
  [P.IsPrime]

/-- Master with `hSES`/`hcomp`/`hdom` discharged: `ker ≠ ⊥` supplies the
homogeneous `y` (§11 + §1); the SES equation is `singleDrop_hSES`, the
comparison is `singleDrop_hcomp_concrete`, domination is `singleDrop_hdom`.

Explicitly conditional on `hag_gr` only (sibling Hilbert–Serre lane). -/
theorem singleDrop_deg_le_of_ker_ne_bot_of_hag (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hd : 2 ≤ d) (Pgr : ℚ[X])
    (hag_gr : (fun n => ((singleDrop_grHilbert
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) n : ℕ) : ℚ))
      =ᶠ[Filter.atTop] evalFun Pgr)
    (hker : RingHom.ker (polySurjResidue P d g hgen) ≠ ⊥) :
    Pgr.natDegree ≤ d - 2 := by
  obtain ⟨t, y, hym, hyne, hyhom⟩ :=
    hsAssemble_exists_homogeneous_mem_ker _ d g hgen hker
  refine singleDrop_deg_le_of_step P d g hgen hd y t hym hyne hyhom
    (singleDrop_grHilbert (IsLocalRing.maximalIdeal (Localization.AtPrime P)))
    (singleDrop_quotHilbert (IsLocalRing.ResidueField (Localization.AtPrime P))
      d t y hyhom)
    ?hSES ?hcomp Pgr hag_gr (singleDrop_hdom d)
  · intro n hn
    exact singleDrop_hSES (IsLocalRing.ResidueField (Localization.AtPrime P))
      d t y hyhom hyne n hn
  · intro n
    exact singleDrop_hcomp_concrete (R := Localization.AtPrime P)
      d g hgen t y hyhom n hym

/-- The §6-style contrapositive on the discharged master: dim-equality plus
the drop forces `ker = ⊥`.

Explicitly conditional on `hag_gr` + `hdimEq` (`hdimEq` is the
sibling R2' exact-degree result). -/
theorem singleDrop_ker_eq_bot_of_hag (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hd : 2 ≤ d) (Pgr : ℚ[X])
    (hag_gr : (fun n => ((singleDrop_grHilbert
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) n : ℕ) : ℚ))
      =ᶠ[Filter.atTop] evalFun Pgr)
    (hdimEq : ∀ Q : ℚ[X], Q.natDegree ≤ d - 1 →
      (fun n => ((singleDrop_grHilbert
        (IsLocalRing.maximalIdeal (Localization.AtPrime P)) n : ℕ) : ℚ))
        =ᶠ[Filter.atTop] evalFun Q →
      Q.natDegree = d - 1) :
    RingHom.ker (polySurjResidue P d g hgen) = ⊥ := by
  by_contra hker
  have hle :=
    singleDrop_deg_le_of_ker_ne_bot_of_hag P d g hgen hd Pgr hag_gr hker
  have hle' : Pgr.natDegree ≤ d - 1 := le_trans hle (by omega)
  have heq := hdimEq Pgr hle' hag_gr
  omega

end DischargedMaster

#print axioms singleDrop_homogeneous_mem_ker_pos
#print axioms singleDrop_hSES
#print axioms singleDrop_isPolyGrowth_sub
#print axioms singleDrop_quot_exact
#print axioms singleDrop_deg_le_of_ker_ne_bot
#print axioms singleDrop_ker_eq_bot
#print axioms singleDrop_hcomp_concrete
#print axioms singleDrop_hdom
#print axioms singleDrop_deg_le_of_ker_ne_bot_of_hag
#print axioms singleDrop_ker_eq_bot_of_hag

end SingleDropRegularity
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

/-! ## §12. Exact-degree reading of `hdimEq` (hdimEq close-or-narrow)

Closes-or-narrows the `hdimEq` residue of `ker_assemble_ker_eq_bot`
(`KernelAssembly.lean` §3): every rational polynomial of degree
`≤ d - 1` eventually equal to the `gr` Hilbert function has degree
exactly `d - 1`.

* Eisenbud-style leading-coefficient theory (unconditional):
  `singleDrop_natDegree_eq_of_coeff_ne_zero` (a degree bound plus a
  nonzero coefficient at the bound forces exact degree) and
  `singleDrop_poly_eq_of_evalFun_eventuallyEq` (eventual agreement on
  `ℕ` determines the polynomial: the agreement set contains an infinite
  tail image, so `Polynomial.eq_of_infinite_eval_eq` applies).
* `singleDrop_hdimEq_of_grWitness`: the `gr`-side Hilbert witness triple
  (`hle`, `hagW`, `hc`) yields `hdimEq` in exact KerAssemble-hyp shape
  (witness identifies every competitor via uniqueness; the leading
  coefficient reads off `d - 1`).
* `singleDrop_hdimEq_of_hle_gr`: the `hle_gr`-chained form. From the
  R-2a′ lower bound `hle_gr : d ≤ ringKrullDim (grRegular P)`, the
  (proved) upper bound `hub`, and the R-2c′ dimension-to-witness
  implication `hwit`, gives `hdimEq` in exact KerAssemble-hyp shape.
  `hub` is discharged by `mult_ringKrullDim_gr_le` (Multiplicity §7,:509);
  `hle_gr` is the live R-2a′ remainder (`HdimGrMinAtAss`, `UnmixednessAtLengthTwo`
  §8); `hwit` (Hilbert witness from `dim`) is closed (`DimensionToMultiplicity`
  §§1–2). Nothing here assumes `ker = ⊥` (conditional form).
  Circularity note (post-Multiplicity §17): `hle_gr` is goal-strength
  (`mult_hle_gr_iff_ker_eq_bot`:1905 gives `hle_gr ↔ ker = ⊥`), so this
  chained form cannot ground an unconditional route on its own.
  Spelling bridge: `hwit` here is `gr`-side (witness for `singleDrop_grHilbert`);
  the Multiplicity §14 residual is quot-side (witness for `multQuotHilbert`);
  R-2d′ (`mult_quotHilbert_eq_grPieceLength`:1280, cf. `mult_hmult_grSide`
  :1370 / `mult_hdimEq_grSide`:1399) identifies the two spellings.

## Status

* `singleDrop_natDegree_eq_of_coeff_ne_zero`,
  `singleDrop_poly_eq_of_evalFun_eventuallyEq`: unconditional.
* `singleDrop_hdimEq_of_grWitness`: conditional-exact on the `gr`-side
  Hilbert witness triple `[hle, hagW, hc]`.
* `singleDrop_hdimEq_of_hle_gr`: conditional-exact on
  `[hle_gr, hub, hwit]` (`hub` already proved in Multiplicity;
  `hle_gr` = R-2a′ remainder, `UnmixednessAtLengthTwo` §8).

## References

Mathlib (`lean-toolchain` pins `v4.34.0`), all read-only:
* `Algebra/Polynomial/Degree/Operations.lean`:
  `le_natDegree_of_ne_zero`.
* `Algebra/Polynomial/Roots.lean`: `eq_of_infinite_eval_eq`.
* `Data/Set/Finite/Basic.lean`: `infinite_range_of_injective`.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace SingleDropRegularity

open scoped Polynomial

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.NewtonDifferences
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AssociatedGradedRing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjection

section HdimEqExact

variable {K : Type*} [Field K] {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K))
  [P.IsPrime]

/-- Eisenbud-style leading-coefficient reading: a degree bound plus a
nonzero coefficient at the bound forces exact degree.
-/
theorem singleDrop_natDegree_eq_of_coeff_ne_zero (Q : ℚ[X]) (e : ℕ)
    (hle : Q.natDegree ≤ e) (hc : Q.coeff e ≠ 0) :
    Q.natDegree = e :=
  le_antisymm hle (Polynomial.le_natDegree_of_ne_zero hc)

/-- Eventual agreement on naturals determines the polynomial: two rational
polynomials eventually equal on `ℕ` (as `evalFun`) are equal, since the
agreement set contains the infinite image of a tail.
-/
theorem singleDrop_poly_eq_of_evalFun_eventuallyEq {Pw Qw : ℚ[X]}
    (h : evalFun Pw =ᶠ[Filter.atTop] evalFun Qw) : Pw = Qw := by
  apply Polynomial.eq_of_infinite_eval_eq
  have h' : ∀ᶠ n in Filter.atTop, evalFun Pw n = evalFun Qw n := h
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h'
  have hinj : Function.Injective (fun k : ℕ => (((N + k : ℕ)) : ℚ)) := by
    intro a b hab
    have hcast : N + a = N + b := Nat.cast_injective hab
    exact Nat.add_left_cancel hcast
  have himg : Set.range (fun k : ℕ => (((N + k : ℕ)) : ℚ)) ⊆
      {x | Polynomial.eval x Pw = Polynomial.eval x Qw} := by
    rintro x ⟨k, rfl⟩
    have hkk := hN (N + k) (Nat.le_add_right N k)
    simpa [evalFun] using hkk
  exact Set.Infinite.mono himg (Set.infinite_range_of_injective hinj)

/-- `hdimEq` in exact KerAssemble-hyp shape, from a `gr`-side Hilbert
witness: the witness identifies every competitor (uniqueness), and its
leading coefficient reads off degree `d - 1`.

Conditional on exactly the witness triple `[hle, hagW, hc]`. -/
theorem singleDrop_hdimEq_of_grWitness (d : ℕ)
    (Pwit : ℚ[X]) (hle : Pwit.natDegree ≤ d - 1)
    (hagW : (fun n => ((singleDrop_grHilbert
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) n : ℕ) : ℚ))
      =ᶠ[Filter.atTop] evalFun Pwit)
    (hc : Pwit.coeff (d - 1) ≠ 0) :
    ∀ Q : ℚ[X], Q.natDegree ≤ d - 1 →
      (fun n => ((singleDrop_grHilbert
        (IsLocalRing.maximalIdeal (Localization.AtPrime P)) n : ℕ) : ℚ))
        =ᶠ[Filter.atTop] evalFun Q →
      Q.natDegree = d - 1 := by
  intro Q hQ hagQ
  have hPQ : Pwit = Q :=
    singleDrop_poly_eq_of_evalFun_eventuallyEq (hagW.symm.trans hagQ)
  subst hPQ
  exact singleDrop_natDegree_eq_of_coeff_ne_zero Pwit (d - 1) hle hc

/-- `hdimEq` in exact KerAssemble-hyp shape, chained from `hle_gr`: the
R-2a′ lower bound plus the (proved) upper bound give `dim gr = d`, and
the R-2c′ dimension-to-witness implication supplies the witness triple.

Conditional on exactly `[hle_gr, hub, hwit]`. -/
theorem singleDrop_hdimEq_of_hle_gr (d : ℕ)
    (hle_gr : d ≤ ringKrullDim (grRegular P))
    (hub : ringKrullDim (grRegular P) ≤ d)
    (hwit : ringKrullDim (grRegular P) = d →
      ∃ Pwit : ℚ[X], Pwit.natDegree ≤ d - 1 ∧
        (fun n => ((singleDrop_grHilbert
          (IsLocalRing.maximalIdeal (Localization.AtPrime P)) n : ℕ) : ℚ))
          =ᶠ[Filter.atTop] evalFun Pwit ∧ Pwit.coeff (d - 1) ≠ 0) :
    ∀ Q : ℚ[X], Q.natDegree ≤ d - 1 →
      (fun n => ((singleDrop_grHilbert
        (IsLocalRing.maximalIdeal (Localization.AtPrime P)) n : ℕ) : ℚ))
        =ᶠ[Filter.atTop] evalFun Q →
      Q.natDegree = d - 1 := by
  have hdim : ringKrullDim (grRegular P) = d := le_antisymm hub hle_gr
  obtain ⟨Pwit, hle, hagW, hc⟩ := hwit hdim
  exact singleDrop_hdimEq_of_grWitness P d Pwit hle hagW hc

end HdimEqExact

#print axioms singleDrop_natDegree_eq_of_coeff_ne_zero
#print axioms singleDrop_poly_eq_of_evalFun_eventuallyEq
#print axioms singleDrop_hdimEq_of_grWitness
#print axioms singleDrop_hdimEq_of_hle_gr

end SingleDropRegularity
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
