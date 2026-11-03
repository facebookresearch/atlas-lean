/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.HilbertWitnessNarrowing

/-!
# Kernel chain: `ker polySurjResidue = ⊥` from minimality (mechanical chaining)

No new mathematics: this file threads hypotheses exactly, chaining the two
Witness masters:

* `kwit_hmult_of_minimal` (`HilbertWitnessNarrowing.lean`, conditional-exact on
  `[hmin, KwitNoHomRel]` + `2 ≤ d`) feeds `hmult`;
* `kwit_ker_eq_bot_of_hmult` (`HilbertWitnessNarrowing.lean`, conditional-exact on
  `[hmult]` + `2 ≤ d`) closes `ker = ⊥`.

`hmin` is stated in the same form P1 used
(`HilbertWitnessNarrowing.lean`: `d ≤ spanFinrank 𝔪`; for `d = 1`).
The `hdimEq` hyp-shape consumed downstream is
`ker_assemble_ker_eq_bot` (`KernelAssembly.lean`).

## Status

* `ker_chain_ker_eq_bot`: conditional-exact on `[hmin, KwitNoHomRel]`
  (+ `2 ≤ d`).
* `ker_chain_hmult_one`: conditional-exact on `[hmin]` (the `d = 1`
  analytic corollary via `kwit_hmult_of_minimal_one`; the
  `ker = ⊥` close needs `2 ≤ d` throughout, so `d = 1` stops at `hmult`).

## Residual register (verbatim)

`KwitNoHomRel P d g hgen`: `ker` contains no nonzero homogeneous relation
of degree `≥ 1` — the exact remainder given `hmin`
(`kwit_hmult_iff_noHomRel_of_minimal`, `HilbertWitnessNarrowing.lean`).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace KernelChain

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.NewtonDifferences
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjection
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.MultiplicityNonvanishing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.HilbertWitnessNarrowing

section KerChain

variable {K : Type*} [Field K] {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K))
  [P.IsPrime]

/-- `ker = ⊥` from minimality plus the exact homogeneous-relations residual:
`kwit_hmult_of_minimal` (:928) supplies `hmult`, `kwit_ker_eq_bot_of_hmult`
(:462) closes the kernel. No new math; exact hyp threading.

Conditional on exactly `[hmin, KwitNoHomRel]` (+ `2 ≤ d`). -/
theorem ker_chain_ker_eq_bot (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hd : 2 ≤ d)
    (hmin : d ≤ (IsLocalRing.maximalIdeal
      (Localization.AtPrime P)).spanFinrank)
    (hNoHom : KwitNoHomRel P d g hgen) :
    RingHom.ker (polySurjResidue P d g hgen) = ⊥ := by
  have hmult := kwit_hmult_of_minimal P d g hgen hd hmin hNoHom
  exact kwit_ker_eq_bot_of_hmult P d g hgen hd hmult

/-- `d = 1` analytic corollary on `[hmin]` alone via
`kwit_hmult_of_minimal_one` (:884). States `hmult`, not `ker = ⊥`: every
`ker`-close in the chain needs `2 ≤ d`.

Conditional on exactly `[hmin]`. -/
theorem ker_chain_hmult_one
    (g : Fin 1 → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hmin : 1 ≤ (IsLocalRing.maximalIdeal
      (Localization.AtPrime P)).spanFinrank) :
    ¬ seqDiff (1 - 1) (fun n => ((multQuotHilbert
      (IsLocalRing.ResidueField (Localization.AtPrime P)) 1
      (RingHom.ker (polySurjResidue P 1 g hgen)) (n + 1) : ℕ) : ℚ))
      =ᶠ[Filter.atTop] 0 :=
  kwit_hmult_of_minimal_one P g hgen hmin

end KerChain

#print axioms ker_chain_ker_eq_bot
#print axioms ker_chain_hmult_one

end KernelChain
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

/-!
# Kernel chain appendix: high-residual update + `d = 1` bridge

Part (1): `ker_chain_ker_eq_bot_high` threads the tighter Witness master
`kwit_hmult_of_minimal_high` (`HilbertWitnessNarrowing.lean`, conditional-exact on
`[hmin, KwitNoHomRelHigh]`) into `kwit_ker_eq_bot_of_hmult`.

Part (2): `ker_chain_ker_eq_bot_one` closes `ker = ⊥` for `d = 1` on `[hmin]`
alone. If `ker ≠ ⊥`, ker-homogeneity gives a nonzero homogeneous `q ∈ ker`
of some degree `i`; in one variable `q = c * X^i`
(`ker_chain_fin1_homog_eq`), so `X^i ∈ ker`. If `i = 0` then `1 ∈ ker`,
killing `Hq 0`, against `kwit_quotHilbert_ne_zero_of_minimal`; if `i ≥ 1`
then every homogeneous degree-`N` polynomial (`N ≥ i`) is a multiple of
`X^i`, so every large quotient piece vanishes and `Hq` is eventually `0`,
against `kwit_hmult_of_minimal_one`.

## Status

* `ker_chain_ker_eq_bot_high`: conditional-exact on `[hmin, KwitNoHomRelHigh]`
  (+ `2 ≤ d`).
* `ker_chain_ker_eq_bot_one`: conditional-exact on `[hmin]`.

## Residual register (verbatim)

`KwitNoHomRelHigh P d g hgen`: `ker` contains no nonzero homogeneous relation
of degree `≥ 2` — the exact remainder given `hmin`
(`kwit_hmult_iff_noHomRelHigh_of_minimal`, `HilbertWitnessNarrowing.lean`).
For `d = 1` there is no remainder: `ker = ⊥` on `[hmin]` alone.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace KernelChain

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.NewtonDifferences
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjection
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.MultiplicityNonvanishing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.HilbertWitnessNarrowing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjectionInjective
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.LengthFramework

section KerChainHigh

variable {K : Type*} [Field K] {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K))
  [P.IsPrime]

/-- `ker = ⊥` from minimality plus the high-degree residual only:
`kwit_hmult_of_minimal_high` (:1465) supplies `hmult`,
`kwit_ker_eq_bot_of_hmult` (:462) closes the kernel. Tighter than
`ker_chain_ker_eq_bot` (degree-1 relations are discharged by minimality).

Conditional on exactly `[hmin, KwitNoHomRelHigh]` (+ `2 ≤ d`). -/
theorem ker_chain_ker_eq_bot_high (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hd : 2 ≤ d)
    (hmin : d ≤ (IsLocalRing.maximalIdeal
      (Localization.AtPrime P)).spanFinrank)
    (hHigh : KwitNoHomRelHigh P d g hgen) :
    RingHom.ker (polySurjResidue P d g hgen) = ⊥ := by
  have hmult := kwit_hmult_of_minimal_high P d g hgen hd hmin hHigh
  exact kwit_ker_eq_bot_of_hmult P d g hgen hd hmult

/-- A `Fin 1` exponent of degree `N` is the single monomial exponent. -/
theorem ker_chain_fin1_single_of_degree (d : Fin 1 →₀ ℕ) (N : ℕ)
    (h : d.degree = N) :
    d = Finsupp.single 0 N := by
  have hdecomp : d = Finsupp.single 0 (d 0) := by
    apply Finsupp.ext
    intro i
    have hi : i = 0 := Subsingleton.elim i 0
    rw [hi]
    exact Finsupp.single_eq_same.symm
  have hd0 : d 0 = N := by
    have h2 : (Finsupp.single (0 : Fin 1) (d 0)).degree = N := by
      rw [← hdecomp]
      exact h
    rw [Finsupp.degree_single] at h2
    exact h2
  rw [hdecomp, hd0]

/-- Homogeneous polynomials in one variable are monomials. -/
theorem ker_chain_fin1_homog_eq {κ : Type*} [Field κ]
    (x : MvPolynomial (Fin 1) κ) (N : ℕ)
    (hx : x.IsHomogeneous N) :
    x = MvPolynomial.monomial (Finsupp.single 0 N)
      (x.coeff (Finsupp.single 0 N)) := by
  have hx' : MvPolynomial.IsWeightedHomogeneous (1 : Fin 1 → ℕ) x N := hx
  refine MvPolynomial.IsWeightedHomogeneous.eq_monomial_of_unique_weight
    (d₀ := Finsupp.single (0 : Fin 1) N) hx' (fun d hd => ?_)
  have h : Finsupp.degree d = Finsupp.weight (fun _ => 1) d :=
    congrArg (fun f : (Fin 1 →₀ ℕ) →+ ℕ => f d)
      Finsupp.degree_eq_weight_one
  have hdeg : d.degree = N := by
    rw [h]
    exact hd
  exact ker_chain_fin1_single_of_degree d N hdeg

/-- A nonzero homogeneous element of an ideal yields the pure power `X^i`. -/
theorem ker_chain_fin1_X_pow_mem {κ : Type*} [Field κ]
    {ker : Ideal (MvPolynomial (Fin 1) κ)}
    {q : MvPolynomial (Fin 1) κ} {i : ℕ}
    (hmem : q ∈ ker) (hhom : q.IsHomogeneous i) (hne : q ≠ 0) :
    MvPolynomial.X (0 : Fin 1) ^ i ∈ ker := by
  have hq := ker_chain_fin1_homog_eq q i hhom
  have hcne : q.coeff (Finsupp.single 0 i) ≠ 0 := by
    intro hz
    apply hne
    rw [hq, hz, MvPolynomial.monomial_zero]
  have hunit : IsUnit (MvPolynomial.C (q.coeff (Finsupp.single 0 i))) :=
    IsUnit.map (MvPolynomial.C (σ := Fin 1)) (isUnit_iff_ne_zero.mpr hcne)
  have hmem2 : MvPolynomial.C (q.coeff (Finsupp.single 0 i)) *
      MvPolynomial.X 0 ^ i ∈ ker := by
    rw [MvPolynomial.C_mul_X_pow_eq_monomial, ← hq]
    exact hmem
  exact (ker.unit_mul_mem_iff_mem hunit).mp hmem2

/-- `X^i ∈ ker` kills every quotient piece of degree `≥ i`: every homogeneous
degree-`N` polynomial in one variable is a multiple of `X^i`. -/
theorem ker_chain_fin1_kerPiece_top {κ : Type*} [Field κ]
    (ker : Ideal (MvPolynomial (Fin 1) κ))
    {i N : ℕ} (hle : i ≤ N)
    (hXi : MvPolynomial.X (0 : Fin 1) ^ i ∈ ker) :
    multKerPiece κ 1 ker N = ⊤ := by
  ext x
  simp only [Submodule.mem_top, iff_true]
  have hsub : (MvPolynomial.homogeneousSubmodule (Fin 1) κ N).subtype x =
      x.val := rfl
  have hxhom : x.val.IsHomogeneous N :=
    (MvPolynomial.mem_homogeneousSubmodule N x.val).mp x.property
  have hx := ker_chain_fin1_homog_eq (x.val) N hxhom
  have hadd : Finsupp.single (0 : Fin 1) (N - i) + Finsupp.single (0 : Fin 1) i
      = Finsupp.single (0 : Fin 1) N := by
    rw [← Finsupp.single_add]
    have hNi : N - i + i = N := by omega
    rw [hNi]
  have hfactor : x.val = MvPolynomial.monomial (Finsupp.single 0 (N - i))
      (x.val.coeff (Finsupp.single 0 N)) * MvPolynomial.X 0 ^ i := by
    conv_lhs => rw [hx]
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul_monomial,
      hadd, mul_one]
  have hmem : x.val ∈ ker := by
    rw [hfactor]
    exact ker.mul_mem_left _ hXi
  unfold multKerPiece
  rw [Submodule.mem_comap, hsub, Submodule.restrictScalars_mem]
  exact hmem

/-- A full kernel piece kills the quotient Hilbert value. -/
theorem ker_chain_quotHilbert_eq_zero_of_piece_top {κ : Type*} [Field κ]
    {d : ℕ} {ker : Ideal (MvPolynomial (Fin d) κ)} {N : ℕ}
    (h : multKerPiece κ d ker N = ⊤) :
    multQuotHilbert κ d ker N = 0 := by
  unfold multQuotHilbert
  rw [h]
  have : Subsingleton (↥(MvPolynomial.homogeneousSubmodule (Fin d) κ N) ⧸
      (⊤ : Submodule κ
        ↥(MvPolynomial.homogeneousSubmodule (Fin d) κ N))) :=
    ⟨fun a b => by
      obtain ⟨a', rfl⟩ := Submodule.Quotient.mk_surjective _ a
      obtain ⟨b', rfl⟩ := Submodule.Quotient.mk_surjective _ b
      have ha : (Submodule.Quotient.mk a' : _ ⧸
          (⊤ : Submodule κ
            ↥(MvPolynomial.homogeneousSubmodule (Fin d) κ N))) = 0 := by
        rw [Submodule.Quotient.mk_eq_zero]
        exact Submodule.mem_top
      have hb : (Submodule.Quotient.mk b' : _ ⧸
          (⊤ : Submodule κ
            ↥(MvPolynomial.homogeneousSubmodule (Fin d) κ N))) = 0 := by
        rw [Submodule.Quotient.mk_eq_zero]
        exact Submodule.mem_top
      rw [ha, hb]⟩
  exact finLength_zero_of_subsingleton

/-- A trivial kernel has full kernel pieces. -/
theorem ker_chain_piece_top_of_ker_top {κ : Type*} [Field κ] {d : ℕ}
    {ker : Ideal (MvPolynomial (Fin d) κ)} (N : ℕ) (h : ker = ⊤) :
    multKerPiece κ d ker N = ⊤ := by
  unfold multKerPiece
  rw [h]
  simp

/-- `d = 1` bridge: `ker = ⊥` on `[hmin]` alone. If `ker ≠ ⊥`,
ker-homogeneity plus the one-variable monomial shape gives `X^i ∈ ker`;
`i = 0` kills `Hq 0` and `i ≥ 1` kills all large `Hq`, both against the
`d = 1` nonvanishing (`kwit_hmult_of_minimal_one`,
`kwit_quotHilbert_ne_zero_of_minimal`).

Conditional on exactly `[hmin]`. -/
theorem ker_chain_ker_eq_bot_one
    (g : Fin 1 → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hmin : 1 ≤ (IsLocalRing.maximalIdeal
      (Localization.AtPrime P)).spanFinrank) :
    RingHom.ker (polySurjResidue P 1 g hgen) = ⊥ := by
  have hmult := kwit_hmult_of_minimal_one P g hgen hmin
  have hne0 : ∀ n, multQuotHilbert
      (IsLocalRing.ResidueField (Localization.AtPrime P)) 1
      (RingHom.ker (polySurjResidue P 1 g hgen)) n ≠ 0 :=
    fun n => kwit_quotHilbert_ne_zero_of_minimal P 1 g hgen hmin (le_refl 1) n
  by_contra hne
  obtain ⟨p, hpmem, hpne⟩ := (Submodule.ne_bot_iff _).mp hne
  have hcomp : ∃ i ∈ Finset.range (p.totalDegree + 1),
      (MvPolynomial.homogeneousComponent i) p ≠ 0 := by
    by_contra hall
    have hall' : ∀ i ∈ Finset.range (p.totalDegree + 1),
        (MvPolynomial.homogeneousComponent i) p = 0 := by
      intro i hi
      by_contra hne2
      exact hall ⟨i, hi, hne2⟩
    have hsum : p = ∑ i ∈ Finset.range (p.totalDegree + 1),
        (MvPolynomial.homogeneousComponent i) p :=
      (MvPolynomial.sum_homogeneousComponent p).symm
    apply hpne
    rw [hsum]
    exact Finset.sum_eq_zero hall'
  obtain ⟨i, _, hine⟩ := hcomp
  have hcmem := hsAssemble_ker_homogeneousComponent_mem
    (IsLocalRing.maximalIdeal (Localization.AtPrime P)) 1 g hgen p hpmem i
  have hchom := MvPolynomial.homogeneousComponent_isHomogeneous i p
  have hXi : MvPolynomial.X (0 : Fin 1) ^ i ∈
      RingHom.ker (polySurjResidue P 1 g hgen) :=
    ker_chain_fin1_X_pow_mem hcmem hchom hine
  by_cases hi0 : i = 0
  · subst hi0
    simp only [pow_zero] at hXi
    have htop : RingHom.ker (polySurjResidue P 1 g hgen) = ⊤ :=
      (RingHom.ker (polySurjResidue P 1 g hgen)).eq_top_of_isUnit_mem hXi
        isUnit_one
    have hQ0 := ker_chain_quotHilbert_eq_zero_of_piece_top
      (ker_chain_piece_top_of_ker_top 0 htop)
    exact hne0 0 hQ0
  · have hvan : (fun n => ((multQuotHilbert
          (IsLocalRing.ResidueField (Localization.AtPrime P)) 1
          (RingHom.ker (polySurjResidue P 1 g hgen)) (n + 1) : ℕ) : ℚ))
        =ᶠ[Filter.atTop] 0 := by
      refine Filter.eventually_atTop.mpr ⟨i, fun n hn => ?_⟩
      simp only [Pi.zero_apply]
      have hN : i ≤ n + 1 := by omega
      have hQ := ker_chain_quotHilbert_eq_zero_of_piece_top
        (ker_chain_fin1_kerPiece_top _ hN hXi)
      rw [hQ, Nat.cast_zero]
    have h11 : (1 : ℕ) - 1 = 0 := rfl
    rw [h11, seqDiff_zero] at hmult
    exact hmult hvan

end KerChainHigh

#print axioms ker_chain_ker_eq_bot_high
#print axioms ker_chain_ker_eq_bot_one

end KernelChain
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

/-!
# Minimality appendix: `hmin` discharged from sop data (proof)

Per-prime minimality for the `d`-split in
`hkerAtAss_of_hmin_hdimEq` (`Geometry/K2UnmixednessEndgame.lean`). The per-prime `d` at
the use site (`depthEqDimAt_of_hker_atPrime`, `Geometry/K2UnmixednessEndgame.lean`)
comes from `grlift_sop_exists` (`Regularity/Koszul/GradedLift.lean`), which
provides `(d, g, hgen, hd)` with `hd : d = spanFinrank 𝔪` — a propositional
equation, not a definitional one, so the bridge is `le_of_eq hd` / `hd ▸`,
not `rfl`.

* `ker_chain_hmin_of_sop`: general `hmin` (`d ≤ spanFinrank 𝔪`, the
  `HilbertWitnessNarrowing.lean` shape) from the sop equation. Same statement as
  `grlift_sop_minimal` (`GradedLift.lean`); restated here so the
  KerChain `d`-split feeds need no new import.
* `ker_chain_hmin_one_of_sop`: the `HminOneAtAss` per-prime shape
  (`1 ≤ spanFinrank 𝔪`, `Geometry/K2UnmixednessEndgame.lean`) from the sop equation
  plus the `d ≥ 1` branch hypothesis. Feeds `ker_chain_ker_eq_bot_one`
   in the `d = 1` branch; the `d = 0` branch needs no `hmin`
  (`hsAssemble_ker_eq_bot_zero` is unconditional).
* `ker_chain_one_le_spanFinrank_of_ne_bot`: `1 ≤ spanFinrank 𝔪` from
  `𝔪 ≠ ⊥` (the `spanFinrank`-zero characterization). Prime-agnostic half
  of universal `HminOneAtAss`; the other half (`𝔪(R_Q) ≠ ⊥` per
  `Q ∈ Ass(R ⧸ J)`) lives downstream (proved; this file cannot
  import `Geometry/K2UnmixednessEndgame` — pointers in the register below).

## Status

* `ker_chain_hmin_of_sop`: unconditional (conditional-form on the sop
  equation `hd`).
* `ker_chain_hmin_one_of_sop`: unconditional (conditional-form on
  `[hd, 1 ≤ d]`).
* `ker_chain_one_le_spanFinrank_of_ne_bot`: unconditional
  (conditional-form on `[𝔪 ≠ ⊥]`).

## Residual register (verbatim)

Universal `HminOneAtAss` (`Geometry/K2UnmixednessEndgame.lean`) per `Q ∈ Ass(R ⧸ J)`
with sop-`d = 0` (`Q = ⊥`): `J ≤ Q` + `J ≠ ⊥` + `(Q ≠ ⊥ → 𝔪(R_Q) ≠ ⊥)`
(localization image of a nonzero prime; none attempted here — all closed
Downstream: `Geometry/K2UnmixednessEndgame.lean` (:601),
`Geometry/UnmixednessAtLengthTwo.lean` (:255,:270)).
The `𝔪 ≠ ⊥ → 1 ≤ spanFinrank` link is above.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace KernelChain

section KerChainMinimality

variable {K : Type*} [Field K] {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K))
  [P.IsPrime]

/-- General `hmin` from the sop equation: the per-prime `d` from
`grlift_sop_exists` (`GradedLift.lean`) satisfies `d = spanFinrank 𝔪`,
hence `d ≤ spanFinrank 𝔪` (the `HilbertWitnessNarrowing.lean` shape). The equation
is propositional, so this is `le_of_eq`, not `rfl`.
-/
theorem ker_chain_hmin_of_sop (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (_hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hd : d = (IsLocalRing.maximalIdeal
      (Localization.AtPrime P)).spanFinrank) :
    d ≤ (IsLocalRing.maximalIdeal (Localization.AtPrime P)).spanFinrank :=
  le_of_eq hd

/-- The `HminOneAtAss` per-prime shape from sop data in the `d ≥ 1` branch:
`hd : d = spanFinrank 𝔪` plus `1 ≤ d` gives `1 ≤ spanFinrank 𝔪`
(`Geometry/K2UnmixednessEndgame.lean`). Feeds `ker_chain_ker_eq_bot_one`.
-/
theorem ker_chain_hmin_one_of_sop (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (_hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hd : d = (IsLocalRing.maximalIdeal
      (Localization.AtPrime P)).spanFinrank)
    (hd1 : 1 ≤ d) :
    1 ≤ (IsLocalRing.maximalIdeal (Localization.AtPrime P)).spanFinrank := by
  rw [← hd]
  exact hd1

/-- `1 ≤ spanFinrank 𝔪` from `𝔪 ≠ ⊥`: Noetherian `FG` plus the
`spanFinrank`-zero characterization
(`Submodule.spanFinrank_eq_zero_iff_eq_bot`,
`Mathlib/Algebra/Module/SpanRank.lean`; `Ideal.fg_of_isNoetherianRing`,
`Mathlib/RingTheory/Noetherian/Defs.lean` — same pair as
`regularLocal_dimZero_isField`, `Geometry/LocalMultiplicity.lean`).
-/
theorem ker_chain_one_le_spanFinrank_of_ne_bot
    (hne : IsLocalRing.maximalIdeal (Localization.AtPrime P) ≠ ⊥) :
    1 ≤ (IsLocalRing.maximalIdeal (Localization.AtPrime P)).spanFinrank := by
  have hfg := Ideal.fg_of_isNoetherianRing
    (IsLocalRing.maximalIdeal (Localization.AtPrime P))
  have h0 : (IsLocalRing.maximalIdeal
    (Localization.AtPrime P)).spanFinrank ≠ 0 := by
    intro hz
    exact hne ((Submodule.spanFinrank_eq_zero_iff_eq_bot hfg).mp hz)
  omega

end KerChainMinimality

#print axioms ker_chain_hmin_of_sop
#print axioms ker_chain_hmin_one_of_sop
#print axioms ker_chain_one_le_spanFinrank_of_ne_bot

end KernelChain
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
