/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.DFinsupp.BigOperators
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.AssociatedGradedRing
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.NewtonDifferences
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.LengthFramework
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.FiltrationStability
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.YSopStep
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedSurjection

/-!
# Dim-equality forces the graded surjection injective (M4c-ii assembly)

Final assembly of sub-plan M4c-ii (the Hilbert–Samuel bypass): dim-equality
forces the M4b surjection `polySurjResidue` injective, so `ker = ⊥` and hence
`gr(R_P) ≅ κ[t₁..t_d]` with `κ = R_P / 𝔪` the residue field and `d = dim`.
This file proves the assembly logic — that the five proved inputs plus
dim-equality formally entail `ker = ⊥` and the polynomial identification —
with the remaining analytic inputs (growth bounds, SES data, dim-equality
itself) as explicit hypotheses, following the repo's conditional-explicit
pattern (cf. `ExtComparison`, `KoszulConeSESResidual`).

## The five inputs and their roles

* `NewtonDifferences` (§1 here): the `IsPolyGrowth` interface reads growth degrees
  off Hilbert functions — nonvanishing pins the degree exactly
  (`growth_exact_of_not_vanishing`), vanishing drops it strictly
  (`growth_drop_of_vanishing`).
* `YSopStep` (§2 here): `ysop_step` (Hilbert-drop) turns the per-prime
  inputs plus the SES equation plus the domain growth bound into the
  quotient vanishing that forces the quotient growth degree down
  (`hsAssemble_quotDegree_lt`).
* `LengthFramework` (§3 here): the `finLength` framework discharges the SES
  equation — per-rung SES additivity normalizes to the `hses` input shape
  (`hsAssemble_hses_of_additivity`), and lengths drop under further
  quotients (`hsAssemble_finLength_quot_le`).
* `FiltrationStability` (§4 here): the Krull injectivity corollary kills
  embedded kernels at `R_P`, supplying the injectivity half of SES
  exactness (`hsAssemble_injective_of_ker_le_adic`,
  `hsAssemble_ker_eq_bot_of_le_adic`).
* `GradedSurjection` (§5–6 here): the quotient-kernel form
  `polySurjResidue_quotKerEquiv` turns `ker = ⊥` into the graded
  identification `S ≃+* grRegular P` (`hsAssemble_isoOfKerEqBot`).

## The master chain (§6)

`hsAssemble_ker_eq_bot`: from the domain growth bound (`hF`), dim-equality
(`hdimEq`: the quotient growth degree equals `e`), the generator/dimension
bridge (`hdim`: `e + 1 = d` plus `hd_pos`: `1 < d`), and the analytic
residual (`hdrop`: a nonzero
kernel supplies a `y`-step — per-prime inputs, SES equation, quotient growth
bound), contrapositive through the §2 degree gap gives `ker = ⊥`.
`hsAssemble_grEquiv` adds the §5 identification.

## Explicit hypotheses (residuals) and their discharge routes

* `hF`: domain Hilbert function has growth `≤ e` — closed by §13
  (`hsAssemble_hF`, via the stars-and-bars identity and `chooseFun`).
* `hdimEq`: quotient growth degree is exactly `e` — via `quotKerEquiv`
  length transfer plus `dim gr = dim R = d`.
* `hdrop`: nonzero kernel yields the drop shape (homogeneous
  non-zerodivisor in `ker`, mul-by-`y` SES on graded pieces, quotient
  growth bound) — needs homogeneity of `ker` plus the graded SES.
* `hdim`: `e + 1 = d` — closed by §8 (take `e := d - 1`).
* `hd_pos`: `1 < d` — forces `e ≥ 1`, which the strict-drop reading
  (`growth_drop_of_vanishing`) needs; the `e = 0` case is §7 and the
  `d = 0` case is §14 (unconditional masters).

## Consumption map for `GradedLift` (file 6)

File 6 consumes `hsAssemble_ker_eq_bot` (kernel triviality over
`κ = IsLocalRing.ResidueField R_P` with `d` generators) and
`hsAssemble_grEquiv` (the `MvPolynomial (Fin d) κ ≃+* grRegular P`
identification), discharging or propagating the five explicit hypotheses
(: `hF` closed by §13, `hdim` closed by §8; `d = 0` unconditional
by §14, `d = 1` Artinian needing only `hnonvan`/`hdrop₀`).

## References

Mathlib (`lean-toolchain` pins `v4.34.0`), all read-only:
* `Algebra/Polynomial/Degree/Defs.lean`: `Polynomial.coeff_natDegree`,
  `Polynomial.natDegree_zero`, `Polynomial.leadingCoeff_ne_zero`.
* `Algebra/Polynomial/Degree/Operations.lean`:
  `Polynomial.coeff_eq_zero_of_natDegree_lt`.
* `Data/Nat/Factorial/Basic.lean`: `Nat.factorial_ne_zero`.
* `Order/Filter/AtTopBot/Basic.lean`: `Filter.eventually_atTop`.
* `Order/Filter/Basic.lean`: `Filter.EventuallyEq.symm/trans`.
* `RingTheory/Ideal/Quotient/Operations.lean`: `RingEquiv.quotientBot`.
* `RingTheory/Ideal/Quotient/Operations.lean`: quotients by equal ideals
  (via `RingHom.quotientKerEquivOfSurjective` in `GradedSurjection`).

Project (read-only):
* `Regularity/Multiplicity/NewtonDifferences.lean` (M4c-ii part 1: `seqDiff`,
  `IsPolyGrowth`, `seqDiff_eventuallyEq_const_of_eventuallyEq_evalFun`).
* `Regularity/Koszul/YSopStep.lean` (M4c-ii part 3: `ysop_step`,
  `finLength_ses_of_injective`).
* `Regularity/Koszul/LengthFramework.lean` (M4c-i: `finLength`,
  `finLength_add_of_submodule`).
* `Regularity/Koszul/FiltrationStability.lean` (M4c-ii part 2:
  `injective_of_ker_le_adic`, `krull_atPrime_ker_eq_bot`,
  `maximalIdeal_atPrime_ne_top`, `isNoetherianRing_atPrime`).
* `Regularity/Koszul/GradedSurjection.lean` (M4b: `polySurjResidue`,
  `polySurjResidue_quotKerEquiv`).
* `Regularity/Koszul/AssociatedGradedRing.lean` (step A4(i): `grRegular`).

## Status

* §1–§5: unconditional (proved from the five inputs + Mathlib).
* §6 (`hsAssemble_ker_eq_bot`, `hsAssemble_grEquiv`): conditional-explicit
  on `hF`, `hdimEq`, `hdrop`, `hdim`, `hd_pos` (residuals listed above).
* §7 (e=0): Artinian masters conditional-explicit on `hF₀`, `hnonvan`,
  `hdrop₀` (no `hdim`/`hd_pos`). §8 (`hdim`): `_of_dim` masters drop
  `hdim` (closed). §9 (`hF` analytic half): unconditional; §10
  (`hdimEq`↔`hmult`): factoring unconditional, masters take `hmult`;
  §11 (`hdrop` homogeneity half): unconditional-given-inputs, masters
  take `hprin`. §12: doc-only R1–R4 register.
* §13 (R1: `hsAssemble_hF`): unconditional. §14 (R4): `d = 0` masters
  unconditional; `d = 1` Artinian masters conditional-explicit on
  `hnonvan`, `hdrop₀` (`hF₀` closed).
-/

open scoped Polynomial

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace GradedSurjectionInjective

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.NewtonDifferences
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.LengthFramework
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.FiltrationStability
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.YSopStep
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjection
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AssociatedGradedRing

/-! ## §1. Degree reading from the Newton interface -/

/-- Nonvanishing pins the growth degree exactly: a degree-`≤ e` Hilbert
function whose `e`-th difference does not vanish eventually agrees with a
rational polynomial of degree exactly `e` (the multiplicity reading).
-/
theorem growth_exact_of_not_vanishing {F : ℕ → ℚ} {e : ℕ}
    (h : IsPolyGrowth F e) (hne : ¬ seqDiff e F =ᶠ[Filter.atTop] 0) :
    ∃ P : ℚ[X], P.natDegree = e ∧ F =ᶠ[Filter.atTop] evalFun P := by
  obtain ⟨P, hd, hP⟩ := h
  have hconst := seqDiff_eventuallyEq_const_of_eventuallyEq_evalFun P e hP hd
  have hcoeff : P.coeff e ≠ 0 := by
    intro hc
    apply hne
    have hzero : (fun _ : ℕ => (Nat.factorial e : ℚ) * P.coeff e)
        = (0 : ℕ → ℚ) := by
      funext n
      simp only [hc, mul_zero, Pi.zero_apply]
    rwa [hzero] at hconst
  have hle : e ≤ P.natDegree := by
    by_contra hlt
    have hlt' : P.natDegree < e := lt_of_not_ge hlt
    exact hcoeff (Polynomial.coeff_eq_zero_of_natDegree_lt hlt')
  exact ⟨P, le_antisymm hd hle, hP⟩

/-- Vanishing drops the growth degree strictly (for `e > 0`): a degree-`≤ e`
Hilbert function whose `e`-th difference vanishes eventually agrees with a
rational polynomial of degree `< e`. This is the degree/dimension reading
the dim-equality contradiction feeds on.
-/
theorem growth_drop_of_vanishing {Fq : ℕ → ℚ} {e : ℕ} (he : 0 < e)
    (h : IsPolyGrowth Fq e) (hvan : seqDiff e Fq =ᶠ[Filter.atTop] 0) :
    ∃ Q : ℚ[X], Q.natDegree ≤ e ∧
      Fq =ᶠ[Filter.atTop] evalFun Q ∧ Q.natDegree < e := by
  obtain ⟨Q, hd, hQ⟩ := h
  have hconst := seqDiff_eventuallyEq_const_of_eventuallyEq_evalFun Q e hQ hd
  have hcz : (Nat.factorial e : ℚ) * Q.coeff e = 0 := by
    have h00 : (fun _ => (Nat.factorial e : ℚ) * Q.coeff e)
        =ᶠ[Filter.atTop] (0 : ℕ → ℚ) := hconst.symm.trans hvan
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h00
    have hNN := hN N le_rfl
    simpa using hNN
  have hfact : (Nat.factorial e : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero e)
  have hcoeff : Q.coeff e = 0 := by
    rcases mul_eq_zero.mp hcz with h | h
    · exact absurd h hfact
    · exact h
  refine ⟨Q, hd, hQ, ?_⟩
  rcases eq_or_ne Q 0 with rfl | hQne
  · rw [Polynomial.natDegree_zero]
    exact he
  · have hne' : Q.natDegree ≠ e := by
      intro hcon
      have hlc : Q.coeff e = Q.leadingCoeff := by
        rw [← hcon, Polynomial.coeff_natDegree]
      rw [hlc] at hcoeff
      exact Polynomial.leadingCoeff_ne_zero.mpr hQne hcoeff
    omega

/-! ## §2. The Hilbert-drop pipeline through `ysop_step` -/

section QuotDrop

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- The drop pipeline: `ysop_step` turns the per-prime inputs, the SES
equation, and the domain growth bound into the quotient vanishing, and §1
reads off the strict degree gap for the quotient Hilbert function.
-/
theorem hsAssemble_quotDegree_lt (J : Ideal R) (H Hq : ℕ → ℕ) (e : ℕ)
    (he : 0 < e)
    (hne : ∀ Q ∈ J.minimalPrimes, Q ≠ IsLocalRing.maximalIdeal R)
    (hle : ∀ A ∈ associatedPrimes R (R ⧸ J),
      ¬ IsLocalRing.maximalIdeal R ≤ A)
    (hses : ∀ n, Hq (n + 1) + H n = H (n + 1))
    (hF : IsPolyGrowth (fun n => ((H n : ℕ) : ℚ)) e)
    (hFq : IsPolyGrowth (fun n => ((Hq (n + 1) : ℕ) : ℚ)) e) :
    ∃ Q : ℚ[X], Q.natDegree ≤ e ∧
      (fun n => ((Hq (n + 1) : ℕ) : ℚ)) =ᶠ[Filter.atTop] evalFun Q ∧
      Q.natDegree < e := by
  obtain ⟨_y, _hym, _hymin, _hreg, hvan⟩ :=
    ysop_step J e H Hq hne hle hses hF
  exact growth_drop_of_vanishing he hFq hvan

end QuotDrop

/-! ## §3. The `finLength` SES discharge route -/

/-- Per-rung SES additivity normalizes to the `hses` input shape: the
`finLength B = finLength A + finLength C` output of
`finLength_ses_of_injective` (along the mul-by-`y` injection supplied by
§4) is the SES equation `ysop_step` consumes.
-/
theorem hsAssemble_hses_of_additivity (H Hq : ℕ → ℕ)
    (hadd : ∀ n, H (n + 1) = H n + Hq (n + 1)) :
    ∀ n, Hq (n + 1) + H n = H (n + 1) := by
  intro n
  rw [hadd n, add_comm]

/-- Lengths drop under further quotients: the pointwise half of Hilbert
comparison along `S ⧸ ker` versus intermediate quotients.
-/
theorem hsAssemble_finLength_quot_le {A M : Type*} [Ring A] [AddCommGroup M]
    [Module A M] (hM : IsFiniteLength A M) (N : Submodule A M) :
    finLength A (M ⧸ N) ≤ finLength A M := by
  have hadd := finLength_add_of_submodule hM N
  omega

/-! ## §4–§6. The `R_P` assembly -/

section Assemble

variable {K : Type*} [Field K] {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K))
  [P.IsPrime]

/-- Krull embedded-kernel killer at `R_P`: a submodule contained in every
adic power is `⊥`. This supplies the injectivity half of the mul-by-`y`
SES exactness behind the `hses` component of `hdrop`.
-/
theorem hsAssemble_ker_eq_bot_of_le_adic
    (N : Submodule (Localization.AtPrime P) (Localization.AtPrime P))
    (hN : N ≤ ⨅ i,
      IsLocalRing.maximalIdeal (Localization.AtPrime P) ^ i • ⊤) :
    N = ⊥ :=
  krull_atPrime_ker_eq_bot P N hN

/-- Krull injectivity corollary at `R_P`: a map whose kernel lies in every
adic power is injective — the exactness input `finLength_ses_of_injective`
needs for the §3 discharge.
-/
theorem hsAssemble_injective_of_ker_le_adic {M' : Type*} [AddCommGroup M']
    [Module (Localization.AtPrime P) M']
    (f : Localization.AtPrime P →ₗ[Localization.AtPrime P] M')
    (h : LinearMap.ker f ≤ ⨅ i,
      IsLocalRing.maximalIdeal (Localization.AtPrime P) ^ i • ⊤) :
    Function.Injective f :=
  injective_of_ker_le_adic _ (maximalIdeal_atPrime_ne_top P) f h

/-- From `ker = ⊥` to the graded identification: the first-isomorphism form
`polySurjResidue_quotKerEquiv` collapses along `RingEquiv.quotientBot` to
`MvPolynomial (Fin d) κ ≃+* grRegular P`.
-/
noncomputable def hsAssemble_isoOfKerEqBot (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hker : RingHom.ker (polySurjResidue P d g hgen) = ⊥) :
    MvPolynomial (Fin d) (IsLocalRing.ResidueField (Localization.AtPrime P)) ≃+*
      grRegular P := by
  have e := polySurjResidue_quotKerEquiv P d g hgen
  rw [hker] at e
  exact (RingEquiv.quotientBot
    (MvPolynomial (Fin d) (IsLocalRing.ResidueField (Localization.AtPrime P)))).symm.trans
    e

/-- Dim-equality forces the kernel trivial: a nonzero kernel would supply a
`y`-step (`hdrop`), whose §2 degree gap contradicts dim-equality
(`hdimEq`), so `ker (polySurjResidue P d g hgen) = ⊥`.

Explicitly conditional on `hF`, `hdimEq`, `hdrop`, `hdim`, `hd_pos`
(see the module docstring for discharge routes). -/
theorem hsAssemble_ker_eq_bot (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (H Hq : ℕ → ℕ) (e : ℕ)
    (hd_pos : 1 < d) (hdim : e + 1 = d)
    (hF : IsPolyGrowth (fun n => ((H n : ℕ) : ℚ)) e)
    (hdimEq : ∀ Q : ℚ[X], Q.natDegree ≤ e →
      (fun n => ((Hq (n + 1) : ℕ) : ℚ)) =ᶠ[Filter.atTop] evalFun Q →
      Q.natDegree = e)
    (hdrop : RingHom.ker (polySurjResidue P d g hgen) ≠ ⊥ →
      ∃ J : Ideal (Localization.AtPrime P),
        (∀ Q ∈ J.minimalPrimes,
          Q ≠ IsLocalRing.maximalIdeal (Localization.AtPrime P)) ∧
        (∀ A ∈ associatedPrimes (Localization.AtPrime P)
          (Localization.AtPrime P ⧸ J),
          ¬ IsLocalRing.maximalIdeal (Localization.AtPrime P) ≤ A) ∧
        (∀ n, Hq (n + 1) + H n = H (n + 1)) ∧
        IsPolyGrowth (fun n => ((Hq (n + 1) : ℕ) : ℚ)) e) :
    RingHom.ker (polySurjResidue P d g hgen) = ⊥ := by
  by_contra hker
  obtain ⟨J, hne, hle, hses, hFq⟩ := hdrop hker
  have he : 0 < e := by omega
  obtain ⟨Q, hdQ, hQ, hlt⟩ :=
    hsAssemble_quotDegree_lt J H Hq e he hne hle hses hF hFq
  have heq := hdimEq Q hdQ hQ
  omega

/-- The M4c-ii conclusion in file-6 consumption shape:
`gr(R_P) ≅ κ[t₁..t_d]` with `κ = R_P / 𝔪` and `d = dim`.

Explicitly conditional on `hF`, `hdimEq`, `hdrop`, `hdim`, `hd_pos`
(see the module docstring for discharge routes). -/
noncomputable def hsAssemble_grEquiv (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (H Hq : ℕ → ℕ) (e : ℕ)
    (hd_pos : 1 < d) (hdim : e + 1 = d)
    (hF : IsPolyGrowth (fun n => ((H n : ℕ) : ℚ)) e)
    (hdimEq : ∀ Q : ℚ[X], Q.natDegree ≤ e →
      (fun n => ((Hq (n + 1) : ℕ) : ℚ)) =ᶠ[Filter.atTop] evalFun Q →
      Q.natDegree = e)
    (hdrop : RingHom.ker (polySurjResidue P d g hgen) ≠ ⊥ →
      ∃ J : Ideal (Localization.AtPrime P),
        (∀ Q ∈ J.minimalPrimes,
          Q ≠ IsLocalRing.maximalIdeal (Localization.AtPrime P)) ∧
        (∀ A ∈ associatedPrimes (Localization.AtPrime P)
          (Localization.AtPrime P ⧸ J),
          ¬ IsLocalRing.maximalIdeal (Localization.AtPrime P) ≤ A) ∧
        (∀ n, Hq (n + 1) + H n = H (n + 1)) ∧
        IsPolyGrowth (fun n => ((Hq (n + 1) : ℕ) : ℚ)) e) :
    MvPolynomial (Fin d) (IsLocalRing.ResidueField (Localization.AtPrime P)) ≃+*
      grRegular P :=
  hsAssemble_isoOfKerEqBot P d g hgen
    (hsAssemble_ker_eq_bot P d g hgen H Hq e hd_pos hdim hF hdimEq hdrop)

end Assemble

/-! ## §7. The `e = 0` (Artinian) case

`growth_drop_of_vanishing` needs `e ≥ 1`; for `e = 0` the `0`-th difference
is the sequence (`seqDiff_zero`), so the drop output is plain eventual
vanishing — no quotient growth bound is needed. The `e = 0` masters below
are conditional-explicit only on the domain bound (`hF₀`), the nonvanishing
input (`hnonvan`, the `e = 0` form of dim-equality: `hdimEq` at `e = 0`
is consistent with vanishing, hence content-free), and the drop shape
without a quotient growth bound (`hdrop₀`).

Status: the eventually-zero reading is unconditional; the masters are
conditional-explicit on `hF₀`, `hnonvan`, `hdrop₀` (no `hdim`/`hd_pos`). -/

section ArtinianZero

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- The `e = 0` drop pipeline: `ysop_step` at `d = 0` says the shifted
quotient Hilbert function vanishes eventually. No quotient growth bound. -/
theorem hsAssemble_quotEventuallyZero (J : Ideal R) (H Hq : ℕ → ℕ)
    (hne : ∀ Q ∈ J.minimalPrimes, Q ≠ IsLocalRing.maximalIdeal R)
    (hle : ∀ A ∈ associatedPrimes R (R ⧸ J),
      ¬ IsLocalRing.maximalIdeal R ≤ A)
    (hses : ∀ n, Hq (n + 1) + H n = H (n + 1))
    (hF : IsPolyGrowth (fun n => ((H n : ℕ) : ℚ)) 0) :
    (fun n => ((Hq (n + 1) : ℕ) : ℚ)) =ᶠ[Filter.atTop] 0 := by
  obtain ⟨_y, _hym, _hymin, _hreg, hvan⟩ :=
    ysop_step J 0 H Hq hne hle hses hF
  rwa [seqDiff_zero] at hvan

end ArtinianZero

section ArtinianAssemble

variable {K : Type*} [Field K] {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K))
  [P.IsPrime]

/-- Dim-equality forces the kernel trivial in the Artinian (`e = 0`) case:
a nonzero kernel would supply a `y`-step (`hdrop₀`), whose §7 eventual
vanishing contradicts nonvanishing (`hnonvan`). -/
theorem hsAssemble_ker_eq_bot_artinian (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (H Hq : ℕ → ℕ)
    (hF : IsPolyGrowth (fun n => ((H n : ℕ) : ℚ)) 0)
    (hnonvan : ¬ (fun n => ((Hq (n + 1) : ℕ) : ℚ)) =ᶠ[Filter.atTop] 0)
    (hdrop₀ : RingHom.ker (polySurjResidue P d g hgen) ≠ ⊥ →
      ∃ J : Ideal (Localization.AtPrime P),
        (∀ Q ∈ J.minimalPrimes,
          Q ≠ IsLocalRing.maximalIdeal (Localization.AtPrime P)) ∧
        (∀ A ∈ associatedPrimes (Localization.AtPrime P)
          (Localization.AtPrime P ⧸ J),
          ¬ IsLocalRing.maximalIdeal (Localization.AtPrime P) ≤ A) ∧
        (∀ n, Hq (n + 1) + H n = H (n + 1))) :
    RingHom.ker (polySurjResidue P d g hgen) = ⊥ := by
  by_contra hker
  obtain ⟨J, hne, hle, hses⟩ := hdrop₀ hker
  exact hnonvan (hsAssemble_quotEventuallyZero J H Hq hne hle hses hF)

end ArtinianAssemble

/-! ## §8. The dimension bridge: `e := d - 1` closes `hdim`

With `e := d - 1`, the generator/dimension bridge `hdim : e + 1 = d` is
pure arithmetic (`omega` from `1 ≤ d`), so the §6 masters below take one
fewer hypothesis. `hd_pos : 1 < d` stays (it is application data: the
`d = 1` case is §7 with `hF₀` closed by §13, see §14; the `d = 0` case
is §14 with unconditional masters).

Status: the bridge lemma is unconditional; the masters are
conditional-explicit on `hF`, `hdimEq`, `hdrop`, `hd_pos` (`hdim` closed). -/

section DimBridge

variable {K : Type*} [Field K] {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K))
  [P.IsPrime]

/-- The §6 kernel master with `e := d - 1`: `hdim` discharged by `omega`. -/
theorem hsAssemble_ker_eq_bot_of_dim (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (H Hq : ℕ → ℕ)
    (hd_pos : 1 < d)
    (hF : IsPolyGrowth (fun n => ((H n : ℕ) : ℚ)) (d - 1))
    (hdimEq : ∀ Q : ℚ[X], Q.natDegree ≤ d - 1 →
      (fun n => ((Hq (n + 1) : ℕ) : ℚ)) =ᶠ[Filter.atTop] evalFun Q →
      Q.natDegree = d - 1)
    (hdrop : RingHom.ker (polySurjResidue P d g hgen) ≠ ⊥ →
      ∃ J : Ideal (Localization.AtPrime P),
        (∀ Q ∈ J.minimalPrimes,
          Q ≠ IsLocalRing.maximalIdeal (Localization.AtPrime P)) ∧
        (∀ A ∈ associatedPrimes (Localization.AtPrime P)
          (Localization.AtPrime P ⧸ J),
          ¬ IsLocalRing.maximalIdeal (Localization.AtPrime P) ≤ A) ∧
        (∀ n, Hq (n + 1) + H n = H (n + 1)) ∧
        IsPolyGrowth (fun n => ((Hq (n + 1) : ℕ) : ℚ)) (d - 1)) :
    RingHom.ker (polySurjResidue P d g hgen) = ⊥ :=
  hsAssemble_ker_eq_bot P d g hgen H Hq (d - 1) hd_pos (by omega)
    hF hdimEq hdrop

end DimBridge

/-! ## §9. Binomial sequences have polynomial growth (the `hF` core)

The domain Hilbert function of `κ[t₁..t_d]` is, degree by degree, the
binomial sequence `n ↦ C(n + d - 1, d - 1)` (stars and bars; the finrank
half was residual R1, closed in §13 — see §12). This section proves the
analytic half
unconditionally:
every binomial sequence `n ↦ C(n, k)` over `ℚ` has polynomial growth of
degree `≤ k`, by induction on `k` along
`C(n, k+1) * (k+1) = C(n, k) * (n - k)`
(`Nat.choose_succ_right_eq`), with interpolating polynomial
`Q(X) = P(X) * (X - k) / (k + 1)`.
-/

/-- The binomial sequence `n ↦ C(n, k)` over `ℚ` has polynomial growth of
degree `≤ k`. -/
theorem chooseFun_isPolyGrowth (k : ℕ) :
    IsPolyGrowth (chooseFun (R := ℚ) k) k := by
  induction k with
  | zero =>
    refine ⟨1, by rw [Polynomial.natDegree_one],
      Filter.Eventually.of_forall fun n => ?_⟩
    change ((Nat.choose n 0 : ℕ) : ℚ) = (1 : ℚ[X]).eval (n : ℚ)
    rw [Nat.choose_zero_right, Nat.cast_one, Polynomial.eval_one]
  | succ k ih =>
    obtain ⟨P, hd, hP⟩ := ih
    set c : ℚ := ((k + 1 : ℕ) : ℚ)⁻¹ with hc
    refine ⟨Polynomial.C c * (P * (Polynomial.X - Polynomial.C (k : ℚ))),
      ?_, ?_⟩
    · have h1 := Polynomial.natDegree_mul_le (p := Polynomial.C c)
        (q := P * (Polynomial.X - Polynomial.C (k : ℚ)))
      rw [Polynomial.natDegree_C] at h1
      have h2 := Polynomial.natDegree_mul_le (p := P)
        (q := Polynomial.X - Polynomial.C (k : ℚ))
      rw [Polynomial.natDegree_X_sub_C] at h2
      omega
    · obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp hP
      refine Filter.eventually_atTop.mpr ⟨N₁ ⊔ (k + 1), fun n hn => ?_⟩
      have hn1 : N₁ ≤ n := le_trans (le_max_left _ _) hn
      have hnk : k + 1 ≤ n := le_trans (le_max_right _ _) hn
      have hPn : ((Nat.choose n k : ℕ) : ℚ) = P.eval (n : ℚ) := hN₁ n hn1
      have hcast := congrArg (fun m : ℕ => (m : ℚ))
        (Nat.choose_succ_right_eq n k)
      rw [Nat.cast_mul, Nat.cast_mul] at hcast
      have hsub : ((n - k : ℕ) : ℚ) = (n : ℚ) - (k : ℚ) :=
        Nat.cast_sub (by omega : k ≤ n)
      rw [hsub] at hcast
      change ((Nat.choose n (k + 1) : ℕ) : ℚ) =
        (Polynomial.C c * (P * (Polynomial.X - Polynomial.C (k : ℚ)))).eval
          (n : ℚ)
      simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C]
      rw [hc, ← hPn]
      have hC : ((k + 1 : ℕ) : ℚ) ≠ 0 := by
        have h : k + 1 ≠ 0 := by omega
        exact_mod_cast h
      calc ((Nat.choose n (k + 1) : ℕ) : ℚ)
          = (((Nat.choose n (k + 1) : ℕ) : ℚ) * ((k + 1 : ℕ) : ℚ)) *
            (((k + 1 : ℕ) : ℚ))⁻¹ := by
              rw [mul_assoc, mul_inv_cancel₀ hC, mul_one]
        _ = (((Nat.choose n k : ℕ) : ℚ) * ((n : ℚ) - (k : ℚ))) *
            (((k + 1 : ℕ) : ℚ))⁻¹ := by rw [hcast]
        _ = (((k + 1 : ℕ) : ℚ))⁻¹ *
            (((Nat.choose n k : ℕ) : ℚ) * ((n : ℚ) - (k : ℚ))) := by
              rw [mul_comm]

/-- Polynomial growth is stable under shifting the sequence forward (the
shifted interpolating polynomial is `P.comp (X + C N)`). -/
theorem isPolyGrowth_comp_add {F : ℕ → ℚ} {e : ℕ} (h : IsPolyGrowth F e)
    (N : ℕ) : IsPolyGrowth (fun n => F (n + N)) e := by
  obtain ⟨P, hd, hP⟩ := h
  refine ⟨P.comp (Polynomial.X + Polynomial.C (N : ℚ)), ?_, ?_⟩
  · have hle := Polynomial.natDegree_comp_le (p := P)
      (q := Polynomial.X + Polynomial.C (N : ℚ))
    rw [Polynomial.natDegree_X_add_C] at hle
    rw [Nat.mul_one] at hle
    exact le_trans hle hd
  · obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp hP
    refine Filter.eventually_atTop.mpr ⟨N₁, fun n hn => ?_⟩
    have h1 : F (n + N) = P.eval ((n + N : ℕ) : ℚ) :=
      hN₁ (n + N) (le_trans hn (Nat.le_add_right n N))
    have h2 : (P.comp (Polynomial.X + Polynomial.C (N : ℚ))).eval (n : ℚ)
        = P.eval ((n + N : ℕ) : ℚ) := by
      rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
        Polynomial.eval_C, Nat.cast_add]
    change F (n + N) =
      (P.comp (Polynomial.X + Polynomial.C (N : ℚ))).eval (n : ℚ)
    rw [h1, h2]

/-- The domain Hilbert function: homogeneous-component lengths of
`κ[t₁..t_d]` over the residue field `κ`. -/
noncomputable def hsAssemble_domainHilbert (κ : Type*) [Field κ] (d n : ℕ) :
    ℕ :=
  finLength κ (MvPolynomial.homogeneousSubmodule (Fin d) κ n)

/-- The domain growth bound from stars-and-bars: `hF` for the concrete
domain Hilbert function, conditional only on the stars-and-bars identity
(residual R1, see §12). -/
theorem hsAssemble_hF_of_starsBars (κ : Type*) [Field κ] (d : ℕ) (hd : 1 ≤ d)
    (hSB : ∀ n, hsAssemble_domainHilbert κ d n =
      Nat.choose (n + d - 1) (d - 1)) :
    IsPolyGrowth (fun n => ((hsAssemble_domainHilbert κ d n : ℕ) : ℚ))
      (d - 1) := by
  have hgr := isPolyGrowth_comp_add (chooseFun_isPolyGrowth (d - 1)) (d - 1)
  have heq : (fun n => ((hsAssemble_domainHilbert κ d n : ℕ) : ℚ)) =
      (fun n => chooseFun (R := ℚ) (d - 1) (n + (d - 1))) := by
    funext n
    have hN : n + d - 1 = n + (d - 1) := by omega
    change ((hsAssemble_domainHilbert κ d n : ℕ) : ℚ) =
      ((Nat.choose (n + (d - 1)) (d - 1) : ℕ) : ℚ)
    rw [hSB n, hN]
  rw [heq]
  exact hgr

/-! ## §10. `hdimEq` is multiplicity-nonvanishing

Given the quotient growth bound `hFq`, the exact-degree reading `hdimEq`
holds if and only if the top difference does not vanish (for `e ≥ 1`;
the `e = 0` form is §7's `hnonvan`). Forward: nonvanishing pins an
exact-degree polynomial (§1), whose top coefficient is nonzero; every
other agreeing polynomial shares that top coefficient (both `e`-th
differences are eventually the `e!`-scaled constants), so it has degree
exactly `e`. Backward: vanishing would drop the degree (§1), contradicting
`hdimEq`. The masters below take the multiplicity input `hmult` instead of
`hdimEq`, shrinking the residual to "the quotient Hilbert function has
nonzero multiplicity" (which needs dim theory: the leading coefficient of
a Hilbert polynomial is nonzero iff the dimension is as claimed).

conditional-explicit on `hF`, `hmult`, `hdrop`, `hd_pos`, `hdim`
(`hdimEq` factored to `hmult`). -/

/-- Nonvanishing plus the growth bound gives the exact-degree reading. -/
theorem hsAssemble_hdimEq_of_not_vanishing {Fq : ℕ → ℚ} {e : ℕ}
    (hFq : IsPolyGrowth Fq e)
    (hne : ¬ seqDiff e Fq =ᶠ[Filter.atTop] 0) :
    ∀ Q : ℚ[X], Q.natDegree ≤ e → Fq =ᶠ[Filter.atTop] evalFun Q →
      Q.natDegree = e := by
  obtain ⟨P, hPdeg, hPag⟩ := growth_exact_of_not_vanishing hFq hne
  have hPne : P ≠ 0 := by
    rintro rfl
    apply hne
    have h0 : evalFun (0 : ℚ[X]) = (0 : ℕ → ℚ) := by
      funext n
      simp [evalFun]
    rw [h0] at hPag
    have h2 := seqDiff_eventuallyEq_of_eventuallyEq hPag e
    rwa [seqDiff_zero_fun] at h2
  have hPcoeff : P.coeff e ≠ 0 := by
    have hlc : P.coeff e = P.leadingCoeff := by
      rw [← hPdeg, Polynomial.coeff_natDegree]
    rw [hlc]
    exact Polynomial.leadingCoeff_ne_zero.mpr hPne
  have hfact : (Nat.factorial e : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero e)
  intro Q hdQ hQag
  have hconstP :=
    seqDiff_eventuallyEq_const_of_eventuallyEq_evalFun P e hPag (le_of_eq hPdeg)
  have hconstQ :=
    seqDiff_eventuallyEq_const_of_eventuallyEq_evalFun Q e hQag hdQ
  have hQQ : (fun _ : ℕ => (Nat.factorial e : ℚ) * Q.coeff e) =ᶠ[Filter.atTop]
      fun _ : ℕ => (Nat.factorial e : ℚ) * P.coeff e :=
    hconstQ.symm.trans hconstP
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hQQ
  have hNN := hN N le_rfl
  simp only at hNN
  have hcoeff : Q.coeff e = P.coeff e := mul_left_cancel₀ hfact hNN
  have hQcoeff : Q.coeff e ≠ 0 := by rw [hcoeff]; exact hPcoeff
  have hle : e ≤ Q.natDegree := by
    by_contra hlt
    have hlt' : Q.natDegree < e := lt_of_not_ge hlt
    exact hQcoeff (Polynomial.coeff_eq_zero_of_natDegree_lt hlt')
  exact le_antisymm hdQ hle

/-- The exact-degree reading forces nonvanishing (for `e > 0`). -/
theorem hsAssemble_not_vanishing_of_hdimEq {Fq : ℕ → ℚ} {e : ℕ} (he : 0 < e)
    (hFq : IsPolyGrowth Fq e)
    (hdimEq : ∀ Q : ℚ[X], Q.natDegree ≤ e → Fq =ᶠ[Filter.atTop] evalFun Q →
      Q.natDegree = e) :
    ¬ seqDiff e Fq =ᶠ[Filter.atTop] 0 := by
  intro hvan
  obtain ⟨Q, hdQ, hQ, hlt⟩ := growth_drop_of_vanishing he hFq hvan
  have heq := hdimEq Q hdQ hQ
  omega

section MultAssemble

variable {K : Type*} [Field K] {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K))
  [P.IsPrime]

/-- The §6 kernel master with `hdimEq` factored to multiplicity-nonvanishing. -/
theorem hsAssemble_ker_eq_bot_of_mult (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (H Hq : ℕ → ℕ) (e : ℕ)
    (hd_pos : 1 < d) (hdim : e + 1 = d)
    (hF : IsPolyGrowth (fun n => ((H n : ℕ) : ℚ)) e)
    (hmult : ¬ seqDiff e (fun n => ((Hq (n + 1) : ℕ) : ℚ))
      =ᶠ[Filter.atTop] 0)
    (hdrop : RingHom.ker (polySurjResidue P d g hgen) ≠ ⊥ →
      ∃ J : Ideal (Localization.AtPrime P),
        (∀ Q ∈ J.minimalPrimes,
          Q ≠ IsLocalRing.maximalIdeal (Localization.AtPrime P)) ∧
        (∀ A ∈ associatedPrimes (Localization.AtPrime P)
          (Localization.AtPrime P ⧸ J),
          ¬ IsLocalRing.maximalIdeal (Localization.AtPrime P) ≤ A) ∧
        (∀ n, Hq (n + 1) + H n = H (n + 1)) ∧
        IsPolyGrowth (fun n => ((Hq (n + 1) : ℕ) : ℚ)) e) :
    RingHom.ker (polySurjResidue P d g hgen) = ⊥ := by
  by_contra hker
  obtain ⟨J, hne, hle, hses, hFq⟩ := hdrop hker
  have he : 0 < e := by omega
  obtain ⟨Q, hdQ, hQ, hlt⟩ :=
    hsAssemble_quotDegree_lt J H Hq e he hne hle hses hF hFq
  have hdimEq := hsAssemble_hdimEq_of_not_vanishing hFq hmult
  have heq := hdimEq Q hdQ hQ
  omega

end MultAssemble

/-! ## §11. The kernel is homogeneous (the `hdrop` first half)

`hdrop` says a nonzero kernel yields the drop shape. Its first half is
ker-homogeneity: `polySurj` sends homogeneous polynomials to homogeneous
classes (`hsAssemble_polySurj_of_homogeneous`, via `eval₂Hom_monomial` —
coefficients land in degree 0, each variable in degree 1, so a monomial
of total degree `n` lies in degree `n`), hence kernel elements have
kernel homogeneous components (`hsAssemble_ker_homogeneousComponent_mem`,
via uniqueness of homogeneous decomposition
`hsAssemble_of_sum_eq_zero`), hence a nonzero kernel contains a nonzero
homogeneous element (`hsAssemble_exists_homogeneous_mem_ker`). `hdrop`
then follows from its principal-step form
(`hsAssemble_hdrop_of_principalStep`), and the masters below take the
principal-step rule `hprin` instead of `hdrop`, shrinking the residual to
"a nonzero homogeneous `y ∈ ker` yields the drop shape" (residual R3,
see §12: needs `y`-regularity on graded pieces, the mul-by-`y` SES, and
the quotient growth bound).

conditional-explicit on `hF`, `hdimEq`, `hprin`, `hd_pos`, `hdim`
(`hdrop` factored to `hprin`). -/

/-- Uniqueness of homogeneous decomposition: if a sum of homogeneous
classes (one per degree below `N`) is zero, each class is zero. -/
theorem hsAssemble_of_sum_eq_zero {A : ℕ → Type*} [∀ n, AddCommGroup (A n)]
    {N : ℕ} {y : ∀ n, A n}
    (h : ∑ i ∈ Finset.range N, DirectSum.of A i (y i) = 0)
    {i : ℕ} (hi : i < N) : y i = 0 := by
  have h2 := congrArg (fun s : DirectSum ℕ A => s i) h
  rw [DFinsupp.finsetSum_apply] at h2
  rw [Finset.sum_eq_single i
    (fun j _ hji => DirectSum.of_eq_of_ne j i (y j) (Ne.symm hji))
    (fun hi' => absurd (Finset.mem_range.mpr hi) hi')] at h2
  rw [DirectSum.of_eq_same] at h2
  simpa using h2

section KerHomogeneousPow

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- Powers of degree-1 classes land in the power degree. -/
theorem hsAssemble_of_pow_mem (k : ℕ) (x : grPiece R I 1) :
    ∃ y : grPiece R I k,
      (DirectSum.of (grPiece R I) 1 x) ^ k =
        DirectSum.of (grPiece R I) k y := by
  induction k with
  | zero =>
    exact ⟨1, by rw [pow_zero]; exact (DirectSum.of_zero_one _).symm⟩
  | succ k ih =>
    obtain ⟨y, hy⟩ := ih
    refine ⟨GradedMonoid.GMul.mul y x, ?_⟩
    rw [pow_succ, hy]
    exact associatedGraded_of_mul_of R I k 1 y x

/-- Finite products of powers land in the sum degree (the per-monomial
input: `m` is kept general so indices transport by `subst`, not casts). -/
theorem hsAssemble_of_prod_mem {ι : Type*} (s : Finset ι)
    (t : ι → ℕ) (x : ι → grPiece R I 1) (m : ℕ) (hm : s.sum t = m) :
    ∃ y : grPiece R I m,
      (∏ i ∈ s, (DirectSum.of (grPiece R I) 1 (x i)) ^ (t i)) =
        DirectSum.of (grPiece R I) m y := by
  classical
  revert m hm
  induction s using Finset.induction with
  | empty =>
    intro m hm
    rw [Finset.sum_empty] at hm
    subst hm
    exact ⟨1, by rw [Finset.prod_empty]; exact (DirectSum.of_zero_one _).symm⟩
  | @insert a s has ih =>
    intro m hm
    rw [Finset.sum_insert has] at hm
    subst hm
    obtain ⟨y, hy⟩ := ih (s.sum t) rfl
    obtain ⟨w, hw⟩ := hsAssemble_of_pow_mem I (t a) (x a)
    refine ⟨GradedMonoid.GMul.mul w y, ?_⟩
    rw [Finset.prod_insert has, hy, hw]
    exact associatedGraded_of_mul_of R I _ _ w y

end KerHomogeneousPow

section KerHomogeneous

variable {R : Type*} [CommRing R] (I : Ideal R) (d : ℕ) (g : Fin d → R)
  (hgen : Ideal.span (Set.range g) = I)

/-- `polySurj` sends homogeneous polynomials to homogeneous classes. -/
theorem hsAssemble_polySurj_of_homogeneous {n : ℕ}
    {p : MvPolynomial (Fin d) (R ⧸ I)} (hphom : p.IsHomogeneous n) :
    ∃ y : grPiece R I n,
      polySurj R I d g hgen p = DirectSum.of (grPiece R I) n y := by
  have hdeg : ∀ e ∈ p.support, e.degree = n := by
    intro e he
    by_contra hcon
    exact (Finsupp.mem_support_iff.mp he) (hphom.coeff_eq_zero hcon)
  have hmono : ∀ e : Fin d →₀ ℕ, ∃ y : grPiece R I n,
      e ∈ p.support →
        polySurj R I d g hgen (MvPolynomial.monomial e (p.coeff e)) =
          DirectSum.of (grPiece R I) n y := by
    intro e
    by_cases he : e ∈ p.support
    · have h0n : 0 + e.degree = n := by rw [zero_add]; exact hdeg e he
      rw [← h0n]
      have hmk : polySurj R I d g hgen
          (MvPolynomial.monomial e (p.coeff e)) =
          coeffHom R I (p.coeff e) * (e.prod (fun i k =>
            (DirectSum.of (grPiece R I) 1
              (genClass R I d g i hgen)) ^ k) : associatedGraded R I) :=
        MvPolynomial.eval₂Hom_monomial _ _ _ _
      obtain ⟨c, hc⟩ : ∃ c, Ideal.Quotient.mk I c = p.coeff e :=
        ⟨Quotient.out _, Ideal.Quotient.mk_out _⟩
      have hcoeff : coeffHom R I (p.coeff e) =
          DirectSum.of (grPiece R I) 0 (grMk0 R I c) := by
        rw [← hc, coeffHom_mk]
      rw [hcoeff] at hmk
      -- Re-ascribe at `DirectSum` type so the graded rewrites below match
      -- syntactically (`associatedGraded` is a plain def).
      have hmk2 : polySurj R I d g hgen
          (MvPolynomial.monomial e (p.coeff e)) =
          (DirectSum.of (grPiece R I) 0 (grMk0 R I c)) *
            (e.prod (fun i k => (DirectSum.of (grPiece R I) 1
              (genClass R I d g i hgen)) ^ k) :
              DirectSum ℕ (grPiece R I)) := hmk
      have hm : Finset.univ.sum e = e.degree :=
        (Finsupp.degree_eq_sum e).symm
      obtain ⟨y, hy⟩ := hsAssemble_of_prod_mem I Finset.univ e
        (fun i => genClass R I d g i hgen) e.degree hm
      have hps := Finsupp.prod_fintype e (fun i k =>
        (DirectSum.of (grPiece R I) 1 (genClass R I d g i hgen)) ^ k)
        (fun i => pow_zero _)
      rw [hps] at hmk2
      have hy2 : (∏ i, (fun i k =>
          (DirectSum.of (grPiece R I) 1
            (genClass R I d g i hgen)) ^ k) i (e i)) =
          DirectSum.of (grPiece R I) e.degree y := hy
      rw [hy2, associatedGraded_of_mul_of] at hmk2
      refine ⟨GradedMonoid.GMul.mul (grMk0 R I c) y, fun _ => hmk2⟩
    · exact ⟨0, fun hem => absurd hem he⟩
  have hmap : polySurj R I d g hgen p =
      ∑ e ∈ p.support, polySurj R I d g hgen
        (MvPolynomial.monomial e (p.coeff e)) := by
    conv_lhs => rw [MvPolynomial.as_sum p]
    rw [map_sum]
  obtain ⟨w, hw⟩ := Classical.axiomOfChoice hmono
  refine ⟨∑ e ∈ p.support, w e, ?_⟩
  rw [hmap]
  have hsum : (∑ e ∈ p.support, DirectSum.of (grPiece R I) n (w e)) =
      DirectSum.of (grPiece R I) n (∑ e ∈ p.support, w e) :=
    (map_sum (DirectSum.of (grPiece R I) n) w p.support).symm
  rw [← hsum]
  exact Finset.sum_congr rfl (fun e he => hw e he)

/-- Kernel elements have kernel homogeneous components. -/
theorem hsAssemble_ker_homogeneousComponent_mem
    (p : MvPolynomial (Fin d) (R ⧸ I))
    (hp : p ∈ RingHom.ker (polySurj R I d g hgen)) (n : ℕ) :
    (MvPolynomial.homogeneousComponent n) p ∈
      RingHom.ker (polySurj R I d g hgen) := by
  have hsplit := MvPolynomial.sum_homogeneousComponent p
  have hmap : polySurj R I d g hgen p =
      ∑ i ∈ Finset.range (p.totalDegree + 1),
        polySurj R I d g hgen
          ((MvPolynomial.homogeneousComponent i) p) := by
    conv_lhs => rw [← hsplit]
    rw [map_sum]
  have hmono : ∀ i : ℕ, ∃ y : grPiece R I i,
      polySurj R I d g hgen ((MvPolynomial.homogeneousComponent i) p) =
        DirectSum.of (grPiece R I) i y := fun i =>
    hsAssemble_polySurj_of_homogeneous I d g hgen
      (MvPolynomial.homogeneousComponent_isHomogeneous i p)
  obtain ⟨y, hy⟩ := Classical.axiomOfChoice hmono
  have hsum : ∑ i ∈ Finset.range (p.totalDegree + 1),
      DirectSum.of (grPiece R I) i (y i) = 0 := by
    have h0 : ∑ i ∈ Finset.range (p.totalDegree + 1),
        polySurj R I d g hgen
          ((MvPolynomial.homogeneousComponent i) p) = 0 := by
      rw [← hmap]
      exact RingHom.mem_ker.mp hp
    simp only [hy] at h0
    exact h0
  rw [RingHom.mem_ker]
  by_cases hn : n < p.totalDegree + 1
  · have hyn : y n = 0 := hsAssemble_of_sum_eq_zero hsum hn
    rw [hy n, hyn]
    exact map_zero _
  · have hzc : (MvPolynomial.homogeneousComponent n) p = 0 :=
      MvPolynomial.homogeneousComponent_eq_zero n p (by omega)
    rw [hzc]
    exact map_zero _

/-- A nonzero kernel contains a nonzero homogeneous element. -/
theorem hsAssemble_exists_homogeneous_mem_ker
    (hker : RingHom.ker (polySurj R I d g hgen) ≠ ⊥) :
    ∃ n y, y ∈ RingHom.ker (polySurj R I d g hgen) ∧ y ≠ 0 ∧
      MvPolynomial.IsHomogeneous y n := by
  obtain ⟨p, hpmem, hpne⟩ := (Submodule.ne_bot_iff _).mp hker
  by_cases hall : ∀ i ∈ Finset.range (p.totalDegree + 1),
      (MvPolynomial.homogeneousComponent i) p = 0
  · exfalso
    apply hpne
    rw [← MvPolynomial.sum_homogeneousComponent p]
    exact Finset.sum_eq_zero hall
  · obtain ⟨i, hi⟩ := not_forall.mp hall
    have himem : i ∈ Finset.range (p.totalDegree + 1) := by
      by_contra hcon
      exact hi (fun h => absurd h hcon)
    have hine : (MvPolynomial.homogeneousComponent i) p ≠ 0 :=
      fun h => hi (fun _ => h)
    exact ⟨i, (MvPolynomial.homogeneousComponent i) p,
      hsAssemble_ker_homogeneousComponent_mem I d g hgen p hpmem i, hine,
      MvPolynomial.homogeneousComponent_isHomogeneous i p⟩

/-- `hdrop` follows from its principal-step form: a nonzero homogeneous
`y ∈ ker` yields the drop shape. -/
theorem hsAssemble_hdrop_of_principalStep [IsLocalRing R] (H Hq : ℕ → ℕ)
    (e : ℕ)
    (hprin : ∀ (y : MvPolynomial (Fin d) (R ⧸ I)) (n : ℕ),
      y ∈ RingHom.ker (polySurj R I d g hgen) → y ≠ 0 →
        MvPolynomial.IsHomogeneous y n →
      ∃ J : Ideal R,
        (∀ Q ∈ J.minimalPrimes, Q ≠ IsLocalRing.maximalIdeal R) ∧
        (∀ A ∈ associatedPrimes R (R ⧸ J),
          ¬ IsLocalRing.maximalIdeal R ≤ A) ∧
        (∀ m, Hq (m + 1) + H m = H (m + 1)) ∧
        IsPolyGrowth (fun m => ((Hq (m + 1) : ℕ) : ℚ)) e) :
    RingHom.ker (polySurj R I d g hgen) ≠ ⊥ →
      ∃ J : Ideal R,
        (∀ Q ∈ J.minimalPrimes, Q ≠ IsLocalRing.maximalIdeal R) ∧
        (∀ A ∈ associatedPrimes R (R ⧸ J),
          ¬ IsLocalRing.maximalIdeal R ≤ A) ∧
        (∀ m, Hq (m + 1) + H m = H (m + 1)) ∧
        IsPolyGrowth (fun m => ((Hq (m + 1) : ℕ) : ℚ)) e := by
  intro hker
  obtain ⟨n, y, hym, hyne, hyhom⟩ :=
    hsAssemble_exists_homogeneous_mem_ker I d g hgen hker
  exact hprin y n hym hyne hyhom

end KerHomogeneous

section PrincipalAssemble

variable {K : Type*} [Field K] {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K))
  [P.IsPrime]

/-- The §6 kernel master with `hdrop` factored to its principal-step form. -/
theorem hsAssemble_ker_eq_bot_of_principal (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (H Hq : ℕ → ℕ) (e : ℕ)
    (hd_pos : 1 < d) (hdim : e + 1 = d)
    (hF : IsPolyGrowth (fun n => ((H n : ℕ) : ℚ)) e)
    (hdimEq : ∀ Q : ℚ[X], Q.natDegree ≤ e →
      (fun n => ((Hq (n + 1) : ℕ) : ℚ)) =ᶠ[Filter.atTop] evalFun Q →
      Q.natDegree = e)
    (hprin : ∀ (y : MvPolynomial (Fin d)
        (IsLocalRing.ResidueField (Localization.AtPrime P))) (n : ℕ),
      y ∈ RingHom.ker (polySurjResidue P d g hgen) → y ≠ 0 →
        MvPolynomial.IsHomogeneous y n →
      ∃ J : Ideal (Localization.AtPrime P),
        (∀ Q ∈ J.minimalPrimes,
          Q ≠ IsLocalRing.maximalIdeal (Localization.AtPrime P)) ∧
        (∀ A ∈ associatedPrimes (Localization.AtPrime P)
          (Localization.AtPrime P ⧸ J),
          ¬ IsLocalRing.maximalIdeal (Localization.AtPrime P) ≤ A) ∧
        (∀ k, Hq (k + 1) + H k = H (k + 1)) ∧
        IsPolyGrowth (fun k => ((Hq (k + 1) : ℕ) : ℚ)) e) :
    RingHom.ker (polySurjResidue P d g hgen) = ⊥ := by
  have hdrop : RingHom.ker (polySurjResidue P d g hgen) ≠ ⊥ →
      ∃ J : Ideal (Localization.AtPrime P),
        (∀ Q ∈ J.minimalPrimes,
          Q ≠ IsLocalRing.maximalIdeal (Localization.AtPrime P)) ∧
        (∀ A ∈ associatedPrimes (Localization.AtPrime P)
          (Localization.AtPrime P ⧸ J),
          ¬ IsLocalRing.maximalIdeal (Localization.AtPrime P) ≤ A) ∧
        (∀ k, Hq (k + 1) + H k = H (k + 1)) ∧
        IsPolyGrowth (fun k => ((Hq (k + 1) : ℕ) : ℚ)) e :=
    hsAssemble_hdrop_of_principalStep
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) d g hgen H Hq e
      hprin
  exact hsAssemble_ker_eq_bot P d g hgen H Hq e hd_pos hdim hF hdimEq hdrop

end PrincipalAssemble

/-! ## §12. Remaining residuals (status)

Precise statements of what the §6 masters still need, after §§7–11:

1. **R1 (`hF`: stars-and-bars identity).** closed by §13
   (`hsAssemble_domainHilbert_eq_choose` plus unconditional
   `hsAssemble_hF`): finrank of `homogeneousSubmodule` via the monomial
   basis, plus stars-and-bars counting by induction with hockey-stick.
2. **R2 (`hdimEq`/`hmult`: multiplicity-nonvanishing).** partial (U2): §10 shows `hdimEq ↔ hmult`
  given `hFq` (for `e ≥ 1`); the
   `e = 0` form is §7's `hnonvan`. The quot-side leg `dim (S ⧸ ker) =
   d` ⇒ witness is CLOSED (`DimensionToMultiplicity` §§1–2, R-2c′); the live
   remainder is `dim gr = dim R = d` per Ass prime (R-2a′,
   `HdimGrMinAtAss`, `UnmixednessAtLengthTwo` §8 partial) plus the `d ≥ 2`
   witness (`HwitMinAtAss`). milestones in
   `Regularity/Multiplicity/MultiplicityNonvanishing.lean` (M-R2a–e proved; residuals
   updated — see `DimensionToMultiplicity` + `UnmixednessAtLengthTwo` §8).
3. **R3 (`hdrop`: principal-step rule).** still open: §11 closes the
   ker-homogeneity half: `hdrop` follows from the rule "a nonzero
   homogeneous `y ∈ ker` yields the drop shape". The rule itself needs
   `y`-regularity on graded pieces, the mul-by-`y` SES
   (`finLength_ses_of_injective`), and the quotient growth bound.
   Estimate: ~300+ lines.: M1–M5 proved in
   `Regularity/KoszulPrincipalStep.lean`, but the single-step-Hq
   abstraction proved machine-checked unfixable — re-scoped to the
   single-y drop (`Regularity/Multiplicity/SingleDropRegularity.lean`).
4. **R4 (`hd_pos`: application data).** closed by §14: `d = 0`
   unconditional masters (`hsAssemble_ker_eq_bot_zero`,
   `hsAssemble_grEquiv_zero`, via M4a); `d = 1` Artinian masters with
   `hF₀` discharged. `1 < d` remains application data for file 6.
-/

/-! ## §13. Stars-and-bars: the domain Hilbert function (R1 closed)

The domain Hilbert function `hsAssemble_domainHilbert κ d n` is the
`κ`-length of the degree-`n` homogeneous piece of `κ[t₁..t_d]`. Over a
field, length is finrank (`finLength_eq_finrank`); the homogeneous piece
is the supported-finsupp submodule
(`homogeneousSubmodule_eq_finsupp_supported`), whose finrank is the
number of degree-`n` exponents (`hsAssemble_finrank_homogeneous`, via
the monomial basis `MvPolynomial.basisMonomials` and
`finrank_span_eq_card`); and that number is the stars-and-bars binomial
coefficient (`hsAssemble_card_degreeEq` plus `hsAssemble_card_sumEq`, by
induction on `d` along `Fin.sum_univ_succ` with the hockey-stick
identity `Nat.sum_range_add_choose`). The unconditional growth bound
`hsAssemble_hF` discharges `hsAssemble_hF_of_starsBars` (§9).
-/

/-- Degree-`n` exponents in `d` variables form a finite type: each
coordinate is `≤ n`, so inject into `Fin d → Fin (n+1)`. -/
noncomputable instance hsAssemble_fintype_degreeEq (d n : ℕ) :
    Fintype {e : Fin d →₀ ℕ // e.degree = n} := by
  refine Fintype.ofInjective (fun e : {e : Fin d →₀ ℕ // e.degree = n} =>
    fun i : Fin d => (⟨e.val i, ?_⟩ : Fin (n + 1))) ?_
  · have hle : e.val i ≤ n :=
      calc e.val i ≤ ∑ j, e.val j :=
            Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
        _ = e.val.degree := (Finsupp.degree_eq_sum e.val).symm
        _ = n := e.property
    omega
  · intro a b hab
    have hfun : a.val = b.val := by
      ext i
      have hi := congrFun hab i
      exact Fin.ext_iff.mp hi
    exact Subtype.ext hfun

/-- Weak compositions of `n` into `d` parts form a finite type (same
coordinate bound as `hsAssemble_fintype_degreeEq`). -/
noncomputable instance hsAssemble_fintype_sumEq (d n : ℕ) :
    Fintype {f : Fin d → ℕ // ∑ i, f i = n} := by
  refine Fintype.ofInjective (fun f : {f : Fin d → ℕ // ∑ i, f i = n} =>
    fun i : Fin d => (⟨f.val i, ?_⟩ : Fin (n + 1))) ?_
  · have hle : f.val i ≤ n :=
      calc f.val i ≤ ∑ j, f.val j :=
            Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
        _ = n := f.property
    omega
  · intro a b hab
    have hfun : a.val = b.val := by
      funext i
      have hi := congrFun hab i
      exact Fin.ext_iff.mp hi
    exact Subtype.ext hfun

/-- Stars-and-bars counting, function form: weak compositions of `n` into
`d + 1` parts number `C(n + d, d)`. HilbertFunctionCount on `d`: splitting off the
first coordinate (`Fin.sum_univ_succ`) fibers the count over its value,
and the hockey-stick identity (`Nat.sum_range_add_choose`, after
reflection `Finset.sum_range_reflect`) sums the fibers. -/
theorem hsAssemble_card_sumEq : ∀ (d n : ℕ),
    Fintype.card {f : Fin (d + 1) → ℕ // ∑ i, f i = n} =
      Nat.choose (n + d) d := by
  intro d
  induction d with
  | zero =>
    intro n
    change Fintype.card {f : Fin 1 → ℕ // ∑ i, f i = n} = Nat.choose n 0
    rw [Nat.choose_zero_right, Fintype.card_eq_one_iff]
    refine ⟨⟨fun _ => n, by rw [Fin.sum_univ_one]⟩, fun g => ?_⟩
    refine Subtype.ext ?_
    funext i
    rw [Fin.eq_zero i]
    have h := g.property
    rw [Fin.sum_univ_one] at h
    exact h
  | succ d ih =>
    intro n
    let e : {f : Fin (d + 1 + 1) → ℕ // ∑ i, f i = n} ≃
        Σ k : Fin (n + 1), {g : Fin (d + 1) → ℕ // ∑ i, g i = n - k.val} :=
      { toFun := fun f =>
          ⟨⟨f.val 0, by
              have h := f.property
              rw [Fin.sum_univ_succ] at h
              omega⟩,
            Fin.tail f.val, by
              have h := f.property
              rw [Fin.sum_univ_succ] at h
              change ∑ i : Fin (d + 1), f.val i.succ = n - f.val 0
              omega⟩
        invFun := fun s =>
          ⟨Fin.cons s.1.val s.2.val, by
            rw [Fin.sum_cons]
            have h := s.2.property
            have hk := s.1.2
            omega⟩
        left_inv := fun f => by
          refine Subtype.ext ?_
          exact Fin.cons_self_tail f.val
        right_inv := fun s => by
          obtain ⟨⟨k, hk⟩, ⟨g, hg⟩⟩ := s
          simp only [Fin.tail_cons]
          exact Sigma.ext (Fin.ext rfl) (heq_of_eq (Subtype.ext rfl)) }
    rw [Fintype.card_congr e, Fintype.card_sigma]
    simp_rw [ih]
    have hsum : (∑ k : Fin (n + 1), Nat.choose (n - k.val + d) d) =
        ∑ i ∈ Finset.range (n + 1), Nat.choose (n - i + d) d := by
      have h := Fin.sum_univ_eq_sum_range
        (fun i => Nat.choose (n - i + d) d) (n + 1)
      exact h
    rw [hsum]
    have hrefl := Finset.sum_range_reflect
      (fun j => Nat.choose (j + d) d) (n + 1)
    rw [show n + 1 - 1 = n from by omega] at hrefl
    rw [hrefl, Nat.sum_range_add_choose]
    congr 1

/-- Stars-and-bars counting, finsupp form: degree-`n` exponents biject
with weak compositions (`Finsupp.equivFunOnFinite` preserves the sum by
`Finsupp.degree_eq_sum`). -/
theorem hsAssemble_card_degreeEq (d n : ℕ) :
    Fintype.card {e : Fin d →₀ ℕ // e.degree = n} =
      Fintype.card {f : Fin d → ℕ // ∑ i, f i = n} := by
  refine Fintype.card_congr
    (Equiv.subtypeEquiv Finsupp.equivFunOnFinite fun e => ?_)
  show e.degree = n ↔ ∑ i, Finsupp.equivFunOnFinite e i = n
  rw [Finsupp.degree_eq_sum]
  exact Iff.rfl

/-- The finrank of the degree-`n` homogeneous piece is the number of
degree-`n` exponents: the piece is the span of the monomial singles
(`homogeneousSubmodule_eq_finsupp_supported` plus
`AddMonoidAlgebra.supported_eq_span_single`), and monomials are linearly
independent (`MvPolynomial.basisMonomials` restricted to the degree set). -/
theorem hsAssemble_finrank_homogeneous (κ : Type*) [Field κ] (d n : ℕ) :
    Module.finrank κ ↥(MvPolynomial.homogeneousSubmodule (Fin d) κ n) =
      Fintype.card {e : Fin d →₀ ℕ // e.degree = n} := by
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported,
    AddMonoidAlgebra.supported_eq_span_single]
  have hsing : (fun m : Fin d →₀ ℕ => AddMonoidAlgebra.single m (1 : κ)) =
      (fun m : Fin d →₀ ℕ => MvPolynomial.monomial m (1 : κ)) :=
    funext fun m => MvPolynomial.single_eq_monomial m 1
  rw [hsing]
  have him : ((fun m : Fin d →₀ ℕ => MvPolynomial.monomial m (1 : κ)) ''
        {e | e.degree = n}) =
      Set.range (fun a : {e : Fin d →₀ ℕ // e.degree = n} =>
        MvPolynomial.monomial a.val (1 : κ)) := by
    ext x
    simp only [Set.mem_image, Set.mem_range, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
    · rintro ⟨⟨a, ha⟩, rfl⟩
      exact ⟨a, ha, rfl⟩
  rw [him]
  have hli : LinearIndependent κ
      (fun a : {e : Fin d →₀ ℕ // e.degree = n} =>
        MvPolynomial.monomial a.val (1 : κ)) := by
    have h := (MvPolynomial.basisMonomials (Fin d) κ).linearIndependent
    rw [MvPolynomial.coe_basisMonomials] at h
    exact h.comp _ Subtype.val_injective
  exact finrank_span_eq_card hli

/-- R1: the stars-and-bars identity for the domain Hilbert function. -/
theorem hsAssemble_domainHilbert_eq_choose (κ : Type*) [Field κ] (d : ℕ)
    (hd : 1 ≤ d) (n : ℕ) :
    hsAssemble_domainHilbert κ d n = Nat.choose (n + d - 1) (d - 1) := by
  obtain ⟨d', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  change hsAssemble_domainHilbert κ (d' + 1) n =
    Nat.choose (n + (d' + 1) - 1) (d' + 1 - 1)
  have : Module.Finite κ
      ↥(MvPolynomial.homogeneousSubmodule (Fin (d' + 1)) κ n) :=
    Module.finite_def.mpr ((Submodule.fg_top _).mpr
      (MvPolynomial.homogeneousSubmodule_fg (Fin (d' + 1)) κ n))
  unfold hsAssemble_domainHilbert
  rw [finLength_eq_finrank, hsAssemble_finrank_homogeneous,
    hsAssemble_card_degreeEq, hsAssemble_card_sumEq]
  congr 1

/-- R1 discharge: the unconditional domain growth bound. -/
theorem hsAssemble_hF (κ : Type*) [Field κ] (d : ℕ) (hd : 1 ≤ d) :
    IsPolyGrowth (fun n => ((hsAssemble_domainHilbert κ d n : ℕ) : ℚ))
      (d - 1) :=
  hsAssemble_hF_of_starsBars κ d hd
    (fun n => hsAssemble_domainHilbert_eq_choose κ d hd n)

/-! ## §14. The `d = 0` case and closed Artinian masters (R4 closed)

For `d = 0`, `hgen` says the maximal ideal is spanned by nothing, hence
`𝔪 = ⊥` (`hsAssemble_maximalIdeal_eq_bot_of_zero`): `R_P` is a field.
Every `p : MvPolynomial (Fin 0) κ` is a constant
(`hsAssemble_finZero_eq_C`, via `MvPolynomial.isEmptyRingEquiv`), and
constants map through `coeffHom`, which is injective
(`hsAssemble_coeffHom_injective`, via the M4a identification
`grPiece_zero_equiv_quotient`); hence `ker = ⊥` unconditionally
(`hsAssemble_ker_eq_bot_zero`) with unconditional identification
(`hsAssemble_grEquiv_zero`). The Artinian masters at `d = 1` take `hF₀`
from §13 (`hsAssemble_hF_one`), leaving only the genuine quotient
residuals `hnonvan`/`hdrop₀`.

conditional-explicit on `hnonvan`, `hdrop₀` (`hF₀` closed). -/

/-- M4a computes on `grMk0`: the identification sends the class of `r` to
`mk r`. -/
theorem hsAssemble_grPiece_zero_equiv_grMk0 {R : Type*} [CommRing R]
    (I : Ideal R) (r : R) :
    grPiece_zero_equiv_quotient R I (grMk0 R I r) =
      Ideal.Quotient.mk I r :=
  grPiece_zero_to_quotient_mk R I _

/-- The coefficient map is injective: degree-0 components extract along
`DirectSum.of_eq_same`, and M4a identifies them with quotient classes. -/
theorem hsAssemble_coeffHom_injective {R : Type*} [CommRing R] (I : Ideal R) :
    Function.Injective (coeffHom R I) := by
  intro a b hab
  rw [← Ideal.Quotient.mk_out a, ← Ideal.Quotient.mk_out b, coeffHom_mk,
    coeffHom_mk] at hab
  have hab2 : DirectSum.of (grPiece R I) 0 (grMk0 R I (Quotient.out a)) =
      DirectSum.of (grPiece R I) 0 (grMk0 R I (Quotient.out b)) := hab
  have h0 := congrArg (fun s : DirectSum ℕ (grPiece R I) => s 0) hab2
  rw [DirectSum.of_eq_same, DirectSum.of_eq_same] at h0
  have h1 := congrArg (grPiece_zero_equiv_quotient R I) h0
  rw [hsAssemble_grPiece_zero_equiv_grMk0, hsAssemble_grPiece_zero_equiv_grMk0,
    Ideal.Quotient.mk_out, Ideal.Quotient.mk_out] at h1
  exact h1

/-- Polynomials in no variables are constants. -/
theorem hsAssemble_finZero_eq_C (R : Type*) [CommRing R]
    (p : MvPolynomial (Fin 0) R) : p = MvPolynomial.C (p.coeff 0) := by
  have h := (MvPolynomial.isEmptyRingEquiv R (Fin 0)).symm_apply_apply p
  rw [MvPolynomial.isEmptyRingEquiv_symm_apply] at h
  rw [MvPolynomial.isEmptyRingEquiv_eq_coeff_zero] at h
  exact h.symm

/-- At `d = 0` the graded surjection has trivial kernel: every input is a
constant, and constants map through the injective `coeffHom`. -/
theorem hsAssemble_ker_polySurj_zero {R : Type*} [CommRing R] (I : Ideal R)
    (g : Fin 0 → R) (hgen : Ideal.span (Set.range g) = I) :
    RingHom.ker (polySurj R I 0 g hgen) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro p hp
  have hC : p = MvPolynomial.C (p.coeff 0) :=
    hsAssemble_finZero_eq_C (R ⧸ I) p
  rw [RingHom.mem_ker, hC, polySurj_C] at hp
  have h0 : p.coeff 0 = 0 := by
    apply hsAssemble_coeffHom_injective I
    rw [hp, map_zero]
  rw [hC, h0, map_zero]

/-- The `d = 1` case of the unconditional domain bound (the Artinian
`hF₀`, since `1 - 1 = 0`). -/
theorem hsAssemble_hF_one (κ : Type*) [Field κ] :
    IsPolyGrowth (fun n => ((hsAssemble_domainHilbert κ 1 n : ℕ) : ℚ)) 0 :=
  hsAssemble_hF κ 1 (le_refl 1)

section ZeroCase

variable {K : Type*} [Field K] {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K))
  [P.IsPrime]

/-- At `d = 0`, `hgen` forces the maximal ideal to `⊥`: `R_P` is a field. -/
theorem hsAssemble_maximalIdeal_eq_bot_of_zero
    (g : Fin 0 → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    IsLocalRing.maximalIdeal (Localization.AtPrime P) = ⊥ := by
  rw [← hgen]
  have hempty : Set.range g = ∅ :=
    Set.eq_empty_iff_forall_notMem.mpr (fun x hx => by
      obtain ⟨i, _⟩ := hx
      exact Fin.isEmpty.false i)
  rw [hempty]
  exact Submodule.span_empty

/-- R4: `ker = ⊥` at `d = 0`, unconditionally. -/
theorem hsAssemble_ker_eq_bot_zero (g : Fin 0 → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    RingHom.ker (polySurjResidue P 0 g hgen) = ⊥ :=
  hsAssemble_ker_polySurj_zero _ g hgen

/-- R4: the graded identification at `d = 0`, unconditionally. -/
noncomputable def hsAssemble_grEquiv_zero (g : Fin 0 → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    MvPolynomial (Fin 0) (IsLocalRing.ResidueField (Localization.AtPrime P)) ≃+*
      grRegular P :=
  hsAssemble_isoOfKerEqBot P 0 g hgen
    (hsAssemble_ker_eq_bot_zero P g hgen)

/-- R4: the Artinian kernel master at `d = 1` with `hF₀` discharged —
conditional only on the genuine quotient residuals. -/
theorem hsAssemble_ker_eq_bot_artinian_one
    (g : Fin 1 → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (Hq : ℕ → ℕ)
    (hnonvan : ¬ (fun n => ((Hq (n + 1) : ℕ) : ℚ)) =ᶠ[Filter.atTop] 0)
    (hdrop₀ : RingHom.ker (polySurjResidue P 1 g hgen) ≠ ⊥ →
      ∃ J : Ideal (Localization.AtPrime P),
        (∀ Q ∈ J.minimalPrimes,
          Q ≠ IsLocalRing.maximalIdeal (Localization.AtPrime P)) ∧
        (∀ A ∈ associatedPrimes (Localization.AtPrime P)
          (Localization.AtPrime P ⧸ J),
          ¬ IsLocalRing.maximalIdeal (Localization.AtPrime P) ≤ A) ∧
        (∀ n, Hq (n + 1) +
            hsAssemble_domainHilbert
              (IsLocalRing.ResidueField (Localization.AtPrime P)) 1 n =
            hsAssemble_domainHilbert
              (IsLocalRing.ResidueField (Localization.AtPrime P)) 1 (n + 1))) :
    RingHom.ker (polySurjResidue P 1 g hgen) = ⊥ :=
  hsAssemble_ker_eq_bot_artinian P 1 g hgen
    (hsAssemble_domainHilbert (IsLocalRing.ResidueField (Localization.AtPrime P))
      1)
    Hq (hsAssemble_hF_one _) hnonvan hdrop₀

/-- R4: the Artinian identification master at `d = 1` with `hF₀`
discharged. -/
noncomputable def hsAssemble_grEquiv_artinian_one
    (g : Fin 1 → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (Hq : ℕ → ℕ)
    (hnonvan : ¬ (fun n => ((Hq (n + 1) : ℕ) : ℚ)) =ᶠ[Filter.atTop] 0)
    (hdrop₀ : RingHom.ker (polySurjResidue P 1 g hgen) ≠ ⊥ →
      ∃ J : Ideal (Localization.AtPrime P),
        (∀ Q ∈ J.minimalPrimes,
          Q ≠ IsLocalRing.maximalIdeal (Localization.AtPrime P)) ∧
        (∀ A ∈ associatedPrimes (Localization.AtPrime P)
          (Localization.AtPrime P ⧸ J),
          ¬ IsLocalRing.maximalIdeal (Localization.AtPrime P) ≤ A) ∧
        (∀ n, Hq (n + 1) +
            hsAssemble_domainHilbert
              (IsLocalRing.ResidueField (Localization.AtPrime P)) 1 n =
            hsAssemble_domainHilbert
              (IsLocalRing.ResidueField (Localization.AtPrime P)) 1 (n + 1))) :
    MvPolynomial (Fin 1) (IsLocalRing.ResidueField (Localization.AtPrime P)) ≃+*
      grRegular P :=
  hsAssemble_isoOfKerEqBot P 1 g hgen
    (hsAssemble_ker_eq_bot_artinian_one P g hgen Hq hnonvan hdrop₀)

end ZeroCase

#print axioms growth_exact_of_not_vanishing
#print axioms growth_drop_of_vanishing
#print axioms hsAssemble_quotDegree_lt
#print axioms hsAssemble_finLength_quot_le
#print axioms hsAssemble_ker_eq_bot_of_le_adic
#print axioms hsAssemble_injective_of_ker_le_adic
#print axioms hsAssemble_isoOfKerEqBot
#print axioms hsAssemble_ker_eq_bot
#print axioms hsAssemble_grEquiv
#print axioms hsAssemble_quotEventuallyZero
#print axioms hsAssemble_ker_eq_bot_artinian
#print axioms hsAssemble_ker_eq_bot_of_dim
#print axioms chooseFun_isPolyGrowth
#print axioms isPolyGrowth_comp_add
#print axioms hsAssemble_hF_of_starsBars
#print axioms hsAssemble_hdimEq_of_not_vanishing
#print axioms hsAssemble_ker_eq_bot_of_mult
#print axioms hsAssemble_of_sum_eq_zero
#print axioms hsAssemble_polySurj_of_homogeneous
#print axioms hsAssemble_ker_homogeneousComponent_mem
#print axioms hsAssemble_exists_homogeneous_mem_ker
#print axioms hsAssemble_ker_eq_bot_of_principal
#print axioms hsAssemble_card_sumEq
#print axioms hsAssemble_card_degreeEq
#print axioms hsAssemble_finrank_homogeneous
#print axioms hsAssemble_domainHilbert_eq_choose
#print axioms hsAssemble_hF
#print axioms hsAssemble_grPiece_zero_equiv_grMk0
#print axioms hsAssemble_coeffHom_injective
#print axioms hsAssemble_finZero_eq_C
#print axioms hsAssemble_ker_polySurj_zero
#print axioms hsAssemble_hF_one
#print axioms hsAssemble_maximalIdeal_eq_bot_of_zero
#print axioms hsAssemble_ker_eq_bot_zero
#print axioms hsAssemble_grEquiv_zero
#print axioms hsAssemble_ker_eq_bot_artinian_one
#print axioms hsAssemble_grEquiv_artinian_one

end GradedSurjectionInjective
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
