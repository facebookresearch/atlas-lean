/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.NewtonDifferences
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.LengthFramework
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.FiltrationStability
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.YSopStep
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.SystemOfParametersExistence
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.HilbertSerre
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.GradedSurjectionInjective
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.HilbertSamuelDegree

/-!
# Superficial reduction for the χ-degree
Dimension reduction for the Hilbert–Samuel degree via s.o.p. elements
(used as the superficial sequence). For `y` the first s.o.p. element, the `y`-quotient Hilbert
function `Hq` satisfies the SES equation against `H`, and the growth
degree drops by exactly one; iterating down to dimension zero bounds
`deg χ ≤ dim A`. Textbook mathematics (Atiyah–Macdonald Ch. 11 /
Matsumura §14), outside the crux ring: no circularity.

## What this file proves

* (§0) Reduction data: `IsSupSes` (the eventual SES equation),
  `IsARStableFor` (Artin–Rees trace stabilization — the stability half
  of superficiality), `SupSelectData`/`SupStepData` (the s.o.p.-step
  datum: `y ∈ 𝔪` + minimal-prime avoidance + regularity),
  `supChi` (the relative Hilbert–Samuel function
  `χ_J n = length(R ⧸ (𝔪^{n+1} ⊔ J))`, generalizing `hsSamuel`),
  `SupSesAssembly` + `SupDimZeroBase` (the two residual SPEC shapes).
* (§1) Sequence-level degree drop (unconditional): `supSplit_seqDiff`,
  `supSes_diff_eventuallyEq` (eventual SES equation says the quotient
  sequence is `ΔH` — the eventual form of `ysop_quot_eq_seqDiff`),
  `supGrowth_of_iterDiff_eventuallyEq` (iterated-difference lifting),
  `supQuot_growth_drop` (drop: quotient growth `≤ d - 1`),
  `supTotal_growth_lift` (lift: total growth `≤ e + 1` from quotient
  `≤ e`), `sup_exactDrop_of_nonvanishing` (exact degree `d - 1` from
  nonvanishing — the "exactly one" half; multiplicity input stays
  with H3).
* (§2) Ring-level inputs (unconditional): `sup_arStable_of_artinRees`
  (every element is AR-stable — the Filtration wrapper),
  `supSopSelect` (s.o.p.-step selection — the SopExist §2 wrapper),
  `supStepData_of_avoidance` (full datum incl. regularity — the Ysop
  §2 wrapper), `supStepData_dimDrop` (Krull dimension drops — the
  SopExist §3 wrapper), `sup_lengthFin_supChi` (length finiteness for
  `χ_J` — via HSDegree §2 + double-quotient identification),
  `supChi_bot` (`χ_⊥ = hsSamuel` bridge).
* (§3) Masters: `sup_sopReduction_master` (one-step joint: dimension
  drops and growth drops, conditional-exact on `[IsSupSes]`),
  `sup_chi_degree_le_dim` (iteration to dimension zero,
  conditional-exact on `[hsop-select, har, hfin, hses-rule, hbase]`,
  of which `hsop`/`har`/`hfin` discharge unconditionally in §2),
  `sup_chi_degree_le_dim_supChi` (the `χ := supChi` corollary,
  conditional-exact on `[SupSesAssembly, SupDimZeroBase]` only).
* (§4, doc-only) Residual register: the two SPECs and their
  discharge routes.

## Status

* §1: all unconditional.
* §2: all unconditional.
* §3: `sup_sopReduction_master` conditional-exact on `[IsSupSes H Hq]`
  (select-data discharges via `supSopSelect`);
  `sup_chi_degree_le_dim` conditional-exact on the five listed inputs
  (three discharge in §2; effective residual `[SupSesAssembly χ,
  SupDimZeroBase χ]`); `sup_chi_degree_le_dim_supChi`
  conditional-exact on `[SupSesAssembly supChi, SupDimZeroBase
  supChi]`.
* Angle split with H1 (no overlap): H1 owns rationality via Hilbert
  series; this file owns reduction via s.o.p. (different suppliers:
  SopExist/Ysop/Filtration here).

## References

Project (read-only):
* `Regularity/Multiplicity/NewtonDifferences.lean`: `seqDiff` (:123),
  `seqDiff_one_apply` (:156), `seqDiff_eventuallyEq_of_eventuallyEq`
  (:237), `IsPolyGrowth` (:465) + `.mono` (:472),
  `exists_topCoeff_of_isPolyGrowth` (:491).
* `Regularity/Koszul/YSopStep.lean`:
  `exists_ysop_regular_avoid_minimalPrimes` (:172),
  `seqDiff_iter_add` (:268), `ysop_quot_eq_seqDiff` (:280, the ∀-form
  generalized here to eventual).
* `Regularity/Koszul/SystemOfParametersExistence.lean`:
  `exists_mem_maximal_avoid_minimalPrimes_ne_maximal` (:166),
  `krullDimLE_quotient_sup_span_singleton` (:199).
* `Regularity/Koszul/FiltrationStability.lean`: `artinRees_ideal` (:214).
* `Regularity/Koszul/LengthFramework.lean`: `isFiniteLength_quotient` (:161),
  `finLength` (:211).
* `Regularity/Multiplicity/HilbertSerre.lean`:
  `hsIsPolyGrowth_comp_add_succ` (:1606),
  `hsExists_isPolyGrowth_of_seqDiff_eventuallyEq` (:1868).
* `Regularity/Multiplicity/GradedSurjectionInjective.lean`:
  `growth_exact_of_not_vanishing` (:168).
* `Regularity/Multiplicity/HilbertSamuelDegree.lean`:
  `hsDegree_isFiniteLength_quot_pow` (:380), `hsSamuel` (:405).

Mathlib (`lean-toolchain` pins `v4.34.0`), all read-only:
* `LinearAlgebra/Isomorphisms.lean`:
  `Submodule.quotientQuotientEquivQuotientSup`.
* `RingTheory/FiniteLength.lean`: `LinearEquiv.isFiniteLength`.
* `Order/Filter/AtTopBot/Basic.lean`: `Filter.eventually_atTop`.
-/

open scoped Polynomial

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace SuperficialReduction

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.NewtonDifferences
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.LengthFramework
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.FiltrationStability
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.YSopStep
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.SystemOfParametersExistence
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.HilbertSerre
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjectionInjective
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.HilbertSamuelDegree

/-! ## §0. Reduction data -/

/-- The eventual SES length equation linking a Hilbert–Samuel function
`H` to its `y`-quotient `Hq`: `Hq (n+1) + H n = H (n+1)` from some rank
on. This is the eventual form of the `ysop_quot_eq_seqDiff` equation
(Ysop:280, which needs the equation at every `n`); the eventual form
is what Artin–Rees stabilization delivers, since the kernel filtration
of mul-by-`y` stabilizes only past some rank. -/
def IsSupSes (H Hq : ℕ → ℕ) : Prop :=
  ∃ c : ℕ, ∀ n : ℕ, c ≤ n → Hq (n + 1) + H n = H (n + 1)

/-- Artin–Rees trace stabilization for `y`: the trace of the `I`-adic
filtration on `span {y}` stabilizes, in the exact
`artinRees_ideal` (Filtration:214) shape. This is the stability half
of superficiality — the form the SES argument consumes (the colon form
is equivalent for regular `y`; that equivalence is standard but not
formalized here). -/
def IsARStableFor {R : Type*} [CommRing R] (I : Ideal R) (y : R) : Prop :=
  ∃ k : ℕ, ∀ n : ℕ, k ≤ n →
    (I ^ n ⊓ Ideal.span {y} : Ideal R)
      = I ^ (n - k) * (I ^ k ⊓ Ideal.span {y})

/-- The s.o.p.-selection datum: `y ∈ 𝔪` avoiding every minimal prime
over `J` except possibly `𝔪` itself — the exact SopExist §2 output
shape (`exists_mem_maximal_avoid_minimalPrimes_ne_maximal`,:166),
which is also the exact SopExist §3 input shape. -/
def SupSelectData {R : Type*} [CommRing R] [IsLocalRing R] (J : Ideal R)
    (y : R) : Prop :=
  y ∈ IsLocalRing.maximalIdeal R ∧
    ∀ Q ∈ J.minimalPrimes, Q ≠ IsLocalRing.maximalIdeal R → y ∉ Q

/-- The full s.o.p.-step datum: selection plus regularity mod `J` —
the exact Ysop §2 output shape
(`exists_ysop_regular_avoid_minimalPrimes`,:172). Regularity is what
kills the SES defect `(0 : y)` when discharging `SupSesAssembly`. -/
def SupStepData {R : Type*} [CommRing R] [IsLocalRing R] (J : Ideal R)
    (y : R) : Prop :=
  SupSelectData J y ∧ IsSMulRegular (R ⧸ J) y

/-- The relative Hilbert–Samuel function: `R`-lengths of quotients by
`𝔪^{n+1} ⊔ J`. At `J = ⊥` this is `hsSamuel` (`supChi_bot`). The
relative form is what the s.o.p. induction needs, since each step
passes from `J` to `J ⊔ span {y}`. Absent from Mathlib v4.34.0. -/
noncomputable def supChi {R : Type*} [CommRing R] [IsLocalRing R]
    (J : Ideal R) (n : ℕ) : ℕ :=
  finLength R (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 1) ⊔ J))

/-- SPEC (residual): the SES-assembly rule. From `y ∈ 𝔪`,
AR-stability of `y`, and length finiteness on both sides, conclude the
eventual SES equation for `χ`. This packages the mul-by-`y` SES on
adic quotients (kernel/cokernel identification + SES additivity of
length); all its antecedents are proved (`sup_arStable_of_artinRees`,
`sup_lengthFin_supChi`), only the assembly step itself is missing. -/
def SupSesAssembly {R : Type*} [CommRing R] [IsLocalRing R]
    (χ : Ideal R → ℕ → ℕ) : Prop :=
  ∀ (J' : Ideal R) (y : R), y ∈ IsLocalRing.maximalIdeal R →
    IsARStableFor (IsLocalRing.maximalIdeal R) y →
    (∀ n : ℕ, IsFiniteLength R
      (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 1) ⊔ J'))) →
    (∀ n : ℕ, IsFiniteLength R
      (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 1)
        ⊔ (J' ⊔ Ideal.span {y})))) →
    IsSupSes (χ J') (χ (J' ⊔ Ideal.span {y}))

/-- SPEC (residual): the dimension-zero base case. Over a
zero-dimensional quotient, `χ` has growth degree `0` (the adic
filtration stabilizes, so `χ` is eventually constant). H3 supplier
(needs Artinian stabilization + Nakayama, not in tree). -/
def SupDimZeroBase {R : Type*} [CommRing R] [IsLocalRing R]
    (χ : Ideal R → ℕ → ℕ) : Prop :=
  ∀ J' : Ideal R, Ring.KrullDimLE 0 (R ⧸ J') →
    IsPolyGrowth (fun n => ((χ J' n : ℕ) : ℚ)) 0

/-! ## §1. Sequence-level degree drop -/

/-- Difference splitting: `Δ^k (ΔF) = Δ^{k+1} F` (symmetric form of
Ysop `seqDiff_iter_add`,:268). -/
theorem supSplit_seqDiff (F : ℕ → ℚ) (k : ℕ) :
    seqDiff k (seqDiff 1 F) = seqDiff (k + 1) F := by
  exact (seqDiff_iter_add F k 1).symm

#print axioms supSplit_seqDiff

/-- The eventual SES equation says the (shifted) quotient sequence is
the first difference of `H` — the eventual generalization of
`ysop_quot_eq_seqDiff` (Ysop:280; same `ℕ`-subtraction argument via
`Nat.cast_sub`, applied past the stabilization rank).
-/
theorem supSes_diff_eventuallyEq (H Hq : ℕ → ℕ) (hses : IsSupSes H Hq) :
    (fun n => ((Hq (n + 1) : ℕ) : ℚ)) =ᶠ[Filter.atTop]
      seqDiff 1 (fun n => ((H n : ℕ) : ℚ)) := by
  obtain ⟨c, hc⟩ := hses
  refine Filter.eventually_atTop.mpr ⟨c, fun n hn => ?_⟩
  have h := hc n hn
  have hle : H n ≤ H (n + 1) := by omega
  have hsub : Hq (n + 1) = H (n + 1) - H n := by omega
  change ((Hq (n + 1) : ℕ) : ℚ) = seqDiff 1 (fun n => ((H n : ℕ) : ℚ)) n
  rw [hsub, Nat.cast_sub hle, seqDiff_one_apply]

#print axioms supSes_diff_eventuallyEq

/-- Iterated-difference lifting: if `Δ^k F` is eventually a polynomial
`Q`, then `F` has growth bound `Q.natDegree + k`. HilbertFunctionCount on `k`,
peeling one difference per step with the degree-tracked lift
`hsExists_isPolyGrowth_of_seqDiff_eventuallyEq` (HilbertSerre:1868).
-/
theorem supGrowth_of_iterDiff_eventuallyEq (F : ℕ → ℚ) (Q : ℚ[X])
    (k : ℕ) (h : seqDiff k F =ᶠ[Filter.atTop] evalFun Q) :
    IsPolyGrowth F (Q.natDegree + k) := by
  revert F h
  induction k with
  | zero =>
    intro F h
    rw [seqDiff_zero] at h
    exact ⟨Q, Nat.le_add_right _ _, h⟩
  | succ k ih =>
    intro F h
    rw [seqDiff_succ', ← seqDiff_one] at h
    obtain ⟨P, hPdeg, hP⟩ := ih (seqDiff 1 F) h
    have hlift := hsExists_isPolyGrowth_of_seqDiff_eventuallyEq hP
    exact hlift.mono (by omega)

#print axioms supGrowth_of_iterDiff_eventuallyEq

/-- Drop: the quotient growth degree drops by (at least) one. From
`IsPolyGrowth H d` with `1 ≤ d` and the eventual SES equation, the
shifted quotient sequence has growth `≤ d - 1`. Proof: the quotient is
eventually `ΔH` (`supSes_diff_eventuallyEq`), so `Δ^{d-1}` of it is
eventually `Δ^d H`, which is eventually constant (top coefficient,
Newton:491); the iterated lift (`supGrowth_of_iterDiff_eventuallyEq`
with `Q = C c`) gives bound `0 + (d - 1)`.
-/
theorem supQuot_growth_drop (H Hq : ℕ → ℕ) (d : ℕ)
    (hses : IsSupSes H Hq)
    (hF : IsPolyGrowth (fun n => ((H n : ℕ) : ℚ)) d) (hd : 1 ≤ d) :
    IsPolyGrowth (fun n => ((Hq (n + 1) : ℕ) : ℚ)) (d - 1) := by
  obtain ⟨c, hc⟩ := exists_topCoeff_of_isPolyGrowth hF
  have hΔ : (fun n => ((Hq (n + 1) : ℕ) : ℚ)) =ᶠ[Filter.atTop]
      seqDiff 1 (fun n => ((H n : ℕ) : ℚ)) :=
    supSes_diff_eventuallyEq H Hq hses
  have hd0 : d ≠ 0 := by omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd0
  have hcong := seqDiff_eventuallyEq_of_eventuallyEq hΔ k
  rw [supSplit_seqDiff] at hcong
  have hfun : (fun _ : ℕ => (Nat.factorial (k + 1) : ℚ) * c)
      = evalFun (Polynomial.C ((Nat.factorial (k + 1) : ℚ) * c)) := by
    funext n
    simp [evalFun]
  have hQ0 : seqDiff k (fun n => ((Hq (n + 1) : ℕ) : ℚ)) =ᶠ[Filter.atTop]
      evalFun (Polynomial.C ((Nat.factorial (k + 1) : ℚ) * c)) := by
    rw [← hfun]
    exact hcong.trans hc
  have hgrade := supGrowth_of_iterDiff_eventuallyEq _ _ k hQ0
  rw [Polynomial.natDegree_C, Nat.zero_add] at hgrade
  have hkk : k.succ - 1 = k := by omega
  rwa [hkk]

#print axioms supQuot_growth_drop

/-- Lift: the total growth degree rises by (at most) one over the
quotient. From the eventual SES equation and quotient growth `≤ e`,
`H` has growth `≤ e + 1`. Proof: `ΔH` is eventually the quotient
sequence (`supSes_diff_eventuallyEq`, symmetric), hence eventually a
polynomial of degree `≤ e`; the degree-tracked lift (HilbertSerre
:1868) gives `H` growth `≤ e + 1`. This is the direction the
dimension induction (§3) consumes.
-/
theorem supTotal_growth_lift (H Hq : ℕ → ℕ) (e : ℕ)
    (hses : IsSupSes H Hq)
    (hG : IsPolyGrowth (fun n => ((Hq (n + 1) : ℕ) : ℚ)) e) :
    IsPolyGrowth (fun n => ((H n : ℕ) : ℚ)) (e + 1) := by
  obtain ⟨P, hPdeg, hP⟩ := hG
  have hsesΔ := supSes_diff_eventuallyEq H Hq hses
  have hΔ : seqDiff 1 (fun n => ((H n : ℕ) : ℚ)) =ᶠ[Filter.atTop]
      evalFun P :=
    hsesΔ.symm.trans hP
  have hlift := hsExists_isPolyGrowth_of_seqDiff_eventuallyEq hΔ
  exact hlift.mono (by omega)

#print axioms supTotal_growth_lift

/-- Exact drop: nonvanishing pins the quotient degree at exactly
`d - 1`. From `IsPolyGrowth H d` with `¬ Δ^d H =ᶠ 0`, the eventual SES
equation, and `1 ≤ d`, the shifted quotient sequence is eventually a
polynomial of degree exactly `d - 1` (upper bound by
`supQuot_growth_drop`, lower bound by congruence transfer of
nonvanishing, exactness by `growth_exact_of_not_vanishing`,
HSAssemble:168). The multiplicity input supplying `hne` stays with
H3.
-/
theorem sup_exactDrop_of_nonvanishing (H Hq : ℕ → ℕ) (d : ℕ)
    (hses : IsSupSes H Hq)
    (hF : IsPolyGrowth (fun n => ((H n : ℕ) : ℚ)) d)
    (hne : ¬ seqDiff d (fun n => ((H n : ℕ) : ℚ)) =ᶠ[Filter.atTop] 0)
    (hd : 1 ≤ d) :
    ∃ S : ℚ[X], S.natDegree = d - 1 ∧
      (fun n => ((Hq (n + 1) : ℕ) : ℚ)) =ᶠ[Filter.atTop] evalFun S := by
  have hdrop : IsPolyGrowth (fun n => ((Hq (n + 1) : ℕ) : ℚ)) (d - 1) :=
    supQuot_growth_drop H Hq d hses hF hd
  have hneG : ¬ seqDiff (d - 1) (fun n => ((Hq (n + 1) : ℕ) : ℚ))
      =ᶠ[Filter.atTop] 0 := by
    intro hvan
    apply hne
    have hd0 : d ≠ 0 := by omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd0
    have hkk : k.succ - 1 = k := by omega
    rw [hkk] at hvan
    have hΔ := supSes_diff_eventuallyEq H Hq hses
    have hcong := seqDiff_eventuallyEq_of_eventuallyEq hΔ k
    rw [supSplit_seqDiff] at hcong
    exact hcong.symm.trans hvan
  exact growth_exact_of_not_vanishing hdrop hneG

#print axioms sup_exactDrop_of_nonvanishing

/-! ## §2. Ring-level inputs -/

/-- Every element is AR-stable: direct instantiation of
`artinRees_ideal` (Filtration:214) at `J = span {y}`. This discharges
the `har` input of the iteration master.
-/
theorem sup_arStable_of_artinRees {R : Type*} [CommRing R]
    [IsNoetherianRing R] (I : Ideal R) (y : R) :
    IsARStableFor I y :=
  artinRees_ideal I (Ideal.span {y})

#print axioms sup_arStable_of_artinRees

/-- The s.o.p.-step selection exists: some `y ∈ 𝔪` avoids every minimal
prime over `J` except possibly `𝔪` — direct wrapper over SopExist §2
(`exists_mem_maximal_avoid_minimalPrimes_ne_maximal`,:166). This
discharges the `hsop` input of the iteration master; no positive-dimension
hypothesis is needed since `𝔪`-minimal primes are excluded, not avoided.
-/
theorem supSopSelect {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (J : Ideal R) : ∃ y : R, SupSelectData J y := by
  obtain ⟨y, hym, havoid⟩ :=
    exists_mem_maximal_avoid_minimalPrimes_ne_maximal J
  exact ⟨y, hym, havoid⟩

#print axioms supSopSelect

/-- The full s.o.p.-step datum (selection + regularity mod `J`) exists
under the per-prime non-containment inputs — direct wrapper over Ysop
§2 (`exists_ysop_regular_avoid_minimalPrimes`,:172). The `hne` input
here is the all-primes form; the conditional form in `SupSelectData`
follows by specialization.
-/
theorem supStepData_of_avoidance {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (J : Ideal R)
    (hne : ∀ Q ∈ J.minimalPrimes, Q ≠ IsLocalRing.maximalIdeal R)
    (hle : ∀ P ∈ associatedPrimes R (R ⧸ J),
      ¬ IsLocalRing.maximalIdeal R ≤ P) :
    ∃ y : R, SupStepData J y := by
  obtain ⟨y, hym, hymin, hreg⟩ :=
    exists_ysop_regular_avoid_minimalPrimes J hne hle
  exact ⟨y, ⟨hym, fun Q hQ _ => hymin Q hQ⟩, hreg⟩

#print axioms supStepData_of_avoidance

/-- The s.o.p. step drops Krull dimension by (at least) one — direct
wrapper over SopExist §3
(`krullDimLE_quotient_sup_span_singleton`,:199), whose avoidance
input is exactly `SupSelectData`.
-/
theorem supStepData_dimDrop {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (J : Ideal R) (y : R) (e : ℕ)
    (hsop : SupSelectData J y)
    (hJ : Ring.KrullDimLE (e + 1) (R ⧸ J)) :
    Ring.KrullDimLE e (R ⧸ (J ⊔ Ideal.span {y})) :=
  krullDimLE_quotient_sup_span_singleton J y hsop.2 e hJ

#print axioms supStepData_dimDrop

/-- Length finiteness for the relative quotients: `R ⧸ (𝔪^{n+1} ⊔ J)`
has finite `R`-length. Via HSDegree §2
(`hsDegree_isFiniteLength_quot_pow`,:380) for `R ⧸ 𝔪^{n+1}`,
stability under quotients (`isFiniteLength_quotient`, Length:161),
and transport along the double-quotient identification
(`Submodule.quotientQuotientEquivQuotientSup` +
`LinearEquiv.isFiniteLength`). This discharges the `hfin` input of the
iteration master.
-/
theorem sup_lengthFin_supChi {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (J : Ideal R) (n : ℕ) :
    IsFiniteLength R
      (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 1) ⊔ J)) := by
  have hfin : IsFiniteLength R
      (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1)) :=
    hsDegree_isFiniteLength_quot_pow (n + 1) (by omega)
  have hquot := isFiniteLength_quotient hfin
    (Submodule.map
      (Submodule.mkQ
        (IsLocalRing.maximalIdeal R ^ (n + 1) : Submodule R R))
      (J : Submodule R R))
  have e := Submodule.quotientQuotientEquivQuotientSup
    (IsLocalRing.maximalIdeal R ^ (n + 1) : Submodule R R)
    (J : Submodule R R)
  exact e.isFiniteLength hquot

#print axioms sup_lengthFin_supChi

/-- At `J = ⊥`, the relative function is the absolute one:
`χ_⊥ = hsSamuel` (HSDegree:405), by `sup_bot_eq`.
-/
theorem supChi_bot {R : Type*} [CommRing R] [IsLocalRing R] (n : ℕ) :
    supChi (R := R) (⊥ : Ideal R) n = hsSamuel (R := R) n := by
  unfold supChi hsSamuel
  rw [sup_bot_eq]

#print axioms supChi_bot

/-! ## §3. Reduction masters -/

/-- The s.o.p.-reduction master (one step, joint conclusion): from the
selection datum, the dimension bound, the eventual SES equation, and
the growth bound with `1 ≤ d`, both the Krull dimension drops (via
SopExist §3) and the quotient growth drops to `d - 1` (via §1 drop).
The selection datum discharges unconditionally (`supSopSelect`).

Conditional on exactly `[IsSupSes H Hq]`. -/
theorem sup_sopReduction_master {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (J : Ideal R) (y : R) (e d : ℕ)
    (H Hq : ℕ → ℕ)
    (hsop : SupSelectData J y)
    (hJ : Ring.KrullDimLE (e + 1) (R ⧸ J))
    (hses : IsSupSes H Hq)
    (hF : IsPolyGrowth (fun n => ((H n : ℕ) : ℚ)) d)
    (hd : 1 ≤ d) :
    Ring.KrullDimLE e (R ⧸ (J ⊔ Ideal.span {y})) ∧
      IsPolyGrowth (fun n => ((Hq (n + 1) : ℕ) : ℚ)) (d - 1) := by
  refine ⟨supStepData_dimDrop J y e hsop hJ, ?_⟩
  exact supQuot_growth_drop H Hq d hses hF hd

#print axioms sup_sopReduction_master

/-- The χ-degree iteration master: `deg χ_J ≤ e` from `KrullDimLE e`.
HilbertFunctionCount on `e`, generalizing `J`: at each positive step select `y`
(`hsop`), drop the dimension (SopExist §3), assemble the SES equation
(`hses` fed by `har`/`hfin`), apply the induction hypothesis to the
quotient, shift (`hsIsPolyGrowth_comp_add_succ`, HilbertSerre:1606),
and lift (§1 lift). Base case is `hbase`.

Conditional on exactly `[hsop-select, har, hfin, hses-rule,
hbase]`; `hsop`/`har`/`hfin` discharge unconditionally
(`supSopSelect`, `sup_arStable_of_artinRees`, `sup_lengthFin_supChi`),
so the effective residual is `[SupSesAssembly χ, SupDimZeroBase χ]`. -/
theorem sup_chi_degree_le_dim {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (χ : Ideal R → ℕ → ℕ) (e : ℕ) (J : Ideal R)
    (hJ : Ring.KrullDimLE e (R ⧸ J))
    (hsop : ∀ J' : Ideal R, ∃ y : R, SupSelectData J' y)
    (har : ∀ y : R, IsARStableFor (IsLocalRing.maximalIdeal R) y)
    (hfin : ∀ J' : Ideal R, ∀ n : ℕ, IsFiniteLength R
      (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 1) ⊔ J')))
    (hses : SupSesAssembly χ)
    (hbase : SupDimZeroBase χ) :
    IsPolyGrowth (fun n => ((χ J n : ℕ) : ℚ)) e := by
  revert J hJ
  induction e with
  | zero =>
    intro J hJ
    exact hbase J hJ
  | succ e ih =>
    intro J hJ
    obtain ⟨y, hym, havoid⟩ := hsop J
    have hdrop : Ring.KrullDimLE e (R ⧸ (J ⊔ Ideal.span {y})) :=
      krullDimLE_quotient_sup_span_singleton J y havoid e hJ
    have hsesJy : IsSupSes (χ J) (χ (J ⊔ Ideal.span {y})) :=
      hses J y hym (har y) (hfin J) (hfin (J ⊔ Ideal.span {y}))
    have hIH : IsPolyGrowth
        (fun n => ((χ (J ⊔ Ideal.span {y}) n : ℕ) : ℚ)) e :=
      ih (J ⊔ Ideal.span {y}) hdrop
    have hshift : IsPolyGrowth
        (fun n => ((χ (J ⊔ Ideal.span {y}) (n + 1) : ℕ) : ℚ)) e :=
      hsIsPolyGrowth_comp_add_succ hIH
    exact supTotal_growth_lift (χ J) (χ (J ⊔ Ideal.span {y})) e hsesJy
      hshift

#print axioms sup_chi_degree_le_dim

/-- The iteration master at `χ := supChi`, with the three proved inputs
discharged in-file: conditional-exact on `[SupSesAssembly supChi,
SupDimZeroBase supChi]` only. This is the H3 consumption shape (H3
combines it with H1's rationality for the exact-degree statement).

Conditional on exactly `[SupSesAssembly supChi,
SupDimZeroBase supChi]`. -/
theorem sup_chi_degree_le_dim_supChi {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (e : ℕ) (J : Ideal R)
    (hJ : Ring.KrullDimLE e (R ⧸ J))
    (hses : SupSesAssembly (supChi (R := R)))
    (hbase : SupDimZeroBase (supChi (R := R))) :
    IsPolyGrowth (fun n => ((supChi (R := R) J n : ℕ) : ℚ)) e :=
  sup_chi_degree_le_dim (supChi (R := R)) e J hJ supSopSelect
    (sup_arStable_of_artinRees (IsLocalRing.maximalIdeal R))
    sup_lengthFin_supChi hses hbase

#print axioms sup_chi_degree_le_dim_supChi

/-! ## §4. Residual register (doc-only)

Two SPECs remain; everything else in the reduction chain is proved.

1. `SupSesAssembly χ`: the mul-by-`y` SES equation from
   AR-stability + length finiteness. All antecedents are proved
   (`sup_arStable_of_artinRees`, `sup_lengthFin_supChi`, plus
   `finLength_add_of_submodule` for SES additivity of length and
   `finLength_ses_of_injective` (Ysop:317) for the injection-side
   assembly); only the kernel/cokernel identification of mul-by-`y`
   on `R ⧸ (𝔪^{n+1} ⊔ J)` is missing. The regularity half
   (`SupStepData`, via `supStepData_of_avoidance` from per-prime
   non-containment) kills the kernel defect `(0 : y)`.
2. `SupDimZeroBase χ`: `χ` eventually constant over zero-dimensional
   quotients (Artinian stabilization + Nakayama). H3 supplier.

Given H1's rationality (exact polynomiality of `χ`) + these two, H3
closes the exact statement `deg χ = dim A`, and the §1 exact-drop
lemma turns it into `deg χ_{A/yA} = dim A - 1`.
-/

end SuperficialReduction
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
