/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Submodule

/-!
# Filtration stability: Artin–Rees + Krull intersection (sub-plan M4c-ii, part 2)

Part 2 of the Hilbert–Samuel bypass (sub-plan M4c-ii): the stability and
Artin–Rees consequences for the maximal-ideal-adic filtration of `R_P` that the
`y`-sop step (part 3) and dim-equality consume. Unlike part 1 (Newton
differences, needed because Mathlib's `HilbertPoly` is `CharZero`-only), this
part is a thin verified wrapper layer: Mathlib's
`RingTheory/Filtration.lean` already carries `Ideal.Filtration` + `Stable`,
the Artin–Rees lemma (`Ideal.exists_pow_inf_eq_pow_smul`), and Krull's
intersection theorem in local (`Ideal.iInf_pow_eq_bot_of_isLocalRing`) and
domain (`Ideal.iInf_pow_eq_bot_of_isDomain`) forms. Every declaration below
instantiates or re-shapes that API into the exact consumption forms; no new
commutative algebra is proved.

## Sections

* (§1) Stable filtrations: the adic filtration is stable (`adic_stable`,
  `adic_zero`), the tail formula (`stable_pow_smul_eq_of_ge`,
  `stable_iff_pow_smul_eq_of_ge`), stability inheritance — the Artin–Rees
  engine (`stable_of_le`, `stable_inf_of_stable`), and the FG bridge
  (`stable_iff_submodule_fg`).
* (§2) Artin–Rees: the submodule form (`artinRees_submodule`), its eventually
  form (`artinRees_eventuallyEq`), the `• ⊤ ↔ ↑(I^n)` bridges to ideal powers
  (`adic_smul_top_eq_coe`, `adic_inf_eq_coe_inf`, `adic_smul_coe_eq_coe_mul`),
  and the ideal form (`artinRees_ideal`).
* (§3) Cofinality: every stable filtration with `N 0 = ⊤` is mutually cofinal
  with the adic filtration (`stable_cofinal_adic`) — the comparison the `y`-sop
  step applies to the `y`-adic vs `𝔪`-adic filtrations.
* (§4) Krull intersection: ideal and submodule forms (`krull_pow_eq_bot`,
  `krull_pow_smul_eq_bot`), the embedded-kernel killers (`krull_mem_eq_zero`,
  `krull_le_eq_bot`, `krull_ideal_mem_eq_zero`), and the injectivity corollary
  dim-equality consumes (`injective_of_ker_le_adic`).
* (§5) The `R_P` specialization: Noetherian instance (`isNoetherianRing_atPrime`),
  properness of the maximal ideal (`maximalIdeal_atPrime_ne_top`), Krull at `R_P`
  (`krull_atPrime_pow_eq_bot`, `krull_atPrime_smul_eq_bot`), and the kernel
  killers (`krull_atPrime_ker_eq_bot`, `krull_atPrime_mem_eq_zero`).

Consumption map for part 3 (`y`-sop + dim-equality): run the dimension induction
on `F := fun n ↦ ((finLength κ (grPiece R 𝔪 n) : ℕ) : ℚ)` (parts 1–2 supply the
difference calculus and the length framework); at each step compare the
`y`-adic filtration against the `𝔪`-adic one via `stable_cofinal_adic`, kill
embedded kernels with `krull_le_eq_bot` / `injective_of_ker_le_adic`, and force
`ker polySurj = ⊥` from dim-equality via `polySurjResidue_quotKerEquiv`.

## References

Mathlib (`lean-toolchain` pins `v4.34.0`), all read-only:
* `RingTheory/Filtration.lean`: `Ideal.Filtration` (:52), `Stable` (:173),
  `stableFiltration` (:178), `stableFiltration_stable` (:184),
  `Stable.exists_pow_smul_eq_of_ge` (:201),
  `stable_iff_exists_pow_smul_eq_of_ge` (:209),
  `Stable.bounded_difference` (:227), `submodule_fg_iff_stable` (:336),
  `Stable.of_le` (:367), `Stable.inter_right` (:375),
  `Ideal.exists_pow_inf_eq_pow_smul` (:388, Artin–Rees),
  `Ideal.iInf_pow_smul_eq_bot_of_isLocalRing` (:425),
  `Ideal.iInf_pow_eq_bot_of_isLocalRing` (:431, Krull).
* `RingTheory/Ideal/Operations.lean`: `Ideal.smul_eq_mul` (:68),
  `Ideal.mul_top` (:511).
* `RingTheory/Ideal/Defs.lean`: `Ideal` is an `abbrev` (:40), so ideal
  equalities and their submodule coercions are definitionally interchangeable.
* `RingTheory/Localization/Submodule.lean`:
  `IsLocalization.isNoetherianRing` (:81).
* `RingTheory/Polynomial/Basic.lean`: `MvPolynomial.isNoetherianRing` (:935).
* `RingTheory/LocalRing/MaximalIdeal/Basic.lean`:
  `IsLocalRing.maximalIdeal.isMaximal` (:36).
* `RingTheory/Localization/AtPrime/Basic.lean`: `Localization.AtPrime`,
  `IsLocalRing (Localization.AtPrime P)`.
* `Algebra/Module/Submodule/Ker.lean`: `LinearMap.ker_eq_bot` (:199).
* `Order/Filter/AtTopBot/Basic.lean`: `Filter.eventually_atTop`.

Project (read-only; deliberately not imported — sibling-owned):
* `Regularity/Koszul/AssociatedGradedRing.lean` (step A4(i): `grPiece`, `associatedGraded`;
  owned by a sibling lane).
* `Regularity/Koszul/LengthFramework.lean` (M4c-i: `finLength`; the `ℕ`-valued lengths).
* `Regularity/Multiplicity/NewtonDifferences.lean` (M4c-ii part 1: `seqDiff`, `IsPolyGrowth`).
* `Regularity/Koszul/GradedSurjection.lean` (M4b: `polySurjResidue_quotKerEquiv`).

## Status

All declarations below are unconditional (thin verified wrappers over Mathlib's
`RingTheory/Filtration.lean` API).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace FiltrationStability

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-! ## §1. Stable filtrations -/

/-- The adic filtration `N ↦ I^• • N` is stable (from `n₀ = 0`).
-/
theorem adic_stable (I : Ideal R) (N : Submodule R M) :
    (I.stableFiltration N).Stable :=
  Ideal.stableFiltration_stable I N

/-- The adic filtration of `⊤` starts at `⊤`.
-/
theorem adic_zero (I : Ideal R) :
    (I.stableFiltration (⊤ : Submodule R M)).N 0 = ⊤ := by
  change I ^ 0 • (⊤ : Submodule R M) = ⊤
  simp

/-- Stability tail formula: past `n₀`, every term is a power of `I` times the
`n₀`-th term.
-/
theorem stable_pow_smul_eq_of_ge {I : Ideal R} {F : I.Filtration M}
    (h : F.Stable) : ∃ n₀, ∀ n ≥ n₀, F.N n = I ^ (n - n₀) • F.N n₀ :=
  h.exists_pow_smul_eq_of_ge

/-- Stability iff the tail formula (for proving stability of new filtrations).
-/
theorem stable_iff_pow_smul_eq_of_ge {I : Ideal R} {F : I.Filtration M} :
    F.Stable ↔ ∃ n₀, ∀ n ≥ n₀, F.N n = I ^ (n - n₀) • F.N n₀ :=
  Ideal.Filtration.stable_iff_exists_pow_smul_eq_of_ge

/-- Stability inheritance: in a finite module over a Noetherian ring, every
sub-filtration of a stable filtration is stable. This is the Artin–Rees
engine (via finite generation of the Rees submodule).
-/
theorem stable_of_le [IsNoetherianRing R] [Module.Finite R M] {I : Ideal R}
    {F F' : I.Filtration M} (hF : F.Stable) (hle : F' ≤ F) : F'.Stable :=
  hF.of_le hle

/-- Intersecting a stable filtration with any filtration stays stable — the
shape Artin–Rees applies (`stableFiltration ⊤ ⊓ trivialFiltration N`).
-/
theorem stable_inf_of_stable [IsNoetherianRing R] [Module.Finite R M]
    {I : Ideal R} {F F' : I.Filtration M} (hF : F.Stable) :
    (F ⊓ F').Stable :=
  Ideal.Filtration.Stable.inter_right _ hF

/-- Finite generation of the Rees submodule is equivalent to stability (when
every component is finitely generated).
-/
theorem stable_iff_submodule_fg {I : Ideal R} (F : I.Filtration M)
    (h : ∀ i, (F.N i).FG) : F.submodule.FG ↔ F.Stable :=
  Ideal.Filtration.submodule_fg_iff_stable F h

/-! ## §2. Artin–Rees -/

/-- Artin–Rees, submodule form: the trace of the adic filtration on `N`
stabilizes to `I^(n-k)` times the `k`-th trace.
-/
theorem artinRees_submodule [IsNoetherianRing R] [Module.Finite R M]
    (I : Ideal R) (N : Submodule R M) :
    ∃ k, ∀ n ≥ k, I ^ n • ⊤ ⊓ N = I ^ (n - k) • (I ^ k • ⊤ ⊓ N) :=
  Ideal.exists_pow_inf_eq_pow_smul I N

/-- Artin–Rees, eventually form: the shape the Newton interface (§1 of
`NewtonDifferences`) transports to Hilbert functions.
-/
theorem artinRees_eventuallyEq [IsNoetherianRing R] [Module.Finite R M]
    (I : Ideal R) (N : Submodule R M) :
    ∃ k, (fun n => I ^ n • ⊤ ⊓ N)
      =ᶠ[Filter.atTop] fun n => I ^ (n - k) • (I ^ k • ⊤ ⊓ N) := by
  obtain ⟨k, hk⟩ := artinRees_submodule I N
  exact ⟨k, Filter.eventually_atTop.mpr ⟨k, fun n hn => hk n hn⟩⟩

/-- Bridge: `I^n • ⊤` is the coercion of the ideal power (connects the
filtration language to the `grPiece` language of ideal powers).
-/
theorem adic_smul_top_eq_coe (I : Ideal R) (n : ℕ) :
    I ^ n • (⊤ : Submodule R R) = ↑(I ^ n) :=
  (I ^ n).mul_top

/-- Bridge: intersecting the adic term with a submodule-coercion is the
coercion of the ideal intersection.
-/
theorem adic_inf_eq_coe_inf (I J : Ideal R) (n : ℕ) :
    I ^ n • (⊤ : Submodule R R) ⊓ (J : Submodule R R) = ↑(I ^ n ⊓ J) := by
  rw [adic_smul_top_eq_coe]

/-- Bridge: smul by an ideal power on a coercion is the coercion of the ideal
product.
-/
theorem adic_smul_coe_eq_coe_mul (I J : Ideal R) (n : ℕ) :
    I ^ n • (J : Submodule R R) = ↑(I ^ n * J) :=
  Ideal.smul_eq_mul _ _

/-- Artin–Rees, ideal form: the trace `I^n ⊓ J` stabilizes to
`I^(n-k) * (I^k ⊓ J)`.
-/
theorem artinRees_ideal [IsNoetherianRing R] (I J : Ideal R) :
    ∃ k, ∀ n ≥ k, (I ^ n ⊓ J : Ideal R) = I ^ (n - k) * (I ^ k ⊓ J) := by
  have hfin : Module.Finite R R := inferInstance
  obtain ⟨k, hk⟩ := artinRees_submodule (M := R) I (J : Submodule R R)
  refine ⟨k, fun n hn => ?_⟩
  have h := hk n hn
  rw [adic_inf_eq_coe_inf, adic_inf_eq_coe_inf,
    adic_smul_coe_eq_coe_mul] at h
  exact h

/-! ## §3. Cofinality of stable filtrations -/

/-- Every stable filtration with `N 0 = ⊤` is mutually cofinal with the adic
filtration: both inclusions hold up to a uniform shift `n₀`. The `y`-sop step
applies this to the `y`-adic vs `𝔪`-adic filtrations.
-/
theorem stable_cofinal_adic (I : Ideal R) {F : I.Filtration M} (hF : F.Stable)
    (h0 : F.N 0 = ⊤) :
    ∃ n₀, ∀ n,
      I ^ (n + n₀) • ⊤ ≤ F.N n ∧ F.N (n + n₀) ≤ I ^ n • ⊤ := by
  have hadic : (I.stableFiltration (⊤ : Submodule R M)).Stable :=
    Ideal.stableFiltration_stable I ⊤
  have e : (I.stableFiltration (⊤ : Submodule R M)).N 0 = F.N 0 := by
    rw [h0]
    exact adic_zero I
  obtain ⟨n₀, hn₀⟩ := hadic.bounded_difference hF e
  exact ⟨n₀, fun n => hn₀ n⟩

/-! ## §4. Krull intersection -/

/-- Krull intersection, submodule form: over a Noetherian local ring, the
intersection of the adic filtration on a finite module is `⊥`.
-/
theorem krull_pow_smul_eq_bot [IsNoetherianRing R] [IsLocalRing R]
    [Module.Finite R M] (I : Ideal R) (hI : I ≠ ⊤) :
    (⨅ i, I ^ i • ⊤ : Submodule R M) = ⊥ :=
  Ideal.iInf_pow_smul_eq_bot_of_isLocalRing I hI

/-- Krull intersection, ideal form: `⨅ i, I^i = ⊥`.
-/
theorem krull_pow_eq_bot [IsNoetherianRing R] [IsLocalRing R] (I : Ideal R)
    (hI : I ≠ ⊤) : ⨅ i, I ^ i = ⊥ :=
  Ideal.iInf_pow_eq_bot_of_isLocalRing I hI

/-- Krull element killer: anything in every adic power is zero.
-/
theorem krull_mem_eq_zero [IsNoetherianRing R] [IsLocalRing R]
    [Module.Finite R M] (I : Ideal R) (hI : I ≠ ⊤) (x : M)
    (hx : x ∈ (⨅ i, I ^ i • ⊤ : Submodule R M)) : x = 0 := by
  rw [krull_pow_smul_eq_bot I hI] at hx
  simpa using hx

/-- Krull submodule killer: a submodule contained in every adic power is `⊥`.
This kills embedded kernels in the Hilbert–Samuel argument.
-/
theorem krull_le_eq_bot [IsNoetherianRing R] [IsLocalRing R]
    [Module.Finite R M] (I : Ideal R) (hI : I ≠ ⊤) (N : Submodule R M)
    (hN : N ≤ ⨅ i, I ^ i • ⊤) : N = ⊥ :=
  eq_bot_iff.mpr (hN.trans (le_of_eq (krull_pow_smul_eq_bot I hI)))

/-- Krull element killer, ideal form.
-/
theorem krull_ideal_mem_eq_zero [IsNoetherianRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I ≠ ⊤) (x : R) (hx : x ∈ ⨅ i, I ^ i) : x = 0 := by
  rw [krull_pow_eq_bot I hI] at hx
  simpa using hx

/-- Injectivity from adic containment of the kernel: the corollary dim-equality
consumes (a map whose kernel is killed by Krull is injective).
-/
theorem injective_of_ker_le_adic [IsNoetherianRing R] [IsLocalRing R]
    [Module.Finite R M] {M' : Type*} [AddCommGroup M'] [Module R M']
    (I : Ideal R) (hI : I ≠ ⊤) (f : M →ₗ[R] M')
    (h : LinearMap.ker f ≤ ⨅ i, I ^ i • ⊤) : Function.Injective f :=
  LinearMap.ker_eq_bot.mp (krull_le_eq_bot I hI _ h)

/-! ## §5. The `R_P` specialization -/

variable {K : Type*} [Field K] {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K))
  [P.IsPrime]

/-- `R_P` is Noetherian (localization of the Noetherian polynomial ring).
-/
instance isNoetherianRing_atPrime :
    IsNoetherianRing (Localization.AtPrime P) := by
  have hbase : IsNoetherianRing (MvPolynomial (Fin m) K) := inferInstance
  exact IsLocalization.isNoetherianRing P.primeCompl _ hbase

/-- The maximal ideal of `R_P` is proper.
-/
theorem maximalIdeal_atPrime_ne_top :
    IsLocalRing.maximalIdeal (Localization.AtPrime P) ≠ ⊤ :=
  (IsLocalRing.maximalIdeal.isMaximal _).ne_top

/-- Krull at `R_P`, ideal form: `⨅ i, 𝔪^i = ⊥`.
-/
theorem krull_atPrime_pow_eq_bot :
    ⨅ i, IsLocalRing.maximalIdeal (Localization.AtPrime P) ^ i = ⊥ :=
  Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal_atPrime_ne_top P)

/-- Krull at `R_P`, submodule form.
-/
theorem krull_atPrime_smul_eq_bot :
    (⨅ i, IsLocalRing.maximalIdeal (Localization.AtPrime P) ^ i • ⊤ :
      Submodule (Localization.AtPrime P) (Localization.AtPrime P)) = ⊥ :=
  Ideal.iInf_pow_smul_eq_bot_of_isLocalRing _ (maximalIdeal_atPrime_ne_top P)

/-- Krull kernel killer at `R_P`.
-/
theorem krull_atPrime_ker_eq_bot
    (N : Submodule (Localization.AtPrime P) (Localization.AtPrime P))
    (hN : N ≤ ⨅ i, IsLocalRing.maximalIdeal (Localization.AtPrime P) ^ i • ⊤) :
    N = ⊥ :=
  krull_le_eq_bot _ (maximalIdeal_atPrime_ne_top P) _ hN

/-- Krull element killer at `R_P`.
-/
theorem krull_atPrime_mem_eq_zero (x : Localization.AtPrime P)
    (hx : x ∈ (⨅ i, IsLocalRing.maximalIdeal (Localization.AtPrime P) ^ i • ⊤ :
      Submodule (Localization.AtPrime P) (Localization.AtPrime P))) :
    x = 0 :=
  krull_mem_eq_zero _ (maximalIdeal_atPrime_ne_top P) _ hx

#print axioms artinRees_ideal
#print axioms stable_cofinal_adic
#print axioms krull_le_eq_bot
#print axioms injective_of_ker_le_adic
#print axioms krull_atPrime_pow_eq_bot

end FiltrationStability
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
