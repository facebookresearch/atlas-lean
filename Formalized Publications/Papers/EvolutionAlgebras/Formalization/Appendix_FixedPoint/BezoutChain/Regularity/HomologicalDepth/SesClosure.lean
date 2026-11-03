/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.NewtonDifferences
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.LengthFramework
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.YSopStep
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.SystemOfParametersExistence
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.HilbertSerre
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.SuperficialReduction
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.ChiDegreeMaster

/-!
# Sup-SES closure: the H2 §3 residuals discharged
Closer-lane discharge of the two H2 §3 residual SPECs
(`SuperficialReduction.lean`: `SupSesAssembly`:192, `SupDimZeroBase`:207)
plus the H3-pin-shaped nonvanishing tower feeding H6's `HchiReduceAtAss`
pin. Uses the banked §1+§2 theory (`supSes_diff_eventuallyEq`,
`supTotal_growth_lift`, `sup_lengthFin_supChi`, `supChi_bot`,
`finLength_ses_of_injective`); rebuilds nothing.

## Verdicts (see grades per declaration)

* (§1) `SupSesAssembly` as stated is **false** (`supSesAssembly_false_supChi`,
  formal refutation): the `y = 0` instance forces every `χ` eventually
  zero, but `χ_⊥ n = length(R/𝔪ⁿ⁺¹) ≠ 0` (`supChi_pos_of_ne_top`).
  The task design note's suggested route (SES from y-regularity + AR-stability)
  is mathematically insufficient even with regularity: over a DVR,
  `y = π²` is regular and AR-stable, yet the SES equation fails at every
  rank (`χ(n) = n+1`, `χ_q(n) = min(n+1,2)`, so
  `χ_q(n+1) + χ(n) = n+3 ≠ n+2 = χ(n+1)`). The failure is order:
  `y ∈ 𝔪²` leaves a nonzero kernel `(𝔪ⁿ⁺²:π²)/𝔪ⁿ⁺¹`. This is recorded
  as `SupSesAssemblyReg` = false-or-blocked (formal DVR refutation not
  attempted: needs DVR length computations).
* (§2) The true gate is the colon-stabilization condition
  `SupColonStabFor` (`((𝔪ⁿ⁺² ⊔ J') : y) = 𝔪ⁿ⁺¹ ⊔ J'` eventually — the
  order-one/superficiality content). From it, the mul-by-`y` SES on adic
  quotients is built in-file (well-definedness from `y ∈ 𝔪`,
  injectivity from the colon equation via `ker_liftQ_eq_bot`, cokernel
  identified by the third isomorphism theorem) and length additivity
  (`finLength_ses_of_injective`) yields `IsSupSes`
  (`supSes_of_colonStab`, `supSesAssemblyColon_supChi` — unconditional
  from explicit colon data).
* (§3) `SupDimZeroBase` is **closed unconditionally**
  (`supDimZeroBase_unconditional`): dim-0 + Noetherian gives Artinian
  (Hopkins–Levitzki), hence `𝔪ᵏ ≤ J'`, hence `χ` eventually constant,
  hence growth `0`.
* (§4) Masters: `sup_sopReduction_master_gated` (conditional-exact on
  `[SupColonStabFor]`), `sup_chi_degree_le_dim_gated` (conditional-exact
  on the per-step selection-colon tower `[hsel]` — the iteration
  with `hsop`/`har`/`hfin` proved, `hses` via §2, `hbase` via §3);
  nonvanishing lift (`sup_nonvanishing_lift`, unconditional), dim-zero
  seed (`sup_dimZero_seed`, unconditional), iterated tower
  (`sup_tower_nonvanishing`, conditional-exact on `[hsel]`), and the
  verbatim H3-pin conclusion `hChiReduceAtAss_of_towers`
  (conditional-exact on `[htower]`).

## Residual register

open (exact, scoped): the per-step selection-colon tower
(`hsel` in `sup_chi_degree_le_dim_gated` / `sup_tower_nonvanishing` /
`hChiReduceAtAss_of_towers`): each step needs `y ∈ 𝔪` avoiding minimal
primes (proved: `supSopSelect`) plus eventual colon stabilization.
Price: superficial/order-one element existence via prime avoidance on
the associated graded (~300–500 lines: associated-prime avoidance over
`associatedGraded` + homogeneous lifting) and colon-from-superficial
transfer (~100 lines). Closed this lane: [`SupDimZeroBase`],
[SES assembly from colon data], [§3 masters modulo the tower],
[H3-pin-shaped nonvanishing modulo the tower].

## References

Project (read-only): `SuperficialReduction.lean` (§1+§2 bank, §3 masters,
both SPEC shapes), `YSopStep.lean` (`finLength_ses_of_injective`
:317, `ysop_step`), `FiltrationStability.lean` (`artinRees_ideal`, via
`sup_arStable_of_artinRees`), `LengthFramework.lean` (`finLength`,
`coe_finLength`), `NewtonDifferences.lean` (`seqDiff`, `IsPolyGrowth`,
`evalFun`, shift lemmas), `HilbertSerre.lean`
(`hsIsPolyGrowth_comp_add_succ`:1606), `SystemOfParametersExistence.lean`
(`krullDimLE_quotient_sup_span_singleton`:199),
`ChiDegreeMaster.lean` (`HchiReduceAtAss`:153, `chiFunQ`).

Mathlib (`lean-toolchain` pins `v4.34.0`), all read-only:
`HopkinsLevitzki.lean` (`IsNoetherianRing.isArtinianRing_of_krullDimLE_zero`),
`LocalRing/Quotient.lean`
(`exists_maximalIdeal_pow_le_of_isArtinianRing_quotient`),
`Ideal/Quotient/Noetherian.lean` (quotient-Noetherian instance),
`Ideal/Colon.lean` (`Submodule.colon`, `mem_colon_singleton`),
`LinearAlgebra/Isomorphisms.lean`
(`quotientQuotientEquivQuotientSup`), `LinearAlgebra/Quotient/Basic.lean`
(`ker_liftQ_eq_bot`, `range_liftQ`), `Length.lean`
(`length_eq_zero_iff`, `length_pos`), `KrullDimension/Basic.lean`
(`krullDimLE_iff`, `ringKrullDim_eq_of_ringEquiv`),
`Ideal/Quotient/Operations.lean` (`RingEquiv.quotientBot`).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace SesClosure

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.NewtonDifferences
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.LengthFramework
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.YSopStep
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.SystemOfParametersExistence
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.HilbertSerre
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.SuperficialReduction
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.ChiDegreeMaster

/-! ## §1. The ungated SPEC is false -/

/-- Every ring's zero element is AR-stable: both sides of the
`artinRees_ideal` equation collapse to `⊥` since `span {0} = ⊥`.
This is the half of the `y = 0` counterexample that needs no
Noetherian hypothesis.
-/
theorem supArStable_zero {R : Type*} [CommRing R] (I : Ideal R) :
    IsARStableFor I 0 := by
  refine ⟨0, fun n _ => ?_⟩
  rw [Ideal.span_singleton_eq_bot.mpr rfl]
  simp

#print axioms supArStable_zero

/-- A self-SES equation forces eventual vanishing: `IsSupSes H H`
says `H (n+1) + H n = H (n+1)` eventually, hence `H n = 0`
eventually.
-/
theorem supSesSelf_vanishing (H : ℕ → ℕ) (hses : IsSupSes H H) :
    H =ᶠ[Filter.atTop] 0 := by
  obtain ⟨c, hc⟩ := hses
  refine Filter.eventually_atTop.mpr ⟨c, fun n hn => ?_⟩
  change H n = 0
  have h := hc n hn
  omega

#print axioms supSesSelf_vanishing

/-- The ungated assembly SPEC forces every `χ` eventually zero:
instantiate at `y = 0` (which lies in `𝔪`, is AR-stable by
`supArStable_zero`, and has `J' ⊔ span {0} = J'`), with length
finiteness from `sup_lengthFin_supChi`.
-/
theorem supSesAssembly_forces_vanishing {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (χ : Ideal R → ℕ → ℕ)
    (h : SupSesAssembly (R := R) χ) (J' : Ideal R) :
    χ J' =ᶠ[Filter.atTop] 0 := by
  have h0 := h J' 0 (Ideal.zero_mem _) (supArStable_zero _)
    (sup_lengthFin_supChi J')
    (sup_lengthFin_supChi (J' ⊔ Ideal.span {0}))
  rw [Ideal.span_singleton_eq_bot.mpr rfl, sup_bot_eq] at h0
  exact supSesSelf_vanishing (χ J') h0

#print axioms supSesAssembly_forces_vanishing

/-- The bottom ideal is proper in any local ring (via `1 ≠ 0`).
-/
theorem supBot_ne_top {R : Type*} [CommRing R] [IsLocalRing R] :
    (⊥ : Ideal R) ≠ ⊤ := by
  intro hcon
  have h1 : (1 : R) ∈ (⊥ : Ideal R) := by
    rw [hcon]
    exact Submodule.mem_top
  exact one_ne_zero (Ideal.mem_bot.mp h1)

#print axioms supBot_ne_top

/-- Positivity of the relative Hilbert–Samuel function: over a proper
ideal `J'`, every value `χ_J' n` is nonzero, since the quotient by
`𝔪ⁿ⁺¹ ⊔ J' ≤ 𝔪 ≠ ⊤` is nontrivial and nontrivial modules have
positive length.
-/
theorem supChi_pos_of_ne_top {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (J' : Ideal R) (hJ : J' ≠ ⊤) (n : ℕ) :
    supChi (R := R) J' n ≠ 0 := by
  have hpow : IsLocalRing.maximalIdeal R ^ (n + 1)
      ≤ IsLocalRing.maximalIdeal R := by
    rw [pow_succ]
    exact Ideal.mul_le_right
  have hle : IsLocalRing.maximalIdeal R ^ (n + 1) ⊔ J'
      ≤ IsLocalRing.maximalIdeal R :=
    sup_le hpow (IsLocalRing.le_maximalIdeal hJ)
  have hne : IsLocalRing.maximalIdeal R ^ (n + 1) ⊔ J' ≠ ⊤ := by
    intro hcon
    have hmax := IsLocalRing.maximalIdeal.isMaximal R
    exact hmax.ne_top (top_le_iff.mp (hcon ▸ hle))
  have hNontriv : Nontrivial
      (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 1) ⊔ J')) :=
    Ideal.Quotient.nontrivial_iff.mpr hne
  have hpos : Module.length R
      (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 1) ⊔ J')) ≠ 0 := by
    rw [ne_eq, Module.length_eq_zero_iff]
    exact not_subsingleton_iff_nontrivial.mpr hNontriv
  have hfin := sup_lengthFin_supChi (R := R) J' n
  unfold supChi
  intro hzero
  have hcoe := coe_finLength hfin
  rw [hzero, Nat.cast_zero] at hcoe
  exact hpos hcoe.symm

#print axioms supChi_pos_of_ne_top

/-- Falsity of the ungated SPEC: `SupSesAssembly supChi` would force
`χ_⊥` eventually zero (`supSesAssembly_forces_vanishing`), but every
value is positive (`supChi_pos_of_ne_top`). The H2 §3 residual as
posed at Superficial:192 is unclosable; §2 gates it by the colon
condition.

Status: false (formal refutation). -/
theorem supSesAssembly_false_supChi {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] :
    ¬ SupSesAssembly (R := R) (supChi (R := R)) := by
  intro hcon
  have hvan :=
    supSesAssembly_forces_vanishing (supChi (R := R)) hcon ⊥
  have hpos : ∀ n : ℕ, supChi (R := R) (⊥ : Ideal R) n ≠ 0 :=
    supChi_pos_of_ne_top ⊥ supBot_ne_top
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hvan
  have h0 : supChi (R := R) (⊥ : Ideal R) N = 0 := hN N le_rfl
  exact hpos N h0

#print axioms supSesAssembly_false_supChi

/-- SPEC (false-or-blocked): the regularity-gated assembly form — the
design note's suggested route (SES from y-regularity + AR-stability +
finiteness). False: over a DVR, `y = π²` is regular and AR-stable
(Artin–Rees is unconditional in Noetherian rings), yet with
`χ(n) = n+1` and `χ_q(n) = min(n+1,2)` the equation
`χ_q(n+1) + χ(n) = χ(n+1)` reads `n+3 = n+2` and fails at every
rank. The failure is order (`y ∈ 𝔪²`): the mul-by-`y` kernel
`(𝔪ⁿ⁺² : π²)/𝔪ⁿ⁺¹ = 𝔪ⁿ/𝔪ⁿ⁺¹` never vanishes. Formal DVR
refutation not attempted (needs DVR length computations, scoped
~250–400 lines); the true gate is `SupColonStabFor` (§2).

Status: false-or-blocked (witness documented, formal refutation
scoped, not attempted). -/
def SupSesAssemblyReg {R : Type*} [CommRing R] [IsLocalRing R]
    (χ : Ideal R → ℕ → ℕ) : Prop :=
  ∀ (J' : Ideal R) (y : R), y ∈ IsLocalRing.maximalIdeal R →
    IsSMulRegular (R ⧸ J') y →
    IsARStableFor (IsLocalRing.maximalIdeal R) y →
    (∀ n : ℕ, IsFiniteLength R
      (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 1) ⊔ J'))) →
    (∀ n : ℕ, IsFiniteLength R
      (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 1)
        ⊔ (J' ⊔ Ideal.span {y})))) →
    IsSupSes (χ J') (χ (J' ⊔ Ideal.span {y}))

#print axioms SupSesAssemblyReg

/-! ## §2. The true gate: colon stabilization + SES assembly -/

/-- The colon-stabilization condition for `y` over `J'`: eventually
`((𝔪ⁿ⁺² ⊔ J') : y) = 𝔪ⁿ⁺¹ ⊔ J'`. This is the order-one /
superficiality content the SES argument actually consumes: it says
exactly that mul-by-`y` is injective on the adic quotients past some
rank. Strictly stronger than regularity (the DVR `π²` witness of §1
is regular but violates this at every rank).

Specification address (the exact missing input; scoped in the module
register). -/
def SupColonStabFor {R : Type*} [CommRing R] [IsLocalRing R]
    (J' : Ideal R) (y : R) : Prop :=
  ∃ c : ℕ, ∀ n : ℕ, c ≤ n →
    ((IsLocalRing.maximalIdeal R ^ (n + 2) ⊔ J' : Ideal R) :
      Submodule R R).colon {y}
      = IsLocalRing.maximalIdeal R ^ (n + 1) ⊔ J'

#print axioms SupColonStabFor

/-- The SES equation from colon data: the mul-by-`y` short exact
sequence on adic quotients. Well-definedness uses `y ∈ 𝔪`
(`𝔪ⁿ⁺¹·y ⊆ 𝔪ⁿ⁺²`, `J'·y ⊆ J'`); injectivity is the colon equation
via `Submodule.ker_liftQ_eq_bot`; the cokernel is identified with
`R ⧸ (𝔪ⁿ⁺² ⊔ (J' ⊔ span {y}))` by the third isomorphism theorem;
lengths add by `finLength_ses_of_injective`. The second finiteness
hypothesis is kept for SPEC-shape compatibility (length additivity
needs only the middle term).
-/
theorem supSes_of_colonStab {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (J' : Ideal R) (y : R)
    (hym : y ∈ IsLocalRing.maximalIdeal R)
    (hcol : SupColonStabFor (R := R) J' y)
    (hfinA : ∀ n : ℕ, IsFiniteLength R
      (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 1) ⊔ J')))
    (_hfinB : ∀ n : ℕ, IsFiniteLength R
      (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 1)
        ⊔ (J' ⊔ Ideal.span {y})))) :
    IsSupSes (supChi (R := R) J')
      (supChi (R := R) (J' ⊔ Ideal.span {y})) := by
  obtain ⟨c, hc⟩ := hcol
  refine ⟨c, fun n hn => ?_⟩
  have e2 : n + 1 + 1 = n + 2 := by omega
  have hpow2 : IsLocalRing.maximalIdeal R ^ (n + 1)
        * IsLocalRing.maximalIdeal R
      = IsLocalRing.maximalIdeal R ^ (n + 2) := by
    rw [mul_comm, ← pow_succ']
  unfold supChi
  rw [e2]
  set A : Ideal R := IsLocalRing.maximalIdeal R ^ (n + 1) ⊔ J'
    with hAdef
  set B : Ideal R := IsLocalRing.maximalIdeal R ^ (n + 2) ⊔ J'
    with hBdef
  have hcolon := hc n hn
  have hmul : A * Ideal.span {y} ≤ B := by
    rw [hAdef, Ideal.sup_mul]
    apply sup_le
    · calc IsLocalRing.maximalIdeal R ^ (n + 1) * Ideal.span {y}
            ≤ IsLocalRing.maximalIdeal R ^ (n + 1)
              * IsLocalRing.maximalIdeal R :=
            mul_le_mul_of_nonneg_left
              (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hym))
              bot_le
        _ = IsLocalRing.maximalIdeal R ^ (n + 2) := hpow2
        _ ≤ B := by
            change IsLocalRing.maximalIdeal R ^ (n + 2)
              ≤ IsLocalRing.maximalIdeal R ^ (n + 2) ⊔ J'
            exact le_sup_left
    · calc J' * Ideal.span {y} ≤ J' := Ideal.mul_le_left
        _ ≤ B := by
            change J' ≤ IsLocalRing.maximalIdeal R ^ (n + 2) ⊔ J'
            exact le_sup_right
  have hmem : ∀ x : R, x ∈ A → x * y ∈ B := by
    intro x hx
    exact hmul (Ideal.mul_mem_mul hx
      (Ideal.mem_span_singleton_self y))
  have hkerle : ((A : Ideal R) : Submodule R R) ≤ LinearMap.ker
      ((Submodule.mkQ (B : Submodule R R)).comp
        (LinearMap.mulRight R y)) := by
    intro x hx
    rw [LinearMap.mem_ker]
    change Submodule.mkQ (B : Submodule R R) (x * y) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hmem x hx)
  have hkerle2 : LinearMap.ker
      ((Submodule.mkQ (B : Submodule R R)).comp
        (LinearMap.mulRight R y))
      ≤ ((A : Ideal R) : Submodule R R) := by
    intro x hx
    rw [LinearMap.mem_ker] at hx
    have hxmem : x * y ∈ (B : Submodule R R) :=
      Ideal.Quotient.eq_zero_iff_mem.mp hx
    have hxcol : x ∈ ((B : Submodule R R).colon {y}) := by
      rw [Submodule.mem_colon_singleton]
      rwa [smul_eq_mul]
    rw [hcolon] at hxcol
    change x ∈ ((A : Ideal R) : Submodule R R)
    exact hxcol
  set f : R ⧸ (A : Submodule R R) →ₗ[R] R ⧸ (B : Submodule R R) :=
    Submodule.liftQ (A : Submodule R R) _ hkerle with hfdef
  have hkerf : LinearMap.ker f = ⊥ :=
    Submodule.ker_liftQ_eq_bot _ _ _ hkerle2
  have hfinj : Function.Injective f := LinearMap.ker_eq_bot.mp hkerf
  have hrange2 : LinearMap.range
      ((Submodule.mkQ (B : Submodule R R)).comp
        (LinearMap.mulRight R y))
      = Submodule.map (Submodule.mkQ (B : Submodule R R))
        ((Ideal.span {y} : Ideal R) : Submodule R R) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a * y, Ideal.mem_span_singleton'.mpr ⟨a, rfl⟩, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hb
      refine ⟨t, ?_⟩
      change Submodule.mkQ (B : Submodule R R) (t * y) = _
      rw [ht]
  have hrange : LinearMap.range f
      = Submodule.map (Submodule.mkQ (B : Submodule R R))
        ((Ideal.span {y} : Ideal R) : Submodule R R) := by
    rw [hfdef, Submodule.range_liftQ]
    exact hrange2
  have eC0 := Submodule.quotientQuotientEquivQuotientSup
    (B : Submodule R R)
    ((Ideal.span {y} : Ideal R) : Submodule R R)
  rw [← hrange] at eC0
  have hsup : ((B : Submodule R R)
        ⊔ ((Ideal.span {y} : Ideal R) : Submodule R R))
      = ((IsLocalRing.maximalIdeal R ^ (n + 2)
        ⊔ (J' ⊔ Ideal.span {y}) : Ideal R) : Submodule R R) := by
    have h1 : B ⊔ Ideal.span {y} = IsLocalRing.maximalIdeal R ^ (n + 2)
        ⊔ (J' ⊔ Ideal.span {y}) := by
      rw [hBdef]
      exact sup_assoc _ _ _
    calc ((B : Submodule R R)
          ⊔ ((Ideal.span {y} : Ideal R) : Submodule R R))
        = ((B ⊔ Ideal.span {y} : Ideal R) : Submodule R R) := rfl
      _ = ((IsLocalRing.maximalIdeal R ^ (n + 2)
          ⊔ (J' ⊔ Ideal.span {y}) : Ideal R) : Submodule R R) := by
          rw [h1]
  rw [hsup] at eC0
  have hBfin : IsFiniteLength R (R ⧸ (B : Submodule R R)) := by
    have h := hfinA (n + 1)
    rwa [e2] at h
  have hadd := finLength_ses_of_injective f hfinj eC0 hBfin
  omega

#print axioms supSes_of_colonStab

/-- SPEC (the true gated form): SES assembly from colon-stabilization
data. Unlike `SupSesAssembly` (§1: false) and `SupSesAssemblyReg`
(§1: false-or-blocked), this form closes unconditionally at
`χ := supChi` (`supSesAssemblyColon_supChi`).

Specification address (closed at `supChi` below). -/
def SupSesAssemblyColon {R : Type*} [CommRing R] [IsLocalRing R]
    (χ : Ideal R → ℕ → ℕ) : Prop :=
  ∀ (J' : Ideal R) (y : R), y ∈ IsLocalRing.maximalIdeal R →
    SupColonStabFor (R := R) J' y →
    (∀ n : ℕ, IsFiniteLength R
      (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 1) ⊔ J'))) →
    (∀ n : ℕ, IsFiniteLength R
      (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 1)
        ⊔ (J' ⊔ Ideal.span {y})))) →
    IsSupSes (χ J') (χ (J' ⊔ Ideal.span {y}))

#print axioms SupSesAssemblyColon

/-- The gated assembly closes at `χ := supChi`: every hypothesis is
either supplied by the caller (colon data) or proved
(`sup_lengthFin_supChi`).
-/
theorem supSesAssemblyColon_supChi {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] :
    SupSesAssemblyColon (R := R) (supChi (R := R)) := by
  intro J' y hym hcol hfinA hfinB
  exact supSes_of_colonStab J' y hym hcol hfinA hfinB

#print axioms supSesAssemblyColon_supChi

/-! ## §3. The dimension-zero base, closed unconditionally -/

/-- Adic stabilization in dimension zero: over a zero-dimensional
quotient, some power of `𝔪` lies in `J'`. Noetherian + dim 0 gives
Artinian (Hopkins–Levitzki), and the maximal ideal of a Noetherian
local ring is nilpotent mod any ideal with Artinian quotient.
-/
theorem supAdicStab_of_dimZero {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (J' : Ideal R)
    (hJ : Ring.KrullDimLE 0 (R ⧸ J')) :
    ∃ k : ℕ, IsLocalRing.maximalIdeal R ^ k ≤ J' := by
  have hNoeth : IsNoetherianRing (R ⧸ J') :=
    Ideal.Quotient.isNoetherianRing J'
  have hDim : Ring.KrullDimLE 0 (R ⧸ J') := hJ
  have hArt : IsArtinianRing (R ⧸ J') :=
    @IsNoetherianRing.isArtinianRing_of_krullDimLE_zero (R ⧸ J')
      inferInstance hNoeth hDim
  exact @IsLocalRing.exists_maximalIdeal_pow_le_of_isArtinianRing_quotient
    R inferInstance inferInstance J' hArt

#print axioms supAdicStab_of_dimZero

/-- Adic stabilization makes `χ` eventually constant: once
`𝔪ⁿ⁺¹ ≤ J'`, the quotient `R ⧸ (𝔪ⁿ⁺¹ ⊔ J')` is constantly `R ⧸ J'`.
-/
theorem supChi_eventuallyConst_of_adicStab {R : Type*} [CommRing R]
    [IsLocalRing R] (J' : Ideal R)
    (hstab : ∃ k : ℕ, IsLocalRing.maximalIdeal R ^ k ≤ J') :
    (fun n : ℕ => ((supChi (R := R) J' n : ℕ) : ℚ))
      =ᶠ[Filter.atTop] fun _ : ℕ =>
        ((finLength R (R ⧸ J') : ℕ) : ℚ) := by
  obtain ⟨k, hk⟩ := hstab
  refine Filter.eventually_atTop.mpr ⟨k, fun n hn => ?_⟩
  have hle : IsLocalRing.maximalIdeal R ^ (n + 1) ≤ J' := by
    obtain ⟨d, hd⟩ : ∃ d : ℕ, n + 1 = k + d := ⟨n + 1 - k, by omega⟩
    calc IsLocalRing.maximalIdeal R ^ (n + 1)
        = IsLocalRing.maximalIdeal R ^ k
          * IsLocalRing.maximalIdeal R ^ d := by
          rw [hd, pow_add]
      _ ≤ J' * IsLocalRing.maximalIdeal R ^ d :=
          mul_le_mul_of_nonneg_right hk bot_le
      _ ≤ J' := Ideal.mul_le_left
  have heq : IsLocalRing.maximalIdeal R ^ (n + 1) ⊔ J' = J' :=
    sup_eq_right.mpr hle
  change ((supChi (R := R) J' n : ℕ) : ℚ)
    = ((finLength R (R ⧸ J') : ℕ) : ℚ)
  unfold supChi
  rw [heq]

#print axioms supChi_eventuallyConst_of_adicStab

/-- An eventually constant `ℚ`-sequence has polynomial growth `0`
(witnessed by the constant polynomial).
-/
theorem isPolyGrowth_zero_of_eventuallyConst (F : ℕ → ℚ) (c : ℚ)
    (h : F =ᶠ[Filter.atTop] fun _ : ℕ => c) :
    IsPolyGrowth F 0 := by
  refine ⟨Polynomial.C c, ?_, ?_⟩
  · rw [Polynomial.natDegree_C]
  · have heval : evalFun (Polynomial.C c) = fun _ : ℕ => c := by
      funext n
      change Polynomial.eval (n : ℚ) (Polynomial.C c) = c
      exact Polynomial.eval_C
    rwa [heval]

#print axioms isPolyGrowth_zero_of_eventuallyConst

/-- The dimension-zero base, closed: over a zero-dimensional
quotient, `χ = supChi J'` has growth degree `0`. This discharges the
`hbase` input of the H2 §3 iteration master (`sup_chi_degree_le_dim`
:497) unconditionally.
-/
theorem supDimZeroBase_unconditional {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] :
    SupDimZeroBase (R := R) (supChi (R := R)) := by
  intro J' hJ
  have hstab := supAdicStab_of_dimZero J' hJ
  have hconst := supChi_eventuallyConst_of_adicStab J' hstab
  exact isPolyGrowth_zero_of_eventuallyConst _ _ hconst

#print axioms supDimZeroBase_unconditional

/-! ## §4. Gated masters + H3-pin-shaped nonvanishing -/

/-- The one-step joint master with the SES input discharged through
§2: from selection + colon data, both the Krull dimension drops and
the quotient growth drops to `d - 1`.

Conditional on exactly `[SupColonStabFor]`. -/
theorem sup_sopReduction_master_gated {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (J : Ideal R) (y : R)
    (e d : ℕ)
    (hsop : SupSelectData (R := R) J y)
    (hcol : SupColonStabFor (R := R) J y)
    (hJ : Ring.KrullDimLE (e + 1) (R ⧸ J))
    (hF : IsPolyGrowth
      (fun n => ((supChi (R := R) J n : ℕ) : ℚ)) d)
    (hd : 1 ≤ d) :
    Ring.KrullDimLE e (R ⧸ (J ⊔ Ideal.span {y})) ∧
      IsPolyGrowth
        (fun n => ((supChi (R := R) (J ⊔ Ideal.span {y}) (n + 1) :
          ℕ) : ℚ)) (d - 1) := by
  have hses : IsSupSes (supChi (R := R) J)
      (supChi (R := R) (J ⊔ Ideal.span {y})) :=
    supSes_of_colonStab J y hsop.1 hcol (sup_lengthFin_supChi J)
      (sup_lengthFin_supChi (J ⊔ Ideal.span {y}))
  exact sup_sopReduction_master J y e d _ _ hsop hJ hses hF hd

#print axioms sup_sopReduction_master_gated

/-- The χ-degree iteration master with four of five inputs proved:
`hsop`/`har`/`hfin` discharge as in, `hses` via the §2
assembly, `hbase` via the §3 unconditional close. Only the per-step
selection-with-colon tower remains.

Conditional on exactly `[hsel]` (the selection-colon tower). -/
theorem sup_chi_degree_le_dim_gated {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (e : ℕ) (J : Ideal R)
    (hJ : Ring.KrullDimLE e (R ⧸ J))
    (hsel : ∀ J' : Ideal R, ∃ y : R,
      SupSelectData (R := R) J' y ∧
        SupColonStabFor (R := R) J' y) :
    IsPolyGrowth (fun n => ((supChi (R := R) J n : ℕ) : ℚ)) e := by
  revert J hJ
  induction e with
  | zero =>
    intro J hJ
    exact supDimZeroBase_unconditional J hJ
  | succ e ih =>
    intro J hJ
    obtain ⟨y, hsel_y, hcol⟩ := hsel J
    have hdrop : Ring.KrullDimLE e (R ⧸ (J ⊔ Ideal.span {y})) :=
      krullDimLE_quotient_sup_span_singleton J y hsel_y.2 e hJ
    have hsesJy : IsSupSes (supChi (R := R) J)
        (supChi (R := R) (J ⊔ Ideal.span {y})) :=
      supSes_of_colonStab J y hsel_y.1 hcol (sup_lengthFin_supChi J)
        (sup_lengthFin_supChi (J ⊔ Ideal.span {y}))
    have hIH : IsPolyGrowth
        (fun n => ((supChi (R := R) (J ⊔ Ideal.span {y}) n :
          ℕ) : ℚ)) e :=
      ih (J ⊔ Ideal.span {y}) hdrop
    have hshift : IsPolyGrowth
        (fun n => ((supChi (R := R) (J ⊔ Ideal.span {y}) (n + 1) :
          ℕ) : ℚ)) e :=
      hsIsPolyGrowth_comp_add_succ hIH
    exact supTotal_growth_lift (supChi (R := R) J)
      (supChi (R := R) (J ⊔ Ideal.span {y})) e hsesJy hshift

#print axioms sup_chi_degree_le_dim_gated

/-- Shift converse for eventual vanishing: if the shifted sequence
is eventually zero, so is the original (tails absorb the shift).
-/
theorem sup_nonvanishing_shift_converse {G : ℕ → ℚ}
    (h : (fun n : ℕ => G (n + 1)) =ᶠ[Filter.atTop] 0) :
    G =ᶠ[Filter.atTop] 0 := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h
  refine Filter.eventually_atTop.mpr ⟨N + 1, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
  have h2 := hN m (by omega)
  simpa using h2

#print axioms sup_nonvanishing_shift_converse

/-- Nonvanishing transfers across the unit shift: differences commute
with shifts (`seqDiff_comp_add`), and vanishing pulls back along the
shift (`sup_nonvanishing_shift_converse`).
-/
theorem sup_nonvanishing_shift (Hq : ℕ → ℚ) (e : ℕ)
    (hne : ¬ seqDiff e Hq =ᶠ[Filter.atTop] 0) :
    ¬ seqDiff e (fun n : ℕ => Hq (n + 1)) =ᶠ[Filter.atTop] 0 := by
  rw [seqDiff_comp_add Hq 1 e]
  intro hcon
  exact hne (sup_nonvanishing_shift_converse hcon)

#print axioms sup_nonvanishing_shift

/-- Nonvanishing lifts across the SES step: quotient nonvanishing at
degree `e` gives total nonvanishing at `e + 1`. The quotient
sequence is eventually `ΔH` (`supSes_diff_eventuallyEq`), so
`Δ^e` of it is eventually `Δ^(e+1) H`.
-/
theorem sup_nonvanishing_lift (H Hq : ℕ → ℕ) (e : ℕ)
    (hses : IsSupSes H Hq)
    (hq : ¬ seqDiff e (fun n : ℕ => ((Hq (n + 1) : ℕ) : ℚ))
      =ᶠ[Filter.atTop] 0) :
    ¬ seqDiff (e + 1) (fun n : ℕ => ((H n : ℕ) : ℚ))
      =ᶠ[Filter.atTop] 0 := by
  intro hcon
  apply hq
  have hΔ := supSes_diff_eventuallyEq H Hq hses
  have hcong := seqDiff_eventuallyEq_of_eventuallyEq hΔ e
  rw [supSplit_seqDiff] at hcong
  exact hcong.trans hcon

#print axioms sup_nonvanishing_lift

/-- The dim-zero nonvanishing seed: over a quotient by a proper
ideal, `χ` is pointwise nonzero (`supChi_pos_of_ne_top`), hence not
eventually zero. Fires at the `e = 0` base of the tower (no
dimension hypothesis needed — positivity holds at any dimension).
-/
theorem sup_dimZero_seed {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (J' : Ideal R) (hne : J' ≠ ⊤) :
    ¬ (fun n : ℕ => ((supChi (R := R) J' n : ℕ) : ℚ))
      =ᶠ[Filter.atTop] 0 := by
  intro hcon
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hcon
  have h0 : supChi (R := R) J' N = 0 := Nat.cast_eq_zero.mp (hN N le_rfl)
  exact supChi_pos_of_ne_top J' hne N h0

#print axioms sup_dimZero_seed

/-- The iterated nonvanishing tower: from `KrullDimLE e`, the `e`-th
difference of `χ` does not vanish. HilbertFunctionCount on `e`: the seed
(`sup_dimZero_seed`) at `0`, the lift (`sup_nonvanishing_lift` +
`sup_nonvanishing_shift`) at each step, with the SES equation from
§2 and dimension drop from SopExist §3. Properness propagates since
each step stays inside `𝔪`.

Conditional on exactly `[hsel]` (the selection-colon tower). -/
theorem sup_tower_nonvanishing {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (e : ℕ) (J : Ideal R)
    (hJ : Ring.KrullDimLE e (R ⧸ J)) (hne : J ≠ ⊤)
    (hsel : ∀ J' : Ideal R, J' ≠ ⊤ → ∃ y : R,
      SupSelectData (R := R) J' y ∧
        SupColonStabFor (R := R) J' y) :
    ¬ seqDiff e (fun n : ℕ => ((supChi (R := R) J n : ℕ) : ℚ))
      =ᶠ[Filter.atTop] 0 := by
  revert J hJ hne
  induction e with
  | zero =>
    intro J _ hne
    rw [seqDiff_zero]
    exact sup_dimZero_seed J hne
  | succ e ih =>
    intro J hJ hne
    obtain ⟨y, hsel_y, hcol⟩ := hsel J hne
    have hdrop : Ring.KrullDimLE e (R ⧸ (J ⊔ Ideal.span {y})) :=
      krullDimLE_quotient_sup_span_singleton J y hsel_y.2 e hJ
    have hne' : J ⊔ Ideal.span {y} ≠ ⊤ := by
      have hJm : J ≤ IsLocalRing.maximalIdeal R :=
        IsLocalRing.le_maximalIdeal hne
      have hym : Ideal.span {y} ≤ IsLocalRing.maximalIdeal R :=
        Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hsel_y.1)
      have hle : J ⊔ Ideal.span {y} ≤ IsLocalRing.maximalIdeal R :=
        sup_le hJm hym
      intro hcon
      exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top
        (top_le_iff.mp (hcon ▸ hle))
    have hIH := ih (J ⊔ Ideal.span {y}) hdrop hne'
    have hshift : ¬ seqDiff e
        (fun n : ℕ => ((supChi (R := R) (J ⊔ Ideal.span {y}) (n + 1) :
          ℕ) : ℚ)) =ᶠ[Filter.atTop] 0 :=
      sup_nonvanishing_shift _ e hIH
    have hsesJy : IsSupSes (supChi (R := R) J)
        (supChi (R := R) (J ⊔ Ideal.span {y})) :=
      supSes_of_colonStab J y hsel_y.1 hcol (sup_lengthFin_supChi J)
        (sup_lengthFin_supChi (J ⊔ Ideal.span {y}))
    exact sup_nonvanishing_lift (supChi (R := R) J)
      (supChi (R := R) (J ⊔ Ideal.span {y})) e hsesJy hshift

#print axioms sup_tower_nonvanishing

/-- The `ringKrullDim` pin transports to `KrullDimLE` over `⧸ ⊥`:
`S ⧸ ⊥ ≃+* S` (`RingEquiv.quotientBot`) preserves Krull dimension.
-/
theorem krullDimLE_quotBot_of_pin {S : Type*} [CommRing S] (dimN : ℕ)
    (hpin : ringKrullDim S = ((dimN : ℕ∞) : WithBot ℕ∞)) :
    Ring.KrullDimLE dimN (S ⧸ (⊥ : Ideal S)) := by
  rw [Ring.krullDimLE_iff]
  have heq : ringKrullDim (S ⧸ (⊥ : Ideal S)) = ringKrullDim S :=
    RingEquiv.ringKrullDim (RingEquiv.quotientBot S)
  rw [heq, hpin]
  exact le_rfl

#print axioms krullDimLE_quotBot_of_pin

/-- The H3-pin conclusion, verbatim `HchiReduceAtAss` (ChiDegree
:153): at every `Q ∈ Ass(R ⧸ J)`, the `dimN`-th difference of `χ`
does not vanish, with `dimN` pinned to `ringKrullDim(R_Q)`. The
bridge `chiFunQ = cast ∘ supChi ⊥` is `supChi_bot`; the dimension
pin becomes `KrullDimLE` over `⧸ ⊥` via
`krullDimLE_quotBot_of_pin`; nonvanishing is the §4 tower. This is
the input H6 fires into `hdimEqMinAtAss_of_chi_specs`.

Conditional on exactly `[htower]` (per-`Q` dimension pin +
selection-colon tower over `R_Q`). -/
theorem hChiReduceAtAss_of_towers (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (htower : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) →
      ∃ dimN : ℕ,
        ringKrullDim (Localization.AtPrime Q)
          = ((dimN : ℕ∞) : WithBot ℕ∞) ∧
        (∀ J' : Ideal (Localization.AtPrime Q), J' ≠ ⊤ →
          ∃ y : Localization.AtPrime Q,
            SupSelectData (R := Localization.AtPrime Q) J' y ∧
              SupColonStabFor (R := Localization.AtPrime Q) J' y)) :
    HchiReduceAtAss m K J := by
  intro Q _ hQ
  obtain ⟨dimN, hpin, hsel⟩ := htower Q hQ
  refine ⟨dimN, hpin, ?_⟩
  have hlink : chiFunQ m K Q = fun n : ℕ =>
      ((supChi (R := Localization.AtPrime Q) ⊥ n : ℕ) : ℚ) := by
    funext n
    change ((HilbertSamuelDegree.hsSamuel (R := Localization.AtPrime Q) n :
      ℕ) : ℚ) = _
    rw [← supChi_bot]
  rw [hlink]
  have hdim : Ring.KrullDimLE dimN
      (Localization.AtPrime Q ⧸ (⊥ : Ideal (Localization.AtPrime Q))) :=
    krullDimLE_quotBot_of_pin dimN hpin
  have hbot : (⊥ : Ideal (Localization.AtPrime Q)) ≠ ⊤ :=
    supBot_ne_top
  exact sup_tower_nonvanishing dimN ⊥ hdim hbot hsel

#print axioms hChiReduceAtAss_of_towers

/-! ## §5. Residual register (doc-only)

closed this lane:
1. `SupDimZeroBase supChi` — unconditional
   (`supDimZeroBase_unconditional`).
2. SES assembly from colon data — unconditional
   (`supSesAssemblyColon_supChi`).
3. H2 §3 masters modulo the tower (`sup_sopReduction_master_gated` on
   `[SupColonStabFor]`; `sup_chi_degree_le_dim_gated` on `[hsel]`).
4. H3-pin-shaped nonvanishing modulo the tower
   (`sup_tower_nonvanishing` on `[hsel]`;
   `hChiReduceAtAss_of_towers` on `[htower]`, concluding verbatim
   `HchiReduceAtAss`).
5. Refutations: `SupSesAssembly` false (`supSesAssembly_false_supChi`,
   formal); `SupSesAssemblyReg` false-or-blocked (DVR `π²` witness
   documented, formal refutation scoped ~250–400, not attempted).

open (exact): the per-step selection-colon tower `hsel` (each step:
`y ∈ 𝔪` avoiding minimal primes — proved via `supSopSelect` — plus
eventual colon stabilization `SupColonStabFor`). Price: superficial /
order-one element existence via prime avoidance on the associated
graded (~300–500 lines) + colon-from-superficial transfer (~100
lines). The `hne` side conditions (`J ≠ ⊤`) are proof obligations
discharged in-file (properness propagates inside `𝔪`), never residual
hypotheses.
-/

end SesClosure
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
