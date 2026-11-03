/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.SystemOfParameters
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedSurjection
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.List.OfFn
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.UniqueFactorizationDomain.Defs

/-!
# Regular-sequence probe: the `gr`-of-regular-sequence alternate route (step 0)

Step-0 probe for the alternate route to `ker polySurjResidue = ⊥` (the M4c-ii
hypothesis `hker` consumed by `grlift_grEquivOfKerEqBot`), bypassing the
Hilbert–Serre chain: if the sop `g` is a regular sequence, then `gr(g)(R_P)`
is polynomial, by induction on the principal short exact sequence
`0 → gr(-1) → gr → gr(R/xR) → 0` at each regular generator.

## §0–§1 survey results (Mathlib `v4.34.0`, all lines verified by read/grep)

present (module + line):

* `IsSMulRegular` — `Mathlib/Algebra/Regular/SMul.lean`
  (`Function.Injective ((c • ·) : M → M)`).
* `IsSMulRegular.of_ne_zero` — `Mathlib/Algebra/Module/Torsion/Free.lean`
  (needs `[IsTorsionFree R M]` for `M = R`, plus `[IsCancelMulZero R]`).
* `RingTheory.Sequence.IsWeaklyRegular` / `IsRegular` —
  `Mathlib/RingTheory/Regular/RegularSequence.lean` /
  (`List`-based; `IsRegular` extends weak with `top_ne_smul`).
* `isRegular_cons_iff` , `isWeaklyRegular_singleton_iff` ,
  `IsRegular.cons` , `IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal`
  (needs `[Module.Finite R L] [Nontrivial L]`).
* `Ideal.ofList` (abbrev) and `ofList_singleton`.
* `IsRegularLocalRing` — `Mathlib/RingTheory/RegularLocalRing/Defs.lean`;
  `IsRegularRing`.
* `isDomain_of_local_atPrime` —
  `Mathlib/RingTheory/Localization/AtPrime/Basic.lean` (instance).
* `Module.Finite.self` — `Mathlib/RingTheory/Finiteness/Basic.lean`.
* `IsLocalRing extends Nontrivial` — `Mathlib/RingTheory/LocalRing/Defs.lean`.
* `IsLocalRing.mem_maximalIdeal` —
  `Mathlib/RingTheory/LocalRing/MaximalIdeal/Basic.lean`.
* `UniqueFactorizationMonoid.irreducible_iff_prime` (class field) —
  `Mathlib/RingTheory/UniqueFactorizationDomain/Defs.lean`.
* `List.mem_ofFn'` — `Mathlib/Data/List/OfFn.lean`;
  `List.length_ofFn` — Lean core `Init/Data/List/OfFn.lean`.

absent (with evidence):

* No associated graded ring: `associatedGraded` appears nowhere in Mathlib;
  `RingTheory/Filtration.lean` carries only `Ideal.Filtration` (plus the
  Rees-submodule "associated module" prose).
  The project builds `gr` itself (`AssociatedGradedRing`).
* No `gr` exact sequences: no `×x̄`-injectivity, no principal SES, no
  cokernel identification `gr(R/xR) ≅ gr/(x̄)`.
* No Koszul complex in commutative algebra: only the todo at
  `RingTheory/Regular/RegularSequence.lean` (per `KoszulFrag`).
* No Auslander–Buchsbaum / Cohen–Macaulay:
  `grep -rni "auslander\|buchsbaum"` over `RingTheory/` is empty.
* No grade/depth definition: `RingTheory/Regular/Depth.lean` is a 15-line
  deprecated stub.
* No bridge from `IsRegularLocalRing` (or minimal `𝔪`-generators) to
  `Sequence.IsRegular` anywhere in Mathlib.
* No `Fin`-family regular-sequence API (all `List`-based) — §1 bridges it.

## What this file proves

* (§0) Survey pins: compile-time presence checks for the cited API.
* (§1) The `Fin`-to-`List` bridge `ofList_ofFn_eq_span_range`, connecting the
  GrLift `Fin`-sop to the `List`-based `IsRegular` API. Unconditional.
* (§2) First-order regularity over `R_P`: nonzero ⟹ regular
  (`isSMulRegular_of_ne_zero_atPrime`) and the length-1 assembly
  (`isRegular_singleton_of_mem_maximalIdeal_ne_zero`,).
  unconditional.
* (§3) Minimal generators are prime in `R_P`: `𝔪 ∖ 𝔪²` ⟹ nonzero,
  ⟹ irreducible (general local ring), ⟹ prime (UFD, automatic per
  `SystemOfParameters`). Unconditional. This is the foothold for gap-r2.
* (§4) The master residual `GrRegSeqMaster` (regular sop ⟹ `ker = ⊥`),
  the wiring theorem `ker_eq_bot_of_master_of_sop` (conditional-exact on
  `[hreg, GrRegSeqMaster]`), and the scoped step residuals below.

## Open gaps (follow-up work)

* Gap-r1 `SopIsRegular`: the sop is a regular sequence. Step `x₁` is proved
  (§2–§3). Step `x₂` needs `x₁` prime (proved, §3) + `x₁ ∤ x₂` (needs
  Nakayama-minimality from the cotangent API — follow-up, small). Steps `≥ 3`
  need primeness/UFD descent along successive quotients — absent from Mathlib
  (see above); alternatively the uniform version (every minimal list regular).
* Gap-r2 `GrStepColonCapture`: `×x̄` injectivity ⟺ colon capture
  `(𝔪ⁿ⁺² : x) ∩ 𝔪ⁿ ⊆ 𝔪ⁿ⁺¹` for prime minimal `x`. The `n = 0` case is easy
  (`x ∉ 𝔪²`); general `n` needs `𝔪`-adic order induction using §3 primeness.
  Follow-up, medium.
* Gap-r3 `GrStepIntersection`: `xR ∩ 𝔪ⁿ ⊆ x·𝔪ⁿ⁻¹ + 𝔪ⁿ⁺¹` (cokernel is `gr`
  of the quotient). Artin–Rees-flavored; follow-up must also survey
  Artin–Rees availability (not covered by this probe). Medium-hard.
* Gap-r4 `GrPolyLift`: per-step SES data ⟹ `ker polySurj = ⊥` (graded
  induction + polynomial recognition). The recognition step may re-enter
  Hilbert-function comparison (partial circularity with the bypassed chain)
  unless done by direct graded-freeness induction. Medium-hard, needs scoping.

Verdict: partial by design (probe). The "bypass" is not cheap:
gap-r1 (steps ≥ 3) and gap-r4 are real theory, not formalities.

## References

Project (read-only): `Regularity/Koszul/SystemOfParameters.lean` (sop extraction, UFD +
regular-local instances for `R_P`), `Regularity/Koszul/GradedSurjection.lean`
(`polySurjResidue`, `polySurjResidue_quotKerEquiv`), `Regularity/Koszul/AssociatedGradedRing.lean`
(`grPiece`, `associatedGraded`), `Regularity/Koszul/GradedLift.lean` (§1 sop,
`grlift_grEquivOfKerEqBot` — the `hker` consumption point),
`RingTheory/Regular/RegularSequence.lean` (Mathlib's `List`-based `IsRegular` API,
used directly; no local wrappers). Mathlib addresses are listed in the survey above.

## Status

* §0 pins, §1 bridge, §2 first-order regularity, §3 minimal ⟹ prime:
  unconditional.
* §4 `ker_eq_bot_of_master_of_sop`: conditional-exact on
  `[hreg, GrRegSeqMaster]`.
* `SopIsRegular`, `GrStepColonCapture`, `GrStepIntersection`, `GrPolyLift`,
  `GrRegSeqMaster`: explicit residuals (gap-r1–R4 + master).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace RegularSequenceProbe

open RingTheory.Sequence
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjection

/-! ## §0. Survey pins (compile-time presence checks) -/

/-- Pin: `isRegular_cons_iff` (`RegularSequence.lean`). -/
example {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (r : R) (rs : List R) :
    IsRegular M (r :: rs) ↔
      IsSMulRegular M r ∧ IsRegular (QuotSMulTop r M) rs :=
  isRegular_cons_iff M r rs

/-- Pin: `IsRegular.cons` (`RegularSequence.lean`). -/
example {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {r : R} {rs : List R} (h1 : IsSMulRegular M r)
    (h2 : IsRegular (QuotSMulTop r M) rs) : IsRegular M (r :: rs) :=
  IsRegular.cons h1 h2

/-- Pin: `IsRegularLocalRing` (`RegularLocalRing/Defs.lean`). -/
example (R : Type*) [CommRing R] [IsRegularLocalRing R] : True :=
  trivial

/-! ## §1. The `Fin`-family to `List` bridge -/

/-- A `Fin`-family as a `List` spans the same ideal as the family.
Connects the GrLift `Fin`-sop shape to the `List`-based `IsRegular` API.
-/
theorem ofList_ofFn_eq_span_range {R : Type*} [CommRing R] {d : ℕ}
    (g : Fin d → R) :
    Ideal.ofList (List.ofFn g) = Ideal.span (Set.range g) := by
  change Ideal.span { r | r ∈ List.ofFn g } = _
  congr 1
  exact Set.ext fun x => List.mem_ofFn' g x

/-! ## §2. First-order regularity over `R_P` -/

variable {K : Type*} [Field K] {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K))
  [P.IsPrime]

/-- Pin: `R_P` is a domain (`isDomain_of_local_atPrime`,
`AtPrime/Basic.lean`). -/
example : IsDomain (Localization.AtPrime P) := inferInstance

/-- Pin: `R_P` is finite over itself (`Module.Finite.self`,
`Finiteness/Basic.lean`; needed by). -/
example : Module.Finite (Localization.AtPrime P)
    (Localization.AtPrime P) := inferInstance

/-- Pin: `R_P` is nontrivial (`IsLocalRing extends Nontrivial`,
`LocalRing/Defs.lean`; needed by). -/
example : Nontrivial (Localization.AtPrime P) := inferInstance

/-- Nonzero elements of `R_P` are regular.

`IsTorsionFree R R`  and `IsCancelMulZero` from `IsDomain` are
automatic). -/
theorem isSMulRegular_of_ne_zero_atPrime (x : Localization.AtPrime P)
    (hne : x ≠ 0) : IsSMulRegular (Localization.AtPrime P) x :=
  IsSMulRegular.of_ne_zero hne

/-- Length-1 assembly: `x ∈ 𝔪`, `x ≠ 0` gives a regular sequence.

`of_isWeaklyRegular_of_mem_maximalIdeal`). -/
theorem isRegular_singleton_of_mem_maximalIdeal_ne_zero
    (x : Localization.AtPrime P)
    (hx : x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hne : x ≠ 0) :
    IsRegular (Localization.AtPrime P) [x] :=
  IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal (Localization.AtPrime P)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact hx)
    ((isWeaklyRegular_singleton_iff _ x).mpr
      (IsSMulRegular.of_ne_zero hne))

/-! ## §3. Minimal generators are prime in `R_P` -/

/-- Outside any ideal power ⟹ nonzero.
-/
theorem ne_zero_of_not_mem_pow {R : Type*} [CommRing R] (I : Ideal R)
    (n : ℕ) (x : R) (h : x ∉ I ^ n) : x ≠ 0 := by
  intro heq
  subst heq
  exact h (I ^ n).zero_mem

/-- Minimal generators are irreducible (general local ring): in
`x = a * b` with `x ∉ 𝔪²`, one factor is a unit.

`MaximalIdeal/Basic.lean`). -/
theorem irreducible_of_mem_maximalIdeal_not_mem_sq {R : Type*}
    [CommRing R] [IsLocalRing R] (x : R)
    (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hsq : x ∉ (IsLocalRing.maximalIdeal R) ^ 2) : Irreducible x := by
  constructor
  · intro hu
    exact (mem_nonunits_iff.mp
      ((IsLocalRing.mem_maximalIdeal x).mp hx)) hu
  · intro a b hab
    by_contra hcon
    push Not at hcon
    obtain ⟨ha, hb⟩ := hcon
    have ham : a ∈ IsLocalRing.maximalIdeal R :=
      (IsLocalRing.mem_maximalIdeal a).mpr (mem_nonunits_iff.mpr ha)
    have hbm : b ∈ IsLocalRing.maximalIdeal R :=
      (IsLocalRing.mem_maximalIdeal b).mpr (mem_nonunits_iff.mpr hb)
    have hmem : a * b ∈ (IsLocalRing.maximalIdeal R) ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul ham hbm
    rw [← hab] at hmem
    exact hsq hmem

/-- Minimal generators of `𝔪_P` are prime (the gap-r2 foothold).

`SystemOfParameters`; `irreducible_iff_prime`,
`UniqueFactorizationDomain/Defs.lean`). -/
theorem prime_of_mem_maximalIdeal_not_mem_sq_atPrime
    (x : Localization.AtPrime P)
    (hx : x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hsq : x ∉ (IsLocalRing.maximalIdeal (Localization.AtPrime P)) ^ 2) :
    Prime x :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mp
    (irreducible_of_mem_maximalIdeal_not_mem_sq x hx hsq)

/-! ## §4. Sop bridge, master, and scoped residuals -/

/-- The GrLift `Fin`-sop in `List` form (the `IsRegular` input shape).
-/
theorem ofList_ofFn_sop {d : ℕ} (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    Ideal.ofList (List.ofFn g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
  rw [ofList_ofFn_eq_span_range, hgen]

/-- Residual gap-r1: some sop-length `List` spanning `𝔪_P` is a regular
sequence. Step `x₁` is proved (§2–§3); step `x₂` needs `x₁ ∤ x₂`
(Nakayama-minimality, follow-up small); steps `≥ 3` need primeness/UFD
descent (Mathlib-absent). The uniform version (every minimal list is
regular) is what the master consumes via `ofList_ofFn_sop`. -/
def SopIsRegular : Prop :=
  ∃ rs : List (Localization.AtPrime P),
    Ideal.ofList rs = IsLocalRing.maximalIdeal (Localization.AtPrime P) ∧
      IsRegular (Localization.AtPrime P) rs

/-- Residual gap-r2: colon capture for prime minimal generators — the
ideal-theoretic content of `×x̄` injectivity on `gr` (`y ∈ 𝔪ⁿ`,
`xy ∈ 𝔪ⁿ⁺²` ⟹ `y ∈ 𝔪ⁿ⁺¹`). The `n = 0` case is easy (`x ∉ 𝔪²`);
general `n` needs `𝔪`-adic order induction on §3 primeness. -/
def GrStepColonCapture (x : Localization.AtPrime P) : Prop :=
  Prime x → x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime P) →
    x ∉ (IsLocalRing.maximalIdeal (Localization.AtPrime P)) ^ 2 →
      ∀ n : ℕ, ∀ y : Localization.AtPrime P,
        y ∈ (IsLocalRing.maximalIdeal (Localization.AtPrime P)) ^ n →
          x * y ∈ (IsLocalRing.maximalIdeal (Localization.AtPrime P)) ^ (n + 2) →
            y ∈ (IsLocalRing.maximalIdeal (Localization.AtPrime P)) ^ (n + 1)

/-- Residual gap-r3: the Artin–Rees intersection property
(`xR ∩ 𝔪ⁿ ⊆ x·𝔪ⁿ⁻¹ + 𝔪ⁿ⁺¹`) — the ideal-theoretic content of the
cokernel identification `gr(R/xR) ≅ gr/(x̄)`. -/
def GrStepIntersection (x : Localization.AtPrime P) : Prop :=
  Prime x → x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime P) →
    x ∉ (IsLocalRing.maximalIdeal (Localization.AtPrime P)) ^ 2 →
      ∀ n : ℕ, ∀ y : Localization.AtPrime P,
        y ∈ Ideal.span {x} →
          y ∈ (IsLocalRing.maximalIdeal (Localization.AtPrime P)) ^ n →
            ∃ a : Localization.AtPrime P, ∃ b : Localization.AtPrime P,
              a ∈ (IsLocalRing.maximalIdeal (Localization.AtPrime P)) ^ (n - 1) ∧
                b ∈ (IsLocalRing.maximalIdeal (Localization.AtPrime P)) ^ (n + 1) ∧
                  y = x * a + b

/-- Residual, the master: a regular sop kills the M4c kernel — the
endpoint of the SES-induction alternate route. Proved from gap-r2–R4
by follow-up work; consumed below in exactly the `hker` shape
`grlift_grEquivOfKerEqBot` takes. -/
def GrRegSeqMaster : Prop :=
  ∀ (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)),
    IsRegular (Localization.AtPrime P) (List.ofFn g) →
      RingHom.ker (polySurjResidue P d g hgen) = ⊥

/-- Residual gap-r4: per-step SES data ⟹ `ker polySurj = ⊥` (the graded
induction + polynomial-recognition bridge). The recognition step may
re-enter Hilbert-function comparison (partial circularity with the
bypassed chain) unless done by direct graded-freeness induction. -/
def GrPolyLift : Prop :=
  ∀ (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)),
    IsRegular (Localization.AtPrime P) (List.ofFn g) →
      (∀ i : Fin d, GrStepColonCapture P (g i)) →
        (∀ i : Fin d, GrStepIntersection P (g i)) →
          RingHom.ker (polySurjResidue P d g hgen) = ⊥

/-- The alternate route, wired: master + regular sop discharges M4c-ii's
`hker` for the GrLift sop shape.

Conditional on exactly `[hreg, GrRegSeqMaster]`. -/
theorem ker_eq_bot_of_master_of_sop (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hreg : IsRegular (Localization.AtPrime P) (List.ofFn g))
    (hmaster : GrRegSeqMaster P) :
    RingHom.ker (polySurjResidue P d g hgen) = ⊥ :=
  hmaster d g hgen hreg

#print axioms ofList_ofFn_eq_span_range
#print axioms isSMulRegular_of_ne_zero_atPrime
#print axioms isRegular_singleton_of_mem_maximalIdeal_ne_zero
#print axioms irreducible_of_mem_maximalIdeal_not_mem_sq
#print axioms prime_of_mem_maximalIdeal_not_mem_sq_atPrime
#print axioms ofList_ofFn_sop
#print axioms ker_eq_bot_of_master_of_sop

end RegularSequenceProbe
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
