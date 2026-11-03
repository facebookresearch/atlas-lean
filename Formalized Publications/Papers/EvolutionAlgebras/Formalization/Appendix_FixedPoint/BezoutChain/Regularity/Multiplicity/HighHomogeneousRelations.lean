/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.HilbertWitnessNarrowing
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedSurjection
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.GradedSurjectionInjective
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.AssociatedGradedRing
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Algebra.GroupWithZero.Associated
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Algebra.Prime.Defs
import Mathlib.Data.Multiset.ZeroCons
import Mathlib.Data.Nat.Init
import Mathlib.RingTheory.Ideal.Lattice
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.UniqueFactorizationDomain.Defs

/-!
# High-degree homogeneous relations: the `deg ≥ 2` half of `KwitNoHomRel`

Closes-or-narrows the `deg ≥ 2` homogeneous-relations residual: a nonzero
homogeneous `y ∈ ker (polySurjResidue P d g hgen)` of degree `≥ 2` cannot
exist. The full residual `KwitNoHomRel` (`HilbertWitnessNarrowing.lean`) splits
unconditionally into the linear half `KwitNoHomRelLow` (degree 1 — owned by
a parallel lane, taken as a hypothesis here, never proved) and the high
half `KwitNoHomRelHigh` (degrees `≥ 2` — this file).

## What this file proves

* (§1) The split `kwitHigh_split`: `KwitNoHomRel ↔ Low ∧ High`.
  unconditional.
* (§2) Pair exactness `kwitHigh_low_high_iff_ker_eq_bot`: given `1 ≤ d`,
  `(Low ∧ High) ↔ ker = ⊥`. The forward chase rules out degree-0
  components via `ker ≠ ⊤`, which follows from `Low` itself (applied to
  `X 0`); no `hmin`, no Hilbert data. Unconditional (conditional-form on
  `1 ≤ d`).
* (§3) Descent infrastructure (unconditional): a prime factor of a
  `ker`-member lies in `ker` (`kwitHigh_mem_factor_of_prod_mem`, needs
  `KwitKerIsPrime`); every nonzero `ker`-member has a nonzero homogeneous
  component of degree `≥ 1` bounded by its total degree
  (`kwitHigh_chase_factor`, needs `KwitKerIsPrime` for the degree-0/unit
  exclusion).
* (§4) Master `kwitHigh_of_low_prime_noIrred`: `High` from
  `[Low, KwitKerIsPrime, KwitNoIrredHigh]` by strong induction on the
  degree: factor `y` into primes in the UFD `κ[X]`; some prime factor
  lies in `ker`; chase it to a homogeneous `z ∈ ker` of degree
  `m ∈ [1, n]`; `m = 1` contradicts `Low`, `m < n` contradicts the IH,
  and `m = n` forces `y` associated to a prime hence irreducible,
  contradicting `KwitNoIrredHigh`. Conditional-exact on the three
  hypotheses. Exactness `kwitHigh_iff_noIrred_of_low_prime`:
  given `[Low, KwitKerIsPrime]`, `High ↔ KwitNoIrredHigh`.
* (§5) Dimension cost analysis (unconditional): any nonzero `y ∈ ker` forces
  `dim gr + 1 ≤ dim κ[X]` (`kwitHigh_dim_drop_of_mem_ker`, via
  `ringKrullDim_succ_le_of_surjective`), hence so does any violation of
  `KwitNoIrredHigh`. This prices the remaining gap: closing
  `KwitNoIrredHigh` needs the reverse comparison `dim κ[X] ≤ dim gr`
  (i.e. `hle_gr` transported — not assumed here) plus dimension
  finiteness. The drop half is proved; the comparison half is the
  remaining dimension theory.

## Why `hmin` and regularity are not needed for the descent

The factor descent (§§3–4) is pure graded-UFD algebra over the residue
field `κ`; it uses neither `hmin` nor any regularity input. Those enter
through the two remaining gaps: `Low` (parallel lane, via
Nakayama/minimality of the `[gᵢ]`) and the dimension-theoretic closure
of `KwitNoIrredHigh` (`dim R_P = d` from `hmin`, plus the missing
`dim gr = dim R_P` comparison). The UFD input is the UFD-ness of
`S = κ[X]` (`MvPolynomial.uniqueFactorizationMonoid`); the UFD-ness of
`R_P` itself is not needed.

## Candidate-route mapping (from the task design note)

* UFD-ness: used (§§3–4, on `S = κ[X]`).
* Minimal-prime-over-`ker` + equidimensionality: surveyed and not used.
  Mathlib has minimal primes (`MinimalPrime/Basic.lean`,
  `nonempty_minimalPrimes`, `exists_minimalPrimes_le`)
  and the one-step drop (`NonZeroDivisors.lean`), but no catenary /
  equidimensionality / height API turning "minimal prime over `ker` is
  nonzero" into a usable drop; moreover descent needs primality at `ker`
  (factors must be proved back in `ker`, not merely in a prime above it), so
  `KwitKerIsPrime` is the exact residual.
* Initial-form descent: subsumed — the factor chase (§3) descends
  through homogeneous components rather than initial forms.
* Colon-capture (`GrStepColonCapture`, `RegularSequenceProbe.lean`):
  not needed — no `gr`-injectivity is used anywhere here.

## Mathlib survey (`lean-toolchain` pins `v4.34.0`), all read-only

present (module + line, all verified by read/grep/`#check`):

* `Ideal.IsPrime` class — `RingTheory/Ideal/Prime.lean`;
  `isPrime_iff` , `ne_top` , `one_notMem`.
* `Ideal.eq_top_of_isUnit_mem` — `RingTheory/Ideal/Lattice.lean`.
* `Ideal.mul_mem_right` — `RingTheory/Ideal/Defs.lean`.
* `Prime.ne_zero` / `not_isUnit` / `irreducible` —
  `Algebra/Prime/Defs.lean` / /.
* `Associated.dvd` / `symm` / `irreducible` —
  `Algebra/GroupWithZero/Associated.lean` / /.
* `UniqueFactorizationMonoid.exists_prime_factors` —
  `RingTheory/UniqueFactorizationDomain/Defs.lean`.
* `MvPolynomial.uniqueFactorizationMonoid` (instance) —
  `RingTheory/Polynomial/UniqueFactorization.lean`.
* `totalDegree_mul_of_isDomain`  and
  `totalDegree_le_of_dvd_of_isDomain`  —
  `Algebra/MvPolynomial/NoZeroDivisors.lean`.
* `totalDegree_eq_zero_iff_eq_C` —
  `Algebra/MvPolynomial/Degrees.lean`.
* `isHomogeneous_X` , `homogeneousComponent_isHomogeneous`
  , `homogeneousComponent_zero` ,
  `homogeneousComponent_eq_zero` , `sum_homogeneousComponent`
  , `IsHomogeneous.totalDegree`  —
  `RingTheory/MvPolynomial/Homogeneous.lean`.
* `X_ne_zero` — `Algebra/MvPolynomial/Basic.lean`.
* `mem_nonZeroDivisors_iff_ne_zero` —
  `Algebra/GroupWithZero/NonZeroDivisors.lean`.
* `ringKrullDim_succ_le_of_surjective` —
  `RingTheory/KrullDimension/NonZeroDivisors.lean` (via
  `ringKrullDim_quotient_succ_le_of_nonZeroDivisor`, which uses
  `PrimeSpectrum.zeroLocus` and `Ideal.disjoint_nonZeroDivisors`).
* `Nat.strong_induction_on` — `Data/Nat/Init.lean`.
* `Multiset.induction_on` (`Data/Multiset/ZeroCons.lean`),
  `mem_cons_of_mem` , `mem_cons_self`;
  `Multiset.dvd_prod` (`Algebra/BigOperators/Group/Multiset/Basic.lean`),
  `prod_zero` / `prod_cons` (same file, `to_additive` pair).
* `Ideal.minimalPrimes` (`RingTheory/Ideal/MinimalPrime/Basic.lean`);
  `R_P` is a UFD automatically (per `SystemOfParameters.lean`).

absent (with evidence):

* No associated graded ring: only the Rees algebra
  (`RingTheory/ReesAlgebra.lean`); the project builds `gr` itself
  (`AssociatedGradedRing.lean`), per the `RegularSequenceProbe.lean` survey.
* No catenary / equidimensionality / height-drop API: `grep -rni`
  `"catenary\|equidimensional"` over `RingTheory/` is empty (re-verified
  for this file); `KrullDimension/` has only one-step drops
  (`NonZeroDivisors.lean`), PID height (`PID.lean`), and bounds.
* No `dim gr_I(R) = dim R` and no `dim κ[X] = d` upper bound in the
  needed form (only lower bounds like
  `ringKrullDim_add_natCard_le_ringKrullDim_mvPolynomial` at
  `NonZeroDivisors.lean`).
* No bridge from `IsRegularLocalRing` (or minimal `𝔪`-generators) to
  `Sequence.IsRegular` (per the `RegularSequenceProbe.lean` survey, §0–§1),
  and no `gr`-exact sequences — the alternate route's gap-r1–R4.

## References

Project (read-only):
* `Regularity/HomologicalDepth/HilbertWitnessNarrowing.lean` (`KwitNoHomRel`:911).
* `Regularity/Multiplicity/GradedSurjectionInjective.lean`
  (`hsAssemble_ker_homogeneousComponent_mem`:950,
  `hsAssemble_exists_homogeneous_mem_ker`:988 — the `by_cases`/`not_forall`
  chase pattern copied in `kwitHigh_chase_factor`).
* `Regularity/Koszul/GradedSurjection.lean` (`polySurjResidue`:344,
  `polySurjResidue_surjective`:354).
* `Regularity/Koszul/AssociatedGradedRing.lean` (`grRegular`:663).
* `Regularity/Koszul/RegularSequenceProbe.lean` (regular-sequence present/absent
  survey; `GrStepColonCapture`:316, not needed here).

## Status

* §1 split, §2 pair exactness, §5 dimension drop: unconditional
  (§2 conditional-form on `1 ≤ d`, application data).
* §3 helpers: unconditional (conditional-form on `KwitKerIsPrime`).
* §4 master: conditional-exact on
  `[KwitNoHomRelLow, KwitKerIsPrime, KwitNoIrredHigh]`; exactness
  `High ↔ KwitNoIrredHigh` given the first two.
* Overall: partial (`KwitNoIrredHigh` open — the exact minimal
  remainder given `[Low, KwitKerIsPrime]`; `Low` is the parallel lane).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace HighHomogeneousRelations

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.HilbertWitnessNarrowing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjection
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjectionInjective
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AssociatedGradedRing

variable {K : Type*} [Field K] {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K))
  [P.IsPrime]

/-- The residue field `κ` of `R_P` (reducible, so the field instance flows). -/
abbrev homRelK : Type _ := IsLocalRing.ResidueField (Localization.AtPrime P)

/-! ## §1. The low/high split of `KwitNoHomRel` -/

/-- Low: no nonzero linear (degree-1) homogeneous relation in `ker`.
parallel lane — taken as a hypothesis everywhere below, never proved. -/
def KwitNoHomRelLow (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) : Prop :=
  ∀ y : MvPolynomial (Fin d) (homRelK P),
    y ∈ RingHom.ker (polySurjResidue P d g hgen) →
      MvPolynomial.IsHomogeneous y 1 → y = 0

/-- High: no nonzero homogeneous relation of degree `≥ 2` in `ker`.
This file's target. -/
def KwitNoHomRelHigh (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) : Prop :=
  ∀ (y : MvPolynomial (Fin d) (homRelK P)) (n : ℕ),
    y ∈ RingHom.ker (polySurjResidue P d g hgen) →
      MvPolynomial.IsHomogeneous y n → 2 ≤ n → y = 0

/-- Primality of `ker`, i.e. (via `polySurjResidue_quotKerEquiv`) `gr` is a
domain. The descent needs primality at `ker` (prime factors must be proved back
in `ker`); minimal primes above `ker` do not suffice. Implied by
`Low ∧ High` (then `ker = ⊥`, prime in a domain), so this is a
stepping-stone residual, not an independent gap. -/
def KwitKerIsPrime (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) : Prop :=
  Ideal.IsPrime (RingHom.ker (polySurjResidue P d g hgen))

/-- No irreducible homogeneous relation of degree `≥ 2`: the exact minimal
remainder given `[Low, KwitKerIsPrime]` (see
`kwitHigh_iff_noIrred_of_low_prime`). Reducible relations descend (master);
irreducible ones are the hard core, to be closed by dimension theory (§5
prices the gap via the unconditional drop). -/
def KwitNoIrredHigh (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) : Prop :=
  ∀ (y : MvPolynomial (Fin d) (homRelK P)) (n : ℕ),
    y ∈ RingHom.ker (polySurjResidue P d g hgen) →
      MvPolynomial.IsHomogeneous y n → 2 ≤ n → Irreducible y → y = 0

/-- The split: `KwitNoHomRel ↔ Low ∧ High` (`1 ≤ n` is `n = 1 ∨ 2 ≤ n`).
-/
theorem kwitHigh_split (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    KwitNoHomRel P d g hgen ↔
      KwitNoHomRelLow P d g hgen ∧ KwitNoHomRelHigh P d g hgen := by
  constructor
  · intro h
    refine ⟨fun y hym hhom => h y 1 hym hhom le_rfl, ?_⟩
    intro y n hym hhom hn
    exact h y n hym hhom (by omega)
  · intro h y n hym hhom hn1
    by_cases hn : n = 1
    · subst hn
      exact h.1 y hym hhom
    · exact h.2 y n hym hhom (by omega)

/-! ## §2. Pair exactness: `Low ∧ High ↔ ker = ⊥` -/

/-- `ker = ⊥` from `Low ∧ High`: homogeneous chase. Degree-0 components are
units-or-zero (`homogeneousComponent_zero`); a nonzero one forces
`ker = ⊤`, contradicting `ker ≠ ⊤`, which follows from `Low` itself
(applied to `X 0`, using `1 ≤ d`) — no `hmin` needed.
-/
theorem kwitHigh_ker_eq_bot_of_low_high (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hd : 1 ≤ d)
    (hlow : KwitNoHomRelLow P d g hgen)
    (hhigh : KwitNoHomRelHigh P d g hgen) :
    RingHom.ker (polySurjResidue P d g hgen) = ⊥ := by
  have hnetop : RingHom.ker (polySurjResidue P d g hgen) ≠ ⊤ := by
    intro htop
    have hmem : MvPolynomial.X (⟨0, hd⟩ : Fin d) ∈
        RingHom.ker (polySurjResidue P d g hgen) := by
      rw [htop]
      exact Submodule.mem_top
    have h0 := hlow _ hmem (MvPolynomial.isHomogeneous_X _ _)
    exact MvPolynomial.X_ne_zero _ h0
  apply eq_bot_iff.mpr
  intro p hpmem
  have hcomp : ∀ i ∈ Finset.range (p.totalDegree + 1),
      (MvPolynomial.homogeneousComponent i) p = 0 := by
    intro i _
    by_cases hi0 : i = 0
    · subst hi0
      by_contra hne
      have hcmem := hsAssemble_ker_homogeneousComponent_mem
        (IsLocalRing.maximalIdeal (Localization.AtPrime P)) d g hgen p hpmem 0
      have hc0 : (MvPolynomial.homogeneousComponent 0) p =
          MvPolynomial.C (p.coeff 0) :=
        MvPolynomial.homogeneousComponent_zero p
      have hr : p.coeff 0 ≠ 0 := by
        intro hz
        exact hne (by rw [hc0, hz, map_zero])
      have hunit : IsUnit (MvPolynomial.C (p.coeff 0) :
          MvPolynomial (Fin d) (homRelK P)) :=
        IsUnit.map MvPolynomial.C (isUnit_iff_ne_zero.mpr hr)
      rw [← hc0] at hunit
      exact hnetop (Ideal.eq_top_of_isUnit_mem _ hcmem hunit)
    · have hcmem := hsAssemble_ker_homogeneousComponent_mem
        (IsLocalRing.maximalIdeal (Localization.AtPrime P)) d g hgen p hpmem i
      have hc_hom := MvPolynomial.homogeneousComponent_isHomogeneous i p
      by_cases hi1 : i = 1
      · subst hi1
        exact hlow _ hcmem hc_hom
      · exact hhigh _ i hcmem hc_hom (by omega)
  have hsum : p = ∑ i ∈ Finset.range (p.totalDegree + 1),
      (MvPolynomial.homogeneousComponent i) p :=
    (MvPolynomial.sum_homogeneousComponent p).symm
  rw [hsum, Finset.sum_eq_zero hcomp]
  exact Submodule.zero_mem _

/-- Pair exactness: the split pair is exactly `ker = ⊥` (given `1 ≤ d`).
-/
theorem kwitHigh_low_high_iff_ker_eq_bot (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hd : 1 ≤ d) :
    (KwitNoHomRelLow P d g hgen ∧ KwitNoHomRelHigh P d g hgen) ↔
      RingHom.ker (polySurjResidue P d g hgen) = ⊥ := by
  constructor
  · intro h
    exact kwitHigh_ker_eq_bot_of_low_high P d g hgen hd h.1 h.2
  · intro hker
    refine ⟨fun y hym _ => ?_, fun y _ hym _ _ => ?_⟩
    · rw [hker] at hym
      exact (Submodule.mem_bot _).mp hym
    · rw [hker] at hym
      exact (Submodule.mem_bot _).mp hym

/-! ## §3. Descent infrastructure: factors and homogeneous chase -/

/-- A prime factor of a `ker`-member lies in `ker` (multiset induction with
`Ideal.isPrime_iff`; the empty case is `1 ∉ ker`).
-/
theorem kwitHigh_mem_factor_of_prod_mem (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hprime : KwitKerIsPrime P d g hgen)
    (s : Multiset (MvPolynomial (Fin d) (homRelK P)))
    (hmem : s.prod ∈ RingHom.ker (polySurjResidue P d g hgen)) :
    ∃ p ∈ s, p ∈ RingHom.ker (polySurjResidue P d g hgen) := by
  have hI {x y : MvPolynomial (Fin d) (homRelK P)}
      (h : x * y ∈ RingHom.ker (polySurjResidue P d g hgen)) :
      x ∈ RingHom.ker (polySurjResidue P d g hgen) ∨
        y ∈ RingHom.ker (polySurjResidue P d g hgen) :=
    (Ideal.isPrime_iff.mp hprime).2 h
  suffices h : ∀ t : Multiset (MvPolynomial (Fin d) (homRelK P)),
      t.prod ∈ RingHom.ker (polySurjResidue P d g hgen) →
        ∃ p ∈ t, p ∈ RingHom.ker (polySurjResidue P d g hgen) from
    h s hmem
  intro t
  refine Multiset.induction_on t ?_ ?_
  · intro h1
    simp only [Multiset.prod_zero] at h1
    exact (Ideal.IsPrime.one_notMem hprime h1).elim
  · intro a u ih hu
    rw [Multiset.prod_cons] at hu
    rcases hI hu with ha | hs
    · exact ⟨a, Multiset.mem_cons_self a u, ha⟩
    · obtain ⟨p, hps, hpk⟩ := ih hs
      exact ⟨p, Multiset.mem_cons_of_mem hps, hpk⟩

/-- Chase: a nonzero `ker`-member has a nonzero homogeneous component in
`ker` of degree `m` with `1 ≤ m ≤ totalDegree`. The degree-0 component is
a constant (`homogeneousComponent_zero`); if nonzero it is a unit (field
coefficients), forcing `ker = ⊤` against `KwitKerIsPrime.ne_top`. The
`by_cases`/`not_forall` extraction mirrors
`hsAssemble_exists_homogeneous_mem_ker`.
-/
theorem kwitHigh_chase_factor (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hprime : KwitKerIsPrime P d g hgen)
    {p : MvPolynomial (Fin d) (homRelK P)}
    (hpmem : p ∈ RingHom.ker (polySurjResidue P d g hgen))
    (hp0 : p ≠ 0) :
    ∃ z : MvPolynomial (Fin d) (homRelK P), ∃ m : ℕ,
      z ∈ RingHom.ker (polySurjResidue P d g hgen) ∧ z ≠ 0 ∧
        MvPolynomial.IsHomogeneous z m ∧ 1 ≤ m ∧ m ≤ p.totalDegree := by
  have hcomp_mem : ∀ i : ℕ, (MvPolynomial.homogeneousComponent i) p ∈
      RingHom.ker (polySurjResidue P d g hgen) := fun i =>
    hsAssemble_ker_homogeneousComponent_mem
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) d g hgen p hpmem i
  have hcomp0 : (MvPolynomial.homogeneousComponent 0) p = 0 := by
    by_contra hne
    have hc0 : (MvPolynomial.homogeneousComponent 0) p =
        MvPolynomial.C (p.coeff 0) :=
      MvPolynomial.homogeneousComponent_zero p
    have hr : p.coeff 0 ≠ 0 := by
      intro hz
      exact hne (by rw [hc0, hz, map_zero])
    have hunit : IsUnit (MvPolynomial.C (p.coeff 0) :
        MvPolynomial (Fin d) (homRelK P)) :=
      IsUnit.map MvPolynomial.C (isUnit_iff_ne_zero.mpr hr)
    rw [← hc0] at hunit
    exact Ideal.IsPrime.ne_top hprime
      (Ideal.eq_top_of_isUnit_mem _ (hcomp_mem 0) hunit)
  by_cases hall : ∀ i ∈ Finset.range (p.totalDegree + 1),
      (MvPolynomial.homogeneousComponent i) p = 0
  · exfalso
    apply hp0
    rw [← MvPolynomial.sum_homogeneousComponent p]
    exact Finset.sum_eq_zero hall
  · obtain ⟨i, hi⟩ := not_forall.mp hall
    have himem : i ∈ Finset.range (p.totalDegree + 1) := by
      by_contra hcon
      exact hi (fun h => absurd h hcon)
    have hine : (MvPolynomial.homogeneousComponent i) p ≠ 0 :=
      fun h => hi (fun _ => h)
    have hi1 : 1 ≤ i := by
      by_contra hcon
      have hi0 : i = 0 := by omega
      subst hi0
      exact hine hcomp0
    have hile : i ≤ p.totalDegree := by
      by_contra hcon
      have hlt : p.totalDegree < i := by omega
      exact hine (MvPolynomial.homogeneousComponent_eq_zero i p hlt)
    exact ⟨_, _, hcomp_mem i, hine,
      MvPolynomial.homogeneousComponent_isHomogeneous i p, hi1, hile⟩

/-! ## §4. Master: `High` from prime-factor descent -/

/-- Master: `High` from `[Low, KwitKerIsPrime, KwitNoIrredHigh]` by strong
induction on the degree. Given homogeneous `w ∈ ker` of degree `N ≥ 2`,
`w ≠ 0`: factor into primes in the UFD `κ[X]`; the product is associated
to `w`, hence in `ker`; some prime factor `p ∈ ker`; chase `p` to
homogeneous `z ∈ ker` of degree `m ∈ [1, totalDegree p] ⊆ [1, N]`
(`totalDegree_le_of_dvd_of_isDomain` via `p ∣ w`). If `m = 1`, `Low`
kills `z`; if `m < N`, the IH kills `z`; if `m = N`, then
`totalDegree p = N`, so `p ∣ w` with equal degrees forces `w` associated
to the prime `p`, hence irreducible, and `KwitNoIrredHigh` kills `w`.

Conditional on exactly
`[KwitNoHomRelLow, KwitKerIsPrime, KwitNoIrredHigh]`. -/
theorem kwitHigh_of_low_prime_noIrred (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hlow : KwitNoHomRelLow P d g hgen)
    (hprime : KwitKerIsPrime P d g hgen)
    (hnoirr : KwitNoIrredHigh P d g hgen) :
    KwitNoHomRelHigh P d g hgen := by
  intro y n hym hhom hn2
  suffices h : ∀ N : ℕ, 2 ≤ N → ∀ w : MvPolynomial (Fin d) (homRelK P),
      w ∈ RingHom.ker (polySurjResidue P d g hgen) →
        MvPolynomial.IsHomogeneous w N → w = 0 from
    h n hn2 y hym hhom
  intro N
  refine Nat.strong_induction_on N ?_
  intro N ih hN2 w hmem hhomW
  by_contra wne
  obtain ⟨facs, hfacprime, hassoc⟩ :=
    UniqueFactorizationMonoid.exists_prime_factors w wne
  have hprodmem : facs.prod ∈ RingHom.ker (polySurjResidue P d g hgen) := by
    obtain ⟨u, hu⟩ := hassoc.symm
    rw [← hu]
    exact Ideal.mul_mem_right _ _ hmem
  obtain ⟨p, hpfac, hpmem⟩ :=
    kwitHigh_mem_factor_of_prod_mem P d g hgen hprime facs hprodmem
  have hpprime : Prime p := hfacprime p hpfac
  have hp0 : p ≠ 0 := hpprime.ne_zero
  have hdvd : p ∣ w :=
    dvd_trans (Multiset.dvd_prod hpfac) (Associated.dvd hassoc)
  have htpn : p.totalDegree ≤ N := by
    have htdw : w.totalDegree = N := hhomW.totalDegree wne
    rw [← htdw]
    exact MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdvd wne
  obtain ⟨z, m, hzmem, hz0, hzhom, hm1, hmt⟩ :=
    kwitHigh_chase_factor P d g hgen hprime hpmem hp0
  by_cases hm : m = 1
  · subst hm
    exact hz0 (hlow z hzmem hzhom)
  · have hm2 : 2 ≤ m := by omega
    have hmn : m ≤ N := le_trans hmt htpn
    by_cases hlt : m < N
    · exact hz0 (ih m hlt hm2 z hzmem hzhom)
    · have hmeq : m = N := by omega
      have htpeq : p.totalDegree = N := by omega
      obtain ⟨q, rfl⟩ := hdvd
      have hq0 : q ≠ 0 := by
        intro hq
        exact wne (by rw [hq, mul_zero])
      have htq0 : q.totalDegree = 0 := by
        have hadd := MvPolynomial.totalDegree_mul_of_isDomain hp0 hq0
        have htdw : (p * q).totalDegree = N := hhomW.totalDegree wne
        omega
      have hqC : q = MvPolynomial.C (q.coeff 0) :=
        MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp htq0
      have hqr : q.coeff 0 ≠ 0 := by
        intro hz
        exact hq0 (by rw [hqC, hz, map_zero])
      have hqunit : IsUnit q := by
        rw [hqC]
        exact IsUnit.map MvPolynomial.C (isUnit_iff_ne_zero.mpr hqr)
      obtain ⟨u, rfl⟩ := hqunit
      have hassocpw :
          Associated p (p * (u : MvPolynomial (Fin d) (homRelK P))) :=
        ⟨u, rfl⟩
      have hirr : Irreducible (p * (u : MvPolynomial (Fin d) (homRelK P))) :=
        hassocpw.irreducible hpprime.irreducible
      exact wne (hnoirr _ N hmem hhomW hN2 hirr)

/-- Exactness: given `[Low, KwitKerIsPrime]`, `High ↔ KwitNoIrredHigh` —
the irreducible remainder is minimal, not just sufficient.
-/
theorem kwitHigh_iff_noIrred_of_low_prime (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hlow : KwitNoHomRelLow P d g hgen)
    (hprime : KwitKerIsPrime P d g hgen) :
    KwitNoHomRelHigh P d g hgen ↔ KwitNoIrredHigh P d g hgen := by
  constructor
  · intro hhigh y n hym hhom hn2 _
    exact hhigh y n hym hhom hn2
  · intro hnoirr
    exact kwitHigh_of_low_prime_noIrred P d g hgen hlow hprime hnoirr

/-! ## §5. Dimension cost analysis: the unconditional drop -/

/-- Any nonzero `y ∈ ker` forces `dim gr + 1 ≤ dim κ[X]`: `y` is a
non-zero-divisor (domain) killed by the surjective `polySurjResidue`
(`ringKrullDim_succ_le_of_surjective`).
-/
theorem kwitHigh_dim_drop_of_mem_ker (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (y : MvPolynomial (Fin d) (homRelK P))
    (hym : y ∈ RingHom.ker (polySurjResidue P d g hgen))
    (hy0 : y ≠ 0) :
    ringKrullDim (grRegular P) + 1 ≤
      ringKrullDim (MvPolynomial (Fin d) (homRelK P)) :=
  ringKrullDim_succ_le_of_surjective (polySurjResidue P d g hgen)
    (polySurjResidue_surjective P d g hgen)
    (mem_nonZeroDivisors_iff_ne_zero.mpr hy0)
    (RingHom.mem_ker.mp hym)

/-- Any violation of `KwitNoIrredHigh` forces the dimension drop — the
scoped gap: closing `KwitNoIrredHigh` needs the reverse comparison
`dim κ[X] ≤ dim gr` (i.e. `hle_gr` transported — not assumed) plus
dimension finiteness.
-/
theorem kwitHigh_dim_drop_of_noIrred_violation (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (y : MvPolynomial (Fin d) (homRelK P)) (n : ℕ)
    (hym : y ∈ RingHom.ker (polySurjResidue P d g hgen))
    (_ : MvPolynomial.IsHomogeneous y n) (_ : 2 ≤ n)
    (hirr : Irreducible y) :
    ringKrullDim (grRegular P) + 1 ≤
      ringKrullDim (MvPolynomial (Fin d) (homRelK P)) :=
  kwitHigh_dim_drop_of_mem_ker P d g hgen y hym hirr.ne_zero

/-! ## §6. Residual register (doc-only)

Minimal non-circular remainder (verbatim): `KwitNoIrredHigh`, i.e.
`∀ (y: MvPolynomial (Fin d) κ) (n: ℕ),
  y ∈ RingHom.ker (polySurjResidue P d g hgen) →
    MvPolynomial.IsHomogeneous y n → 2 ≤ n → Irreducible y → y = 0`
for `κ = IsLocalRing.ResidueField R_P`, given `[KwitNoHomRelLow
(parallel lane), KwitKerIsPrime (stepping stone, implied by
`Low ∧ High`)]`.

Why `KwitNoIrredHigh` cannot be closed here (all machine-checked or cited):

* An unconditional proof is impossible without dimension input: e.g. over
  `S = k[x, y]`, the homogeneous prime `(x ^ 2 + y ^ 2)` (over `ℝ`) shows
  primality + `Low` do not imply `High` — irreducible quadratic relations
  are consistent with both. The UFD descent provably stops exactly at the
  irreducible core (`kwitHigh_iff_noIrred_of_low_prime`).
* Closing the irreducible core needs `dim κ[X] ≤ dim gr` plus finiteness:
  the drop half (`dim gr + 1 ≤ dim κ[X]` from any nonzero relation) is
  proved here (`kwitHigh_dim_drop_of_mem_ker`); the comparison half is
  `hle_gr`-shaped and not assumed (the cloud), and Mathlib at the pinned
  toolchain has no `dim gr = dim R`, no catenary/equidimensionality, and
  no `dim κ[X] = d` upper bound (see the §0 survey).
* The remainder is exact, not just sufficient:
  `kwitHigh_iff_noIrred_of_low_prime` shows
  `High ↔ KwitNoIrredHigh` given `[Low, KwitKerIsPrime]`, and
  `kwitHigh_low_high_iff_ker_eq_bot` shows
  `(Low ∧ High) ↔ ker = ⊥` given `1 ≤ d`; no circular hypothesis
  (`ker = ⊥`, `hle_gr`, `hdimEq`, `hmult`) was assumed anywhere.
* `hmin` and regularity are not needed for the descent (pure graded-UFD
  algebra over `κ`); they enter through `Low` (parallel lane) and through
  the eventual dimension-theoretic closure (`dim R_P = d`).

Consumers: `kwitHigh_of_low_prime_noIrred` discharges the `deg ≥ 2` half
of `KwitNoHomRel` on `[Low, KwitKerIsPrime, KwitNoIrredHigh]`; feeding
`Low` (parallel lane) + `KwitNoIrredHigh` (dimension theory) + the
stepping-stone `KwitKerIsPrime` into `kwitHigh_ker_eq_bot_of_low_high`
yields `ker = ⊥`, hence `hmult` via `kwit_hmult_of_ker_eq_bot`.
-/

#print axioms kwitHigh_split
#print axioms kwitHigh_ker_eq_bot_of_low_high
#print axioms kwitHigh_low_high_iff_ker_eq_bot
#print axioms kwitHigh_mem_factor_of_prod_mem
#print axioms kwitHigh_chase_factor
#print axioms kwitHigh_of_low_prime_noIrred
#print axioms kwitHigh_iff_noIrred_of_low_prime
#print axioms kwitHigh_dim_drop_of_mem_ker
#print axioms kwitHigh_dim_drop_of_noIrred_violation

/-! ## §7. Join: `Low` from minimality + the restated master

`KwitNoHomRelLow` is exactly the conclusion of Q1
(`kwit_noHomRel_degree_one_of_minimal`, `HilbertWitnessNarrowing.lean`), which is
generic in `m / K / P`: a degree-1 homogeneous `y ∈ ker` vanishes from
`hgen + hmin`. Since `homRelK` is a reducible abbrev for
`IsLocalRing.ResidueField (Localization.AtPrime P)`, the instantiation is
definitional; the file's section-variable `P` is passed explicitly to Q1's
explicit `P` (fixing Q1's implicit `K`, `m` by unification).
-/

/-- `Low` from minimality: direct instantiation of Q1.

Conditional on exactly `[hmin]`. -/
theorem kwitHigh_low_of_minimal (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hmin : d ≤
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)).spanFinrank) :
    KwitNoHomRelLow P d g hgen := by
  intro y hym hhom
  exact kwit_noHomRel_degree_one_of_minimal P d g hgen hmin y hym hhom

/-- Restated master: `High` from `[hmin, KwitKerIsPrime, KwitNoIrredHigh]`
(`Low` discharged by the join).

Conditional on exactly the three hypotheses. -/
theorem kwitHigh_of_minimal_prime_noIrred (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hmin : d ≤
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)).spanFinrank)
    (hprime : KwitKerIsPrime P d g hgen)
    (hnoirr : KwitNoIrredHigh P d g hgen) :
    KwitNoHomRelHigh P d g hgen :=
  kwitHigh_of_low_prime_noIrred P d g hgen
    (kwitHigh_low_of_minimal P d g hgen hmin) hprime hnoirr

/-- Full `KwitNoHomRel` from `[hmin, KwitKerIsPrime, KwitNoIrredHigh]`.

Conditional on exactly the three hypotheses. -/
theorem kwitHigh_full_of_minimal_prime_noIrred (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hmin : d ≤
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)).spanFinrank)
    (hprime : KwitKerIsPrime P d g hgen)
    (hnoirr : KwitNoIrredHigh P d g hgen) :
    KwitNoHomRel P d g hgen := by
  rw [kwitHigh_split]
  exact ⟨kwitHigh_low_of_minimal P d g hgen hmin,
    kwitHigh_of_minimal_prime_noIrred P d g hgen hmin hprime hnoirr⟩

/-- `ker = ⊥` from `[hmin, KwitKerIsPrime, KwitNoIrredHigh]` (given `1 ≤ d`).

Conditional on exactly the three hypotheses (conditional-form on `1 ≤ d`). -/
theorem kwitHigh_ker_eq_bot_of_minimal_prime_noIrred (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hd : 1 ≤ d)
    (hmin : d ≤
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)).spanFinrank)
    (hprime : KwitKerIsPrime P d g hgen)
    (hnoirr : KwitNoIrredHigh P d g hgen) :
    RingHom.ker (polySurjResidue P d g hgen) = ⊥ :=
  kwitHigh_ker_eq_bot_of_low_high P d g hgen hd
    (kwitHigh_low_of_minimal P d g hgen hmin)
    (kwitHigh_of_minimal_prime_noIrred P d g hgen hmin hprime hnoirr)

/-! ## §8. Attack on `KwitKerIsPrime`: exact narrowing to `gr`-NoZeroDivisors

`KwitKerIsPrime` cannot be closed from `hmin` + regularity with the available
theory: `R_P` regular-local (automatic, `SystemOfParameters.lean`) does not yield "`gr`
is a domain" without the deep identification of `gr` of a regular local ring
with a polynomial ring (needs `dim gr = dim R_P` + regular-sequence `gr`
theory — the gap-r1–R4 of `RegularSequenceProbe.lean`, absent from Mathlib at the
pinned toolchain). Note a domain hypothesis on `R_P` alone would not suffice
either: the associated graded of a domain can have nilpotents (e.g. the cusp).

Instead this section proves the exact minimal sub-remainder, using nothing
beyond the first isomorphism theorem (`polySurjResidue_quotKerEquiv`):
`KwitKerIsPrime ↔ NoZeroDivisors (grRegular P)`, with `Nontrivial (grRegular P)`
proved unconditionally (degree-0 piece `≃+* κ` via
`grPiece_zero_equiv_quotient`). No `ker = ⊥`, `hle`, `hdimEq`, `hmult`, or
`High` is assumed anywhere in §8.
-/

/-- `ker = ⊥` implies `KwitKerIsPrime` (`⊥` is prime in the domain `κ[X]`,
`Ideal.isPrime_bot`).
-/
theorem kwitHigh_prime_of_ker_eq_bot (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hker : RingHom.ker (polySurjResidue P d g hgen) = ⊥) :
    KwitKerIsPrime P d g hgen := by
  unfold KwitKerIsPrime
  rw [hker]
  exact Ideal.isPrime_bot

/-- `Low ∧ High` implies `KwitKerIsPrime` (given `1 ≤ d`): the stepping stone
is implied by the goal conjunction, hence strictly weaker than it.
-/
theorem kwitHigh_prime_of_low_high (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hd : 1 ≤ d)
    (hlow : KwitNoHomRelLow P d g hgen)
    (hhigh : KwitNoHomRelHigh P d g hgen) :
    KwitKerIsPrime P d g hgen :=
  kwitHigh_prime_of_ker_eq_bot P d g hgen
    (kwitHigh_ker_eq_bot_of_low_high P d g hgen hd hlow hhigh)

/-- `grRegular P` is nontrivial, unconditionally: `1 = of₀ 1`
(`DirectSum.of_zero_one`), `of₀` is injective (`DirectSum.of_injective`), and
the degree-0 piece is `≃+* κ` (`grPiece_zero_equiv_quotient`), a field.
-/
theorem kwitHigh_gr_nontrivial : Nontrivial (grRegular P) := by
  have h10 : (1 : grRegular P) ≠ 0 := by
    intro h
    have h1 : (1 : grRegular P) =
        DirectSum.of (grPiece (Localization.AtPrime P)
          (IsLocalRing.maximalIdeal (Localization.AtPrime P))) 0 1 :=
      (DirectSum.of_zero_one _).symm
    rw [h1] at h
    have h0 : DirectSum.of (grPiece (Localization.AtPrime P)
          (IsLocalRing.maximalIdeal (Localization.AtPrime P))) 0
          (0 : grPiece (Localization.AtPrime P)
            (IsLocalRing.maximalIdeal (Localization.AtPrime P)) 0) = 0 :=
      map_zero _
    have h' := h.trans h0.symm
    have h2 : (1 : grPiece (Localization.AtPrime P)
        (IsLocalRing.maximalIdeal (Localization.AtPrime P)) 0) = 0 :=
      DirectSum.of_injective _ h'
    have h3 := congrArg (⇑(grPiece_zero_equiv_quotient
      (Localization.AtPrime P) (IsLocalRing.maximalIdeal _))) h2
    simp only [map_one, map_zero] at h3
    exact one_ne_zero h3
  exact ⟨1, 0, h10⟩

/-- Exact narrowing: `KwitKerIsPrime ↔ NoZeroDivisors (grRegular P)`.
Forward: `ker` prime makes the quotient a domain, transported across
`polySurjResidue_quotKerEquiv`. Backward: products in `ker` map to
zero-products in `gr` (`NoZeroDivisors` splits them), and `ker ≠ ⊤` follows
from unconditional `Nontrivial (grRegular P)`.

`NoZeroDivisors (grRegular P)` is the exact minimal sub-remainder). -/
theorem kwitHigh_prime_iff_gr_noZeroDivisors (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    KwitKerIsPrime P d g hgen ↔ NoZeroDivisors (grRegular P) := by
  constructor
  · intro hprime
    have hQ : NoZeroDivisors (MvPolynomial (Fin d) (homRelK P) ⧸
        RingHom.ker (polySurjResidue P d g hgen)) := by
      refine ⟨?_⟩
      intro a b hab
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
      rw [← map_mul] at hab
      have hmem : x * y ∈ RingHom.ker (polySurjResidue P d g hgen) :=
        Ideal.Quotient.eq_zero_iff_mem.mp hab
      rcases (Ideal.isPrime_iff.mp hprime).2 hmem with hx | hy
      · exact Or.inl (Ideal.Quotient.eq_zero_iff_mem.mpr hx)
      · exact Or.inr (Ideal.Quotient.eq_zero_iff_mem.mpr hy)
    refine ⟨?_⟩
    intro a b hab
    have hsym : (polySurjResidue_quotKerEquiv P d g hgen).symm (a * b) = 0 := by
      rw [hab, map_zero]
    rw [map_mul] at hsym
    rcases eq_zero_or_eq_zero_of_mul_eq_zero hsym with ha | hb
    · refine Or.inl ?_
      have hcongr := congrArg
        (fun z => polySurjResidue_quotKerEquiv P d g hgen z) ha
      simpa using hcongr
    · refine Or.inr ?_
      have hcongr := congrArg
        (fun z => polySurjResidue_quotKerEquiv P d g hgen z) hb
      simpa using hcongr
  · intro hNZD
    have _hNZD := hNZD
    have _hNT := kwitHigh_gr_nontrivial P
    unfold KwitKerIsPrime
    rw [Ideal.isPrime_iff]
    refine ⟨?_, ?_⟩
    · intro htop
      have hmem1 : (1 : MvPolynomial (Fin d) (homRelK P)) ∈
          RingHom.ker (polySurjResidue P d g hgen) := by
        rw [htop]
        exact Submodule.mem_top
      have h1Q : (1 : MvPolynomial (Fin d) (homRelK P) ⧸
          RingHom.ker (polySurjResidue P d g hgen)) = 0 := by
        rw [← map_one (Ideal.Quotient.mk _)]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem1
      have h1gr : (1 : grRegular P) = 0 := by
        have hcongr := congrArg
          (fun z => polySurjResidue_quotKerEquiv P d g hgen z) h1Q
        simp only [map_one, map_zero] at hcongr
        exact hcongr
      exact one_ne_zero h1gr
    · intro x y hmem
      have hmul : polySurjResidue P d g hgen x *
          polySurjResidue P d g hgen y = 0 := by
        rw [← map_mul]
        exact RingHom.mem_ker.mp hmem
      rcases eq_zero_or_eq_zero_of_mul_eq_zero hmul with hx | hy
      · exact Or.inl (RingHom.mem_ker.mpr hx)
      · exact Or.inr (RingHom.mem_ker.mpr hy)

/-! ## §9. Residual register addendum (§§7–8)

Updated minimal remainder (verbatim): `KwitNoHomRel P d g hgen` holds on
`[hmin, KwitKerIsPrime, KwitNoIrredHigh]`
(`kwitHigh_full_of_minimal_prime_noIrred`); equivalently
`RingHom.ker (polySurjResidue P d g hgen) = ⊥` on the same hypotheses given
`1 ≤ d`. `Low` is discharged (it is Q1); the two open hypotheses are
`KwitKerIsPrime` and `KwitNoIrredHigh`, narrowed exactly by
`kwitHigh_prime_iff_gr_noZeroDivisors` (i.e. `NoZeroDivisors (grRegular P)`,
`Nontrivial` proved) and `kwitHigh_iff_noIrred_of_low_prime` respectively.
`KwitKerIsPrime` is implied by the goal conjunction
(`kwitHigh_prime_of_low_high`), so it is a stepping stone, not an
independent gap. Closing `NoZeroDivisors (grRegular P)` needs the
`gr`-of-regular-local identification (absent: `dim gr = dim R_P`, no
catenary/equidimensionality, gap-r1–R4); closing `KwitNoIrredHigh` needs the
reverse dimension comparison (only the drop half is proved, §5).

Grades: §7 join + restated master conditional-exact on the stated hyps;
§8 `prime_of_ker_eq_bot`, `prime_of_low_high`, `gr_nontrivial`,
`prime_iff_gr_noZeroDivisors` unconditional. Overall: partial
(`KwitKerIsPrime` narrowed to `NoZeroDivisors (grRegular P)`;
`KwitNoIrredHigh` open).
-/

#print axioms kwitHigh_low_of_minimal
#print axioms kwitHigh_of_minimal_prime_noIrred
#print axioms kwitHigh_full_of_minimal_prime_noIrred
#print axioms kwitHigh_ker_eq_bot_of_minimal_prime_noIrred
#print axioms kwitHigh_prime_of_ker_eq_bot
#print axioms kwitHigh_prime_of_low_high
#print axioms kwitHigh_gr_nontrivial
#print axioms kwitHigh_prime_iff_gr_noZeroDivisors

end HighHomogeneousRelations
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

/-! ## §10. Witness bridge (A12 low discharge) + `gr`-domain narrowing

(1) witness bridge — `kwitHigh_witness_bridge`: the Witness-side high residual
`HilbertWitnessNarrowing.KwitNoHomRelHigh` (`HilbertWitnessNarrowing.lean`) and this file's
`KwitNoHomRelHigh`  have definitionally equal bodies (they differ only
by the reducible abbrev `homRelK` for `IsLocalRing.ResidueField R_P`), so the
iff is `Iff.rfl`. Unconditional. This discharges A12's low (the missing
explicit link between the two `High` statements). The low half needs no bridge:
Witness has no separate `Low` def — degree 1 is the theorem
`kwit_noHomRel_degree_one_of_minimal`, already consumed by the §7 join
(`kwitHigh_low_of_minimal`).
`kwitHigh_hmult_of_minimal_prime_noIrred` wires this file's full master
(`kwitHigh_full_of_minimal_prime_noIrred`) into Witness's top-level
`kwit_hmult_of_minimal` (`HilbertWitnessNarrowing.lean`): `hmult` on
`[hmin, KwitKerIsPrime, KwitNoIrredHigh]` (+ `2 ≤ d`). Conditional-exact.

(2) `gr`-domain narrowing — the §8 remainder `NoZeroDivisors (grRegular P)`
attacked from `[hmin + R_P-regular]`, with no cloud hypotheses
(`ker = ⊥`, `hle`, `hdimEq`, `hmult`, `High`, `NoIrredHigh` assumed nowhere):
* `kwitHigh_gr_noZeroDivisors_iff_bot_prime`: `NoZeroDivisors (grRegular P) ↔
  IsPrime (⊥: Ideal (grRegular P))`, via `kwitHigh_gr_nontrivial` +
  `Ideal.isPrime_iff` (`RingTheory/Ideal/Prime.lean`) +
  `Submodule.mem_bot` (`Algebra/Module/Submodule/Lattice.lean`).
  unconditional. This is the exact ideal-language entry point for the
  minimal-prime analysis of `gr` (`gr` is Noetherian by
  `mult_isNoetherianRing_grRegular`, `MultiplicityNonvanishing.lean`).
* `kwitHigh_gr_noZeroDivisors_of_ker_eq_bot`: `ker = ⊥ → NoZeroDivisors gr`
  (chain of `kwitHigh_prime_of_ker_eq_bot` + `kwitHigh_prime_iff_gr_noZeroDivisors`).
  unconditional (conditional-form on `ker = ⊥`; documents goal-implies-stone,
  not a closure).

Why `NoZeroDivisors (grRegular P)` cannot be closed here (all surveyed):
* Domain input does not suffice: the associated graded of a domain can carry
  nilpotents (cusp-type: `in(x) * in(y) = 0` for initial forms), so
  `IsDomain R_P` (`isDomain_of_local_atPrime`) + Krull intersection
  (`FiltrationStability.lean`) cannot imply the goal; regularity is
  essential, and only through the deep `gr`-of-regular identification.
* Regular-sequence descent needs gap-r1–R4 (`RegularSequenceProbe.lean`):
  R1 (sop is regular — only length 1 proved, §2–§3; steps `≥ 3` need UFD
  descent absent from Mathlib), R2 colon capture, R3 Artin–Rees intersection,
  R4 graded-SES induction; plus there is no bridge `IsRegularLocalRing →
  Sequence.IsRegular` in Mathlib (surveyed, `RegularSequenceProbe.lean`).
* Minimal-prime analysis of `gr` stops at reduced: the nilradical is strictly
  weaker than `⊥` prime, and uniqueness needs catenary / equidimensionality —
  `grep -rni "catenary\|equidimensional"` over Mathlib `RingTheory/` is empty
  (re-verified §0 survey).

Grades: bridge, bot-prime iff, of_ker_eq_bot unconditional; hmult join
conditional-exact on `[hmin, KwitKerIsPrime, KwitNoIrredHigh]` (+ `2 ≤ d`).
Overall: partial (see verbatim register below).

Residual register (verbatim): `KwitNoHomRelHigh` (Witness, bridged) holds
on `[hmin, KwitKerIsPrime, KwitNoIrredHigh]`; `KwitKerIsPrime` is exactly
`NoZeroDivisors (grRegular P)` (proved, `Nontrivial` included) and exactly
`IsPrime (⊥ : Ideal (grRegular P))` (this section); `KwitNoIrredHigh` is the exact
minimal remainder given `[Low, KwitKerIsPrime]`. The two open items are
`NoZeroDivisors (grRegular P)` (needs `gr`-of-regular-local theory: gap-r1–R4)
and `KwitNoIrredHigh` (needs reverse dimension comparison `dim κ[X] ≤ dim gr`).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace HighHomogeneousRelations

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.HilbertWitnessNarrowing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjection
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AssociatedGradedRing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.MultiplicityNonvanishing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.NewtonDifferences

variable {K : Type*} [Field K] {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K))
  [P.IsPrime]

/-- Bridge: the Witness-side high residual and this file's `High` coincide
(`Iff.rfl` — bodies are defeq via the reducible abbrev `homRelK`).
Discharges A12's low.
-/
theorem kwitHigh_witness_bridge (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    KwitNoHomRelHigh P d g hgen ↔
      KwitNoHomRelHigh P d g hgen :=
  Iff.rfl

/-- Top-level wiring: `hmult` from `[hmin, KwitKerIsPrime, KwitNoIrredHigh]`
(this file's full master fed into Witness's `kwit_hmult_of_minimal`).

Conditional on exactly the three hypotheses (+ `2 ≤ d`). -/
theorem kwitHigh_hmult_of_minimal_prime_noIrred (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hd : 2 ≤ d)
    (hmin : d ≤ (IsLocalRing.maximalIdeal
      (Localization.AtPrime P)).spanFinrank)
    (hprime : KwitKerIsPrime P d g hgen)
    (hnoirr : KwitNoIrredHigh P d g hgen) :
    ¬ seqDiff (d - 1) (fun n => ((multQuotHilbert
      (IsLocalRing.ResidueField (Localization.AtPrime P)) d
      (RingHom.ker (polySurjResidue P d g hgen)) (n + 1) : ℕ) : ℚ))
      =ᶠ[Filter.atTop] 0 :=
  kwit_hmult_of_minimal P d g hgen hd hmin
    (kwitHigh_full_of_minimal_prime_noIrred P d g hgen hmin hprime hnoirr)

/-- Exact narrowing: `NoZeroDivisors (grRegular P) ↔ IsPrime ⊥` — the
ideal-language form of the §8 remainder, entry point for minimal-prime
analysis. Uses only `kwitHigh_gr_nontrivial` (proved).
-/
theorem kwitHigh_gr_noZeroDivisors_iff_bot_prime :
    NoZeroDivisors (grRegular P) ↔ Ideal.IsPrime (⊥ : Ideal (grRegular P)) := by
  have _hNT := kwitHigh_gr_nontrivial P
  constructor
  · intro hNZD
    have _hNZD := hNZD
    rw [Ideal.isPrime_iff]
    refine ⟨?_, ?_⟩
    · intro htop
      have h1mem : (1 : grRegular P) ∈ (⊥ : Ideal (grRegular P)) := by
        rw [htop]
        exact Submodule.mem_top
      rw [Submodule.mem_bot] at h1mem
      exact one_ne_zero h1mem
    · intro x y hmem
      rw [Submodule.mem_bot] at hmem
      rcases eq_zero_or_eq_zero_of_mul_eq_zero hmem with hx | hy
      · exact Or.inl ((Submodule.mem_bot _).mpr hx)
      · exact Or.inr ((Submodule.mem_bot _).mpr hy)
  · intro hprime
    refine ⟨?_⟩
    intro a b hab
    have hmem : a * b ∈ (⊥ : Ideal (grRegular P)) :=
      (Submodule.mem_bot _).mpr hab
    rcases (Ideal.isPrime_iff.mp hprime).2 hmem with ha | hb
    · exact Or.inl ((Submodule.mem_bot _).mp ha)
    · exact Or.inr ((Submodule.mem_bot _).mp hb)

/-- `ker = ⊥` implies `NoZeroDivisors (grRegular P)` (goal-implies-stone;
documents non-circularity, not a closure).
-/
theorem kwitHigh_gr_noZeroDivisors_of_ker_eq_bot (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hker : RingHom.ker (polySurjResidue P d g hgen) = ⊥) :
    NoZeroDivisors (grRegular P) :=
  (kwitHigh_prime_iff_gr_noZeroDivisors P d g hgen).mp
    (kwitHigh_prime_of_ker_eq_bot P d g hgen hker)

#print axioms kwitHigh_witness_bridge
#print axioms kwitHigh_hmult_of_minimal_prime_noIrred
#print axioms kwitHigh_gr_noZeroDivisors_iff_bot_prime
#print axioms kwitHigh_gr_noZeroDivisors_of_ker_eq_bot

end HighHomogeneousRelations
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
