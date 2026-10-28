/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Statement.Definitions
import Appendix_FixedPoint.BezoutChain.Statement.GenericLinear
import Appendix_FixedPoint.BezoutChain.Statement.Statement
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.AvoidanceApply
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.RegularityBridge
import Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.Submodule.Bilinear
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.List.OfFn
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Generic choices of linear forms and quadrics (regular-element toolkit)

This module proves two generic-choice results.
Despite the file name, no resultants are used; regularity throughout comes
from prime avoidance:

* `exists_regular_chartForm` (R1): a linear form `ℓ` whose image in the cone
  quotient `S` is regular and which is nonzero on every projective point of
  the locus.
* `exists_regular_quadrics` (R2): a unit matrix `M` of `K`-linear combinations
  of the equations whose images in `S` form a regular sequence.

The shared engine is finite-subspace avoidance over the infinite field `K`:
regularity comes from prime avoidance —
zerodivisors are the union of the associated primes — plus simultaneous
avoidance of finitely many point-evaluation kernels, all via
`Appendix_FixedPoint.BezoutChain.GenericLinear.not_covered_by_proper_submodules`.

## Adaptations to the stated signatures

1. `hS : coneQuotient n K G ≠ 0` does not elaborate (`coneQuotient` is a
   `Type`, so `≠ 0` is a type error). The intended meaning is
   `Nontrivial (coneQuotient n K G)`, used here.
2. `IsSMulRegular S (mkLin ℓ)` does not elaborate (`mkLin ℓ` is a polynomial,
   but regularity needs an element of `S`). The quotient image
   `Ideal.Quotient.mk _ (mkLin n K ℓ)` is used here.
3. In `exists_regular_quadrics`, `S` is unbound and the listed combination
   elements are polynomials rather than elements of `S`. `S` is taken to be
   `coneQuotient n K G` and the combinations are pushed through
   `Ideal.Quotient.mk _`.
4. Both statements are *false* as stated with only `hS`, so further
   hypotheses are added (each names exactly the obstruction):
   * `hfin : (vanishingLocus n K G).Finite` for the point conditions: with
     `G = 0` the locus is all of projective space, on which every nonzero
     linear form vanishes somewhere, so no `ℓ` can satisfy the conclusion.
   * `havoid`: every associated prime must cut the space of available
     coefficients in a *proper* subspace. Without this, no generic choice can
     exist (e.g. an associated prime containing all linear forms kills every
     candidate). Discharging `havoid` for the concrete system is left to the
     downstream depth/Cohen–Macaulay argument.
   * `hG : ∀ i, (G i).IsHomogeneous 2` for `exists_regular_quadrics`: the
     homogeneous-origin trick (every combination vanishes at `0`, so the
     final span is proper) gives `top_ne_smul`.
   The `Nontrivial` hypothesis `_hS` is retained for interface stability even
   though the union-lemma path below does not consume it.

## Notes on the Mathlib API

* The regular-sequence API lives in
  `Mathlib/RingTheory/Regular/RegularSequence.lean` (namespace
  `RingTheory.Sequence`), not under `Depth/*`. Moreover `IsRegular` takes the
  *module* first: `RingTheory.Sequence.IsRegular S l` with `S` acting on
  itself is well formed and is what is used here.
* `biUnion_associatedPrimes_eq_compl_regular` exists but at top level
  (in `Mathlib/RingTheory/Regular/IsSMulRegular.lean`), not under `Ideal.*`;
  likewise `associatedPrimes.finite` (`Finiteness.lean`) and
  `associatedPrimes.nonempty` are top-level. `associatedPrimes.finite` needs
  `[IsNoetherianRing A] [Module.Finite A M]` (both satisfied here by instances).
* `Ideal.finite_minimalPrimes_of_isNoetherianRing` does exist
  (`Mathlib/RingTheory/Ideal/MinimalPrime/Noetherian.lean`); this file uses
  finiteness of *associated* primes instead, since regularity is controlled by
  `Ass`, not by minimal primes.

## `mkSystem` narrowing (`exists_regular_quadrics_mkSystem`, below)

R2 at `G = mkSystem n K F`, conditional on `hunmixed`-at-`k ≥ 2` only: the
proof is `exists_regular_quadrics` with `havoid` discharged per step by
`AvoidanceApply.comap_ne_top_zero_of_t1` (`k = 0`, t1-style `Gᵢ ≠ 0`) and
`AvoidanceApply.comap_ne_top_of_step` (`k ≥ 1`, proved `k ≤ 1` unmixedness +
explicit `hunmixed_ge2`), with `hsucc` repackaged by
`AvoidanceApply.hsucc_of_step_outputs`. Homogeneity via
`mkSystem_homogeneous`.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
open scoped BigOperators

/-- Regularity from avoiding every associated prime: over a Noetherian ring,
an element outside `⋃ Ass` is regular. Contrapositive of the union lemma.

## References

* `Mathlib/RingTheory/Regular/IsSMulRegular.lean`,
  `biUnion_associatedPrimes_eq_compl_regular`. -/
theorem regular_of_avoid (S Q : Type*) [CommRing S] [IsNoetherianRing S]
    [AddCommGroup Q] [Module S Q] (x : S)
    (hav : ∀ P ∈ associatedPrimes S Q, x ∉ (P : Set S)) :
    IsSMulRegular Q x := by
  have hU := biUnion_associatedPrimes_eq_zero_divisors S Q
  intro a b hab
  have hab' : x • a = x • b := hab
  have hsub : x • (a - b) = 0 := by rw [smul_sub, hab', sub_self]
  by_cases hzero : a - b = 0
  · exact sub_eq_zero.mp hzero
  · exfalso
    have hmem : x ∈ ⋃ P ∈ associatedPrimes S Q, (P : Set S) := by
      rw [hU]
      exact ⟨a - b, hzero, hsub⟩
    rw [Set.mem_iUnion₂] at hmem
    obtain ⟨P, hP, hm⟩ := hmem
    exact hav P hP hm

/-- Parallel-avoidance engine: over an infinite field, one coefficient
vector avoids any finite family of proper submodules. Both the
associated-prime pullbacks and the point-evaluation kernels below are fed
through this single lemma.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GenericLinear`,
  `Appendix_FixedPoint.BezoutChain.not_covered_by_proper_submodules` (itself a corollary of
  `Submodule.exists_forall_notMem_of_forall_ne_top`). -/
theorem exists_avoiding_coeff {ι : Type*} (K : Type*) [Field K]
    [IsAlgClosed K] (W : Finset (Submodule K (ι → K)))
    (hW : ∀ w ∈ W, w ≠ ⊤) :
    ∃ ℓ : ι → K, ∀ w ∈ W, ℓ ∉ w := by
  have hU := not_covered_by_proper_submodules W hW
  have hex : ∃ ℓ, ℓ ∉ ⋃ s ∈ W, (s : Set (ι → K)) := by
    by_contra hcon
    push Not at hcon
    exact hU (Set.eq_univ_of_forall hcon)
  obtain ⟨ℓ, hℓ⟩ := hex
  exact ⟨ℓ, fun w hw hm => hℓ (Set.mem_iUnion₂.mpr
    ⟨w, Finset.mem_coe.mpr hw, hm⟩)⟩

/-- The coefficient-to-linear-form map into the cone quotient.

## References

* `Mathlib/RingTheory/Ideal/Quotient/Defs.lean`, `Ideal.Quotient.mk`;
  `Mathlib/RingTheory/Ideal/Quotient/Operations.lean`,
  `Ideal.Quotient.algebra` (the `Algebra K` structure feeding `Module K ↥S`). -/
noncomputable def coeffToCone (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K) :
    (Fin (n + 2) → K) →ₗ[K] coneQuotient n K G :=
  comboLin K (fun j => Ideal.Quotient.mk (Ideal.span (Set.range G))
    (MvPolynomial.X j))

/-- Evaluation of `mkLin` is the dot product.

## References

* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.eval_C`,
  `MvPolynomial.eval_X` (with `map_sum`, `map_mul` for the `eval` ring hom). -/
theorem eval_mkLin (n : ℕ) (K : Type*) [Field K]
    (v ℓ : Fin (n + 2) → K) :
    MvPolynomial.eval v (mkLin n K ℓ) = ∑ j, ℓ j * v j := by
  simp only [mkLin, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]

/-- `comboLin` against a point is evaluation of `mkLin` (used to transport the
kernel-avoidance conclusion back to `eval`-nonvanishing).

## References

* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.eval_C`,
  `MvPolynomial.eval_X`; `smul_eq_mul`. -/
theorem comboLin_eval (n : ℕ) (K : Type*) [Field K]
    (v ℓ : Fin (n + 2) → K) :
    comboLin K v ℓ = MvPolynomial.eval v (mkLin n K ℓ) := by
  rw [comboLin_apply, eval_mkLin]
  apply Finset.sum_congr rfl
  intro j _
  exact smul_eq_mul _ _

/-- Pushing a scalar multiple through the cone quotient map.

Proved via the bundled algebra map `Ideal.Quotient.mkₐ` and `map_smul`:
the quotient `Module K` structure is quotient-induced, so rewriting the
scalar action through `Algebra.algebraMap` by `rfl` fails; the bundled-map
transport avoids the issue entirely.

## References

* `Mathlib/RingTheory/Ideal/Quotient/Operations.lean`, `Ideal.Quotient.mkₐ`,
  `Ideal.Quotient.mkₐ_eq_mk`; `map_smul` for the algebra hom. -/
theorem mk_quotient_smul (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K) (c : K)
    (p : MvPolynomial (Fin (n + 2)) K) :
    Ideal.Quotient.mk (Ideal.span (Set.range G)) (c • p)
      = c • Ideal.Quotient.mk (Ideal.span (Set.range G)) p := by
  have e : (Ideal.Quotient.mkₐ K (Ideal.span (Set.range G))) (c • p)
      = c • (Ideal.Quotient.mkₐ K (Ideal.span (Set.range G))) p :=
    map_smul _ _ _
  have h1 : Ideal.Quotient.mk (Ideal.span (Set.range G)) (c • p)
      = (Ideal.Quotient.mkₐ K (Ideal.span (Set.range G))) (c • p) := by
    rw [Ideal.Quotient.mkₐ_eq_mk]
  have h2 : (Ideal.Quotient.mkₐ K (Ideal.span (Set.range G))) p
      = Ideal.Quotient.mk (Ideal.span (Set.range G)) p := by
    rw [Ideal.Quotient.mkₐ_eq_mk]
  rw [h1, e, h2]

/-- The quotient image of `mkLin` is the combination of variable images.

## References

* `Mathlib/Algebra/MvPolynomial/Basic.lean`, `MvPolynomial.smul_eq_C_mul`.
* `Mathlib/RingTheory/Ideal/Quotient/Operations.lean`,
  `Ideal.Quotient.mkₐ` (via `mk_quotient_smul` above). -/
theorem mk_mkLin (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K) (ℓ : Fin (n + 2) → K) :
    Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)
      = coeffToCone n K G ℓ := by
  simp only [coeffToCone, comboLin_apply, mkLin, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  have e1 : MvPolynomial.C (ℓ j) * MvPolynomial.X j
      = (ℓ j) • MvPolynomial.X j :=
    (MvPolynomial.smul_eq_C_mul _ _).symm
  rw [e1]
  exact mk_quotient_smul n K G _ _

/-- R1: a regular chart form avoiding the locus. Given `S ≠ 0` (as
`Nontrivial`), finiteness of the projective locus, and properness of every
associated-prime pullback to coefficient space, there is a linear form whose
image in `S` is regular and which vanishes at no point of the locus (on any
representative). See the module docstring for why `hfin`/`havoid` are needed.
Note: `_hS` is retained for interface stability and is intentionally unused on
the union-lemma path below (see the module docstring).

## References

* `biUnion_associatedPrimes_eq_compl_regular`,
  `associatedPrimes.finite S S` (needs `IsNoetherianRing S` from
  `Mathlib/RingTheory/Ideal/Quotient/Noetherian.lean` and
  `Mathlib/RingTheory/Polynomial/Basic.lean`, plus `Module.Finite.self`).
* `Projectivization.rep_nonzero`, `Projectivization.mk_rep`,
  `Projectivization.mk_eq_mk_iff`
  (`Mathlib/LinearAlgebra/Projectivization/Basic.lean`): every locus point
  contributes one representative to the finite avoidance family, and an
  arbitrary representative is a unit multiple of it, so nonvanishing transfers.
* `IsAlgClosed K → Infinite K`
  (`Mathlib/FieldTheory/IsAlgClosed/Basic.lean`, instance) feeds the engine. -/
theorem exists_regular_chartForm (n : ℕ) (K : Type*) [Field K] [IsAlgClosed K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (_hS : Nontrivial (coneQuotient n K G))
    (hfin : (vanishingLocus n K G).Finite)
    (havoid : ∀ P ∈ associatedPrimes (coneQuotient n K G) (coneQuotient n K G),
      Submodule.comap (coeffToCone n K G)
        (Submodule.restrictScalars K
          (P : Submodule (coneQuotient n K G) (coneQuotient n K G))) ≠ ⊤) :
    ∃ ℓ : Fin (n + 2) → K,
      IsSMulRegular (coneQuotient n K G)
        (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ∧
      ∀ p ∈ vanishingLocus n K G, ∀ (v : Fin (n + 2) → K) (hv : v ≠ 0),
        Projectivization.mk K v hv = p → MvPolynomial.eval v (mkLin n K ℓ) ≠ 0 := by
  classical
  have hAssFin :=
    associatedPrimes.finite (coneQuotient n K G) (coneQuotient n K G)
  obtain ⟨ℓ, hℓ⟩ := exists_avoiding_coeff K
    (hAssFin.toFinset.image (fun P => Submodule.comap (coeffToCone n K G)
        (Submodule.restrictScalars K
          (P : Submodule (coneQuotient n K G) (coneQuotient n K G))))
      ∪ hfin.toFinset.image
        (fun p => LinearMap.ker (comboLin K (p.rep : Fin (n + 2) → K))))
    (by
      intro w hw
      rw [Finset.mem_union] at hw
      rcases hw with hA | hB
      · obtain ⟨P, hPmem, rfl⟩ := Finset.mem_image.mp hA
        exact havoid P ((Set.Finite.mem_toFinset hAssFin).mp hPmem)
      · obtain ⟨p, hpL, rfl⟩ := Finset.mem_image.mp hB
        have hrep : p.rep ≠ (0 : Fin (n + 2) → K) :=
          Projectivization.rep_nonzero p
        obtain ⟨j, hj⟩ := Function.ne_iff.mp hrep
        intro hker
        have hmem : (Pi.single j (1 : K) : Fin (n + 2) → K) ∈
            LinearMap.ker (comboLin K (p.rep : Fin (n + 2) → K)) := by
          rw [hker]
          exact Submodule.mem_top
        have hval : comboLin K (p.rep : Fin (n + 2) → K)
            ((Pi.single j (1 : K) : Fin (n + 2) → K)) = p.rep j := by
          have h0 : ∀ l ∈ (Finset.univ : Finset (Fin (n + 2))), l ≠ j →
              (((Pi.single j (1 : K) : Fin (n + 2) → K)) l • p.rep l) = 0 := by
            intro l _ hlj
            rw [Pi.single_eq_of_ne hlj, zero_smul]
          rw [comboLin_apply,
            Finset.sum_eq_single_of_mem j (Finset.mem_univ j) h0,
            Pi.single_eq_same, one_smul]
        rw [LinearMap.mem_ker, hval] at hmem
        exact hj hmem)
  have hreg : IsSMulRegular (coneQuotient n K G) (coeffToCone n K G ℓ) := by
    refine regular_of_avoid (coneQuotient n K G) _ _ ?_
    intro P hP hm
    have hmem : ℓ ∈ Submodule.comap (coeffToCone n K G)
        (Submodule.restrictScalars K
          (P : Submodule (coneQuotient n K G) (coneQuotient n K G))) :=
      Submodule.mem_comap.mpr hm
    exact hℓ _ (Finset.mem_union_left _ (Finset.mem_image.mpr
      ⟨P, (Set.Finite.mem_toFinset hAssFin).mpr hP, rfl⟩)) hmem
  refine ⟨ℓ, by rw [mk_mkLin]; exact hreg, ?_⟩
  intro p hp v hv hmk
  have hrepL : p ∈ hfin.toFinset := (Set.Finite.mem_toFinset hfin).mpr hp
  have hker_mem : LinearMap.ker (comboLin K (p.rep : Fin (n + 2) → K))
      ∈ hAssFin.toFinset.image (fun P => Submodule.comap (coeffToCone n K G)
          (Submodule.restrictScalars K
            (P : Submodule (coneQuotient n K G) (coneQuotient n K G))))
        ∪ hfin.toFinset.image
          (fun p => LinearMap.ker (comboLin K (p.rep : Fin (n + 2) → K))) :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p, hrepL, rfl⟩)
  have hne : comboLin K (p.rep : Fin (n + 2) → K) ℓ ≠ 0 :=
    fun h0 => hℓ _ hker_mem (LinearMap.mem_ker.mpr h0)
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' K v p.rep hv
    p.rep_nonzero).mp (hmk.trans p.mk_rep.symm)
  have ha0 : a ≠ 0 := fun haz => hv (by rw [haz, zero_smul] at ha; exact ha.symm)
  have hscale : comboLin K ((a : K) • p.rep) ℓ
      = (a : K) • comboLin K p.rep ℓ := by
    rw [comboLin_apply, comboLin_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Pi.smul_apply, smul_comm]
  rw [← comboLin_eval]
  rw [← ha, hscale]
  exact smul_ne_zero ha0 hne

/-- An ideal times `⊤` lies in the ideal (used to turn `⊤ = ofList • ⊤`
around in the homogeneous-origin argument).

## References

* `Mathlib/RingTheory/Ideal/Operations.lean`, `Submodule.smul_eq_map₂`;
  `Mathlib/Algebra/Module/Submodule/Bilinear.lean`, `Submodule.map₂_le`;
  `LinearMap.lsmul_apply`; `smul_eq_mul`; `Ideal.mul_mem_left`. -/
theorem ideal_smul_top_le (S : Type*) [CommRing S] (I : Ideal S) :
    I • (⊤ : Submodule S S) ≤ (I : Submodule S S) := by
  rw [Submodule.smul_eq_map₂]
  refine Submodule.map₂_le.mpr ?_
  intro a ha b _
  rw [LinearMap.lsmul_apply]
  have hsm : a • b = a * b := rfl
  rw [hsm]
  exact Ideal.mul_mem_right _ _ ha

/-- Successive-regularity repackaging for the R2 `key` induction (general
`G`): the per-step `IsSMulRegular` outputs (quotients by `Ideal.ofList` of
taken prefix lists — `hreg` for old rows, `hregQ` for the new row)
repackaged into `RegularityBridge.SuccessiveSMulRegular` for the combination
family `q j = comboLin K G (r j)`, via
`AvoidanceApply.hsucc_of_step_outputs` transported along `hcombo`. At
each step `k ≤ n` this supplies the `hsucc` that
`avoid_of_unmixed_hlow` / `avoid_of_hunmixed_ge2` consume, closing the
per-step chain `` `IsSMulRegular` outputs → `SuccessiveSMulRegular q`
→ `hAss` → avoidance → next step's `havoid` ``.

## References

* `AvoidanceApply.hsucc_of_step_outputs` (the `ofList`-to-span repackaging). -/
theorem hsucc_comboLin_of_key_outputs (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (k : ℕ) (r : Fin k → (Fin (n + 1) → K))
    (h : Fin k → MvPolynomial (Fin (n + 2)) K)
    (hcombo : ∀ j, h j = comboLin K G (r j))
    (hreg : ∀ j : Fin k, IsSMulRegular
      (MvPolynomial (Fin (n + 2)) K ⧸ (Ideal.ofList (List.take (j.val) (List.ofFn h)) •
        (⊤ : Submodule (MvPolynomial (Fin (n + 2)) K)
          (MvPolynomial (Fin (n + 2)) K))))
      (h j)) :
    RegularityBridge.SuccessiveSMulRegular (fun j => comboLin K G (r j)) := by
  have hsucc := AvoidanceApply.hsucc_of_step_outputs h hreg
  have heq : h = fun j => comboLin K G (r j) := funext hcombo
  rw [heq] at hsucc
  exact hsucc

/-- R2 (restated): a regular sequence of quadrics after a unit change of
variables, in the polynomial ring.

The specification asks for combinations whose images
in the cone quotient `S = coneQuotient n K G` form a regular sequence — but
every `G j` maps to `0` in `S` (`Ideal.Quotient.mk_eq_zero`), so those images
are all `0` and the avoidance hypothesis is unsatisfiable for nontrivial `S`.
The intended content is stated here instead: a unit
matrix `M` whose `K`-linear combinations `F k = ∑ j, M k j • G j` form a
regular sequence in `MvPolynomial (Fin (n + 2)) K` itself — weak regularity on
the successive quotients `R ⧸ (F₀, …, F_{k-1})`, plus `⊤ ≠ span` via the
homogeneous-origin trick (`hG`: every combination vanishes at `0`, so
evaluation at `0` kills the whole span) — with
`Ideal.span (Set.range F) = Ideal.span (Set.range G)` from `IsUnit M` (the
inverse matrix expands each `G i` back out of the combinations).

HilbertFunctionCount over the rows: at each step the previously chosen combinations span
a proper subspace of coefficient space (dimension count via
`finrank_span_finset_le_card`), while regularity on the current module
quotient comes from avoiding `Ass` of that quotient. The avoidance properness
at every intermediate quotient is the hypothesis `havoid` (see module
docstring). Each regular step drops Krull dimension by one
(see `ringKrullDim_quotient_succ_le_of_nonZeroDivisor`).

## References

* `RingTheory.Sequence.isWeaklyRegular_iff`, `RingTheory.Sequence.IsRegular.mk`
  (`Mathlib/RingTheory/Regular/RegularSequence.lean`).
* `Matrix.linearIndependent_rows_iff_isUnit`
  (`Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean`): independent rows
  give the unit matrix.
* `LinearIndependent.finSnoc`, `linearIndependent_empty_type`
  (`Mathlib/LinearAlgebra/LinearIndependent/Lemmas.lean`): row-independence
  bookkeeping.
* `finrank_span_finset_le_card`
  (`Mathlib/LinearAlgebra/Dimension/Constructions.lean`),
  `Module.finrank_pi`: the chosen rows never span.
* `MvPolynomial.IsHomogeneous.coeff_eq_zero`
  (`Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`),
  `MvPolynomial.eval_zero`, `MvPolynomial.constantCoeff_eq`: evaluation at `0`.
* `biUnion_associatedPrimes_eq_zero_divisors` (via `regular_of_avoid` above),
  `associatedPrimes.finite`: regularity from `Ass`-avoidance.
* `Appendix_FixedPoint.BezoutChain.not_covered_by_proper_submodules`
  (`EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GenericLinear`, via `exists_avoiding_coeff`
  above): the parallel-avoidance engine.
* `Units.inv_mul` (`Mathlib/Algebra/Group/Units/Defs.lean`),
  `Matrix.mul_apply` (`Mathlib/Data/Matrix/Mul.lean`),
  `Matrix.one_apply` (`Mathlib/Data/Matrix/Diagonal.lean`): the
  inverse-matrix span repair.
* `Finset.smul_sum` (`Mathlib/Algebra/BigOperators/GroupWithZero/Action.lean`),
  `Finset.sum_smul` (`Mathlib/Algebra/Module/BigOperators.lean`), `mul_smul`
  (`Mathlib/Algebra/Group/Action/Defs.lean`): the double-sum swap.
* `MvPolynomial.smul_eq_C_mul` (`Mathlib/Algebra/MvPolynomial/Basic.lean`):
  ideal membership of `K`-scalar multiples. -/
theorem exists_regular_quadrics (n : ℕ) (K : Type*) [Field K] [IsAlgClosed K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hG : ∀ i, (G i).IsHomogeneous 2)
    (hZd : IsZeroDimensional n K G)
    (havoid : ∀ (J : Submodule (MvPolynomial (Fin (n + 2)) K)
          (MvPolynomial (Fin (n + 2)) K)),
      J ≤ (Ideal.span (Set.range G) :
        Submodule (MvPolynomial (Fin (n + 2)) K)
          (MvPolynomial (Fin (n + 2)) K)) →
      ∀ P ∈ associatedPrimes (MvPolynomial (Fin (n + 2)) K)
          ((MvPolynomial (Fin (n + 2)) K) ⧸ J),
        Submodule.comap (comboLin K G)
          (Submodule.restrictScalars K
            (P : Submodule (MvPolynomial (Fin (n + 2)) K)
              (MvPolynomial (Fin (n + 2)) K))) ≠ ⊤) :
    ∃ M : Matrix (Fin (n + 1)) (Fin (n + 1)) K, IsUnit M ∧
      RingTheory.Sequence.IsRegular (MvPolynomial (Fin (n + 2)) K)
        (List.ofFn fun k => ∑ j, M k j • G j) ∧
      Ideal.span (Set.range fun k => ∑ j, M k j • G j)
        = Ideal.span (Set.range G) := by
  classical
  have heval0 : ∀ i, MvPolynomial.eval (0 : Fin (n + 2) → K) (G i) = 0 := by
    intro i
    have h1 : MvPolynomial.eval (0 : Fin (n + 2) → K) (G i)
        = MvPolynomial.constantCoeff (G i) :=
      congrFun (congrArg DFunLike.coe MvPolynomial.eval_zero) (G i)
    rw [h1, MvPolynomial.constantCoeff_eq]
    exact MvPolynomial.IsHomogeneous.coeff_eq_zero (hG i) (by
      have hdeg : (0 : Fin (n + 2) →₀ ℕ).degree = 0 := by simp [Finsupp.degree]
      omega)
  have hcombo0 : ∀ c : Fin (n + 1) → K,
      MvPolynomial.eval (0 : Fin (n + 2) → K) (comboLin K G c) = 0 := by
    intro c
    rw [comboLin_apply, map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, heval0 j,
      mul_zero]
  have key : ∀ k : ℕ, k ≤ n + 1 →
      ∃ (r : Fin k → (Fin (n + 1) → K))
        (h : Fin k → MvPolynomial (Fin (n + 2)) K),
        LinearIndependent K r ∧
        (∀ j, h j = comboLin K G (r j)) ∧
        (∀ j : Fin k, IsSMulRegular
          (MvPolynomial (Fin (n + 2)) K ⧸ (Ideal.ofList (List.take (j : ℕ) (List.ofFn h))
            • (⊤ : Submodule (MvPolynomial (Fin (n + 2)) K)
                (MvPolynomial (Fin (n + 2)) K))))
          (h j)) := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨fun j : Fin 0 => j.elim0, fun j : Fin 0 => j.elim0,
        linearIndependent_empty_type, fun j => j.elim0, fun j => j.elim0⟩
    | succ k ih =>
      intro hk
      have hk' : k ≤ n + 1 := le_trans (Nat.le_succ k) hk
      obtain ⟨r, h, hindep, hcombo, hreg⟩ := ih hk'
      have hmono : Ideal.ofList (List.ofFn h)
          ≤ Ideal.span (Set.range G) := by
        refine Ideal.span_le.mpr (fun x hx => ?_)
        simp only [Set.mem_ofPred_eq, List.mem_ofFn] at hx
        obtain ⟨j, rfl⟩ := hx
        rw [hcombo j, comboLin_apply]
        refine Ideal.sum_mem _ (fun l _ => ?_)
        rw [MvPolynomial.smul_eq_C_mul]
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨l, rfl⟩)
      have hJle : (Ideal.ofList (List.ofFn h)
          • (⊤ : Submodule (MvPolynomial (Fin (n + 2)) K)
              (MvPolynomial (Fin (n + 2)) K)))
          ≤ (Ideal.span (Set.range G) :
            Submodule (MvPolynomial (Fin (n + 2)) K)
              (MvPolynomial (Fin (n + 2)) K)) :=
        le_trans (ideal_smul_top_le _ _) (fun x hx => hmono hx)
      have hAssFin := associatedPrimes.finite (MvPolynomial (Fin (n + 2)) K)
        ((MvPolynomial (Fin (n + 2)) K) ⧸ (Ideal.ofList (List.ofFn h)
          • (⊤ : Submodule (MvPolynomial (Fin (n + 2)) K)
              (MvPolynomial (Fin (n + 2)) K))))
      obtain ⟨c, hc⟩ := exists_avoiding_coeff K
        ({Submodule.span K (Set.range r)} ∪ hAssFin.toFinset.image
          (fun P => Submodule.comap (comboLin K G)
            (Submodule.restrictScalars K
              (P : Submodule (MvPolynomial (Fin (n + 2)) K)
                (MvPolynomial (Fin (n + 2)) K)))))
        (by
          intro w hw
          rw [Finset.mem_union, Finset.mem_singleton] at hw
          rcases hw with rfl | hcomap
          · intro htop
            have hfin : Module.finrank K (Fin (n + 1) → K) = n + 1 := by
              rw [Module.finrank_pi, Fintype.card_fin]
            have hle : Set.finrank K (Set.range r) ≤ k := by
              have h1 := finrank_span_finset_le_card (R := K) (Finset.univ.image r)
              rw [show (↑(Finset.univ.image r) : Set (Fin (n + 1) → K))
                  = Set.range r from by
                rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]] at h1
              exact le_trans h1
                (le_trans Finset.card_image_le (by simp))
            have hcon : Set.finrank K (Set.range r)
                = Module.finrank K (Fin (n + 1) → K) := by
              unfold Set.finrank
              rw [htop]
              exact Submodule.topEquiv.finrank_eq
            omega
          · obtain ⟨P, hPmem, rfl⟩ := Finset.mem_image.mp hcomap
            -- `hZd` is threaded to this avoidance-application point so the
            -- `AvoidanceApply.avoid_of_unmixed_hlow` recipe's `hZd` requirement
            -- is supplied by the R2 argument (`hsucc`/`hunmixed`/`hlow` stay open).
            have _hZd_recipe : IsZeroDimensional n K G := hZd
            exact havoid _ hJle P
              ((Set.Finite.mem_toFinset hAssFin).mp hPmem))
      have hc_span : c ∉ Submodule.span K (Set.range r) :=
        hc _ (Finset.mem_union_left _ (Finset.mem_singleton_self _))
      have hregQ : IsSMulRegular
          ((MvPolynomial (Fin (n + 2)) K) ⧸ (Ideal.ofList (List.ofFn h)
            • (⊤ : Submodule (MvPolynomial (Fin (n + 2)) K)
                (MvPolynomial (Fin (n + 2)) K))))
          (comboLin K G c) := by
        refine regular_of_avoid (MvPolynomial (Fin (n + 2)) K) _ _ ?_
        intro P hP hm
        have hmem : c ∈ Submodule.comap (comboLin K G)
            (Submodule.restrictScalars K
              (P : Submodule (MvPolynomial (Fin (n + 2)) K)
                (MvPolynomial (Fin (n + 2)) K))) :=
          Submodule.mem_comap.mpr hm
        exact hc _ (Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨P, (Set.Finite.mem_toFinset hAssFin).mpr hP, rfl⟩)) hmem
      have hlast : ∀ (j : Fin (k + 1)), ¬ (j : ℕ) < k → j = Fin.last k := by
        intro j hj
        rw [Fin.ext_iff, Fin.val_last]
        have hlt2 := j.isLt
        omega
      have hoFn : List.ofFn (Fin.snoc h (comboLin K G c))
          = List.ofFn h ++ [comboLin K G c] := by
        rw [List.ofFn_succ', ← List.concat_eq_append]
        congr 1
        · exact congrArg List.ofFn (funext fun i => Fin.snoc_castSucc _ _ _)
        · exact Fin.snoc_last _ _
      have htake : ∀ (i : ℕ), i ≤ k →
          List.take i (List.ofFn (Fin.snoc h (comboLin K G c)))
            = List.take i (List.ofFn h) := by
        intro i hi
        rw [hoFn, List.take_append_of_le_length (by rwa [List.length_ofFn])]
      have htake_last :
          List.take k (List.ofFn (Fin.snoc h (comboLin K G c)))
            = List.ofFn h := by
        have hlen : (List.ofFn h).length = k := List.length_ofFn
        rw [hoFn, List.take_append_of_le_length hlen.ge]
        have h2 : List.take k (List.ofFn h)
            = List.take (List.ofFn h).length (List.ofFn h) := by
          rw [hlen]
        rw [h2]
        exact List.take_length
      refine ⟨Fin.snoc r c, Fin.snoc h (comboLin K G c),
        LinearIndependent.finSnoc hindep hc_span, ?_, ?_⟩
      · intro j
        by_cases hj : (j : ℕ) < k
        · have hj' : j = Fin.castSucc ⟨(j : ℕ), hj⟩ := Fin.ext rfl
          rw [hj', Fin.snoc_castSucc, Fin.snoc_castSucc]
          exact hcombo _
        · rw [hlast j hj, Fin.snoc_last, Fin.snoc_last]
      · intro j
        by_cases hj : (j : ℕ) < k
        · rw [htake (j : ℕ) (le_of_lt hj)]
          have hj' : j = Fin.castSucc ⟨(j : ℕ), hj⟩ := Fin.ext rfl
          rw [hj', Fin.snoc_castSucc]
          exact hreg ⟨(j : ℕ), hj⟩
        · rw [hlast j hj, Fin.snoc_last, Fin.val_last, htake_last]
          exact hregQ
  obtain ⟨r, h, hindep, hcombo, hreg⟩ := key (n + 1) le_rfl
  have hrow : (Matrix.of r).row = r := by
    funext i j
    exact Matrix.of_apply r i j
  have hfun : (fun k => ∑ j, Matrix.of r k j • G j) = h := by
    funext k
    rw [hcombo k, comboLin_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.of_apply]
  have hmonoFull : Ideal.span (Set.range h) ≤ Ideal.span (Set.range G) := by
    refine Ideal.span_le.mpr (fun x hx => ?_)
    obtain ⟨k, rfl⟩ := hx
    rw [hcombo k, comboLin_apply]
    refine Ideal.sum_mem _ (fun l _ => ?_)
    rw [MvPolynomial.smul_eq_C_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨l, rfl⟩)
  obtain ⟨N, hNM⟩ : ∃ N : Matrix (Fin (n + 1)) (Fin (n + 1)) K,
      N * Matrix.of r = 1 := by
    obtain ⟨u, hu⟩ := Matrix.linearIndependent_rows_iff_isUnit.mp (by
      rw [hrow]
      exact hindep)
    exact ⟨↑u⁻¹, by rw [← hu]; exact Units.inv_mul u⟩
  have hexpand : ∀ i, G i = ∑ k, N i k • h k := by
    intro i
    have hsum : ∀ j, (∑ k, N i k * Matrix.of r k j)
        = (if i = j then (1 : K) else 0) := by
      intro j
      rw [← Matrix.mul_apply, hNM]
      exact Matrix.one_apply (n := Fin (n + 1)) (α := K) (i := i) (j := j)
    have e1 : ∀ k, N i k • h k
        = ∑ j, (N i k * Matrix.of r k j) • G j := by
      intro k
      rw [hcombo k, comboLin_apply, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_smul, Matrix.of_apply]
    calc G i = ∑ j, (if i = j then (1 : K) else 0) • G j := by
            have hss := Finset.sum_eq_single (s := Finset.univ)
              (f := fun j => (if i = j then (1 : K) else 0) • G j) i
              (fun j _ hji => by rw [ite_eq_right (fun h => hji h.symm), zero_smul])
              (fun hcon => absurd (Finset.mem_univ i) hcon)
            rw [ite_eq_left (show i = i from rfl), one_smul] at hss
            exact hss.symm
      _ = ∑ k, N i k • h k := by
            simp only [e1]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro j _
            rw [← Finset.sum_smul, hsum j]
  refine ⟨Matrix.of r, ?_, ?_, ?_⟩
  · exact Matrix.linearIndependent_rows_iff_isUnit.mp (by
      rw [hrow]
      exact hindep)
  · rw [hfun]
    refine RingTheory.Sequence.IsRegular.mk ?_ ?_
    · rw [RingTheory.Sequence.isWeaklyRegular_iff]
      intro i hi
      simp only [List.length_ofFn] at hi
      simp only [List.getElem_ofFn]
      exact hreg ⟨i, hi⟩
    · intro htop
      have h1 : (1 : MvPolynomial (Fin (n + 2)) K) ∈ Ideal.ofList (List.ofFn h)
          • (⊤ : Submodule (MvPolynomial (Fin (n + 2)) K)
              (MvPolynomial (Fin (n + 2)) K)) :=
        htop ▸ Submodule.mem_top
      have hmem1 : (1 : MvPolynomial (Fin (n + 2)) K)
          ∈ Ideal.ofList (List.ofFn h) :=
        ideal_smul_top_le _ _ h1
      have hle : Ideal.ofList (List.ofFn h)
          ≤ RingHom.ker (MvPolynomial.eval (0 : Fin (n + 2) → K)) := by
        refine Ideal.span_le.mpr (fun x hx => ?_)
        simp only [Set.mem_ofPred_eq, List.mem_ofFn] at hx
        obtain ⟨j, rfl⟩ := hx
        exact RingHom.mem_ker.mpr (by rw [hcombo j]; exact hcombo0 _)
      have hE1 : MvPolynomial.eval (0 : Fin (n + 2) → K) 1 = 0 :=
        RingHom.mem_ker.mp (hle hmem1)
      have hE1' : MvPolynomial.eval (0 : Fin (n + 2) → K) 1 = 1 := map_one _
      rw [hE1] at hE1'
      exact one_ne_zero hE1'.symm
  · rw [hfun]
    apply le_antisymm
    · exact hmonoFull
    · refine Ideal.span_le.mpr (fun x hx => ?_)
      obtain ⟨i, rfl⟩ := hx
      rw [hexpand i]
      refine Ideal.sum_mem _ (fun k _ => ?_)
      rw [MvPolynomial.smul_eq_C_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k, rfl⟩)

/-- R2 at `mkSystem`, conditional on `hunmixed`-at-`k ≥ 2` only.

Specialization of `exists_regular_quadrics` to `G = mkSystem n K F` in which
the per-step avoidance properness (`havoid`) is discharged by the narrowed
chain instead of taken as hypothesis:

* homogeneity comes from `mkSystem_homogeneous` (needs `hF`);
* step `k = 0` via the domain step
  (`AvoidanceApply.comap_ne_top_zero_of_t1`: t1-style `Gᵢ ≠ 0`, no `hZd`,
  no `hlow`, no unmixedness);
* steps `k ≥ 1` via `AvoidanceApply.comap_ne_top_of_step` (proved `k ≤ 1`
  unmixedness internally, explicit `hunmixed_ge2` at `k ≥ 2`), with `hsucc`
  repackaged from the step outputs
  (`AvoidanceApply.hsucc_of_step_outputs`).

Steps `k = 0, 1` need no unmixedness hypothesis; the only unmixedness demand
left is the explicit `hunmixed_ge2` (plus the step-independent catenary
`hlow`). The t2a/t2b dichotomy inputs are not needed here (generic rows);
they supply `hsucc` for the generator pair instead
(`AvoidanceApply.hsucc_mkSystem_pair_of_dichotomy`). No t3 content.

## References

* `exists_regular_quadrics` above (proof copied, `havoid` replaced).
* `mkSystem_homogeneous` (`Statement/Statement.lean`).
* `AvoidanceApply.comap_ne_top_zero_of_t1`,
  `AvoidanceApply.hsucc_of_step_outputs`,
  `AvoidanceApply.comap_ne_top_of_step`.
* (all other references as in `exists_regular_quadrics`). -/
theorem exists_regular_quadrics_mkSystem (n : ℕ) (K : Type*) [Field K]
    [IsAlgClosed K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2)
    (hZd : IsZeroDimensional n K (mkSystem n K F))
    (hlow : ∀ (P : Ideal (MvPolynomial (Fin (n + 2)) K)) [P.IsPrime],
      Ideal.span (Set.range (mkSystem n K F)) ≤ P →
      ((((n + 2 : ℕ))) : WithBot ℕ∞) ≤
        (P.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial (Fin (n + 2)) K ⧸ P))
    (hunmixed_ge2 : ∀ (k : ℕ), 2 ≤ k →
      ∀ (q : Fin k → MvPolynomial (Fin (n + 2)) K)
      (_hsucc : RegularityBridge.SuccessiveSMulRegular q)
      (J : Ideal (MvPolynomial (Fin (n + 2)) K))
      (_hJ : J = Ideal.span (Set.range q)),
      ∀ P ∈ associatedPrimes (MvPolynomial (Fin (n + 2)) K)
        (MvPolynomial (Fin (n + 2)) K ⧸ J), P ∈ J.minimalPrimes) :
    ∃ M : Matrix (Fin (n + 1)) (Fin (n + 1)) K, IsUnit M ∧
      RingTheory.Sequence.IsRegular (MvPolynomial (Fin (n + 2)) K)
        (List.ofFn fun k => ∑ j, M k j • mkSystem n K F j) ∧
      Ideal.span (Set.range fun k => ∑ j, M k j • mkSystem n K F j)
        = Ideal.span (Set.range (mkSystem n K F)) := by
  classical
  have hG : ∀ i, ((mkSystem n K F) i).IsHomogeneous 2 :=
    mkSystem_homogeneous n K F hF
  have heval0 : ∀ i, MvPolynomial.eval (0 : Fin (n + 2) → K) (mkSystem n K F i)
      = 0 := by
    intro i
    have h1 : MvPolynomial.eval (0 : Fin (n + 2) → K) (mkSystem n K F i)
        = MvPolynomial.constantCoeff (mkSystem n K F i) :=
      congrFun (congrArg DFunLike.coe MvPolynomial.eval_zero) (mkSystem n K F i)
    rw [h1, MvPolynomial.constantCoeff_eq]
    exact MvPolynomial.IsHomogeneous.coeff_eq_zero (hG i) (by
      have hdeg : (0 : Fin (n + 2) →₀ ℕ).degree = 0 := by simp [Finsupp.degree]
      omega)
  have hcombo0 : ∀ c : Fin (n + 1) → K,
      MvPolynomial.eval (0 : Fin (n + 2) → K)
        (comboLin K (mkSystem n K F) c) = 0 := by
    intro c
    rw [comboLin_apply, map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, heval0 j,
      mul_zero]
  have key : ∀ k : ℕ, k ≤ n + 1 →
      ∃ (r : Fin k → (Fin (n + 1) → K))
        (h : Fin k → MvPolynomial (Fin (n + 2)) K),
        LinearIndependent K r ∧
        (∀ j, h j = comboLin K (mkSystem n K F) (r j)) ∧
        (∀ j : Fin k, IsSMulRegular
          (MvPolynomial (Fin (n + 2)) K ⧸ (Ideal.ofList (List.take (j : ℕ) (List.ofFn h))
            • (⊤ : Submodule (MvPolynomial (Fin (n + 2)) K)
                (MvPolynomial (Fin (n + 2)) K))))
          (h j)) := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨fun j : Fin 0 => j.elim0, fun j : Fin 0 => j.elim0,
        linearIndependent_empty_type, fun j => j.elim0, fun j => j.elim0⟩
    | succ k ih =>
      intro hk
      have hk' : k ≤ n + 1 := le_trans (Nat.le_succ k) hk
      obtain ⟨r, h, hindep, hcombo, hreg⟩ := ih hk'
      have hAssFin := associatedPrimes.finite (MvPolynomial (Fin (n + 2)) K)
        ((MvPolynomial (Fin (n + 2)) K) ⧸ (Ideal.ofList (List.ofFn h)
          • (⊤ : Submodule (MvPolynomial (Fin (n + 2)) K)
              (MvPolynomial (Fin (n + 2)) K))))
      obtain ⟨c, hc⟩ := exists_avoiding_coeff K
        ({Submodule.span K (Set.range r)} ∪ hAssFin.toFinset.image
          (fun P => Submodule.comap (comboLin K (mkSystem n K F))
            (Submodule.restrictScalars K
              (P : Submodule (MvPolynomial (Fin (n + 2)) K)
                (MvPolynomial (Fin (n + 2)) K)))))
        (by
          intro w hw
          rw [Finset.mem_union, Finset.mem_singleton] at hw
          rcases hw with rfl | hcomap
          · intro htop
            have hfin : Module.finrank K (Fin (n + 1) → K) = n + 1 := by
              rw [Module.finrank_pi, Fintype.card_fin]
            have hle : Set.finrank K (Set.range r) ≤ k := by
              have h1 := finrank_span_finset_le_card (R := K) (Finset.univ.image r)
              rw [show (↑(Finset.univ.image r) : Set (Fin (n + 1) → K))
                  = Set.range r from by
                rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]] at h1
              exact le_trans h1
                (le_trans Finset.card_image_le (by simp))
            have hcon : Set.finrank K (Set.range r)
                = Module.finrank K (Fin (n + 1) → K) := by
              unfold Set.finrank
              rw [htop]
              exact Submodule.topEquiv.finrank_eq
            omega
          · obtain ⟨P, hPmem, rfl⟩ := Finset.mem_image.mp hcomap
            have hPm := (Set.Finite.mem_toFinset hAssFin).mp hPmem
            by_cases h0k : k = 0
            · subst h0k
              exact AvoidanceApply.comap_ne_top_zero_of_t1 n K F h P hPm
            · have hkStep : k ≤ n := by omega
              have hsuccStep :=
                AvoidanceApply.hsucc_of_step_outputs h hreg
              exact AvoidanceApply.comap_ne_top_of_step n K _ hZd k hkStep h
                hsuccStep hlow (hunmixed_ge2 k) P hPm)
      have hc_span : c ∉ Submodule.span K (Set.range r) :=
        hc _ (Finset.mem_union_left _ (Finset.mem_singleton_self _))
      have hregQ : IsSMulRegular
          ((MvPolynomial (Fin (n + 2)) K) ⧸ (Ideal.ofList (List.ofFn h)
            • (⊤ : Submodule (MvPolynomial (Fin (n + 2)) K)
                (MvPolynomial (Fin (n + 2)) K))))
          (comboLin K (mkSystem n K F) c) := by
        refine regular_of_avoid (MvPolynomial (Fin (n + 2)) K) _ _ ?_
        intro P hP hm
        have hmem : c ∈ Submodule.comap (comboLin K (mkSystem n K F))
            (Submodule.restrictScalars K
              (P : Submodule (MvPolynomial (Fin (n + 2)) K)
                (MvPolynomial (Fin (n + 2)) K))) :=
          Submodule.mem_comap.mpr hm
        exact hc _ (Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨P, (Set.Finite.mem_toFinset hAssFin).mpr hP, rfl⟩)) hmem
      have hlast : ∀ (j : Fin (k + 1)), ¬ (j : ℕ) < k → j = Fin.last k := by
        intro j hj
        rw [Fin.ext_iff, Fin.val_last]
        have hlt2 := j.isLt
        omega
      have hoFn : List.ofFn (Fin.snoc h (comboLin K (mkSystem n K F) c))
          = List.ofFn h ++ [comboLin K (mkSystem n K F) c] := by
        rw [List.ofFn_succ', ← List.concat_eq_append]
        congr 1
        · exact congrArg List.ofFn (funext fun i => Fin.snoc_castSucc _ _ _)
        · exact Fin.snoc_last _ _
      have htake : ∀ (i : ℕ), i ≤ k →
          List.take i (List.ofFn (Fin.snoc h (comboLin K (mkSystem n K F) c)))
            = List.take i (List.ofFn h) := by
        intro i hi
        rw [hoFn, List.take_append_of_le_length (by rwa [List.length_ofFn])]
      have htake_last :
          List.take k (List.ofFn (Fin.snoc h (comboLin K (mkSystem n K F) c)))
            = List.ofFn h := by
        have hlen : (List.ofFn h).length = k := List.length_ofFn
        rw [hoFn, List.take_append_of_le_length hlen.ge]
        have h2 : List.take k (List.ofFn h)
            = List.take (List.ofFn h).length (List.ofFn h) := by
          rw [hlen]
        rw [h2]
        exact List.take_length
      refine ⟨Fin.snoc r c, Fin.snoc h (comboLin K (mkSystem n K F) c),
        LinearIndependent.finSnoc hindep hc_span, ?_, ?_⟩
      · intro j
        by_cases hj : (j : ℕ) < k
        · have hj' : j = Fin.castSucc ⟨(j : ℕ), hj⟩ := Fin.ext rfl
          rw [hj', Fin.snoc_castSucc, Fin.snoc_castSucc]
          exact hcombo _
        · rw [hlast j hj, Fin.snoc_last, Fin.snoc_last]
      · intro j
        by_cases hj : (j : ℕ) < k
        · rw [htake (j : ℕ) (le_of_lt hj)]
          have hj' : j = Fin.castSucc ⟨(j : ℕ), hj⟩ := Fin.ext rfl
          rw [hj', Fin.snoc_castSucc]
          exact hreg ⟨(j : ℕ), hj⟩
        · rw [hlast j hj, Fin.snoc_last, Fin.val_last, htake_last]
          exact hregQ
  obtain ⟨r, h, hindep, hcombo, hreg⟩ := key (n + 1) le_rfl
  have hrow : (Matrix.of r).row = r := by
    funext i j
    exact Matrix.of_apply r i j
  have hfun : (fun k => ∑ j, Matrix.of r k j • mkSystem n K F j) = h := by
    funext k
    rw [hcombo k, comboLin_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.of_apply]
  have hmonoFull : Ideal.span (Set.range h) ≤
      Ideal.span (Set.range (mkSystem n K F)) := by
    refine Ideal.span_le.mpr (fun x hx => ?_)
    obtain ⟨k, rfl⟩ := hx
    rw [hcombo k, comboLin_apply]
    refine Ideal.sum_mem _ (fun l _ => ?_)
    rw [MvPolynomial.smul_eq_C_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨l, rfl⟩)
  obtain ⟨N, hNM⟩ : ∃ N : Matrix (Fin (n + 1)) (Fin (n + 1)) K,
      N * Matrix.of r = 1 := by
    obtain ⟨u, hu⟩ := Matrix.linearIndependent_rows_iff_isUnit.mp (by
      rw [hrow]
      exact hindep)
    exact ⟨↑u⁻¹, by rw [← hu]; exact Units.inv_mul u⟩
  have hexpand : ∀ i, mkSystem n K F i = ∑ k, N i k • h k := by
    intro i
    have hsum : ∀ j, (∑ k, N i k * Matrix.of r k j)
        = (if i = j then (1 : K) else 0) := by
      intro j
      rw [← Matrix.mul_apply, hNM]
      exact Matrix.one_apply (n := Fin (n + 1)) (α := K) (i := i) (j := j)
    have e1 : ∀ k, N i k • h k
        = ∑ j, (N i k * Matrix.of r k j) • mkSystem n K F j := by
      intro k
      rw [hcombo k, comboLin_apply, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_smul, Matrix.of_apply]
    calc mkSystem n K F i
        = ∑ j, (if i = j then (1 : K) else 0) • mkSystem n K F j := by
            have hss := Finset.sum_eq_single (s := Finset.univ)
              (f := fun j => (if i = j then (1 : K) else 0) • mkSystem n K F j) i
              (fun j _ hji => by rw [ite_eq_right (fun h => hji h.symm), zero_smul])
              (fun hcon => absurd (Finset.mem_univ i) hcon)
            rw [ite_eq_left (show i = i from rfl), one_smul] at hss
            exact hss.symm
      _ = ∑ k, N i k • h k := by
            simp only [e1]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro j _
            rw [← Finset.sum_smul, hsum j]
  refine ⟨Matrix.of r, ?_, ?_, ?_⟩
  · exact Matrix.linearIndependent_rows_iff_isUnit.mp (by
      rw [hrow]
      exact hindep)
  · rw [hfun]
    refine RingTheory.Sequence.IsRegular.mk ?_ ?_
    · rw [RingTheory.Sequence.isWeaklyRegular_iff]
      intro i hi
      simp only [List.length_ofFn] at hi
      simp only [List.getElem_ofFn]
      exact hreg ⟨i, hi⟩
    · intro htop
      have h1 : (1 : MvPolynomial (Fin (n + 2)) K) ∈ Ideal.ofList (List.ofFn h)
          • (⊤ : Submodule (MvPolynomial (Fin (n + 2)) K)
              (MvPolynomial (Fin (n + 2)) K)) :=
        htop ▸ Submodule.mem_top
      have hmem1 : (1 : MvPolynomial (Fin (n + 2)) K)
          ∈ Ideal.ofList (List.ofFn h) :=
        ideal_smul_top_le _ _ h1
      have hle : Ideal.ofList (List.ofFn h)
          ≤ RingHom.ker (MvPolynomial.eval (0 : Fin (n + 2) → K)) := by
        refine Ideal.span_le.mpr (fun x hx => ?_)
        simp only [Set.mem_ofPred_eq, List.mem_ofFn] at hx
        obtain ⟨j, rfl⟩ := hx
        exact RingHom.mem_ker.mpr (by rw [hcombo j]; exact hcombo0 _)
      have hE1 : MvPolynomial.eval (0 : Fin (n + 2) → K) 1 = 0 :=
        RingHom.mem_ker.mp (hle hmem1)
      have hE1' : MvPolynomial.eval (0 : Fin (n + 2) → K) 1 = 1 := map_one _
      rw [hE1] at hE1'
      exact one_ne_zero hE1'.symm
  · rw [hfun]
    apply le_antisymm
    · exact hmonoFull
    · refine Ideal.span_le.mpr (fun x hx => ?_)
      obtain ⟨i, rfl⟩ := hx
      rw [hexpand i]
      refine Ideal.sum_mem _ (fun k _ => ?_)
      rw [MvPolynomial.smul_eq_C_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k, rfl⟩)

/-! ## General conditional R2 + `hSES`/`hSEC` feed

`exists_regular_quadrics_of_unmixed_hlow` is R2 for general `G` with the
per-step avoidance properness (`havoid`) discharged by the narrowed chain
instead of taken as hypothesis: step `k = 0` via the general domain step
(`AvoidanceApply.comap_ne_top_zero_general`: `noAssPrime_contains_span_zero`
+ `hZd`, no `hlow`, no unmixedness), steps `k ≥ 1` via
`AvoidanceApply.comap_ne_top_of_step` (proved `k ≤ 1` unmixedness
internally, explicit `hunmixed_ge2` at `k ≥ 2`), with `hsucc` repackaged
from the step outputs (`AvoidanceApply.hsucc_of_step_outputs`, in
`comboLin` form `hsucc_comboLin_of_key_outputs` above).

Exact hypothesis list: `hG` (homogeneity — the origin trick for
`top_ne_smul`), `hZd`, step-independent catenary `hlow`, and `hunmixed_ge2`
(minimality over `J` for `2 ≤ k`). Steps `k = 0, 1` need no unmixedness
hypothesis.

`hSES_of_ses_data` / `hSEC_of_ses_data` package per-`(k, d)` SES data
(injective `K`-linear `f` + cokernel identification `e`, the exact inputs
of `HilbertFunctionCount.graded_piece_ses`, itself `Elimination.ses_finrank_add`) into
the exact per-instance `hSES` / `hSEC` recurrence shapes consumed by
`HilbertFunctionCount.length_section_eq_two_pow`; the consumer assembles the
`∀ k, k < n + 1 → ∀ d, …` / `∀ d, …` binders by applying these per
instance. The SES data itself (regularity ⇒ injectivity + the cokernel
identification, read-only here — sourced from downstream hypotheses,
never imported) stays an explicit hypothesis —
never silently dropped. -/

/-- R2 for general `G`, conditional on `hunmixed`-at-`k ≥ 2` (+ `hlow`) only.

Specialization-free form of `exists_regular_quadrics`: the per-step
avoidance properness (`havoid`) is discharged by the narrowed chain
instead of taken as hypothesis:

* step `k = 0` via the general domain step
  (`AvoidanceApply.comap_ne_top_zero_general`: `noAssPrime_contains_span_zero`
  from `hZd`, no `hlow`, no unmixedness);
* steps `k ≥ 1` via `AvoidanceApply.comap_ne_top_of_step` (proved `k ≤ 1`
  unmixedness internally, explicit `hunmixed_ge2` at `k ≥ 2`), with `hsucc`
  repackaged from the step outputs
  (`AvoidanceApply.hsucc_of_step_outputs`).

Steps `k = 0, 1` need no unmixedness hypothesis; the only unmixedness
demand left is the explicit `hunmixed_ge2` (plus the step-independent
catenary `hlow`).

## References

* `exists_regular_quadrics` above (proof copied, `havoid` replaced).
* `AvoidanceApply.comap_ne_top_zero_general`,
  `AvoidanceApply.hsucc_of_step_outputs`,
  `AvoidanceApply.comap_ne_top_of_step`.
* (all other references as in `exists_regular_quadrics`). -/
theorem exists_regular_quadrics_of_unmixed_hlow (n : ℕ) (K : Type*) [Field K]
    [IsAlgClosed K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hG : ∀ i, (G i).IsHomogeneous 2)
    (hZd : IsZeroDimensional n K G)
    (hlow : ∀ (P : Ideal (MvPolynomial (Fin (n + 2)) K)) [P.IsPrime],
      Ideal.span (Set.range G) ≤ P →
      ((((n + 2 : ℕ))) : WithBot ℕ∞) ≤
        (P.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial (Fin (n + 2)) K ⧸ P))
    (hunmixed_ge2 : ∀ (k : ℕ), 2 ≤ k →
      ∀ (q : Fin k → MvPolynomial (Fin (n + 2)) K)
      (_hsucc : RegularityBridge.SuccessiveSMulRegular q)
      (J : Ideal (MvPolynomial (Fin (n + 2)) K))
      (_hJ : J = Ideal.span (Set.range q)),
      ∀ P ∈ associatedPrimes (MvPolynomial (Fin (n + 2)) K)
        (MvPolynomial (Fin (n + 2)) K ⧸ J), P ∈ J.minimalPrimes) :
    ∃ M : Matrix (Fin (n + 1)) (Fin (n + 1)) K, IsUnit M ∧
      RingTheory.Sequence.IsRegular (MvPolynomial (Fin (n + 2)) K)
        (List.ofFn fun k => ∑ j, M k j • G j) ∧
      Ideal.span (Set.range fun k => ∑ j, M k j • G j)
        = Ideal.span (Set.range G) := by
  classical
  have heval0 : ∀ i, MvPolynomial.eval (0 : Fin (n + 2) → K) (G i) = 0 := by
    intro i
    have h1 : MvPolynomial.eval (0 : Fin (n + 2) → K) (G i)
        = MvPolynomial.constantCoeff (G i) :=
      congrFun (congrArg DFunLike.coe MvPolynomial.eval_zero) (G i)
    rw [h1, MvPolynomial.constantCoeff_eq]
    exact MvPolynomial.IsHomogeneous.coeff_eq_zero (hG i) (by
      have hdeg : (0 : Fin (n + 2) →₀ ℕ).degree = 0 := by simp [Finsupp.degree]
      omega)
  have hcombo0 : ∀ c : Fin (n + 1) → K,
      MvPolynomial.eval (0 : Fin (n + 2) → K) (comboLin K G c) = 0 := by
    intro c
    rw [comboLin_apply, map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, heval0 j,
      mul_zero]
  have key : ∀ k : ℕ, k ≤ n + 1 →
      ∃ (r : Fin k → (Fin (n + 1) → K))
        (h : Fin k → MvPolynomial (Fin (n + 2)) K),
        LinearIndependent K r ∧
        (∀ j, h j = comboLin K G (r j)) ∧
        (∀ j : Fin k, IsSMulRegular
          (MvPolynomial (Fin (n + 2)) K ⧸ (Ideal.ofList (List.take (j : ℕ) (List.ofFn h))
            • (⊤ : Submodule (MvPolynomial (Fin (n + 2)) K)
                (MvPolynomial (Fin (n + 2)) K))))
          (h j)) := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨fun j : Fin 0 => j.elim0, fun j : Fin 0 => j.elim0,
        linearIndependent_empty_type, fun j => j.elim0, fun j => j.elim0⟩
    | succ k ih =>
      intro hk
      have hk' : k ≤ n + 1 := le_trans (Nat.le_succ k) hk
      obtain ⟨r, h, hindep, hcombo, hreg⟩ := ih hk'
      have hAssFin := associatedPrimes.finite (MvPolynomial (Fin (n + 2)) K)
        ((MvPolynomial (Fin (n + 2)) K) ⧸ (Ideal.ofList (List.ofFn h)
          • (⊤ : Submodule (MvPolynomial (Fin (n + 2)) K)
              (MvPolynomial (Fin (n + 2)) K))))
      obtain ⟨c, hc⟩ := exists_avoiding_coeff K
        ({Submodule.span K (Set.range r)} ∪ hAssFin.toFinset.image
          (fun P => Submodule.comap (comboLin K G)
            (Submodule.restrictScalars K
              (P : Submodule (MvPolynomial (Fin (n + 2)) K)
                (MvPolynomial (Fin (n + 2)) K)))))
        (by
          intro w hw
          rw [Finset.mem_union, Finset.mem_singleton] at hw
          rcases hw with rfl | hcomap
          · intro htop
            have hfin : Module.finrank K (Fin (n + 1) → K) = n + 1 := by
              rw [Module.finrank_pi, Fintype.card_fin]
            have hle : Set.finrank K (Set.range r) ≤ k := by
              have h1 := finrank_span_finset_le_card (R := K) (Finset.univ.image r)
              rw [show (↑(Finset.univ.image r) : Set (Fin (n + 1) → K))
                  = Set.range r from by
                rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]] at h1
              exact le_trans h1
                (le_trans Finset.card_image_le (by simp))
            have hcon : Set.finrank K (Set.range r)
                = Module.finrank K (Fin (n + 1) → K) := by
              unfold Set.finrank
              rw [htop]
              exact Submodule.topEquiv.finrank_eq
            omega
          · obtain ⟨P, hPmem, rfl⟩ := Finset.mem_image.mp hcomap
            have hPm := (Set.Finite.mem_toFinset hAssFin).mp hPmem
            by_cases h0k : k = 0
            · subst h0k
              exact AvoidanceApply.comap_ne_top_zero_general n K G hZd h P hPm
            · have hkStep : k ≤ n := by omega
              have hsuccStep :=
                AvoidanceApply.hsucc_of_step_outputs h hreg
              exact AvoidanceApply.comap_ne_top_of_step n K G hZd k hkStep h
                hsuccStep hlow (hunmixed_ge2 k) P hPm)
      have hc_span : c ∉ Submodule.span K (Set.range r) :=
        hc _ (Finset.mem_union_left _ (Finset.mem_singleton_self _))
      have hregQ : IsSMulRegular
          ((MvPolynomial (Fin (n + 2)) K) ⧸ (Ideal.ofList (List.ofFn h)
            • (⊤ : Submodule (MvPolynomial (Fin (n + 2)) K)
                (MvPolynomial (Fin (n + 2)) K))))
          (comboLin K G c) := by
        refine regular_of_avoid (MvPolynomial (Fin (n + 2)) K) _ _ ?_
        intro P hP hm
        have hmem : c ∈ Submodule.comap (comboLin K G)
            (Submodule.restrictScalars K
              (P : Submodule (MvPolynomial (Fin (n + 2)) K)
                (MvPolynomial (Fin (n + 2)) K))) :=
          Submodule.mem_comap.mpr hm
        exact hc _ (Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨P, (Set.Finite.mem_toFinset hAssFin).mpr hP, rfl⟩)) hmem
      have hlast : ∀ (j : Fin (k + 1)), ¬ (j : ℕ) < k → j = Fin.last k := by
        intro j hj
        rw [Fin.ext_iff, Fin.val_last]
        have hlt2 := j.isLt
        omega
      have hoFn : List.ofFn (Fin.snoc h (comboLin K G c))
          = List.ofFn h ++ [comboLin K G c] := by
        rw [List.ofFn_succ', ← List.concat_eq_append]
        congr 1
        · exact congrArg List.ofFn (funext fun i => Fin.snoc_castSucc _ _ _)
        · exact Fin.snoc_last _ _
      have htake : ∀ (i : ℕ), i ≤ k →
          List.take i (List.ofFn (Fin.snoc h (comboLin K G c)))
            = List.take i (List.ofFn h) := by
        intro i hi
        rw [hoFn, List.take_append_of_le_length (by rwa [List.length_ofFn])]
      have htake_last :
          List.take k (List.ofFn (Fin.snoc h (comboLin K G c)))
            = List.ofFn h := by
        have hlen : (List.ofFn h).length = k := List.length_ofFn
        rw [hoFn, List.take_append_of_le_length hlen.ge]
        have h2 : List.take k (List.ofFn h)
            = List.take (List.ofFn h).length (List.ofFn h) := by
          rw [hlen]
        rw [h2]
        exact List.take_length
      refine ⟨Fin.snoc r c, Fin.snoc h (comboLin K G c),
        LinearIndependent.finSnoc hindep hc_span, ?_, ?_⟩
      · intro j
        by_cases hj : (j : ℕ) < k
        · have hj' : j = Fin.castSucc ⟨(j : ℕ), hj⟩ := Fin.ext rfl
          rw [hj', Fin.snoc_castSucc, Fin.snoc_castSucc]
          exact hcombo _
        · rw [hlast j hj, Fin.snoc_last, Fin.snoc_last]
      · intro j
        by_cases hj : (j : ℕ) < k
        · rw [htake (j : ℕ) (le_of_lt hj)]
          have hj' : j = Fin.castSucc ⟨(j : ℕ), hj⟩ := Fin.ext rfl
          rw [hj', Fin.snoc_castSucc]
          exact hreg ⟨(j : ℕ), hj⟩
        · rw [hlast j hj, Fin.snoc_last, Fin.val_last, htake_last]
          exact hregQ
  obtain ⟨r, h, hindep, hcombo, hreg⟩ := key (n + 1) le_rfl
  have hrow : (Matrix.of r).row = r := by
    funext i j
    exact Matrix.of_apply r i j
  have hfun : (fun k => ∑ j, Matrix.of r k j • G j) = h := by
    funext k
    rw [hcombo k, comboLin_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.of_apply]
  have hmonoFull : Ideal.span (Set.range h) ≤ Ideal.span (Set.range G) := by
    refine Ideal.span_le.mpr (fun x hx => ?_)
    obtain ⟨k, rfl⟩ := hx
    rw [hcombo k, comboLin_apply]
    refine Ideal.sum_mem _ (fun l _ => ?_)
    rw [MvPolynomial.smul_eq_C_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨l, rfl⟩)
  obtain ⟨N, hNM⟩ : ∃ N : Matrix (Fin (n + 1)) (Fin (n + 1)) K,
      N * Matrix.of r = 1 := by
    obtain ⟨u, hu⟩ := Matrix.linearIndependent_rows_iff_isUnit.mp (by
      rw [hrow]
      exact hindep)
    exact ⟨↑u⁻¹, by rw [← hu]; exact Units.inv_mul u⟩
  have hexpand : ∀ i, G i = ∑ k, N i k • h k := by
    intro i
    have hsum : ∀ j, (∑ k, N i k * Matrix.of r k j)
        = (if i = j then (1 : K) else 0) := by
      intro j
      rw [← Matrix.mul_apply, hNM]
      exact Matrix.one_apply (n := Fin (n + 1)) (α := K) (i := i) (j := j)
    have e1 : ∀ k, N i k • h k
        = ∑ j, (N i k * Matrix.of r k j) • G j := by
      intro k
      rw [hcombo k, comboLin_apply, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_smul, Matrix.of_apply]
    calc G i = ∑ j, (if i = j then (1 : K) else 0) • G j := by
            have hss := Finset.sum_eq_single (s := Finset.univ)
              (f := fun j => (if i = j then (1 : K) else 0) • G j) i
              (fun j _ hji => by rw [ite_eq_right (fun h => hji h.symm), zero_smul])
              (fun hcon => absurd (Finset.mem_univ i) hcon)
            rw [ite_eq_left (show i = i from rfl), one_smul] at hss
            exact hss.symm
      _ = ∑ k, N i k • h k := by
            simp only [e1]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro j _
            rw [← Finset.sum_smul, hsum j]
  refine ⟨Matrix.of r, ?_, ?_, ?_⟩
  · exact Matrix.linearIndependent_rows_iff_isUnit.mp (by
      rw [hrow]
      exact hindep)
  · rw [hfun]
    refine RingTheory.Sequence.IsRegular.mk ?_ ?_
    · rw [RingTheory.Sequence.isWeaklyRegular_iff]
      intro i hi
      simp only [List.length_ofFn] at hi
      simp only [List.getElem_ofFn]
      exact hreg ⟨i, hi⟩
    · intro htop
      have h1 : (1 : MvPolynomial (Fin (n + 2)) K) ∈ Ideal.ofList (List.ofFn h)
          • (⊤ : Submodule (MvPolynomial (Fin (n + 2)) K)
              (MvPolynomial (Fin (n + 2)) K)) :=
        htop ▸ Submodule.mem_top
      have hmem1 : (1 : MvPolynomial (Fin (n + 2)) K)
          ∈ Ideal.ofList (List.ofFn h) :=
        ideal_smul_top_le _ _ h1
      have hle : Ideal.ofList (List.ofFn h)
          ≤ RingHom.ker (MvPolynomial.eval (0 : Fin (n + 2) → K)) := by
        refine Ideal.span_le.mpr (fun x hx => ?_)
        simp only [Set.mem_ofPred_eq, List.mem_ofFn] at hx
        obtain ⟨j, rfl⟩ := hx
        exact RingHom.mem_ker.mpr (by rw [hcombo j]; exact hcombo0 _)
      have hE1 : MvPolynomial.eval (0 : Fin (n + 2) → K) 1 = 0 :=
        RingHom.mem_ker.mp (hle hmem1)
      have hE1' : MvPolynomial.eval (0 : Fin (n + 2) → K) 1 = 1 := map_one _
      rw [hE1] at hE1'
      exact one_ne_zero hE1'.symm
  · rw [hfun]
    apply le_antisymm
    · exact hmonoFull
    · refine Ideal.span_le.mpr (fun x hx => ?_)
      obtain ⟨i, rfl⟩ := hx
      rw [hexpand i]
      refine Ideal.sum_mem _ (fun k _ => ?_)
      rw [MvPolynomial.smul_eq_C_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k, rfl⟩)

/-- Per-instance `hSES` feed: SES data (injective `K`-linear `f` between the
graded pieces + cokernel identification `e` with the next-quotient piece,
the exact inputs of `HilbertFunctionCount.graded_piece_ses`) with the stated finrank
values yields the exact per-`(k, d)` `hSES` recurrence instance consumed by
`HilbertFunctionCount.length_section_eq_two_pow`. The consumer assembles the
`∀ k, k < n + 1 → ∀ d, …` binders by applying this per instance to the
SES data (regularity ⇒ injectivity + cokernel
identification), which stays an explicit hypothesis here.

## References

* `HilbertFunctionCount.graded_piece_ses` (applied; itself `Elimination.ses_finrank_add`
  + `LinearMap.finrank_range_add_finrank_ker`).
* `HilbertFunctionCount.length_section_eq_two_pow` (consumer `hSES` shape).
* SES-data injectivity + cokernel identification (read-only
  source of `f` / `hinj` / `e`, taken as hypotheses, never imported). -/
theorem hSES_of_ses_data (n : ℕ) (K : Type*) [Field K]
    (H : ℕ → ℕ → ℕ)
    (k : ℕ) (_hk : k < n + 1) (d : ℕ)
    (P Q R : Type*) [AddCommGroup P] [AddCommGroup Q] [AddCommGroup R]
    [Module K P] [Module K Q] [Module K R]
    [Module.Finite K P] [Module.Finite K Q]
    (f : P →ₗ[K] Q) (e : (Q ⧸ LinearMap.range f) ≃ₗ[K] R)
    (hinj : Function.Injective f)
    (hP : Module.finrank K P = (if 2 ≤ d then H k (d - 2) else 0))
    (hQ : Module.finrank K Q = H k d)
    (hR : Module.finrank K R = H (k + 1) d) :
    H (k + 1) d + (if 2 ≤ d then H k (d - 2) else 0) = H k d := by
  have h := graded_piece_ses K P Q R f e hinj
  omega

/-- Per-instance `hSEC` feed: SES data (injective `K`-linear `f` between the
graded pieces, degree shift `1` + cokernel identification `e` with the
section piece, the exact inputs of `HilbertFunctionCount.graded_piece_ses`) with the
stated finrank values yields the exact per-`d` `hSEC` recurrence instance
consumed by `HilbertFunctionCount.length_section_eq_two_pow`. The consumer assembles
the `∀ d, …` binder by applying this per instance to the R1-regularity SES
data (from Statement's `hreg`), which stays an explicit hypothesis here.

## References

* `HilbertFunctionCount.graded_piece_ses` (applied; itself `Elimination.ses_finrank_add`
  + `LinearMap.finrank_range_add_finrank_ker`).
* `HilbertFunctionCount.length_section_eq_two_pow` (consumer `hSEC` shape). -/
theorem hSEC_of_ses_data (n : ℕ) (K : Type*) [Field K]
    (H : ℕ → ℕ → ℕ) (F : ℕ → ℕ)
    (d : ℕ)
    (P Q R : Type*) [AddCommGroup P] [AddCommGroup Q] [AddCommGroup R]
    [Module K P] [Module K Q] [Module K R]
    [Module.Finite K P] [Module.Finite K Q]
    (f : P →ₗ[K] Q) (e : (Q ⧸ LinearMap.range f) ≃ₗ[K] R)
    (hinj : Function.Injective f)
    (hP : Module.finrank K P = (if 1 ≤ d then H (n + 1) (d - 1) else 0))
    (hQ : Module.finrank K Q = H (n + 1) d)
    (hR : Module.finrank K R = F d) :
    F d + (if 1 ≤ d then H (n + 1) (d - 1) else 0) = H (n + 1) d := by
  have h := graded_piece_ses K P Q R f e hinj
  omega

/-! ## Explicit z-section toolkit (R1 at `mkSystem`)

Target statement: with `G = mkSystem n K F`, the z-variable form below has
regular image in `S = coneQuotient n K G`, i.e.
`IsSMulRegular S (mk (X last))`, feeding `Elimination.section_artinian`
(`hreg` input) toward chart finiteness and the `hcover`/`finite_locus`
circuit. No `hfin`/`havoid` are taken: single-form Ass-regularity must be
computed directly, never routed through the `hcover` discharge (circular).

Ass-control plan per piece:

* `k ≤ 1` unmixedness
  (`Unmixedness.mem_minimalPrimes_of_successive_zero/_singleton`): applies to
  quotients by `≤ 1` generators, while `S` quotients by `n + 1`; it applies
  directly only at `n = 0`. For `n ≥ 1` the argument stops at the open
  `k ≥ 2` obstruction (see `Unmixedness.lean`, `## Obstruction`; the
  `CohenMacaulayFragment` conditionals need the unproduced U2/`hdim`
  inputs).
* Triangular t1/t2a/t2b (`TriangularRegularity`; `AvoidanceApply.avoid_mkSystem_pair`
  supplies `hsucc` for generator pairs): regularity of the `G`-generators, not
  of the z-form; no lemma bridges generator-regularity to `z̄ ∉ P`,
  so this route also stops (t3 already stops in `TriangularRegularity`).
* No S-side transport bridge exists, and the S-side height inputs are
  open: cone unmixedness (`hAss`,
  height `≤ k ≤ n` on `Ass S S`) and the S-side catenary lower bound (`hHt`,
  including the z-prime case over `(span G, z)`). See `Unmixedness.lean`,
  `## Obstruction`, for the cone-`Ass` side.

Residual (exact): `IsSMulRegular S ℓ̄z` for `n ≥ 1` bottoms out at
cone-`Ass` control at `k = n + 1 ≥ 2` — the open unmixedness/catenary inputs
above. Proved here instead: the explicit section element and its chart
data below, for the eventual discharge. -/

/-! ## hsuccStep at `mkSystem`, conditional-exact on the `hunmixed` conclusion

`hsuccStep_mkSystem_of_hunmixed` packages the per-step call-site pair used by
the R2 `key` inductions (`exists_regular_quadrics_mkSystem`:892-895,
`exists_regular_quadrics_of_unmixed_hlow`:1193-1196): the `hsuccStep`
repackaging (`AvoidanceApply.hsucc_of_step_outputs`) plus the per-step
avoidance output (`comap ≠ ⊤`) it feeds, for `G = mkSystem n K F`.
`bridgeSystem` is `mkSystem (statementIndex n) K (bridgeForms …)`
(`BridgeToFixedPoint/MkSystemBridge.lean`), so the bridgeSystem step is this
theorem by application (no `Bridge` import is taken here).

The `hunmixed` hypothesis is the exact `GradeDepthFragment.unmixed_of_grade_of_depthEq`
(`GradeDepthFragment.lean`) conclusion shape — per-prime, with the `[P.IsPrime]`
instance binder, over `J = Ideal.span (Set.range h)` — so discharge
is one line:

```lean
fun P _ hP => GradeDepthFragment.unmixed_of_grade_of_depthEq (n + 2) K h hsucc J rfl P hP
  hbridge_T3 hchain hdepth
```

once T3's `k = 2` bridge proves (parallel development; cannot be imported here).

The `hdepth` hypothesis shape is pinned verbatim (it cannot be a
physical binder: `GradeDepthFragment` is outside this file's import closure — verified
by closure computation — and a top-of-file import edit is forbidden by this
lane's append-only ownership; supplies the binder at the use site):

```lean
(hdepth: ∀ (Q: Ideal (MvPolynomial (Fin (n + 2)) K)) [Q.IsPrime],
  Q ∈ associatedPrimes _ (_ ⧸ Ideal.span (Set.range h)) →
    GradeDepthFragment.DepthEqDimAt (n + 2) K Q)
```

Closed side data (cited, not re-proved): `hsucc` repackaging is unconditional
(`AvoidanceApply.hsucc_of_step_outputs`, `AvoidanceApply.lean`); rungs
`< 2` unmixedness is unconditional (`MacaulayScoped.scoped_prefix_zero/one`,
`MacaulayScoped.lean`, via `Unmixedness.lean`); prefix restriction is
`MacaulayScoped.successive_prefix` (`MacaulayScoped.lean`). Alternate
(C5) feed of the same conclusion shape: `scoped_of_chain_depth_babyAB`
(`GradeUnmixedBridge.lean`) from `(hchain, hdepth, hbaby)`.

Residual register (verbatim): open at `k ≥ 2`: [hunmixed-conclusion (shape, `k = 2` pending
T3-discharge, `k > 2` open; `k < 2` closed by
`scoped_prefix_zero/one`)]; [hlow (step-independent catenary lower bound,
 shape, open)]; [hdepth (hdepth shape, doc-pinned,
open — deep-core (iii))]. Context (supplied by the induction/consumer):
[hreg (per-step `IsSMulRegular` outputs)], [hZd (`IsZeroDimensional`)],
[hk (`k ≤ n`)].
-/

/-- hsuccStep at `mkSystem`, conditional-exact on the `hunmixed` conclusion:
per-step `IsSMulRegular` outputs repackage to `SuccessiveSMulRegular h`, and
with `hlow` + `hunmixed` (conclusion-exact) every `Ass` prime of the
step quotient has proper `comboLin` pullback — the exact pair the R2 `key`
induction consumes. See the section header for shapes, wiring, and
the residual register.

## References

* `AvoidanceApply.hsucc_of_step_outputs` (`AvoidanceApply.lean`;
  `ofList`-take to span-image repackaging).
* `AvoidanceApply.avoid_of_hunmixed_ge2` (`AvoidanceApply.lean`) and
  `AvoidanceApply.span_le_of_comap_comboLin_eq_top` (`AvoidanceApply.lean`).
* `RegularityBridge.span_range_eq_ofList_ofFn` (`RegularityBridge.lean`);
  `RegularSequenceDimDrop.span_smul_top` (`RegularSequenceDimDrop.lean`).
* `AssociatedPrimes.mem_iff`
  (`Mathlib/RingTheory/Ideal/AssociatedPrime/Basic.lean`) for the
  membership-to-instance adaptation (as at `AvoidanceApply.lean`).
* `GradeDepthFragment.unmixed_of_grade_of_depthEq` (`GradeDepthFragment.lean`) for the
  `hunmixed` conclusion shape; `MacaulayScoped.scoped_prefix_zero/one`
  (`MacaulayScoped.lean`) for closed rungs `< 2`. -/
theorem hsuccStep_mkSystem_of_hunmixed (n : ℕ) (K : Type*) [Field K] [IsAlgClosed K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hZd : IsZeroDimensional n K (mkSystem n K F))
    (k : ℕ) (hk : k ≤ n)
    (h : Fin k → MvPolynomial (Fin (n + 2)) K)
    (hreg : ∀ j : Fin k, IsSMulRegular
      (MvPolynomial (Fin (n + 2)) K ⧸ (Ideal.ofList (List.take (j.val) (List.ofFn h)) •
        (⊤ : Submodule (MvPolynomial (Fin (n + 2)) K)
          (MvPolynomial (Fin (n + 2)) K))))
      (h j))
    (hlow : ∀ (P : Ideal (MvPolynomial (Fin (n + 2)) K)) [P.IsPrime],
      Ideal.span (Set.range (mkSystem n K F)) ≤ P →
      ((((n + 2 : ℕ))) : WithBot ℕ∞) ≤
        (P.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial (Fin (n + 2)) K ⧸ P))
    (hunmixed : ∀ (P : Ideal (MvPolynomial (Fin (n + 2)) K)) [P.IsPrime],
      P ∈ associatedPrimes (MvPolynomial (Fin (n + 2)) K)
        (MvPolynomial (Fin (n + 2)) K ⧸ Ideal.span (Set.range h)) →
      P ∈ (Ideal.span (Set.range h)).minimalPrimes) :
    RegularityBridge.SuccessiveSMulRegular h ∧
      ∀ (P : Ideal (MvPolynomial (Fin (n + 2)) K)),
        P ∈ associatedPrimes (MvPolynomial (Fin (n + 2)) K)
          (MvPolynomial (Fin (n + 2)) K ⧸ (Ideal.ofList (List.ofFn h) •
            (⊤ : Submodule (MvPolynomial (Fin (n + 2)) K)
              (MvPolynomial (Fin (n + 2)) K)))) →
        Submodule.comap (comboLin K (mkSystem n K F))
          (Submodule.restrictScalars K
            (P : Submodule (MvPolynomial (Fin (n + 2)) K)
              (MvPolynomial (Fin (n + 2)) K))) ≠ ⊤ := by
  have hsuccStep := AvoidanceApply.hsucc_of_step_outputs h hreg
  have hunmixed_mem : ∀ P ∈ associatedPrimes (MvPolynomial (Fin (n + 2)) K)
      (MvPolynomial (Fin (n + 2)) K ⧸ Ideal.span (Set.range h)),
      P ∈ (Ideal.span (Set.range h)).minimalPrimes := by
    intro P hPm
    exact @hunmixed P (AssociatedPrimes.mem_iff.mp hPm).isPrime hPm
  refine ⟨hsuccStep, fun P hPmem => ?_⟩
  have eJ : (Ideal.ofList (List.ofFn h) •
      (⊤ : Submodule (MvPolynomial (Fin (n + 2)) K)
        (MvPolynomial (Fin (n + 2)) K)) : Submodule (MvPolynomial (Fin (n + 2)) K)
      (MvPolynomial (Fin (n + 2)) K)) = ↑(Ideal.span (Set.range h)) := by
    rw [← RegularityBridge.span_range_eq_ofList_ofFn h]
    exact RegularSequenceDimDrop.span_smul_top _
  rw [eJ] at hPmem
  have hno := AvoidanceApply.avoid_of_hunmixed_ge2 n K (mkSystem n K F) hZd k hk h
    hsuccStep (Ideal.span (Set.range h)) rfl hlow (fun _ => hunmixed_mem) P hPmem
  exact fun htop =>
    hno (AvoidanceApply.span_le_of_comap_comboLin_eq_top n K (mkSystem n K F) P htop)

/-! ## Unconditional `hlow` (catenary lower bound, wired from `hlow_uncond`)

`hlow_uncond` (`Dimension/HeightLowerBound.lean`, via
`TriangularChain.normap_of_prime`, `quotient_dim_of_normap`, and
`FiberExhibit.hheight_uncond`) proves the exact `hlow`
conclusion for every prime with no system hypothesis, so the
step-independent catenary input of all three consumers below is discharged:
`exists_regular_quadrics_mkSystem` ,
`exists_regular_quadrics_of_unmixed_hlow` , and
`hsuccStep_mkSystem_of_hunmixed`. No import edit is needed:
`HeightLowerBound` is already in this file's transitive import closure via
`AvoidanceApply` (`AvoidanceApply.lean`).

Residual register (verbatim): open at `k ≥ 2`: [hunmixed-conclusion (shape, `k = 2` pending
T3-discharge, `k > 2` open; `k < 2` closed by
`scoped_prefix_zero/one`)]; [hdepth (hdepth shape, doc-pinned,
open — deep-core (iii))]. Closed here: [hlow (step-independent catenary
lower bound, shape, closed by `hlow_general` wiring
`hlow_uncond`)]. Context (supplied by the induction/consumer):
[hreg (per-step `IsSMulRegular` outputs)], [hZd (`IsZeroDimensional`)],
[hk (`k ≤ n`)].
-/

/-- Unconditional step-independent catenary lower bound in exactly the
 `hlow` hypothesis shape, for general `G`: every prime
containing `span G` satisfies
`(n + 2) ≤ P.height + dim (R ⧸ P)`. The containment hypothesis is unused
(`hlow_uncond` needs no system at all); it is retained for interface
stability with the three consumers.

## References

* `HeightLowerBound.hlow_uncond` (`Dimension/HeightLowerBound.lean`).
* `TriangularChain.normap_of_prime`, `quotient_dim_of_normap`
  (`Dimension/TriangularChain.lean`).
* `FiberExhibit.hheight_uncond` (`Dimension/FiberExhibit.lean`). -/
theorem hlow_general (n : ℕ) (K : Type*) [Field K] [IsAlgClosed K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K) :
    ∀ (P : Ideal (MvPolynomial (Fin (n + 2)) K)) [P.IsPrime],
      Ideal.span (Set.range G) ≤ P →
      ((((n + 2 : ℕ))) : WithBot ℕ∞) ≤
        (P.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial (Fin (n + 2)) K ⧸ P) := by
  intro P _ _
  exact hlow_uncond n K P

/-- R2 for general `G`, conditional on `hunmixed`-at-`k ≥ 2` only: the
`hlow` input of `exists_regular_quadrics_of_unmixed_hlow` is discharged by
`hlow_general`.

## References

* `exists_regular_quadrics_of_unmixed_hlow` above.
* `hlow_general` above. -/
theorem exists_regular_quadrics_of_unmixed (n : ℕ) (K : Type*) [Field K]
    [IsAlgClosed K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hG : ∀ i, (G i).IsHomogeneous 2)
    (hZd : IsZeroDimensional n K G)
    (hunmixed_ge2 : ∀ (k : ℕ), 2 ≤ k →
      ∀ (q : Fin k → MvPolynomial (Fin (n + 2)) K)
      (_hsucc : RegularityBridge.SuccessiveSMulRegular q)
      (J : Ideal (MvPolynomial (Fin (n + 2)) K))
      (_hJ : J = Ideal.span (Set.range q)),
      ∀ P ∈ associatedPrimes (MvPolynomial (Fin (n + 2)) K)
        (MvPolynomial (Fin (n + 2)) K ⧸ J), P ∈ J.minimalPrimes) :
    ∃ M : Matrix (Fin (n + 1)) (Fin (n + 1)) K, IsUnit M ∧
      RingTheory.Sequence.IsRegular (MvPolynomial (Fin (n + 2)) K)
        (List.ofFn fun k => ∑ j, M k j • G j) ∧
      Ideal.span (Set.range fun k => ∑ j, M k j • G j)
        = Ideal.span (Set.range G) :=
  exists_regular_quadrics_of_unmixed_hlow n K G hG hZd (hlow_general n K G)
    hunmixed_ge2

/-- R2 at `mkSystem`, conditional on `hunmixed`-at-`k ≥ 2` only: the `hlow`
input of `exists_regular_quadrics_mkSystem` is discharged by `hlow_general`.

## References

* `exists_regular_quadrics_mkSystem` above.
* `hlow_general` above. -/
theorem exists_regular_quadrics_mkSystem_of_hunmixed_ge2 (n : ℕ) (K : Type*)
    [Field K] [IsAlgClosed K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2)
    (hZd : IsZeroDimensional n K (mkSystem n K F))
    (hunmixed_ge2 : ∀ (k : ℕ), 2 ≤ k →
      ∀ (q : Fin k → MvPolynomial (Fin (n + 2)) K)
      (_hsucc : RegularityBridge.SuccessiveSMulRegular q)
      (J : Ideal (MvPolynomial (Fin (n + 2)) K))
      (_hJ : J = Ideal.span (Set.range q)),
      ∀ P ∈ associatedPrimes (MvPolynomial (Fin (n + 2)) K)
        (MvPolynomial (Fin (n + 2)) K ⧸ J), P ∈ J.minimalPrimes) :
    ∃ M : Matrix (Fin (n + 1)) (Fin (n + 1)) K, IsUnit M ∧
      RingTheory.Sequence.IsRegular (MvPolynomial (Fin (n + 2)) K)
        (List.ofFn fun k => ∑ j, M k j • mkSystem n K F j) ∧
      Ideal.span (Set.range fun k => ∑ j, M k j • mkSystem n K F j)
        = Ideal.span (Set.range (mkSystem n K F)) :=
  exists_regular_quadrics_mkSystem n K F hF hZd (hlow_general n K _) hunmixed_ge2

/-- hsuccStep at `mkSystem` with `hlow` discharged: per-step
`IsSMulRegular` outputs repackage to `SuccessiveSMulRegular h`, and with
`hunmixed` (conclusion-exact) every `Ass` prime of the step quotient
has proper `comboLin` pullback. See `hsuccStep_mkSystem_of_hunmixed` for
shapes, wiring, and the residual register.

## References

* `hsuccStep_mkSystem_of_hunmixed` above.
* `hlow_general` above. -/
theorem hsuccStep_mkSystem_of_hunmixed_uncond_hlow (n : ℕ) (K : Type*)
    [Field K] [IsAlgClosed K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hZd : IsZeroDimensional n K (mkSystem n K F))
    (k : ℕ) (hk : k ≤ n)
    (h : Fin k → MvPolynomial (Fin (n + 2)) K)
    (hreg : ∀ j : Fin k, IsSMulRegular
      (MvPolynomial (Fin (n + 2)) K ⧸ (Ideal.ofList (List.take (j.val) (List.ofFn h)) •
        (⊤ : Submodule (MvPolynomial (Fin (n + 2)) K)
          (MvPolynomial (Fin (n + 2)) K))))
      (h j))
    (hunmixed : ∀ (P : Ideal (MvPolynomial (Fin (n + 2)) K)) [P.IsPrime],
      P ∈ associatedPrimes (MvPolynomial (Fin (n + 2)) K)
        (MvPolynomial (Fin (n + 2)) K ⧸ Ideal.span (Set.range h)) →
      P ∈ (Ideal.span (Set.range h)).minimalPrimes) :
    RegularityBridge.SuccessiveSMulRegular h ∧
      ∀ (P : Ideal (MvPolynomial (Fin (n + 2)) K)),
        P ∈ associatedPrimes (MvPolynomial (Fin (n + 2)) K)
          (MvPolynomial (Fin (n + 2)) K ⧸ (Ideal.ofList (List.ofFn h) •
            (⊤ : Submodule (MvPolynomial (Fin (n + 2)) K)
              (MvPolynomial (Fin (n + 2)) K)))) →
        Submodule.comap (comboLin K (mkSystem n K F))
          (Submodule.restrictScalars K
            (P : Submodule (MvPolynomial (Fin (n + 2)) K)
              (MvPolynomial (Fin (n + 2)) K))) ≠ ⊤ :=
  hsuccStep_mkSystem_of_hunmixed n K F hZd k hk h hreg (hlow_general n K _)
    hunmixed

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
