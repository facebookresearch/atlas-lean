/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.ResidualWiring
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.R1RegularSection
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.Rung.RungDiagonal
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.Rung.RungRegular
import Appendix_FixedPoint.BezoutChain.Statement.Definitions
import Appendix_FixedPoint.BezoutChain.Geometry.UnmixednessAtLengthK
import Appendix_FixedPoint.BezoutChain.Geometry.UnmixednessAtLengthTwo
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.DimensionToMultiplicity
import Appendix_FixedPoint.BezoutChain.Regularity.Grade.GradedDimEq
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.HighRelationsLowerBound
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.RegularityBridge
import Appendix_FixedPoint.BezoutChain.Regularity.Unmixed.Unmixedness
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Span

/-!
# `ConeNoEmbedded` at rungs `≥ 2`: R-side reduction + diagonal narrowing

This lane attacks the open central crux for rungs `≥ 2` (`n ≥ 1`,
i.e. `k = n + 1 ≥ 2` equations): `R1RegularSection.ConeNoEmbedded n K F` — no
embedded primes on the `mkSystem` cone. Rung 1 (`n = 0`) is closed
(`R1RegularSection.coneNoEmbedded_rung1_of_ne_zero`, via singleton unmixedness);
here the general-`n` case is reduced to named residuals, and the `hsucc`
half is given a precise diagonal-narrowing SPEC with the known witness
excluded.

## What is proved here

* §1 `mem_associatedPrimes_quot_of_mem_associatedPrimes_ge` (unconditional):
  the S-side→R-side associated-prime pullback at general `n` (verbatim
  generalization of the rung-1
  `R1RegularSection.mem_associatedPrimes_quot_of_mem_associatedPrimes`, whose proof
  never uses rung-1 facts: `Ideal.comap_radical` + definitional
  `comap`-of-colon).
* §2 `coneNoEmbedded_of_hunmixed` (unconditional reduction): `ConeNoEmbedded`
  from the R-side unmixedness `∀`-form (every `P ∈ Ass(R ⧸ J)` minimal over
  `J`), descended through the surjective quotient correspondence
  (`Ideal.map_comap_of_surjective`). Mirrors the rung-1 descent
  (`R1RegularSection.coneNoEmbedded_rung1_of_ne_zero`), with the singleton lemma
  replaced by the hypothesis. No `hsucc` needed for the bridge itself.
* §3 `coneNoEmbedded_of_hsucc_of_hdimEqMin` (conditional-exact on
  `[hsucc, HdimEqMinAtAss]`): §2 fed with
  `UnmixednessAtLengthK.hunmixed_of_hdimEqMin`.
* §4 `havoid_secForm_of_hsucc_of_hdimEqMin_of_hcut` (conditional-exact on
  `[hF, hsucc, hdimEq, hcut]` + `[IsAlgClosed K]`): general-`n` `havoid`
  for the explicit section, via §3 +
  `R1RegularSection.secFormAvoidsMinimal_of_hcut` +
  `R1RegularSection.havoid_secForm_of_noEmbedded_of_minAvoid`.
* §5 `havoid_secForm_bridgeForms_of_algebraData_of_hsucc_of_hdimEqMin`
  (conditional-exact on `[hsucc, hdimEq]` given consumer algebra data):
  the §4 package at `bridgeForms`/`bridgeSystem` data (by `rfl`-defeq,
  mirroring `ResidualWiring`), in the verbatim `Hres2` second-component shape
  at instance `(n, c)`. This is the general-rung `havoid` half of `Hres2`.
* §6 diagonal narrowing for the `hsucc` half: `IsDiagonalQuad` (SPEC),
  `cross_not_diagonal` (unconditional: `X i * X j`, `i ≠ j`, is not a
  diagonal quadric, by a `coeff`-at-`single i 1 + single j 1` computation
  mirroring `Triangular.mkSystem_ne_zero`), and
  `badConsts_f1_not_diagonal` (unconditional: the
  `RungRegular.badConsts` rung-1 killer `F₁ = X₀X₁` is excluded by the
  diagonal predicate, via `RungRegular.bridgeForms_two_one`).
* §7 supply: rung-1 `hsucc` + `ConeNoEmbedded`
  unconditional (`hsucc_bridgeSystem_rung1`,
  `coneNoEmbedded_zero_uncond` via §2 + closed singleton unmixedness —
  the `HdimEq` route bypassed); end-to-end rung-1 `Hres2Inst` pair from
  algebra data (`hres2_pair_rung1_of_algebraData`); rung-2 `hsucc` under
  `[diagonal, nondegeneracy]` (`hsucc_bridgeSystem_rung2_diagonal`) with
  §§3–5 instantiated at `n = 2` on `[HdimEqMinAtAss]` alone;
  `hdimEqMinAtAss_of_embdim_le_one` reframing the `d ≥ 2` remainder as
  an embdim bound.

## Precise narrowed remainder (out of scope)

1. `hsucc : SuccessiveSMulRegular (mkSystem n K F)` at `j.val ≥ 2`
   (`n ≥ 3`): the (t3) obstruction (`TriangularRegularity`: after quotienting
   by the rung-2 prime the quotient is a domain but no longer a polynomial
   ring — no division algorithm, no `deg_z`). The full `∀ (n, c)` form is
   false (`RungRegular.hreg_forall_false`, off-diagonal witness); §6 is the
   machine-checked starting point of the scoped diagonal-`c` narrowing
   follow-up, and §7 closes rung 0 unconditionally, rung 1 under
   `[diagonal, nondegeneracy]`, hence `hsucc` at `n ≤ 2` — only
   `j.val ≥ 2` rungs remain.
2. `HdimEqMinAtAss` (equivalent to `HmultMinAtAss`/`HwitMinAtAss`/
   `HkerMinAtAss` at `d ≥ 2` by the `DimensionToMultiplicity` iffs): the R-2c′
   dimension-to-multiplicity leg is closed (exact on `HgrDimEqMinAtAss`);
   live remainder is R-2a′ `dim gr(R_Q) = d` per Ass prime
   (`HdimGrMinAtAss`, `UnmixednessAtLengthTwo` §8: `d = 0/1` closed, `d ≥ 2` on
   `HwitMinAtAss`). Bypassed at rung 1 (§7 singleton route); vacuous
   under `embdim ≤ 1` (§7 reframing); genuinely present at rung `≥ 2`.
3. `hF`/`hcut` at instance data: discharged by consumer algebra data
   (`bridgeForms_homogeneous`, `SpineAdapter.hcut_of_algebraData_semiring`;
   consumed in §5 via `ResidualWiring`). Nothing else is assumed.

## Import DAG

New leaf module (no importers): `BridgeToFixedPoint/ResidualWiring`,
`BridgeToFixedPoint/R1RegularSection`,
`BridgeToFixedPoint/RungDiagonal`, `BridgeToFixedPoint/RungRegular`,
`Geometry/UnmixednessAtLengthK`,
`Geometry/UnmixednessAtLengthTwo`, `Regularity/RegularityBridge`, `Regularity/Unmixedness`,
`Statement/Definitions`, narrow Mathlib. No cycle risk.

## References

Project (`Formalization/Appendix_FixedPoint/BezoutChain/`):

* `BridgeToFixedPoint/R1RegularSection.lean`:
  `cutsOutOrigin`, `SecFormAvoidsMinimal`, `ConeNoEmbedded`,
  `havoid_secForm_of_noEmbedded_of_minAvoid`,
  `secFormAvoidsMinimal_of_hcut`,
  `mem_associatedPrimes_quot_of_mem_associatedPrimes`,
  `coneNoEmbedded_rung1_of_ne_zero` (all mirrored or consumed).
* `Geometry/UnmixednessAtLengthK.lean`: `hunmixed_of_hdimEqMin`.
* `Geometry/UnmixednessAtLengthTwo.lean`: `HdimEqMinAtAss`,
  `HmultMinAtAss`, `hdimEqMin_of_hmultMin`.
* `BridgeToFixedPoint/Rung/RungRegular.lean`: `hreg_rung0`, `badConsts`,
  `bridgeForms_two_one`, `hreg_forall_false` (§7 rung-0/∀-form inputs).
* `BridgeToFixedPoint/ResidualWiring.lean`: `Hres2`,
  `secFormAvoidsMinimal_bridgeForms_of_algebraData`.
* `BridgeToFixedPoint/Rung/RungDiagonal.lean`: `rungI0`, `IsDiagonal`,
  `hreg_rung1_diagonal` (§7 rung-2 `hsucc`).
* `Regularity/Unmixed/Unmixedness.lean`:
  `mem_minimalPrimes_of_successive_singleton` (§7 singleton route).
* `Regularity/Avoid/AvoidanceApply.lean`: `hsucc_of_step_outputs`,
  `hsucc_mkSystem_singleton` (§7 `hsucc` assembly).
* `Regularity/Avoid/TriangularRegularity.lean`: `mkSystem_ne_zero` (coeff technique).

Mathlib v4.34.0 (all `grep`-verified, same citations as the mirrored files):

* `AssociatedPrimes.mem_iff`
  (`Mathlib/RingTheory/Ideal/AssociatedPrime/Basic.lean`).
* `Ideal.comap_radical`, `Ideal.comap_isPrime`, `Ideal.comap_mono`,
  `Ideal.map_mono`, `Ideal.map_comap_of_surjective`
  (`Mathlib/RingTheory/Ideal/Maps.lean`).
* `Ideal.Quotient.mk_surjective`, `Ideal.Quotient.eq_zero_iff_mem`
  (`Mathlib/RingTheory/Ideal/Quotient/Defs.lean`).
* `MvPolynomial.coeff_X_mul`, `MvPolynomial.coeff_X_same`,
  `MvPolynomial.coeff_X`, `MvPolynomial.coeff_X_pow`,
  `MvPolynomial.coeff_C_mul`, `MvPolynomial.coeff_sum`
  (`Mathlib/Algebra/MvPolynomial/Basic.lean`).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace ConeNoEmbeddedRungs

open scoped BigOperators

/-! ## §1. S-side→R-side Ass pullback at general `n` (unconditional) -/

/-- S-side associated primes pull back to R-side ones along the cone quotient
map at general `n`: verbatim generalization of
`R1RegularSection.mem_associatedPrimes_quot_of_mem_associatedPrimes` (whose proof
never uses rung-1 facts). `comap` commutes with `radical`
(`Ideal.comap_radical`), and the `comap`-of-colon step is definitional.
-/
theorem mem_associatedPrimes_quot_of_mem_associatedPrimes_ge
    (n : ℕ) (K : Type*) [Field K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (P : Ideal (coneQuotient n K (mkSystem n K F)))
    (hP : P ∈ associatedPrimes (coneQuotient n K (mkSystem n K F))
      (coneQuotient n K (mkSystem n K F))) :
    Ideal.comap (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))) P
      ∈ associatedPrimes (MvPolynomial (Fin (n + 2)) K)
        (MvPolynomial (Fin (n + 2)) K ⧸ Ideal.span (Set.range (mkSystem n K F))) := by
  rw [AssociatedPrimes.mem_iff] at hP ⊢
  obtain ⟨hprime, x, hx⟩ := hP
  have hQprime : P.IsPrime := hprime
  refine ⟨Ideal.comap_isPrime _ _, x, ?_⟩
  rw [hx, Ideal.comap_radical]
  congr 1

#print axioms mem_associatedPrimes_quot_of_mem_associatedPrimes_ge

/-! ## §2. Master bridge: `ConeNoEmbedded` from R-side unmixedness -/

/-- `ConeNoEmbedded` at general `n` from the R-side unmixedness `∀`-form:
every `P ∈ Ass(R ⧸ J)` minimal over `J` descends through the surjective
quotient correspondence (`Ideal.map_comap_of_surjective`). Mirrors the rung-1
descent (`R1RegularSection.coneNoEmbedded_rung1_of_ne_zero`), with the singleton
unmixedness lemma replaced by the hypothesis. The bridge itself needs no
`hsucc` (`hsucc` is only needed to *obtain* the R-side `∀`-form).
-/
theorem coneNoEmbedded_of_hunmixed
    (n : ℕ) (K : Type*) [Field K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hunmixed : ∀ P : Ideal (MvPolynomial (Fin (n + 2)) K),
      P ∈ associatedPrimes (MvPolynomial (Fin (n + 2)) K)
        (MvPolynomial (Fin (n + 2)) K ⧸ Ideal.span (Set.range (mkSystem n K F))) →
      P ∈ (Ideal.span (Set.range (mkSystem n K F))).minimalPrimes) :
    R1RegularSection.ConeNoEmbedded n K F := by
  intro P hP Q' hQ' hle
  have hPR := mem_associatedPrimes_quot_of_mem_associatedPrimes_ge n K F P hP
  have hmin : Ideal.comap
      (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))) P
      ∈ (Ideal.span (Set.range (mkSystem n K F))).minimalPrimes :=
    hunmixed _ hPR
  have hQ'prime : Q'.IsPrime := hQ'
  have hprimeQ : (Ideal.comap
      (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))) Q').IsPrime :=
    Ideal.comap_isPrime _ _
  have hJle : Ideal.span (Set.range (mkSystem n K F)) ≤
      Ideal.comap (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))) Q' := by
    rw [Ideal.span_le]
    intro y hy
    obtain ⟨i, rfl⟩ := hy
    change Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))
      (mkSystem n K F i) ∈ Q'
    have h0 : Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))
        (mkSystem n K F i) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
    rw [h0]
    exact Submodule.zero_mem _
  have hleR : Ideal.comap
      (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))) Q'
      ≤ Ideal.comap
        (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))) P :=
    Ideal.comap_mono hle
  have hmin2 := hmin.2 ⟨hprimeQ, hJle⟩ hleR
  have hsurj : Function.Surjective
      (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))) :=
    Ideal.Quotient.mk_surjective
  have eP := Ideal.map_comap_of_surjective _ hsurj P
  have eQ := Ideal.map_comap_of_surjective _ hsurj Q'
  rw [← eP, ← eQ]
  exact Ideal.map_mono hmin2

#print axioms coneNoEmbedded_of_hunmixed

/-! ## §3. Instantiation on `[hsucc, HdimEqMinAtAss]` -/

/-- `ConeNoEmbedded` at general `n` from `[hsucc, HdimEqMinAtAss]`: §2 fed
with `UnmixednessAtLengthK.hunmixed_of_hdimEqMin` (at `k := n + 1`, `m := n + 2`).

Conditional on exactly `[hsucc, hdimEq]`. -/
theorem coneNoEmbedded_of_hsucc_of_hdimEqMin
    (n : ℕ) (K : Type*) [Field K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular (mkSystem n K F))
    (hdimEq : UnmixednessAtLengthTwo.HdimEqMinAtAss (n + 2) K
      (Ideal.span (Set.range (mkSystem n K F)))) :
    R1RegularSection.ConeNoEmbedded n K F := by
  refine coneNoEmbedded_of_hunmixed n K F (fun P hP => ?_)
  have := (AssociatedPrimes.mem_iff.mp hP).isPrime
  exact UnmixednessAtLengthK.hunmixed_of_hdimEqMin (n + 2) K (mkSystem n K F) hsucc
    _ rfl P hP hdimEq

#print axioms coneNoEmbedded_of_hsucc_of_hdimEqMin

/-! ## §4. End-to-end `havoid` at general `n` -/

/-- General-`n` `havoid` for the explicit section from
`[hF, hsucc, hdimEq, hcut]` (+ `[IsAlgClosed K]`): §3 +
`R1RegularSection.secFormAvoidsMinimal_of_hcut` through
`R1RegularSection.havoid_secForm_of_noEmbedded_of_minAvoid`.

Conditional on exactly `[hF, hsucc, hdimEq, hcut]`. -/
theorem havoid_secForm_of_hsucc_of_hdimEqMin_of_hcut
    (n : ℕ) (K : Type*) [Field K] [IsAlgClosed K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2)
    (hsucc : RegularityBridge.SuccessiveSMulRegular (mkSystem n K F))
    (hdimEq : UnmixednessAtLengthTwo.HdimEqMinAtAss (n + 2) K
      (Ideal.span (Set.range (mkSystem n K F))))
    (hcut : R1RegularSection.cutsOutOrigin n K F) :
    ∀ P ∈ associatedPrimes (coneQuotient n K (mkSystem n K F))
      (coneQuotient n K (mkSystem n K F)),
      Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))
        (mkLin n K (R1RegularSection.secForm n K)) ∉ P :=
  R1RegularSection.havoid_secForm_of_noEmbedded_of_minAvoid n K F
    (coneNoEmbedded_of_hsucc_of_hdimEqMin n K F hsucc hdimEq)
    (R1RegularSection.secFormAvoidsMinimal_of_hcut n K F hF hcut)

#print axioms havoid_secForm_of_hsucc_of_hdimEqMin_of_hcut

/-! ## §5. The `Hres2` `havoid` half at instance `(n, c)` bridge data -/

/-- General-rung `havoid` at `bridgeForms`/`bridgeSystem` data from consumer
algebra data + `[hsucc, hdimEq]`: the §4 package applied by `rfl`-defeq
(`bridgeSystem n K c hn` is `mkSystem (statementIndex n) K
(bridgeForms n K c hn)`; mirrors `ResidualWiring`), in the verbatim `Hres2`
second-component shape at instance `(n, c)`. `hF`/`hcut` are discharged
from algebra data via
`ResidualWiring.secFormAvoidsMinimal_bridgeForms_of_algebraData`.

Conditional on exactly `[hsucc, hdimEq]` given algebra data. -/
theorem havoid_secForm_bridgeForms_of_algebraData_of_hsucc_of_hdimEqMin
    (K E : Type*) [Field K] [IsAlgClosed K]
    [NonUnitalNonAssocSemiring E] [Module K E]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (V : Submodule K E) (b : Module.Basis (Fin n) K V)
    (hexp : ∀ i j, (b i : E) * (b j : E) = ∑ k, c i j k • (b k : E))
    (hN : absNilpotent K E V = {0})
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E)
    (hsucc : RegularityBridge.SuccessiveSMulRegular (bridgeSystem n K c hn))
    (hdimEq : UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex n + 2) K
      (Ideal.span (Set.range (bridgeSystem n K c hn)))) :
    ∀ P ∈ associatedPrimes
        (coneQuotient (statementIndex n) K (bridgeSystem n K c hn))
        (coneQuotient (statementIndex n) K (bridgeSystem n K c hn)),
      Ideal.Quotient.mk
        (Ideal.span (Set.range (bridgeSystem n K c hn)))
        (mkLin (statementIndex n) K
          (R1RegularSection.secForm (statementIndex n) K)) ∉ P :=
  R1RegularSection.havoid_secForm_of_noEmbedded_of_minAvoid (statementIndex n) K
    (bridgeForms n K c hn)
    (coneNoEmbedded_of_hsucc_of_hdimEqMin (statementIndex n) K
      (bridgeForms n K c hn) hsucc hdimEq)
    (ResidualWiring.secFormAvoidsMinimal_bridgeForms_of_algebraData K E n hn c V b
      hexp hN htower hcomm)

#print axioms havoid_secForm_bridgeForms_of_algebraData_of_hsucc_of_hdimEqMin

/-! ## §6. Diagonal narrowing for the `hsucc` half -/

/-- A quadric is diagonal if it is a `K`-linear combination of squares of
variables (no cross terms): the SPEC predicate for the scoped diagonal-`c`
narrowing of the rung-`≥ 1` `hreg` inputs (cf.
`RungRegular.hreg_forall_false`: the full `∀ (n, c)` form is refuted by the
off-diagonal `badConsts`). -/
def IsDiagonalQuad {σ : Type*} [Fintype σ] (K : Type*) [Field K]
    (p : MvPolynomial σ K) : Prop :=
  ∃ c : σ → K, p = ∑ l, MvPolynomial.C (c l) *
    (MvPolynomial.X l * MvPolynomial.X l)

/-- The cross monomial `single i 1 + single j 1` takes value `≤ 1` at every
coordinate when `i ≠ j` (at most one summand is nonzero there). Stated over
`Fin m` (all consumers are `Fin`-indexed), so no `DecidableEq` binder. -/
theorem cross_single_le_one (m : ℕ)
    (i j l : Fin m) (hij : i ≠ j) :
    (Finsupp.single i 1 + Finsupp.single j 1 : Fin m →₀ ℕ) l ≤ 1 := by
  by_cases hi : l = i <;> by_cases hj : l = j
  · exact absurd (hi.symm.trans hj) hij
  · subst hi
    simp [Finsupp.add_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne hj]
  · subst hj
    simp [Finsupp.add_apply, Finsupp.single_eq_of_ne (Ne.symm hij),
      Finsupp.single_eq_same]
  · simp [Finsupp.add_apply, Finsupp.single_eq_of_ne hi,
      Finsupp.single_eq_of_ne hj]

/-- A diagonal sum has `coeff 0` at every cross monomial (`i ≠ j`): each
square `(X l)^2` sees `single l 2 ≠ single i 1 + single j 1` (differ at `l`
by `cross_single_le_one`), via `MvPolynomial.coeff_X_pow`. -/
theorem coeff_diagonal_sum_cross_zero (m : ℕ)
    (K : Type*) [Field K] (c : Fin m → K) (i j : Fin m) (hij : i ≠ j) :
    ((∑ l, MvPolynomial.C (c l) *
      (MvPolynomial.X l * MvPolynomial.X l) : MvPolynomial (Fin m) K)).coeff
      (Finsupp.single i 1 + Finsupp.single j 1) = 0 := by
  rw [MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro l _
  rw [MvPolynomial.coeff_C_mul]
  have hsq : ∀ l : Fin m,
      (MvPolynomial.X l * MvPolynomial.X l : MvPolynomial (Fin m) K)
      = MvPolynomial.X l ^ 2 := fun l => (pow_two _).symm
  rw [hsq, MvPolynomial.coeff_X_pow]
  have hne : Finsupp.single l 2 ≠
      (Finsupp.single i 1 + Finsupp.single j 1 : Fin m →₀ ℕ) := by
    intro h
    have hpt := congrArg (fun f : Fin m →₀ ℕ => f l) h
    rw [Finsupp.single_eq_same] at hpt
    have hle := cross_single_le_one m i j l hij
    omega
  simp [hne]

/-- The cross product has `coeff 1` at its own monomial (the
`Triangular.mkSystem_ne_zero` computation: `coeff_X_mul` + `coeff_X_same`). -/
theorem coeff_cross_one {σ : Type*} (K : Type*) [Field K] (i j : σ) :
    (MvPolynomial.X i * MvPolynomial.X j : MvPolynomial σ K).coeff
      (Finsupp.single i 1 + Finsupp.single j 1) = 1 := by
  rw [MvPolynomial.coeff_X_mul]
  exact MvPolynomial.coeff_X_same _

/-- Unconditional: a cross term `X i * X j` (`i ≠ j`) is not a diagonal
quadric — `congrArg coeff` at `single i 1 + single j 1` gives `1 = 0`. -/
theorem cross_not_diagonal (m : ℕ)
    (K : Type*) [Field K] (i j : Fin m) (hij : i ≠ j) :
    ¬ IsDiagonalQuad K
      (MvPolynomial.X i * MvPolynomial.X j : MvPolynomial (Fin m) K) := by
  rintro ⟨c, hc⟩
  have hcon := congrArg
    (fun p : MvPolynomial (Fin m) K =>
      p.coeff (Finsupp.single i 1 + Finsupp.single j 1)) hc
  rw [coeff_cross_one, coeff_diagonal_sum_cross_zero m K c i j hij] at hcon
  exact one_ne_zero hcon

/-- Unconditional: the `RungRegular.badConsts` rung-1 killer `F₁ = X₀X₁` is
excluded by the diagonal predicate (via
`RungRegular.bridgeForms_two_one`). Hence the scoped diagonal-`c` narrowing
kills the known `hreg_forall_false` witness; the narrowing follow-up is to
discharge the t2a/t2b `hdich` inputs + rung-`≥ 2` outputs under
`IsDiagonalQuad`. -/
theorem badConsts_f1_not_diagonal (K : Type*) [Field K] (hn2 : 0 < 2) :
    ¬ IsDiagonalQuad K
      (bridgeForms 2 K (RungRegular.badConsts K) hn2
        RungRegular.badI1) := by
  rw [RungRegular.bridgeForms_two_one]
  exact cross_not_diagonal _ K _ _ (by decide)

#print axioms cross_single_le_one
#print axioms coeff_diagonal_sum_cross_zero
#print axioms coeff_cross_one
#print axioms cross_not_diagonal
#print axioms badConsts_f1_not_diagonal

/-! ## §7. Supply: rung-1 unconditional + rung-2 diagonal instantiation

This section discharges the `[hsucc, HdimEqMinAtAss]` inputs of §§3–5
where the mathematics grounds, and reframes the rest as a precise
remainder:

* `hsucc_bridgeSystem_rung1` (unconditional): `hsucc` at `n = 1` — the
  family is a singleton (`statementIndex 1 + 1 = 1`), so `j.val = 0` is
  forced and rung 0 (`RungRegular.hreg_rung0`, t1) closes it.
* `hsucc_mkSystem_zero_uncond` (unconditional): `hsucc` for the
  singleton `mkSystem 0 K F` family, via
  `AvoidanceApply.hsucc_mkSystem_singleton` (t1 repackaged).
* `coneNoEmbedded_zero_uncond` (unconditional, all `F`): `ConeNoEmbedded`
  at `n = 0` via §2 fed with the closed singleton unmixedness
  (`Unmixedness.mem_minimalPrimes_of_successive_singleton`) on the t1
  `hsucc` above. No `HdimEqMinAtAss`, no `hcut`, no `F₀ ≠ 0` needed —
  the `HdimEq` route (§3) is bypassed at rung 1.
* `coneNoEmbedded_bridgeForms_rung1_uncond` (unconditional): the bridge
  instance (`statementIndex 1 ≡ 0` by `rfl`-defeq, as in `ResidualWiring`).
* `hres2_pair_rung1_of_algebraData` (end-to-end at rung 1): the full
  `Hres2Inst` pair `(hsucc ∧ havoid)` at `n = 1` from consumer algebra
  data — `hsucc` unconditional above, `havoid` via the proved rung-1
  `havoid_secForm_bridgeForms_rung1_of_algebraData` (`hcut` from algebra
  data; `SecFormAvoidsMinimal` genuinely needs it —
  `ResidualWiring.not_forall_secFormAvoidsMinimal_bridgeForms`).
* `hsucc_bridgeSystem_rung2_diagonal` (conditional-exact on
  `[diagonal, nondegeneracy]`): `hsucc` at `n = 2` — `j.val ∈ {0, 1}`
  (`statementIndex 2 + 1 = 2`), rung 0 by `hreg_rung0`, rung 1 by
  `RungDiagonal.hreg_rung1_diagonal`. This is the maximal `hsucc`
  grounding: `j.val ≥ 2` (present at `n ≥ 3`) is the (t3) obstruction,
  and the full `∀ (n, c)` form is false
  (`RungRegular.hreg_forall_false`).
* `coneNoEmbedded_bridgeForms_rung2_diagonal_of_hdimEqMin` /
  `havoid_secForm_bridgeForms_rung2_diagonal_of_algebraData_of_hdimEqMin`
  (conditional-exact on `[diagonal, nondegeneracy, HdimEqMinAtAss]` (+
  algebra data for `hcut`)): §§3–5 at `n = 2` with `hsucc` supplied.
* `hdimEqMinAtAss_of_embdim_le_one` (unconditional conditional-form):
  `HdimEqMinAtAss` from `spanFinrank 𝔪(R_Q) ≤ 1` over `Ass` — the
  `2 ≤ d` case is then vacuous (`omega`). This reframes (not closes)
  the `d ≥ 2` remainder as an embedding-dimension bound.

precise remainder after this section:

1. `hsucc` at `j.val ≥ 2` (`n ≥ 3`): the (t3) obstruction (quotient by
   the rung-2 prime is a domain but not a polynomial ring — no
   `deg_z`), even under `IsDiagonalQuad`/diagonal-`c`. Rungs `≤ 1`
   are fully closed (rung 0 unconditional; rung 1 on `[diagonal,
   nondegeneracy]`).
2. `HdimEqMinAtAss` at `d ≥ 2`: the R-2c′ leg
   (dimension-to-multiplicity) is closed (`DimensionToMultiplicity`, exact on
   `HgrDimEqMinAtAss`); live remainder is R-2a′ (`dim gr(R_Q) = d`
   per Ass prime — see `UnmixednessAtLengthTwo` §8: `d = 0/1` closed
   unconditionally, `d ≥ 2` on `HwitMinAtAss`). Genuinely present at
   rung `≥ 2`: at height-2 Ass primes `embdim = 2` by regularity
   (`MultiplicityNonvanishing.mult_dim_atPrime_eq_spanFinrank`), so the
   `embdim ≤ 1` vacuous discharge above does not apply in general. -/

/-- `hsucc` at `n = 1`, unconditional: the family is a singleton
(`statementIndex 1 + 1 = 1`), so `j.val = 0` is forced and the t1
rung-0 output (`RungRegular.hreg_rung0`) closes every step output.
-/
theorem hsucc_bridgeSystem_rung1 (K : Type*) [Field K]
    (c : Fin 1 → Fin 1 → Fin 1 → K) (hn : 0 < 1) :
    RegularityBridge.SuccessiveSMulRegular (bridgeSystem 1 K c hn) := by
  apply AvoidanceApply.hsucc_of_step_outputs
  intro j
  refine RungRegular.hreg_rung0 K 1 hn c j ?_
  have h1 : statementIndex 1 + 1 = 1 := rfl
  have hlt := j.isLt
  omega

/-- `hsucc` for the singleton `mkSystem 0 K F` family, unconditional:
t1 (`Triangular.mkSystem_isSMulRegular`, which needs no hypothesis on
`F`) repackaged by `AvoidanceApply.hsucc_mkSystem_singleton`.
-/
theorem hsucc_mkSystem_zero_uncond (K : Type*) [Field K]
    (F : Fin (0 + 1) → MvPolynomial (Fin (0 + 1)) K) :
    RegularityBridge.SuccessiveSMulRegular (mkSystem 0 K F) :=
  AvoidanceApply.hsucc_mkSystem_singleton 0 K F (mkSystem 0 K F) 0 rfl

/-- `ConeNoEmbedded` at `n = 0`, unconditional for all `F`: §2
(`coneNoEmbedded_of_hunmixed`) fed with the closed singleton
unmixedness (`Unmixedness.mem_minimalPrimes_of_successive_singleton`)
on the t1 `hsucc` above. The `HdimEqMinAtAss` route (§3) is bypassed
at rung 1 — no `HdimEq`, no `hcut`, no `F₀ ≠ 0` needed.
-/
theorem coneNoEmbedded_zero_uncond (K : Type*) [Field K]
    (F : Fin (0 + 1) → MvPolynomial (Fin (0 + 1)) K) :
    R1RegularSection.ConeNoEmbedded 0 K F := by
  refine coneNoEmbedded_of_hunmixed 0 K F (fun P hP => ?_)
  exact mem_minimalPrimes_of_successive_singleton (0 + 2) K
    (mkSystem 0 K F) (hsucc_mkSystem_zero_uncond K F) _ rfl P hP

/-- `ConeNoEmbedded` at rung-1 bridge data, unconditional:
`coneNoEmbedded_zero_uncond` at `statementIndex 1 ≡ 0` by `rfl`-defeq
(same identification as `ResidualWiring`, which needs `hcut` only for its
`F₀ ≠ 0` route — here singleton unmixedness replaces it).
-/
theorem coneNoEmbedded_bridgeForms_rung1_uncond (K : Type*) [Field K]
    (c : Fin 1 → Fin 1 → Fin 1 → K) (hn : 0 < 1) :
    R1RegularSection.ConeNoEmbedded (statementIndex 1) K (bridgeForms 1 K c hn) :=
  coneNoEmbedded_zero_uncond K (bridgeForms 1 K c hn)

/-- End-to-end `Hres2Inst` pair at rung 1 from consumer algebra data:
`hsucc` is unconditional (`hsucc_bridgeSystem_rung1`); `havoid` is the
proved rung-1 algebra-data discharge (`hcut` from `SpineAdapter`;
`SecFormAvoidsMinimal` genuinely needs algebra data per
`ResidualWiring.not_forall_secFormAvoidsMinimal_bridgeForms`).
-/
theorem hres2_pair_rung1_of_algebraData (K E : Type*) [Field K]
    [IsAlgClosed K] [NonUnitalNonAssocSemiring E] [Module K E]
    (c : Fin 1 → Fin 1 → Fin 1 → K) (hn : 0 < 1)
    (V : Submodule K E) (b : Module.Basis (Fin 1) K V)
    (hexp : ∀ i j, (b i : E) * (b j : E) = ∑ k, c i j k • (b k : E))
    (hN : absNilpotent K E V = {0})
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E) :
    RegularityBridge.SuccessiveSMulRegular (bridgeSystem 1 K c hn) ∧
      (∀ P ∈ associatedPrimes
          (coneQuotient (statementIndex 1) K (bridgeSystem 1 K c hn))
          (coneQuotient (statementIndex 1) K (bridgeSystem 1 K c hn)),
        Ideal.Quotient.mk
          (Ideal.span (Set.range (bridgeSystem 1 K c hn)))
          (mkLin (statementIndex 1) K
            (R1RegularSection.secForm (statementIndex 1) K)) ∉ P) := by
  constructor
  · exact hsucc_bridgeSystem_rung1 K c hn
  · exact ResidualWiring.havoid_secForm_bridgeForms_rung1_of_algebraData K E c hn
      V b hexp hN htower hcomm

/-- `hsucc` at `n = 2` under diagonal-`c` + nondegeneracy: `j.val ∈ {0,1}`
(`statementIndex 2 + 1 = 2`), rung 0 by `hreg_rung0`, rung 1 by
`RungDiagonal.hreg_rung1_diagonal`. Maximal `hsucc` grounding short of
the (t3) obstruction (`j.val ≥ 2`, present at `n ≥ 3`).

Conditional on exactly `[diagonal, nondegeneracy]`. -/
theorem hsucc_bridgeSystem_rung2_diagonal (K : Type*) [Field K]
    (c : Fin 2 → Fin 2 → Fin 2 → K) (hn : 0 < 2)
    (hdiag : RungDiagonal.IsDiagonal K c)
    (hnondeg : ∀ j : Fin (statementIndex 2 + 1), j.val = 1 →
      bridgeForms 2 K c hn (RungDiagonal.rungI0 2) ≠ 0 ∨
        bridgeForms 2 K c hn j ≠ 0) :
    RegularityBridge.SuccessiveSMulRegular (bridgeSystem 2 K c hn) := by
  apply AvoidanceApply.hsucc_of_step_outputs
  intro j
  have h2 : statementIndex 2 + 1 = 2 := rfl
  have hlt := j.isLt
  by_cases hj0 : j.val = 0
  · exact RungRegular.hreg_rung0 K 2 hn c j hj0
  · have hj1 : j.val = 1 := by omega
    exact RungDiagonal.hreg_rung1_diagonal K 2 hn c j hj1 hdiag
      (hnondeg j hj1)

/-- `ConeNoEmbedded` at rung-2 bridge data from
`[diagonal, nondegeneracy, HdimEqMinAtAss]`: §3
(`coneNoEmbedded_of_hsucc_of_hdimEqMin`) with `hsucc` supplied by
`hsucc_bridgeSystem_rung2_diagonal` (`bridgeSystem` is `mkSystem` at
bridge data by `rfl`-defeq, as in §5).

Conditional on exactly `[hdiag, hnondeg, hdimEq]`. -/
theorem coneNoEmbedded_bridgeForms_rung2_diagonal_of_hdimEqMin (K : Type*)
    [Field K]
    (c : Fin 2 → Fin 2 → Fin 2 → K) (hn : 0 < 2)
    (hdiag : RungDiagonal.IsDiagonal K c)
    (hnondeg : ∀ j : Fin (statementIndex 2 + 1), j.val = 1 →
      bridgeForms 2 K c hn (RungDiagonal.rungI0 2) ≠ 0 ∨
        bridgeForms 2 K c hn j ≠ 0)
    (hdimEq : UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex 2 + 2) K
      (Ideal.span (Set.range (bridgeSystem 2 K c hn)))) :
    R1RegularSection.ConeNoEmbedded (statementIndex 2) K (bridgeForms 2 K c hn) :=
  coneNoEmbedded_of_hsucc_of_hdimEqMin (statementIndex 2) K
    (bridgeForms 2 K c hn)
    (hsucc_bridgeSystem_rung2_diagonal K c hn hdiag hnondeg) hdimEq

/-- Rung-2 `havoid` at bridge data from algebra data +
`[diagonal, nondegeneracy, HdimEqMinAtAss]`: §5 at `n = 2` with `hsucc`
supplied (`hF`/`hcut` discharged from algebra data via `ResidualWiring`,
as in §5).

Conditional on exactly `[hdiag, hnondeg, hdimEq]` given algebra data. -/
theorem havoid_secForm_bridgeForms_rung2_diagonal_of_algebraData_of_hdimEqMin
    (K E : Type*) [Field K] [IsAlgClosed K]
    [NonUnitalNonAssocSemiring E] [Module K E]
    (c : Fin 2 → Fin 2 → Fin 2 → K) (hn : 0 < 2)
    (V : Submodule K E) (b : Module.Basis (Fin 2) K V)
    (hexp : ∀ i j, (b i : E) * (b j : E) = ∑ k, c i j k • (b k : E))
    (hN : absNilpotent K E V = {0})
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E)
    (hdiag : RungDiagonal.IsDiagonal K c)
    (hnondeg : ∀ j : Fin (statementIndex 2 + 1), j.val = 1 →
      bridgeForms 2 K c hn (RungDiagonal.rungI0 2) ≠ 0 ∨
        bridgeForms 2 K c hn j ≠ 0)
    (hdimEq : UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex 2 + 2) K
      (Ideal.span (Set.range (bridgeSystem 2 K c hn)))) :
    ∀ P ∈ associatedPrimes
        (coneQuotient (statementIndex 2) K (bridgeSystem 2 K c hn))
        (coneQuotient (statementIndex 2) K (bridgeSystem 2 K c hn)),
      Ideal.Quotient.mk
        (Ideal.span (Set.range (bridgeSystem 2 K c hn)))
        (mkLin (statementIndex 2) K
          (R1RegularSection.secForm (statementIndex 2) K)) ∉ P :=
  R1RegularSection.havoid_secForm_of_noEmbedded_of_minAvoid (statementIndex 2) K
    (bridgeForms 2 K c hn)
    (coneNoEmbedded_bridgeForms_rung2_diagonal_of_hdimEqMin K c hn hdiag
      hnondeg hdimEq)
    (ResidualWiring.secFormAvoidsMinimal_bridgeForms_of_algebraData K E 2 hn c V b
      hexp hN htower hcomm)

/-- `HdimEqMinAtAss` from an embedding-dimension bound: if every
`Q ∈ Ass(R ⧸ J)` has `spanFinrank 𝔪(R_Q) ≤ 1`, the `2 ≤ d` case is
vacuous (`omega` on the minimality equation). Reframes the `d ≥ 2`
remainder as an embdim bound (= `dim R_Q` by regularity,
`MultiplicityNonvanishing.mult_dim_atPrime_eq_spanFinrank`); at rung `≥ 2`
the bound fails in general (height-2 Ass primes), so this does not
close the crux.
-/
theorem hdimEqMinAtAss_of_embdim_le_one (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hle : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) →
      (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank ≤ 1) :
    UnmixednessAtLengthTwo.HdimEqMinAtAss m K J := by
  intro Q _ hQ d hdmin hd2 Qw hleQ hag
  have h1 := hle Q hQ
  omega

#print axioms hsucc_bridgeSystem_rung1
#print axioms hsucc_mkSystem_zero_uncond
#print axioms coneNoEmbedded_zero_uncond
#print axioms coneNoEmbedded_bridgeForms_rung1_uncond
#print axioms hres2_pair_rung1_of_algebraData
#print axioms hsucc_bridgeSystem_rung2_diagonal
#print axioms coneNoEmbedded_bridgeForms_rung2_diagonal_of_hdimEqMin
#print axioms havoid_secForm_bridgeForms_rung2_diagonal_of_algebraData_of_hdimEqMin
#print axioms hdimEqMinAtAss_of_embdim_le_one

/-! ## §8. Crux-form variants of the §3 master (Q5 integration)

One-line adapter applications: the §3 master
(`coneNoEmbedded_of_hsucc_of_hdimEqMin`) fed with the /52
supply-chain forward lanes, so `ConeNoEmbedded` at general `n` follows
whichever crux form proves — witness (`hwitMin`, the prime mover),
multiplicity (`hmultMin`, no new import: `UnmixednessAtLengthTwo.lean`),
kernel (`hkerMin`), R-2a′ (`grDimEq`), the Hilbert–Samuel lower bound
(`lower`, via the GrDimEq §3b supply adapter), minimal `hle`
(`hhleMin`, via the HighHleMin `hhleMin_iff_lower` iff + the §3b
adapter), and no-high-relations (`noHomRelHighMin`, via the DimToMult
§7 master). The rung-2 diagonal instances on `[hwitMin]` close the
section: `FinalDischargeHub`'s rung-2 pair assembly consumes the `havoid` one.

Status: each conditional-exact on `[hsucc, <named crux input>]`
(§8 general-`n`); rung-2 instances conditional-exact on
`[hdiag, hnondeg, hwit]` (+ algebra data for `havoid`).

## References

* `DimensionToMultiplicity.lean` (`hdimEqMin_of_grDimEq` /
  `hdimEqMin_of_hwitMin` / `hdimEqMin_of_hkerMin` /
  `hdimEqMin_of_noHomRelHighMin`).
* `UnmixednessAtLengthTwo.lean` (`hdimEqMin_of_hmultMin`).
* `GradedDimEq.lean` (`hdimEqMin_of_lower`, §3b supply adapter).
* `HighRelationsLowerBound.lean` (`hhleMin_iff_lower`).
-/

/-- `ConeNoEmbedded` at general `n` from `[hsucc, HwitMinAtAss]`: the §3
master via `hdimEqMin_of_hwitMin`.

Conditional on exactly `[hsucc, hwit]`. -/
theorem coneNoEmbedded_of_hsucc_of_hwitMin
    (n : ℕ) (K : Type*) [Field K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular (mkSystem n K F))
    (hwit : UnmixednessAtLengthTwo.HwitMinAtAss (n + 2) K
      (Ideal.span (Set.range (mkSystem n K F)))) :
    R1RegularSection.ConeNoEmbedded n K F :=
  coneNoEmbedded_of_hsucc_of_hdimEqMin n K F hsucc
    (DimensionToMultiplicity.hdimEqMin_of_hwitMin _ _ _ hwit)

/-- `ConeNoEmbedded` at general `n` from `[hsucc, HmultMinAtAss]`: the §3
master via `hdimEqMin_of_hmultMin`.

Conditional on exactly `[hsucc, hmult]`. -/
theorem coneNoEmbedded_of_hsucc_of_hmultMin
    (n : ℕ) (K : Type*) [Field K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular (mkSystem n K F))
    (hmult : UnmixednessAtLengthTwo.HmultMinAtAss (n + 2) K
      (Ideal.span (Set.range (mkSystem n K F)))) :
    R1RegularSection.ConeNoEmbedded n K F :=
  coneNoEmbedded_of_hsucc_of_hdimEqMin n K F hsucc
    (UnmixednessAtLengthTwo.hdimEqMin_of_hmultMin _ _ _ hmult)

/-- `ConeNoEmbedded` at general `n` from `[hsucc, HkerMinAtAss]`: the §3
master via `hdimEqMin_of_hkerMin` (goal-strength).

Conditional on exactly `[hsucc, hker]`. -/
theorem coneNoEmbedded_of_hsucc_of_hkerMin
    (n : ℕ) (K : Type*) [Field K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular (mkSystem n K F))
    (hker : UnmixednessAtLengthTwo.HkerMinAtAss (n + 2) K
      (Ideal.span (Set.range (mkSystem n K F)))) :
    R1RegularSection.ConeNoEmbedded n K F :=
  coneNoEmbedded_of_hsucc_of_hdimEqMin n K F hsucc
    (DimensionToMultiplicity.hdimEqMin_of_hkerMin _ _ _ hker)

/-- `ConeNoEmbedded` at general `n` from `[hsucc, R-2a′]`: the §3 master
via `hdimEqMin_of_grDimEq`.

Conditional on exactly `[hsucc, hgr]`. -/
theorem coneNoEmbedded_of_hsucc_of_grDimEqMin
    (n : ℕ) (K : Type*) [Field K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular (mkSystem n K F))
    (hgr : DimensionToMultiplicity.HgrDimEqMinAtAss (n + 2) K
      (Ideal.span (Set.range (mkSystem n K F)))) :
    R1RegularSection.ConeNoEmbedded n K F :=
  coneNoEmbedded_of_hsucc_of_hdimEqMin n K F hsucc
    (DimensionToMultiplicity.hdimEqMin_of_grDimEq _ _ _ hgr)

/-- `ConeNoEmbedded` at general `n` from `[hsucc, lower bound]`: the §3
master via the GrDimEq §3b supply adapter `hdimEqMin_of_lower`.

Conditional on exactly `[hsucc, hlower]`. -/
theorem coneNoEmbedded_of_hsucc_of_lower
    (n : ℕ) (K : Type*) [Field K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular (mkSystem n K F))
    (hlower : GradedDimEq.HgrDimLowerMinAtAss (n + 2) K
      (Ideal.span (Set.range (mkSystem n K F)))) :
    R1RegularSection.ConeNoEmbedded n K F :=
  coneNoEmbedded_of_hsucc_of_hdimEqMin n K F hsucc
    (GradedDimEq.hdimEqMin_of_lower _ _ _ hlower)

/-- `ConeNoEmbedded` at general `n` from `[hsucc, HhleMinAtAss]`: the §3
master via `hhleMin_iff_lower` + the §3b supply adapter.

Conditional on exactly `[hsucc, hhle]`. -/
theorem coneNoEmbedded_of_hsucc_of_hhleMin
    (n : ℕ) (K : Type*) [Field K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular (mkSystem n K F))
    (hhle : HighRelationsLowerBound.HhleMinAtAss (n + 2) K
      (Ideal.span (Set.range (mkSystem n K F)))) :
    R1RegularSection.ConeNoEmbedded n K F :=
  coneNoEmbedded_of_hsucc_of_hdimEqMin n K F hsucc
    (GradedDimEq.hdimEqMin_of_lower _ _ _
      ((HighRelationsLowerBound.hhleMin_iff_lower _ _ _).mp hhle))

/-- `ConeNoEmbedded` at general `n` from `[hsucc, no-hom-rel-high]`: the
§3 master via the DimToMult §7 master `hdimEqMin_of_noHomRelHighMin`.

Conditional on exactly `[hsucc, hHigh]`. -/
theorem coneNoEmbedded_of_hsucc_of_noHomRelHighMin
    (n : ℕ) (K : Type*) [Field K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular (mkSystem n K F))
    (hHigh : DimensionToMultiplicity.HnoHomRelHighMinAtAss (n + 2) K
      (Ideal.span (Set.range (mkSystem n K F)))) :
    R1RegularSection.ConeNoEmbedded n K F :=
  coneNoEmbedded_of_hsucc_of_hdimEqMin n K F hsucc
    (DimensionToMultiplicity.hdimEqMin_of_noHomRelHighMin _ _ _ hHigh)

/-- `ConeNoEmbedded` at rung-2 bridge data from
`[diagonal, nondegeneracy, HwitMinAtAss]`: the §8 `hwitMin` variant with
`hsucc` supplied by `hsucc_bridgeSystem_rung2_diagonal`.

Conditional on exactly `[hdiag, hnondeg, hwit]`. -/
theorem coneNoEmbedded_bridgeForms_rung2_diagonal_of_hwitMin (K : Type*)
    [Field K]
    (c : Fin 2 → Fin 2 → Fin 2 → K) (hn : 0 < 2)
    (hdiag : RungDiagonal.IsDiagonal K c)
    (hnondeg : ∀ j : Fin (statementIndex 2 + 1), j.val = 1 →
      bridgeForms 2 K c hn (RungDiagonal.rungI0 2) ≠ 0 ∨
        bridgeForms 2 K c hn j ≠ 0)
    (hwit : UnmixednessAtLengthTwo.HwitMinAtAss (statementIndex 2 + 2) K
      (Ideal.span (Set.range (bridgeSystem 2 K c hn)))) :
    R1RegularSection.ConeNoEmbedded (statementIndex 2) K (bridgeForms 2 K c hn) :=
  coneNoEmbedded_of_hsucc_of_hwitMin (statementIndex 2) K
    (bridgeForms 2 K c hn)
    (hsucc_bridgeSystem_rung2_diagonal K c hn hdiag hnondeg) hwit

/-- Rung-2 `havoid` at bridge data from algebra data +
`[diagonal, nondegeneracy, HwitMinAtAss]`: the §5 package at `n = 2`
with `hsucc` supplied and `hwit` adapted (one-line §8 application).

Conditional on exactly `[hdiag, hnondeg, hwit]` given algebra data. -/
theorem havoid_secForm_bridgeForms_rung2_diagonal_of_algebraData_of_hwitMin
    (K E : Type*) [Field K] [IsAlgClosed K]
    [NonUnitalNonAssocSemiring E] [Module K E]
    (c : Fin 2 → Fin 2 → Fin 2 → K) (hn : 0 < 2)
    (V : Submodule K E) (b : Module.Basis (Fin 2) K V)
    (hexp : ∀ i j, (b i : E) * (b j : E) = ∑ k, c i j k • (b k : E))
    (hN : absNilpotent K E V = {0})
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E)
    (hdiag : RungDiagonal.IsDiagonal K c)
    (hnondeg : ∀ j : Fin (statementIndex 2 + 1), j.val = 1 →
      bridgeForms 2 K c hn (RungDiagonal.rungI0 2) ≠ 0 ∨
        bridgeForms 2 K c hn j ≠ 0)
    (hwit : UnmixednessAtLengthTwo.HwitMinAtAss (statementIndex 2 + 2) K
      (Ideal.span (Set.range (bridgeSystem 2 K c hn)))) :
    ∀ P ∈ associatedPrimes
        (coneQuotient (statementIndex 2) K (bridgeSystem 2 K c hn))
        (coneQuotient (statementIndex 2) K (bridgeSystem 2 K c hn)),
      Ideal.Quotient.mk
        (Ideal.span (Set.range (bridgeSystem 2 K c hn)))
        (mkLin (statementIndex 2) K
          (R1RegularSection.secForm (statementIndex 2) K)) ∉ P :=
  havoid_secForm_bridgeForms_of_algebraData_of_hsucc_of_hdimEqMin K E 2 hn c
    V b hexp hN htower hcomm
    (hsucc_bridgeSystem_rung2_diagonal K c hn hdiag hnondeg)
    (DimensionToMultiplicity.hdimEqMin_of_hwitMin _ _ _ hwit)

#print axioms coneNoEmbedded_of_hsucc_of_hwitMin
#print axioms coneNoEmbedded_of_hsucc_of_hmultMin
#print axioms coneNoEmbedded_of_hsucc_of_hkerMin
#print axioms coneNoEmbedded_of_hsucc_of_grDimEqMin
#print axioms coneNoEmbedded_of_hsucc_of_lower
#print axioms coneNoEmbedded_of_hsucc_of_hhleMin
#print axioms coneNoEmbedded_of_hsucc_of_noHomRelHighMin
#print axioms coneNoEmbedded_bridgeForms_rung2_diagonal_of_hwitMin
#print axioms havoid_secForm_bridgeForms_rung2_diagonal_of_algebraData_of_hwitMin

end ConeNoEmbeddedRungs
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
