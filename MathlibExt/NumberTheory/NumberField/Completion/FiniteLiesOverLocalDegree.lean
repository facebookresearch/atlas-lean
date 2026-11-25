/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.AdeleLocallyCompact
public import MathlibExt.NumberTheory.NumberField.Completion.FiniteLiesOverInstances
public import MathlibExt.NumberTheory.NumberField.Completion.FiniteLiesOverRamificationIndex
public import MathlibExt.RingTheory.DiscreteValuationRing.IntegralClosureComplete
public import Mathlib.RingTheory.RamificationInertia.Basic
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.FieldTheory.Perfect

@[expose] public section

namespace IsDedekindDomain.HeightOneSpectrum

open scoped WithZero NumberField NumberField.LiesOver

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

/-!
# The local degree formula

This file formalizes part (4) of ATLAS `NumberTheoryI` target N236, Theorem 11.23,
which is a local-degree prerequisite used later for target N265, Theorem 13.5:
for a prime `w` of `L` above a prime `v` of `K`, the completion degree satisfies
`[L_w : K_v] = e_w f_w`. At atlas-lean revision
`e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`, see the
[Theorem 11.23 target, lines 1668--1684](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/targets.yaml#L1668-L1684)
and the primary Lean theorem
[`thm_11_23_part4_completion_degree_eq_ef`, lines 2403--2460](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/KroneckerWeber.lean#L2403-L2460).
Its local-ring calculation is isolated as
[`thm_5_35_completion_degree_eq_local_ef`, lines 1748--1792](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/KroneckerWeber.lean#L1748-L1792).

## Source-to-API map

Here `v.adicCompletion K` and `w.adicCompletion L` are the source fields
`K_v` and `L_w`, so `Module.finrank` is their extension degree. The source's
global ramification index `Ideal.ramificationIdx v.asIdeal w.asIdeal` and residue
degree `Ideal.inertiaDeg v.asIdeal w.asIdeal` are respectively
`w.asIdeal.ramificationIdx (𝓞 K)` and `w.asIdeal.inertiaDeg (𝓞 K)` below; the
`LiesOver` instance records `w ∣ v`.

The proof follows the same local argument. It applies the ramification--inertia
sum formula to the finite extension of completion integer rings, collapses the
sum because a local ring has a unique maximal ideal, identifies the resulting
integer-ring rank with the fraction-field rank, and then uses the established
completion-preservation theorems for `e` and `f`. Thus the conclusion is the
source equality itself, not merely the unramified special case `e = f = 1`.
Parts (1)--(3), (5), and (6) of Theorem 11.23 are outside this theorem's scope.
-/

/-- **The local degree is the product of ramification index and inertia degree.** Let $L/K$ be an
extension of number fields, let $v$ be a nonzero prime ideal of $\mathcal{O}_K$ (a finite place of
$K$) and $w$ a nonzero prime ideal of $\mathcal{O}_L$ lying over $v$. Regard the completion $L_w$
as an algebra over $K_v$ via the canonical map $K_v \to L_w$. Then the dimension of $L_w$ over
$K_v$ equals $e(w \mid v) \, f(w \mid v)$, the ramification index of $w$ over $v$ times the
inertia degree of $w$ over $v$. -/
theorem finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg :
    Module.finrank (v.adicCompletion K) (w.adicCompletion L) =
      w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K) := by
  have halg : algebraMap (v.adicCompletionIntegers K)
      (w.adicCompletionIntegers L) = adicCompletionIntegersMap v w := rfl
  let _ : IsScalarTower (v.adicCompletionIntegers K)
      (w.adicCompletionIntegers L) (w.adicCompletion L) :=
    IsScalarTower.of_algebraMap_eq (by
      intro x
      rw [IsScalarTower.algebraMap_apply (v.adicCompletionIntegers K)
        (v.adicCompletion K) (w.adicCompletion L)]
      rfl)
  let _ : FaithfulSMul (v.adicCompletionIntegers K)
      (w.adicCompletionIntegers L) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (halg ▸ adicCompletionIntegersMap_injective v w)
  let _ : Module.IsTorsionFree (v.adicCompletionIntegers K)
      (w.adicCompletionIntegers L) := inferInstance
  let _ : Module.Flat (v.adicCompletionIntegers K)
      (w.adicCompletionIntegers L) := inferInstance
  let _ : IsLocalHom (algebraMap (v.adicCompletionIntegers K)
      (w.adicCompletionIntegers L)) :=
    IsLocalHom.mk (fun x hx => by
      by_contra hxnu
      have hxmem : x ∈ IsLocalRing.maximalIdeal
          (v.adicCompletionIntegers K) :=
        (IsLocalRing.mem_maximalIdeal x).mpr ((mem_nonunits_iff).mpr hxnu)
      have hcomap := comap_maximalIdeal_adicCompletionIntegersMap v w
      have himg : algebraMap (v.adicCompletionIntegers K)
          (w.adicCompletionIntegers L) x ∈ IsLocalRing.maximalIdeal
          (w.adicCompletionIntegers L) := by
        rw [halg]
        have hmem : x ∈ Ideal.comap (adicCompletionIntegersMap v w)
            (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L)) := by
          rw [hcomap]
          exact hxmem
        exact hmem
      exact (((mem_nonunits_iff).mp ((IsLocalRing.mem_maximalIdeal _).mp himg)) hx))
  let _ : CharZero (v.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  let _ : PerfectField (v.adicCompletion K) := PerfectField.ofCharZero
  let _ : Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L) :=
    inferInstance
  let eR : ↥((w.adicCompletionIntegers L).valuation.integer) ≃+*
      w.adicCompletionIntegers L :=
    RingEquiv.subringCongr
      (ValuationSubring.integer_valuation (w.adicCompletionIntegers L))
  let _ : Algebra (v.adicCompletionIntegers K)
      ↥((w.adicCompletionIntegers L).valuation.integer) :=
    (eR.symm.toRingHom.comp (algebraMap (v.adicCompletionIntegers K)
      (w.adicCompletionIntegers L))).toAlgebra
  let e : ↥((w.adicCompletionIntegers L).valuation.integer)
      ≃ₐ[v.adicCompletionIntegers K] w.adicCompletionIntegers L :=
    { eR with commutes' := fun r => rfl }
  let _ : IsScalarTower (v.adicCompletionIntegers K)
      ↥((w.adicCompletionIntegers L).valuation.integer)
      (w.adicCompletion L) :=
    IsScalarTower.of_algebraMap_eq (by
      intro x
      rw [IsScalarTower.algebraMap_apply (v.adicCompletionIntegers K)
        (w.adicCompletionIntegers L) (w.adicCompletion L)]
      rfl)
  let _ : IsLocalHom eR.symm.toRingHom :=
    eR.symm.surjective.isLocalHom
  let _ : IsLocalHom (algebraMap (v.adicCompletionIntegers K)
      ↥((w.adicCompletionIntegers L).valuation.integer)) :=
    RingHom.isLocalHom_comp _ _
  have hfin : Module.Finite (v.adicCompletionIntegers K)
      ((w.adicCompletionIntegers L).valuation.integer) :=
    Valuation.module_finite_integer_of_isAdicComplete
      (v.adicCompletionIntegers K) (v.adicCompletion K)
      (w.adicCompletion L) _ (w.adicCompletionIntegers L).valuation
  let _ : Module.Finite (v.adicCompletionIntegers K)
      (w.adicCompletionIntegers L) := Module.Finite.equiv e.toLinearEquiv
  have hprimes : Ideal.primesOver (IsLocalRing.maximalIdeal
      (v.adicCompletionIntegers K)) (w.adicCompletionIntegers L) =
      {IsLocalRing.maximalIdeal (w.adicCompletionIntegers L)} :=
    IsLocalRing.primesOver_eq (R := v.adicCompletionIntegers K)
      (w.adicCompletionIntegers L)
      (IsDiscreteValuationRing.not_a_field (v.adicCompletionIntegers K))
  have hsum := Ideal.sum_ramification_inertia_eq_finrank
    (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
    (w.adicCompletionIntegers L)
  have hmem : IsLocalRing.maximalIdeal (w.adicCompletionIntegers L) ∈
      Ideal.primesOver (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
        (w.adicCompletionIntegers L) := by
    rw [hprimes]
    exact Set.mem_singleton _
  let _ : Unique (Ideal.primesOver (IsLocalRing.maximalIdeal
      (v.adicCompletionIntegers K)) (w.adicCompletionIntegers L)) :=
    { default := ⟨_, hmem⟩
      uniq := fun q =>
        Subtype.ext (Set.mem_singleton_iff.mp (hprimes ▸ q.property)) }
  rw [Fintype.sum_unique] at hsum
  have hlocal : (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L)).ramificationIdx
      (v.adicCompletionIntegers K) *
      (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L)).inertiaDeg
      (v.adicCompletionIntegers K) =
      Module.finrank (v.adicCompletionIntegers K)
        (w.adicCompletionIntegers L) := hsum
  rw [IsFractionRing.finrank_eq (v.adicCompletionIntegers K) (v.adicCompletion K)
    (w.adicCompletionIntegers L) (w.adicCompletion L), ← hlocal,
    ramificationIdx_adicCompletionIntegersMap v w,
    inertiaDeg_adicCompletionIntegersMap v w]

end HeightOneSpectrum

end IsDedekindDomain
