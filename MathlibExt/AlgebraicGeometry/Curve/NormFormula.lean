/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from the following files of the FLT project
(https://github.com/anthropics/fermats-last-theorem):
`Theorems/Thm_AlgebraicCurve_N.lean` and `P2M/Sol/S_AlgebraicCurve_N.lean`
for each `N` in:
`Divisor_evalFun_algebraMap_pushforward`;
`Place_evalAt_norm_eq_prod_fiber`;
`Divisor_evalFun_pullback`;
`Divisor_pushforwardNormFormula`;
`Divisor_pushforward_div`;
`Place_ord_norm_eq_sum_fiberOver`;
`Place_ord_norm_eq_zero_of_forall_fiber`.
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.RingTheory.Ideal.Norm.RelNorm
public import Mathlib.RingTheory.Valuation.LocalSubring
public import MathlibExt.AlgebraicGeometry.Curve.PlaceExtension
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import MathlibExt.RingTheory.NormTrace.Prod

/-!
# Norms, divisors and evaluation along a finite separable extension

For a finite separable extension `F' / F` of function fields over `K`, the order of the norm
`N(f)` at a place `v` of `F` is the sum of `e(w|v) f(w|v) ord_w f` over the places `w` above
`v`, so the pushforward of `div f` is `div (N f)`. When the places involved are rational, the
value of `N(f)` at `v` is the product of the values of `f` at the places above `v`.
-/

@[expose] public section

noncomputable section

section

open AlgebraicCurve AlgebraicCurve.Divisor

private theorem zpow_finset_sum' {K : Type*} [Field K] {c : K} (hc : c ≠ 0) {ι : Type*}
    (s : Finset ι) (n : ι → ℤ) : ∏ i ∈ s, c ^ n i = c ^ (∑ i ∈ s, n i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.prod_cons, Finset.sum_cons, zpow_add₀ hc, ih]

theorem AlgebraicCurve.Divisor.evalFun_algebraMap_pushforward {K F F' : Type*} [Field K] [Field F]
    [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [Algebra.IsIntegral F F'] {g : F} (hg : g ≠ 0) (D : Divisor K F')
    (hratw : ∀ w ∈ D.support, Place.IsRational w)
    (hratv : ∀ w ∈ D.support, (w.restrict F).IsRational)
    (hord : ∀ w ∈ D.support, (w.restrict F).ord g = 0) : Divisor.evalFun (algebraMap F F' g) D =
    Divisor.evalFun g (Divisor.pushforward F D) := by
  classical
  have hstep1 : evalFun (algebraMap F F' g) D
      = ∏ w ∈ D.support, (w.restrict F).evalAt g ^ D w := by
    rw [evalFun_def]
    refine Finset.prod_congr rfl fun w hw => ?_
    rw [w.evalAt_algebraMap_eq_evalAt_restrict (hratv w hw)
      ((w.restrict F).mem_of_ord_nonneg hg (hord w hw).ge)]
  have hne : ∀ w ∈ D.support, (w.restrict F).evalAt g ≠ 0 := fun w hw =>
    (w.restrict F).evalAt_ne_zero (hratv w hw) hg (hord w hw)
  have hstep2 : ∏ w ∈ D.support, (w.restrict F).evalAt g ^ D w
      = ∏ v ∈ D.support.image (fun w => w.restrict F),
          ∏ w ∈ D.support with w.restrict F = v, (w.restrict F).evalAt g ^ D w :=
    (Finset.prod_fiberwise_of_maps_to
      (fun w hw => Finset.mem_image.mpr ⟨w, hw, rfl⟩) _).symm
  have hstep3 : ∀ v ∈ D.support.image (fun w => w.restrict F),
      (∏ w ∈ D.support with w.restrict F = v, (w.restrict F).evalAt g ^ D w)
        = v.evalAt g ^ (pushforward F D v) := by
    intro v hv
    obtain ⟨w₀, hw₀, rfl⟩ := Finset.mem_image.mp hv
    calc
      ∏ w ∈ D.support with w.restrict F = w₀.restrict F, (w.restrict F).evalAt g ^ D w
          = ∏ w ∈ D.support with w.restrict F = w₀.restrict F,
              (w₀.restrict F).evalAt g ^ (D w * (w.inertiaDeg F : ℤ)) := by
            refine Finset.prod_congr rfl fun w hw => ?_
            obtain ⟨hwD, hwv⟩ := Finset.mem_filter.mp hw
            rw [hwv, w.inertiaDeg_eq_one_of_isRational (hratw w hwD) (hratv w hwD),
              Nat.cast_one, mul_one]
      _ = (w₀.restrict F).evalAt g
            ^ (∑ w ∈ D.support with w.restrict F = w₀.restrict F,
                D w * (w.inertiaDeg F : ℤ)) :=
            zpow_finset_sum' (hne w₀ hw₀) _ _
      _ = (w₀.restrict F).evalAt g ^ (pushforward F D (w₀.restrict F)) := by
            rw [pushforward_apply, Finset.sum_filter]
  rw [hstep1, hstep2, Finset.prod_congr rfl hstep3]
  exact (Finsupp.prod_of_support_subset _ (support_pushforward_subset D)
    (fun v n => v.evalAt g ^ n) fun v _ => zpow_zero _).symm

end

section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

section

open IsDedekindDomain WithZero IsLocalRing UniqueFactorizationMonoid

section

open IsDedekindDomain IsLocalRing UniqueFactorizationMonoid

namespace AlgebraicCurve

attribute [local instance 0] Place.valuationSubringAlgebra

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [CharZero F]

namespace Place

variable (v : Place K F)

scoped instance : Module.Free v.toValuationSubring (integralClosureAt F' v) :=
  Module.free_of_finite_type_torsion_free'

abbrev conductorIdeal : Ideal (integralClosureAt F' v) :=
  (IsLocalRing.maximalIdeal v.toValuationSubring).map
    (algebraMap v.toValuationSubring (integralClosureAt F' v))

omit [Algebra K F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F']
  [CharZero F] in

omit [Algebra K F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F']
  [CharZero F] in

theorem conductorIdeal_ne_bot : conductorIdeal (F' := F') v ≠ ⊥ := by
  intro h
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  have hπmem : algebraMap v.toValuationSubring (integralClosureAt F' v) π
      ∈ conductorIdeal (F' := F') v :=
    Ideal.mem_map_of_mem _ (hπ.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π)
  rw [h, Ideal.mem_bot] at hπmem
  exact hπ.ne_zero (algebraMap_integralClosureAt_injective v (by rw [hπmem, map_zero]))

noncomputable scoped instance conductorQuotientAlgebra :
    Algebra (IsLocalRing.ResidueField v.toValuationSubring)
      (integralClosureAt F' v ⧸ conductorIdeal (F' := F') v) :=
  Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map

omit [Algebra K F'] [IsScalarTower K F F'] [CharZero F] in

theorem residue_norm_eq_norm_mk (c : integralClosureAt F' v) :
    IsLocalRing.residue v.toValuationSubring
        (Algebra.norm v.toValuationSubring c)
      = Algebra.norm (IsLocalRing.ResidueField v.toValuationSubring)
          (Ideal.Quotient.mk (conductorIdeal (F' := F') v) c) := by

  have key : algebraMap v.toValuationSubring
      (v.toValuationSubring ⧸ IsLocalRing.maximalIdeal v.toValuationSubring)
        (Algebra.norm v.toValuationSubring c)
      = Algebra.norm
          (v.toValuationSubring ⧸ IsLocalRing.maximalIdeal v.toValuationSubring)
          (Ideal.Quotient.mk (conductorIdeal (F' := F') v) c) := by

    have hequiv := Algebra.norm_eq_of_algEquiv
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor (A := v.toValuationSubring)
        (integralClosureAt F' v) (IsLocalRing.maximalIdeal v.toValuationSubring))
      (Ideal.Quotient.mk (conductorIdeal (F' := F') v) c)
    rw [Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk] at hequiv

    have hbase : algebraMap v.toValuationSubring
        (v.toValuationSubring ⧸ IsLocalRing.maximalIdeal v.toValuationSubring)
          (Algebra.norm v.toValuationSubring c)
          = Algebra.norm
              (v.toValuationSubring ⧸ IsLocalRing.maximalIdeal v.toValuationSubring)
              ((1 : v.toValuationSubring ⧸ IsLocalRing.maximalIdeal v.toValuationSubring)
                ⊗ₜ[v.toValuationSubring] c) := by
      rw [Algebra.norm_apply, Algebra.norm_apply, ← Algebra.baseChange_lmul,
        LinearMap.det_baseChange]
    exact hbase.trans hequiv
  exact key

end Place

namespace Place

variable {v : Place K F} {w : Place K F'}

abbrev fiberCenterPow (hw : w.restrict F = v) : Ideal (integralClosureAt F' v) :=
  (fiberCenter F' v hw).asIdeal
    ^ (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx'
        (fiberCenter F' v hw).asIdeal

omit [CharZero F] in

theorem conductorIdeal_le_fiberCenterPow (hw : w.restrict F = v) :
    conductorIdeal (F' := F') v ≤ fiberCenterPow hw :=
  Ideal.le_pow_ramificationIdx

noncomputable scoped instance fiberCenterPowQuotientAlgebra (hw : w.restrict F = v) :
    Algebra (IsLocalRing.ResidueField v.toValuationSubring)
      (integralClosureAt F' v ⧸ fiberCenterPow hw) :=
  Ideal.Quotient.algebraQuotientOfLEComap
    (Ideal.map_le_iff_le_comap.mp (conductorIdeal_le_fiberCenterPow hw))

scoped instance (hw : w.restrict F = v) :
    Module.Finite (IsLocalRing.ResidueField v.toValuationSubring)
      (integralClosureAt F' v ⧸ fiberCenterPow hw) := by
  haveI : IsScalarTower v.toValuationSubring
      (IsLocalRing.ResidueField v.toValuationSubring)
      (integralClosureAt F' v ⧸ fiberCenterPow hw) := IsScalarTower.of_algebraMap_eq' rfl
  exact Module.Finite.of_restrictScalars_finite v.toValuationSubring
    (IsLocalRing.ResidueField v.toValuationSubring)
    (integralClosureAt F' v ⧸ fiberCenterPow hw)

omit [CharZero F] in

theorem isNilpotent_mk_sub_algebraMap (hw : w.restrict F = v) {c : integralClosureAt F' v}
    {r : v.toValuationSubring}
    (hr : c - algebraMap v.toValuationSubring (integralClosureAt F' v) r
      ∈ (fiberCenter F' v hw).asIdeal) :
    IsNilpotent (Ideal.Quotient.mk (fiberCenterPow hw) c
      - algebraMap (IsLocalRing.ResidueField v.toValuationSubring)
          (integralClosureAt F' v ⧸ fiberCenterPow hw)
          (IsLocalRing.residue v.toValuationSubring r)) := by

  have halg : algebraMap (IsLocalRing.ResidueField v.toValuationSubring)
      (integralClosureAt F' v ⧸ fiberCenterPow hw) (IsLocalRing.residue v.toValuationSubring r)
        = Ideal.Quotient.mk (fiberCenterPow hw)
            (algebraMap v.toValuationSubring (integralClosureAt F' v) r) := rfl
  rw [halg, ← map_sub]

  refine ⟨(IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx'
    (fiberCenter F' v hw).asIdeal, ?_⟩
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.pow_mem_pow hr _

omit [CharZero F] in

theorem norm_mk_fiberCenterPow (hw : w.restrict F = v) {c : integralClosureAt F' v}
    {r : v.toValuationSubring}
    (hr : c - algebraMap v.toValuationSubring (integralClosureAt F' v) r
      ∈ (fiberCenter F' v hw).asIdeal) :
    Algebra.norm (IsLocalRing.ResidueField v.toValuationSubring)
        (Ideal.Quotient.mk (fiberCenterPow hw) c)
      = IsLocalRing.residue v.toValuationSubring r
          ^ Module.finrank (IsLocalRing.ResidueField v.toValuationSubring)
              (integralClosureAt F' v ⧸ fiberCenterPow hw) :=
  Algebra.norm_eq_pow_finrank_of_isNilpotent_sub_algebraMap
    (isNilpotent_mk_sub_algebraMap hw hr)

omit [CharZero F] in

theorem finrank_fiberCenterPow (hw : w.restrict F = v) (hwrat : w.IsRational)
    (hvrat : v.IsRational) :
    Module.finrank (IsLocalRing.ResidueField v.toValuationSubring)
        (integralClosureAt F' v ⧸ fiberCenterPow hw)
      = w.ramificationIndex F := by
  haveI : (fiberCenter F' v hw).asIdeal.IsMaximal :=
    (fiberCenter F' v hw).isPrime.isMaximal (fiberCenter F' v hw).ne_bot
  have hne : (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx'
      (fiberCenter F' v hw).asIdeal ≠ 0 := by
    rw [← ramificationIndex_eq_ramificationIdx_fiberCenter _ hw]
    exact w.ramificationIndex_pos.ne'

  haveI := fiberCenter_liesOver hw
  have key : Module.finrank
      (v.toValuationSubring ⧸ IsLocalRing.maximalIdeal v.toValuationSubring)
      (integralClosureAt F' v ⧸ (fiberCenter F' v hw).asIdeal
        ^ (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx'
            (fiberCenter F' v hw).asIdeal) = w.ramificationIndex F := by
    rw [Ideal.finrank_prime_pow_ramificationIdx _ _ (fiberCenter F' v hw).ne_bot hne,
      ← Ideal.inertiaDeg_algebraMap, ← inertiaDeg_eq_inertiaDeg_fiberCenter _ hw,
      w.inertiaDeg_eq_one_of_isRational hwrat (hw.symm ▸ hvrat), mul_one,
      ← ramificationIndex_eq_ramificationIdx_fiberCenter _ hw]
  exact key

end Place

namespace Place

variable (v : Place K F)

local instance : DecidableEq (Place K F') := Classical.decEq _

omit [CharZero F] in

def fiberIdeal (w : Place K F') : Ideal (integralClosureAt F' v) :=
  if hw : w.restrict F = v then fiberCenterPow hw else ⊤

omit [CharZero F] in
theorem fiberIdeal_of_mem {w : Place K F'} (hw : w.restrict F = v) :
    fiberIdeal v w = fiberCenterPow hw := dif_pos hw

omit [CharZero F] in
theorem fiberIdeal_of_notMem {w : Place K F'} (hw : ¬w.restrict F = v) :
    fiberIdeal v w = ⊤ := dif_neg hw

omit [CharZero F] in

theorem conductorIdeal_le_fiberIdeal (w : Place K F') :
    conductorIdeal (F' := F') v ≤ fiberIdeal v w := by
  by_cases hw : w.restrict F = v
  · rw [fiberIdeal_of_mem v hw]
    exact conductorIdeal_le_fiberCenterPow hw
  · rw [fiberIdeal_of_notMem v hw]
    exact le_top

omit [CharZero F] in

theorem isCoprime_fiberIdeal {w w' : Place K F'} (hne : w ≠ w') :
    IsCoprime (fiberIdeal v w) (fiberIdeal v w') := by
  by_cases hw : w.restrict F = v
  · by_cases hw' : w'.restrict F = v
    · rw [fiberIdeal_of_mem v hw, fiberIdeal_of_mem v hw']
      haveI : (fiberCenter F' v hw).asIdeal.IsMaximal :=
        (fiberCenter F' v hw).isPrime.isMaximal (fiberCenter F' v hw).ne_bot
      haveI : (fiberCenter F' v hw').asIdeal.IsMaximal :=
        (fiberCenter F' v hw').isPrime.isMaximal (fiberCenter F' v hw').ne_bot
      refine IsCoprime.pow (Ideal.isCoprime_of_isMaximal ?_)
      intro heq
      exact hne (eq_of_fiberCenter_eq hw hw' (HeightOneSpectrum.ext heq))
    · rw [fiberIdeal_of_notMem v hw', ← Ideal.one_eq_top]
      exact isCoprime_one_right
  · rw [fiberIdeal_of_notMem v hw, ← Ideal.one_eq_top]
    exact isCoprime_one_left

omit [CharZero F] in

theorem count_normalizedFactors_conductorIdeal {w : Place K F'} (hw : w.restrict F = v) :
    (normalizedFactors (conductorIdeal (F' := F') v)).count (fiberCenter F' v hw).asIdeal
      = (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx'
          (fiberCenter F' v hw).asIdeal := by
  haveI : (fiberCenter F' v hw).asIdeal.IsPrime := (fiberCenter F' v hw).isPrime
  exact (Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count
    (conductorIdeal_ne_bot (F' := F') v) inferInstance (fiberCenter F' v hw).ne_bot).symm

omit [CharZero F] in

theorem conductorIdeal_eq_prod_fiber :
    conductorIdeal (F' := F') v = ∏ w ∈ v.fiber F', fiberIdeal v w := by
  classical
  have hbot := conductorIdeal_ne_bot (F' := F') v
  set S : Multiset (Ideal (integralClosureAt F' v)) := normalizedFactors (conductorIdeal v)
    with hS

  have hfactor : ∀ Q ∈ S.toFinset, ∃ w' : Place K F', ∃ hw' : w'.restrict F = v,
      (fiberCenter F' v hw').asIdeal = Q := by
    intro Q hQ
    rw [Multiset.mem_toFinset] at hQ
    have hQprime : Prime Q := prime_of_normalized_factor Q hQ
    have hQbot : Q ≠ ⊥ := hQprime.ne_zero
    haveI : Q.IsPrime := Ideal.isPrime_of_prime hQprime
    exact ⟨placeOfPrime ⟨Q, inferInstance, hQbot⟩, restrict_placeOfPrime _,
      congrArg HeightOneSpectrum.asIdeal (fiberCenter_placeOfPrime
        (⟨Q, inferInstance, hQbot⟩ : HeightOneSpectrum (integralClosureAt F' v)))⟩

  set T : Finset (Ideal (integralClosureAt F' v)) := (v.fiber F').attach.image
    (fun w' => (fiberCenter F' v (mem_fiber.mp w'.2)).asIdeal) with hT
  have hsub : S.toFinset ⊆ T := by
    intro Q hQ
    obtain ⟨w', hw', rfl⟩ := hfactor Q hQ
    exact Finset.mem_image.mpr ⟨⟨w', mem_fiber.mpr hw'⟩, Finset.mem_attach _ _, rfl⟩
  have hinj : Set.InjOn (fun w' : {x // x ∈ v.fiber F'} =>
      (fiberCenter F' v (mem_fiber.mp w'.2)).asIdeal) (v.fiber F').attach := by
    intro w₁ _ w₂ _ h
    exact Subtype.ext (eq_of_fiberCenter_eq (mem_fiber.mp w₁.2) (mem_fiber.mp w₂.2)
      (HeightOneSpectrum.ext h))

  calc
    conductorIdeal (F' := F') v = ∏ Q ∈ S.toFinset, Q ^ S.count Q := by
          rw [← Finset.prod_multiset_count, hS, Ideal.prod_normalizedFactors_eq_self hbot]
    _ = ∏ Q ∈ T, Q ^ S.count Q := by
          refine Finset.prod_subset hsub fun Q _ hQ => ?_
          rw [Multiset.count_eq_zero_of_notMem
            (fun h => hQ (Multiset.mem_toFinset.mpr h)), pow_zero]
    _ = ∏ w' ∈ (v.fiber F').attach,
          (fiberCenter F' v (mem_fiber.mp w'.2)).asIdeal
            ^ S.count (fiberCenter F' v (mem_fiber.mp w'.2)).asIdeal := by
          rw [hT, Finset.prod_image hinj]
    _ = ∏ w' ∈ (v.fiber F').attach, fiberIdeal v w'.1 := by
          refine Finset.prod_congr rfl fun w' _ => ?_
          rw [hS, count_normalizedFactors_conductorIdeal v (mem_fiber.mp w'.2),
            fiberIdeal_of_mem v (mem_fiber.mp w'.2)]
    _ = ∏ w ∈ v.fiber F', fiberIdeal v w := Finset.prod_attach (v.fiber F') (fiberIdeal v)

omit [CharZero F] in

theorem prod_fiberIdeal_le_of_subset {s t : Finset (Place K F')} (hst : s ⊆ t) :
    ∏ w ∈ t, fiberIdeal v w ≤ ∏ w ∈ s, fiberIdeal v w := by
  classical
  rw [← Finset.prod_sdiff hst]
  exact Ideal.mul_le_right

omit [CharZero F] in

theorem conductorIdeal_le_prod_fiberIdeal (s : Finset (Place K F')) :
    conductorIdeal (F' := F') v ≤ ∏ w ∈ s, fiberIdeal v w := by
  classical
  calc conductorIdeal (F' := F') v
      = ∏ w ∈ v.fiber F', fiberIdeal v w := conductorIdeal_eq_prod_fiber v
    _ = ∏ w ∈ v.fiber F' ∪ s, fiberIdeal v w := by
        refine Finset.prod_subset Finset.subset_union_left fun w _ hw' => ?_
        exact (fiberIdeal_of_notMem v fun hmem => hw' (mem_fiber.mpr hmem)).trans
          Ideal.one_eq_top.symm
    _ ≤ ∏ w ∈ s, fiberIdeal v w :=
        prod_fiberIdeal_le_of_subset v Finset.subset_union_right

end Place

namespace Place

variable (v : Place K F)

noncomputable scoped instance fiberIdealQuotientAlgebra (w : Place K F') :
    Algebra (IsLocalRing.ResidueField v.toValuationSubring)
      (integralClosureAt F' v ⧸ fiberIdeal v w) :=
  Ideal.Quotient.algebraQuotientOfLEComap
    (Ideal.map_le_iff_le_comap.mp (conductorIdeal_le_fiberIdeal v w))

noncomputable scoped instance prodFiberIdealQuotientAlgebra (s : Finset (Place K F')) :
    Algebra (IsLocalRing.ResidueField v.toValuationSubring)
      (integralClosureAt F' v ⧸ ∏ w ∈ s, fiberIdeal v w) :=
  Ideal.Quotient.algebraQuotientOfLEComap
    (Ideal.map_le_iff_le_comap.mp (conductorIdeal_le_prod_fiberIdeal v s))

omit [Algebra K F'] [IsScalarTower K F F'] [CharZero F] in

theorem finite_quotient_of_conductorLE (Q : Ideal (integralClosureAt F' v))
    [Algebra (IsLocalRing.ResidueField v.toValuationSubring) (integralClosureAt F' v ⧸ Q)]
    [IsScalarTower v.toValuationSubring (IsLocalRing.ResidueField v.toValuationSubring)
      (integralClosureAt F' v ⧸ Q)] :
    Module.Finite (IsLocalRing.ResidueField v.toValuationSubring)
      (integralClosureAt F' v ⧸ Q) :=
  Module.Finite.of_restrictScalars_finite v.toValuationSubring
    (IsLocalRing.ResidueField v.toValuationSubring) (integralClosureAt F' v ⧸ Q)

set_option maxHeartbeats 4000000 in
omit [CharZero F] in

theorem norm_mk_prod_fiberIdeal (c : integralClosureAt F' v) (s : Finset (Place K F')) :
    Algebra.norm (IsLocalRing.ResidueField v.toValuationSubring)
        (Ideal.Quotient.mk (∏ w ∈ s, fiberIdeal v w) c)
      = ∏ w ∈ s,
          Algebra.norm (IsLocalRing.ResidueField v.toValuationSubring)
            (Ideal.Quotient.mk (fiberIdeal v w) c) := by
  classical
  induction s using Finset.cons_induction with
  | empty =>

      haveI : Subsingleton
          (integralClosureAt F' v ⧸ (∏ w ∈ (∅ : Finset (Place K F')), fiberIdeal v w)) :=
        Ideal.Quotient.subsingleton_iff.mpr (by rw [Finset.prod_empty]; exact Ideal.one_eq_top)
      conv_rhs => rw [Finset.prod_empty]
      exact Algebra.norm_of_subsingleton _
  | cons a s ha ih =>

      have hcop : IsCoprime (fiberIdeal v a) (∏ w ∈ s, fiberIdeal v w) :=
        IsCoprime.prod_right fun w hw => isCoprime_fiberIdeal v (fun h => ha (h ▸ hw))
      have hprod : ∏ w ∈ Finset.cons a s ha, fiberIdeal v w
          = fiberIdeal v a ⊓ ∏ w ∈ s, fiberIdeal v w := by
        rw [Finset.prod_cons, Ideal.mul_eq_inf_of_isCoprime hcop]

      haveI : IsScalarTower v.toValuationSubring
          (IsLocalRing.ResidueField v.toValuationSubring)
          (integralClosureAt F' v ⧸ fiberIdeal v a) := IsScalarTower.of_algebraMap_eq' rfl
      haveI : IsScalarTower v.toValuationSubring
          (IsLocalRing.ResidueField v.toValuationSubring)
          (integralClosureAt F' v ⧸ ∏ w ∈ s, fiberIdeal v w) :=
        IsScalarTower.of_algebraMap_eq' rfl
      haveI := finite_quotient_of_conductorLE v (fiberIdeal v a)
      haveI := finite_quotient_of_conductorLE v (∏ w ∈ s, fiberIdeal v w)

      set e : (integralClosureAt F' v ⧸ (∏ w ∈ Finset.cons a s ha, fiberIdeal v w)) ≃+*
          (integralClosureAt F' v ⧸ fiberIdeal v a)
            × (integralClosureAt F' v ⧸ ∏ w ∈ s, fiberIdeal v w) :=
        (Ideal.quotEquivOfEq hprod).trans
          (Ideal.quotientInfEquivQuotientProd _ _ hcop) with he

      have hemk : ∀ x : integralClosureAt F' v,
          e (Ideal.Quotient.mk _ x) = (Ideal.Quotient.mk _ x, Ideal.Quotient.mk _ x) := by
        intro x
        rw [he, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
        exact Prod.ext
          (by rw [Ideal.quotientInfEquivQuotientProd_fst, Ideal.Quotient.factor_mk])
          (by rw [Ideal.quotientInfEquivQuotientProd_snd, Ideal.Quotient.factor_mk])

      have hkey : Algebra.norm (IsLocalRing.ResidueField v.toValuationSubring)
          (Ideal.Quotient.mk (∏ w ∈ Finset.cons a s ha, fiberIdeal v w) c)
            = Algebra.norm (IsLocalRing.ResidueField v.toValuationSubring)
                ((Ideal.Quotient.mk (fiberIdeal v a) c,
                  Ideal.Quotient.mk (∏ w ∈ s, fiberIdeal v w) c) :
                  (integralClosureAt F' v ⧸ fiberIdeal v a)
                    × (integralClosureAt F' v ⧸ ∏ w ∈ s, fiberIdeal v w)) := by
        refine (Algebra.norm_eq_of_equiv_equiv
          (RingEquiv.refl (IsLocalRing.ResidueField v.toValuationSubring)) e ?_
          (Ideal.Quotient.mk (∏ w ∈ Finset.cons a s ha, fiberIdeal v w) c)).trans ?_
        ·
          refine RingHom.ext fun x => ?_
          obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
          exact (hemk (algebraMap v.toValuationSubring (integralClosureAt F' v) r)).symm
        ·
          rw [hemk]
          rfl
      calc (Algebra.norm (IsLocalRing.ResidueField v.toValuationSubring)
              (Ideal.Quotient.mk (∏ w ∈ Finset.cons a s ha, fiberIdeal v w) c))
          = Algebra.norm (IsLocalRing.ResidueField v.toValuationSubring)
              (Ideal.Quotient.mk (fiberIdeal v a) c)
            * Algebra.norm (IsLocalRing.ResidueField v.toValuationSubring)
              (Ideal.Quotient.mk (∏ w ∈ s, fiberIdeal v w) c) := by
            rw [hkey]; exact Algebra.norm_prod _
        _ = ∏ w ∈ Finset.cons a s ha,
              Algebra.norm (IsLocalRing.ResidueField v.toValuationSubring)
                (Ideal.Quotient.mk (fiberIdeal v w) c) := by
            rw [Finset.prod_cons, ih]

omit [CharZero F] in

theorem norm_mk_conductor_eq_prod_fiber (c : integralClosureAt F' v) :
    Algebra.norm (IsLocalRing.ResidueField v.toValuationSubring)
        (Ideal.Quotient.mk (conductorIdeal (F' := F') v) c)
      = ∏ w ∈ v.fiber F',
          Algebra.norm (IsLocalRing.ResidueField v.toValuationSubring)
            (Ideal.Quotient.mk (fiberIdeal v w) c) := by
  classical
  rw [← norm_mk_prod_fiberIdeal v c (v.fiber F')]

  have he : (Ideal.quotEquivOfEq (conductorIdeal_eq_prod_fiber (F' := F') v))
      (Ideal.Quotient.mk (conductorIdeal (F' := F') v) c)
        = Ideal.Quotient.mk (∏ w ∈ v.fiber F', fiberIdeal v w) c :=
    Ideal.quotEquivOfEq_mk _ _
  rw [← he]
  refine Algebra.norm_eq_of_equiv_equiv
    (RingEquiv.refl (IsLocalRing.ResidueField v.toValuationSubring))
    (Ideal.quotEquivOfEq (conductorIdeal_eq_prod_fiber (F' := F') v)) ?_ _
  refine RingHom.ext fun x => ?_
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
  exact (Ideal.quotEquivOfEq_mk (conductorIdeal_eq_prod_fiber (F' := F') v)
    (algebraMap v.toValuationSubring (integralClosureAt F' v) r)).symm

end Place

namespace Place

variable {v : Place K F}

omit [CharZero F] in

theorem sub_algebraMap_evalAt_mem_fiberCenter {w : Place K F'} (hw : w.restrict F = v)
    (hwrat : w.IsRational) {c : integralClosureAt F' v}
    (_hc : algebraMap (integralClosureAt F' v) F' c ≠ 0)
    (_hord : w.ord (algebraMap (integralClosureAt F' v) F' c) = 0) :
    c - algebraMap v.toValuationSubring (integralClosureAt F' v)
        (algebraMap K v.toValuationSubring
          (w.evalAt (algebraMap (integralClosureAt F' v) F' c)))
      ∈ (fiberCenter F' v hw).asIdeal := by
  set lam : K := w.evalAt (algebraMap (integralClosureAt F' v) F' c) with hlam
  set d : integralClosureAt F' v := c - algebraMap v.toValuationSubring
    (integralClosureAt F' v) (algebraMap K v.toValuationSubring lam) with hd

  rcases eq_or_ne d 0 with hd0 | hd0
  · rw [hd0]; exact Ideal.zero_mem _
  rw [mem_fiberCenter_iff_ord_pos hw hd0]

  have hcoe : algebraMap (integralClosureAt F' v) F' d
      = algebraMap (integralClosureAt F' v) F' c - algebraMap K F' lam := by
    rw [hd, map_sub]
    congr 1
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply v.toValuationSubring
      F F',
      show (algebraMap v.toValuationSubring F) (algebraMap K v.toValuationSubring lam)
        = algebraMap K F lam from v.coe_algebraMap lam,
      ← IsScalarTower.algebraMap_apply]

  have hmem : algebraMap (integralClosureAt F' v) F' c ∈ w.toValuationSubring :=
    forall_mem_of_restrict_eq hw c
  have hres : residue w.toValuationSubring ⟨algebraMap (integralClosureAt F' v) F' c, hmem⟩
      = algebraMap K w.ResidueField lam := (w.algebraMap_evalAt hwrat hmem).symm

  have hdmem : algebraMap (integralClosureAt F' v) F' d ∈ w.toValuationSubring := by
    rw [hcoe]
    exact sub_mem hmem (w.algebraMap_mem' lam)
  have hdF : algebraMap (integralClosureAt F' v) F' d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (integralClosureAt F' v) F')).mpr hd0
  rw [← w.mem_maximalIdeal_iff_ord_pos hdF hdmem]
  rw [← IsLocalRing.residue_eq_zero_iff]
  have hsplit : (⟨algebraMap (integralClosureAt F' v) F' d, hdmem⟩ : w.toValuationSubring)
      = ⟨algebraMap (integralClosureAt F' v) F' c, hmem⟩
        - algebraMap K w.toValuationSubring lam := by
    refine Subtype.ext ?_
    show algebraMap (integralClosureAt F' v) F' d
      = ((⟨algebraMap (integralClosureAt F' v) F' c, hmem⟩
          - algebraMap K w.toValuationSubring lam : w.toValuationSubring) : F')
    rw [hcoe]
    push_cast
    rw [w.coe_algebraMap]
  rw [hsplit, map_sub, hres, sub_eq_zero, ← IsLocalRing.ResidueField.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply]

end Place

namespace Place

variable {v : Place K F}

omit [CharZero F] in

theorem algebraMap_evalAt_coe (hv : v.IsRational) (r : v.toValuationSubring) :
    algebraMap K v.ResidueField
        (v.evalAt (algebraMap v.toValuationSubring F r))
      = IsLocalRing.residue v.toValuationSubring r := by
  have hcoe : algebraMap v.toValuationSubring F r = (r : F) := rfl
  rw [hcoe]
  have hmem : (r : F) ∈ v.toValuationSubring := r.2
  rw [v.algebraMap_evalAt hv hmem]

omit [CharZero F] in

theorem residue_algebraMap (lam : K) :
    IsLocalRing.residue v.toValuationSubring (algebraMap K v.toValuationSubring lam)
      = algebraMap K v.ResidueField lam := by
  rw [← IsLocalRing.ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply]

omit [CharZero F] in

theorem norm_mk_fiberIdeal_eq_norm_mk_fiberCenterPow {w : Place K F'}
    (hw : w.restrict F = v) (c : integralClosureAt F' v) :
    Algebra.norm (IsLocalRing.ResidueField v.toValuationSubring)
        (Ideal.Quotient.mk (fiberIdeal v w) c)
      = Algebra.norm (IsLocalRing.ResidueField v.toValuationSubring)
          (Ideal.Quotient.mk (fiberCenterPow hw) c) := by
  have he : (Ideal.quotEquivOfEq (fiberIdeal_of_mem v hw))
      (Ideal.Quotient.mk (fiberIdeal v w) c) = Ideal.Quotient.mk (fiberCenterPow hw) c :=
    Ideal.quotEquivOfEq_mk _ _
  rw [← he]
  refine Algebra.norm_eq_of_equiv_equiv
    (RingEquiv.refl (IsLocalRing.ResidueField v.toValuationSubring))
    (Ideal.quotEquivOfEq (fiberIdeal_of_mem v hw)) ?_ _
  refine RingHom.ext fun x => ?_
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
  exact (Ideal.quotEquivOfEq_mk (fiberIdeal_of_mem v hw)
    (algebraMap v.toValuationSubring (integralClosureAt F' v) r)).symm

omit [CharZero F] in

theorem residue_norm_eq_prod_evalAt (hv : v.IsRational)
    (hrat : ∀ w ∈ v.fiber F', Place.IsRational w) {c : integralClosureAt F' v}
    (hc : algebraMap (integralClosureAt F' v) F' c ≠ 0)
    (hord : ∀ w ∈ v.fiber F', w.ord (algebraMap (integralClosureAt F' v) F' c) = 0) :
    IsLocalRing.residue v.toValuationSubring (Algebra.norm v.toValuationSubring c)
      = ∏ w ∈ v.fiber F',
          algebraMap K v.ResidueField
              (w.evalAt (algebraMap (integralClosureAt F' v) F' c))
            ^ w.ramificationIndex F := by
  classical

  rw [residue_norm_eq_norm_mk v c, norm_mk_conductor_eq_prod_fiber v c]

  refine Finset.prod_congr rfl fun w hw => ?_
  have hwv : w.restrict F = v := mem_fiber.mp hw

  have hsub := sub_algebraMap_evalAt_mem_fiberCenter hwv (hrat w hw) hc (hord w hw)

  rw [norm_mk_fiberIdeal_eq_norm_mk_fiberCenterPow hwv c, norm_mk_fiberCenterPow hwv hsub,
    finrank_fiberCenterPow hwv (hrat w hw) hv, residue_algebraMap]

end Place

end AlgebraicCurve

end

open IsDedekindDomain IsLocalRing UniqueFactorizationMonoid _root_.AlgebraicCurve AlgebraicCurve
  _root_.AlgebraicCurve.Place AlgebraicCurve.Place in
theorem AlgebraicCurve.Place.evalAt_norm_eq_prod_fiber {K F F' : Type*} [Field K] [Field F]
    [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F'] (v : Place K F)
    (f : F') (hf : f ≠ 0) (hv : v.IsRational) (hrat : ∀ w ∈ v.fiber F', Place.IsRational w)
    (hord : ∀ w ∈ v.fiber F', w.ord f = 0) : v.evalAt (Algebra.norm F f) = ∏ w ∈ v.fiber F',
    w.evalAt f ^ (w.ramificationIndex F) :=
    by
  classical

  obtain ⟨c, rfl⟩ := Place.exists_integralClosureAt_of_ord_fiber_nonneg
    (v := v) hf (fun w hw => (hord w hw).ge)
  have hc : c ≠ 0 := fun h => hf (by rw [h, map_zero])

  have hnorm : Algebra.norm F (algebraMap (integralClosureAt F' v) F' c)
      = algebraMap v.toValuationSubring F (Algebra.norm v.toValuationSubring c) := by
    rw [← Algebra.algebraMap_intNorm (A := v.toValuationSubring) (K := F) (L := F')
      (B := integralClosureAt F' v), Algebra.intNorm_eq_norm]

  refine v.algebraMap_residueField_injective ?_
  rw [hnorm]

  have hlhs : algebraMap K v.ResidueField
      (v.evalAt (algebraMap v.toValuationSubring F (Algebra.norm v.toValuationSubring c)))
        = IsLocalRing.residue v.toValuationSubring (Algebra.norm v.toValuationSubring c) :=
    Place.algebraMap_evalAt_coe hv _
  rw [hlhs, Place.residue_norm_eq_prod_evalAt hv hrat hf hord, map_prod]

  exact Finset.prod_congr rfl fun w hw => (map_pow _ _ _).symm

end

section

attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring
open AlgebraicCurve AlgebraicCurve.Divisor

theorem AlgebraicCurve.Divisor.evalFun_pullback {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F']
    [Algebra.IsSeparable F F'] {f : F'} (hf : f ≠ 0) (E : Divisor K F)
    (hrat : ∀ v ∈ E.support, Place.IsRational v)
    (hratw : ∀ v ∈ E.support, ∀ w ∈ v.fiber F', Place.IsRational w)
    (hord : ∀ v ∈ E.support, ∀ w ∈ v.fiber F', w.ord f = 0) : Divisor.evalFun f
    (Divisor.pullback F' E) = Divisor.evalFun (Algebra.norm F f) E := by
  classical
  rw [show evalFun f (pullback F' E)
      = ∏ w ∈ E.support.biUnion (fun v => v.fiber F'), w.evalAt f ^ (pullback F' E) w from
    Finsupp.prod_of_support_subset _ (AlgebraicCurve.Divisor.support_pullback_subset E)
      (fun w n => w.evalAt f ^ n) fun w _ => zpow_zero _,
    Finset.prod_biUnion (AlgebraicCurve.Place.pairwiseDisjoint_fiber E.support), evalFun_def]
  refine Finset.prod_congr rfl fun v hv => ?_
  calc
    ∏ w ∈ v.fiber F', w.evalAt f ^ (pullback F' E) w
        = ∏ w ∈ v.fiber F', (w.evalAt f ^ (w.ramificationIndex F : ℤ)) ^ E v := by
          refine Finset.prod_congr rfl fun w hw => ?_
          rw [pullback_apply, Place.mem_fiber.mp hw, ← zpow_mul]
    _ = (∏ w ∈ v.fiber F', w.evalAt f ^ (w.ramificationIndex F : ℤ)) ^ E v :=
          Finset.prod_zpow _ _ _
    _ = (∏ w ∈ v.fiber F', w.evalAt f ^ (w.ramificationIndex F)) ^ E v := by
          refine congrArg (· ^ E v) (Finset.prod_congr rfl fun w _ => ?_)
          rw [zpow_natCast]
    _ = v.evalAt (Algebra.norm F f) ^ E v := by
          rw [AlgebraicCurve.Place.evalAt_norm_eq_prod_fiber v f hf (hrat v hv) (hratw v hv) (hord
            v hv)]

end

section

attribute [-simp] AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
attribute [-simp] AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
open AlgebraicCurve

section

section

open IsDedekindDomain Polynomial

namespace AlgebraicCurve

namespace Place

section SupportTransfer

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F'] [Algebra F F']
  [FiniteDimensional F F']

variable (w : Place K F')

end SupportTransfer

section FiberFiniteness

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
  [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F']

end FiberFiniteness

end Place

end AlgebraicCurve

section

open IsDedekindDomain WithZero IsLocalRing

namespace AlgebraicCurve

namespace Place

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

attribute [local instance 0] valuationSubringAlgebra

section Setup

variable (v : Place K F)

scoped instance (priority := 100) : IsScalarTower v.toValuationSubring F F' :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

end Setup

section Center

variable {v : Place K F} {w : Place K F'}

end Center

section Assembly

variable (v : Place K F)

end Assembly

end Place

end AlgebraicCurve

section

open IsDedekindDomain WithZero IsLocalRing UniqueFactorizationMonoid

namespace AlgebraicCurve

namespace Place

section DVR

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem ord_coe_eq_of_span_singleton_eq_pow_maximalIdeal {r : v.toValuationSubring} {n : ℕ}
    (h : Ideal.span {r} = IsLocalRing.maximalIdeal v.toValuationSubring ^ n) :
    v.ord (r : F) = n := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton] at h
  obtain ⟨u, hu⟩ := h

  have hr : r = ((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) * π ^ n := by
    rw [mul_comm, Units.eq_mul_inv_iff_mul_eq]
    exact hu
  have hcoe : (r : F) = (((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) : F)
      * (π : F) ^ (n : ℤ) := by
    rw [hr]
    push_cast
    rw [zpow_natCast]
  rw [hcoe, v.ord_unit_smul_zpow u⁻¹ hπ (n : ℤ)]

end DVR

end Place

attribute [local instance 0] Place.valuationSubringAlgebra

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [CharZero F]

namespace Place
open AlgebraicCurve.Place

scoped instance (v : Place K F) : CharZero v.toValuationSubring :=
  ⟨fun a b hab => Nat.cast_injective (R := F)
    (by simpa using congrArg (Subtype.val : v.toValuationSubring → F) hab)⟩

section IdealNorm

variable {v : Place K F} {w : Place K F'}

theorem relNorm_fiberCenter (hw : w.restrict F = v) :
    Ideal.relNorm v.toValuationSubring (fiberCenter F' v hw).asIdeal
      = IsLocalRing.maximalIdeal v.toValuationSubring ^ w.inertiaDeg F := by
  haveI : (fiberCenter F' v hw).asIdeal.IsMaximal :=
    (fiberCenter F' v hw).isPrime.isMaximal (fiberCenter F' v hw).ne_bot
  haveI : (fiberCenter F' v hw).asIdeal.LiesOver
      (IsLocalRing.maximalIdeal v.toValuationSubring) := fiberCenter_liesOver hw
  rw [Ideal.relNorm_eq_pow_of_isMaximal (fiberCenter F' v hw).asIdeal
    (IsLocalRing.maximalIdeal v.toValuationSubring), inertiaDeg_eq_inertiaDeg_fiberCenter _ hw,
    Ideal.inertiaDeg'_eq_inertiaDeg]

theorem relNorm_span_singleton {c : integralClosureAt F' v}
    (hc : c ≠ 0) :
    Ideal.relNorm v.toValuationSubring (Ideal.span {c})
      = IsLocalRing.maximalIdeal v.toValuationSubring
          ^ (∑ w ∈ v.fiber F',
              w.inertiaDeg F * (w.ord (algebraMap (integralClosureAt F' v) F' c)).toNat) := by
  have hspan : (Ideal.span {c} : Ideal (integralClosureAt F' v)) ≠ ⊥ := by simpa using hc
  set S : Multiset (Ideal (integralClosureAt F' v)) := normalizedFactors (Ideal.span {c})
    with hS

  have hfactor : ∀ Q ∈ S.toFinset, ∃ w' : Place K F', ∃ hw' : w'.restrict F = v,
      (fiberCenter F' v hw').asIdeal = Q := by
    intro Q hQ
    rw [Multiset.mem_toFinset] at hQ
    have hQprime : Prime Q := prime_of_normalized_factor Q hQ
    have hQbot : Q ≠ ⊥ := hQprime.ne_zero
    haveI : Q.IsPrime := Ideal.isPrime_of_prime hQprime
    exact ⟨placeOfPrime ⟨Q, inferInstance, hQbot⟩, restrict_placeOfPrime _,
      congrArg HeightOneSpectrum.asIdeal (fiberCenter_placeOfPrime
        (⟨Q, inferInstance, hQbot⟩ : HeightOneSpectrum (integralClosureAt F' v)))⟩

  set T : Finset (Ideal (integralClosureAt F' v)) := (v.fiber F').attach.image
    (fun w' => (fiberCenter F' v (mem_fiber.mp w'.2)).asIdeal) with hT
  have hsub : S.toFinset ⊆ T := by
    intro Q hQ
    obtain ⟨w', hw', rfl⟩ := hfactor Q hQ
    exact Finset.mem_image.mpr ⟨⟨w', mem_fiber.mpr hw'⟩, Finset.mem_attach _ _, rfl⟩
  have hinj : Set.InjOn (fun w' : {x // x ∈ v.fiber F'} =>
      (fiberCenter F' v (mem_fiber.mp w'.2)).asIdeal) (v.fiber F').attach := by
    intro w₁ _ w₂ _ h
    exact Subtype.ext (eq_of_fiberCenter_eq (mem_fiber.mp w₁.2) (mem_fiber.mp w₂.2)
      (HeightOneSpectrum.ext h))

  calc
    Ideal.relNorm v.toValuationSubring (Ideal.span {c})
        = Ideal.relNorm v.toValuationSubring (∏ Q ∈ S.toFinset, Q ^ S.count Q) := by
          rw [← Finset.prod_multiset_count, hS, Ideal.prod_normalizedFactors_eq_self hspan]
    _ = ∏ Q ∈ S.toFinset, Ideal.relNorm v.toValuationSubring Q ^ S.count Q := by
          rw [map_prod]
          exact Finset.prod_congr rfl fun Q _ => map_pow _ Q _
    _ = ∏ Q ∈ S.toFinset, IsLocalRing.maximalIdeal v.toValuationSubring
          ^ ((IsLocalRing.maximalIdeal v.toValuationSubring).inertiaDeg' Q * S.count Q) := by
          refine Finset.prod_congr rfl fun Q hQ => ?_
          obtain ⟨w', hw', rfl⟩ := hfactor Q hQ
          rw [relNorm_fiberCenter hw', ← pow_mul, inertiaDeg_eq_inertiaDeg_fiberCenter _ hw']
    _ = IsLocalRing.maximalIdeal v.toValuationSubring
          ^ (∑ Q ∈ S.toFinset,
              (IsLocalRing.maximalIdeal v.toValuationSubring).inertiaDeg' Q * S.count Q) :=
          Finset.prod_pow_eq_pow_sum S.toFinset
            (fun Q => (IsLocalRing.maximalIdeal v.toValuationSubring).inertiaDeg' Q * S.count Q)
            (IsLocalRing.maximalIdeal v.toValuationSubring)
    _ = IsLocalRing.maximalIdeal v.toValuationSubring
          ^ (∑ w ∈ v.fiber F',
              w.inertiaDeg F * (w.ord (algebraMap (integralClosureAt F' v) F' c)).toNat) := by
          congr 1

          calc
            ∑ Q ∈ S.toFinset,
                (IsLocalRing.maximalIdeal v.toValuationSubring).inertiaDeg' Q * S.count Q
                = ∑ Q ∈ T,
                    (IsLocalRing.maximalIdeal v.toValuationSubring).inertiaDeg' Q
                      * S.count Q := by
                  refine Finset.sum_subset hsub fun Q _ hQ => ?_
                  rw [Multiset.count_eq_zero_of_notMem
                    (fun h => hQ (Multiset.mem_toFinset.mpr h)), mul_zero]
            _ = ∑ w' ∈ (v.fiber F').attach,
                  (IsLocalRing.maximalIdeal v.toValuationSubring).inertiaDeg'
                      (fiberCenter F' v (mem_fiber.mp w'.2)).asIdeal
                    * S.count (fiberCenter F' v (mem_fiber.mp w'.2)).asIdeal := by
                  rw [hT, Finset.sum_image hinj]
            _ = ∑ w' ∈ (v.fiber F').attach, (w'.1.inertiaDeg F
                  * (w'.1.ord (algebraMap (integralClosureAt F' v) F' c)).toNat) := by
                  refine Finset.sum_congr rfl fun w' _ => ?_
                  rw [← inertiaDeg_eq_inertiaDeg_fiberCenter _ (mem_fiber.mp w'.2),
                    count_normalizedFactors_span_singleton (mem_fiber.mp w'.2) hc]
            _ = ∑ w ∈ v.fiber F',
                  w.inertiaDeg F
                    * (w.ord (algebraMap (integralClosureAt F' v) F' c)).toNat :=
                  Finset.sum_attach (v.fiber F') fun w =>
                    w.inertiaDeg F * (w.ord (algebraMap (integralClosureAt F' v) F' c)).toNat

end IdealNorm

section ElementNorm

variable (v : Place K F)

theorem ord_norm_algebraMap_integralClosureAt
    {c : integralClosureAt F' v} (hc : c ≠ 0) :
    v.ord (Algebra.norm F (algebraMap (integralClosureAt F' v) F' c))
      = ∑ w ∈ v.fiber F', (w.inertiaDeg F : ℤ)
          * w.ord (algebraMap (integralClosureAt F' v) F' c) := by

  rw [← Algebra.algebraMap_intNorm (A := v.toValuationSubring) (K := F) (L := F')
    (B := integralClosureAt F' v)]

  have hrel := relNorm_span_singleton (v := v) hc
  rw [Ideal.relNorm_singleton] at hrel

  rw [ValuationSubring.algebraMap_apply, ord_coe_eq_of_span_singleton_eq_pow_maximalIdeal v hrel]

  push_cast
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [Int.toNat_of_nonneg
    (w.ord_nonneg_of_mem (forall_mem_of_restrict_eq (mem_fiber.mp hw) c))]

theorem ord_norm_eq_sum_fiber {f : F'} (hf : f ≠ 0) :
    v.ord (Algebra.norm F f) = ∑ w ∈ v.fiber F', (w.inertiaDeg F : ℤ) * w.ord f := by

  obtain ⟨⟨c, s⟩, hcs⟩ := IsLocalization.surj
    (nonZeroDivisors (integralClosureAt F' v)) f
  have hs0 : (s : integralClosureAt F' v) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  have hsF : algebraMap (integralClosureAt F' v) F' (s : integralClosureAt F' v) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (integralClosureAt F' v) F')).mpr hs0
  have hcF : algebraMap (integralClosureAt F' v) F' c ≠ 0 := by
    rw [← hcs]
    exact mul_ne_zero hf hsF
  have hc0 : c ≠ 0 := fun h => hcF (by rw [h, map_zero])

  have hintc := ord_norm_algebraMap_integralClosureAt v hc0
  have hints := ord_norm_algebraMap_integralClosureAt v hs0

  rw [← hcs, map_mul, v.ord_mul (Algebra.norm_ne_zero_iff.mpr hf)
    (Algebra.norm_ne_zero_iff.mpr hsF), hints] at hintc
  have hsplit : ∑ w ∈ v.fiber F', (w.inertiaDeg F : ℤ)
      * w.ord (f * algebraMap (integralClosureAt F' v) F' (s : integralClosureAt F' v))
        = (∑ w ∈ v.fiber F', (w.inertiaDeg F : ℤ) * w.ord f)
          + ∑ w ∈ v.fiber F', (w.inertiaDeg F : ℤ)
              * w.ord (algebraMap (integralClosureAt F' v) F' (s : integralClosureAt F' v))
                := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [w.ord_mul hf hsF]
    ring
  rw [hsplit] at hintc
  omega

end ElementNorm

end Place

namespace Divisor
open AlgebraicCurve.Divisor

theorem pushforwardNormFormula :
    Divisor.PushforwardNormFormula K F F' := by
  intro f hf D hD v
  classical
  rw [Divisor.pushforward_apply, Place.ord_norm_eq_sum_fiber v hf]
  calc
    ∑ w ∈ D.support, (if w.restrict F = v then D w * (w.inertiaDeg F : ℤ) else 0)
        = ∑ w ∈ D.support ∪ v.fiber F',
            (if w.restrict F = v then D w * (w.inertiaDeg F : ℤ) else 0) := by
          refine Finset.sum_subset Finset.subset_union_left fun w _ hw => ?_
          rw [Finsupp.notMem_support_iff.mp hw, zero_mul, ite_self]
    _ = ∑ w ∈ v.fiber F', (if w.restrict F = v then D w * (w.inertiaDeg F : ℤ) else 0) := by
          refine (Finset.sum_subset Finset.subset_union_right fun w _ hw => ?_).symm
          rw [if_neg fun h => hw (Place.mem_fiber.mpr h)]
    _ = ∑ w ∈ v.fiber F', (w.inertiaDeg F : ℤ) * w.ord f := by
          refine Finset.sum_congr rfl fun w hw => ?_
          rw [if_pos (Place.mem_fiber.mp hw), hD w, mul_comm]

end Divisor

end AlgebraicCurve

end

end

section

attribute [-simp] AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
attribute [-simp] AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
open AlgebraicCurve AlgebraicCurve.Divisor

theorem AlgebraicCurve.Divisor.pushforward_div {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F']
    [Algebra.IsSeparable F F'] [CharZero F] {f : F'} (hf : f ≠ 0)
    {D : Divisor K F'} (hD : ∀ w, D w = w.ord f) {E : Divisor K F}
    (hE : ∀ v, E v = v.ord (Algebra.norm F f)) : Divisor.pushforward F D = E :=
  pushforward_eq_of_normFormula AlgebraicCurve.Divisor.pushforwardNormFormula hf hD hE

end

section

section

open IsDedekindDomain WithZero IsLocalRing

namespace AlgebraicCurve

namespace Place

section Uniqueness

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)

end Uniqueness

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

end Place

end AlgebraicCurve

end

section

open AlgebraicCurve

theorem AlgebraicCurve.Place.ord_norm_eq_zero_of_forall_fiber {K F F' : Type*} [Field K] [Field F]
    [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [CharZero F]
    {f : F'} (hf : f ≠ 0) (v : Place K F) (h : ∀ w ∈ v.fiber F', w.ord f = 0) : v.ord
    (Algebra.norm F f) = 0 := by
  rw [AlgebraicCurve.Place.ord_norm_eq_sum_fiber v hf]
  exact Finset.sum_eq_zero fun w hw => by rw [h w hw, mul_zero]

end

end
