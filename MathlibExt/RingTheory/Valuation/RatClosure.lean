/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ValuationSubring_exists_two_closed_subfields_completion_inf_eq_ratClosure_of_
liesOverPrime.lean`
and
`P2M/Sol/S_ValuationSubring_exists_two_closed_subfields_completion_inf_eq_ratClosure_of_
liesOverPrime.lean`
and
`Definitions/Def_ValuationSubring_CompletionRatClosure.lean`
and
`Definitions/Def_FLTPrelim_Ramification.lean`
and the upstream results it uses, from
`Theorems/Thm_ValuationSubring_isAlgClosed_completion_of_liesOverPrime.lean`,
`P2M/Sol/S_ValuationSubring_isAlgClosed_completion_of_liesOverPrime.lean`,
`Theorems/Thm_ValuationSubring_valuation_completion_ratClosure_natCast_pos_and_lt_one_and_rankOne_
of_liesOverPrime.lean`,
`P2M/Sol/S_ValuationSubring_valuation_completion_ratClosure_natCast_pos_and_lt_one_and_rankOne_of_
liesOverPrime.lean`,
`Theorems/Thm_Valued_isClosed_submodule_of_finiteDimensional_of_isClosed_subfield.lean`,
`P2M/Sol/S_Valued_isClosed_submodule_of_finiteDimensional_of_isClosed_subfield.lean`,
`Theorems/Thm_ValuationSubring_mulArchimedean_valueGroup_of_isAlgebraic_of_valuation_natCast_lt_
one.lean`,
`P2M/Sol/S_ValuationSubring_mulArchimedean_valueGroup_of_isAlgebraic_of_valuation_natCast_lt_
one.lean`,
`Theorems/Thm_ValuationSubring_isAlgClosed_completion_of_mulArchimedean_valueGroup.lean`,
`P2M/Sol/S_ValuationSubring_isAlgClosed_completion_of_mulArchimedean_valueGroup.lean`,
`Theorems/Thm_ValuationSubring_exists_pow_valuation_eq_valuation_natCast_zpow_of_isAlgebraic.lean`,
`P2M/Sol/S_ValuationSubring_exists_pow_valuation_eq_valuation_natCast_zpow_of_isAlgebraic.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
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

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.Algebra.Valued.WithVal
public import MathlibExt.RingTheory.Valuation.LiesOverPrime

import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Analysis.Normed.Field.Dense
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.RingTheory.Valuation.RankOne
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.MetricSpace.Perfect
import MathlibExt.RingTheory.Valuation.PowAlgebraic

/-!
# Two closed subfields of a completed algebraic closure of `ℚ`

Let `A` be a valuation subring of an algebraic closure of `ℚ` lying over a rational prime `r`,
and let `ratClosure A` be the closure of the prime field in the completion of `A.valuation`.
The completion is algebraically closed, so it contains a square root and a cube root of `r`.
Adjoining either one to `ratClosure A` gives a finite extension, hence a closed subfield; the
two extensions have degrees `2` and `3`, so they meet exactly in `ratClosure A`. Each of them
contains uncountably many elements outside `ratClosure A`, because `ratClosure A` is a perfect
set in a complete metric space and hence uncountable.

## Main declarations

* `ValuationSubring.ratClosure`: the closure of the prime field in the completion.
* `ValuationSubring.exists_two_closed_subfields_completion_inf_eq_ratClosure_of_liesOverPrime`:
  the existence of the two closed subfields.
-/

@[expose] public section

noncomputable section

namespace ValuationSubring


variable (A : ValuationSubring (AlgebraicClosure ℚ))

/-- The closure of the prime field in the completion of a valuation
subring of an algebraic closure of `ℚ`. -/
public def ratClosure : Subfield A.valuation.Completion :=
  (⊥ : Subfield A.valuation.Completion).topologicalClosure

public theorem isClosed_ratClosure : IsClosed (ratClosure A : Set A.valuation.Completion) :=
  Subfield.isClosed_topologicalClosure _

public theorem bot_le_ratClosure : (⊥ : Subfield A.valuation.Completion) ≤ ratClosure A :=
  Subfield.le_topologicalClosure _

@[simp] public theorem ratCast_mem_ratClosure (q : ℚ) :
    (q : A.valuation.Completion) ∈ ratClosure A :=
  bot_le_ratClosure A (SubfieldClass.ratCast_mem _ q)

@[simp] public theorem natCast_mem_ratClosure (n : ℕ) :
    (n : A.valuation.Completion) ∈ ratClosure A :=
  natCast_mem (ratClosure A) n

@[simp] public theorem intCast_mem_ratClosure (n : ℤ) :
    (n : A.valuation.Completion) ∈ ratClosure A :=
  intCast_mem (ratClosure A) n

private instance charZero_completion : CharZero A.valuation.Completion :=
  charZero_of_injective_ringHom
    (UniformSpace.Completion.coeRingHom (α := WithVal A.valuation)).injective

end ValuationSubring



namespace ValuationSubring.ValueGroupArch

section ValueGroup

variable {K : Type*} [Field K] (A : ValuationSubring K)

private theorem valuation_intCast_eq_one_of_not_dvd {p : ℕ} (hp : p.Prime)
    (hAp : A.valuation (p : K) < 1) {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) :
    A.valuation (a : K) = 1 := by
  have hcop : IsCoprime a (p : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have := Int.gcd_dvd_right a p
    have h2 : (Int.gcd a p : ℤ) ∣ (p : ℤ) := Int.gcd_dvd_right a p
    have h3 : Int.gcd a p ∣ p := by exact_mod_cast h2
    rcases (Nat.dvd_prime hp).mp h3 with h | h
    · exact h
    · exfalso
      apply ha
      have h4 : (Int.gcd a p : ℤ) ∣ a := Int.gcd_dvd_left a p
      rw [h] at h4
      exact h4
  obtain ⟨s, t, hst⟩ := hcop
  have hle : A.valuation (a : K) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A a)
  refine le_antisymm hle (not_lt.mp fun hlt => ?_)
  have h1 : (s : K) * (a : K) + (t : K) * (p : K) = 1 := by
    have := congrArg (fun z : ℤ => (z : K)) hst
    push_cast at this
    exact this
  have hs : A.valuation (s : K) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A s)
  have ht : A.valuation (t : K) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A t)
  have hlt1 : A.valuation ((s : K) * (a : K)) < 1 := by
    rw [map_mul]
    calc A.valuation (s : K) * A.valuation (a : K) ≤ 1 * A.valuation (a : K) :=
          mul_le_mul_left hs _
      _ < 1 := by rw [one_mul]; exact hlt
  have hlt2 : A.valuation ((t : K) * (p : K)) < 1 := by
    rw [map_mul]
    calc A.valuation (t : K) * A.valuation (p : K) ≤ 1 * A.valuation (p : K) :=
          mul_le_mul_left ht _
      _ < 1 := by rw [one_mul]; exact hAp
  have := A.valuation.map_add_lt hlt1 hlt2
  rw [h1, map_one] at this
  exact lt_irrefl _ this

private theorem exists_valuation_natCast_eq_pow {p : ℕ} (hp : p.Prime)
    (hAp : A.valuation (p : K) < 1) {n : ℕ} (hn : n ≠ 0) :
    ∃ e : ℕ, A.valuation (n : K) = A.valuation (p : K) ^ e := by
  obtain ⟨e, n', hn', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.one_lt.ne'
  refine ⟨e, ?_⟩
  have h1 : A.valuation ((n' : ℤ) : K) = 1 :=
    valuation_intCast_eq_one_of_not_dvd A hp hAp (by exact_mod_cast hn')
  push_cast
  rw [map_mul, map_pow]
  rw [Int.cast_natCast] at h1
  rw [h1, mul_one]

private theorem exists_valuation_ratCast_eq_zpow [CharZero K] {p : ℕ} (hp : p.Prime)
    (hAp : A.valuation (p : K) < 1) {c : ℚ} (hc : c ≠ 0) :
    ∃ k : ℤ, A.valuation (c : K) = A.valuation (p : K) ^ k := by
  have hp0 : A.valuation (p : K) ≠ 0 := by
    rw [ne_eq, Valuation.zero_iff]; exact_mod_cast hp.ne_zero
  have hnum : c.num ≠ 0 := Rat.num_ne_zero.mpr hc
  obtain ⟨e₁, he₁⟩ := exists_valuation_natCast_eq_pow A hp hAp (Int.natAbs_ne_zero.mpr hnum)
  obtain ⟨e₂, he₂⟩ := exists_valuation_natCast_eq_pow A hp hAp c.den_nz
  refine ⟨(e₁ : ℤ) - e₂, ?_⟩
  have hnumv : A.valuation (c.num : K) = A.valuation (p : K) ^ e₁ := by
    rw [← he₁]
    rcases Int.natAbs_eq c.num with h | h
    · conv_lhs => rw [h]
      rw [Int.cast_natCast]
    · conv_lhs => rw [h]
      rw [Int.cast_neg, Valuation.map_neg, Int.cast_natCast]
  rw [Rat.cast_def, map_div₀, hnumv, he₂, zpow_sub₀ hp0, zpow_natCast, zpow_natCast]

variable [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K]

private theorem exists_pow_valuation_eq_valuation_prime_zpow {p : ℕ} (hp : p.Prime)
    (hAp : A.valuation (p : K) < 1) {x : K} (hx : x ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ ∃ k : ℤ, A.valuation x ^ n = A.valuation (p : K) ^ k := by
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  obtain ⟨n, hn, c, hc, hcv⟩ :=
    ValuationSubring.exists_pow_valuation_eq_valuation_algebraMap_of_isAlgebraic (E := ℚ) A hx
  obtain ⟨k, hk⟩ := exists_valuation_ratCast_eq_zpow A hp hAp hc
  refine ⟨n, hn, k, ?_⟩
  rw [← map_pow, hcv, ← hk, eq_ratCast]

private theorem mulArchimedean_valueGroup {p : ℕ} (hp : p.Prime) (hAp : A.valuation (p : K) < 1) :
    MulArchimedean A.ValueGroup := by
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  set π := A.valuation (p : K) with hπ
  have hp0 : π ≠ 0 := by
    rw [hπ, ne_eq, Valuation.zero_iff]
    exact_mod_cast hp.ne_zero
  have hπpos : 0 < π := zero_lt_iff.mpr hp0
  have hneg : ∀ k : ℤ, 1 < π ^ k → k < 0 := by
    intro k hk
    by_contra hk0
    push Not at hk0
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk0
    rw [zpow_natCast] at hk
    exact absurd hk (not_lt.mpr (pow_le_one₀ zero_le hAp.le))
  refine ⟨fun x y hy => ?_⟩
  by_cases hx1 : x ≤ 1
  · exact ⟨1, hx1.trans (by rw [pow_one]; exact hy.le)⟩
  push Not at hx1
  obtain ⟨g, rfl⟩ := A.valuation_surjective x
  obtain ⟨h, rfl⟩ := A.valuation_surjective y
  have hg0 : g ≠ 0 := by rintro rfl; simp at hx1
  have hh0 : h ≠ 0 := by rintro rfl; simp at hy
  obtain ⟨a, ha, k, hk⟩ := exists_pow_valuation_eq_valuation_prime_zpow A hp hAp hg0
  obtain ⟨b, hb, l, hl⟩ := exists_pow_valuation_eq_valuation_prime_zpow A hp hAp hh0
  have hk0 : k < 0 := hneg k (by rw [← hk]; exact one_lt_pow₀ hx1 ha.ne')
  have hl0 : l < 0 := hneg l (by rw [← hl]; exact one_lt_pow₀ hy hb.ne')
  refine ⟨b * k.natAbs, ?_⟩
  apply le_of_pow_le_pow_left₀ ha.ne' zero_le
  have hexp : l * ((k.natAbs : ℤ) * a) ≤ k := by
    have hka : (k.natAbs : ℤ) ≤ (k.natAbs : ℤ) * a := by
      have : (1 : ℤ) ≤ a := by exact_mod_cast ha
      nlinarith [Int.natCast_nonneg k.natAbs]
    have hkabs : (k.natAbs : ℤ) = -k := by omega
    nlinarith
  calc A.valuation g ^ a = π ^ k := hk
    _ ≤ π ^ (l * ((k.natAbs : ℤ) * a)) := zpow_le_zpow_right_of_le_one₀ hπpos hAp.le hexp
    _ = ((A.valuation h ^ b) ^ k.natAbs) ^ a := by
        rw [hl, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul]
    _ = (A.valuation h ^ (b * k.natAbs)) ^ a := by rw [pow_mul]

end ValueGroup

end ValuationSubring.ValueGroupArch

private theorem mulArchimedean_valueGroup_of_isAlgebraic_of_valuation_natCast_lt_one
    {K : Type*} [Field K] [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K]
    (A : ValuationSubring K) {p : ℕ} (hp : p.Prime) (hAp : A.valuation (p : K) < 1) :
    MulArchimedean A.ValueGroup :=
  ValuationSubring.ValueGroupArch.mulArchimedean_valueGroup A hp hAp

open MonoidWithZeroHom

namespace ValuationSubring.CompletionAlgClosed

section AlgClosed

variable {K : Type*} [Field K] (A : ValuationSubring K)

private theorem mulArchimedean_valueGroup₀ {L Γ₀ : Type*} [Field L]
    [LinearOrderedCommGroupWithZero Γ₀] [MulArchimedean Γ₀] (v : Valuation L Γ₀) :
    MulArchimedean (ValueGroup₀ (v : L →*₀ Γ₀)) := by
  have : MulArchimedean (valueGroup (v : L →*₀ Γ₀)) :=
    MulArchimedean.comap (valueGroup (v : L →*₀ Γ₀)).subtype (Subtype.strictMono_coe _)
  infer_instance

@[reducible] private noncomputable def rankOneOfMulArchimedean {L Γ₀ : Type*} [Field L]
    [LinearOrderedCommGroupWithZero Γ₀] [MulArchimedean Γ₀] (v : Valuation L Γ₀)
    [v.IsNontrivial] : v.RankOne :=
  haveI := mulArchimedean_valueGroup₀ v
  (Valuation.nonempty_rankOne_iff_mulArchimedean.mpr inferInstance).some

private theorem isNontrivial_valuation (hA : A ≠ ⊤) : A.valuation.IsNontrivial := by
  obtain ⟨x, hx⟩ : ∃ x : K, x ∉ A := by
    by_contra h
    push Not at h
    exact hA (_root_.eq_top_iff.mpr fun x _ => h x)
  refine ⟨x, ?_, ?_⟩
  · intro h0
    rw [Valuation.zero_iff] at h0
    exact hx (h0 ▸ A.zero_mem)
  · intro h1
    exact hx ((A.valuation_le_one_iff x).mp h1.le)

private theorem isNontrivial_completion (hA : A ≠ ⊤) :
    (Valued.v (R := A.valuation.Completion)).IsNontrivial := by
  obtain ⟨x, h0, h1⟩ := isNontrivial_valuation A hA
  refine ⟨((WithVal.toVal A.valuation x : WithVal A.valuation) : A.valuation.Completion), ?_, ?_⟩
  · rw [Valued.valuedCompletion_apply]; exact h0
  · rw [Valued.valuedCompletion_apply]; exact h1

private theorem isAlgClosed_completion [IsAlgClosed K] [CharZero K] [MulArchimedean A.ValueGroup]
    (hA : A ≠ ⊤) :
    IsAlgClosed A.valuation.Completion := by
  have := isNontrivial_completion A hA
  let hr : (Valued.v (R := A.valuation.Completion)).RankOne := rankOneOfMulArchimedean _
  let : NontriviallyNormedField A.valuation.Completion :=
    Valued.toNontriviallyNormedField A.valuation.Completion A.ValueGroup
  have : IsUltrametricDist A.valuation.Completion := inferInstance
  have : CompleteSpace A.valuation.Completion := inferInstance
  have : CharZero A.valuation.Completion :=
    charZero_of_injective_ringHom
      (UniformSpace.Completion.coeRingHom (α := WithVal A.valuation)).injective
  have : IsAlgClosed (WithVal A.valuation) :=
    IsAlgClosed.of_ringEquiv K (WithVal A.valuation) (WithVal.equiv A.valuation).symm
  exact IsAlgClosed.of_denseRange (K := WithVal A.valuation)
    UniformSpace.Completion.denseRange_coe

end AlgClosed

end ValuationSubring.CompletionAlgClosed

private theorem isAlgClosed_completion_of_mulArchimedean_valueGroup
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (A : ValuationSubring K) [MulArchimedean A.ValueGroup] (hA : A ≠ ⊤) :
    IsAlgClosed A.valuation.Completion :=
  ValuationSubring.CompletionAlgClosed.isAlgClosed_completion A hA

private theorem isAlgClosed_completion_of_liesOverPrime
    (p : ℕ) (hp : p.Prime) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    IsAlgClosed A.valuation.Completion := by
  have hAp : A.valuation (p : AlgebraicClosure ℚ) < 1 := A.mem_nonunits_iff.mp hA
  have : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    convert AlgebraicClosure.isAlgebraic ℚ
  have : MulArchimedean A.ValueGroup :=
    mulArchimedean_valueGroup_of_isAlgebraic_of_valuation_natCast_lt_one A hp hAp
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hAtop : A ≠ ⊤ := by
    intro htop
    have hmem : (p : AlgebraicClosure ℚ)⁻¹ ∈ A := by rw [htop]; exact ValuationSubring.mem_top _
    have hle : A.valuation (p : AlgebraicClosure ℚ)⁻¹ ≤ 1 := (A.valuation_le_one_iff _).mpr hmem
    rw [map_inv₀, inv_le_one₀ (zero_lt_iff.mpr ((map_ne_zero A.valuation).mpr hp0))] at hle
    exact absurd hAp (not_lt.mpr hle)
  exact isAlgClosed_completion_of_mulArchimedean_valueGroup A hAtop

namespace ValuationSubring
namespace CompletionCoe

variable (A : ValuationSubring (AlgebraicClosure ℚ))

private theorem v_coe (x : AlgebraicClosure ℚ) : Valued.v (x : A.valuation.Completion) =
    A.valuation x := by
  rw [show (x : A.valuation.Completion) =
      (((WithVal.equiv A.valuation).symm x : WithVal A.valuation) : A.valuation.Completion) from
          rfl,
    Valued.valuedCompletion_apply]
  rfl

private noncomputable def coeHom : AlgebraicClosure ℚ →+* A.valuation.Completion :=
  (UniformSpace.Completion.coeRingHom : WithVal A.valuation →+* A.valuation.Completion).comp
    (WithVal.equiv A.valuation).symm.toRingHom

private theorem coeHom_apply (x : AlgebraicClosure ℚ) : coeHom A x = (x : A.valuation.Completion)
    := rfl

private theorem coe_ratCast' (q : ℚ) : ((q : AlgebraicClosure ℚ) : A.valuation.Completion) =
    (q : A.valuation.Completion) := by
  rw [← coeHom_apply, map_ratCast]

private theorem v_ratCast (q : ℚ) : Valued.v (q : A.valuation.Completion) = A.valuation
    (q : AlgebraicClosure ℚ) := by
  rw [← coe_ratCast', v_coe]

private theorem v_natCast (n : ℕ) : Valued.v (n : A.valuation.Completion) = A.valuation
    (n : AlgebraicClosure ℚ) := by
  rw [← Rat.cast_natCast, v_ratCast, Rat.cast_natCast]

end CompletionCoe

/-- Over a rational prime, the valuation on the completion is archimedean in the sense that
every element of valuation `< 1` has a power below any nonzero valuation. -/
private theorem exists_pow_le_of_liesOverPrime (r : ℕ) (hr : r.Prime)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r) :
    ∀ x y : A.valuation.Completion, Valued.v x < 1 → y ≠ 0 →
      ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y := by
  have hAp : A.valuation (r : AlgebraicClosure ℚ) < 1 := A.mem_nonunits_iff.mp hA
  have : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    convert AlgebraicClosure.isAlgebraic ℚ
  have : MulArchimedean A.ValueGroup :=
    mulArchimedean_valueGroup_of_isAlgebraic_of_valuation_natCast_lt_one A hr hAp
  intro x y hx hy
  rcases eq_or_ne (Valued.v x) 0 with hx0 | hx0
  · exact ⟨1, by rw [hx0, pow_one]; exact zero_le⟩
  · have hy0 : Valued.v y ≠ 0 := (map_ne_zero _).mpr hy
    have hxpos : 0 < Valued.v x := zero_lt_iff.mpr hx0
    have hinv : 1 < (Valued.v x)⁻¹ := (one_lt_inv₀ hxpos).mpr hx
    obtain ⟨n, hn⟩ := MulArchimedean.arch (Valued.v y)⁻¹ hinv
    refine ⟨n, ?_⟩
    rw [inv_pow] at hn
    exact (inv_le_inv₀ (zero_lt_iff.mpr hy0) (pow_pos hxpos n)).mp hn

end ValuationSubring


/-- In a valued field where every element of valuation `< 1` has a power below any
nonzero valuation, the value group is multiplicatively archimedean. -/
private theorem Valued.mulArchimedean_valueGroup₀_of_exists_pow_le
    {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y) :
    MulArchimedean (MonoidWithZeroHom.ValueGroup₀ ((Valued.v : Valuation K Γ₀) : K →*₀ Γ₀)) := by
  refine ⟨fun a b hb => ?_⟩
  obtain ⟨xa, rfl⟩ := MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective
      ((Valued.v : Valuation K Γ₀) : K →*₀ Γ₀) a
  obtain ⟨xb, rfl⟩ := MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective
      ((Valued.v : Valuation K Γ₀) : K →*₀ Γ₀) b
  rw [← Valuation.restrict_def] at hb ⊢
  rw [← Valuation.restrict_def]
  have hb1 : 1 < Valued.v xb := by
    by_contra h
    exact absurd hb (not_lt.mpr ((Valuation.restrict_le_one_iff _).mpr (not_lt.mp h)))
  have hxb0 : xb ≠ 0 := fun h => by
    rw [h, map_zero] at hb1; exact absurd hb1 (not_lt.mpr zero_le)
  rcases eq_or_ne (Valued.v xa) 0 with ha0 | ha0
  · refine ⟨0, ?_⟩
    refine le_of_le_of_eq ?_ (_root_.pow_zero _).symm
    exact (Valuation.restrict_le_one_iff _).mpr (by rw [ha0]; exact zero_le)
  · have hxa0 : xa ≠ 0 := fun h => ha0 (by rw [h, map_zero])
    have h1 : Valued.v xb⁻¹ < 1 := by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hb1
    obtain ⟨n, hn⟩ := hrk xb⁻¹ xa⁻¹ h1 (inv_ne_zero hxa0)
    refine ⟨n, ?_⟩
    rw [map_inv₀, map_inv₀, inv_pow] at hn
    have key : (Valued.v : Valuation K Γ₀).restrict xa ≤
        (Valued.v : Valuation K Γ₀).restrict (xb ^ n) := by
      rw [Valuation.restrict_le_iff, map_pow]
      exact (inv_le_inv₀ (pow_pos (zero_lt_iff.mpr ((map_ne_zero _).mpr hxb0)) n)
          (zero_lt_iff.mpr ha0)).mp hn
    exact key.trans_eq (map_pow _ _ _)

private theorem Valued.isClosed_submodule_of_finiteDimensional_of_isClosed_subfield
    (K : Type*) [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    [CompleteSpace K]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (K₀' : Subfield K) (hcl : IsClosed (K₀' : Set K)) (hnt : ∃ x ∈ K₀', x ≠ 0 ∧ Valued.v x < 1)
    (V : Submodule ↥K₀' K) [FiniteDimensional ↥K₀' ↥V] :
    IsClosed (V : Set K) := by
  classical
  obtain ⟨x₀, hx₀K, hx₀0, hx₀1⟩ := hnt
  have hnt' : (Valued.v : Valuation K Γ₀).IsNontrivial := ⟨⟨x₀, (map_ne_zero _).mpr hx₀0, hx₀1.ne⟩⟩
  have hMA := Valued.mulArchimedean_valueGroup₀_of_exists_pow_le hrk
  have hcs : CompleteSpace ↥K₀' := hcl.completeSpace_coe
  let hRO : Valuation.RankOne (Valued.v : Valuation K Γ₀) :=
    (Valuation.nonempty_rankOne_iff_mulArchimedean.mpr hMA).some
  let : NontriviallyNormedField K := Valued.toNontriviallyNormedField K Γ₀
  let hK₀ : NormedField ↥K₀' := NormedField.induced ↥K₀' K K₀'.subtype Subtype.val_injective
  have hnorm : ∀ x : ↥K₀', ‖x‖ = ‖(x : K)‖ := fun x => rfl
  let : NontriviallyNormedField ↥K₀' := NontriviallyNormedField.ofNormNeOne
    ⟨⟨x₀, hx₀K⟩, fun h => hx₀0 (congrArg Subtype.val h), by
      rw [hnorm]; exact (Valued.toNormedField.norm_lt_one_iff.mpr hx₀1).ne⟩
  have hcsm : ContinuousSMul ↥K₀' K :=
    ⟨(continuous_subtype_val.comp continuous_fst).mul continuous_snd⟩
  exact @Submodule.closed_of_finiteDimensional ↥K₀' K _ hcs _ _ _ _ hcsm _ V _

namespace ValuationSubring
namespace TwoSubfields

open CompletionCoe

section Coprime

variable (A : ValuationSubring (AlgebraicClosure ℚ)) {r : ℕ}

private theorem vA_natCast_le_one (n : ℕ) : A.valuation (n : AlgebraicClosure ℚ) ≤ 1 :=
  (A.valuation_le_one_iff _).mpr (natCast_mem A n)

private theorem vA_intCast_le_one (n : ℤ) : A.valuation (n : AlgebraicClosure ℚ) ≤ 1 :=
  (A.valuation_le_one_iff _).mpr (intCast_mem A n)

private theorem vA_natCast_eq_one_of_coprime (hA : A.LiesOverPrime r) {d : ℕ} (hd : d.Coprime r) :
    A.valuation (d : AlgebraicClosure ℚ) = 1 := by
  refine le_antisymm (vA_natCast_le_one A d) (not_lt.mp fun hlt => ?_)
  have hAr : A.valuation (r : AlgebraicClosure ℚ) < 1 := A.mem_nonunits_iff.mp hA
  obtain ⟨u, t, hut⟩ := Nat.isCoprime_iff_coprime.mpr hd
  have h1 : (u : AlgebraicClosure ℚ) * d + t * r = 1 := by exact_mod_cast hut
  have hv : A.valuation ((u : AlgebraicClosure ℚ) * d + t * r) < 1 := by
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
    · rw [map_mul]; exact (mul_le_of_le_one_left zero_le (vA_intCast_le_one A u)).trans_lt hlt
    · rw [map_mul]; exact (mul_le_of_le_one_left zero_le (vA_intCast_le_one A t)).trans_lt hAr
  rw [h1, map_one] at hv
  exact lt_irrefl _ hv

end Coprime

section ValuationOfRatClosure

variable (A : ValuationSubring (AlgebraicClosure ℚ)) {r : ℕ}

private theorem vA_natCast_eq_one_of_not_dvd (hr : r.Prime) (hA : A.LiesOverPrime r) {d : ℕ}
    (hd : ¬ r ∣ d) :
    A.valuation (d : AlgebraicClosure ℚ) = 1 :=
  vA_natCast_eq_one_of_coprime A hA ((Nat.Prime.coprime_iff_not_dvd hr).mpr hd).symm

private theorem vA_natCast_eq_zpow (hr : r.Prime) (hA : A.LiesOverPrime r) {n : ℕ} (hn : n ≠ 0) :
    ∃ e : ℕ, A.valuation (n : AlgebraicClosure ℚ) = A.valuation (r : AlgebraicClosure ℚ) ^ e := by
  obtain ⟨e, n', hnd, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn r hr.ne_one
  refine ⟨e, ?_⟩
  rw [Nat.cast_mul, Nat.cast_pow, map_mul, map_pow, vA_natCast_eq_one_of_not_dvd A hr hA hnd,
      mul_one]

private theorem vA_ratCast_eq_zpow (hr : r.Prime) (hA : A.LiesOverPrime r) {q : ℚ} (hq : q ≠ 0) :
    ∃ n : ℤ, A.valuation (q : AlgebraicClosure ℚ) = A.valuation (r : AlgebraicClosure ℚ) ^ n := by
  have hnum0 : q.num.natAbs ≠ 0 := by simpa using (Rat.num_ne_zero.mpr hq)
  obtain ⟨a, ha⟩ := vA_natCast_eq_zpow A hr hA hnum0
  obtain ⟨b, hb⟩ := vA_natCast_eq_zpow A hr hA q.den_nz
  have hvnum :
      A.valuation (q.num : AlgebraicClosure ℚ) = A.valuation (r : AlgebraicClosure ℚ) ^ a := by
    have hcast : ((q.num.natAbs : ℕ) : AlgebraicClosure ℚ) =
        ((q.num.natAbs : ℤ) : AlgebraicClosure ℚ) :=
      (Int.cast_natCast _).symm
    rcases Int.natAbs_eq q.num with hn | hn
    · rw [hn, ← hcast]; exact ha
    · rw [hn, Int.cast_neg, Valuation.map_neg, ← hcast]; exact ha
  refine ⟨(a : ℤ) - b, ?_⟩
  have hvr0 : A.valuation (r : AlgebraicClosure ℚ) ≠ 0 :=
    (map_ne_zero _).mpr (by exact_mod_cast hr.ne_zero)
  rw [Rat.cast_def, map_div₀, hvnum, hb, zpow_sub₀ hvr0, zpow_natCast, zpow_natCast]

private theorem exists_rat_v_eq {x : A.valuation.Completion} (hx : x ∈ ratClosure A) (hx0 : x ≠ 0) :
    ∃ q : ℚ, Valued.v (q : A.valuation.Completion) = Valued.v x := by
  have hvx0 : Valued.v.restrict x ≠ 0 := (map_ne_zero _).mpr hx0
  have hopen : IsOpen {y : A.valuation.Completion | Valued.v.restrict y = Valued.v.restrict x} :=
    (Valued.isClopen_sphere _ hvx0).isOpen
  have hxmem : x ∈ closure ((⊥ : Subfield A.valuation.Completion) : Set A.valuation.Completion) :=
    hx
  obtain ⟨y, hyV, hybot⟩ := mem_closure_iff.mp hxmem _ hopen rfl
  have : (⊥ : Subfield A.valuation.Completion) ≤ (Rat.castHom A.valuation.Completion).fieldRange :=
    bot_le
  obtain ⟨q, hq⟩ := RingHom.mem_fieldRange.mp (this hybot)
  refine ⟨q, ?_⟩
  have hyx : Valued.v.restrict y = Valued.v.restrict x := hyV
  have h1 : Valued.v y ≤ Valued.v x := (Valuation.restrict_le_iff _).mp hyx.le
  have h2 : Valued.v x ≤ Valued.v y := (Valuation.restrict_le_iff _).mp hyx.ge
  rw [show (q : A.valuation.Completion) = y from hq]
  exact le_antisymm h1 h2

private theorem v_eq_zpow_of_mem_ratClosure (hr : r.Prime) (hA : A.LiesOverPrime r)
    {x : A.valuation.Completion}
    (hx : x ∈ ratClosure A) (hx0 : x ≠ 0) :
    ∃ n : ℤ, Valued.v x = Valued.v ((r : A.valuation.Completion)) ^ n := by
  obtain ⟨q, hq⟩ := exists_rat_v_eq A hx hx0
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [Rat.cast_zero, map_zero] at hq
    exact hx0 ((map_eq_zero _).mp hq.symm)
  obtain ⟨n, hn⟩ := vA_ratCast_eq_zpow A hr hA hq0
  exact ⟨n, by rw [← hq, v_ratCast, hn, v_natCast]⟩

end ValuationOfRatClosure

section Roots

variable (A : ValuationSubring (AlgebraicClosure ℚ)) {r : ℕ}

private theorem pow_ne_natCast_of_mem_ratClosure (hr : r.Prime) (hA : A.LiesOverPrime r) {k : ℕ}
    (hk : 2 ≤ k) {x : A.valuation.Completion} (hx : x ∈ ratClosure A) :
    x ^ k ≠ (r : A.valuation.Completion) := by
  intro hxk
  have hvr : Valued.v ((r : A.valuation.Completion)) = A.valuation (r : AlgebraicClosure ℚ) :=
    v_natCast A r
  have hvr1 : Valued.v ((r : A.valuation.Completion)) < 1 := by
    rw [hvr]; exact A.mem_nonunits_iff.mp hA
  have hvr0 : 0 < Valued.v ((r : A.valuation.Completion)) := by
    rw [hvr]; exact zero_lt_iff.mpr ((map_ne_zero _).mpr (by exact_mod_cast hr.ne_zero))
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hxk
    exact hvr0.ne' (by rw [← hxk, map_zero])
  obtain ⟨n, hn⟩ := v_eq_zpow_of_mem_ratClosure A hr hA hx hx0
  have h := congrArg Valued.v hxk
  rw [map_pow, hn, ← zpow_natCast, ← zpow_mul] at h
  have h' : Valued.v ((r : A.valuation.Completion)) ^ (n * (k : ℤ)) =
      Valued.v ((r : A.valuation.Completion)) ^ (1 : ℤ) := by
    rw [zpow_one]; exact h
  have hinj := (zpow_right_strictAnti₀ hvr0 hvr1).injective h'
  have : (k : ℤ) ∣ 1 := ⟨n, by rw [mul_comm]; exact hinj.symm⟩
  have hk1 : (k : ℤ) ≤ 1 := Int.le_of_dvd one_pos this
  omega

private theorem exists_pow_eq_natCast (hr : r.Prime) (hA : A.LiesOverPrime r) {k : ℕ} (hk : 0 < k) :
    ∃ d : A.valuation.Completion, d ^ k = (r : A.valuation.Completion) := by
  have := isAlgClosed_completion_of_liesOverPrime r hr A hA
  exact IsAlgClosed.exists_pow_nat_eq _ hk

end Roots

section Degree

variable (A : ValuationSubring (AlgebraicClosure ℚ)) {r : ℕ}

private noncomputable def pk (r k : ℕ) : Polynomial ↥(ratClosure A) :=
  Polynomial.X ^ k - Polynomial.C ((r : ℕ) : ↥(ratClosure A))

private theorem pk_monic {k : ℕ} (hk : 0 < k) : (pk A r k).Monic := by
  unfold pk; exact Polynomial.monic_X_pow_sub_C _ (Nat.pos_iff_ne_zero.mp hk)

private theorem pk_natDegree {k : ℕ} : (pk A r k).natDegree = k := by
  unfold pk; rw [Polynomial.natDegree_X_pow_sub_C]

private theorem aeval_pk {k : ℕ} {d : A.valuation.Completion}
    (hd : d ^ k = (r : A.valuation.Completion)) :
    Polynomial.aeval d (pk A r k) = 0 := by
  unfold pk
  rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hd, map_natCast, sub_self]

private theorem isIntegral_of_pow_eq {k : ℕ} (hk : 0 < k) {d : A.valuation.Completion}
    (hd : d ^ k = (r : A.valuation.Completion)) :
    IsIntegral ↥(ratClosure A) d :=
  ⟨pk A r k, pk_monic A hk, by rw [← Polynomial.aeval_def]; exact aeval_pk A hd⟩

private theorem pk_irreducible (hr : r.Prime) (hA : A.LiesOverPrime r) {k : ℕ} (hk2 : 2 ≤ k)
    (hk3 : k ≤ 3) :
    Irreducible (pk A r k) := by
  have hk : 0 < k := by omega
  rw [(pk_monic A hk).irreducible_iff_roots_eq_zero_of_degree_le_three
      (by rw [pk_natDegree A]; exact hk2) (by rw [pk_natDegree A]; exact hk3),
    Multiset.eq_zero_iff_forall_notMem]
  intro y hy
  rw [Polynomial.mem_roots (pk_monic A hk).ne_zero, Polynomial.IsRoot, pk, Polynomial.eval_sub,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hy
  have : (y : A.valuation.Completion) ^ k = (r : A.valuation.Completion) := by
    have := congrArg (Subtype.val : ↥(ratClosure A) → A.valuation.Completion) hy
    simpa using this
  exact pow_ne_natCast_of_mem_ratClosure A hr hA hk2 y.2 this

private theorem finrank_adjoin_eq (hr : r.Prime) (hA : A.LiesOverPrime r) {k : ℕ} (hk2 : 2 ≤ k)
    (hk3 : k ≤ 3) {d : A.valuation.Completion} (hd : d ^ k = (r : A.valuation.Completion)) :
    Module.finrank ↥(ratClosure A)
      ↥(IntermediateField.adjoin ↥(ratClosure A) ({d} : Set A.valuation.Completion)) = k := by
  have hk : 0 < k := by omega
  rw [IntermediateField.adjoin.finrank (isIntegral_of_pow_eq A hk hd),
    ← minpoly.eq_of_irreducible_of_monic (pk_irreducible A hr hA hk2 hk3) (aeval_pk A hd)
      (pk_monic A hk),
    pk_natDegree A]

private theorem adjoin_inf_adjoin_eq_bot (hr : r.Prime) (hA : A.LiesOverPrime r)
    {d₂ d₃ : A.valuation.Completion}
    (h₂ : d₂ ^ 2 = (r : A.valuation.Completion)) (h₃ : d₃ ^ 3 = (r : A.valuation.Completion)) :
    IntermediateField.adjoin ↥(ratClosure A) ({d₂} : Set A.valuation.Completion) ⊓
        IntermediateField.adjoin ↥(ratClosure A) ({d₃} : Set A.valuation.Completion)
      = ⊥ := by
  have hd2 := IntermediateField.finrank_dvd_of_le_right
    (inf_le_left : IntermediateField.adjoin ↥(ratClosure A) ({d₂} : Set _) ⊓
        IntermediateField.adjoin ↥(ratClosure A) ({d₃} : Set _) ≤ _)
  have hd3 := IntermediateField.finrank_dvd_of_le_right
    (inf_le_right : IntermediateField.adjoin ↥(ratClosure A) ({d₂} : Set _) ⊓
        IntermediateField.adjoin ↥(ratClosure A) ({d₃} : Set _) ≤ _)
  rw [finrank_adjoin_eq A hr hA le_rfl (by norm_num) h₂] at hd2
  rw [finrank_adjoin_eq A hr hA (by norm_num) le_rfl h₃] at hd3
  have := Nat.dvd_gcd hd2 hd3
  norm_num at this
  exact this

end Degree

section Uncountable

variable (A : ValuationSubring (AlgebraicClosure ℚ)) {r : ℕ}

private theorem not_countable_nat_bool : ¬ Countable (ℕ → Bool) := by
  classical
  intro h
  have := h
  obtain ⟨g, hg⟩ := Countable.exists_injective_nat (ℕ → Bool)
  let e : Set ℕ → (ℕ → Bool) := fun s n => decide (n ∈ s)
  have he : Function.Injective e := by
    intro s t hst
    ext n
    have := congr_fun hst n
    simpa [e] using this
  exact Function.cantor_injective (g ∘ e) (hg.comp he)

private theorem not_countable_ratClosure (hr : r.Prime) (hA : A.LiesOverPrime r)
    (hrk : ∀ x y : A.valuation.Completion, Valued.v x < 1 → y ≠ 0 →
      ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y) :
    ¬ (ratClosure A : Set A.valuation.Completion).Countable := by
  classical
  have hvr : Valued.v ((r : A.valuation.Completion)) = A.valuation (r : AlgebraicClosure ℚ) :=
    v_natCast A r
  have hvr1 : Valued.v ((r : A.valuation.Completion)) < 1 := by
    rw [hvr]; exact A.mem_nonunits_iff.mp hA
  have hvr0 : Valued.v ((r : A.valuation.Completion)) ≠ 0 := by
    rw [hvr]; exact (map_ne_zero _).mpr (by exact_mod_cast hr.ne_zero)
  have hrC0 : (r : A.valuation.Completion) ≠ 0 := fun h => hvr0 (by rw [h, map_zero])
  have hnt' : (Valued.v : Valuation A.valuation.Completion A.ValueGroup).IsNontrivial :=
    ⟨⟨(r : A.valuation.Completion), hvr0, hvr1.ne⟩⟩
  have hMA := Valued.mulArchimedean_valueGroup₀_of_exists_pow_le hrk
  let hRO : Valuation.RankOne (Valued.v : Valuation A.valuation.Completion A.ValueGroup) :=
    (Valuation.nonempty_rankOne_iff_mulArchimedean.mpr hMA).some
  let : NontriviallyNormedField A.valuation.Completion :=
    Valued.toNontriviallyNormedField A.valuation.Completion A.ValueGroup
  have hnr1 : ‖(r : A.valuation.Completion)‖ < 1 := Valued.toNormedField.norm_lt_one_iff.mpr hvr1
  have hnr0 : 0 ≤ ‖(r : A.valuation.Completion)‖ := norm_nonneg _
  have hperf : Perfect (ratClosure A : Set A.valuation.Completion) := by
    refine ⟨isClosed_ratClosure A, fun x hx => ?_⟩
    rw [accPt_iff_nhds]
    intro U hU
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hnr1
    refine ⟨x + (r : A.valuation.Completion) ^ (n + 1), ⟨hball ?_, ?_⟩, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_pow, pow_succ]
      exact lt_of_le_of_lt (mul_le_of_le_one_right (pow_nonneg hnr0 n) hnr1.le) hn
    · exact (ratClosure A).add_mem hx ((ratClosure A).pow_mem (natCast_mem_ratClosure A r) _)
    · intro h
      exact pow_ne_zero (n + 1) hrC0 (by simpa using h)
  intro hcount
  obtain ⟨f, hfK, -, hfinj⟩ :=
    hperf.exists_nat_bool_injection ⟨0, SetLike.mem_coe.mpr (ratClosure A).zero_mem⟩
  have hcr : (Set.range f).Countable := hcount.mono hfK
  have : Countable ↥(Set.range f) := hcr.to_subtype
  have : Countable (ℕ → Bool) :=
    (Function.Injective.of_comp (f := (Subtype.val : ↥(Set.range f) → A.valuation.Completion))
      (show Function.Injective
        (Subtype.val ∘ fun a : ℕ → Bool => (⟨f a, ⟨a, rfl⟩⟩ : ↥(Set.range f))) from
          hfinj)).countable
  exact not_countable_nat_bool this

end Uncountable

section Closed

variable (A : ValuationSubring (AlgebraicClosure ℚ)) {r : ℕ}

private theorem finiteDimensional_adjoin {k : ℕ} (hk : 0 < k) {d : A.valuation.Completion}
    (hd : d ^ k = (r : A.valuation.Completion)) :
    FiniteDimensional ↥(ratClosure A)
      ↥(IntermediateField.adjoin ↥(ratClosure A) ({d} : Set A.valuation.Completion)) :=
  IntermediateField.adjoin.finiteDimensional (isIntegral_of_pow_eq A hk hd)

private theorem ratClosure_le_toSubfield
    (F : IntermediateField ↥(ratClosure A) A.valuation.Completion) :
    ratClosure A ≤ F.toSubfield := fun x hx => F.algebraMap_mem ⟨x, hx⟩

private theorem isClosed_toSubfield (hr : r.Prime) (hA : A.LiesOverPrime r)
    (hrk : ∀ x y : A.valuation.Completion, Valued.v x < 1 → y ≠ 0 →
      ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (F : IntermediateField ↥(ratClosure A) A.valuation.Completion)
    [hF : FiniteDimensional ↥(ratClosure A) ↥F] :
    IsClosed (F.toSubfield : Set A.valuation.Completion) := by
  have hvr : Valued.v ((r : A.valuation.Completion)) = A.valuation (r : AlgebraicClosure ℚ) :=
    v_natCast A r
  have hnt : ∃ x ∈ ratClosure A, x ≠ 0 ∧ Valued.v x < 1 := by
    refine ⟨(r : A.valuation.Completion), natCast_mem_ratClosure A r, fun h => ?_, ?_⟩
    · have : Valued.v ((r : A.valuation.Completion)) = 0 := by rw [h, map_zero]
      rw [hvr] at this
      exact (map_ne_zero A.valuation).mpr (by exact_mod_cast hr.ne_zero) this
    · rw [hvr]; exact A.mem_nonunits_iff.mp hA
  have : FiniteDimensional ↥(ratClosure A) ↥(F.toSubalgebra.toSubmodule) :=
    Subalgebra.finiteDimensional_toSubmodule.mpr hF
  exact Valued.isClosed_submodule_of_finiteDimensional_of_isClosed_subfield
    A.valuation.Completion hrk (ratClosure A) (isClosed_ratClosure A) hnt F.toSubalgebra.toSubmodule

private theorem toSubfield_inf_toSubfield_eq
    {F G : IntermediateField ↥(ratClosure A) A.valuation.Completion} (h : F ⊓ G = ⊥) :
    F.toSubfield ⊓ G.toSubfield = ratClosure A := by
  ext x
  constructor
  · rintro ⟨hxF, hxG⟩
    have hx : x ∈ F ⊓ G := IntermediateField.mem_inf.mpr ⟨hxF, hxG⟩
    rw [h, IntermediateField.mem_bot] at hx
    obtain ⟨y, rfl⟩ := hx
    exact y.2
  · intro hx
    exact ⟨ratClosure_le_toSubfield A F hx, ratClosure_le_toSubfield A G hx⟩

private theorem mem_toSubfield_adjoin_self (d : A.valuation.Completion) :
    d ∈ (IntermediateField.adjoin ↥(ratClosure A) ({d} : Set A.valuation.Completion)).toSubfield :=
  IntermediateField.mem_adjoin_simple_self _ d

private theorem not_countable_sdiff (hr : r.Prime) (hA : A.LiesOverPrime r)
    (hrk : ∀ x y : A.valuation.Completion, Valued.v x < 1 → y ≠ 0 →
      ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (L : Subfield A.valuation.Completion) (d : A.valuation.Completion) (hKL : ratClosure A ≤ L)
    (hdL : d ∈ L) (hdK : d ∉ ratClosure A) :
    ¬ ((L : Set A.valuation.Completion) \ ↑(ratClosure A)).Countable := by
  intro hc
  apply not_countable_ratClosure A hr hA hrk
  refine (hc.image fun y => y - d).mono fun t ht => ?_
  refine ⟨d + t, ⟨L.add_mem hdL (hKL ht), fun h => hdK ?_⟩, by ring⟩
  have : d = (d + t) - t := by ring
  rw [this]; exact (ratClosure A).sub_mem h ht

end Closed

end TwoSubfields

open TwoSubfields in
/-- If `A` is a valuation subring of an algebraic closure of `ℚ` lying over a rational prime
`r`, then the completion of `A.valuation` contains two closed subfields containing
`ratClosure A` whose intersection is exactly `ratClosure A`, each with uncountably many
elements outside `ratClosure A`. -/
public theorem exists_two_closed_subfields_completion_inf_eq_ratClosure_of_liesOverPrime
    (r : ℕ) [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r) :
    ∃ L₁ L₂ : Subfield A.valuation.Completion,
      ratClosure A ≤ L₁ ∧ ratClosure A ≤ L₂ ∧
      IsClosed (L₁ : Set A.valuation.Completion) ∧ IsClosed (L₂ : Set A.valuation.Completion) ∧
      L₁ ⊓ L₂ = ratClosure A ∧
      ¬ ((L₁ : Set A.valuation.Completion) \ ↑(ratClosure A)).Countable ∧
      ¬ ((L₂ : Set A.valuation.Completion) \ ↑(ratClosure A)).Countable := by
  have hrp : r.Prime := Fact.out
  have hrk := exists_pow_le_of_liesOverPrime r hrp A hA
  obtain ⟨d₂, hd₂⟩ := exists_pow_eq_natCast A hrp hA (k := 2) two_pos
  obtain ⟨d₃, hd₃⟩ := exists_pow_eq_natCast A hrp hA (k := 3) three_pos
  have hF₂ := finiteDimensional_adjoin A two_pos hd₂
  have hF₃ := finiteDimensional_adjoin A three_pos hd₃
  exact ⟨_, _, ratClosure_le_toSubfield A _, ratClosure_le_toSubfield A _,
    isClosed_toSubfield A hrp hA hrk _, isClosed_toSubfield A hrp hA hrk _,
    toSubfield_inf_toSubfield_eq A (adjoin_inf_adjoin_eq_bot A hrp hA hd₂ hd₃),
    not_countable_sdiff A hrp hA hrk _ d₂ (ratClosure_le_toSubfield A _)
      (mem_toSubfield_adjoin_self A d₂)
      (fun h => pow_ne_natCast_of_mem_ratClosure A hrp hA le_rfl h hd₂),
    not_countable_sdiff A hrp hA hrk _ d₃ (ratClosure_le_toSubfield A _)
      (mem_toSubfield_adjoin_self A d₃)
      (fun h => pow_ne_natCast_of_mem_ratClosure A hrp hA (by norm_num) h hd₃)⟩

end ValuationSubring

end
