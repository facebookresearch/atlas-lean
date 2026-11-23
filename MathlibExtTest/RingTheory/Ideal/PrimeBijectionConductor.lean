/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Int.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import MathlibExt.RingTheory.Ideal.PrimeBijectionConductor

@[expose] public section

namespace PrimeBijectionConductorTest

/-- Denominator-clearing ideal `𝔠 = span {6}` in `ℤ`, identity algebra: the comaximality
hypothesis holds because every nonzero prime of `ℤ` is maximal. -/
noncomputable def equivSix : {𝔮 : Ideal ℤ // 𝔮.IsPrime ∧ 𝔮 ≠ ⊥ ∧
    ¬ ((Ideal.span {(6 : ℤ)}).map (algebraMap ℤ ℤ) ≤ 𝔮)} ≃
    {𝔭 : Ideal ℤ // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ Ideal.span {(6 : ℤ)} ≤ 𝔭} :=
  Ideal.primeEquivOfCoprimeConductor (by simpa using Function.injective_id)
    (Ideal.span {(6 : ℤ)})
    (by rw [ne_eq, Ideal.span_singleton_eq_bot]; norm_num)
    (fun c _ b => ⟨c * b, rfl⟩)
    (fun 𝔭 h𝔭 hne hnc => by
      have hne' : 𝔭 ≠ Ideal.span {(6 : ℤ)} ⊔ 𝔭 := fun h =>
        hnc (h ▸ le_sup_left)
      exact (Ideal.isMaximal_def.1 (h𝔭.isMaximal hne)).2 _
        (lt_of_le_of_ne le_sup_right hne'))

/-- The prime `(5)` of `ℤ`, as an element of the domain of `equivSix`:
it does not contain `(6)`. -/
def primeFiveDomain : {𝔮 : Ideal ℤ // 𝔮.IsPrime ∧ 𝔮 ≠ ⊥ ∧
    ¬ (Ideal.span {(6 : ℤ)}).map (algebraMap ℤ ℤ) ≤ 𝔮} := by
  refine ⟨Ideal.span {(5 : ℤ)}, ?_, ?_, ?_⟩
  · rw [Ideal.span_singleton_prime (by norm_num),
      Int.prime_iff_natAbs_prime]
    exact by decide
  · rw [ne_eq, Ideal.span_singleton_eq_bot]
    norm_num
  · rw [show algebraMap ℤ ℤ = RingHom.id ℤ from rfl, Ideal.map_id,
      Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]
    norm_num

/-- The forward map of `equivSix` is contraction. -/
theorem equivSix_apply (𝔮 : {𝔮 : Ideal ℤ // 𝔮.IsPrime ∧ 𝔮 ≠ ⊥ ∧
    ¬ (Ideal.span {(6 : ℤ)}).map (algebraMap ℤ ℤ) ≤ 𝔮}) :
    (equivSix 𝔮).1 = 𝔮.1.comap (algebraMap ℤ ℤ) :=
  Ideal.primeEquivOfCoprimeConductor_apply _ _ _ _ _ _

/-- The prime `(5)` is carried to itself. -/
example : (equivSix primeFiveDomain).1 = Ideal.span {(5 : ℤ)} := by
  rw [equivSix_apply,
    show primeFiveDomain.1 = Ideal.span {(5 : ℤ)} from rfl,
    show algebraMap ℤ ℤ = RingHom.id ℤ from rfl, Ideal.comap_id]

/-- The prime `(2)` is excluded: it contains `(6)`. -/
example : (Ideal.span {(6 : ℤ)}).map (algebraMap ℤ ℤ) ≤
    Ideal.span {(2 : ℤ)} := by
  rw [show algebraMap ℤ ℤ = RingHom.id ℤ from rfl, Ideal.map_id,
    Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]
  exact ⟨3, by norm_num⟩

/-- Round trip: applying the equivalence and its inverse returns `(5)`. -/
example : equivSix.symm (equivSix primeFiveDomain) = primeFiveDomain :=
  Equiv.symm_apply_apply _ _

/-- The full spectra away from `(6)`, including their generic points. -/
noncomputable def allEquivSix : {𝔮 : Ideal ℤ // 𝔮.IsPrime ∧
    ¬ ((Ideal.span {(6 : ℤ)}).map (algebraMap ℤ ℤ) ≤ 𝔮)} ≃
    {𝔭 : Ideal ℤ // 𝔭.IsPrime ∧ ¬ Ideal.span {(6 : ℤ)} ≤ 𝔭} :=
  Ideal.primeEquivOfNotLeConductor (by simpa using Function.injective_id)
    (Ideal.span {(6 : ℤ)})
    (by rw [ne_eq, Ideal.span_singleton_eq_bot]; norm_num)
    (fun c _ b => ⟨c * b, rfl⟩)
    (fun 𝔭 h𝔭 hne hnc => by
      have hne' : 𝔭 ≠ Ideal.span {(6 : ℤ)} ⊔ 𝔭 := fun h =>
        hnc (h ▸ le_sup_left)
      exact (Ideal.isMaximal_def.1 (h𝔭.isMaximal hne)).2 _
        (lt_of_le_of_ne le_sup_right hne'))

/-- The generic point of `Spec ℤ` does not contain `(6)`. -/
def primeZeroDomain : {𝔮 : Ideal ℤ // 𝔮.IsPrime ∧
    ¬ (Ideal.span {(6 : ℤ)}).map (algebraMap ℤ ℤ) ≤ 𝔮} := by
  refine ⟨⊥, inferInstance, ?_⟩
  rw [show algebraMap ℤ ℤ = RingHom.id ℤ from rfl, Ideal.map_id,
    Ideal.span_singleton_le_iff_mem, Ideal.mem_bot]
  norm_num

/-- The same generic point in the target spectrum away from `(6)`. -/
def primeZeroCodomain : {𝔭 : Ideal ℤ // 𝔭.IsPrime ∧
    ¬ Ideal.span {(6 : ℤ)} ≤ 𝔭} := by
  refine ⟨⊥, inferInstance, ?_⟩
  rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_bot]
  norm_num

/-- Contraction in the all-prime equivalence retains the generic point. -/
example : (allEquivSix primeZeroDomain).1 = ⊥ := by
  calc
    (allEquivSix primeZeroDomain).1 =
        primeZeroDomain.1.comap (algebraMap ℤ ℤ) :=
      Ideal.primeEquivOfNotLeConductor_apply _ _ _ _ _ _
    _ = ⊥ := Ideal.comap_bot_of_injective (algebraMap ℤ ℤ)
      (by simpa using Function.injective_id)

/-- Extension in the all-prime equivalence retains the generic point. -/
example : (allEquivSix.symm primeZeroCodomain).1 = ⊥ := by
  calc
    (allEquivSix.symm primeZeroCodomain).1 =
        primeZeroCodomain.1.map (algebraMap ℤ ℤ) :=
      Ideal.primeEquivOfNotLeConductor_symm_apply _ _ _ _ _ _
    _ = ⊥ := Ideal.map_bot (f := algebraMap ℤ ℤ)

end PrimeBijectionConductorTest
