/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.MvFormalGroup.End
public import MathlibExt.RingTheory.MvPowerSeries.MvFormalGroupRescaledLog

@[expose] public section

noncomputable section

namespace MetaMathlibExt

open MvPowerSeries

universe u

/-- Consumer with the original binders, restated verbatim. -/
private theorem exactSource {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime]
    (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    {d : ℕ} (F : MvFormalGroup d 𝓞) [F.IsComm] :
    ∃ (Fp : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞) (φ : Fin d → MvPowerSeries (Fin d) 𝓞),
      (∀ (i : Fin d) (m : (Fin d ⊕ Fin d) →₀ ℕ), m ≠ 0 →
        (Fp i).coeff m * (p : 𝓞) = (p : 𝓞) ^ m.degree * (F.toPowerSeries i).coeff m) ∧
      (∀ i, (Fp i).constantCoeff = 0) ∧
      (∀ i, (φ i).constantCoeff = 0) ∧
      MvFormalGroup.linearPart φ = 1 ∧
      (∀ (N : ℕ) (i : Fin d), ∀ᶠ m in Filter.cofinite,
        (φ i).coeff m ∈ Ideal.span {(p : 𝓞) ^ N}) ∧
      (∀ i, subst Fp (φ i) =
        subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i) +
          subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i)) :=
  MvFormalGroup.exists_rescaledLog_of_isAdicComplete p hp F

/-- The statement also applies in a higher universe. -/
example {𝓞 : Type (u + 1)} [CommRing 𝓞] (p : ℕ) [Fact p.Prime]
    (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞) [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    {d : ℕ} (F : MvFormalGroup d 𝓞) [F.IsComm] :
    ∃ φ : Fin d → MvPowerSeries (Fin d) 𝓞, MvFormalGroup.linearPart φ = 1 := by
  obtain ⟨-, φ, -, -, -, h, -⟩ := MvFormalGroup.exists_rescaledLog_of_isAdicComplete p hp F
  exact ⟨φ, h⟩

/-- The additive formal group law is commutative, so it has such a logarithm. -/
example {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime]
    (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞) [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] (d : ℕ) :
    ∃ φ : Fin d → MvPowerSeries (Fin d) 𝓞,
      (∀ i, (φ i).constantCoeff = 0) ∧ MvFormalGroup.linearPart φ = 1 := by
  obtain ⟨-, φ, -, -, h0, h1, -⟩ :=
    MvFormalGroup.exists_rescaledLog_of_isAdicComplete p hp (MvFormalGroup.addMv d 𝓞)
  exact ⟨φ, h0, h1⟩

/-- The rescaling of the additive formal group law is itself: it has no terms of degree `≥ 2`,
and the degree-one terms are multiplied by `a ^ 0`. -/
example {R : Type*} [CommRing R] {a : R} (ha : a ∈ nonZeroDivisors R) (d : ℕ) :
    (MvFormalGroup.addMv d R).rescale ha = MvFormalGroup.addMv d R := by
  apply MvFormalGroup.ext
  funext i
  ext m
  rw [MvFormalGroup.coeff_rescale]
  change (if m = 0 then 0 else a ^ (m.degree - 1) *
    coeff m (X (Sum.inl i) + X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R)) =
      coeff m (X (Sum.inl i) + X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R)
  by_cases h : m = Finsupp.single (Sum.inl i) 1 ∨ m = Finsupp.single (Sum.inr i) 1
  · rcases h with rfl | rfl <;> simp
  · simp only [not_or] at h
    simp [coeff_X, h.1, h.2]

/-- The coefficients of total degree `n ≥ 1` of `F.rescale ha`, multiplied by `a`, are those of
`F` multiplied by `a ^ n`. -/
example {R : Type*} [CommRing R] {a : R} (ha : a ∈ nonZeroDivisors R) {d : ℕ}
    (F : MvFormalGroup d R) (i : Fin d) (m : Fin d ⊕ Fin d →₀ ℕ) (hm : m ≠ 0) :
    coeff m ((F.rescale ha).toPowerSeries i) * a = a ^ m.degree * coeff m (F.toPowerSeries i) := by
  obtain ⟨t, ht⟩ : ∃ t, m.degree = t + 1 :=
    ⟨m.degree - 1, by have := (Finsupp.degree_eq_zero_iff m).not.mpr hm; omega⟩
  rw [MvFormalGroup.coeff_rescale, ite_eq_right hm, ht, Nat.add_sub_cancel, pow_succ]
  ring

/-- The rescaling of a commutative formal group law is commutative, so its endomorphisms form a
semiring. -/
example {R : Type*} [CommRing R] {a : R} (ha : a ∈ nonZeroDivisors R) {d : ℕ}
    (F : MvFormalGroup d R) [F.IsComm] : Semiring (MvFormalGroup.End (F.rescale ha)) :=
  inferInstance

/-- The logarithm of `MvFormalGroup.exists_log_rescale_of_isAdicComplete` is a homomorphism from
`F.rescale hp` to the additive formal group law with identity linear part. -/
example {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime]
    (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞) [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    {d : ℕ} (F : MvFormalGroup d 𝓞) [F.IsComm] :
    ∃ φ : MvFormalGroup.Hom (F.rescale hp) (MvFormalGroup.addMv d 𝓞),
      MvFormalGroup.linearPart φ.toPowerSeries = 1 := by
  obtain ⟨φ, h0, h1, -, hlog⟩ := MvFormalGroup.exists_log_rescale_of_isAdicComplete p hp F
  refine ⟨⟨φ, h0, fun i => ?_⟩, h1⟩
  have hX : ∀ s : Fin d ⊕ Fin d, constantCoeff (X s : MvPowerSeries (Fin d ⊕ Fin d) 𝓞) = 0 :=
    fun s => constantCoeff_X s
  rw [hlog i]
  change _ = subst _ (X (Sum.inl i) + X (Sum.inr i))
  rw [MvFormalGroup.subst_X_add_X (by
    rintro (j | j)
    exacts [constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun l => hX _)
        (fun l => hX _) (h0 j),
      constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun l => hX _)
        (fun l => hX _) (h0 j)])]
  rfl

end MetaMathlibExt
