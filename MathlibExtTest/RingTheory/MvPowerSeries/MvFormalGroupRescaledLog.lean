/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

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


/-- Rescaling the additive formal group law gives it back: it has no terms of degree `≥ 2`, and
the degree-one terms are multiplied by `a ^ 0`. -/
example {R : Type*} [CommRing R] (a : R) (d : ℕ) :
    (MvFormalGroup.addMv d R).rescale a = MvFormalGroup.addMv d R := by
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

/-- Rescaling by `1` gives back `F`. -/
example {R : Type*} [CommRing R] {d : ℕ} (F : MvFormalGroup d R) : F.rescale 1 = F := by
  apply MvFormalGroup.ext
  funext i
  ext m
  rw [MvFormalGroup.coeff_rescale, one_pow, one_mul]
  split_ifs with hm
  · rw [hm, coeff_zero_eq_constantCoeff_apply, F.constantCoeff_eq_zero]
  · rfl

/-- Rescaling by the zero divisor `0` keeps only the linear terms, which are those of the additive
law, so it gives the additive formal group law whatever `F` is. -/
example {R : Type*} [CommRing R] {d : ℕ} (F : MvFormalGroup d R) :
    F.rescale 0 = MvFormalGroup.addMv d R := by
  apply MvFormalGroup.ext
  funext i
  ext m
  rw [MvFormalGroup.coeff_rescale]
  change _ = coeff m (X (Sum.inl i) + X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R)
  split_ifs with hm
  · rw [hm, coeff_zero_eq_constantCoeff_apply, map_add, constantCoeff_X, constantCoeff_X,
      add_zero]
  · by_cases h1 : m.degree = 1
    · obtain ⟨s, rfl⟩ : ∃ s, Finsupp.single s 1 = m := by
        have hmem : m ∈ {d' : Fin d ⊕ Fin d →₀ ℕ | d'.degree = 1} := h1
        rw [← Finsupp.range_single_one] at hmem
        exact hmem
      rw [h1, Nat.sub_self, pow_zero, one_mul]
      rcases s with j | j
      · rw [F.coeff_single_inl]
        by_cases hij : i = j
        · subst hij; simp [coeff_X, Finsupp.single_left_inj one_ne_zero]
        · simp [coeff_X, Finsupp.single_left_inj one_ne_zero, hij, Ne.symm hij]
      · rw [F.coeff_single_inr]
        by_cases hij : i = j
        · subst hij; simp [coeff_X, Finsupp.single_left_inj one_ne_zero]
        · simp [coeff_X, Finsupp.single_left_inj one_ne_zero, hij, Ne.symm hij]
    · have hl : m ≠ Finsupp.single (Sum.inl i) 1 := by
        rintro rfl; exact h1 (Finsupp.degree_single _ _)
      have hr : m ≠ Finsupp.single (Sum.inr i) 1 := by
        rintro rfl; exact h1 (Finsupp.degree_single _ _)
      rw [zero_pow (by have := (Finsupp.degree_eq_zero_iff m).not.mpr hm; omega), zero_mul,
        map_add, coeff_X, coeff_X, ite_eq_right hl, ite_eq_right hr, add_zero]

/-- The coefficients of total degree `n ≥ 1` of `F.rescale a`, multiplied by `a`, are those of
`F` multiplied by `a ^ n`. -/
example {R : Type*} [CommRing R] (a : R) {d : ℕ}
    (F : MvFormalGroup d R) (i : Fin d) (m : Fin d ⊕ Fin d →₀ ℕ) (hm : m ≠ 0) :
    coeff m ((F.rescale a).toPowerSeries i) * a = a ^ m.degree * coeff m (F.toPowerSeries i) := by
  obtain ⟨t, ht⟩ : ∃ t, m.degree = t + 1 :=
    ⟨m.degree - 1, by have := (Finsupp.degree_eq_zero_iff m).not.mpr hm; omega⟩
  rw [MvFormalGroup.coeff_rescale, ite_eq_right hm, ht, Nat.add_sub_cancel, pow_succ]
  ring

/-- The rescaling of a commutative formal group law is commutative, so its endomorphisms form a
semiring. -/
example {R : Type*} [CommRing R] (a : R) {d : ℕ}
    (F : MvFormalGroup d R) [F.IsComm] : Semiring (MvFormalGroup.End (F.rescale a)) :=
  inferInstance

/-- The logarithm of `MvFormalGroup.exists_log_rescale_of_isAdicComplete` is a homomorphism from
`F.rescale p` to the additive formal group law with identity linear part. -/
example {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime]
    (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞) [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    {d : ℕ} (F : MvFormalGroup d 𝓞) [F.IsComm] :
    ∃ φ : MvFormalGroup.Hom (F.rescale (p : 𝓞)) (MvFormalGroup.addMv d 𝓞),
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
