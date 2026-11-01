/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Definitions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SpinIrreducible
public import Mathlib.RepresentationTheory.Character

/-! Character calculations for the real Schrödinger representation.

Its trace vanishes away from the center, while central elements have trace
4096 times their scalar sign. These calculations support the real spin-lift
existence proof. Every automorphism of Q fixing its center is implemented by
a bijective real linear intertwiner; orthogonal normalization is separate. -/

@[expose] public section
open Multiplicative
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

theorem sum_zero_of_equiv_neg {ι : Type*} [Fintype ι] (e : ι ≃ ι)
    (f : ι → ℝ) (hf : ∀ i, f (e i) = -f i) : (∑ i, f i) = 0 := by
  have h := Equiv.sum_comp e f
  simp_rw [hf] at h
  rw [Finset.sum_neg_distrib] at h
  exact eq_zero_of_neg_eq h

theorem binaryCharacter_sum_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → ZMod 2) (hb : b ≠ 0) :
    (∑ t : ι → ZMod 2, qSign (∑ i, b i * t i)) = 0 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, b i ≠ 0 := by
    by_contra hn
    apply hb
    funext i
    simpa using not_exists.mp hn i
  have hbi : b i = 1 := by
    have hv := (b i).val_lt
    have hn : (b i).val ≠ 0 := by intro h; exact hi ((ZMod.val_eq_zero _).mp h)
    apply ZMod.val_injective 2
    change (b i).val = 1
    omega
  have hdot : (∑ j, b j * (Pi.single i 1 : ι → ZMod 2) j) = 1 := by
    simp only [ Pi.single_apply, mul_ite, mul_one, mul_zero]
    simpa using hbi
  apply sum_zero_of_equiv_neg (Equiv.addRight (Pi.single i 1 : ι → ZMod 2))
    (fun t : ι → ZMod 2 => qSign (∑ j, b j * t j))
  intro t
  change qSign (∑ j, b j * (t + (Pi.single i 1 : ι → ZMod 2)) j) = -qSign (∑ j, b j * t j)
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  rw [hdot, qSign_add]
  have hminus : qSign (1 : ZMod 2) = (-1 : ℝ) := by norm_num [qSign]
  rw [hminus, mul_neg_one]

theorem spinCharacter_sum_zero (b : SpinIndex) (hb : b ≠ 0) :
    (∑ t : SpinIndex, qSign (spinDot b t)) = 0 :=
  binaryCharacter_sum_zero b hb

noncomputable def spinCoordinateTrace (e : SpinSpace →ₗ[ℝ] SpinSpace) : ℝ :=
  ∑ t, e (Pi.single t 1) t

theorem spinCoordinateTrace_eq_trace (e : SpinSpace →ₗ[ℝ] SpinSpace) :
    spinCoordinateTrace e = LinearMap.trace ℝ SpinSpace e := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (Pi.basisFun ℝ SpinIndex)]
  simp [spinCoordinateTrace, Matrix.trace]

theorem spinRepresentation_trace_noncentral (g : Q) (hg : g ∉ centerQ) :
    spinCoordinateTrace (spinRepresentation g).toLinearMap = 0 := by
  by_cases ha : spinTranslation g = 0
  · have hb : spinModulation g ≠ 0 := by
      intro hb
      apply hg
      apply (q_mem_center_iff_base_eq_one g).mpr
      apply Multiplicative.toAdd.injective
      funext i
      obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin 12 ⊕ Fin 12 ≃ Fin 24).surjective i
      cases j with
      | inl j => exact congrFun ha j
      | inr j => exact congrFun hb j
    change (∑ t, qSign (spinPhase g t) * (Pi.single t 1 : SpinSpace) (t + spinTranslation g)) = 0
    simp only [ha, add_zero, Pi.single_eq_same, mul_one, spinPhase, qSign_add,
      ← Finset.mul_sum, spinCharacter_sum_zero _ hb, mul_zero]
  · change (∑ t, qSign (spinPhase g t) * (Pi.single t 1 : SpinSpace) (t + spinTranslation g)) = 0
    apply Finset.sum_eq_zero
    intro t _
    have ht : t + spinTranslation g ≠ t := by
      intro ht
      apply ha
      exact add_left_cancel (show t + spinTranslation g = t + 0 by simpa using ht)
    simp [ht]


theorem spinRepresentation_trace_central (c : ZMod 2) :
    spinCoordinateTrace (spinRepresentation (qCentral c)).toLinearMap = 4096 * qSign c := by
  change (∑ t : SpinIndex, spinRepresentation (qCentral c) (Pi.single t 1) t) = _
  simp only [spinRepresentation_central, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same,
    mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : Fintype.card SpinIndex = 4096 := by
    change Fintype.card (Fin 12 → ZMod 2) = 4096
    rw [Fintype.card_fun, ZMod.card]
    norm_num
  rw [hcard]
  norm_num

theorem spinRepresentation_trace_noncentral' (g : Q) (hg : g ∉ centerQ) :
    LinearMap.trace ℝ SpinSpace (spinRepresentation g).toLinearMap = 0 := by
  rw [← spinCoordinateTrace_eq_trace]
  exact spinRepresentation_trace_noncentral g hg

open Representation

noncomputable def spinEndScalar : ℝ →ₗ[ℝ]
    IntertwiningMap spinLinearRepresentation spinLinearRepresentation :=
  LinearMap.toSpanSingleton ℝ _ 1

theorem spinEndScalar_bijective : Function.Bijective spinEndScalar := by
  constructor
  · intro a b hab
    have h := congrArg (fun t : IntertwiningMap spinLinearRepresentation spinLinearRepresentation =>
      t (Pi.single 0 1) 0) hab
    change a * (1 : ℝ) = b * (1 : ℝ) at h
    simpa using h
  · intro t
    obtain ⟨c, hc⟩ := spinRepresentation_commutant_linear_scalar t.toLinearMap
      (fun q x => IntertwiningMap.isIntertwining
        spinLinearRepresentation spinLinearRepresentation t q x)
    refine ⟨c, ?_⟩
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change c • x = t x
    exact (hc x).symm

theorem spinEnd_finrank :
    Module.finrank ℝ (IntertwiningMap spinLinearRepresentation spinLinearRepresentation) = 1 := by
  rw [← (LinearEquiv.ofBijective spinEndScalar spinEndScalar_bijective).finrank_eq]
  exact Module.finrank_self ℝ

noncomputable def spinTwistedRepresentation (a : MulAut Q) : Representation ℝ Q SpinSpace :=
  spinLinearRepresentation.comp a.toMonoidHom

theorem spinTwisted_character (a : MulAut Q) (ha : ∀ c, a (qCentral c) = qCentral c) :
    (spinTwistedRepresentation a).character = spinLinearRepresentation.character := by
  funext g
  by_cases hg : g ∈ centerQ
  · have hgb := (q_mem_center_iff_base_eq_one g).mp hg
    have hgc : g = qCentral (Multiplicative.toAdd g.coeff) := by
      apply NormalizedCocycleExtension.Extension.ext
      · exact hgb
      · rfl
    rw [hgc]
    change LinearMap.trace ℝ SpinSpace (spinRepresentation (a (qCentral _))).toLinearMap =
      LinearMap.trace ℝ SpinSpace (spinRepresentation (qCentral _)).toLinearMap
    rw [ha]
  · have hag : a g ∉ centerQ := by
      intro hh
      apply hg
      apply Subgroup.mem_center_iff.mpr
      intro k
      apply a.injective
      rw [map_mul, map_mul]
      exact Subgroup.mem_center_iff.mp hh (a k)
    change LinearMap.trace ℝ SpinSpace (spinRepresentation (a g)).toLinearMap =
      LinearMap.trace ℝ SpinSpace (spinRepresentation g).toLinearMap
    rw [spinRepresentation_trace_noncentral' _ hag, spinRepresentation_trace_noncentral' _ hg]
theorem spinTwisted_intertwiner_finrank (a : MulAut Q)
    (ha : ∀ c, a (qCentral c) = qCentral c) :
    Module.finrank ℝ
      (IntertwiningMap spinLinearRepresentation (spinTwistedRepresentation a)) = 1 := by
  let : Finite Q := q_finite_coordinates
  let : Fintype Q := Fintype.ofFinite Q
  let : Invertible (Nat.card Q : ℝ) := invertibleOfNonzero (by
    exact_mod_cast (Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩ : Nat.card Q ≠ 0))
  have h := card_inv_mul_sum_char_mul_char_eq_finrank
    spinLinearRepresentation (spinTwistedRepresentation a)
  rw [spinTwisted_character a ha] at h
  have hself := card_inv_mul_sum_char_mul_char_eq_finrank
    spinLinearRepresentation spinLinearRepresentation
  rw [hself, spinEnd_finrank] at h
  exact_mod_cast h.symm

theorem exists_bijective_spin_intertwiner (a : MulAut Q)
    (ha : ∀ c, a (qCentral c) = qCentral c) :
    ∃ T : SpinSpace →ₗ[ℝ] SpinSpace, Function.Bijective T ∧
      ∀ q x, T (spinRepresentation q x) = spinRepresentation (a q) (T x) := by
  let : IsIrreducible spinLinearRepresentation := spinLinearRepresentation_irreducible
  let : Nontrivial (IntertwiningMap spinLinearRepresentation (spinTwistedRepresentation a)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by
      rw [spinTwisted_intertwiner_finrank a ha]
      decide)
  obtain ⟨T, hT⟩ := exists_ne
    (0 : IntertwiningMap spinLinearRepresentation (spinTwistedRepresentation a))
  have hTi : Function.Injective T :=
    (IsIrreducible.injective_or_eq_zero T).resolve_right hT
  refine ⟨T.toLinearMap, ⟨hTi, LinearMap.injective_iff_surjective.mp hTi⟩, ?_⟩
  intro q x
  exact IntertwiningMap.isIntertwining spinLinearRepresentation (spinTwistedRepresentation a) T q x

theorem exists_spinHolomorph_of_implementation (a : MulAut Q)
    (e : SpinSpace ≃ₗ[ℝ] SpinSpace)
    (he : ∀ q x, e (spinRepresentation q x) = spinRepresentation (a q) (e x))
    (ho : ∀ x y, spinPairing (e x) (e y) = spinPairing x y) :
    ∃ s : SpinHolomorph, s.val = e ∧ spinConjugation s = a := by
  have hconj (q : Q) : e * spinRepresentation q * e⁻¹ = spinRepresentation (a q) := by
    apply LinearEquiv.ext
    intro x
    change e (spinRepresentation q (e.symm x)) = spinRepresentation (a q) x
    rw [he, LinearEquiv.apply_symm_apply]
  have hnormal : e ∈ Subgroup.normalizer (spinImage : Set (SpinSpace ≃ₗ[ℝ] SpinSpace)) := by
    apply Subgroup.mem_normalizer_iff.mpr
    intro h
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨a q, (hconj q).symm⟩
    · rintro ⟨q, hq⟩
      refine ⟨a.symm q, ?_⟩
      have hh : e * h * e⁻¹ = e * spinRepresentation (a.symm q) * e⁻¹ := by
        rw [hconj, a.apply_symm_apply]
        exact hq.symm
      exact (mul_left_cancel (mul_right_cancel hh)).symm
  let s : SpinHolomorph := ⟨e, hnormal, ho⟩
  refine ⟨s, rfl, ?_⟩
  apply MulEquiv.ext
  intro q
  apply spinRepresentation_injective
  rw [spinConjugation_representation]
  exact hconj q

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
