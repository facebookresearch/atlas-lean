/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.LinearAlgebra.ExteriorAlgebra.Coalgebra
public import MathlibExt.LinearAlgebra.ExteriorPower.DeterminantalIdeal
public import MathlibExt.LinearAlgebra.ExteriorPower.FinsuppFiniteSupport
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public meta import Mathlib.Tactic.Abel
public meta import Mathlib.Tactic.NormNum
public meta import Mathlib.Tactic.FinCases

/-!
# Exterior signs, integral minors and finite coordinate support

A tensor coordinate reads the negative cross term in the coproduct of two
independent integer generators. The matrix [2 0] has minor ideals the unit
ideal, the proper ideal (2), and the zero ideal in sizes zero, one and two.
Extension by zero preserves a finitely supported integer vector.
-/

@[expose] public section
noncomputable section
open scoped TensorProduct

namespace MathlibExtTest.ExteriorCoalgebra

abbrev V := Fin 2 → ℤ
abbrev E := ExteriorAlgebra ℤ V

def x : V := ![1, 0]
def y : V := ![0, 1]

def coordinate (i : Fin 2) : E →ₗ[ℤ] ℤ :=
  (LinearMap.proj i : V →ₗ[ℤ] ℤ).comp ExteriorAlgebra.ιInv

lemma coordinate_ι (i : Fin 2) (v : V) :
    coordinate i (ExteriorAlgebra.ι ℤ v) = v i :=
  congrArg (fun z : V => z i) (ExteriorAlgebra.ι_leftInverse v)

lemma coordinate_one (i : Fin 2) : coordinate i (1 : E) = 0 := by
  simp [coordinate, ExteriorAlgebra.ιInv]

def crossCoordinate : E ⊗[ℤ] E →ₗ[ℤ] ℤ :=
  (TensorProduct.lid ℤ ℤ).toLinearMap.comp (TensorProduct.map (coordinate 1) (coordinate 0))

lemma crossCoordinate_tmul (a b : E) :
    crossCoordinate (a ⊗ₜ[ℤ] b) = coordinate 1 a * coordinate 0 b := by
  change TensorProduct.lid ℤ ℤ
    (TensorProduct.map (coordinate 1) (coordinate 0) (a ⊗ₜ[ℤ] b)) = _
  rw [TensorProduct.map_tmul, TensorProduct.lid_tmul]
  rfl

lemma pair_coproduct (a b : V) :
    Coalgebra.comul (R := ℤ) (ExteriorAlgebra.ι ℤ a * ExteriorAlgebra.ι ℤ b) =
      (ExteriorAlgebra.ι ℤ a * ExteriorAlgebra.ι ℤ b) ⊗ₜ[ℤ] (1 : E) +
        ExteriorAlgebra.ι ℤ a ⊗ₜ[ℤ] ExteriorAlgebra.ι ℤ b -
        ExteriorAlgebra.ι ℤ b ⊗ₜ[ℤ] ExteriorAlgebra.ι ℤ a +
        (1 : E) ⊗ₜ[ℤ] (ExteriorAlgebra.ι ℤ a * ExteriorAlgebra.ι ℤ b) := by
  change ExteriorAlgebra.coproduct ℤ V
    (ExteriorAlgebra.ι ℤ a * ExteriorAlgebra.ι ℤ b) = _
  rw [ExteriorAlgebra.coproduct_ι_mul, ExteriorAlgebra.coproduct_ι]
  simp only [map_add, ExteriorAlgebra.signedInsertion_tmul, map_one, mul_one,
    CliffordAlgebra.involute_ι, TensorProduct.neg_tmul]
  abel

example :
    Coalgebra.comul (R := ℤ) (ExteriorAlgebra.ι ℤ x * ExteriorAlgebra.ι ℤ y) =
      (ExteriorAlgebra.ι ℤ x * ExteriorAlgebra.ι ℤ y) ⊗ₜ[ℤ] (1 : E) +
        ExteriorAlgebra.ι ℤ x ⊗ₜ[ℤ] ExteriorAlgebra.ι ℤ y -
        ExteriorAlgebra.ι ℤ y ⊗ₜ[ℤ] ExteriorAlgebra.ι ℤ x +
        (1 : E) ⊗ₜ[ℤ] (ExteriorAlgebra.ι ℤ x * ExteriorAlgebra.ι ℤ y) :=
  pair_coproduct x y

lemma crossValue :
    crossCoordinate (Coalgebra.comul (R := ℤ)
      (ExteriorAlgebra.ι ℤ x * ExteriorAlgebra.ι ℤ y)) = -1 := by
  rw [pair_coproduct]
  simp only [LinearMap.map_add, LinearMap.map_sub, crossCoordinate_tmul,
    coordinate_one, coordinate_ι, mul_zero, zero_mul]
  norm_num [x, y]

example :
    crossCoordinate (Coalgebra.comul (R := ℤ)
      (ExteriorAlgebra.ι ℤ x * ExteriorAlgebra.ι ℤ y)) = -1 := crossValue

example : ExteriorAlgebra.ι ℤ x * ExteriorAlgebra.ι ℤ y ≠ (0 : E) := by
  intro h
  have hz := congrArg
    (fun a : E => crossCoordinate (Coalgebra.comul (R := ℤ) a)) h
  have : (-1 : ℤ) = 0 := crossValue.symm.trans
    (hz.trans (by rw [LinearMap.map_zero, LinearMap.map_zero]))
  norm_num at this

example : Coalgebra.counit (R := ℤ) (algebraMap ℤ E 3) = (3 : ℤ) := by
  change ExteriorAlgebra.algebraMapInv (algebraMap ℤ E 3) = 3
  exact ExteriorAlgebra.algebraMap_leftInverse V 3

def matrix : Matrix (Fin 1) (Fin 2) ℤ := !![2, 0]

example : Matrix.minorIdeal 0 matrix = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  let sr : Set.powersetCard (Fin 1) 0 := ⟨∅, by simp⟩
  let sc : Set.powersetCard (Fin 2) 0 := ⟨∅, by simp⟩
  apply Ideal.subset_span
  refine ⟨(sr, sc), ?_⟩
  exact Matrix.det_fin_zero

lemma minorOne : Matrix.minorIdeal 1 matrix = Ideal.span ({2} : Set ℤ) := by
  classical
  apply le_antisymm
  · rw [Matrix.minorIdeal, Ideal.span_le]
    rintro _ ⟨⟨sr, sc⟩, rfl⟩
    rw [Matrix.det_fin_one]
    let j : Fin 2 := Set.powersetCard.ofFinEmbEquiv.symm sc 0
    have hr : Set.powersetCard.ofFinEmbEquiv.symm sr 0 = (0 : Fin 1) :=
      Subsingleton.elim _ _
    change matrix (Set.powersetCard.ofFinEmbEquiv.symm sr 0) j ∈ _
    rw [hr]
    fin_cases j
    · exact Ideal.subset_span (Set.mem_singleton 2)
    · exact (Ideal.span ({2} : Set ℤ)).zero_mem
  · rw [Ideal.span_le]
    intro a ha
    rcases Set.mem_singleton_iff.mp ha with rfl
    let sr : Set.powersetCard (Fin 1) 1 := ⟨{0}, by simp⟩
    let sc : Set.powersetCard (Fin 2) 1 := ⟨{0}, by simp⟩
    have hr : Set.powersetCard.ofFinEmbEquiv.symm sr 0 = (0 : Fin 1) :=
      Subsingleton.elim _ _
    have hc : Set.powersetCard.ofFinEmbEquiv.symm sc 0 = (0 : Fin 2) := by
      have hm := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem sc
        (Set.powersetCard.ofFinEmbEquiv.symm sc 0)).mp (Set.mem_range_self 0)
      change Set.powersetCard.ofFinEmbEquiv.symm sc 0 ∈ ({0} : Finset (Fin 2)) at hm
      exact Finset.mem_singleton.mp hm
    apply Ideal.subset_span
    refine ⟨(sr, sc), ?_⟩
    rw [Matrix.det_fin_one]
    change matrix (Set.powersetCard.ofFinEmbEquiv.symm sr 0)
      (Set.powersetCard.ofFinEmbEquiv.symm sc 0) = 2
    rw [hr, hc]
    rfl

example : Matrix.minorIdeal 1 matrix = Ideal.span ({2} : Set ℤ) := minorOne

example : (1 : ℤ) ∉ Matrix.minorIdeal 1 matrix := by
  rw [minorOne, Ideal.mem_span_singleton]
  norm_num

example : Matrix.minorIdeal 2 matrix = ⊥ := by
  apply le_antisymm
  · rw [Matrix.minorIdeal, Ideal.span_le]
    rintro _ ⟨⟨sr, sc⟩, rfl⟩
    let e : Fin 2 ↪o Fin 1 := Set.powersetCard.ofFinEmbEquiv.symm sr
    have h : (0 : Fin 2) = 1 := e.injective (Subsingleton.elim _ _)
    exact False.elim ((by decide : (0 : Fin 2) ≠ 1) h)
  · exact bot_le

def twice : ℤ →ₗ[ℤ] ℤ := (2 : ℤ) • LinearMap.id

lemma coefficientTwice : twice.coefficientIdeal = Ideal.span ({2} : Set ℤ) := by
  apply le_antisymm
  · rw [LinearMap.coefficientIdeal, Ideal.span_le]
    rintro _ ⟨⟨a, φ⟩, rfl⟩
    have h : φ (twice a) = 2 * φ a := by
      change φ ((2 : ℤ) • a) = 2 * φ a
      rw [map_smul]
      rfl
    rw [h]
    exact (Ideal.span ({2} : Set ℤ)).mul_mem_right (φ a)
      (Ideal.subset_span (Set.mem_singleton 2))
  · rw [Ideal.span_le]
    intro a ha
    rcases Set.mem_singleton_iff.mp ha with rfl
    simpa [twice] using LinearMap.coefficient_mem twice 1 (LinearMap.id : ℤ →ₗ[ℤ] ℤ)

example : twice.coefficientIdeal = Ideal.span ({2} : Set ℤ) := coefficientTwice

example : twice.determinantalIdeal 1 = Ideal.span ({2} : Set ℤ) := by
  calc
    _ = (exteriorPower.map 1 twice).coefficientIdeal := rfl
    _ = ((exteriorPower.oneEquiv ℤ ℤ).toLinearMap.comp
        (exteriorPower.map 1 twice)).coefficientIdeal :=
      (LinearMap.coefficientIdeal_comp_equiv_left (exteriorPower.oneEquiv ℤ ℤ) _).symm
    _ = (twice.comp (exteriorPower.oneEquiv ℤ ℤ).toLinearMap).coefficientIdeal :=
      congrArg LinearMap.coefficientIdeal (exteriorPower.oneEquiv_naturality twice)
    _ = twice.coefficientIdeal :=
      LinearMap.coefficientIdeal_comp_equiv_right twice (exteriorPower.oneEquiv ℤ ℤ)
    _ = _ := coefficientTwice

def support : Finset ℕ := {2, 5}
def vector : ℕ →₀ ℤ := Finsupp.single 2 3 + Finsupp.single 5 (-1)

lemma supportContains : vector.support ⊆ support := by
  classical
  intro i hi
  by_contra h
  have hn : i ≠ 2 ∧ i ≠ 5 := by simpa [support] using h
  have hz : vector i = 0 := by
    simp [vector, Finsupp.single_apply, hn.1, hn.2, Ne.symm hn.1, Ne.symm hn.2]
  exact (Finsupp.mem_support_iff.mp hi) hz

lemma inclusionRestriction :
    Finsupp.finsetInclude ℤ support (Finsupp.finsetRestrict ℤ support vector) = vector :=
  Finsupp.finsetInclude_restrict_of_support_subset ℤ support vector supportContains

example :
    Finsupp.finsetRestrict ℤ support vector ⟨2, by simp [support]⟩ = (3 : ℤ) := by
  simp [Finsupp.finsetRestrict_apply, vector]

example :
    Finsupp.finsetInclude ℤ support (Finsupp.finsetRestrict ℤ support vector) 5 = (-1 : ℤ) := by
  rw [inclusionRestriction]
  simp [vector]

example :
    Finsupp.finsetInclude ℤ support (Finsupp.finsetRestrict ℤ support vector) 7 = (0 : ℤ) := by
  rw [inclusionRestriction]
  simp [vector]

end MathlibExtTest.ExteriorCoalgebra
