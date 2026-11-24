/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Ring.K2.StableSteinbergFiniteWeylListEval
public import MathlibExt.KTheory.Ring.K2.StableSteinbergFiniteWeylListMonomial
public import MathlibExt.KTheory.Ring.K2.StableSteinbergFiniteWeylWord
import MathlibExt.KTheory.Ring.StableElementary.Inclusions

/-! # Permutation triviality of finite Weyl monomial words

For endpoint functions `a b : Fin m → ℕ` with bounds `ha hb`, pointwise
distinctness `hab`, and units `u : Fin m → Fˣ` over `[Field F]`,
`finiteWeyl_monomial_perm_prod_eq_one` derives equality to `1` of the
head-left `List.ofFn`/`List.prod` ordered product of the corresponding
`Equiv.swap`s from equality to `1` of the ordered product of the accepted
`Matrix.GeneralLinearGroup.weylMonomialSLUnit` terms. The proof packages
the bounded data as `FiniteWeylWord.ofBoundedNat` and applies the generic
`FiniteWeylWord.permEval_eq_one_of_monomialSLEval_eq_one`; that result
coerces the monomial evaluation to its semidirect-product base and takes the
right projection, preserving exact head-left order. `[Field F]` is kept to
match the exhibited kernel monomial list. In addition,
`finiteWeyl_word_perm_prod_eq_one` derives the same `Equiv.swap` product
equality directly from equality to `1` of the `toStableE` image of the
caller-supplied head-left `List.ofFn`/`List.prod` `StableSteinberg.weyl`
word. It uses `toStableE_evalFiniteWeylWord`, transports the resulting
elementary product to the finite special-linear evaluation, and applies
`bruhatMiddle_specialLinearEval` before the same bundled permutation lemma.
Purpose: permutation input for the finite-torus landing route. Nonclaims: no finite-torus
landing or containment, representation independence, weight/diagonal
conclusion, kernel generation, TWT claim, or Matsumoto theorem.
-/

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe u

/-- Finite Weyl monomial words have trivial permutation product: if the
head-left `List.ofFn`/`List.prod` ordered product of the accepted
`weylMonomialSLUnit` terms at `⟨a k, ha k⟩`, `⟨b k, hb k⟩` equals `1`,
then the ordered product of the corresponding `Equiv.swap`s equals `1`.
`[Field F]` matches the exhibited kernel monomial list. The empty list
gives `1 = 1`. Purpose: permutation input. Nonclaims: no finite-torus
landing or containment, representation independence, weight/diagonal
conclusion, kernel generation, TWT claim, or Matsumoto theorem. -/
public theorem finiteWeyl_monomial_perm_prod_eq_one
    {F : Type u} [Field F] {n m : ℕ}
    (a b : Fin m → ℕ) (ha : ∀ k, a k < n) (hb : ∀ k, b k < n)
    (hab : ∀ k, a k ≠ b k) (u : Fin m → Fˣ)
    (hmono : List.prod (List.ofFn (fun k =>
      Matrix.GeneralLinearGroup.weylMonomialSLUnit
        (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n)
        (fun h => hab k (congrArg Fin.val h)) (u k))) = 1) :
    List.prod (List.ofFn (fun k =>
      Equiv.swap (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n))) = 1 := by
  let word := FiniteWeylWord.ofBoundedNat a b ha hb hab u
  have hmono' : FiniteWeylWord.monomialSLEval word = 1 := by
    rw [FiniteWeylWord.monomialSLEval_ofBoundedNat]
    exact hmono
  have hperm :=
    FiniteWeylWord.permEval_eq_one_of_monomialSLEval_eq_one word hmono'
  rw [FiniteWeylWord.permEval_ofBoundedNat] at hperm
  exact hperm

/-- Caller-supplied finite Weyl words have trivial permutation product: if the
`toStableE` image of the head-left `List.ofFn`/`List.prod` ordered product of
the stable `StableSteinberg.weyl (a k) (b k) (hab k) (u k)` generators equals
`1`, then the ordered product of the corresponding `Equiv.swap`s at
`⟨a k, ha k⟩`, `⟨b k, hb k⟩` equals `1`. `[Field F]` is required by the
`bruhatMiddle` retraction in the proof; `ha hb` are the pointwise bounds into
`n` and `hab` is pointwise distinctness. Both sides use head-left `List.ofFn`
order, so the empty list (`m = 0`) gives `1 = 1`. Purpose: caller-supplied
permutation input for the finite-torus landing route. Nonclaims: no
finite-torus landing or containment, representation independence,
weight/diagonal conclusion, kernel generation, TWT claim, or Matsumoto theorem. -/
public theorem finiteWeyl_word_perm_prod_eq_one
    {F : Type u} [Field F] {n m : ℕ}
    (a b : Fin m → ℕ) (ha : ∀ k, a k < n) (hb : ∀ k, b k < n)
    (hab : ∀ k, a k ≠ b k) (u : Fin m → Fˣ)
    (hW : AlgebraicKTheory.StableSteinberg.toStableE (R := F)
      (List.prod (List.ofFn (fun k =>
        AlgebraicKTheory.StableSteinberg.weyl (a k) (b k) (hab k) (u k)))) = 1) :
    List.prod (List.ofFn (fun k =>
      Equiv.swap (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n))) = 1 := by
  let word := FiniteWeylWord.ofBoundedNat a b ha hb hab u
  have hWword : AlgebraicKTheory.StableSteinberg.toStableE
      (AlgebraicKTheory.StableSteinberg.evalFiniteWeylWord word) = 1 := by
    rw [AlgebraicKTheory.StableSteinberg.evalFiniteWeylWord_ofBoundedNat]
    exact hW
  have hkerWord :
      AlgebraicKTheory.StableSteinberg.evalFiniteWeylWordInStableE word = 1 := by
    rw [← AlgebraicKTheory.StableSteinberg.toStableE_evalFiniteWeylWord]
    exact hWword
  have hijFin : ∀ k : Fin m, (⟨a k, ha k⟩ : Fin n) ≠ ⟨b k, hb k⟩ :=
    fun k h => hab k (congrArg Fin.val h)
  have hkerT : (List.ofFn (fun k =>
      AlgebraicKTheory.StableE.elementary n (⟨a k, ha k⟩ : Fin n)
        (⟨b k, hb k⟩ : Fin n) (hijFin k) (↑(u k) : F) *
      AlgebraicKTheory.StableE.elementary n (⟨b k, hb k⟩ : Fin n)
        (⟨a k, ha k⟩ : Fin n) (hijFin k).symm (-(↑(u k)⁻¹ : F)) *
      AlgebraicKTheory.StableE.elementary n (⟨a k, ha k⟩ : Fin n)
        (⟨b k, hb k⟩ : Fin n) (hijFin k) (↑(u k) : F))).prod = 1 :=
    by
      rw [← AlgebraicKTheory.StableSteinberg.evalFiniteWeylWordInStableE_ofBoundedNat]
      exact hkerWord
  have hET : ∀ k : Fin m, AlgebraicKTheory.StableE.fromFinite F n
      (Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
        (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n) (hijFin k) (↑(u k) : F) *
      Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
        (⟨b k, hb k⟩ : Fin n) (⟨a k, ha k⟩ : Fin n) (hijFin k).symm
        (-(↑(u k)⁻¹ : F)) *
      Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
        (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n) (hijFin k) (↑(u k) : F)) =
      (AlgebraicKTheory.StableE.elementary n (⟨a k, ha k⟩ : Fin n)
        (⟨b k, hb k⟩ : Fin n) (hijFin k) (↑(u k) : F) *
      AlgebraicKTheory.StableE.elementary n (⟨b k, hb k⟩ : Fin n)
        (⟨a k, ha k⟩ : Fin n) (hijFin k).symm (-(↑(u k)⁻¹ : F)) *
      AlgebraicKTheory.StableE.elementary n (⟨a k, ha k⟩ : Fin n)
        (⟨b k, hb k⟩ : Fin n) (hijFin k) (↑(u k) : F)) := by
    intro k
    simp only [map_mul, AlgebraicKTheory.StableE.fromFinite_elementary]
  have hfunE : (AlgebraicKTheory.StableE.fromFinite F n) ∘ (fun k : Fin m =>
      Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
        (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n) (hijFin k) (↑(u k) : F) *
      Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
        (⟨b k, hb k⟩ : Fin n) (⟨a k, ha k⟩ : Fin n) (hijFin k).symm
        (-(↑(u k)⁻¹ : F)) *
      Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
        (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n) (hijFin k) (↑(u k) : F)) =
      (fun k : Fin m =>
      AlgebraicKTheory.StableE.elementary n (⟨a k, ha k⟩ : Fin n)
        (⟨b k, hb k⟩ : Fin n) (hijFin k) (↑(u k) : F) *
      AlgebraicKTheory.StableE.elementary n (⟨b k, hb k⟩ : Fin n)
        (⟨a k, ha k⟩ : Fin n) (hijFin k).symm (-(↑(u k)⁻¹ : F)) *
      AlgebraicKTheory.StableE.elementary n (⟨a k, ha k⟩ : Fin n)
        (⟨b k, hb k⟩ : Fin n) (hijFin k) (↑(u k) : F)) :=
    funext hET
  have hfromE : AlgebraicKTheory.StableE.fromFinite F n ((List.ofFn (fun k : Fin m =>
      Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
        (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n) (hijFin k) (↑(u k) : F) *
      Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
        (⟨b k, hb k⟩ : Fin n) (⟨a k, ha k⟩ : Fin n) (hijFin k).symm
        (-(↑(u k)⁻¹ : F)) *
      Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
        (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n) (hijFin k)
        (↑(u k) : F))).prod) =
      (List.ofFn (fun k : Fin m =>
      AlgebraicKTheory.StableE.elementary n (⟨a k, ha k⟩ : Fin n)
        (⟨b k, hb k⟩ : Fin n) (hijFin k) (↑(u k) : F) *
      AlgebraicKTheory.StableE.elementary n (⟨b k, hb k⟩ : Fin n)
        (⟨a k, ha k⟩ : Fin n) (hijFin k).symm (-(↑(u k)⁻¹ : F)) *
      AlgebraicKTheory.StableE.elementary n (⟨a k, ha k⟩ : Fin n)
        (⟨b k, hb k⟩ : Fin n) (hijFin k) (↑(u k) : F))).prod := by
    rw [map_list_prod, List.map_ofFn, hfunE]
  have hfrom : AlgebraicKTheory.StableE.fromFinite F n ((List.ofFn (fun k : Fin m =>
      Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
        (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n) (hijFin k) (↑(u k) : F) *
      Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
        (⟨b k, hb k⟩ : Fin n) (⟨a k, ha k⟩ : Fin n) (hijFin k).symm
        (-(↑(u k)⁻¹ : F)) *
      Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
        (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n) (hijFin k)
        (↑(u k) : F))).prod) = 1 :=
    hfromE.trans hkerT
  have hE1 : (List.ofFn (fun k : Fin m =>
      Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
        (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n) (hijFin k) (↑(u k) : F) *
      Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
        (⟨b k, hb k⟩ : Fin n) (⟨a k, ha k⟩ : Fin n) (hijFin k).symm
        (-(↑(u k)⁻¹ : F)) *
      Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
        (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n) (hijFin k)
        (↑(u k) : F))).prod = 1 := by
    apply AlgebraicKTheory.StableE.fromFinite_injective (R := F) n
    rw [hfrom, map_one]
  have hbridge : ∀ k : Fin m, Matrix.SpecialLinearGroup.toGL
      (Matrix.GeneralLinearGroup.weylSLUnit (⟨a k, ha k⟩ : Fin n)
        (⟨b k, hb k⟩ : Fin n) (hijFin k) (u k)) =
      ((Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
        (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n) (hijFin k) (↑(u k) : F) *
      Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
        (⟨b k, hb k⟩ : Fin n) (⟨a k, ha k⟩ : Fin n) (hijFin k).symm
        (-(↑(u k)⁻¹ : F)) *
      Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
        (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n) (hijFin k) (↑(u k) : F) :
        Matrix.GeneralLinearGroup.elementarySubgroup (Fin n) F) :
      Matrix.GeneralLinearGroup (Fin n) F) := by
    intro k
    apply Units.ext
    simp [Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      Matrix.GeneralLinearGroup.weylSLUnit,
      Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.GeneralLinearGroup.ElementarySubgroup.coe_elementary,
      Matrix.GeneralLinearGroup.coe_elementary]
  have hfunS : (Matrix.SpecialLinearGroup.toGL ∘ (fun k : Fin m =>
      Matrix.GeneralLinearGroup.weylSLUnit (⟨a k, ha k⟩ : Fin n)
        (⟨b k, hb k⟩ : Fin n) (hijFin k) (u k))) =
      (Subgroup.subtype (Matrix.GeneralLinearGroup.elementarySubgroup (Fin n) F) ∘
        (fun k : Fin m =>
      Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
        (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n) (hijFin k) (↑(u k) : F) *
      Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
        (⟨b k, hb k⟩ : Fin n) (⟨a k, ha k⟩ : Fin n) (hijFin k).symm
        (-(↑(u k)⁻¹ : F)) *
      Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
        (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n) (hijFin k)
        (↑(u k) : F))) :=
    funext hbridge
  have hSGL : Matrix.SpecialLinearGroup.toGL
      ((List.ofFn (fun k : Fin m => Matrix.GeneralLinearGroup.weylSLUnit
        (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n) (hijFin k) (u k))).prod) =
      1 := by
    calc Matrix.SpecialLinearGroup.toGL ((List.ofFn (fun k : Fin m =>
            Matrix.GeneralLinearGroup.weylSLUnit (⟨a k, ha k⟩ : Fin n)
              (⟨b k, hb k⟩ : Fin n) (hijFin k) (u k))).prod)
        = (((List.ofFn (fun k : Fin m =>
            Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
              (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n) (hijFin k)
              (↑(u k) : F) *
            Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
              (⟨b k, hb k⟩ : Fin n) (⟨a k, ha k⟩ : Fin n) (hijFin k).symm
              (-(↑(u k)⁻¹ : F)) *
            Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
              (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n) (hijFin k)
              (↑(u k) : F))).map
            (Subgroup.subtype
              (Matrix.GeneralLinearGroup.elementarySubgroup (Fin n) F))).prod) := by
          rw [map_list_prod, List.map_ofFn, List.map_ofFn, hfunS]
      _ = Subgroup.subtype (Matrix.GeneralLinearGroup.elementarySubgroup (Fin n) F)
          ((List.ofFn (fun k : Fin m =>
            Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
              (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n) (hijFin k)
              (↑(u k) : F) *
            Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
              (⟨b k, hb k⟩ : Fin n) (⟨a k, ha k⟩ : Fin n) (hijFin k).symm
              (-(↑(u k)⁻¹ : F)) *
            Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
              (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n) (hijFin k)
              (↑(u k) : F))).prod) := by
          rw [map_list_prod]
      _ = Subgroup.subtype (Matrix.GeneralLinearGroup.elementarySubgroup (Fin n) F)
          1 := by
          rw [hE1]
      _ = 1 := map_one _
  have hS1 : (List.ofFn (fun k : Fin m => Matrix.GeneralLinearGroup.weylSLUnit
      (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n) (hijFin k) (u k))).prod = 1 :=
    Matrix.SpecialLinearGroup.toGL_injective (hSGL.trans (map_one _).symm)
  have hbm1 : Matrix.GeneralLinearGroup.bruhatMiddle
      (1 : Matrix.SpecialLinearGroup (Fin n) F) = 1 := by
    have hfac : (1 : Matrix.SpecialLinearGroup (Fin n) F) =
        Matrix.GeneralLinearGroup.UpperElementary.toSLHom
          (1 : Matrix.GeneralLinearGroup.upperElementarySubgroup (Fin n) F) *
        Matrix.GeneralLinearGroup.monomialSLHom F (Fin n)
          (1 : Matrix.GeneralLinearGroup.MonomialSL F (Fin n)) *
        Matrix.GeneralLinearGroup.UpperElementary.toSLHom
          (1 : Matrix.GeneralLinearGroup.upperElementarySubgroup (Fin n) F) := by
      simp
    exact Matrix.GeneralLinearGroup.bruhatMiddle_factorization_elim _ 1 1 1 hfac
  have hspecial : FiniteWeylWord.specialLinearEval word = 1 := by
    rw [FiniteWeylWord.specialLinearEval_ofBoundedNat]
    exact hS1
  have hmiddle := FiniteWeylWord.bruhatMiddle_specialLinearEval word
  have hmonoWord : FiniteWeylWord.monomialSLEval word = 1 := by
    rw [hspecial, hbm1] at hmiddle
    exact hmiddle.symm
  have hperm :=
    FiniteWeylWord.permEval_eq_one_of_monomialSLEval_eq_one word hmonoWord
  rw [FiniteWeylWord.permEval_ofBoundedNat] at hperm
  exact hperm

end Matrix.GeneralLinearGroup

end
