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
import MathlibExt.KTheory.Ring.StableElementary.Inclusions

/-! # Monomial product of finite central-kernel Weyl words

For `n : ℕ` and `g ∈ StableSteinberg.finiteCentralKernelSubgroup (R := F) n`
over `[Field F]`, `finiteCentralKernel_list_monomial_prod_eq_one` returns the
accepted bounded `List.ofFn` Weyl-generator representation of `g` together with
equality to `1` of the corresponding `List.prod` of accepted
`Matrix.GeneralLinearGroup.weylMonomialSLUnit` terms at the `Fin n` transports
`⟨a k, ha k⟩`, `⟨b k, hb k⟩`. The proof packages the representation as a
`FiniteWeylWord`, projects the kernel hypothesis through
`toStableE_evalFiniteWeylWord`, and descends the resulting finite elementary
identity through `StableE.fromFinite_injective`. It then identifies the finite
special-linear evaluation, eliminates the identity's Bruhat middle, and applies
`FiniteWeylWord.bruhatMiddle_specialLinearEval`. Empty lists (`m = 0`) and
ranks `0`/`1`
are uniform. Purpose: finite central-kernel monomial input for the Matsumoto
comparison. Nonclaims: no finite-torus containment, torus landing,
well-definedness across representations, kernel generation, TWT, or Matsumoto
claim.
-/

@[expose] public section

namespace AlgebraicKTheory

universe u

/-- Finite central-kernel Weyl words have trivial monomial product: for
`g ∈ StableSteinberg.finiteCentralKernelSubgroup (R := F) n` over `[Field F]`,
there are `m`, endpoint functions `a b : Fin m → ℕ` with bounds `ha hb`,
distinctness `hab`, and units `u : Fin m → Fˣ` such that `g` is the head-left
`List.ofFn`/`List.prod` ordered product of the stable `weyl` generators and the
corresponding ordered product of the accepted `weylMonomialSLUnit` terms at
`⟨a k, ha k⟩`, `⟨b k, hb k⟩` equals `1`. `[Field F]` is required by the
`bruhatMiddle` retraction in the proof. The empty list gives `1 = 1`. Purpose:
central-kernel monomial input. Nonclaims: no finite-torus containment, torus
landing, well-definedness across representations, kernel generation, TWT, or
Matsumoto claim. -/
public theorem finiteCentralKernel_list_monomial_prod_eq_one
    {F : Type u} [Field F] (n : ℕ) (g : StableSteinberg F)
    (hg : g ∈ StableSteinberg.finiteCentralKernelSubgroup (R := F) n) :
    ∃ (m : ℕ) (a b : Fin m → ℕ) (ha : ∀ k, a k < n) (hb : ∀ k, b k < n)
      (hab : ∀ k, a k ≠ b k) (u : Fin m → Fˣ),
      g = (List.ofFn (fun k => StableSteinberg.weyl (a k) (b k) (hab k) (u k))).prod ∧
      List.prod (List.ofFn (fun k => Matrix.GeneralLinearGroup.weylMonomialSLUnit
        (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n)
        (fun h => hab k (congrArg Fin.val h)) (u k))) = 1 := by
  have hWeyl : g ∈ StableSteinberg.finiteWeylSubgroup (R := F) n :=
    StableSteinberg.finiteCentralKernelSubgroup_le_finiteWeyl (R := F) n hg
  obtain ⟨m, a, b, ha, hb, hab, u, hrepr⟩ :=
    StableSteinberg.finiteWeylSubgroup_exists_list_repr hWeyl
  let word := Matrix.GeneralLinearGroup.FiniteWeylWord.ofBoundedNat
    a b ha hb hab u
  have hker : StableSteinberg.toStableE (R := F) g = 1 :=
    MonoidHom.mem_ker.mp
      (StableSteinberg.finiteCentralKernelSubgroup_le_ker (R := F) n hg)
  have hijFin : ∀ k : Fin m, (⟨a k, ha k⟩ : Fin n) ≠ ⟨b k, hb k⟩ :=
    fun k h => hab k (congrArg Fin.val h)
  have hreprWord : g = StableSteinberg.evalFiniteWeylWord word :=
    hrepr.trans
      (StableSteinberg.evalFiniteWeylWord_ofBoundedNat
        a b ha hb hab u).symm
  have hW1 : StableSteinberg.toStableE (R := F)
      (StableSteinberg.evalFiniteWeylWord word) = 1 := by
    rw [← hreprWord]
    exact hker
  have hkerWord : StableSteinberg.evalFiniteWeylWordInStableE word = 1 := by
    rw [← StableSteinberg.toStableE_evalFiniteWeylWord]
    exact hW1
  have hkerT : (List.ofFn (fun k =>
      StableE.elementary n (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n) (hijFin k)
        (↑(u k) : F) *
      StableE.elementary n (⟨b k, hb k⟩ : Fin n) (⟨a k, ha k⟩ : Fin n)
        (hijFin k).symm (-(↑(u k)⁻¹ : F)) *
      StableE.elementary n (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n) (hijFin k)
        (↑(u k) : F))).prod = 1 := by
    rw [← StableSteinberg.evalFiniteWeylWordInStableE_ofBoundedNat]
    exact hkerWord
  have hET : ∀ k : Fin m, StableE.fromFinite F n
      (Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
        (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n) (hijFin k) (↑(u k) : F) *
      Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
        (⟨b k, hb k⟩ : Fin n) (⟨a k, ha k⟩ : Fin n) (hijFin k).symm
        (-(↑(u k)⁻¹ : F)) *
      Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
        (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n) (hijFin k) (↑(u k) : F)) =
      (StableE.elementary n (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n) (hijFin k)
        (↑(u k) : F) *
      StableE.elementary n (⟨b k, hb k⟩ : Fin n) (⟨a k, ha k⟩ : Fin n)
        (hijFin k).symm (-(↑(u k)⁻¹ : F)) *
      StableE.elementary n (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n) (hijFin k)
        (↑(u k) : F)) := by
    intro k
    simp only [map_mul, StableE.fromFinite_elementary]
  have hfunE : (StableE.fromFinite F n) ∘ (fun k : Fin m =>
      Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
        (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n) (hijFin k) (↑(u k) : F) *
      Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
        (⟨b k, hb k⟩ : Fin n) (⟨a k, ha k⟩ : Fin n) (hijFin k).symm
        (-(↑(u k)⁻¹ : F)) *
      Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
        (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n) (hijFin k) (↑(u k) : F)) =
      (fun k : Fin m =>
      StableE.elementary n (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n) (hijFin k)
        (↑(u k) : F) *
      StableE.elementary n (⟨b k, hb k⟩ : Fin n) (⟨a k, ha k⟩ : Fin n)
        (hijFin k).symm (-(↑(u k)⁻¹ : F)) *
      StableE.elementary n (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n) (hijFin k)
        (↑(u k) : F)) :=
    funext hET
  have hfromE : StableE.fromFinite F n ((List.ofFn (fun k : Fin m =>
      Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
        (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n) (hijFin k) (↑(u k) : F) *
      Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
        (⟨b k, hb k⟩ : Fin n) (⟨a k, ha k⟩ : Fin n) (hijFin k).symm
        (-(↑(u k)⁻¹ : F)) *
      Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
        (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n) (hijFin k)
        (↑(u k) : F))).prod) =
      (List.ofFn (fun k : Fin m =>
      StableE.elementary n (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n) (hijFin k)
        (↑(u k) : F) *
      StableE.elementary n (⟨b k, hb k⟩ : Fin n) (⟨a k, ha k⟩ : Fin n)
        (hijFin k).symm (-(↑(u k)⁻¹ : F)) *
      StableE.elementary n (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n) (hijFin k)
        (↑(u k) : F))).prod := by
    rw [map_list_prod, List.map_ofFn, hfunE]
  have hfrom : StableE.fromFinite F n ((List.ofFn (fun k : Fin m =>
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
    apply StableE.fromFinite_injective (R := F) n
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
  have hspecial :
      Matrix.GeneralLinearGroup.FiniteWeylWord.specialLinearEval word = 1 := by
    rw [Matrix.GeneralLinearGroup.FiniteWeylWord.specialLinearEval_ofBoundedNat]
    exact hS1
  have hmiddle :=
    Matrix.GeneralLinearGroup.FiniteWeylWord.bruhatMiddle_specialLinearEval word
  have hmonoWord :
      Matrix.GeneralLinearGroup.FiniteWeylWord.monomialSLEval word = 1 := by
    rw [hspecial, hbm1] at hmiddle
    exact hmiddle.symm
  have hmono : (List.ofFn (fun k : Fin m =>
      Matrix.GeneralLinearGroup.weylMonomialSLUnit
        (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n)
        (hijFin k) (u k))).prod = 1 := by
    rw [← Matrix.GeneralLinearGroup.FiniteWeylWord.monomialSLEval_ofBoundedNat]
    exact hmonoWord
  exact ⟨m, a, b, ha, hb, hab, u, hrepr, hmono⟩

end AlgebraicKTheory

end
