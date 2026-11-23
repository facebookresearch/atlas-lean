/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.LocalCoefficient.NervePullbackBarSimplicial
public import MathlibExt.AlgebraicTopology.SimplicialObject.DataIso
public import MathlibExt.CategoryTheory.CategoryHomology.BarSimplicial

/-!
# Identity-nerve comparison for the nerve-pullback coefficient bar

Restricting the coefficient bar along the identity of a category nerve
recovers the landed category-homology coefficient bar.  The family, summand,
component, and degree-map comparisons assemble into canonical isomorphisms of
simplicial data, genuine simplicial objects, and unnormalized alternating-face
complexes.

The comparison is packaged by isomorphisms rather than brittle equality of
`SimplicialObject.Data` structures.  This file makes no constant-local-system,
SSet-local-system, topological, normalized-chain, homology, or plus claim.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.longLine false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

namespace CategoryTheory.CategoryHomology

universe vG uG vA uA

variable {G : Type uG} [Category.{vG} G]
variable {A : Type uA} [Category.{vA} A]
variable (M : G ⥤ A)
variable [HasCoproducts.{max uG vG} A]

omit [HasCoproducts.{max uG vG} A] in
/-- The identity-nerve pullback family is the landed coefficient-bar family. -/
@[simp]
theorem nervePullbackCoefficientFamily_id (n : ℕ) :
    nervePullbackCoefficientFamily (𝟙 (CategoryTheory.nerve G)) M n =
      coefficientBarFamily M n :=
  rfl

/-- The identity-nerve degree object is the landed coefficient-bar object. -/
@[simp]
theorem nervePullbackCoefficientObj_id (n : ℕ) :
    nervePullbackCoefficientObj (𝟙 (CategoryTheory.nerve G)) M n =
      coefficientBarObj M n :=
  rfl

/-- The identity-nerve summand inclusion is the landed coefficient-bar
inclusion. -/
@[simp]
theorem nervePullbackCoefficientι_id {n : ℕ}
    (F : (CategoryTheory.nerve G) _⦋n⦌) :
    nervePullbackCoefficientι (𝟙 (CategoryTheory.nerve G)) M F =
      coefficientBarι M F :=
  rfl

omit [HasCoproducts.{max uG vG} A] in
/-- The identity-nerve face component is the landed coefficient face
component. -/
@[simp]
theorem nervePullbackCoefficientFaceHom_id {n : ℕ}
    (i : Fin (n + 2)) (F : (CategoryTheory.nerve G) _⦋n + 1⦌) :
    nervePullbackCoefficientFaceHom
        (𝟙 (CategoryTheory.nerve G)) M i F =
      coefficientFaceHom M i F := by
  unfold nervePullbackCoefficientFaceHom
  change coefficientFaceHom M i F ≫ eqToHom _ = coefficientFaceHom M i F
  rw [eqToHom_refl, Category.comp_id]

omit [HasCoproducts.{max uG vG} A] in
/-- The identity-nerve degeneracy component is the landed coefficient
degeneracy component. -/
@[simp]
theorem nervePullbackCoefficientDegeneracyHom_id {n : ℕ}
    (i : Fin (n + 1)) (F : (CategoryTheory.nerve G) _⦋n⦌) :
    nervePullbackCoefficientDegeneracyHom
        (𝟙 (CategoryTheory.nerve G)) M i F =
      coefficientDegeneracyHom M i F := by
  unfold nervePullbackCoefficientDegeneracyHom
  change coefficientDegeneracyHom M i F ≫ eqToHom _ =
    coefficientDegeneracyHom M i F
  rw [eqToHom_refl, Category.comp_id]

/-- The identity-nerve face map is the landed coefficient-bar face map. -/
@[simp]
theorem nervePullbackCoefficientFace_id {n : ℕ}
    (i : Fin (n + 2)) :
    nervePullbackCoefficientFace (𝟙 (CategoryTheory.nerve G)) M i =
      coefficientBarFace M i := by
  unfold nervePullbackCoefficientFace coefficientBarFace
  apply Sigma.map'_eq rfl
  intro F
  rw [nervePullbackCoefficientFaceHom_id M]
  exact Category.comp_id _

/-- The identity-nerve degeneracy map is the landed coefficient-bar
degeneracy map. -/
@[simp]
theorem nervePullbackCoefficientDegeneracy_id {n : ℕ}
    (i : Fin (n + 1)) :
    nervePullbackCoefficientDegeneracy (𝟙 (CategoryTheory.nerve G)) M i =
      coefficientBarDegeneracy M i := by
  unfold nervePullbackCoefficientDegeneracy coefficientBarDegeneracy
  apply Sigma.map'_eq rfl
  intro F
  rw [nervePullbackCoefficientDegeneracyHom_id M]
  exact Category.comp_id _

/-- Canonical identity-component comparison of identity-nerve pullback data
with the landed coefficient-bar data. -/
noncomputable def nervePullbackCoefficientDataIdIso :
    nervePullbackCoefficientData (𝟙 (CategoryTheory.nerve G)) M ≅
      coefficientBarData M := by
  let e : ∀ n,
      (nervePullbackCoefficientData (𝟙 (CategoryTheory.nerve G)) M).obj n ≅
        (coefficientBarData M).obj n := fun n => by
    change coefficientBarObj M n ≅ coefficientBarObj M n
    exact Iso.refl _
  apply SimplicialObject.Data.isoOfIso e
  · intro n i
    change (e (n + 1)).hom ≫ coefficientBarFace M i =
      nervePullbackCoefficientFace (𝟙 (CategoryTheory.nerve G)) M i ≫
        (e n).hom
    have hs : (e (n + 1)).hom = 𝟙 _ := rfl
    have ht : (e n).hom = 𝟙 _ := rfl
    rw [hs, ht]
    simp [nervePullbackCoefficientFace_id]
  · intro n i
    change (e n).hom ≫ coefficientBarDegeneracy M i =
      nervePullbackCoefficientDegeneracy (𝟙 (CategoryTheory.nerve G)) M i ≫
        (e (n + 1)).hom
    have hs : (e n).hom = 𝟙 _ := rfl
    have ht : (e (n + 1)).hom = 𝟙 _ := rfl
    rw [hs, ht]
    simp [nervePullbackCoefficientDegeneracy_id]

@[simp]
theorem nervePullbackCoefficientDataIdIso_hom_app (n : ℕ) :
    (nervePullbackCoefficientDataIdIso M).hom.app n = 𝟙 _ :=
  rfl

@[simp]
theorem nervePullbackCoefficientDataIdIso_inv_app (n : ℕ) :
    (nervePullbackCoefficientDataIdIso M).inv.app n = 𝟙 _ :=
  rfl

/-- Canonical identity-component comparison of identity-nerve pullback and
landed coefficient-bar simplicial objects. -/
noncomputable def nervePullbackCoefficientSimplicialIdIso :
    nervePullbackCoefficientSimplicial
        (𝟙 (CategoryTheory.nerve G)) M ≅
      coefficientBarSimplicial M := by
  change (SimplicialObject.Data.toSimplicialFunctor (C := A)).obj
      (nervePullbackCoefficientData (𝟙 (CategoryTheory.nerve G)) M) ≅
    (SimplicialObject.Data.toSimplicialFunctor (C := A)).obj
      (coefficientBarData M)
  exact (SimplicialObject.Data.toSimplicialFunctor (C := A)).mapIso
    (nervePullbackCoefficientDataIdIso M)

@[simp]
theorem nervePullbackCoefficientSimplicialIdIso_hom_app (n : ℕ) :
    (nervePullbackCoefficientSimplicialIdIso M).hom.app
        (op (SimplexCategory.mk n)) = 𝟙 _ := by
  change (nervePullbackCoefficientDataIdIso M).hom.app n = _
  rw [nervePullbackCoefficientDataIdIso_hom_app]
  change 𝟙 _ = 𝟙 _
  rfl

@[simp]
theorem nervePullbackCoefficientSimplicialIdIso_inv_app (n : ℕ) :
    (nervePullbackCoefficientSimplicialIdIso M).inv.app
        (op (SimplexCategory.mk n)) = 𝟙 _ := by
  change (nervePullbackCoefficientDataIdIso M).inv.app n = _
  rw [nervePullbackCoefficientDataIdIso_inv_app]
  change 𝟙 _ = 𝟙 _
  rfl

section Preadditive

variable [Preadditive A]

/-- Canonical identity-component comparison of identity-nerve pullback and
landed unnormalized coefficient-bar complexes. -/
noncomputable def nervePullbackCoefficientComplexIdIso :
    nervePullbackCoefficientComplex (𝟙 (CategoryTheory.nerve G)) M ≅
      coefficientBarComplex M :=
  (AlgebraicTopology.alternatingFaceMapComplex A).mapIso
    (nervePullbackCoefficientSimplicialIdIso M)

@[simp]
theorem nervePullbackCoefficientComplexIdIso_hom_f (n : ℕ) :
    (nervePullbackCoefficientComplexIdIso M).hom.f n = 𝟙 _ := by
  change (nervePullbackCoefficientSimplicialIdIso M).hom.app
    (op (SimplexCategory.mk n)) = _
  rw [nervePullbackCoefficientSimplicialIdIso_hom_app]
  change 𝟙 _ = 𝟙 _
  rfl

@[simp]
theorem nervePullbackCoefficientComplexIdIso_inv_f (n : ℕ) :
    (nervePullbackCoefficientComplexIdIso M).inv.f n = 𝟙 _ := by
  change (nervePullbackCoefficientSimplicialIdIso M).inv.app
    (op (SimplexCategory.mk n)) = _
  rw [nervePullbackCoefficientSimplicialIdIso_inv_app]
  change 𝟙 _ = 𝟙 _
  rfl

end Preadditive

end CategoryTheory.CategoryHomology
