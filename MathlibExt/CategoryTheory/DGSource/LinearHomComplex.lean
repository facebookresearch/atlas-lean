/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
This completed source port retains the original Apache 2.0 license and author credit.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/Algebra/Homology/LinearHomComplex/Basic.lean
Only module/namespace paths are adapted for Atlas; source operations and hypotheses are retained.
-/

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex

/-!
# The `R`-linear Hom complex of two cochain complexes

Let `C` be an `R`-linear preadditive category and let `F` and `G` be cochain complexes in `C`.
Mathlib's `CochainComplex.HomComplex.Cochain F G n` is the `R`-module of degree-`n` cochains from
`F` to `G`, and `CochainComplex.HomComplex.δ` is the signed differential
`δ z = d_G ∘ z + (-1)^{n+1} z ∘ d_F`, already known to be `R`-linear and square-zero.  Mathlib
assembles this data into `CochainComplex.linearHomComplex R F G`, a cochain complex of
`R`-modules, and `CochainComplex.HomComplex F G`, its additive-group-valued counterpart.
This file supplies the comparison isomorphism and functoriality of the module-valued complex.

That complex is the object a differential graded category is enriched in: a DG category over `R`
is a category enriched in `CochainComplex (ModuleCat R) ℤ`, and `CochainComplex C ℤ` is the
motivating example.  The `AddCommGrpCat`-valued complex retains only the underlying
`ℤ`-linearity, whereas a DG category over `R` requires the `R`-module structure on its Hom
complexes.

## Main definitions

* `MathlibExt.DGSource.linearHomComplexPrecomp` and `MathlibExt.DGSource.linearHomComplexPostcomp`: precomposition and
  postcomposition by a morphism of cochain complexes, as morphisms of `R`-linear Hom complexes.
* `MathlibExt.DGSource.linearHomComplexFunctor`: the two variances bundled into a bifunctor, contravariant in
  the source and covariant in the target.

## Main results

* `MathlibExt.DGSource.forget₂LinearHomComplexIso`: forgetting the `R`-module structure degreewise recovers
  Mathlib's `CochainComplex.HomComplex`.
* `CochainComplex.HomComplex.δ_v_apply_of_d_eq_zero` and
  `CochainComplex.HomComplex.Cochain.v_apply_mem_ker_of_δ_eq_zero`: element-level formulas for the
  differential of a cochain of complexes of modules on an element killed by the source
  differential, and the resulting behaviour of closed degree-zero cochains on kernels.

The cochain modules, the differential `δ`, its `R`-linearity and the Leibniz rule for composition
are supplied by Mathlib.

## Implementation notes

Mathlib's `CochainComplex.linearHomComplex` is implicitly reducible, and
`linearHomComplexFunctor` carries `@[expose]`, so their dependent component types elaborate
against their advertised values.  The element-level API is normalized to
`ModuleCat.of R (Cochain F G n)` and explicit `.hom` application.  Differential applications use
Mathlib's `CochainComplex.linearHomComplex_d_hom_apply`.  The additional operations are sealed
and used through their characteristic lemmas.

## References

* B. Keller, *Deriving DG categories*, Section 1.
* Joël Riou's Mathlib constructions `CochainComplex.linearHomComplex` and
  `CochainComplex.HomComplex`, with their cochain/`δ` API in
  `Mathlib/Algebra/Homology/HomotopyCategory/HomComplex.lean`.
-/

public section

open CategoryTheory Limits CochainComplex CochainComplex.HomComplex

namespace MathlibExt.DGSource

universe v u w

variable (R : Type w) [Ring R] {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]

/-- Forgetting the `R`-module structure of the `R`-linear Hom complex recovers Mathlib's
`CochainComplex.HomComplex`. -/
def forget₂LinearHomComplexIso (F G : CochainComplex C ℤ) :
    ((forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).mapHomologicalComplex _).obj
        (linearHomComplex R F G) ≅ CochainComplex.HomComplex F G :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (fun _ _ _ => rfl)

/-- The forward component of the comparison isomorphism is the identity. -/
@[simp]
lemma forget₂LinearHomComplexIso_hom_f (F G : CochainComplex C ℤ) (n : ℤ) :
    (forget₂LinearHomComplexIso R F G).hom.f n = 𝟙 _ := by
  ext z
  rfl

/-- The inverse component of the comparison isomorphism is the identity. -/
@[simp]
lemma forget₂LinearHomComplexIso_inv_f (F G : CochainComplex C ℤ) (n : ℤ) :
    (forget₂LinearHomComplexIso R F G).inv.f n = 𝟙 _ := by
  ext z
  rfl

section Functoriality

variable {F₁ F₂ F₃ G₁ G₂ G₃ : CochainComplex C ℤ}

private def cochainPrecomp (φ : F₁ ⟶ F₂) (G : CochainComplex C ℤ) (n : ℤ) :
    Cochain F₂ G n →ₗ[R] Cochain F₁ G n where
  toFun z := (Cochain.ofHom φ).comp z (zero_add n)
  map_add' z z' := Cochain.comp_add _ z z' (zero_add n)
  map_smul' r z := Cochain.comp_smul _ r z (zero_add n)

private def cochainPostcomp (F : CochainComplex C ℤ) (ψ : G₁ ⟶ G₂) (n : ℤ) :
    Cochain F G₁ n →ₗ[R] Cochain F G₂ n where
  toFun z := z.comp (Cochain.ofHom ψ) (add_zero n)
  map_add' z z' := Cochain.add_comp z z' _ (add_zero n)
  map_smul' r z := Cochain.smul_comp r z _ (add_zero n)

/-- Precomposition by a morphism `φ : F₁ ⟶ F₂` of cochain complexes, as a morphism of `R`-linear
Hom complexes.  It commutes with the differentials because `φ` is a cocycle, so that the second
term of the Leibniz rule for `δ` vanishes. -/
def linearHomComplexPrecomp (φ : F₁ ⟶ F₂) (G : CochainComplex C ℤ) :
    linearHomComplex R F₂ G ⟶ linearHomComplex R F₁ G where
  f n := ModuleCat.ofHom (cochainPrecomp R φ G n)
  comm' _ m _ := ModuleCat.hom_ext (LinearMap.ext fun z => δ_ofHom_comp φ z m)

/-- Postcomposition by a morphism `ψ : G₁ ⟶ G₂` of cochain complexes, as a morphism of `R`-linear
Hom complexes. -/
def linearHomComplexPostcomp (F : CochainComplex C ℤ) (ψ : G₁ ⟶ G₂) :
    linearHomComplex R F G₁ ⟶ linearHomComplex R F G₂ where
  f n := ModuleCat.ofHom (cochainPostcomp R F ψ n)
  comm' _ m _ := ModuleCat.hom_ext (LinearMap.ext fun z => δ_comp_ofHom z ψ m)

variable {R}

@[simp]
lemma linearHomComplexPrecomp_f_apply (φ : F₁ ⟶ F₂) (G : CochainComplex C ℤ) (n : ℤ)
    (z : ModuleCat.of R (Cochain F₂ G n)) :
    (dsimp% only [linearHomComplex_X]
      ModuleCat.Hom.hom ((linearHomComplexPrecomp R φ G).f n) z) =
      ((Cochain.ofHom φ).comp z (zero_add n) : ModuleCat.of R (Cochain F₁ G n)) :=
  (rfl)

@[simp]
lemma linearHomComplexPostcomp_f_apply (F : CochainComplex C ℤ) (ψ : G₁ ⟶ G₂) (n : ℤ)
    (z : ModuleCat.of R (Cochain F G₁ n)) :
    (dsimp% only [linearHomComplex_X]
      ModuleCat.Hom.hom ((linearHomComplexPostcomp R F ψ).f n) z) =
      (z.comp (Cochain.ofHom ψ) (add_zero n) : ModuleCat.of R (Cochain F G₂ n)) :=
  (rfl)

variable (R)

@[simp]
lemma linearHomComplexPrecomp_id (F G : CochainComplex C ℤ) :
    linearHomComplexPrecomp R (𝟙 F) G = 𝟙 _ := by
  ext n (z : ModuleCat.of R (Cochain F G n))
  exact Cochain.id_comp z

@[simp]
lemma linearHomComplexPrecomp_comp (φ : F₁ ⟶ F₂) (φ' : F₂ ⟶ F₃) (G : CochainComplex C ℤ) :
    linearHomComplexPrecomp R (φ ≫ φ') G =
      linearHomComplexPrecomp R φ' G ≫ linearHomComplexPrecomp R φ G := by
  ext n (z : ModuleCat.of R (Cochain F₃ G n))
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.coe_comp,
    Function.comp_apply]
  rw [linearHomComplexPrecomp_f_apply, linearHomComplexPrecomp_f_apply,
    linearHomComplexPrecomp_f_apply, Cochain.ofHom_comp]
  exact Cochain.comp_assoc _ _ _ (zero_add 0) (zero_add n) (by omega)

@[simp]
lemma linearHomComplexPostcomp_id (F G : CochainComplex C ℤ) :
    linearHomComplexPostcomp R F (𝟙 G) = 𝟙 _ := by
  ext n (z : ModuleCat.of R (Cochain F G n))
  exact Cochain.comp_id z

@[simp]
lemma linearHomComplexPostcomp_comp (F : CochainComplex C ℤ) (ψ : G₁ ⟶ G₂) (ψ' : G₂ ⟶ G₃) :
    linearHomComplexPostcomp R F (ψ ≫ ψ') =
      linearHomComplexPostcomp R F ψ ≫ linearHomComplexPostcomp R F ψ' := by
  ext n (z : ModuleCat.of R (Cochain F G₁ n))
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.coe_comp,
    Function.comp_apply]
  rw [linearHomComplexPostcomp_f_apply, linearHomComplexPostcomp_f_apply,
    linearHomComplexPostcomp_f_apply, Cochain.ofHom_comp]
  exact (Cochain.comp_assoc _ _ _ (add_zero n) (zero_add 0) (by omega)).symm

/-- Precomposition and postcomposition commute. -/
lemma linearHomComplexPrecomp_postcomp_comm (φ : F₁ ⟶ F₂) (ψ : G₁ ⟶ G₂) :
    linearHomComplexPrecomp R φ G₁ ≫ linearHomComplexPostcomp R F₁ ψ =
      linearHomComplexPostcomp R F₂ ψ ≫ linearHomComplexPrecomp R φ G₂ := by
  ext n (z : ModuleCat.of R (Cochain F₂ G₁ n))
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.coe_comp]
  exact Cochain.comp_assoc _ _ _ (zero_add n) (add_zero n) (by omega)

/-- The `R`-linear Hom complex as a bifunctor: contravariant in the source cochain complex and
covariant in the target one. -/
@[expose, simps]
def linearHomComplexFunctor :
    (CochainComplex C ℤ)ᵒᵖ ⥤ CochainComplex C ℤ ⥤ CochainComplex (ModuleCat.{v} R) ℤ where
  obj F :=
    { obj G := linearHomComplex R F.unop G
      map ψ := linearHomComplexPostcomp R F.unop ψ
      map_id G := linearHomComplexPostcomp_id R F.unop G
      map_comp ψ ψ' := linearHomComplexPostcomp_comp R F.unop ψ ψ' }
  map φ :=
    { app G := linearHomComplexPrecomp R φ.unop G
      naturality _ _ ψ := (linearHomComplexPrecomp_postcomp_comm R φ.unop ψ).symm }
  map_id F := by ext G : 2; exact linearHomComplexPrecomp_id R F.unop G
  map_comp φ φ' := by ext G : 2; exact linearHomComplexPrecomp_comp R φ'.unop φ.unop G

end Functoriality

end MathlibExt.DGSource

namespace CochainComplex.HomComplex

/-- On an element killed by the differential of the source, the differential of a cochain of
complexes of modules is the differential of the target applied to the value of the cochain. -/
theorem δ_v_apply_of_d_eq_zero {R : Type*} [Ring R] {K L : CochainComplex (ModuleCat R) ℤ}
    {n m : ℤ} (z : Cochain K L n) {p q r : ℤ} (hpq : p + n = q)
    (hpr : p + m = r) {a : K.X p} (ha : (K.d p (p + 1)).hom a = 0) :
    ((δ n m z).v p r hpr).hom a = (L.d q r).hom ((z.v p q hpq).hom a) := by
  by_cases hnm : n + 1 = m
  · rw [δ_v n m hnm z p r hpr q (p + 1) (by omega) rfl]
    simp [ha]
  · rw [δ_shape _ _ hnm, L.shape q r (by simp [ComplexShape.up_Rel]; omega)]
    simp

end CochainComplex.HomComplex

namespace CochainComplex.HomComplex.Cochain

/-- A closed cochain of degree zero between complexes of modules sends elements killed by the
differential to elements killed by the differential. -/
theorem v_apply_mem_ker_of_δ_eq_zero {R : Type*} [Ring R] {K L : CochainComplex (ModuleCat R) ℤ}
    (z : Cochain K L 0) (hz : δ 0 1 z = 0) {p q : ℤ} {a : K.X p}
    (ha : (K.d p q).hom a = 0) :
    (z.v p p (add_zero p)).hom a ∈ LinearMap.ker (L.d p q).hom := by
  by_cases hpq : p + 1 = q
  swap
  · rw [L.shape p q (by simpa [ComplexShape.up_Rel] using hpq)]
    simp
  have key := congrArg (fun φ ↦ ModuleCat.Hom.hom φ a) (Cochain.congr_v hz p q hpq)
  simpa only [δ_zero_cochain_v, Cochain.zero_v, ModuleCat.hom_sub, ModuleCat.hom_comp,
    LinearMap.sub_apply, LinearMap.comp_apply, ha, map_zero, sub_zero, ModuleCat.hom_zero,
    LinearMap.zero_apply, LinearMap.mem_ker] using key

end CochainComplex.HomComplex.Cochain
