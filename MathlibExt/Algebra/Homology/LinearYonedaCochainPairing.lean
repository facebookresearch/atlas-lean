/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.CategoryTheory.Monoidal.Linear
public import MathlibExt.Algebra.Homology.GradedPairing
public import MathlibExt.Algebra.Homology.LinearHomCochainComplex
public import MathlibExt.Algebra.Homology.TensorDifferentialDownNat

/-!
# Graded pairings on linear-Yoneda cochains

In a linear monoidal category, a chain map into a tensor product and a
pairing of coefficient objects induce a graded pairing on linear-Yoneda
cochains.  This generalizes the construction from chain complexes of modules
to categories such as `Rep k G`.

The degreewise pairing projects the tensor complex onto its `(p,q)` summand,
applies the tensor of the two cochains and the coefficient pairing, and
precomposes with the chain diagonal.  Its Leibniz rule follows from the
tensor differential with the Koszul sign `(-1)^p`.

## Main declarations

* `HomologicalComplex.linearYonedaPairingDesc`
* `HomologicalComplex.linearYonedaCochainPairLinearMap`
* `HomologicalComplex.linearYonedaCochainPair`
* `HomologicalComplex.linearYonedaCochainPair_tmul`
* `HomologicalComplex.linearYonedaCochainGradedPairing`
* `HomologicalComplex.linearYonedaCochainGradedPairing_pair`
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory Opposite

universe v u

namespace HomologicalComplex

variable (R : Type v) [CommRing R]
variable (C : Type u) [Category.{v} C] [Preadditive C] [Linear R C]
variable [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear R C]
variable {K₁ K₂ K₃ : ChainComplex C ℕ}
variable {M N P : C}
variable [HasTensor K₁ K₂]

@[simp]
private lemma moduleHom_comp_apply {A B D : ModuleCat.{v} R}
    (f : A ⟶ B) (g : B ⟶ D) (x : A) :
    (f ≫ g).hom x = g.hom (f.hom x) :=
  rfl

@[simp]
private lemma moduleHom_add_apply {A B : ModuleCat.{v} R}
    (f g : A ⟶ B) (x : A) :
    (f + g).hom x = f.hom x + g.hom x :=
  rfl

@[simp]
private lemma moduleHom_zsmul_apply {A B : ModuleCat.{v} R}
    (z : ℤ) (f : A ⟶ B) (x : A) :
    (z • f).hom x = z • f.hom x :=
  rfl

@[simp]
private lemma moduleTensorHom_tmul
    {A B D E : ModuleCat.{v} R}
    (f : A ⟶ B) (g : D ⟶ E) (x : A) (y : D) :
    (f ⊗ₘ g).hom (x ⊗ₜ[R] y) = f.hom x ⊗ₜ[R] g.hom y :=
  rfl

@[no_expose]
noncomputable def linearYonedaPairingDescOfEq
    (mu : M ⊗ N ⟶ P) (p q n : ℕ) (hpq : p + q = n)
    (phi : K₁.X p ⟶ M) (psi : K₂.X q ⟶ N) :
    (tensorObj K₁ K₂).X n ⟶ P :=
  mapBifunctorDesc (fun i j h =>
    if hi : i = p then
      by
        subst i
        have hsum : p + j = p + q := h.trans hpq.symm
        have hj : j = q := Nat.add_left_cancel hsum
        subst j
        exact (phi ⊗ₘ psi) ≫ mu
    else 0)

noncomputable def linearYonedaPairingDesc
    (mu : M ⊗ N ⟶ P) (p q : ℕ)
    (phi : K₁.X p ⟶ M) (psi : K₂.X q ⟶ N) :
    (tensorObj K₁ K₂).X (p + q) ⟶ P :=
  linearYonedaPairingDescOfEq C mu p q (p + q) rfl phi psi

/-- The restriction of a linear-Yoneda pairing descriptor to an arbitrary
tensor summand.  It is the chosen tensor of cochains when the left degree
matches, and zero otherwise. -/
@[reassoc (attr := simp)]
theorem ιTensorObj_comp_linearYonedaPairingDescOfEq
    (mu : M ⊗ N ⟶ P) (p q n i j : ℕ) (hpq : p + q = n)
    (hij : i + j = n) (phi : K₁.X p ⟶ M) (psi : K₂.X q ⟶ N) :
    ιTensorObj K₁ K₂ i j n hij ≫
        linearYonedaPairingDescOfEq C mu p q n hpq phi psi =
      if hi : i = p then
        by
          subst i
          have hsum : p + j = p + q := hij.trans hpq.symm
          have hj : j = q := Nat.add_left_cancel hsum
          subst j
          exact (phi ⊗ₘ psi) ≫ mu
      else 0 := by
  apply ι_mapBifunctorDesc

/-- Restriction of a linear-Yoneda pairing descriptor to a tensor summand
whose two degrees are identified with the selected bidegree. -/
@[reassoc]
theorem ιTensorObj_comp_linearYonedaPairingDescOfEq_of_eq
    (mu : M ⊗ N ⟶ P) (p q n i j : ℕ)
    (hpq : p + q = n) (hij : i + j = n)
    (hi : i = p) (hj : j = q)
    (phi : K₁.X p ⟶ M) (psi : K₂.X q ⟶ N) :
    ιTensorObj K₁ K₂ i j n hij ≫
        linearYonedaPairingDescOfEq C mu p q n hpq phi psi =
      ((K₁.XIsoOfEq hi).hom ⊗ₘ (K₂.XIsoOfEq hj).hom) ≫
        (phi ⊗ₘ psi) ≫ mu := by
  subst i
  subst j
  rw [ιTensorObj_comp_linearYonedaPairingDescOfEq]
  simp

/-- The linear-Yoneda pairing descriptor restricts on its selected tensor
summand to the tensor product of the two cochains followed by the coefficient
pairing. -/
@[reassoc (attr := simp)]
theorem ιTensorObj_comp_linearYonedaPairingDesc
    (mu : M ⊗ N ⟶ P) (p q : ℕ)
    (phi : K₁.X p ⟶ M) (psi : K₂.X q ⟶ N) :
    ιTensorObj K₁ K₂ p q (p + q) rfl ≫
        linearYonedaPairingDesc C mu p q phi psi =
      (phi ⊗ₘ psi) ≫ mu := by
  unfold linearYonedaPairingDesc
  rw [ιTensorObj_comp_linearYonedaPairingDescOfEq]
  simp

/-- The linear-Yoneda pairing descriptor vanishes on every tensor summand
whose left degree differs from the selected degree. -/
@[reassoc (attr := simp)]
theorem ιTensorObj_comp_linearYonedaPairingDesc_of_ne_left
    (mu : M ⊗ N ⟶ P) (p q i j : ℕ) (hij : i + j = p + q)
    (phi : K₁.X p ⟶ M) (psi : K₂.X q ⟶ N) (hi : i ≠ p) :
    ιTensorObj K₁ K₂ i j (p + q) hij ≫
        linearYonedaPairingDesc C mu p q phi psi = 0 := by
  unfold linearYonedaPairingDesc
  rw [ιTensorObj_comp_linearYonedaPairingDescOfEq]
  simp [hi]

/-- Naturality of the linear-Yoneda pairing descriptor under independent
precomposition in its two chain-complex variables. -/
@[reassoc]
theorem linearYonedaPairingDescOfEq_naturality
    {L₁ L₂ : ChainComplex C ℕ} [HasTensor L₁ L₂]
    (f₁ : L₁ ⟶ K₁) (f₂ : L₂ ⟶ K₂)
    (mu : M ⊗ N ⟶ P) (p q n : ℕ) (hpq : p + q = n)
    (phi : K₁.X p ⟶ M) (psi : K₂.X q ⟶ N) :
    (tensorHom f₁ f₂).f n ≫
        linearYonedaPairingDescOfEq C mu p q n hpq phi psi =
      linearYonedaPairingDescOfEq C mu p q n hpq
        (f₁.f p ≫ phi) (f₂.f q ≫ psi) := by
  apply mapBifunctor.hom_ext
  intro i j h
  rw [← Category.assoc, ι_mapBifunctorMap]
  simp only [Category.assoc]
  rw [ιTensorObj_comp_linearYonedaPairingDescOfEq,
    ιTensorObj_comp_linearYonedaPairingDescOfEq]
  change i + j = n at h
  by_cases hi : i = p
  · subst i
    have hj : j = q := by omega
    subst j
    simp only [dite_eq_left]
    change (f₁.f p ▷ L₂.X q) ≫ (K₁.X p ◁ f₂.f q) ≫
        (phi ⊗ₘ psi) ≫ mu =
      ((f₁.f p ≫ phi) ⊗ₘ (f₂.f q ≫ psi)) ≫ mu
    rw [← MonoidalCategory.tensorHom_def_assoc]
    rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc]
  · simp [hi]

/-- Naturality of the linear-Yoneda pairing descriptor under independent
precomposition in its two chain-complex variables. -/
@[reassoc]
theorem linearYonedaPairingDesc_naturality
    {L₁ L₂ : ChainComplex C ℕ} [HasTensor L₁ L₂]
    (f₁ : L₁ ⟶ K₁) (f₂ : L₂ ⟶ K₂)
    (mu : M ⊗ N ⟶ P) (p q : ℕ)
    (phi : K₁.X p ⟶ M) (psi : K₂.X q ⟶ N) :
    (tensorHom f₁ f₂).f (p + q) ≫
        linearYonedaPairingDesc C mu p q phi psi =
      linearYonedaPairingDesc C mu p q
        (f₁.f p ≫ phi) (f₂.f q ≫ psi) :=
  linearYonedaPairingDescOfEq_naturality C f₁ f₂ mu p q (p + q) rfl phi psi

private lemma linearYonedaPairingDesc_add_left
    (mu : M ⊗ N ⟶ P) (p q : ℕ)
    (phi₁ phi₂ : K₁.X p ⟶ M) (psi : K₂.X q ⟶ N) :
    linearYonedaPairingDesc C mu p q (phi₁ + phi₂) psi =
      linearYonedaPairingDesc C mu p q phi₁ psi +
        linearYonedaPairingDesc C mu p q phi₂ psi := by
  apply mapBifunctor.hom_ext
  intro i j h
  unfold linearYonedaPairingDesc linearYonedaPairingDescOfEq
  by_cases hi : i = p
  · subst i
    have hsum : p + j = p + q := by simpa using h
    have hj : j = q := Nat.add_left_cancel hsum
    subst j
    simp only [ι_mapBifunctorDesc, Preadditive.comp_add]
    simp only [dite_eq_left]
    rw [MonoidalPreadditive.add_tensor, Preadditive.add_comp]
  · simp [hi, Preadditive.comp_add]

private lemma linearYonedaPairingDesc_smul_left
    (mu : M ⊗ N ⟶ P) (p q : ℕ) (r : R)
    (phi : K₁.X p ⟶ M) (psi : K₂.X q ⟶ N) :
    linearYonedaPairingDesc C mu p q (r • phi) psi =
      r • linearYonedaPairingDesc C mu p q phi psi := by
  apply mapBifunctor.hom_ext
  intro i j h
  unfold linearYonedaPairingDesc linearYonedaPairingDescOfEq
  by_cases hi : i = p
  · subst i
    have hsum : p + j = p + q := by simpa using h
    have hj : j = q := Nat.add_left_cancel hsum
    subst j
    simp only [Linear.comp_smul, ι_mapBifunctorDesc]
    simp only [dite_eq_left]
    have htensor : (r • phi) ⊗ₘ psi = r • (phi ⊗ₘ psi) := by
      simp [MonoidalCategory.tensorHom_def]
    rw [htensor, Linear.smul_comp]
  · simp [hi, Linear.comp_smul]

private lemma linearYonedaPairingDesc_add_right
    (mu : M ⊗ N ⟶ P) (p q : ℕ)
    (phi : K₁.X p ⟶ M) (psi₁ psi₂ : K₂.X q ⟶ N) :
    linearYonedaPairingDesc C mu p q phi (psi₁ + psi₂) =
      linearYonedaPairingDesc C mu p q phi psi₁ +
        linearYonedaPairingDesc C mu p q phi psi₂ := by
  apply mapBifunctor.hom_ext
  intro i j h
  unfold linearYonedaPairingDesc linearYonedaPairingDescOfEq
  by_cases hi : i = p
  · subst i
    have hsum : p + j = p + q := by simpa using h
    have hj : j = q := Nat.add_left_cancel hsum
    subst j
    simp only [ι_mapBifunctorDesc, Preadditive.comp_add]
    simp only [dite_eq_left]
    rw [MonoidalPreadditive.tensor_add, Preadditive.add_comp]
  · simp [hi, Preadditive.comp_add]

private lemma linearYonedaPairingDesc_smul_right
    (mu : M ⊗ N ⟶ P) (p q : ℕ) (r : R)
    (phi : K₁.X p ⟶ M) (psi : K₂.X q ⟶ N) :
    linearYonedaPairingDesc C mu p q phi (r • psi) =
      r • linearYonedaPairingDesc C mu p q phi psi := by
  apply mapBifunctor.hom_ext
  intro i j h
  unfold linearYonedaPairingDesc linearYonedaPairingDescOfEq
  by_cases hi : i = p
  · subst i
    have hsum : p + j = p + q := by simpa using h
    have hj : j = q := Nat.add_left_cancel hsum
    subst j
    simp only [Linear.comp_smul, ι_mapBifunctorDesc]
    simp only [dite_eq_left]
    have htensor : phi ⊗ₘ (r • psi) = r • (phi ⊗ₘ psi) := by
      simp [MonoidalCategory.tensorHom_def]
    rw [htensor, Linear.smul_comp]
  · simp [hi, Linear.comp_smul]

private lemma tensor_d_comp_linearYonedaPairingDescOfEq
    (mu : M ⊗ N ⟶ P) (p q : ℕ)
    (phi : K₁.X p ⟶ M) (psi : K₂.X q ⟶ N) :
    (tensorObj K₁ K₂).d (p + q + 1) (p + q) ≫
        linearYonedaPairingDescOfEq C mu p q (p + q) rfl phi psi =
      linearYonedaPairingDescOfEq C mu (p + 1) q (p + q + 1) (by omega)
          (K₁.d (p + 1) p ≫ phi) psi +
        ((-1 : ℤ) ^ p) •
          linearYonedaPairingDescOfEq C mu p (q + 1) (p + q + 1) (by omega)
            phi (K₂.d (q + 1) q ≫ psi) := by
  apply mapBifunctor.hom_ext
  intro i j h
  change i + j = p + q + 1 at h
  rw [← Category.assoc, ιTensorObj_comp_d_down_nat K₁ K₂ i j (p + q) h,
    Preadditive.add_comp, Preadditive.comp_add, Preadditive.comp_zsmul]
  by_cases hi_left : i = p + 1
  · subst i
    have hj : j = q := by omega
    subst j
    simp only [dite_eq_right (by omega : p + 1 ≠ 0), Nat.add_one_sub_one,
      tensorHom_id]
    rw [Category.assoc, ιTensorObj_comp_linearYonedaPairingDescOfEq
      (C := C), dite_eq_left rfl]
    rw [ιTensorObj_comp_linearYonedaPairingDescOfEq (C := C),
      dite_eq_left rfl]
    rw [ιTensorObj_comp_linearYonedaPairingDescOfEq (C := C),
      dite_eq_right (by omega : p + 1 ≠ p), smul_zero, add_zero]
    have hmain :
        (K₁.d (p + 1) p ▷ K₂.X q) ≫ (phi ⊗ₘ psi) ≫ mu =
          ((K₁.d (p + 1) p ≫ phi) ⊗ₘ psi) ≫ mu := by
      rw [← Category.assoc, ← MonoidalCategory.tensorHom_id,
        MonoidalCategory.tensorHom_comp_tensorHom]
      simp
    rw [hmain, add_eq_left]
    by_cases hq : q = 0
    · simp [hq]
    · rw [dite_eq_right hq, Preadditive.zsmul_comp, Category.assoc,
        ιTensorObj_comp_linearYonedaPairingDescOfEq (C := C)]
      simp
  · by_cases hi_right : i = p
    · subst i
      have hj : j = q + 1 := by omega
      subst j
      simp only [dite_eq_right (by omega : q + 1 ≠ 0), Nat.add_one_sub_one,
        id_tensorHom]
      rw [Preadditive.zsmul_comp, Category.assoc,
        ιTensorObj_comp_linearYonedaPairingDescOfEq (C := C),
        dite_eq_left rfl]
      rw [ιTensorObj_comp_linearYonedaPairingDescOfEq (C := C),
        dite_eq_right (by omega : p ≠ p + 1), zero_add]
      rw [ιTensorObj_comp_linearYonedaPairingDescOfEq (C := C),
        dite_eq_left rfl]
      have hmain :
          (K₁.X p ◁ K₂.d (q + 1) q) ≫ (phi ⊗ₘ psi) ≫ mu =
            (phi ⊗ₘ (K₂.d (q + 1) q ≫ psi)) ≫ mu := by
        rw [← Category.assoc, ← MonoidalCategory.id_tensorHom,
          MonoidalCategory.tensorHom_comp_tensorHom]
        simp
      rw [hmain, add_eq_right]
      by_cases hp : p = 0
      · simp [hp]
      · have hp_pred : p - 1 ≠ p := by omega
        rw [dite_eq_right hp, Category.assoc,
          ιTensorObj_comp_linearYonedaPairingDescOfEq (C := C)]
        simp [hp_pred]
    · by_cases hi_zero : i = 0
      · subst i
        have hp : p ≠ 0 := by omega
        have hj_zero : j ≠ 0 := by omega
        simp [Category.assoc,
          ιTensorObj_comp_linearYonedaPairingDescOfEq (C := C), hp,
          hj_zero, hi_right]
      · have hi_pred : i - 1 ≠ p := by
          intro hip
          omega
        by_cases hj_zero : j = 0
        · simp [Category.assoc,
            ιTensorObj_comp_linearYonedaPairingDescOfEq (C := C), hi_zero,
            hj_zero, hi_pred, hi_left, hi_right]
        · simp [Category.assoc,
            ιTensorObj_comp_linearYonedaPairingDescOfEq (C := C), hi_zero,
            hj_zero, hi_pred, hi_left, hi_right]

/-- Transporting the source degree before a diagonal and a linear-Yoneda
pairing descriptor is the corresponding arbitrary-total-degree descriptor. -/
@[reassoc]
theorem XIsoOfEq_comp_linearYonedaPairingDescOfEq
    (Delta : K₃ ⟶ tensorObj K₁ K₂) (mu : M ⊗ N ⟶ P)
    (p q n : ℕ) (h : n = p + q)
    (phi : K₁.X p ⟶ M) (psi : K₂.X q ⟶ N) :
    (K₃.XIsoOfEq h).hom ≫ Delta.f (p + q) ≫
        linearYonedaPairingDescOfEq C mu p q (p + q) rfl phi psi =
      Delta.f n ≫
        linearYonedaPairingDescOfEq C mu p q n h.symm phi psi := by
  subst n
  simp

/-- Wrapper form of
`XIsoOfEq_comp_linearYonedaPairingDescOfEq` at total degree `p + q`. -/
@[reassoc]
theorem XIsoOfEq_comp_linearYonedaPairingDesc
    (Delta : K₃ ⟶ tensorObj K₁ K₂) (mu : M ⊗ N ⟶ P)
    (p q n : ℕ) (h : n = p + q)
    (phi : K₁.X p ⟶ M) (psi : K₂.X q ⟶ N) :
    (K₃.XIsoOfEq h).hom ≫ Delta.f (p + q) ≫
        linearYonedaPairingDesc C mu p q phi psi =
      Delta.f n ≫
        linearYonedaPairingDescOfEq C mu p q n h.symm phi psi := by
  unfold linearYonedaPairingDesc
  exact XIsoOfEq_comp_linearYonedaPairingDescOfEq
    C Delta mu p q n h phi psi

noncomputable def linearYonedaCochainPairLinearMap
    (Delta : K₃ ⟶ tensorObj K₁ K₂) (mu : M ⊗ N ⟶ P)
    (p q : ℕ) :
    TensorProduct R (K₁.X p ⟶ M) (K₂.X q ⟶ N) →ₗ[R]
      (K₃.X (p + q) ⟶ P) :=
  TensorProduct.lift <| LinearMap.mk₂ R
    (fun (phi : K₁.X p ⟶ M) (psi : K₂.X q ⟶ N) =>
      Delta.f (p + q) ≫ linearYonedaPairingDesc C mu p q phi psi)
    (fun phi₁ phi₂ psi => by
      rw [linearYonedaPairingDesc_add_left (C := C) (K₁ := K₁) (K₂ := K₂)
        (M := M) (N := N) (P := P), Preadditive.comp_add])
    (fun r phi psi => by
      rw [linearYonedaPairingDesc_smul_left (R := R) (C := C)
        (K₁ := K₁) (K₂ := K₂) (M := M) (N := N) (P := P),
        Linear.comp_smul])
    (fun phi psi₁ psi₂ => by
      rw [linearYonedaPairingDesc_add_right (C := C) (K₁ := K₁) (K₂ := K₂)
        (M := M) (N := N) (P := P), Preadditive.comp_add])
    (fun r phi psi => by
      rw [linearYonedaPairingDesc_smul_right (R := R) (C := C)
        (K₁ := K₁) (K₂ := K₂) (M := M) (N := N) (P := P),
        Linear.comp_smul])

/-- Degreewise pairing of linear-Yoneda cochains induced by a chain diagonal
and a coefficient pairing. -/
noncomputable def linearYonedaCochainPair
    (Delta : K₃ ⟶ tensorObj K₁ K₂) (mu : M ⊗ N ⟶ P)
    (p q : ℕ) :
    ModuleCat.of R (K₁.X p ⟶ M) ⊗
        ModuleCat.of R (K₂.X q ⟶ N) ⟶
      ModuleCat.of R (K₃.X (p + q) ⟶ P) :=
  ModuleCat.ofHom
    (linearYonedaCochainPairLinearMap R (C := C) Delta mu p q)

/-- The linear-Yoneda cochain pairing on a pure tensor. -/
@[simp]
theorem linearYonedaCochainPair_tmul
    (Delta : K₃ ⟶ tensorObj K₁ K₂) (mu : M ⊗ N ⟶ P)
    (p q : ℕ) (phi : K₁.X p ⟶ M) (psi : K₂.X q ⟶ N) :
    (linearYonedaCochainPair R C Delta mu p q).hom
        (phi ⊗ₜ[R] psi) =
      Delta.f (p + q) ≫ linearYonedaPairingDesc C mu p q phi psi :=
  rfl

@[simp]
private theorem linearYonedaCochainPair_tmul_cochain
    (Delta : K₃ ⟶ tensorObj K₁ K₂) (mu : M ⊗ N ⟶ P)
    (p q : ℕ)
    (phi : ((linearHomCochainComplexFunctor R C M).obj (op K₁)).X p)
    (psi : ((linearHomCochainComplexFunctor R C N).obj (op K₂)).X q) :
    (linearYonedaCochainPair R C Delta mu p q).hom
        (phi ⊗ₜ[R] psi) =
      Delta.f (p + q) ≫ linearYonedaPairingDesc C mu p q phi psi :=
  rfl

omit [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear R C] in
@[simp]
private lemma linearHomCochainCoefficientMap_apply
    {A B : C} (f : A ⟶ B) (K : ChainComplex C ℕ) (n : ℕ)
    (phi : K.X n ⟶ A) :
    (((((linearHomCochainComplexBifunctor R C).map f).app
      (op K)).f n).hom phi) = phi ≫ f :=
  rfl

omit [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear R C] in
@[simp]
private lemma linearHomCochainCoefficientMap_apply_cochain
    {A B : C} (f : A ⟶ B) (K : ChainComplex C ℕ) (n : ℕ)
    (phi : ((linearHomCochainComplexFunctor R C A).obj (op K)).X n) :
    (((((linearHomCochainComplexBifunctor R C).map f).app
      (op K)).f n).hom phi) = phi ≫ f :=
  rfl

private lemma linearYonedaPairingDesc_coefficient_naturality
    {M' N' P' : C}
    (fM : M ⟶ M') (fN : N ⟶ N') (fP : P ⟶ P')
    (mu : M ⊗ N ⟶ P) (mu' : M' ⊗ N' ⟶ P')
    (hmu : (fM ⊗ₘ fN) ≫ mu' = mu ≫ fP)
    (p q : ℕ) (phi : K₁.X p ⟶ M) (psi : K₂.X q ⟶ N) :
    linearYonedaPairingDesc C mu p q phi psi ≫ fP =
      linearYonedaPairingDesc C mu' p q
        (phi ≫ fM) (psi ≫ fN) := by
  apply mapBifunctor.hom_ext
  intro i j h
  unfold linearYonedaPairingDesc
  rw [ιTensorObj_comp_linearYonedaPairingDescOfEq_assoc,
    ιTensorObj_comp_linearYonedaPairingDescOfEq]
  change i + j = p + q at h
  by_cases hi : i = p
  · subst i
    have hj : j = q := Nat.add_left_cancel h
    subst j
    simp only [dite_eq_left]
    rw [Category.assoc, ← hmu]
    rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc]
  · simp [hi]

/-- Naturality of the degreewise linear-Yoneda cochain pairing in all three
coefficient objects. -/
theorem linearYonedaCochainPair_coefficient_naturality
    {M' N' P' : C}
    (Delta : K₃ ⟶ tensorObj K₁ K₂)
    (fM : M ⟶ M') (fN : N ⟶ N') (fP : P ⟶ P')
    (mu : M ⊗ N ⟶ P) (mu' : M' ⊗ N' ⟶ P')
    (hmu : (fM ⊗ₘ fN) ≫ mu' = mu ≫ fP)
    (p q : ℕ) :
    linearYonedaCochainPair R C Delta mu p q ≫
        (((linearHomCochainComplexBifunctor R C).map fP).app
          (op K₃)).f (p + q) =
      ((((linearHomCochainComplexBifunctor R C).map fM).app
          (op K₁)).f p ⊗ₘ
        (((linearHomCochainComplexBifunctor R C).map fN).app
          (op K₂)).f q) ≫
        linearYonedaCochainPair R C Delta mu' p q := by
  set_option backward.isDefEq.respectTransparency false in
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro phi psi
  rw [moduleHom_comp_apply, linearYonedaCochainPair_tmul_cochain]
  have hP :
      (((((linearHomCochainComplexBifunctor R C).map fP).app
        (op K₃)).f (p + q)).hom
          (Delta.f (p + q) ≫
            linearYonedaPairingDesc C mu p q phi psi)) =
        (Delta.f (p + q) ≫
          linearYonedaPairingDesc C mu p q phi psi) ≫ fP :=
    linearHomCochainCoefficientMap_apply
      (R := R) (C := C) fP K₃ (p + q)
        (Delta.f (p + q) ≫
          linearYonedaPairingDesc C mu p q phi psi)
  refine hP.trans ?_
  rw [moduleHom_comp_apply]
  have hM :
      (((((linearHomCochainComplexBifunctor R C).map fM).app
        (op K₁)).f p).hom phi) = phi ≫ fM :=
    linearHomCochainCoefficientMap_apply
      (R := R) (C := C) fM K₁ p phi
  have hN :
      (((((linearHomCochainComplexBifunctor R C).map fN).app
        (op K₂)).f q).hom psi) = psi ≫ fN :=
    linearHomCochainCoefficientMap_apply
      (R := R) (C := C) fN K₂ q psi
  let coeffTensor :=
    (((linearHomCochainComplexBifunctor R C).map fM).app
      (op K₁)).f p ⊗ₘ
      (((linearHomCochainComplexBifunctor R C).map fN).app
        (op K₂)).f q
  have hTensor :
      coeffTensor.hom (phi ⊗ₜ[R] psi) =
      (phi ≫ fM) ⊗ₜ[R] (psi ≫ fN) := by
    dsimp only [coeffTensor]
    rw [moduleTensorHom_tmul, hM, hN]
  have hPair :
      (linearYonedaCochainPair R C Delta mu' p q).hom
          ((phi ≫ fM) ⊗ₜ[R] (psi ≫ fN)) =
        Delta.f (p + q) ≫
          linearYonedaPairingDesc C mu' p q
            (phi ≫ fM) (psi ≫ fN) :=
    linearYonedaCochainPair_tmul R C Delta mu' p q
      (phi ≫ fM) (psi ≫ fN)
  calc
    (Delta.f (p + q) ≫
        linearYonedaPairingDesc C mu p q phi psi) ≫ fP =
      Delta.f (p + q) ≫
        linearYonedaPairingDesc C mu' p q
          (phi ≫ fM) (psi ≫ fN) := by
        rw [Category.assoc,
          linearYonedaPairingDesc_coefficient_naturality
            (C := C) fM fN fP mu mu' hmu p q]
    _ = (linearYonedaCochainPair R C Delta mu' p q).hom
        ((phi ≫ fM) ⊗ₜ[R] (psi ≫ fN)) := hPair.symm
    _ = (linearYonedaCochainPair R C Delta mu' p q).hom
        (coeffTensor.hom (phi ⊗ₜ[R] psi)) :=
      (congrArg
        (linearYonedaCochainPair R C Delta mu' p q).hom hTensor).symm

omit [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear R C] in
@[simp]
private lemma linearHomCochainComplex_d_apply
    (K : ChainComplex C ℕ) (G : C) (n : ℕ)
    (phi : ((linearHomCochainComplexFunctor R C G).obj (op K)).X n) :
    (((linearHomCochainComplexFunctor R C G).obj
      (op K)).d n (n + 1)).hom phi = K.d (n + 1) n ≫ phi :=
  rfl

omit [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear R C] in
/-- Degree transport on a linear-Yoneda cochain acts by precomposition with
the inverse source-degree transport. -/
@[simp]
theorem linearYonedaCochainComplex_XIsoOfEq_hom_apply
    (K : ChainComplex C ℕ) (G : C) {a b : ℕ} (h : a = b)
    (phi : K.X a ⟶ G) :
    ((((linearHomCochainComplexFunctor R C G).obj
      (op K)).XIsoOfEq h).hom).hom phi =
      (K.XIsoOfEq h.symm).hom ≫ phi := by
  subst b
  change phi = 𝟙 (K.X a) ≫ phi
  simp

/-- A chain diagonal and coefficient pairing induce a cochain graded pairing
on linear-Yoneda cochains in any linear monoidal category. -/
noncomputable def linearYonedaCochainGradedPairing
    (Delta : K₃ ⟶ tensorObj K₁ K₂) (mu : M ⊗ N ⟶ P) :
    CochainGradedPairing
      ((linearHomCochainComplexFunctor R C M).obj (op K₁))
      ((linearHomCochainComplexFunctor R C N).obj (op K₂))
      ((linearHomCochainComplexFunctor R C P).obj (op K₃)) where
  pair := linearYonedaCochainPair R C Delta mu
  leibniz := by
    set_option backward.isDefEq.respectTransparency false in
    intro p q
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro phi psi
    change (K₁.X p ⟶ M) at phi
    change (K₂.X q ⟶ N) at psi
    rw [moduleHom_comp_apply, linearHomCochainComplex_d_apply]
    change K₃.d (p + q + 1) (p + q) ≫
      Delta.f (p + q) ≫ linearYonedaPairingDesc C mu p q phi psi = _
    rw [moduleHom_add_apply, moduleHom_zsmul_apply]
    rw [moduleHom_comp_apply, moduleHom_comp_apply]
    rw [moduleTensorHom_tmul]
    rw [linearHomCochainComplex_d_apply, ModuleCat.id_apply]
    rw [moduleHom_comp_apply, moduleHom_comp_apply]
    rw [moduleTensorHom_tmul]
    rw [ModuleCat.id_apply, linearHomCochainComplex_d_apply]
    let eL : (p + 1) + q = p + q + 1 := by omega
    let eR : p + (q + 1) = p + q + 1 := by omega
    change K₃.d (p + q + 1) (p + q) ≫
        Delta.f (p + q) ≫ linearYonedaPairingDesc C mu p q phi psi =
      ((((linearHomCochainComplexFunctor R C P).obj
          (op K₃)).XIsoOfEq eL).hom).hom
        (Delta.f ((p + 1) + q) ≫
          linearYonedaPairingDesc C mu (p + 1) q
            (K₁.d (p + 1) p ≫ phi) psi) +
        ((-1 : ℤ) ^ p) •
          ((((linearHomCochainComplexFunctor R C P).obj
            (op K₃)).XIsoOfEq eR).hom).hom
            (Delta.f (p + (q + 1)) ≫
              linearYonedaPairingDesc C mu p (q + 1) phi
                (K₂.d (q + 1) q ≫ psi))
    rw [linearYonedaCochainComplex_XIsoOfEq_hom_apply,
      linearYonedaCochainComplex_XIsoOfEq_hom_apply]
    rw [← Category.assoc, ← Delta.comm]
    simp only [linearYonedaPairingDesc]
    rw [Category.assoc, tensor_d_comp_linearYonedaPairingDescOfEq,
      Preadditive.comp_add, Preadditive.comp_zsmul]
    rw [XIsoOfEq_comp_linearYonedaPairingDescOfEq,
      XIsoOfEq_comp_linearYonedaPairingDescOfEq]

/-- The graded pairing's degreewise map is the linear-Yoneda cochain pair. -/
@[simp]
theorem linearYonedaCochainGradedPairing_pair
    (Delta : K₃ ⟶ tensorObj K₁ K₂) (mu : M ⊗ N ⟶ P)
    (p q : ℕ) :
    (linearYonedaCochainGradedPairing R C Delta mu).pair p q =
      linearYonedaCochainPair R C Delta mu p q :=
  rfl

/-- Naturality of the linear-Yoneda cochain graded pairing in all three
coefficient objects. -/
theorem linearYonedaCochainGradedPairing_coefficient_naturality
    {M' N' P' : C}
    (Delta : K₃ ⟶ tensorObj K₁ K₂)
    (fM : M ⟶ M') (fN : N ⟶ N') (fP : P ⟶ P')
    (mu : M ⊗ N ⟶ P) (mu' : M' ⊗ N' ⟶ P')
    (hmu : (fM ⊗ₘ fN) ≫ mu' = mu ≫ fP)
    (p q : ℕ) :
    (linearYonedaCochainGradedPairing R C Delta mu).pair p q ≫
        (((linearHomCochainComplexBifunctor R C).map fP).app
          (op K₃)).f (p + q) =
      ((((linearHomCochainComplexBifunctor R C).map fM).app
          (op K₁)).f p ⊗ₘ
        (((linearHomCochainComplexBifunctor R C).map fN).app
          (op K₂)).f q) ≫
        (linearYonedaCochainGradedPairing R C Delta mu').pair p q := by
  rw [linearYonedaCochainGradedPairing_pair,
    linearYonedaCochainGradedPairing_pair]
  exact linearYonedaCochainPair_coefficient_naturality
    R C Delta fM fN fP mu mu' hmu p q

end HomologicalComplex
