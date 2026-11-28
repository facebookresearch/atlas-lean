/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.CategoryTheory.Monoidal.Limits.Cokernels
public import MathlibExt.Algebra.Homology.GradedPairing
public import MathlibExt.Algebra.Homology.TensorHomologyDesc

@[expose] public section

noncomputable section

universe v u

open CategoryTheory Limits MonoidalCategory

namespace HomologicalComplex.CochainGradedPairing

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [MonoidalCategory C] [MonoidalPreadditive C]
  {K₁ K₂ K₃ : CochainComplex C ℕ}

private lemma left_succ (P : CochainGradedPairing K₁ K₂ K₃) (p q : ℕ)
    [K₁.HasHomology (p + 1)] [K₂.HasHomology q] [K₃.HasHomology ((p + 1) + q)] :
    ((K₁.toCycles p (p + 1) ▷ K₂.cycles q) ≫ P.pairCycles (p + 1) q) ≫
      K₃.homologyπ ((p + 1) + q) = 0 := by
  rw [pairCycles, K₃.comp_liftCycles]
  apply K₃.liftCycles_homologyπ_eq_zero_of_boundary _ _ _
    ((𝟙 (K₁.X p) ⊗ₘ K₂.iCycles q) ≫ P.pair p q)
  let e := K₃.XIsoOfEq (show (p + 1) + q = p + q + 1 by omega)
  have h₁ : (𝟙 (K₁.X p) ⊗ₘ K₂.iCycles q) ≫
      (K₁.d p (p + 1) ⊗ₘ 𝟙 (K₂.X q)) = K₁.d p (p + 1) ⊗ₘ K₂.iCycles q := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    simp
  have h₂ : (𝟙 (K₁.X p) ⊗ₘ K₂.iCycles q) ≫
      (𝟙 (K₁.X p) ⊗ₘ K₂.d q (q + 1)) = 0 := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom, K₂.iCycles_d]
    simp
  have hto : (K₁.toCycles p (p + 1) ▷ K₂.cycles q) ≫
      (K₁.iCycles (p + 1) ⊗ₘ K₂.iCycles q) =
      K₁.d p (p + 1) ⊗ₘ K₂.iCycles q := by
    calc
      _ = (K₁.toCycles p (p + 1) ⊗ₘ 𝟙 _) ≫
          (K₁.iCycles (p + 1) ⊗ₘ K₂.iCycles q) := by
            simp [MonoidalCategory.tensorHom_def]
      _ = (K₁.toCycles p (p + 1) ≫ K₁.iCycles (p + 1)) ⊗ₘ K₂.iCycles q := by
            rw [MonoidalCategory.tensorHom_comp_tensorHom]
            simp
      _ = _ := by rw [K₁.toCycles_i]
  have hpre :
      ((𝟙 (K₁.X p) ⊗ₘ K₂.iCycles q) ≫ P.pair p q) ≫
          K₃.d (p + q) (p + q + 1) =
        ((K₁.d p (p + 1) ⊗ₘ K₂.iCycles q) ≫ P.pair (p + 1) q) ≫ e.hom := by
    calc
      ((𝟙 (K₁.X p) ⊗ₘ K₂.iCycles q) ≫ P.pair p q) ≫
          K₃.d (p + q) (p + q + 1) =
        (𝟙 (K₁.X p) ⊗ₘ K₂.iCycles q) ≫
          (P.pair p q ≫ K₃.d (p + q) (p + q + 1)) := by rw [Category.assoc]
      _ = (𝟙 (K₁.X p) ⊗ₘ K₂.iCycles q) ≫
          (((K₁.d p (p + 1) ⊗ₘ 𝟙 (K₂.X q)) ≫ P.pair (p + 1) q ≫ e.hom) +
            ((-1 : ℤ) ^ p) •
              ((𝟙 (K₁.X p) ⊗ₘ K₂.d q (q + 1)) ≫ P.pair p (q + 1) ≫
                (K₃.XIsoOfEq (show p + (q + 1) = p + q + 1 by omega)).hom)) := by
          rw [P.leibniz]
      _ = _ := by
        rw [Preadditive.comp_add, Preadditive.comp_zsmul]
        simp only [← Category.assoc, h₁, h₂, zero_comp, smul_zero, add_zero]
  calc
    (K₁.toCycles p (p + 1) ▷ K₂.cycles q) ≫
        (K₁.iCycles (p + 1) ⊗ₘ K₂.iCycles q) ≫ P.pair (p + 1) q =
      (K₁.d p (p + 1) ⊗ₘ K₂.iCycles q) ≫ P.pair (p + 1) q := by
        rw [← Category.assoc, hto]
    _ = (((K₁.d p (p + 1) ⊗ₘ K₂.iCycles q) ≫ P.pair (p + 1) q) ≫ e.hom) ≫
        e.inv := by simp
    _ = (((𝟙 (K₁.X p) ⊗ₘ K₂.iCycles q) ≫ P.pair p q) ≫
        K₃.d (p + q) (p + q + 1)) ≫ e.inv := by rw [hpre]
    _ = ((𝟙 (K₁.X p) ⊗ₘ K₂.iCycles q) ≫ P.pair p q) ≫
        K₃.d (p + q) ((p + 1) + q) := by
          rw [Category.assoc, K₃.d_comp_XIsoOfEq_inv]

private lemma right_succ (P : CochainGradedPairing K₁ K₂ K₃) (p q : ℕ)
    [K₁.HasHomology p] [K₂.HasHomology (q + 1)] [K₃.HasHomology (p + (q + 1))] :
    ((K₁.cycles p ◁ K₂.toCycles q (q + 1)) ≫ P.pairCycles p (q + 1)) ≫
      K₃.homologyπ (p + (q + 1)) = 0 := by
  rw [pairCycles, K₃.comp_liftCycles]
  apply K₃.liftCycles_homologyπ_eq_zero_of_boundary _ _ _
    (((-1 : ℤ) ^ p) • ((K₁.iCycles p ⊗ₘ 𝟙 (K₂.X q)) ≫ P.pair p q))
  let e := K₃.XIsoOfEq (show p + (q + 1) = p + q + 1 by omega)
  have h₁ : (K₁.iCycles p ⊗ₘ 𝟙 (K₂.X q)) ≫
      (K₁.d p (p + 1) ⊗ₘ 𝟙 (K₂.X q)) = 0 := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom, K₁.iCycles_d]
    simp
  have h₂ : (K₁.iCycles p ⊗ₘ 𝟙 (K₂.X q)) ≫
      (𝟙 (K₁.X p) ⊗ₘ K₂.d q (q + 1)) = K₁.iCycles p ⊗ₘ K₂.d q (q + 1) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    simp
  have hto : (K₁.cycles p ◁ K₂.toCycles q (q + 1)) ≫
      (K₁.iCycles p ⊗ₘ K₂.iCycles (q + 1)) =
      K₁.iCycles p ⊗ₘ K₂.d q (q + 1) := by
    calc
      _ = (𝟙 _ ⊗ₘ K₂.toCycles q (q + 1)) ≫
          (K₁.iCycles p ⊗ₘ K₂.iCycles (q + 1)) := by
            simp [MonoidalCategory.tensorHom_def']
      _ = K₁.iCycles p ⊗ₘ
          (K₂.toCycles q (q + 1) ≫ K₂.iCycles (q + 1)) := by
            rw [MonoidalCategory.tensorHom_comp_tensorHom]
            simp
      _ = _ := by rw [K₂.toCycles_i]
  have hpre :
      ((K₁.iCycles p ⊗ₘ 𝟙 (K₂.X q)) ≫ P.pair p q) ≫
          K₃.d (p + q) (p + q + 1) =
        ((-1 : ℤ) ^ p) •
          (((K₁.iCycles p ⊗ₘ K₂.d q (q + 1)) ≫ P.pair p (q + 1)) ≫ e.hom) := by
    calc
      ((K₁.iCycles p ⊗ₘ 𝟙 (K₂.X q)) ≫ P.pair p q) ≫
          K₃.d (p + q) (p + q + 1) =
        (K₁.iCycles p ⊗ₘ 𝟙 (K₂.X q)) ≫
          (P.pair p q ≫ K₃.d (p + q) (p + q + 1)) := by rw [Category.assoc]
      _ = (K₁.iCycles p ⊗ₘ 𝟙 (K₂.X q)) ≫
          (((K₁.d p (p + 1) ⊗ₘ 𝟙 (K₂.X q)) ≫ P.pair (p + 1) q ≫
              (K₃.XIsoOfEq (show (p + 1) + q = p + q + 1 by omega)).hom) +
            ((-1 : ℤ) ^ p) •
              ((𝟙 (K₁.X p) ⊗ₘ K₂.d q (q + 1)) ≫ P.pair p (q + 1) ≫ e.hom)) := by
          rw [P.leibniz]
      _ = _ := by
        rw [Preadditive.comp_add, Preadditive.comp_zsmul]
        simp only [← Category.assoc, h₁, h₂, zero_comp, zero_add]
  have hs : ((-1 : ℤ) ^ p) * ((-1 : ℤ) ^ p) = 1 := by
    rw [← pow_add, ← two_mul]
    simp
  have hpair :
      (((K₁.iCycles p ⊗ₘ K₂.d q (q + 1)) ≫ P.pair p (q + 1)) ≫ e.hom) =
        ((-1 : ℤ) ^ p) •
          (((K₁.iCycles p ⊗ₘ 𝟙 (K₂.X q)) ≫ P.pair p q) ≫
            K₃.d (p + q) (p + q + 1)) := by
    symm
    rw [hpre, smul_smul, hs, one_smul]
  calc
    (K₁.cycles p ◁ K₂.toCycles q (q + 1)) ≫
        (K₁.iCycles p ⊗ₘ K₂.iCycles (q + 1)) ≫ P.pair p (q + 1) =
      (K₁.iCycles p ⊗ₘ K₂.d q (q + 1)) ≫ P.pair p (q + 1) := by
        rw [← Category.assoc, hto]
    _ = ((((K₁.iCycles p ⊗ₘ K₂.d q (q + 1)) ≫ P.pair p (q + 1)) ≫ e.hom) ≫
        e.inv) := by simp
    _ = ((((-1 : ℤ) ^ p) •
        (((K₁.iCycles p ⊗ₘ 𝟙 (K₂.X q)) ≫ P.pair p q) ≫
          K₃.d (p + q) (p + q + 1))) ≫ e.inv) := by rw [hpair]
    _ = (((-1 : ℤ) ^ p) •
        ((((K₁.iCycles p ⊗ₘ 𝟙 (K₂.X q)) ≫ P.pair p q) ≫
          K₃.d (p + q) (p + q + 1)) ≫ e.inv)) := by
            rw [Preadditive.zsmul_comp]
    _ = (((-1 : ℤ) ^ p) •
        ((K₁.iCycles p ⊗ₘ 𝟙 (K₂.X q)) ≫ P.pair p q)) ≫
          K₃.d (p + q) (p + (q + 1)) := by
            rw [Preadditive.zsmul_comp, Category.assoc, K₃.d_comp_XIsoOfEq_inv]

private lemma left_boundary (P : CochainGradedPairing K₁ K₂ K₃) (p q : ℕ)
    [K₁.HasHomology p] [K₂.HasHomology q] [K₃.HasHomology (p + q)] :
    ((K₁.toCycles ((ComplexShape.up ℕ).prev p) p ▷ K₂.cycles q) ≫
      P.pairCycles p q) ≫ K₃.homologyπ (p + q) = 0 := by
  cases p with
  | zero =>
      rw [CochainComplex.prev_nat_zero, K₁.toCycles_eq_zero (by simp [ComplexShape.up])]
      simp
  | succ p =>
      rw [CochainComplex.prev_nat_succ]
      exact left_succ P p q

private lemma right_boundary (P : CochainGradedPairing K₁ K₂ K₃) (p q : ℕ)
    [K₁.HasHomology p] [K₂.HasHomology q] [K₃.HasHomology (p + q)] :
    ((K₁.cycles p ◁ K₂.toCycles ((ComplexShape.up ℕ).prev q) q) ≫
      P.pairCycles p q) ≫ K₃.homologyπ (p + q) = 0 := by
  cases q with
  | zero =>
      rw [CochainComplex.prev_nat_zero, K₂.toCycles_eq_zero (by simp [ComplexShape.up])]
      simp
  | succ q =>
      rw [CochainComplex.prev_nat_succ]
      exact right_succ P p q

@[reassoc]
lemma boundaries_comp_homologyπ (P : CochainGradedPairing K₁ K₂ K₃) (p q : ℕ)
    [K₁.HasHomology p] [K₂.HasHomology q] [K₃.HasHomology (p + q)]
    [HasBinaryCoproduct
      (K₁.X ((ComplexShape.up ℕ).prev p) ⊗ K₂.cycles q)
      (K₁.cycles p ⊗ K₂.X ((ComplexShape.up ℕ).prev q))] :
    Limits.coprod.desc
        (K₁.toCycles ((ComplexShape.up ℕ).prev p) p ▷ K₂.cycles q)
        (K₁.cycles p ◁ K₂.toCycles ((ComplexShape.up ℕ).prev q) q) ≫
      P.pairCycles p q ≫ K₃.homologyπ (p + q) = 0 := by
  apply Limits.coprod.hom_ext
  · rw [Limits.coprod.inl_desc_assoc, comp_zero]
    simpa only [Category.assoc] using left_boundary P p q
  · rw [Limits.coprod.inr_desc_assoc, comp_zero]
    simpa only [Category.assoc] using right_boundary P p q

/-- Let C be a preadditive monoidal category with bilinear tensor product, and P a signed Leibniz
pairing of nonnegative cochain complexes K₁,K₂,K₃. Fix p,q ∈ ℕ with homology in degrees p,q,p+q.
Let ν_p and ν_q be the predecessors for the nonnegative cochain shape and β₁ : K₁,ν_p → Z^p(K₁),
β₂ : K₂,ν_q → Z^q(K₂) the incoming boundary maps. Assume the coproduct of K₁,ν_p ⊗ Z^q(K₂) and
Z^p(K₁) ⊗ K₂,ν_q exists, right tensoring by Z^q(K₂) and K₂,ν_q preserves the cokernel
coequalizer of β₁, and left tensoring by H^p(K₁) preserves that of β₂. The induced map H^p(K₁) ⊗
H^q(K₂) → H^{p+q}(K₃) satisfies (π₁ ⊗ π₂) ≫ pairHomology = pairCycles ≫ π₃. -/
noncomputable def pairHomology (P : CochainGradedPairing K₁ K₂ K₃) (p q : ℕ)
    [K₁.HasHomology p] [K₂.HasHomology q] [K₃.HasHomology (p + q)]
    [HasBinaryCoproduct
      (K₁.X ((ComplexShape.up ℕ).prev p) ⊗ K₂.cycles q)
      (K₁.cycles p ⊗ K₂.X ((ComplexShape.up ℕ).prev q))]
    [PreservesColimit
      (parallelPair (K₂.toCycles ((ComplexShape.up ℕ).prev q) q) 0)
      (tensorLeft (K₁.homology p))]
    [PreservesColimit
      (parallelPair (K₁.toCycles ((ComplexShape.up ℕ).prev p) p) 0)
      (tensorRight (K₂.cycles q))]
    [PreservesColimit
      (parallelPair (K₁.toCycles ((ComplexShape.up ℕ).prev p) p) 0)
      (tensorRight (K₂.X ((ComplexShape.up ℕ).prev q)))] :
    K₁.homology p ⊗ K₂.homology q ⟶ K₃.homology (p + q) :=
  HomologicalComplex.tensorHomologyDesc
    K₁ ((ComplexShape.up ℕ).prev p) p rfl
    K₂ ((ComplexShape.up ℕ).prev q) q rfl
    (P.pairCycles p q ≫ K₃.homologyπ (p + q))
    (P.boundaries_comp_homologyπ p q)

@[reassoc (attr := simp)]
lemma tensor_homologyπ_comp_pairHomology
    (P : CochainGradedPairing K₁ K₂ K₃) (p q : ℕ)
    [K₁.HasHomology p] [K₂.HasHomology q] [K₃.HasHomology (p + q)]
    [HasBinaryCoproduct
      (K₁.X ((ComplexShape.up ℕ).prev p) ⊗ K₂.cycles q)
      (K₁.cycles p ⊗ K₂.X ((ComplexShape.up ℕ).prev q))]
    [PreservesColimit
      (parallelPair (K₂.toCycles ((ComplexShape.up ℕ).prev q) q) 0)
      (tensorLeft (K₁.homology p))]
    [PreservesColimit
      (parallelPair (K₁.toCycles ((ComplexShape.up ℕ).prev p) p) 0)
      (tensorRight (K₂.cycles q))]
    [PreservesColimit
      (parallelPair (K₁.toCycles ((ComplexShape.up ℕ).prev p) p) 0)
      (tensorRight (K₂.X ((ComplexShape.up ℕ).prev q)))] :
    (K₁.homologyπ p ⊗ₘ K₂.homologyπ q) ≫ P.pairHomology p q =
      P.pairCycles p q ≫ K₃.homologyπ (p + q) :=
  HomologicalComplex.tensor_homologyπ_comp_tensorHomologyDesc
    K₁ ((ComplexShape.up ℕ).prev p) p rfl
    K₂ ((ComplexShape.up ℕ).prev q) q rfl
    (P.pairCycles p q ≫ K₃.homologyπ (p + q))
    (P.boundaries_comp_homologyπ p q)

lemma tensor_homologyπ_hom_ext {A : C} (p q : ℕ)
    [K₁.HasHomology p] [K₂.HasHomology q]
    [PreservesColimit
      (parallelPair (K₂.toCycles ((ComplexShape.up ℕ).prev q) q) 0)
      (tensorLeft (K₁.homology p))]
    [PreservesColimit
      (parallelPair (K₁.toCycles ((ComplexShape.up ℕ).prev p) p) 0)
      (tensorRight (K₂.cycles q))]
    {f g : K₁.homology p ⊗ K₂.homology q ⟶ A}
    (h : (K₁.homologyπ p ⊗ₘ K₂.homologyπ q) ≫ f =
      (K₁.homologyπ p ⊗ₘ K₂.homologyπ q) ≫ g) : f = g :=
  HomologicalComplex.tensor_homologyπ_hom_ext
    K₁ ((ComplexShape.up ℕ).prev p) p rfl
    K₂ ((ComplexShape.up ℕ).prev q) q rfl h

@[reassoc]
lemma pairCycles_naturality
    {L₁ L₂ L₃ : CochainComplex C ℕ}
    (P : CochainGradedPairing K₁ K₂ K₃)
    (Q : CochainGradedPairing L₁ L₂ L₃)
    (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) (f₃ : K₃ ⟶ L₃)
    (hpair : ∀ p q, P.pair p q ≫ f₃.f (p + q) =
      (f₁.f p ⊗ₘ f₂.f q) ≫ Q.pair p q)
    (p q : ℕ)
    [K₁.HasHomology p] [K₂.HasHomology q] [K₃.HasHomology (p + q)]
    [L₁.HasHomology p] [L₂.HasHomology q] [L₃.HasHomology (p + q)] :
    (K₁.cyclesMap f₁ p ⊗ₘ K₂.cyclesMap f₂ q) ≫ Q.pairCycles p q =
      P.pairCycles p q ≫ K₃.cyclesMap f₃ (p + q) := by
  rw [← cancel_mono (L₃.iCycles (p + q))]
  simp only [Category.assoc]
  rw [Q.pairCycles_i, cyclesMap_i, P.pairCycles_i_assoc]
  rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc, cyclesMap_i, cyclesMap_i]
  rw [← MonoidalCategory.tensorHom_comp_tensorHom_assoc, hpair]

lemma pairHomology_naturality
    {L₁ L₂ L₃ : CochainComplex C ℕ}
    (P : CochainGradedPairing K₁ K₂ K₃)
    (Q : CochainGradedPairing L₁ L₂ L₃)
    (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) (f₃ : K₃ ⟶ L₃)
    (hpair : ∀ p q, P.pair p q ≫ f₃.f (p + q) =
      (f₁.f p ⊗ₘ f₂.f q) ≫ Q.pair p q)
    (p q : ℕ)
    [K₁.HasHomology p] [K₂.HasHomology q] [K₃.HasHomology (p + q)]
    [L₁.HasHomology p] [L₂.HasHomology q] [L₃.HasHomology (p + q)]
    [HasBinaryCoproduct
      (K₁.X ((ComplexShape.up ℕ).prev p) ⊗ K₂.cycles q)
      (K₁.cycles p ⊗ K₂.X ((ComplexShape.up ℕ).prev q))]
    [PreservesColimit
      (parallelPair (K₂.toCycles ((ComplexShape.up ℕ).prev q) q) 0)
      (tensorLeft (K₁.homology p))]
    [PreservesColimit
      (parallelPair (K₁.toCycles ((ComplexShape.up ℕ).prev p) p) 0)
      (tensorRight (K₂.cycles q))]
    [PreservesColimit
      (parallelPair (K₁.toCycles ((ComplexShape.up ℕ).prev p) p) 0)
      (tensorRight (K₂.X ((ComplexShape.up ℕ).prev q)))]
    [HasBinaryCoproduct
      (L₁.X ((ComplexShape.up ℕ).prev p) ⊗ L₂.cycles q)
      (L₁.cycles p ⊗ L₂.X ((ComplexShape.up ℕ).prev q))]
    [PreservesColimit
      (parallelPair (L₂.toCycles ((ComplexShape.up ℕ).prev q) q) 0)
      (tensorLeft (L₁.homology p))]
    [PreservesColimit
      (parallelPair (L₁.toCycles ((ComplexShape.up ℕ).prev p) p) 0)
      (tensorRight (L₂.cycles q))]
    [PreservesColimit
      (parallelPair (L₁.toCycles ((ComplexShape.up ℕ).prev p) p) 0)
      (tensorRight (L₂.X ((ComplexShape.up ℕ).prev q)))] :
    (K₁.homologyMap f₁ p ⊗ₘ K₂.homologyMap f₂ q) ≫ Q.pairHomology p q =
      P.pairHomology p q ≫ K₃.homologyMap f₃ (p + q) := by
  apply HomologicalComplex.tensorHomologyDesc_naturality
    K₁ ((ComplexShape.up ℕ).prev p) p rfl
    K₂ ((ComplexShape.up ℕ).prev q) q rfl f₁ f₂
    (P.pairCycles p q ≫ K₃.homologyπ (p + q))
    (P.boundaries_comp_homologyπ p q)
    (Q.pairCycles p q ≫ L₃.homologyπ (p + q))
    (Q.boundaries_comp_homologyπ p q)
    (K₃.homologyMap f₃ (p + q))
  rw [pairCycles_naturality_assoc P Q f₁ f₂ f₃ hpair]
  rw [← K₃.homologyπ_naturality f₃]
  rw [Category.assoc]

lemma pairHomology_whisker
    {L₁ L₂ L₃ : CochainComplex C ℕ}
    (P : CochainGradedPairing K₁ K₂ K₃)
    (f₁ : L₁ ⟶ K₁) (f₂ : L₂ ⟶ K₂) (f₃ : K₃ ⟶ L₃)
    (p q : ℕ)
    [K₁.HasHomology p] [K₂.HasHomology q] [K₃.HasHomology (p + q)]
    [L₁.HasHomology p] [L₂.HasHomology q] [L₃.HasHomology (p + q)]
    [HasBinaryCoproduct
      (K₁.X ((ComplexShape.up ℕ).prev p) ⊗ K₂.cycles q)
      (K₁.cycles p ⊗ K₂.X ((ComplexShape.up ℕ).prev q))]
    [PreservesColimit
      (parallelPair (K₂.toCycles ((ComplexShape.up ℕ).prev q) q) 0)
      (tensorLeft (K₁.homology p))]
    [PreservesColimit
      (parallelPair (K₁.toCycles ((ComplexShape.up ℕ).prev p) p) 0)
      (tensorRight (K₂.cycles q))]
    [PreservesColimit
      (parallelPair (K₁.toCycles ((ComplexShape.up ℕ).prev p) p) 0)
      (tensorRight (K₂.X ((ComplexShape.up ℕ).prev q)))]
    [HasBinaryCoproduct
      (L₁.X ((ComplexShape.up ℕ).prev p) ⊗ L₂.cycles q)
      (L₁.cycles p ⊗ L₂.X ((ComplexShape.up ℕ).prev q))]
    [PreservesColimit
      (parallelPair (L₂.toCycles ((ComplexShape.up ℕ).prev q) q) 0)
      (tensorLeft (L₁.homology p))]
    [PreservesColimit
      (parallelPair (L₁.toCycles ((ComplexShape.up ℕ).prev p) p) 0)
      (tensorRight (L₂.cycles q))]
    [PreservesColimit
      (parallelPair (L₁.toCycles ((ComplexShape.up ℕ).prev p) p) 0)
      (tensorRight (L₂.X ((ComplexShape.up ℕ).prev q)))] :
    (P.whisker f₁ f₂ f₃).pairHomology p q =
      (L₁.homologyMap f₁ p ⊗ₘ L₂.homologyMap f₂ q) ≫
        P.pairHomology p q ≫ K₃.homologyMap f₃ (p + q) := by
  let P' := P.whisker f₁ f₂ (𝟙 K₃)
  have hpre :
      (L₁.homologyMap f₁ p ⊗ₘ L₂.homologyMap f₂ q) ≫
          P.pairHomology p q =
        P'.pairHomology p q := by
    simpa [P'] using
      pairHomology_naturality P' P f₁ f₂ (𝟙 K₃)
        (by simp [P']) p q
  have hpost :
      (P.whisker f₁ f₂ f₃).pairHomology p q =
        P'.pairHomology p q ≫ K₃.homologyMap f₃ (p + q) := by
    simpa [P'] using
      pairHomology_naturality P' (P.whisker f₁ f₂ f₃)
        (𝟙 L₁) (𝟙 L₂) f₃ (by simp [P']) p q
  calc
    (P.whisker f₁ f₂ f₃).pairHomology p q =
        P'.pairHomology p q ≫ K₃.homologyMap f₃ (p + q) := hpost
    _ = ((L₁.homologyMap f₁ p ⊗ₘ L₂.homologyMap f₂ q) ≫
          P.pairHomology p q) ≫ K₃.homologyMap f₃ (p + q) := by rw [hpre]
    _ = _ := Category.assoc _ _ _


end HomologicalComplex.CochainGradedPairing

end
