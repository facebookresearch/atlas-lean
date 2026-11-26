/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Monoidal.Limits.Cokernels
public import MathlibExt.Algebra.Homology.ChainGradedPairing
public import MathlibExt.Algebra.Homology.HomologyDegreeTransport
public import MathlibExt.Algebra.Homology.TensorHomologyDesc
/-!
# Homology pairings induced by chain pairings

For a pairing of nonnegative chain complexes in a preadditive monoidal category with bilinear
tensor product, the cycle pairing descends to H_p(K₁) ⊗ H_q(K₂) → H_{p+q}(K₃) when the required
boundary cokernels are preserved by the specified tensor functors. The descent uses three
differential facts: pairs of cycles are cycles, and a boundary in either variable maps to a
boundary in the target. The induced map is characterized by compatibility with the two
cycle-to-homology projections.
-/

@[expose] public section

noncomputable section

universe v u

open CategoryTheory Limits MonoidalCategory

namespace HomologicalComplex

universe w


end HomologicalComplex

namespace HomologicalComplex.ChainGradedPairing
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [(curriedTensor C).Additive]
  [∀ Z : C, ((curriedTensor C).obj Z).Additive]
  {K₁ K₂ K₃ : ChainComplex C ℕ} [K₁.HasTensor K₂]

/-- Let C be a preadditive monoidal category whose tensor product is additive in each variable. Let
P : K₁ ⊗ K₂ → K₃ pair nonnegative chain complexes with the tensor complex defined.
HomologyDescentData records three laws in every p,q ∈ ℕ: the composite (i_Z₁,p ⊗ i_Z₂,q) ≫
P_{p,q} is killed by the outgoing differential of K₃; (d_K₁,p+1,p ⊗ i_Z₂,q) ≫ P_{p,q} factors
through some d_K₃,i′,p+q; and (i_Z₁,p ⊗ d_K₂,q+1,q) ≫ P_{p,q} likewise factors through an
incoming differential. Each law requires only the cycle objects appearing in it. -/
structure HomologyDescentData (P : ChainGradedPairing K₁ K₂ K₃) where
  cycles_d : ∀ p q, [K₁.HasHomology p] → [K₂.HasHomology q] →
    ((K₁.iCycles p ⊗ₘ K₂.iCycles q) ≫ P.pair p q) ≫
      K₃.d (p + q) ((ComplexShape.down ℕ).next (p + q)) = 0
  left_factor : ∀ p q, [K₂.HasHomology q] →
    ∃ (i' : ℕ) (x : K₁.X (p + 1) ⊗ K₂.cycles q ⟶ K₃.X i'),
      (K₁.d (p + 1) p ⊗ₘ K₂.iCycles q) ≫ P.pair p q =
        x ≫ K₃.d i' (p + q)
  right_factor : ∀ p q, [K₁.HasHomology p] →
    ∃ (i' : ℕ) (x : K₁.cycles p ⊗ K₂.X (q + 1) ⟶ K₃.X i'),
      (K₁.iCycles p ⊗ₘ K₂.d (q + 1) q) ≫ P.pair p q =
        x ≫ K₃.d i' (p + q)

variable (P : ChainGradedPairing K₁ K₂ K₃) (D : HomologyDescentData P)

/-- Let C be a preadditive monoidal category whose tensor product is additive in each variable. Let
P : K₁ ⊗ K₂ → K₃ be a chain pairing with the tensor complex defined and D its cycle and boundary
descent data. For p,q ∈ ℕ, assume homology exists for K₁ in p, K₂ in q and K₃ in p+q. The
induced map Z_p(K₁) ⊗ Z_q(K₂) → Z_{p+q}(K₃) is uniquely characterized by its composite with the
target cycle inclusion being (i_Z₁,p ⊗ i_Z₂,q) ≫ P_{p,q}. -/
noncomputable def pairCycles (p q : ℕ)
    [K₁.HasHomology p] [K₂.HasHomology q] [K₃.HasHomology (p + q)] :
    K₁.cycles p ⊗ K₂.cycles q ⟶ K₃.cycles (p + q) :=
  K₃.liftCycles ((K₁.iCycles p ⊗ₘ K₂.iCycles q) ≫ P.pair p q)
    ((ComplexShape.down ℕ).next (p + q)) rfl (D.cycles_d p q)

omit [MonoidalPreadditive C] in
@[reassoc (attr := simp)]
lemma pairCycles_i (p q : ℕ)
    [K₁.HasHomology p] [K₂.HasHomology q] [K₃.HasHomology (p + q)] :
    pairCycles P D p q ≫ K₃.iCycles (p + q) =
      (K₁.iCycles p ⊗ₘ K₂.iCycles q) ≫ P.pair p q :=
  K₃.liftCycles_i _ _ rfl _

omit [MonoidalPreadditive C] in
private lemma left_boundary (p q : ℕ)
    [K₁.HasHomology p] [K₂.HasHomology q] [K₃.HasHomology (p + q)] :
    ((K₁.toCycles (p + 1) p ▷ K₂.cycles q) ≫ pairCycles P D p q) ≫
      K₃.homologyπ (p + q) = 0 := by
  rw [pairCycles, K₃.comp_liftCycles]
  obtain ⟨i', x, hx⟩ := D.left_factor p q
  have hto : (K₁.toCycles (p + 1) p ▷ K₂.cycles q) ≫
      (K₁.iCycles p ⊗ₘ K₂.iCycles q) =
      K₁.d (p + 1) p ⊗ₘ K₂.iCycles q := by
    calc
      _ = (K₁.toCycles (p + 1) p ⊗ₘ 𝟙 _) ≫
          (K₁.iCycles p ⊗ₘ K₂.iCycles q) := by
            simp [MonoidalCategory.tensorHom_def]
      _ = (K₁.toCycles (p + 1) p ≫ K₁.iCycles p) ⊗ₘ K₂.iCycles q := by
            rw [MonoidalCategory.tensorHom_comp_tensorHom]
            simp
      _ = _ := by rw [K₁.toCycles_i]
  apply K₃.liftCycles_homologyπ_eq_zero_of_boundary _ _ _ x
  rw [← Category.assoc, hto, hx]

omit [MonoidalPreadditive C] in
private lemma right_boundary (p q : ℕ)
    [K₁.HasHomology p] [K₂.HasHomology q] [K₃.HasHomology (p + q)] :
    ((K₁.cycles p ◁ K₂.toCycles (q + 1) q) ≫ pairCycles P D p q) ≫
      K₃.homologyπ (p + q) = 0 := by
  rw [pairCycles, K₃.comp_liftCycles]
  obtain ⟨i', x, hx⟩ := D.right_factor p q
  have hto : (K₁.cycles p ◁ K₂.toCycles (q + 1) q) ≫
      (K₁.iCycles p ⊗ₘ K₂.iCycles q) =
      K₁.iCycles p ⊗ₘ K₂.d (q + 1) q := by
    calc
      _ = (𝟙 _ ⊗ₘ K₂.toCycles (q + 1) q) ≫
          (K₁.iCycles p ⊗ₘ K₂.iCycles q) := by
            simp [MonoidalCategory.tensorHom_def']
      _ = K₁.iCycles p ⊗ₘ
          (K₂.toCycles (q + 1) q ≫ K₂.iCycles q) := by
            rw [MonoidalCategory.tensorHom_comp_tensorHom]
            simp
      _ = _ := by rw [K₂.toCycles_i]
  apply K₃.liftCycles_homologyπ_eq_zero_of_boundary _ _ _ x
  rw [← Category.assoc, hto, hx]

omit [MonoidalPreadditive C] in
@[reassoc]
lemma boundaries_comp_homologyπ (p q : ℕ)
    [K₁.HasHomology p] [K₂.HasHomology q] [K₃.HasHomology (p + q)]
    [HasBinaryCoproduct
      (K₁.X (p + 1) ⊗ K₂.cycles q)
      (K₁.cycles p ⊗ K₂.X (q + 1))] :
    Limits.coprod.desc
        (K₁.toCycles (p + 1) p ▷ K₂.cycles q)
        (K₁.cycles p ◁ K₂.toCycles (q + 1) q) ≫
      pairCycles P D p q ≫ K₃.homologyπ (p + q) = 0 := by
  apply Limits.coprod.hom_ext
  · rw [Limits.coprod.inl_desc_assoc, comp_zero]
    simpa only [Category.assoc] using left_boundary P D p q
  · rw [Limits.coprod.inr_desc_assoc, comp_zero]
    simpa only [Category.assoc] using right_boundary P D p q

/-- Let C be a preadditive monoidal category whose tensor product is additive in each variable. Let
P : K₁ ⊗ K₂ → K₃ be a pairing with its tensor complex and descent data D. Fix p,q ∈ ℕ with
homology in degrees p,q,p+q. Write β₁ : K₁,p+1 → Z_p(K₁) and β₂ : K₂,q+1 → Z_q(K₂) for the
incoming boundary maps. Assume the coproduct of K₁,p+1 ⊗ Z_q(K₂) and Z_p(K₁) ⊗ K₂,q+1 exists,
tensoring on the right by Z_q(K₂) and K₂,q+1 preserves the cokernel coequalizer of β₁, and
tensoring on the left by H_p(K₁) preserves that of β₂. Then pairHomology is the map H_p(K₁) ⊗
H_q(K₂) → H_{p+q}(K₃) characterized by (π₁ ⊗ π₂) ≫ pairHomology = pairCycles ≫ π₃. -/
noncomputable def pairHomology (p q : ℕ)
    [K₁.HasHomology p] [K₂.HasHomology q] [K₃.HasHomology (p + q)]
    [HasBinaryCoproduct
      (K₁.X (p + 1) ⊗ K₂.cycles q)
      (K₁.cycles p ⊗ K₂.X (q + 1))]
    [PreservesColimit
      (parallelPair (K₂.toCycles (q + 1) q) 0)
      (tensorLeft (K₁.homology p))]
    [PreservesColimit
      (parallelPair (K₁.toCycles (p + 1) p) 0)
      (tensorRight (K₂.cycles q))]
    [PreservesColimit
      (parallelPair (K₁.toCycles (p + 1) p) 0)
      (tensorRight (K₂.X (q + 1)))] :
    K₁.homology p ⊗ K₂.homology q ⟶ K₃.homology (p + q) :=
  HomologicalComplex.tensorHomologyDesc
    K₁ (p + 1) p (ChainComplex.prev ℕ p)
    K₂ (q + 1) q (ChainComplex.prev ℕ q)
    (pairCycles P D p q ≫ K₃.homologyπ (p + q))
    (boundaries_comp_homologyπ P D p q)

@[reassoc (attr := simp)]
lemma tensor_homologyπ_comp_pairHomology (p q : ℕ)
    [K₁.HasHomology p] [K₂.HasHomology q] [K₃.HasHomology (p + q)]
    [HasBinaryCoproduct
      (K₁.X (p + 1) ⊗ K₂.cycles q)
      (K₁.cycles p ⊗ K₂.X (q + 1))]
    [PreservesColimit
      (parallelPair (K₂.toCycles (q + 1) q) 0)
      (tensorLeft (K₁.homology p))]
    [PreservesColimit
      (parallelPair (K₁.toCycles (p + 1) p) 0)
      (tensorRight (K₂.cycles q))]
    [PreservesColimit
      (parallelPair (K₁.toCycles (p + 1) p) 0)
      (tensorRight (K₂.X (q + 1)))] :
    (K₁.homologyπ p ⊗ₘ K₂.homologyπ q) ≫ pairHomology P D p q =
      pairCycles P D p q ≫ K₃.homologyπ (p + q) :=
  HomologicalComplex.tensor_homologyπ_comp_tensorHomologyDesc
    K₁ (p + 1) p (ChainComplex.prev ℕ p)
    K₂ (q + 1) q (ChainComplex.prev ℕ q)
    (pairCycles P D p q ≫ K₃.homologyπ (p + q))
    (boundaries_comp_homologyπ P D p q)

omit [(curriedTensor C).Additive] [∀ Z : C, ((curriedTensor C).obj Z).Additive]
    [K₁.HasTensor K₂] in
lemma tensor_homologyπ_hom_ext {A : C} (p q : ℕ)
    [K₁.HasHomology p] [K₂.HasHomology q]
    [PreservesColimit
      (parallelPair (K₂.toCycles (q + 1) q) 0)
      (tensorLeft (K₁.homology p))]
    [PreservesColimit
      (parallelPair (K₁.toCycles (p + 1) p) 0)
      (tensorRight (K₂.cycles q))]
    {f g : K₁.homology p ⊗ K₂.homology q ⟶ A}
    (h : (K₁.homologyπ p ⊗ₘ K₂.homologyπ q) ≫ f =
      (K₁.homologyπ p ⊗ₘ K₂.homologyπ q) ≫ g) : f = g :=
  HomologicalComplex.tensor_homologyπ_hom_ext
    K₁ (p + 1) p (ChainComplex.prev ℕ p)
    K₂ (q + 1) q (ChainComplex.prev ℕ q) h

omit [MonoidalPreadditive C] in
@[reassoc]
lemma pairCycles_naturality
    {L₁ L₂ L₃ : ChainComplex C ℕ} [L₁.HasTensor L₂]
    (Q : ChainGradedPairing L₁ L₂ L₃) (E : HomologyDescentData Q)
    (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) (f₃ : K₃ ⟶ L₃)
    (hpair : ∀ p q, P.pair p q ≫ f₃.f (p + q) =
      (f₁.f p ⊗ₘ f₂.f q) ≫ Q.pair p q)
    (p q : ℕ)
    [K₁.HasHomology p] [K₂.HasHomology q] [K₃.HasHomology (p + q)]
    [L₁.HasHomology p] [L₂.HasHomology q] [L₃.HasHomology (p + q)] :
    (K₁.cyclesMap f₁ p ⊗ₘ K₂.cyclesMap f₂ q) ≫ pairCycles Q E p q =
      pairCycles P D p q ≫ K₃.cyclesMap f₃ (p + q) := by
  rw [← cancel_mono (L₃.iCycles (p + q))]
  simp only [Category.assoc]
  rw [pairCycles_i Q E, cyclesMap_i, pairCycles_i_assoc P D]
  rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc, cyclesMap_i, cyclesMap_i]
  rw [← MonoidalCategory.tensorHom_comp_tensorHom_assoc, ← hpair]

lemma pairHomology_naturality
    {L₁ L₂ L₃ : ChainComplex C ℕ} [L₁.HasTensor L₂]
    (Q : ChainGradedPairing L₁ L₂ L₃) (E : HomologyDescentData Q)
    (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) (f₃ : K₃ ⟶ L₃)
    (hpair : ∀ p q, P.pair p q ≫ f₃.f (p + q) =
      (f₁.f p ⊗ₘ f₂.f q) ≫ Q.pair p q)
    (p q : ℕ)
    [K₁.HasHomology p] [K₂.HasHomology q] [K₃.HasHomology (p + q)]
    [L₁.HasHomology p] [L₂.HasHomology q] [L₃.HasHomology (p + q)]
    [HasBinaryCoproduct
      (K₁.X (p + 1) ⊗ K₂.cycles q)
      (K₁.cycles p ⊗ K₂.X (q + 1))]
    [PreservesColimit
      (parallelPair (K₂.toCycles (q + 1) q) 0)
      (tensorLeft (K₁.homology p))]
    [PreservesColimit
      (parallelPair (K₁.toCycles (p + 1) p) 0)
      (tensorRight (K₂.cycles q))]
    [PreservesColimit
      (parallelPair (K₁.toCycles (p + 1) p) 0)
      (tensorRight (K₂.X (q + 1)))]
    [HasBinaryCoproduct
      (L₁.X (p + 1) ⊗ L₂.cycles q)
      (L₁.cycles p ⊗ L₂.X (q + 1))]
    [PreservesColimit
      (parallelPair (L₂.toCycles (q + 1) q) 0)
      (tensorLeft (L₁.homology p))]
    [PreservesColimit
      (parallelPair (L₁.toCycles (p + 1) p) 0)
      (tensorRight (L₂.cycles q))]
    [PreservesColimit
      (parallelPair (L₁.toCycles (p + 1) p) 0)
      (tensorRight (L₂.X (q + 1)))] :
    (K₁.homologyMap f₁ p ⊗ₘ K₂.homologyMap f₂ q) ≫ pairHomology Q E p q =
      pairHomology P D p q ≫ K₃.homologyMap f₃ (p + q) := by
  apply HomologicalComplex.tensorHomologyDesc_naturality
    K₁ (p + 1) p (ChainComplex.prev ℕ p)
    K₂ (q + 1) q (ChainComplex.prev ℕ q) f₁ f₂
    (pairCycles P D p q ≫ K₃.homologyπ (p + q))
    (boundaries_comp_homologyπ P D p q)
    (pairCycles Q E p q ≫ L₃.homologyπ (p + q))
    (boundaries_comp_homologyπ Q E p q)
    (K₃.homologyMap f₃ (p + q))
  rw [pairCycles_naturality_assoc P D Q E f₁ f₂ f₃ hpair]
  rw [← K₃.homologyπ_naturality f₃]
  rw [Category.assoc]

end HomologicalComplex.ChainGradedPairing

end
