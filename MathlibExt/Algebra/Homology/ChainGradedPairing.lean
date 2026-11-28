/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.Monoidal

/-!
# Pairings of nonnegatively graded chain complexes

In a preadditive monoidal category with tensor product additive in each variable, a pairing of
nonnegative chain complexes K₁,K₂,K₃ is a chain map K₁ ⊗ K₂ → K₃, assuming the tensor complex
exists. Its bidegree-(p,q) component maps K₁,p ⊗ K₂,q to K₃,p+q and satisfies the signed Leibniz
rule dP(x,y) = P(dx,y) + (−1)^p P(x,dy). Pairings can be postcomposed with chain maps.
-/

@[expose] public section

noncomputable section

universe v u

open CategoryTheory MonoidalCategory

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [(curriedTensor C).Additive]
  [∀ Z : C, ((curriedTensor C).obj Z).Additive]

/-- Let C be a preadditive monoidal category whose tensor product is additive in each variable. For
nonnegative chain complexes K₁,K₂,K₃ with K₁ ⊗ K₂ defined, a ChainGradedPairing is a chain map P
: K₁ ⊗ K₂ → K₃. Its components P_{p,q} : K₁,p ⊗ K₂,q → K₃,p+q satisfy the signed Leibniz rule
dP(x,y) = P(dx,y) + (−1)^p P(x,dy), with outgoing degree-zero differentials interpreted as zero. -/
abbrev ChainGradedPairing
    (K₁ K₂ K₃ : ChainComplex C ℕ) [K₁.HasTensor K₂] :=
  HomologicalComplex.tensorObj K₁ K₂ ⟶ K₃

namespace ChainGradedPairing

variable {K₁ K₂ K₃ : ChainComplex C ℕ} [K₁.HasTensor K₂]

/-- Let C be a preadditive monoidal category whose tensor product is additive in each variable. Let
P : K₁ ⊗ K₂ → K₃ pair nonnegative chain complexes, with the tensor complex defined. For p,q ∈ ℕ,
pair P p q is the composite K₁,p ⊗ K₂,q → (K₁ ⊗ K₂)_{p+q} → K₃,p+q of the tensor summand
inclusion and the degree-(p+q) component of P. -/
noncomputable def pair (P : ChainGradedPairing K₁ K₂ K₃) (p q : ℕ) :
    K₁.X p ⊗ K₂.X q ⟶ K₃.X (p + q) :=
  HomologicalComplex.ιTensorObj K₁ K₂ p q (p + q) rfl ≫ P.f (p + q)

/-- Let C be a preadditive monoidal category whose tensor product is additive in each variable.
Given a pairing P : K₁ ⊗ K₂ → K₃ of nonnegative chain complexes and a chain map f : K₃ → K₄,
with K₁ ⊗ K₂ defined, postcomp P f is the pairing P ≫ f. Its bidegree component is P_{p,q} ≫
f_{p+q}. -/
def postcomp {K₄ : ChainComplex C ℕ}
    (P : ChainGradedPairing K₁ K₂ K₃) (f : K₃ ⟶ K₄) :
    ChainGradedPairing K₁ K₂ K₄ :=
  P ≫ f

@[reassoc (attr := simp)]
theorem pair_postcomp {K₄ : ChainComplex C ℕ}
    (P : ChainGradedPairing K₁ K₂ K₃) (f : K₃ ⟶ K₄) (p q : ℕ) :
    (P.postcomp f).pair p q = P.pair p q ≫ f.f (p + q) := by
  simp [postcomp, pair, HomologicalComplex.comp_f, Category.assoc]

@[reassoc]
theorem pair_naturality
    {L₁ L₂ L₃ : ChainComplex C ℕ}
    [L₁.HasTensor L₂]
    (P : ChainGradedPairing K₁ K₂ K₃)
    (Q : ChainGradedPairing L₁ L₂ L₃)
    (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) (f₃ : K₃ ⟶ L₃)
    (hpair : HomologicalComplex.tensorHom f₁ f₂ ≫ Q = P ≫ f₃)
    (p q : ℕ) :
    (f₁.f p ⊗ₘ f₂.f q) ≫ Q.pair p q =
      P.pair p q ≫ f₃.f (p + q) := by
  have hpairComponent := congrArg (fun f => f.f (p + q)) hpair
  have hpairComponent' :
      (HomologicalComplex.tensorHom f₁ f₂).f (p + q) ≫ Q.f (p + q) =
        P.f (p + q) ≫ f₃.f (p + q) := by
    simpa only [HomologicalComplex.comp_f] using hpairComponent
  calc
    (f₁.f p ⊗ₘ f₂.f q) ≫ Q.pair p q =
        HomologicalComplex.ιTensorObj K₁ K₂ p q (p + q) rfl ≫
          (HomologicalComplex.tensorHom f₁ f₂).f (p + q) ≫ Q.f (p + q) := by
            rw [pair, MonoidalCategory.tensorHom_def_assoc]
            exact (HomologicalComplex.ι_mapBifunctorMap_assoc f₁ f₂
              (curriedTensor C) (ComplexShape.down ℕ) p q (p + q) rfl
              (Q.f (p + q))).symm
    _ = HomologicalComplex.ιTensorObj K₁ K₂ p q (p + q) rfl ≫
        P.f (p + q) ≫ f₃.f (p + q) := by rw [hpairComponent']
    _ = P.pair p q ≫ f₃.f (p + q) := by rw [pair, Category.assoc]

end ChainGradedPairing

end HomologicalComplex
