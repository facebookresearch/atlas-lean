/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Avocado
-/
module

public import MathlibExt.Algebra.Homology.ChainGradedPairing
public import MathlibExt.Algebra.Homology.KoszulTensorBraiding
public import MathlibExt.Algebra.Homology.TotalComplexSymmetryDownNat

/-!
# Koszul braiding compatibility of chain pairings

Let C be a preadditive braided monoidal category whose tensor is additive
in both variables. For nonnegative complexes K₁,K₂, assume both ordered
tensor complexes exist.

If P:K₁⊗K₂→K₃ and Q:K₂⊗K₁→L₃ agree through a target map f and the
Koszul chain braiding, their component pairings satisfy the
(-1)^(p q) sign rule, coefficient braiding and the target degree
identification q+p=p+q.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory MonoidalCategory

namespace HomologicalComplex.ChainGradedPairing

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [MonoidalCategory C] [BraidedCategory C]
  [(curriedTensor C).Additive]
  [∀ Z : C, ((curriedTensor C).obj Z).Additive]
  {K₁ K₂ K₃ L₃ : ChainComplex C ℕ}
  [K₁.HasTensor K₂] [K₂.HasTensor K₁]

omit [BraidedCategory C] in
private lemma ιTensorObj_comp_XIsoOfEq
    (A B : ChainComplex C ℕ) [A.HasTensor B]
    (p q n n' : ℕ) (h : p + q = n) (e : n = n') :
    ιTensorObj A B p q n h ≫ ((tensorObj A B).XIsoOfEq e).hom =
      ιTensorObj A B p q n' (h.trans e) := by
  subst e
  simp

/-- Let C be a preadditive braided monoidal category with additive
tensoring, and K₁⊗K₂,K₂⊗K₁ existing nonnegative tensor complexes.
Suppose P:K₁⊗K₂→K₃, Q:K₂⊗K₁→L₃ and f:K₃→L₃ satisfy
f∘P=Q∘β_Koszul. Then in bidegree (p,q),
f_(p+q)∘P_(p,q)=(-1)^(p q) Q_(q,p)∘β_(K₁,p,K₂,q),
with the target degree q+p identified with p+q. -/
lemma pair_braiding_of_koszul
    (P : ChainGradedPairing K₁ K₂ K₃)
    (Q : ChainGradedPairing K₂ K₁ L₃) (f : K₃ ⟶ L₃)
    (h : P ≫ f = (koszulTensorBraidingIso K₁ K₂).hom ≫ Q)
    (p q : ℕ) :
    P.pair p q ≫ f.f (p + q) =
      ((-1 : ℤ) ^ (p * q)) •
        ((β_ (K₁.X p) (K₂.X q)).hom ≫ Q.pair q p ≫
          (L₃.XIsoOfEq (Nat.add_comm q p)).hom) := by
  unfold pair
  rw [Category.assoc]
  have hcomponent := congrArg (fun k ↦ k.f (p + q)) h
  simp only [HomologicalComplex.comp_f] at hcomponent
  rw [hcomponent]
  rw [ιTensorObj_koszulTensorBraidingIso_hom_assoc]
  simp only [ComplexShape.σ_down_ℕ]
  conv_lhs => rw [Linear.units_smul_comp]
  have htail :
      ιTensorObj K₂ K₁ q p (p + q) (Nat.add_comm q p) ≫ Q.f (p + q) =
        ιTensorObj K₂ K₁ q p (q + p) rfl ≫ Q.f (q + p) ≫
          (L₃.XIsoOfEq (Nat.add_comm q p)).hom := by
    rw [XIsoOfEq_hom_naturality]
    rw [← Category.assoc, ιTensorObj_comp_XIsoOfEq]
  simp only [Category.assoc]
  rw [htail]
  rfl

end HomologicalComplex.ChainGradedPairing

end
