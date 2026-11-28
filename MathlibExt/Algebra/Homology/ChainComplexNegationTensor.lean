/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.HomologicalComplexRescaling
public import Mathlib.Algebra.Homology.Monoidal

/-!
# Tensor coherence of differential negation

Let C be a preadditive monoidal category with a zero object and tensor
additive in both variables. Negating a chain differential gives the
isomorphism s_K:K≅(-dK) with degree n map (-1)^n id.

For existing tensor products, s_K⊗s_L has degree n value (-1)^n id,
since each tensor summand p+q=n contributes (-1)^p(-1)^q.
Conjugating a diagonal K→K⊗K through these sign maps leaves every
degree component unchanged. Object and morphism universes are independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u

namespace ChainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [MonoidalCategory C]
  [(curriedTensor C).Additive] [∀ X : C, ((curriedTensor C).obj X).Additive]

variable (K L : ChainComplex C ℕ)
  [HomologicalComplex.HasTensor K L]
  [HomologicalComplex.HasTensor (HomologicalComplex.negateDifferentials K)
    (HomologicalComplex.negateDifferentials L)]

omit [HasZeroObject C] in
/-- Let C be a preadditive monoidal category with a zero object,
and assume tensoring is additive in both variables.
Let K,L be nonnegative chain complexes for which K⊗L and
(-dK)⊗(-dL) exist. Differential negation has
s_K:K≅(-dK), with degree n map (-1)^n id.
The degree n component of s_K⊗s_L is (-1)^n times the
identity under the common tensor-degree identification. -/
theorem negation_tensor_f (n : ℕ) :
    (HomologicalComplex.tensorHom (negationIso K).hom (negationIso L).hom).f n =
      degreeSign n • 𝟙 ((HomologicalComplex.tensorObj K L).X n) := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  change p + q = n at hpq
  have hp : ((curriedTensor C).map (degreeSign p • 𝟙 (K.X p))).app (L.X q) =
      degreeSign p • 𝟙 (K.X p ⊗ L.X q) := by
    rw [CategoryTheory.Functor.map_zsmul, CategoryTheory.Functor.map_id]
    rfl
  have hq : ((curriedTensor C).obj (K.X p)).map (degreeSign q • 𝟙 (L.X q)) =
      degreeSign q • 𝟙 (K.X p ⊗ L.X q) := by
    rw [CategoryTheory.Functor.map_zsmul, CategoryTheory.Functor.map_id]
    rfl
  have h := HomologicalComplex.ι_mapBifunctorMap
    (negationIso K).hom (negationIso L).hom (curriedTensor C) (ComplexShape.down ℕ) p q n hpq
  rw [negationIso_hom_f K p, negationIso_hom_f L q] at h
  change HomologicalComplex.ιTensorObj K L p q n hpq ≫
      (HomologicalComplex.tensorHom (negationIso K).hom (negationIso L).hom).f n =
    ((curriedTensor C).map (degreeSign p • 𝟙 (K.X p))).app (L.X q) ≫
      ((curriedTensor C).obj (K.X p)).map (degreeSign q • 𝟙 (L.X q)) ≫
        HomologicalComplex.ιTensorObj K L p q n hpq at h
  erw [hp, hq] at h
  exact h.trans (by
    change (degreeSign p • 𝟙 _) ≫ (degreeSign q • 𝟙 _) ≫
        HomologicalComplex.ιTensorObj K L p q n hpq =
      HomologicalComplex.ιTensorObj K L p q n hpq ≫ (degreeSign n • 𝟙 _)
    have hs : degreeSign p * degreeSign q = degreeSign n :=
      (degreeSign_add p q).symm.trans (congrArg degreeSign hpq)
    have hs' : degreeSign q * degreeSign p = degreeSign n := (mul_comm _ _).trans hs
    simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul,
      Category.id_comp, Category.comp_id, smul_smul]
    let t := HomologicalComplex.ιTensorObj K L p q n hpq
    change (degreeSign q * degreeSign p) • (𝟙 (K.X p ⊗ L.X q) ≫ t) = degreeSign n • t
    exact (congrArg (fun f => (degreeSign q * degreeSign p) • f) (Category.id_comp t)).trans
      (congrArg (fun r : ℤ => r • t) hs'))

omit [HasZeroObject C] in
/-- Let C be a preadditive monoidal category with a zero object,
and assume tensoring is additive in both variables.
Let K,L be nonnegative chain complexes for which K⊗L and
(-dK)⊗(-dL) exist. Differential negation has
s_K:K≅(-dK), with degree n map (-1)^n id.
On the summand K_p⊗L_q with p+q=n, the tensor sign map
satisfies (s_K⊗s_L)∘ι_(p,q)=(-1)^(p+q)ι_(p,q). -/
theorem ι_negation_tensor (p q n : ℕ) (hpq : p + q = n) :
    HomologicalComplex.ιTensorObj K L p q n hpq ≫
        (HomologicalComplex.tensorHom (negationIso K).hom (negationIso L).hom).f n =
      degreeSign (p + q) • HomologicalComplex.ιTensorObj K L p q n hpq := by
  erw [negation_tensor_f, Preadditive.comp_zsmul, Category.comp_id, hpq]
  rfl

end ChainComplex

end

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u

namespace ChainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [MonoidalCategory C]
  [(curriedTensor C).Additive] [∀ X : C, ((curriedTensor C).obj X).Additive]

omit [HasZeroObject C] in
/-- In a preadditive monoidal category with zero object and additive
tensoring, let K⊗K and (-dK)⊗(-dK) exist.
For a chain map f:K→K⊗K, transport by s_K⁻¹ on the source and
s_K⊗s_K on the target has degree n component f_n.
The two degree-n signs cancel. -/
theorem negation_tensor_conjugate_f (K : ChainComplex C ℕ)
    [HomologicalComplex.HasTensor K K]
    [HomologicalComplex.HasTensor (HomologicalComplex.negateDifferentials K)
      (HomologicalComplex.negateDifferentials K)]
    (f : K ⟶ HomologicalComplex.tensorObj K K) (n : ℕ) :
    ((negationIso K).inv ≫ f ≫
      HomologicalComplex.tensorHom (negationIso K).hom (negationIso K).hom).f n = f.f n := by
  change (negationIso K).inv.f n ≫
      (f.f n ≫ (HomologicalComplex.tensorHom (negationIso K).hom (negationIso K).hom).f n) = _
  have ht := negation_tensor_f K K n
  have hs := negationIso_inv_f K n
  have hc : (degreeSign n • 𝟙 (K.X n)) ≫
      (f.f n ≫ (degreeSign n • 𝟙 ((HomologicalComplex.tensorObj K K).X n))) = f.f n := by
    rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.id_comp,
      Category.comp_id, smul_smul, degreeSign_sq, one_smul]
  exact (congrArg₂ (fun (s : K.X n ⟶ K.X n)
      (t : (HomologicalComplex.tensorObj K K).X n ⟶ (HomologicalComplex.tensorObj K K).X n) =>
      s ≫ (f.f n ≫ t)) hs ht).trans hc

end ChainComplex

end
