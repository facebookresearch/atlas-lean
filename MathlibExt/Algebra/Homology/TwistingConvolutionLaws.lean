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

public import MathlibExt.RingTheory.DifferentialGraded.TwistingCochain
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.ComplexShapeSigns
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.Monoidal.Comon_

/-!
# Bilinearity and differentiation of graded convolution

Let R be a commutative ring, C a dg R-coalgebra and A a dg R-algebra, both integer cochain
complexes. Assume all graded tensor coproducts exist, tensoring preserves zero on both sides,
tensoring commutes with the coproducts used for reassociation, and fourfold summand inclusions
determine maps.

For cochains f:C→A of degree m and g:C→A of degree n, set f⋆g=μ_A(f⊗g)Δ_C. On a (p,q)-summand
the tensor uses the Koszul factor (-1)^{np}. Reassociation of three component tensors identifies
the exponents (n+k)p+kr and np+k(p+r).

Convolution is additive in each variable and commutes with integer unit scalars. Its
differential satisfies δ(f⋆g)=(δf)⋆g+(-1)^m f⋆(δg), with both terms identified in degree m+n+1.
The degree-zero cochain e is the composite C→I→A of the coalgebra counit and algebra unit; I is
concentrated in degree zero.

For background on graded convolution, see J.-L. Loday and B. Vallette, Algebraic Operads,
Springer, 2012, <https://doi.org/10.1007/978-3-642-30362-3>.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

namespace CochainComplex

variable {R : Type*} [CommRing R]
variable {C A : CochainComplex (ModuleCat R) ℤ}

/-- Over a commutative ring R, let f:X₁→Y₁ and g:X₂→Y₂ be R-linear maps. Tensoring respects negation
in the left factor: (-f)⊗g=-(f⊗g) as maps X₁⊗X₂→Y₁⊗Y₂. -/
private lemma neg_tensorHom_left {X₁ Y₁ X₂ Y₂ : ModuleCat R}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : ((-f) ⊗ₘ g) = -((f ⊗ₘ g)) := by
  have h : ((-f) ⊗ₘ g) + ((f ⊗ₘ g)) = 0 := by
    rw [← MonoidalPreadditive.add_tensor, neg_add_cancel,
      MonoidalPreadditive.zero_tensor]
  exact eq_neg_of_add_eq_zero_left h

/-- Over a commutative ring R, let f:X₁→Y₁ and g:X₂→Y₂ be R-linear maps. Tensoring respects negation
in the right factor: f⊗(-g)=-(f⊗g) as maps X₁⊗X₂→Y₁⊗Y₂. -/
private lemma neg_tensorHom_right {X₁ Y₁ X₂ Y₂ : ModuleCat R}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : ((f ⊗ₘ (-g))) = -((f ⊗ₘ g)) := by
  have h : ((f ⊗ₘ (-g))) + ((f ⊗ₘ g)) = 0 := by
    rw [← MonoidalPreadditive.tensor_add, neg_add_cancel,
      MonoidalPreadditive.tensor_zero]
  exact eq_neg_of_add_eq_zero_left h

/-- Over a commutative ring R, let f:X₁→Y₁ and g:X₂→Y₂ be R-linear maps. For any integer unit k∈ℤˣ,
(k•f)⊗g=k•(f⊗g) as maps X₁⊗X₂→Y₁⊗Y₂. -/
private lemma tensorHom_units_smul_left {X₁ Y₁ X₂ Y₂ : ModuleCat R} (k : ℤˣ)
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : ((k • f) ⊗ₘ g) = k • (f ⊗ₘ g) := by
  rcases Int.units_eq_one_or k with rfl | rfl
  · simp only [one_smul]
  · simp only [Units.neg_smul, one_smul, neg_tensorHom_left]

/-- Over a commutative ring R, let f:X₁→Y₁ and g:X₂→Y₂ be R-linear maps. For any integer unit k∈ℤˣ,
f⊗(k•g)=k•(f⊗g) as maps X₁⊗X₂→Y₁⊗Y₂. -/
private lemma tensorHom_units_smul_right {X₁ Y₁ X₂ Y₂ : ModuleCat R} (k : ℤˣ)
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : ((f ⊗ₘ (k • g))) = k • (f ⊗ₘ g) := by
  rcases Int.units_eq_one_or k with rfl | rfl
  · simp only [one_smul]
  · simp only [Units.neg_smul, one_smul, neg_tensorHom_right]

/-- Over a commutative ring R, let C,A be integer cochain complexes and f,g,h:C→A have degrees
m,n,k. For input degrees i₁,i₂,i₃, the signed map ((f_{i₁}⊗g_{i₂})⊗h_{i₃})≫α_A equals
α_C≫(f_{i₁}⊗(g_{i₂}⊗h_{i₃})), with exponents (n+k)i₁+ki₂ and ni₁+k(i₁+i₂), respectively. The two
exponents are equal, and α_C,α_A are the associators at the source and shifted target terms. -/
theorem tensorCochain_assoc {m n p : ℤ} (f : HomComplex.Cochain C A m)
    (g : HomComplex.Cochain C A n) (h : HomComplex.Cochain C A p)
    (i₁ i₂ i₃ : ℤ) :
    (((n + p) * i₁ + p * i₂).negOnePow •
        ((f.v i₁ (i₁ + m) rfl ⊗ₘ g.v i₂ (i₂ + n) rfl) ⊗ₘ h.v i₃ (i₃ + p) rfl)) ≫
      (α_ (A.X (i₁ + m)) (A.X (i₂ + n)) (A.X (i₃ + p))).hom =
    (α_ (C.X i₁) (C.X i₂) (C.X i₃)).hom ≫ ((n * i₁ + p * (i₁ + i₂)).negOnePow •
        (f.v i₁ (i₁ + m) rfl ⊗ₘ (g.v i₂ (i₂ + n) rfl ⊗ₘ h.v i₃ (i₃ + p) rfl))) := by
  have hsign : (n + p) * i₁ + p * i₂ = n * i₁ + p * (i₁ + i₂) := by
    rw [add_mul, mul_add, add_assoc]
  rw [hsign, Linear.units_smul_comp, Linear.comp_units_smul,
    MonoidalCategory.associator_naturality]

variable [∀ (X₁ X₂ : GradedObject ℤ (ModuleCat R)), GradedObject.HasTensor X₁ X₂]
variable [∀ (X : ModuleCat R), PreservesColimit (Functor.empty.{0} (ModuleCat R))
  ((curriedTensor (ModuleCat R)).obj X)]
variable [∀ (X : ModuleCat R), PreservesColimit (Functor.empty.{0} (ModuleCat R))
  ((curriedTensor (ModuleCat R)).flip.obj X)]
variable [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
variable [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
variable [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

variable [MonObj A] [ComonObj C]

/-- Let R be a commutative ring, C a dg R-coalgebra and A a dg R-algebra, both integer cochain
complexes. Assume all graded tensor coproducts exist, tensoring preserves zero on both sides,
tensoring commutes with the coproducts used for reassociation, and fourfold summand inclusions
determine maps. The cochain e:C→A of degree zero is ε_C≫η_A, where ε_C:C→I is the coalgebra
counit and η_A:I→A is the algebra unit. The unit cochain complex I is concentrated in degree
zero. -/
noncomputable def convOne : HomComplex.Cochain C A 0 :=
  (HomComplex.Cochain.ofHom (ComonObj.counit (X := C))).comp
    (HomComplex.Cochain.ofHom (MonObj.one (X := A))) (zero_add 0)

/-- For two integer cochain shapes, both with differential from degree p to p+1, the horizontal
totalization sign at any pair (p,q) is ε₁(p,q)=1. -/
private lemma up_ε₁ (x : ℤ × ℤ) :
    ComplexShape.ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) x = 1 := rfl

/-- For two integer cochain shapes, both with differential from degree p to p+1, the vertical
totalization sign at (p,q) is ε₂(p,q)=(-1)^p, where p is the first degree. -/
private lemma up_ε₂ (x : ℤ × ℤ) :
    ComplexShape.ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) x = (x.1).negOnePow := rfl

omit [MonObj A] [ComonObj C] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).obj X)] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).flip.obj X)] [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  X₁.HasTensor₄ObjExt X₂ X₃ X₄] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  X₁.HasGoodTensor₁₂Tensor X₂ X₃] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  X₁.HasGoodTensorTensor₂₃ X₂ X₃] in
/-- Over a commutative ring R, let C,A be integer cochain complexes of R-modules. Assume all graded
tensor coproducts exist, tensoring preserves zero on both sides, tensoring commutes with the
coproducts used for reassociation, and fourfold summand inclusions determine maps. For
homogeneous f of degree m and g of degree n, their tensor has degree m+n and acts on C_p⊗C_q by
(-1)^{np}(f_p⊗g_q). For r+m+n+1=s, the component (C⊗C)_r→(A⊗A)_s of δ(f⊗g) is the component of
(δf)⊗g plus (-1)^m times that of f⊗(δg). The degrees (m+1)+n and m+(n+1) are identified with
m+n+1. -/
private theorem tensorCochain_δ_v {m n : ℤ} (f : HomComplex.Cochain C A m)
    (g : HomComplex.Cochain C A n) (r s : ℤ) (hrs : r + (m + n + 1) = s) :
    (HomComplex.δ (m + n) (m + n + 1) (tensorCochain f g)).v r s hrs =
      (tensorCochain (HomComplex.δ m (m + 1) f) g).v r s (by omega) +
        m.negOnePow •
          (tensorCochain f (HomComplex.δ n (n + 1) g)).v r s (by omega) := by
  simpa only [tensorCochain_eq_tensor] using
    HomComplex.Cochain.tensor_δ_v f g r s hrs

/-- Let R be a commutative ring, C a dg R-coalgebra and A a dg R-algebra, both integer cochain
complexes. Assume all graded tensor coproducts exist, tensoring preserves zero on both sides,
tensoring commutes with the coproducts used for reassociation, and fourfold summand inclusions
determine maps. For |f|=m and |g|=n, convolution f⋆g=μ_A(f⊗g)Δ_C satisfies δ(f⋆g)=(δf)⋆g+(-1)^m
f⋆(δg). Both convolution terms on the right are composites through Δ_C and μ_A, identified in
degree m+n+1 from degrees (m+1)+n and m+(n+1). The tensor sign is (-1)^{np} on left input degree
p. -/
theorem conv_leibniz {m n : ℤ} (f : HomComplex.Cochain C A m)
    (g : HomComplex.Cochain C A n) :
    HomComplex.δ (m + n) (m + n + 1) (conv f g) =
      (((HomComplex.Cochain.ofHom (ComonObj.comul (X := C))).comp
        (tensorCochain (HomComplex.δ m (m + 1) f) g)
        (by omega : (0 : ℤ) + (m + 1 + n) = m + n + 1)).comp
        (HomComplex.Cochain.ofHom (MonObj.mul (X := A)))
        (by omega : (m + n + 1) + 0 = m + n + 1)) +
      m.negOnePow • ((((HomComplex.Cochain.ofHom (ComonObj.comul (X := C))).comp
        (tensorCochain f (HomComplex.δ n (n + 1) g))
        (by omega : (0 : ℤ) + (m + (n + 1)) = m + n + 1)).comp
        (HomComplex.Cochain.ofHom (MonObj.mul (X := A)))
        (by omega : (m + n + 1) + 0 = m + n + 1))) := by
  unfold conv
  rw [HomComplex.δ_comp (n₁ := m + n) (n₂ := 0) (n₁₂ := m + n) _ _
    (add_zero (m + n)) (m + n + 1) 1 (m + n + 1) rfl rfl (zero_add 1)]
  simp only [HomComplex.δ_ofHom, HomComplex.Cochain.comp_zero, zero_add,
    Int.negOnePow_zero, one_smul]
  rw [HomComplex.δ_comp (n₁ := 0) (n₂ := m + n) (n₁₂ := m + n) _ _
    (zero_add (m + n)) 1 (m + n + 1) (m + n + 1) rfl (zero_add 1) rfl]
  simp only [HomComplex.δ_ofHom, HomComplex.Cochain.zero_comp, smul_zero,
    add_zero]
  apply HomComplex.Cochain.ext
  intro r s hrs
  rw [HomComplex.Cochain.comp_v _ _ _ r s s (by omega) (add_zero s),
    HomComplex.Cochain.comp_v _ _ _ r r s (add_zero r) hrs]
  rw [tensorCochain_δ_v f g r s hrs]
  simp only [HomComplex.Cochain.add_v, HomComplex.Cochain.units_smul_v]
  rw [HomComplex.Cochain.comp_v _ _ _ r s s (by omega) (add_zero s),
    HomComplex.Cochain.comp_v _ _ _ r r s (add_zero r) (by omega),
    HomComplex.Cochain.comp_v _ _ _ r s s (by omega) (add_zero s),
    HomComplex.Cochain.comp_v _ _ _ r r s (add_zero r) (by omega)]
  simp only [tensorCochain_v, HomComplex.Cochain.ofHom_v,
    Preadditive.comp_add, Preadditive.add_comp,
    Linear.comp_units_smul, Linear.units_smul_comp]

omit [MonObj A] [ComonObj C] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).obj X)] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).flip.obj X)] [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  X₁.HasTensor₄ObjExt X₂ X₃ X₄] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  X₁.HasGoodTensor₁₂Tensor X₂ X₃] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  X₁.HasGoodTensorTensor₂₃ X₂ X₃] in
/-- Over a commutative ring R, let C,A be integer cochain complexes of R-modules. Assume all graded
tensor coproducts exist, tensoring preserves zero on both sides, tensoring commutes with the
coproducts used for reassociation, and fourfold summand inclusions determine maps. For f₁,f₂:C→A
of degree m and g:C→A of degree n, (f₁+f₂)⊗g=f₁⊗g+f₂⊗g as degree-(m+n) cochains C⊗C→A⊗A. Each
(p,q)-component uses (-1)^{np}. -/
private theorem tensorCochain_add_left {m n : ℤ}
    (f₁ f₂ : HomComplex.Cochain C A m) (g : HomComplex.Cochain C A n) :
    tensorCochain (f₁ + f₂) g = tensorCochain f₁ g + tensorCochain f₂ g := by
  apply HomComplex.Cochain.ext
  intro r s hrs
  rw [tensorCochain_v, HomComplex.Cochain.add_v, tensorCochain_v, tensorCochain_v]
  apply HomologicalComplex.mapBifunctor.hom_ext (c := ComplexShape.up ℤ)
  intro i₁ i₂ hh
  simp only [HomologicalComplex.ι_mapBifunctorDesc, Preadditive.comp_add,
    convSummand, HomComplex.Cochain.add_v, MonoidalPreadditive.add_tensor,
    smul_add, Preadditive.add_comp]

omit [MonObj A] [ComonObj C] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).obj X)] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).flip.obj X)] [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  X₁.HasTensor₄ObjExt X₂ X₃ X₄] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  X₁.HasGoodTensor₁₂Tensor X₂ X₃] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  X₁.HasGoodTensorTensor₂₃ X₂ X₃] in
/-- Over a commutative ring R, let C,A be integer cochain complexes of R-modules. Assume all graded
tensor coproducts exist, tensoring preserves zero on both sides, tensoring commutes with the
coproducts used for reassociation, and fourfold summand inclusions determine maps. For f:C→A of
degree m and g₁,g₂:C→A of degree n, f⊗(g₁+g₂)=f⊗g₁+f⊗g₂ as degree-(m+n) cochains C⊗C→A⊗A. Each
(p,q)-component uses (-1)^{np}. -/
private theorem tensorCochain_add_right {m n : ℤ}
    (f : HomComplex.Cochain C A m) (g₁ g₂ : HomComplex.Cochain C A n) :
    tensorCochain f (g₁ + g₂) = tensorCochain f g₁ + tensorCochain f g₂ := by
  apply HomComplex.Cochain.ext
  intro r s hrs
  rw [tensorCochain_v, HomComplex.Cochain.add_v, tensorCochain_v, tensorCochain_v]
  apply HomologicalComplex.mapBifunctor.hom_ext (c := ComplexShape.up ℤ)
  intro i₁ i₂ hh
  simp only [HomologicalComplex.ι_mapBifunctorDesc, Preadditive.comp_add,
    convSummand, HomComplex.Cochain.add_v, MonoidalPreadditive.tensor_add,
    smul_add, Preadditive.add_comp]

omit [MonObj A] [ComonObj C] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).obj X)] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).flip.obj X)] [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  X₁.HasTensor₄ObjExt X₂ X₃ X₄] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  X₁.HasGoodTensor₁₂Tensor X₂ X₃] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  X₁.HasGoodTensorTensor₂₃ X₂ X₃] in
/-- Over a commutative ring R, let C,A be integer cochain complexes of R-modules. Assume all graded
tensor coproducts exist, tensoring preserves zero on both sides, tensoring commutes with the
coproducts used for reassociation, and fourfold summand inclusions determine maps. For |f|=m,
|g|=n and k∈ℤˣ, (k•f)⊗g=k•(f⊗g) in degree m+n. Tensoring uses (-1)^{np} on a left input degree
p, which commutes with k. -/
private theorem tensorCochain_smul_left {m n : ℤ} (k : ℤˣ)
    (f : HomComplex.Cochain C A m) (g : HomComplex.Cochain C A n) :
    tensorCochain (k • f) g = k • tensorCochain f g := by
  apply HomComplex.Cochain.ext
  intro r s hrs
  rw [tensorCochain_v, HomComplex.Cochain.units_smul_v, tensorCochain_v]
  apply HomologicalComplex.mapBifunctor.hom_ext (c := ComplexShape.up ℤ)
  intro i₁ i₂ hh
  have hcomm : ∀ (Z : (C.X i₁ ⊗ C.X i₂) ⟶ (HomologicalComplex.tensorObj A A).X s),
      (n * i₁).negOnePow • (k • Z) = k • ((n * i₁).negOnePow • Z) := by
    intro Z
    rw [smul_smul, smul_smul, mul_comm ((n * i₁).negOnePow) k]
  simp only [HomologicalComplex.ι_mapBifunctorDesc, convSummand,
    HomComplex.Cochain.units_smul_v, tensorHom_units_smul_left,
    Linear.units_smul_comp, Linear.comp_units_smul, hcomm]

omit [MonObj A] [ComonObj C] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).obj X)] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).flip.obj X)] [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  X₁.HasTensor₄ObjExt X₂ X₃ X₄] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  X₁.HasGoodTensor₁₂Tensor X₂ X₃] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  X₁.HasGoodTensorTensor₂₃ X₂ X₃] in
/-- Over a commutative ring R, let C,A be integer cochain complexes of R-modules. Assume all graded
tensor coproducts exist, tensoring preserves zero on both sides, tensoring commutes with the
coproducts used for reassociation, and fourfold summand inclusions determine maps. For |f|=m,
|g|=n and k∈ℤˣ, f⊗(k•g)=k•(f⊗g) in degree m+n. Tensoring uses (-1)^{np} on a left input degree
p, which commutes with k. -/
private theorem tensorCochain_smul_right {m n : ℤ} (k : ℤˣ)
    (f : HomComplex.Cochain C A m) (g : HomComplex.Cochain C A n) :
    tensorCochain f (k • g) = k • tensorCochain f g := by
  apply HomComplex.Cochain.ext
  intro r s hrs
  rw [tensorCochain_v, HomComplex.Cochain.units_smul_v, tensorCochain_v]
  apply HomologicalComplex.mapBifunctor.hom_ext (c := ComplexShape.up ℤ)
  intro i₁ i₂ hh
  have hcomm : ∀ (Z : (C.X i₁ ⊗ C.X i₂) ⟶ (HomologicalComplex.tensorObj A A).X s),
      (n * i₁).negOnePow • (k • Z) = k • ((n * i₁).negOnePow • Z) := by
    intro Z
    rw [smul_smul, smul_smul, mul_comm ((n * i₁).negOnePow) k]
  simp only [HomologicalComplex.ι_mapBifunctorDesc, convSummand,
    HomComplex.Cochain.units_smul_v, tensorHom_units_smul_right,
    Linear.units_smul_comp, Linear.comp_units_smul, hcomm]

/-- Let R be a commutative ring, C a dg R-coalgebra and A a dg R-algebra, both integer cochain
complexes. Assume all graded tensor coproducts exist, tensoring preserves zero on both sides,
tensoring commutes with the coproducts used for reassociation, and fourfold summand inclusions
determine maps. For f₁,f₂:C→A of degree m and g:C→A of degree n, (f₁+f₂)⋆g=f₁⋆g+f₂⋆g in degree
m+n, where f⋆g=μ_A(f⊗g)Δ_C and the tensor has sign (-1)^{np} on left input degree p. -/
theorem conv_add_left {m n : ℤ} (f₁ f₂ : HomComplex.Cochain C A m)
    (g : HomComplex.Cochain C A n) :
    conv (f₁ + f₂) g = conv f₁ g + conv f₂ g := by
  unfold conv
  rw [tensorCochain_add_left, HomComplex.Cochain.comp_add,
    HomComplex.Cochain.add_comp]

/-- Let R be a commutative ring, C a dg R-coalgebra and A a dg R-algebra, both integer cochain
complexes. Assume all graded tensor coproducts exist, tensoring preserves zero on both sides,
tensoring commutes with the coproducts used for reassociation, and fourfold summand inclusions
determine maps. For f:C→A of degree m and g₁,g₂:C→A of degree n, f⋆(g₁+g₂)=f⋆g₁+f⋆g₂ in degree
m+n, where f⋆g=μ_A(f⊗g)Δ_C and the tensor has sign (-1)^{np} on left input degree p. -/
theorem conv_add_right {m n : ℤ} (f : HomComplex.Cochain C A m)
    (g₁ g₂ : HomComplex.Cochain C A n) :
    conv f (g₁ + g₂) = conv f g₁ + conv f g₂ := by
  unfold conv
  rw [tensorCochain_add_right, HomComplex.Cochain.comp_add,
    HomComplex.Cochain.add_comp]

/-- Let R be a commutative ring, C a dg R-coalgebra and A a dg R-algebra, both integer cochain
complexes. Assume all graded tensor coproducts exist, tensoring preserves zero on both sides,
tensoring commutes with the coproducts used for reassociation, and fourfold summand inclusions
determine maps. For |f|=m, |g|=n and k∈ℤˣ, (k•f)⋆g=k•(f⋆g) in degree m+n, where ⋆=μ_A(-⊗-)Δ_C.
The tensor contributes (-1)^{np} on left input degree p. -/
theorem conv_smul_left {m n : ℤ} (k : ℤˣ)
    (f : HomComplex.Cochain C A m) (g : HomComplex.Cochain C A n) :
    conv (k • f) g = k • conv f g := by
  unfold conv
  rw [tensorCochain_smul_left, HomComplex.Cochain.comp_units_smul,
    HomComplex.Cochain.units_smul_comp]

/-- Let R be a commutative ring, C a dg R-coalgebra and A a dg R-algebra, both integer cochain
complexes. Assume all graded tensor coproducts exist, tensoring preserves zero on both sides,
tensoring commutes with the coproducts used for reassociation, and fourfold summand inclusions
determine maps. For |f|=m, |g|=n and k∈ℤˣ, f⋆(k•g)=k•(f⋆g) in degree m+n, where ⋆=μ_A(-⊗-)Δ_C.
The tensor contributes (-1)^{np} on left input degree p. -/
theorem conv_smul_right {m n : ℤ} (k : ℤˣ)
    (f : HomComplex.Cochain C A m) (g : HomComplex.Cochain C A n) :
    conv f (k • g) = k • conv f g := by
  unfold conv
  rw [tensorCochain_smul_right, HomComplex.Cochain.comp_units_smul,
    HomComplex.Cochain.units_smul_comp]

end CochainComplex
