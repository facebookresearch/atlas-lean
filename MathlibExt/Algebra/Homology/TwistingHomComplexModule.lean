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

public import MathlibExt.Algebra.Homology.TwistingHomComplex

/-!
# The R-linear twisting Hom complex

For a dg coalgebra C and dg algebra A over a commutative ring R, tensoring morphisms and
tensoring homogeneous cochains are R-bilinear. Hence graded convolution is R-bilinear, and
D_τ(f)=δf+τ⋆f-(-1)^n f⋆τ is R-linear.

For Maurer–Cartan τ, these maps give an integer cochain complex of R-modules with degree-n term
Hom^n(C,A), next-degree differential D_τ, and zero outside n+1=m. Its coefficient groups and
differential values are those of the additive twisting Hom complex.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory TensorProduct

namespace CochainComplex

variable {R : Type*} [CommRing R]
variable {C A : CochainComplex (ModuleCat R) ℤ}

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

omit [MonObj A] [ComonObj C] [∀ (X₁ X₂ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasTensor X₁ X₂] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).obj X)] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).flip.obj X)] [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃] in
/-- Let R be commutative and f:X₁→Y₁,g:X₂→Y₂ be R-module morphisms. For λ∈R, (λ•f)⊗g=λ•(f⊗g) as maps
X₁⊗X₂→Y₁⊗Y₂. -/
private theorem tensorHom_smul_left {X₁ Y₁ X₂ Y₂ : ModuleCat R} (k : R)
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : ((k • f) ⊗ₘ g) = k • (f ⊗ₘ g) := by
  apply ModuleCat.hom_ext
  simp only [ModuleCat.hom_tensorHom, ModuleCat.hom_smul,
    TensorProduct.map_smul_left]

omit [MonObj A] [ComonObj C] [∀ (X₁ X₂ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasTensor X₁ X₂] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).obj X)] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).flip.obj X)] [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃] in
/-- Let R be commutative and f:X₁→Y₁,g:X₂→Y₂ be R-module morphisms. For λ∈R, f⊗(λ•g)=λ•(f⊗g). -/
private theorem tensorHom_smul_right {X₁ Y₁ X₂ Y₂ : ModuleCat R} (k : R)
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : (f ⊗ₘ (k • g)) = k • (f ⊗ₘ g) := by
  apply ModuleCat.hom_ext
  simp only [ModuleCat.hom_tensorHom, ModuleCat.hom_smul,
    TensorProduct.map_smul_right]

omit [MonObj A] [ComonObj C] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).obj X)] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).flip.obj X)] [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃] in
/-- Let R be commutative, C,A integer cochain R-module complexes with their tensor products, and
f:C→A,g:C→A homogeneous of degrees m,n. For λ∈R, tensor(λ•f,g)=λ•tensor(f,g) in degree m+n. -/
private theorem tensorCochain_smul_left {m n : ℤ} (k : R)
    (f : HomComplex.Cochain C A m) (g : HomComplex.Cochain C A n) :
    tensorCochain (k • f) g = k • tensorCochain f g := by
  apply HomComplex.Cochain.ext
  intro r s hrs
  rw [tensorCochain_v, HomComplex.Cochain.smul_v, tensorCochain_v]
  apply HomologicalComplex.mapBifunctor.hom_ext (c := ComplexShape.up ℤ)
  intro i₁ i₂ hh
  have hcomm : ∀ (Z : (C.X i₁ ⊗ C.X i₂) ⟶ (HomologicalComplex.tensorObj A A).X s),
      (n * i₁).negOnePow • (k • Z) = k • ((n * i₁).negOnePow • Z) := by
    intro Z
    exact smul_comm _ _ _
  simp only [HomologicalComplex.ι_mapBifunctorDesc, convSummand,
    HomComplex.Cochain.smul_v, tensorHom_smul_left,
    Linear.smul_comp, Linear.comp_smul, hcomm]

omit [MonObj A] [ComonObj C] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).obj X)] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).flip.obj X)] [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃] in
/-- Let R be commutative and f,g homogeneous cochains C→A in degrees m,n of integer R-module
complexes with tensor products. Then tensor(f,λ•g)=λ•tensor(f,g) for every λ∈R. -/
private theorem tensorCochain_smul_right {m n : ℤ} (k : R)
    (f : HomComplex.Cochain C A m) (g : HomComplex.Cochain C A n) :
    tensorCochain f (k • g) = k • tensorCochain f g := by
  apply HomComplex.Cochain.ext
  intro r s hrs
  rw [tensorCochain_v, HomComplex.Cochain.smul_v, tensorCochain_v]
  apply HomologicalComplex.mapBifunctor.hom_ext (c := ComplexShape.up ℤ)
  intro i₁ i₂ hh
  have hcomm : ∀ (Z : (C.X i₁ ⊗ C.X i₂) ⟶ (HomologicalComplex.tensorObj A A).X s),
      (n * i₁).negOnePow • (k • Z) = k • ((n * i₁).negOnePow • Z) := by
    intro Z
    exact smul_comm _ _ _
  simp only [HomologicalComplex.ι_mapBifunctorDesc, convSummand,
    HomComplex.Cochain.smul_v, tensorHom_smul_right,
    Linear.smul_comp, Linear.comp_smul, hcomm]

/-- Let R be commutative, C a dg coalgebra and A a dg algebra in a common integer cochain R-module
category. Use all required graded tensor coproducts, zero-object preservation in both variables,
the two triple-coproduct conditions, and fourfold tensor extensionality. Write Hom^n(C,A) for
the degree-n cochains and f⋆g=μ_A(f⊗g)Δ_C for convolution. For f,g of degrees m,n and λ∈R,
(λ•f)⋆g=λ•(f⋆g) in degree m+n. -/
private theorem conv_smul_left_R {m n : ℤ} (k : R)
    (f : HomComplex.Cochain C A m) (g : HomComplex.Cochain C A n) :
    conv (k • f) g = k • conv f g := by
  unfold conv
  rw [tensorCochain_smul_left, HomComplex.Cochain.comp_smul,
    HomComplex.Cochain.smul_comp]

/-- Let R be commutative, C a dg coalgebra and A a dg algebra in a common integer cochain R-module
category. Use all required graded tensor coproducts, zero-object preservation in both variables,
the two triple-coproduct conditions, and fourfold tensor extensionality. Write Hom^n(C,A) for
the degree-n cochains and f⋆g=μ_A(f⊗g)Δ_C for convolution. For f,g of degrees m,n and λ∈R,
f⋆(λ•g)=λ•(f⋆g). -/
private theorem conv_smul_right_R {m n : ℤ} (k : R)
    (f : HomComplex.Cochain C A m) (g : HomComplex.Cochain C A n) :
    conv f (k • g) = k • conv f g := by
  unfold conv
  rw [tensorCochain_smul_right, HomComplex.Cochain.comp_smul,
    HomComplex.Cochain.smul_comp]

/-- Let R be commutative, C a dg coalgebra and A a dg algebra in a common integer cochain R-module
category. Use all required graded tensor coproducts, zero-object preservation in both variables,
the two triple-coproduct conditions, and fourfold tensor extensionality. Write Hom^n(C,A) for
the degree-n cochains and f⋆g=μ_A(f⊗g)Δ_C for convolution. For τ of degree one and f of degree
n, put D_τ(f)=δf+τ⋆f-(-1)^n f⋆τ, with the left product transported from 1+n to n+1. Here
δf=d_Af+(-1)^{n+1}fd_C and ⋆ has Koszul factor (-1)^{|g|p}. For λ∈R and f∈Hom^n(C,A),
D_τ(λ•f)=λ•D_τ(f), for any degree-one τ. -/
theorem twistedDifferential_smul {n : ℤ} (k : R)
    (τ : HomComplex.Cochain C A 1) (f : HomComplex.Cochain C A n) :
    twistedDifferential τ (k • f) = k • twistedDifferential τ f := by
  unfold twistedDifferential
  rw [HomComplex.δ_smul n (n + 1) k f, conv_smul_right_R k τ f, conv_smul_left_R k f τ]
  have hcast_smul : ∀ {a b : ℤ} (hab : a = b)
      (x : HomComplex.Cochain C A a),
      cast (congrArg (HomComplex.Cochain C A) hab) (k • x) =
        k • cast (congrArg (HomComplex.Cochain C A) hab) x := by
    intro a b hab x
    cases hab
    rfl
  have hcommC : ∀ (X : HomComplex.Cochain C A (n + 1)),
      n.negOnePow • (k • X) = k • (n.negOnePow • X) := by
    intro X
    exact smul_comm _ _ _
  rw [hcast_smul (add_comm (1 : ℤ) n) (conv τ f), smul_sub, smul_add, hcommC]

/-- Let R be commutative, C a dg coalgebra and A a dg algebra in a common integer cochain R-module
category. Use all required graded tensor coproducts, zero-object preservation in both variables,
the two triple-coproduct conditions, and fourfold tensor extensionality. Write Hom^n(C,A) for
the degree-n cochains and f⋆g=μ_A(f⊗g)Δ_C for convolution. For τ of degree one and f of degree
n, put D_τ(f)=δf+τ⋆f-(-1)^n f⋆τ, with the left product transported from 1+n to n+1. Here
δf=d_Af+(-1)^{n+1}fd_C and ⋆ has Koszul factor (-1)^{|g|p}. The map Hom^n(C,A)→_R Hom^m(C,A) is
D_τ transported through n+1=m when this equality holds, and zero otherwise. -/
noncomputable def twistedDifferentialLinear
    (τ : HomComplex.Cochain C A 1) (n m : ℤ) :
    HomComplex.Cochain C A n →ₗ[R] HomComplex.Cochain C A m where
  toFun f :=
    if h : n + 1 = m then
      cast (congrArg (HomComplex.Cochain C A) h) (twistedDifferential τ f)
    else 0
  map_add' := by
    intro f g
    by_cases h : n + 1 = m
    · simp only [dite_eq_left h, twistedDifferential_add]
      cases h
      rfl
    · simp only [dite_eq_right h, add_zero]
  map_smul' := by
    intro k f
    by_cases h : n + 1 = m
    · simp only [dite_eq_left h, twistedDifferential_smul]
      cases h
      rfl
    · simp only [dite_eq_right h, smul_zero]

/-- Let R be commutative, C a dg coalgebra and A a dg algebra in a common integer cochain R-module
category. Use all required graded tensor coproducts, zero-object preservation in both variables,
the two triple-coproduct conditions, and fourfold tensor extensionality. Write Hom^n(C,A) for
the degree-n cochains and f⋆g=μ_A(f⊗g)Δ_C for convolution. For τ of degree one and f of degree
n, put D_τ(f)=δf+τ⋆f-(-1)^n f⋆τ, with the left product transported from 1+n to n+1. Here
δf=d_Af+(-1)^{n+1}fd_C and ⋆ has Koszul factor (-1)^{|g|p}. For δτ+τ⋆τ=0, the integer cochain
complex in R-modules has term Hom^n(C,A), differential D_τ at n→n+1, and zero elsewhere. Its
differentials square to zero. -/
noncomputable def twistedHomComplexModule
    (τ : HomComplex.Cochain C A 1) (hMC : IsMaurerCartan τ) :
    CochainComplex (ModuleCat R) ℤ where
  X n := ModuleCat.of R (HomComplex.Cochain C A n)
  d n m := ModuleCat.ofHom (twistedDifferentialLinear τ n m)
  shape n m hnm := by
    have h : ¬ n + 1 = m := by simpa [ComplexShape.up_Rel] using hnm
    ext f
    simp [twistedDifferentialLinear, dite_eq_right h]
  d_comp_d' n m k hij hjk := by
    have h1 : n + 1 = m := by simpa [ComplexShape.up_Rel] using hij
    have h2 : m + 1 = k := by simpa [ComplexShape.up_Rel] using hjk
    ext f p q hpq x
    simp only [twistedDifferentialLinear, dite_eq_left h1, dite_eq_left h2]
    cases h1
    cases h2
    rw [← ModuleCat.ofHom_comp, ModuleCat.ofHom_apply,
      LinearMap.comp_apply]
    have hSq := twistedDifferential_sq_zero τ f hMC
    have hW := congrArg
      (fun g : HomComplex.Cochain C A ((n + 1) + 1) =>
        ModuleCat.Hom.hom (g.v p q hpq) x) hSq
    exact hW

/-- Let R be commutative, C a dg coalgebra and A a dg algebra in a common integer cochain R-module
category. Use all required graded tensor coproducts, zero-object preservation in both variables,
the two triple-coproduct conditions, and fourfold tensor extensionality. Write Hom^n(C,A) for
the degree-n cochains and f⋆g=μ_A(f⊗g)Δ_C for convolution. For Maurer–Cartan τ and n∈ℤ, its
degree-n object is the R-module Hom^n(C,A), with the pointwise scalar action on cochain
components. -/
@[simp]
theorem twistedHomComplexModule_X (τ : HomComplex.Cochain C A 1)
    (hMC : IsMaurerCartan τ) (n : ℤ) :
    (twistedHomComplexModule τ hMC).X n =
      ModuleCat.of R (HomComplex.Cochain C A n) :=
  rfl

/-- Let R be commutative, C a dg coalgebra and A a dg algebra in a common integer cochain R-module
category. Use all required graded tensor coproducts, zero-object preservation in both variables,
the two triple-coproduct conditions, and fourfold tensor extensionality. Write Hom^n(C,A) for
the degree-n cochains and f⋆g=μ_A(f⊗g)Δ_C for convolution. For τ of degree one and f of degree
n, put D_τ(f)=δf+τ⋆f-(-1)^n f⋆τ, with the left product transported from 1+n to n+1. Here
δf=d_Af+(-1)^{n+1}fd_C and ⋆ has Koszul factor (-1)^{|g|p}. For Maurer–Cartan τ and
f∈Hom^n(C,A), its differential to m equals D_τ(f) under n+1=m, and is zero for n+1≠m. -/
@[simp]
theorem twistedHomComplexModule_d_apply (τ : HomComplex.Cochain C A 1)
    (hMC : IsMaurerCartan τ) (n m : ℤ)
    (f : HomComplex.Cochain C A n) :
    ((twistedHomComplexModule τ hMC).d n m) f =
      (if h : n + 1 = m then
        cast (congrArg (HomComplex.Cochain C A) h)
          (twistedDifferential τ f)
      else 0) :=
  rfl

end CochainComplex
