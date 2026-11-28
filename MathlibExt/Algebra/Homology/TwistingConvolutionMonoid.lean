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

public import MathlibExt.Algebra.Homology.TwistingConvolutionLaws
public import MathlibExt.Algebra.Homology.TensorUnitor

/-!
# Associativity and units of graded convolution

Let R be a commutative ring, C a dg R-coalgebra and A a dg R-algebra, both integer cochain
complexes. Assume all graded tensor coproducts exist, tensoring preserves zero on both sides,
tensoring commutes with the coproducts used for reassociation, and fourfold summand inclusions
determine maps.

For homogeneous cochains f,g:C→A of degrees m,n, convolution is f⋆g=μ_A(f⊗g)Δ_C. On a source
summand of degrees p,q, the tensor has Koszul factor (-1)^{np}. Convolution satisfies
(f⋆g)⋆h=f⋆(g⋆h) after identifying the two associations of the integer total degree.

The degree-zero unit is e=ε_C≫η_A, using the coalgebra counit C→I and algebra unit I→A. The
complex I is concentrated in degree zero, hence e_i=0 for i≠0. The tensors e⊗f and f⊗e are
determined by their (0,r) and (r,0) summands. The counit and algebra unit equations reduce these
summands through the corresponding complex unitors, giving e⋆f=f and f⋆e=f after identifying
0+n=n and n+0=n.

Reference: J.-L. Loday and B. Vallette, Algebraic Operads, Grundlehren 346 (2012).
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

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

/-- Let R be a commutative ring, C a dg R-coalgebra and A a dg R-algebra, both integer cochain
complexes. Assume all graded tensor coproducts exist, tensoring preserves zero on both sides,
tensoring commutes with the coproducts used for reassociation, and fourfold summand inclusions
determine maps. For cochains f:C→A and g:C→A of integer degrees m,n, f⋆g is Δ_C≫(f⊗g)≫μ_A as a
degree-(m+n) cochain C→A. The tensor on input degrees p,q contributes (-1)^{np}. -/
private theorem conv_eq {m n : ℤ} (f : HomComplex.Cochain C A m)
    (g : HomComplex.Cochain C A n) :
    conv f g =
    ((HomComplex.Cochain.ofHom (ComonObj.comul (X := C))).comp
      (HomComplex.Cochain.tensor f g) (zero_add (m + n))).comp
    (HomComplex.Cochain.ofHom (MonObj.mul (X := A))) (add_zero (m + n)) := by
  unfold conv
  rw [tensorCochain_eq_tensor]

/-- Let R be a commutative ring, C a dg R-coalgebra and A a dg R-algebra, both integer cochain
complexes. Assume all graded tensor coproducts exist, tensoring preserves zero on both sides,
tensoring commutes with the coproducts used for reassociation, and fourfold summand inclusions
determine maps. Write e=ε_C≫η_A:C→A for the degree-zero cochain formed from the coalgebra counit
and algebra unit. For every integer i≠0, its component e_i:C_i→A_i is zero, since e factors
through the tensor-unit complex concentrated in degree zero. -/
private theorem convOne_vanish (i : ℤ) (hi : i ≠ 0) :
    (convOne (R := R) (C := C) (A := A)).v i i (by omega) = 0 := by
  unfold convOne
  simp only [HomComplex.Cochain.zero_cochain_comp_v, HomComplex.Cochain.ofHom_v]
  have h0 : IsZero
      ((HomologicalComplex.tensorUnit (ModuleCat R) (ComplexShape.up ℤ)).X i) :=
    HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
      (𝟙_ (ModuleCat R)) i hi
  have hf0 : (ComonObj.counit (X := C)).f i = 0 := h0.eq_of_tgt _ _
  rw [hf0, zero_comp]

/-- Let R be a commutative ring, C a dg R-coalgebra and A a dg R-algebra, both integer cochain
complexes. Assume all graded tensor coproducts exist, tensoring preserves zero on both sides,
tensoring commutes with the coproducts used for reassociation, and fourfold summand inclusions
determine maps. Write e=ε_C≫η_A:C→A for the degree-zero cochain formed from the coalgebra counit
and algebra unit. For integers i,j with i+0=j and i≠0, the C_i→A_j component e_{i,j} is zero. -/
private theorem convOne_vanish_general (i j : ℤ) (hij : i + (0 : ℤ) = j)
    (hi : i ≠ 0) :
    (convOne (R := R) (C := C) (A := A)).v i j hij = 0 := by
  have hj : i = j := by omega
  subst hj
  exact convOne_vanish i hi

/-- Let R be a commutative ring, C a dg R-coalgebra and A a dg R-algebra, both integer cochain
complexes. Assume all graded tensor coproducts exist, tensoring preserves zero on both sides,
tensoring commutes with the coproducts used for reassociation, and fourfold summand inclusions
determine maps. Write e=ε_C≫η_A:C→A for the degree-zero cochain formed from the coalgebra counit
and algebra unit. If f:C→A has integer degree n and p≠0, then (-1)^{np}(e_p⊗f_q)=0 as a map
C_p⊗C_q→A_p⊗A_{q+n}, for every q. -/
private theorem tensor_convOne_summand_vanish {n : ℤ}
    (f : HomComplex.Cochain C A n) (i₁ i₂ : ℤ) (hi₁ : i₁ ≠ 0) :
    (n * i₁).negOnePow •
      ((convOne (R := R) (C := C) (A := A)).v i₁ (i₁ + 0) rfl ⊗ₘ
        f.v i₂ (i₂ + n) rfl) = 0 := by
  have h0 : (convOne (R := R) (C := C) (A := A)).v i₁ (i₁ + 0) rfl = 0 :=
    convOne_vanish_general i₁ (i₁ + 0) rfl hi₁
  rw [h0, MonoidalPreadditive.zero_tensor]
  simp

/-- Let R be a commutative ring, C a dg R-coalgebra and A a dg R-algebra, both integer cochain
complexes. Assume all graded tensor coproducts exist, tensoring preserves zero on both sides,
tensoring commutes with the coproducts used for reassociation, and fourfold summand inclusions
determine maps. Write e=ε_C≫η_A:C→A for the degree-zero cochain formed from the coalgebra counit
and algebra unit. For |f|=n, r+0+n=s, p+q=r and p≠0, ι^C_{p,q,r}≫(e⊗f)_{r,s}=0. Here ι^C
includes C_p⊗C_q in (C⊗C)_r, and (e⊗f)_{r,s} maps to (A⊗A)_s. -/
private theorem tensor_convOne_support_collapse {n : ℤ}
    (f : HomComplex.Cochain C A n) (r s : ℤ) (hrs : r + (0 + n) = s)
    (i₁ i₂ : ℤ) (hij : i₁ + i₂ = r) (hi₁ : i₁ ≠ 0) :
    HomologicalComplex.ιMapBifunctor C C (curriedTensor (ModuleCat R))
        (ComplexShape.up ℤ) i₁ i₂ r hij ≫
      (HomComplex.Cochain.tensor (convOne (R := R) (C := C) (A := A)) f).v
        r s hrs = 0 := by
  rw [HomComplex.Cochain.tensor_v, HomologicalComplex.ι_mapBifunctorDesc]
  dsimp only
  have h0 : (convOne (R := R) (C := C) (A := A)).v i₁ (i₁ + 0) rfl = 0 :=
    convOne_vanish_general i₁ (i₁ + 0) rfl hi₁
  rw [h0, MonoidalPreadditive.zero_tensor]
  simp

/-- Let R be a commutative ring, C a dg R-coalgebra and A a dg R-algebra, both integer cochain
complexes. Assume all graded tensor coproducts exist, tensoring preserves zero on both sides,
tensoring commutes with the coproducts used for reassociation, and fourfold summand inclusions
determine maps. Write e=ε_C≫η_A:C→A for the degree-zero cochain formed from the coalgebra counit
and algebra unit. For |f|=n and r+0+n=s, ι^C_{0,r,r}≫(e⊗f)_{r,s}=(e_0⊗f_r)≫ι^A_{0,r+n,s}; its
sign is (-1)^{n·0}=1. For every p+q=r with p≠0, ι^C_{p,q,r}≫(e⊗f)_{r,s}=0. The inclusions belong
to the respective source C⊗C and target A⊗A degree coproducts. -/
private theorem tensor_convOne_desc_singleton {n : ℤ}
    (f : HomComplex.Cochain C A n) (r s : ℤ) (hrs : r + (0 + n) = s) :
    (HomologicalComplex.ιMapBifunctor C C (curriedTensor (ModuleCat R))
        (ComplexShape.up ℤ) 0 r r (zero_add r) ≫
      (HomComplex.Cochain.tensor (convOne (R := R) (C := C) (A := A)) f).v
        r s hrs =
      (n * 0).negOnePow •
        ((convOne (R := R) (C := C) (A := A)).v 0 (0 + 0) rfl ⊗ₘ
          f.v r (r + n) rfl) ≫
        HomologicalComplex.ιTensorObj A A (0 + 0) (r + n) s (by omega)) ∧
    (∀ (i₁ i₂ : ℤ) (hij : i₁ + i₂ = r) (_hi₁ : i₁ ≠ 0),
      HomologicalComplex.ιMapBifunctor C C (curriedTensor (ModuleCat R))
        (ComplexShape.up ℤ) i₁ i₂ r hij ≫
      (HomComplex.Cochain.tensor (convOne (R := R) (C := C) (A := A)) f).v
        r s hrs = 0) := by
  exact ⟨by rw [HomComplex.Cochain.tensor_v, HomologicalComplex.ι_mapBifunctorDesc],
    fun i₁ i₂ hij hi₁ => tensor_convOne_support_collapse f r s hrs i₁ i₂ hij hi₁⟩

/-- Let R be a commutative ring, C a dg R-coalgebra and A a dg R-algebra, both integer cochain
complexes. Assume all graded tensor coproducts exist, tensoring preserves zero on both sides,
tensoring commutes with the coproducts used for reassociation, and fourfold summand inclusions
determine maps. Write e=ε_C≫η_A:C→A for the degree-zero cochain formed from the coalgebra counit
and algebra unit. If f:C→A has integer degree n and q≠0, then (-1)^{0·p}(f_p⊗e_q)=0 as a map
C_p⊗C_q→A_{p+n}⊗A_q, for every p. -/
private theorem tensor_f_convOne_summand_vanish {n : ℤ}
    (f : HomComplex.Cochain C A n) (i₁ i₂ : ℤ) (hi₂ : i₂ ≠ 0) :
    (0 * i₁).negOnePow •
      (f.v i₁ (i₁ + n) rfl ⊗ₘ
        (convOne (R := R) (C := C) (A := A)).v i₂ (i₂ + 0) rfl) = 0 := by
  have h0 : (convOne (R := R) (C := C) (A := A)).v i₂ (i₂ + 0) rfl = 0 :=
    convOne_vanish_general i₂ (i₂ + 0) rfl hi₂
  rw [h0, MonoidalPreadditive.tensor_zero]
  simp

/-- Let R be a commutative ring, C a dg R-coalgebra and A a dg R-algebra, both integer cochain
complexes. Assume all graded tensor coproducts exist, tensoring preserves zero on both sides,
tensoring commutes with the coproducts used for reassociation, and fourfold summand inclusions
determine maps. Write e=ε_C≫η_A:C→A for the degree-zero cochain formed from the coalgebra counit
and algebra unit. For |f|=n, r+n+0=s, p+q=r and q≠0, ι^C_{p,q,r}≫(f⊗e)_{r,s}=0. Here ι^C
includes C_p⊗C_q in (C⊗C)_r, and (f⊗e)_{r,s} maps to (A⊗A)_s. -/
private theorem tensor_f_convOne_support_collapse {n : ℤ}
    (f : HomComplex.Cochain C A n) (r s : ℤ) (hrs : r + (n + 0) = s)
    (i₁ i₂ : ℤ) (hij : i₁ + i₂ = r) (hi₂ : i₂ ≠ 0) :
    HomologicalComplex.ιMapBifunctor C C (curriedTensor (ModuleCat R))
        (ComplexShape.up ℤ) i₁ i₂ r hij ≫
      (HomComplex.Cochain.tensor f (convOne (R := R) (C := C) (A := A))).v
        r s hrs = 0 := by
  rw [HomComplex.Cochain.tensor_v, HomologicalComplex.ι_mapBifunctorDesc]
  dsimp only
  have h0 : (convOne (R := R) (C := C) (A := A)).v i₂ (i₂ + 0) rfl = 0 :=
    convOne_vanish_general i₂ (i₂ + 0) rfl hi₂
  rw [h0, MonoidalPreadditive.tensor_zero]
  simp

/-- Let R be a commutative ring, C a dg R-coalgebra and A a dg R-algebra, both integer cochain
complexes. Assume all graded tensor coproducts exist, tensoring preserves zero on both sides,
tensoring commutes with the coproducts used for reassociation, and fourfold summand inclusions
determine maps. Write e=ε_C≫η_A:C→A for the degree-zero cochain formed from the coalgebra counit
and algebra unit. For |f|=n and r+n+0=s, ι^C_{r,0,r}≫(f⊗e)_{r,s}=(f_r⊗e_0)≫ι^A_{r+n,0,s}; its
sign is (-1)^{0·r}=1. For every p+q=r with q≠0, ι^C_{p,q,r}≫(f⊗e)_{r,s}=0. The inclusions belong
to the respective source C⊗C and target A⊗A degree coproducts. -/
private theorem tensor_f_convOne_desc_singleton {n : ℤ}
    (f : HomComplex.Cochain C A n) (r s : ℤ) (hrs : r + (n + 0) = s) :
    (HomologicalComplex.ιMapBifunctor C C (curriedTensor (ModuleCat R))
        (ComplexShape.up ℤ) r 0 r (add_zero r) ≫
      (HomComplex.Cochain.tensor f (convOne (R := R) (C := C) (A := A))).v
        r s hrs =
      (0 * r).negOnePow •
        (f.v r (r + n) rfl ⊗ₘ
          (convOne (R := R) (C := C) (A := A)).v 0 (0 + 0) rfl) ≫
        HomologicalComplex.ιTensorObj A A (r + n) (0 + 0) s (by omega)) ∧
    (∀ (i₁ i₂ : ℤ) (hij : i₁ + i₂ = r) (_hi₂ : i₂ ≠ 0),
      HomologicalComplex.ιMapBifunctor C C (curriedTensor (ModuleCat R))
        (ComplexShape.up ℤ) i₁ i₂ r hij ≫
      (HomComplex.Cochain.tensor f (convOne (R := R) (C := C) (A := A))).v
        r s hrs = 0) := by
  exact ⟨by rw [HomComplex.Cochain.tensor_v, HomologicalComplex.ι_mapBifunctorDesc],
    fun i₁ i₂ hij hi₂ => tensor_f_convOne_support_collapse f r s hrs i₁ i₂ hij hi₂⟩

omit [∀ (X₁ X₂ : GradedObject ℤ (ModuleCat R)), GradedObject.HasTensor X₁ X₂] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).obj X)] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).flip.obj X)] [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  X₁.HasTensor₄ObjExt X₂ X₃ X₄] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  X₁.HasGoodTensor₁₂Tensor X₂ X₃] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  X₁.HasGoodTensorTensor₂₃ X₂ X₃] [MonObj A] [ComonObj C] in
/-- Over a commutative ring R, let C,A be integer cochain complexes and z:C→A a cochain of degree a.
If a=b and r+b=s, the component of z regarded as a degree-b cochain is its C_r→A_s component
with r+a=s. This is the canonical transport along the equality of integer degrees. -/
private theorem cochain_cast_v {a b : ℤ} (hab : a = b)
    (z : HomComplex.Cochain C A a) (r s : ℤ) (hrs : r + b = s) :
    (cast (congrArg (HomComplex.Cochain C A) hab) z).v r s hrs =
      z.v r s (by omega) := by
  subst hab
  rfl

/-- Let R be a commutative ring, C a dg R-coalgebra and A a dg R-algebra, both integer cochain
complexes. Assume all graded tensor coproducts exist, tensoring preserves zero on both sides,
tensoring commutes with the coproducts used for reassociation, and fourfold summand inclusions
determine maps. Write e=ε_C≫η_A:C→A for the degree-zero cochain formed from the coalgebra counit
and algebra unit. For |f|=n and r+n+0=s, the following identities hold:
(Δ_C≫(id_C⊗ε_C))_r=(ρ_C⁻¹)_r and ((id_A⊗η_A)≫μ_A)_s=(ρ_A)_s; (id_C⊗id_C)≫(f⊗e)=(id_C≫f)⊗(id_C≫e)
as cochains. With I the tensor-unit complex and σ:I_0≅R,
(ρ_C⁻¹)_r=ρ_{C_r}⁻¹≫(id_{C_r}⊗σ⁻¹)≫ι^{C,I}_{r,0,r}. Identifying n+0 with n leaves the C_r→A_s
component of f⋆e unchanged. The unitors have directions ρ_X:X⊗I→X. -/
private theorem conv_one_right_transport {n : ℤ}
    (f : HomComplex.Cochain C A n) (r s : ℤ) (hrs : r + (n + 0) = s) :
    ((((HomComplex.Cochain.ofHom (ComonObj.comul (X := C))).comp
      (HomComplex.Cochain.ofHom (C ◁ ComonObj.counit (X := C)))
      (zero_add 0))).v r r (add_zero r) =
      (HomComplex.Cochain.ofHom (ρ_ C).inv).v r r (add_zero r)) ∧
    ((((HomComplex.Cochain.ofHom (A ◁ MonObj.one (X := A)))).comp
      (HomComplex.Cochain.ofHom (MonObj.mul (X := A)))
      (zero_add 0))).v s s (add_zero s) =
      (HomComplex.Cochain.ofHom (ρ_ A).hom).v s s (add_zero s) ∧
    ((HomComplex.Cochain.ofHom
      (HomologicalComplex.tensorHom (𝟙 C) (𝟙 C))).comp
      (HomComplex.Cochain.tensor f (convOne (R := R) (C := C) (A := A)))
      (zero_add (n + 0))) =
      HomComplex.Cochain.tensor
        ((HomComplex.Cochain.ofHom (𝟙 C)).comp f (zero_add n))
        ((HomComplex.Cochain.ofHom (𝟙 C)).comp
          (convOne (R := R) (C := C) (A := A)) (zero_add 0)) ∧
    ((HomologicalComplex.rightUnitor' C).inv r =
      (ρ_ (C.X r)).inv ≫
        (((C.X r) ◁ ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (𝟙_ (ModuleCat R))).inv))) ≫
        HomologicalComplex.ιTensorObj C
          (HomologicalComplex.tensorUnit (ModuleCat R) (ComplexShape.up ℤ))
          r 0 r (add_zero r)) ∧
    ((cast (congrArg (HomComplex.Cochain C A) (add_zero n))
      (conv f (convOne (R := R) (C := C) (A := A)))).v r s (by omega : r + n = s) =
      (conv f (convOne (R := R) (C := C) (A := A))).v r s hrs) := by
  have hC : ComonObj.comul (X := C) ≫ C ◁ ComonObj.counit (X := C) = (ρ_ C).inv :=
    ComonObj.comul_counit C
  have hCOf := congrArg HomComplex.Cochain.ofHom hC
  rw [HomComplex.Cochain.ofHom_comp] at hCOf
  have hA : A ◁ MonObj.one (X := A) ≫ MonObj.mul (X := A) = (ρ_ A).hom :=
    MonObj.mul_one A
  have hAOf := congrArg HomComplex.Cochain.ofHom hA
  rw [HomComplex.Cochain.ofHom_comp] at hAOf
  exact ⟨HomComplex.Cochain.congr_v hCOf r r (add_zero r),
    HomComplex.Cochain.congr_v hAOf s s (add_zero s),
    HomComplex.Cochain.ofHom_tensorHom_comp_tensor (𝟙 C) (𝟙 C) f
      (convOne (R := R) (C := C) (A := A)),
    HomologicalComplex.rightUnitor'_inv C r,
    cochain_cast_v (add_zero n) (conv f (convOne (R := R) (C := C) (A := A)))
      r s (by omega : r + n = s)⟩

/-- Let R be a commutative ring, C a dg R-coalgebra and A a dg R-algebra, both integer cochain
complexes. Assume all graded tensor coproducts exist, tensoring preserves zero on both sides,
tensoring commutes with the coproducts used for reassociation, and fourfold summand inclusions
determine maps. For cochains f:C→A and g:C→A of degrees m,n, and r+m+n=s,
(f⋆g)_{r,s}=(Δ_C)_r≫(f⊗g)_{r,s}≫(μ_A)_s. The middle tensor component has sign (-1)^{np} on the
source summand of degrees p,q with p+q=r. -/
private theorem conv_tensor_v {m n : ℤ} (f : HomComplex.Cochain C A m)
    (g : HomComplex.Cochain C A n) (r s : ℤ) (hrs : r + (m + n) = s) :
    (conv f g).v r s hrs =
      (ComonObj.comul (X := C)).f r ≫
        (HomComplex.Cochain.tensor f g).v r s (by omega) ≫
          (MonObj.mul (X := A)).f s := by
  rw [conv_eq f g,
    HomComplex.Cochain.comp_v _ _ _ r s s (by omega) (add_zero s),
    HomComplex.Cochain.comp_v _ _ _ r r s (add_zero r) (by omega),
    HomComplex.Cochain.ofHom_v, HomComplex.Cochain.ofHom_v,
    Category.assoc]

/-- For arbitrary integers m,n,k,r,s, the equality r+((m+n)+k)=s implies r+(m+(n+k))=s. Thus the two
associations of three homogeneous cochain degrees have the same source and target indices. -/
private theorem conv_assoc_v_degree {m n p r s : ℤ}
    (hrs : r + ((m + n) + p) = s) : r + (m + (n + p)) = s := by
  omega

omit [∀ (X₁ X₂ : GradedObject ℤ (ModuleCat R)), GradedObject.HasTensor X₁ X₂] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).obj X)] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).flip.obj X)] [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  X₁.HasTensor₄ObjExt X₂ X₃ X₄] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  X₁.HasGoodTensor₁₂Tensor X₂ X₃] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  X₁.HasGoodTensorTensor₂₃ X₂ X₃] in
/-- Over a commutative ring R, let f:X₁→Y₁ and g:X₂→Y₂ be R-linear maps. Tensoring respects negation
in the left factor: (-f)⊗g=-(f⊗g) as maps X₁⊗X₂→Y₁⊗Y₂. -/
private lemma neg_tensorHom_left {X₁ Y₁ X₂ Y₂ : ModuleCat R}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : ((-f) ⊗ₘ g) = -((f ⊗ₘ g)) := by
  have h : ((-f) ⊗ₘ g) + ((f ⊗ₘ g)) = 0 := by
    rw [← MonoidalPreadditive.add_tensor, neg_add_cancel,
      MonoidalPreadditive.zero_tensor]
  exact eq_neg_of_add_eq_zero_left h

omit [∀ (X₁ X₂ : GradedObject ℤ (ModuleCat R)), GradedObject.HasTensor X₁ X₂] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).obj X)] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).flip.obj X)] [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  X₁.HasTensor₄ObjExt X₂ X₃ X₄] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  X₁.HasGoodTensor₁₂Tensor X₂ X₃] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  X₁.HasGoodTensorTensor₂₃ X₂ X₃] in
/-- Over a commutative ring R, let f:X₁→Y₁ and g:X₂→Y₂ be R-linear maps. Tensoring respects negation
in the right factor: f⊗(-g)=-(f⊗g) as maps X₁⊗X₂→Y₁⊗Y₂. -/
private lemma neg_tensorHom_right {X₁ Y₁ X₂ Y₂ : ModuleCat R}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : ((f ⊗ₘ (-g))) = -((f ⊗ₘ g)) := by
  have h : ((f ⊗ₘ (-g))) + ((f ⊗ₘ g)) = 0 := by
    rw [← MonoidalPreadditive.tensor_add, neg_add_cancel,
      MonoidalPreadditive.tensor_zero]
  exact eq_neg_of_add_eq_zero_left h

omit [∀ (X₁ X₂ : GradedObject ℤ (ModuleCat R)), GradedObject.HasTensor X₁ X₂] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).obj X)] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).flip.obj X)] [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  X₁.HasTensor₄ObjExt X₂ X₃ X₄] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  X₁.HasGoodTensor₁₂Tensor X₂ X₃] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  X₁.HasGoodTensorTensor₂₃ X₂ X₃] in
/-- Over a commutative ring R, let f:X₁→Y₁ and g:X₂→Y₂ be R-linear maps. For any k∈ℤˣ,
(k•f)⊗g=k•(f⊗g) as maps X₁⊗X₂→Y₁⊗Y₂. -/
private lemma tensorHom_units_smul_left {X₁ Y₁ X₂ Y₂ : ModuleCat R} (k : ℤˣ)
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : ((k • f) ⊗ₘ g) = k • (f ⊗ₘ g) := by
  rcases Int.units_eq_one_or k with rfl | rfl
  · simp only [one_smul]
  · simp only [Units.neg_smul, one_smul, neg_tensorHom_left]

omit [∀ (X₁ X₂ : GradedObject ℤ (ModuleCat R)), GradedObject.HasTensor X₁ X₂] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).obj X)] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).flip.obj X)] [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  X₁.HasTensor₄ObjExt X₂ X₃ X₄] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  X₁.HasGoodTensor₁₂Tensor X₂ X₃] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  X₁.HasGoodTensorTensor₂₃ X₂ X₃] in
/-- Over a commutative ring R, let f:X₁→Y₁ and g:X₂→Y₂ be R-linear maps. For any k∈ℤˣ,
f⊗(k•g)=k•(f⊗g) as maps X₁⊗X₂→Y₁⊗Y₂. -/
private lemma tensorHom_units_smul_right {X₁ Y₁ X₂ Y₂ : ModuleCat R} (k : ℤˣ)
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : ((f ⊗ₘ (k • g))) = k • (f ⊗ₘ g) := by
  rcases Int.units_eq_one_or k with rfl | rfl
  · simp only [one_smul]
  · simp only [Units.neg_smul, one_smul, neg_tensorHom_right]

omit [∀ (X₁ X₂ : GradedObject ℤ (ModuleCat R)), GradedObject.HasTensor X₁ X₂] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).obj X)] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).flip.obj X)] [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  X₁.HasTensor₄ObjExt X₂ X₃ X₄] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  X₁.HasGoodTensor₁₂Tensor X₂ X₃] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  X₁.HasGoodTensorTensor₂₃ X₂ X₃] in
/-- Over a commutative ring R, let integer cochain complexes C₁,C₂,A₁,A₂,B₁,B₂ have tensor degree
coproducts for each corresponding pair. For a₁:C₁→A₁, b₁:A₁→B₁, a₂:C₂→A₂ and b₂:A₂→B₂ of degrees
m₁,n₁,m₂,n₂, (a₁⊗a₂)≫(b₁⊗b₂)=(-1)^{n₂m₁}((a₁≫b₁)⊗(a₂≫b₂)), identified in degree (m₁+n₁)+(m₂+n₂). -/
private theorem tensor_comp_tensor {C₁ C₂ A₁ A₂ B₁ B₂ : CochainComplex (ModuleCat R) ℤ}
    {m₁ n₁ m₂ n₂ : ℤ}
    (a₁ : HomComplex.Cochain C₁ A₁ m₁) (b₁ : HomComplex.Cochain A₁ B₁ n₁)
    (a₂ : HomComplex.Cochain C₂ A₂ m₂) (b₂ : HomComplex.Cochain A₂ B₂ n₂)
    [GradedObject.HasTensor C₁.X C₂.X] [GradedObject.HasTensor A₁.X A₂.X]
    [GradedObject.HasTensor B₁.X B₂.X] :
    (HomComplex.Cochain.tensor a₁ a₂).comp (HomComplex.Cochain.tensor b₁ b₂)
      (by omega : (m₁ + m₂) + (n₁ + n₂) = (m₁ + n₁) + (m₂ + n₂)) =
      (n₂ * m₁).negOnePow •
        HomComplex.Cochain.tensor (a₁.comp b₁ rfl) (a₂.comp b₂ rfl) := by
  apply HomComplex.Cochain.ext
  intro r s hrs
  rw [HomComplex.Cochain.comp_v _ _ _ r (r + (m₁ + m₂)) s (by omega) (by omega),
    HomComplex.Cochain.tensor_v, HomComplex.Cochain.tensor_v,
    HomComplex.Cochain.units_smul_v, HomComplex.Cochain.tensor_v]
  apply HomologicalComplex.mapBifunctor.hom_ext (c := ComplexShape.up ℤ)
  intro i₁ i₂ hh
  have hij : i₁ + i₂ = r := hh
  have hsign : m₂ * i₁ + n₂ * (i₁ + m₁) = (m₂ + n₂) * i₁ + n₂ * m₁ := by
    rw [mul_add, add_mul]
    ac_rfl
  rw [← Category.assoc, HomologicalComplex.ι_mapBifunctorDesc]
  dsimp only
  rw [Linear.units_smul_comp, Category.assoc, HomologicalComplex.ι_mapBifunctorDesc]
  conv_rhs => rw [Linear.comp_units_smul, HomologicalComplex.ι_mapBifunctorDesc]
  rw [HomComplex.Cochain.comp_v a₁ b₁ rfl i₁ (i₁ + m₁) _ rfl (by omega),
    HomComplex.Cochain.comp_v a₂ b₂ rfl i₂ (i₂ + m₂) _ rfl (by omega)]
  rw [← MonoidalCategory.tensorHom_comp_tensorHom]
  simp only [Linear.comp_units_smul, smul_smul, ← Int.negOnePow_add]
  rw [hsign, add_comm (n₂ * m₁) ((m₂ + n₂) * i₁), Category.assoc]
  have key : ∀ (y1 y2 : ℤ) (hy1 : (i₁ + m₁) + n₁ = y1) (hy2 : (i₂ + m₂) + n₂ = y2)
      (hι : y1 + y2 = s),
      (b₁.v (i₁ + m₁) y1 hy1 ⊗ₘ b₂.v (i₂ + m₂) y2 hy2) ≫
        HomologicalComplex.ιTensorObj B₁ B₂ y1 y2 s hι =
      (b₁.v (i₁ + m₁) ((i₁ + m₁) + n₁) rfl ⊗ₘ
        b₂.v (i₂ + m₂) ((i₂ + m₂) + n₂) rfl) ≫
        HomologicalComplex.ιTensorObj B₁ B₂ ((i₁ + m₁) + n₁) ((i₂ + m₂) + n₂) s
          (by omega) := by
    intro y1 y2 hy1 hy2 hι
    subst hy1
    subst hy2
    rfl
  rw [key _ _ (add_assoc i₁ m₁ n₁) (add_assoc i₂ m₂ n₂) (by omega)]

omit [∀ (X₁ X₂ : GradedObject ℤ (ModuleCat R)), GradedObject.HasTensor X₁ X₂] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).obj X)] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).flip.obj X)] [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  X₁.HasTensor₄ObjExt X₂ X₃ X₄] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  X₁.HasGoodTensor₁₂Tensor X₂ X₃] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  X₁.HasGoodTensorTensor₂₃ X₂ X₃] in
/-- Over a commutative ring R, let Cᵢ,Aᵢ,Bᵢ,Dᵢ for i=1,2 be integer cochain complexes, with tensor
degree coproducts for each corresponding pair. For composable aᵢ:Cᵢ→Aᵢ, bᵢ:Aᵢ→Bᵢ, cᵢ:Bᵢ→Dᵢ of
degrees mᵢ,nᵢ,kᵢ, the composite (a₁⊗a₂)≫(b₁⊗b₂)≫(c₁⊗c₂) equals
(-1)^{n₂m₁+k₂(m₁+n₁)}((a₁≫b₁≫c₁)⊗(a₂≫b₂≫c₂)), after identifying the total degrees. -/
private theorem tensor_comp_tensor_three {C₁ C₂ A₁ A₂ B₁ B₂ D₁ D₂ : CochainComplex (ModuleCat R) ℤ}
    {m₁ n₁ p₁ m₂ n₂ p₂ : ℤ}
    (a₁ : HomComplex.Cochain C₁ A₁ m₁) (b₁ : HomComplex.Cochain A₁ B₁ n₁)
    (c₁ : HomComplex.Cochain B₁ D₁ p₁)
    (a₂ : HomComplex.Cochain C₂ A₂ m₂) (b₂ : HomComplex.Cochain A₂ B₂ n₂)
    (c₂ : HomComplex.Cochain B₂ D₂ p₂)
    [GradedObject.HasTensor C₁.X C₂.X] [GradedObject.HasTensor A₁.X A₂.X]
    [GradedObject.HasTensor B₁.X B₂.X] [GradedObject.HasTensor D₁.X D₂.X] :
    (((HomComplex.Cochain.tensor a₁ a₂).comp (HomComplex.Cochain.tensor b₁ b₂)
      (by omega : (m₁ + m₂) + (n₁ + n₂) = (m₁ + n₁) + (m₂ + n₂))).comp
      (HomComplex.Cochain.tensor c₁ c₂)
      (by omega : ((m₁ + n₁) + (m₂ + n₂)) + (p₁ + p₂) =
        ((m₁ + n₁) + p₁) + ((m₂ + n₂) + p₂))) =
      (n₂ * m₁ + p₂ * (m₁ + n₁)).negOnePow •
        HomComplex.Cochain.tensor ((a₁.comp b₁ rfl).comp c₁ rfl)
          ((a₂.comp b₂ rfl).comp c₂ rfl) := by
  have h1 := tensor_comp_tensor a₁ b₁ a₂ b₂
  rw [h1, HomComplex.Cochain.units_smul_comp]
  have h2 := tensor_comp_tensor (a₁.comp b₁ rfl) c₁ (a₂.comp b₂ rfl) c₂
  rw [h2, smul_smul, ← Int.negOnePow_add]

/-- Let R be a commutative ring, C a dg R-coalgebra and A a dg R-algebra, both integer cochain
complexes. Assume all graded tensor coproducts exist, tensoring preserves zero on both sides,
tensoring commutes with the coproducts used for reassociation, and fourfold summand inclusions
determine maps. For |f|=m, |g|=n and |h|=k, (f⋆g)⊗h=(Δ_C⊗id_C)≫((f⊗g)⊗h)≫(μ_A⊗id_A) in degree
(m+n)+k. The degree-zero outer maps and the homogeneous tensor components carry the same Koszul
signs as the convolution tensor. -/
private theorem tensor_conv_factor_left {m n p : ℤ}
    (f : HomComplex.Cochain C A m) (g : HomComplex.Cochain C A n)
    (h : HomComplex.Cochain C A p) :
    HomComplex.Cochain.tensor (conv f g) h =
      (((HomComplex.Cochain.ofHom
        (HomologicalComplex.tensorHom (ComonObj.comul (X := C)) (𝟙 C))).comp
        (HomComplex.Cochain.tensor (HomComplex.Cochain.tensor f g) h)
        (zero_add ((m + n) + p))).comp
        (HomComplex.Cochain.ofHom
          (HomologicalComplex.tensorHom (MonObj.mul (X := A)) (𝟙 A)))
        (add_zero ((m + n) + p))) := by
  have e_pre := HomComplex.Cochain.ofHom_tensorHom_comp_tensor
    (ComonObj.comul (X := C)) (𝟙 C)
    (HomComplex.Cochain.tensor f g) h
  rw [HomComplex.Cochain.id_comp] at e_pre
  have e_post := HomComplex.Cochain.tensor_comp_ofHom_tensorHom
    ((HomComplex.Cochain.ofHom (ComonObj.comul (X := C))).comp
      (HomComplex.Cochain.tensor f g) (zero_add (m + n))) h
    (MonObj.mul (X := A)) (𝟙 A)
  rw [HomComplex.Cochain.comp_id] at e_post
  have e_conv := (conv_eq f g).symm
  rw [e_pre, e_post, e_conv]

/-- Let R be a commutative ring, C a dg R-coalgebra and A a dg R-algebra, both integer cochain
complexes. Assume all graded tensor coproducts exist, tensoring preserves zero on both sides,
tensoring commutes with the coproducts used for reassociation, and fourfold summand inclusions
determine maps. For |f|=m, |g|=n and |h|=k, f⊗(g⋆h)=(id_C⊗Δ_C)≫(f⊗(g⊗h))≫(id_A⊗μ_A) in degree
m+(n+k). The degree-zero outer maps and the homogeneous tensor components carry the same Koszul
signs as the convolution tensor. -/
private theorem tensor_conv_factor_right {m n p : ℤ}
    (f : HomComplex.Cochain C A m) (g : HomComplex.Cochain C A n)
    (h : HomComplex.Cochain C A p) :
    HomComplex.Cochain.tensor f (conv g h) =
      (((HomComplex.Cochain.ofHom
        (HomologicalComplex.tensorHom (𝟙 C) (ComonObj.comul (X := C)))).comp
        (HomComplex.Cochain.tensor f (HomComplex.Cochain.tensor g h))
        (zero_add (m + (n + p)))).comp
        (HomComplex.Cochain.ofHom
          (HomologicalComplex.tensorHom (𝟙 A) (MonObj.mul (X := A))))
        (add_zero (m + (n + p)))) := by
  have e_pre := HomComplex.Cochain.ofHom_tensorHom_comp_tensor
    (𝟙 C) (ComonObj.comul (X := C))
    f (HomComplex.Cochain.tensor g h)
  rw [HomComplex.Cochain.id_comp] at e_pre
  have e_post := HomComplex.Cochain.tensor_comp_ofHom_tensorHom
    f ((HomComplex.Cochain.ofHom (ComonObj.comul (X := C))).comp
      (HomComplex.Cochain.tensor g h) (zero_add (n + p)))
    (𝟙 A) (MonObj.mul (X := A))
  rw [HomComplex.Cochain.comp_id] at e_post
  have e_conv := (conv_eq g h).symm
  rw [e_pre, e_post, e_conv]

/-- Let R be a commutative ring and C a dg R-coalgebra, with integer grading. Assume all graded
tensor coproducts exist, tensoring preserves zero on both sides, tensoring commutes with the
coproducts used for reassociation, and fourfold summand inclusions determine maps. The
degree-zero cochains of the structure maps satisfy Δ_C≫(id_C⊗Δ_C)=Δ_C≫(Δ_C⊗id_C)≫α_C. Here
α_C:(C⊗C)⊗C→C⊗(C⊗C) is the complex associator. -/
private theorem ofHom_comul_slide :
    (HomComplex.Cochain.ofHom (ComonObj.comul (X := C))).comp
      (HomComplex.Cochain.ofHom (C ◁ ComonObj.comul (X := C))) (zero_add 0) =
    (HomComplex.Cochain.ofHom (ComonObj.comul (X := C))).comp
      ((HomComplex.Cochain.ofHom (ComonObj.comul (X := C) ▷ C)).comp
        (HomComplex.Cochain.ofHom (α_ C C C).hom) (zero_add 0))
      (zero_add 0) := by
  have hC : ComonObj.comul (X := C) ≫ C ◁ ComonObj.comul (X := C) =
      ComonObj.comul (X := C) ≫ (ComonObj.comul (X := C) ▷ C) ≫ (α_ C C C).hom :=
    ComonObj.comul_assoc C
  have hOf := congrArg HomComplex.Cochain.ofHom hC
  rw [HomComplex.Cochain.ofHom_comp] at hOf
  rw [HomComplex.Cochain.ofHom_comp] at hOf
  rw [HomComplex.Cochain.ofHom_comp] at hOf
  exact hOf

/-- Let R be a commutative ring and A a dg R-algebra, with integer grading. Assume all graded tensor
coproducts exist, tensoring preserves zero on both sides, tensoring commutes with the coproducts
used for reassociation, and fourfold summand inclusions determine maps. The degree-zero cochains
of the structure maps satisfy (μ_A⊗id_A)≫μ_A=α_A≫(id_A⊗μ_A)≫μ_A. Here α_A:(A⊗A)⊗A→A⊗(A⊗A) is the
complex associator. -/
private theorem ofHom_mul_slide :
    (HomComplex.Cochain.ofHom (MonObj.mul (X := A) ▷ A)).comp
      (HomComplex.Cochain.ofHom (MonObj.mul (X := A))) (zero_add 0) =
    (HomComplex.Cochain.ofHom (α_ A A A).hom).comp
      ((HomComplex.Cochain.ofHom (A ◁ MonObj.mul (X := A))).comp
        (HomComplex.Cochain.ofHom (MonObj.mul (X := A))) (zero_add 0))
      (zero_add 0) := by
  have hA : (MonObj.mul (X := A) ▷ A) ≫ MonObj.mul (X := A) =
      (α_ A A A).hom ≫ (A ◁ MonObj.mul (X := A)) ≫ MonObj.mul (X := A) :=
    MonObj.mul_assoc A
  have hOf := congrArg HomComplex.Cochain.ofHom hA
  rw [HomComplex.Cochain.ofHom_comp] at hOf
  rw [HomComplex.Cochain.ofHom_comp] at hOf
  rw [HomComplex.Cochain.ofHom_comp] at hOf
  exact hOf

/-- Let R be a commutative ring and C a dg R-coalgebra, with integer grading. Assume all graded
tensor coproducts exist, tensoring preserves zero on both sides, tensoring commutes with the
coproducts used for reassociation, and fourfold summand inclusions determine maps. The
degree-zero cochains satisfy Δ_C≫(ε_C⊗id_C)=λ_C⁻¹:C→I⊗C, where ε_C:C→I is the counit, I the
tensor-unit complex concentrated in degree zero, and λ_C:I⊗C→C the left unitor. -/
private theorem ofHom_counit_slide :
    (HomComplex.Cochain.ofHom (ComonObj.comul (X := C))).comp
      (HomComplex.Cochain.ofHom (ComonObj.counit (X := C) ▷ C)) (zero_add 0) =
    HomComplex.Cochain.ofHom (λ_ C).inv := by
  have hC : ComonObj.comul (X := C) ≫ ComonObj.counit (X := C) ▷ C = (λ_ C).inv :=
    ComonObj.counit_comul C
  have hOf := congrArg HomComplex.Cochain.ofHom hC
  rw [HomComplex.Cochain.ofHom_comp] at hOf
  exact hOf

/-- Let R be a commutative ring and A a dg R-algebra, with integer grading. Assume all graded tensor
coproducts exist, tensoring preserves zero on both sides, tensoring commutes with the coproducts
used for reassociation, and fourfold summand inclusions determine maps. The degree-zero cochains
satisfy (η_A⊗id_A)≫μ_A=λ_A:I⊗A→A, where η_A:I→A is the algebra unit, I the tensor-unit complex
concentrated in degree zero, and λ_A the left unitor. -/
private theorem ofHom_one_slide :
    (HomComplex.Cochain.ofHom (MonObj.one (X := A) ▷ A)).comp
      (HomComplex.Cochain.ofHom (MonObj.mul (X := A))) (zero_add 0) =
    HomComplex.Cochain.ofHom (λ_ A).hom := by
  have hA : MonObj.one (X := A) ▷ A ≫ MonObj.mul (X := A) = (λ_ A).hom :=
    MonObj.one_mul A
  have hOf := congrArg HomComplex.Cochain.ofHom hA
  rw [HomComplex.Cochain.ofHom_comp] at hOf
  exact hOf

omit [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).obj X)] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).flip.obj X)] [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  X₁.HasTensor₄ObjExt X₂ X₃ X₄] [MonObj A] [ComonObj C] in
/-- Let R be a commutative ring and C,A integer cochain complexes of R-modules. Assume all graded
tensor coproducts exist, tensoring preserves zero on both sides, tensoring commutes with the
coproducts used for reassociation, and fourfold summand inclusions determine maps. For f,g,h:C→A
of integer degrees m,n,k, ((f⊗g)⊗h)≫α_A=α_C≫(f⊗(g⊗h)), identifying (m+n)+k with m+(n+k). The
complex associators go from (X⊗X)⊗X to X⊗(X⊗X), with X=C or A. -/
private theorem tensor_assoc_hmid {m n p : ℤ}
    (f : HomComplex.Cochain C A m) (g : HomComplex.Cochain C A n)
    (h : HomComplex.Cochain C A p) :
    (HomComplex.Cochain.tensor (HomComplex.Cochain.tensor f g) h).comp
      (HomComplex.Cochain.ofHom
        (HomologicalComplex.associator A A A).hom) (add_zero (m + n + p)) =
    (HomComplex.Cochain.ofHom
        (HomologicalComplex.associator C C C).hom).comp
      (HomComplex.Cochain.tensor f (HomComplex.Cochain.tensor g h))
      (by omega) := by
  exact HomComplex.Cochain.tensor_assoc f g h

/-- Let R be a commutative ring, C a dg R-coalgebra and A a dg R-algebra, both integer cochain
complexes. Assume all graded tensor coproducts exist, tensoring preserves zero on both sides,
tensoring commutes with the coproducts used for reassociation, and fourfold summand inclusions
determine maps. For |f|=m, |g|=n, |h|=k and r+((m+n)+k)=s, the C_r→A_s components of
Δ_C≫(Δ_C⊗id_C)≫((f⊗g)⊗h)≫(μ_A⊗id_A)≫μ_A and Δ_C≫(id_C⊗Δ_C)≫(f⊗(g⊗h))≫(id_A⊗μ_A)≫μ_A are equal.
Their integer degrees are identified by associativity of addition. -/
private theorem conv_assoc_hmid_middle_v {m n p r s : ℤ}
    (f : HomComplex.Cochain C A m) (g : HomComplex.Cochain C A n)
    (h : HomComplex.Cochain C A p)
    (hrs : r + ((m + n) + p) = s) :
    (((((HomComplex.Cochain.ofHom (ComonObj.comul (X := C))).comp
      (HomComplex.Cochain.ofHom (ComonObj.comul (X := C) ▷ C)) (zero_add 0)).comp
      (HomComplex.Cochain.tensor (HomComplex.Cochain.tensor f g) h)
      (zero_add ((m + n) + p))).comp
      (HomComplex.Cochain.ofHom (MonObj.mul (X := A) ▷ A))
      (add_zero ((m + n) + p))).comp
      (HomComplex.Cochain.ofHom (MonObj.mul (X := A)))
      (add_zero ((m + n) + p))).v r s hrs =
    (((((HomComplex.Cochain.ofHom (ComonObj.comul (X := C))).comp
      (HomComplex.Cochain.ofHom (C ◁ ComonObj.comul (X := C))) (zero_add 0)).comp
      (HomComplex.Cochain.tensor f (HomComplex.Cochain.tensor g h))
      (zero_add (m + (n + p)))).comp
      (HomComplex.Cochain.ofHom (A ◁ MonObj.mul (X := A)))
      (add_zero (m + (n + p)))).comp
      (HomComplex.Cochain.ofHom (MonObj.mul (X := A)))
      (add_zero (m + (n + p)))).v r s (conv_assoc_v_degree hrs) := by
  have hC : (HomComplex.Cochain.ofHom (ComonObj.comul (X := C))).comp
      (HomComplex.Cochain.ofHom (C ◁ ComonObj.comul (X := C))) (zero_add 0) =
    (HomComplex.Cochain.ofHom (ComonObj.comul (X := C))).comp
      ((HomComplex.Cochain.ofHom (ComonObj.comul (X := C) ▷ C)).comp
        (HomComplex.Cochain.ofHom (α_ C C C).hom) (zero_add 0))
      (zero_add 0) := ofHom_comul_slide
  have hC_v := HomComplex.Cochain.congr_v hC r r (add_zero r)
  have hA : (HomComplex.Cochain.ofHom (MonObj.mul (X := A) ▷ A)).comp
      (HomComplex.Cochain.ofHom (MonObj.mul (X := A))) (zero_add 0) =
    (HomComplex.Cochain.ofHom (α_ A A A).hom).comp
      ((HomComplex.Cochain.ofHom (A ◁ MonObj.mul (X := A))).comp
        (HomComplex.Cochain.ofHom (MonObj.mul (X := A))) (zero_add 0))
      (zero_add 0) := ofHom_mul_slide
  have hA_v := HomComplex.Cochain.congr_v hA s s (add_zero s)
  have hM := tensor_assoc_hmid f g h
  have hM_v := HomComplex.Cochain.congr_v hM r s hrs
  have hαC : (α_ C C C).hom = (HomologicalComplex.associator C C C).hom := rfl
  have hαA : (α_ A A A).hom = (HomologicalComplex.associator A A A).hom := rfl
  simp only [HomComplex.Cochain.comp_zero_cochain_v,
    HomComplex.Cochain.zero_cochain_comp_v, HomComplex.Cochain.ofHom_v] at hC_v hA_v hM_v ⊢
  rw [hC_v]
  simp only [Category.assoc] at ⊢
  rw [hA_v]
  rw [hαC, hαA] at ⊢
  conv_lhs =>
    arg 2
    arg 2
    rw [← Category.assoc]
    rw [hM_v]
    rw [HomComplex.Cochain.comp_v _ _ _ r r s (add_zero r) (by omega)]
    simp only [HomComplex.Cochain.ofHom_v]
    rw [Category.assoc]

/-- Let R be a commutative ring, C a dg R-coalgebra and A a dg R-algebra, both integer cochain
complexes. Assume all graded tensor coproducts exist, tensoring preserves zero on both sides,
tensoring commutes with the coproducts used for reassociation, and fourfold summand inclusions
determine maps. For homogeneous f,g,h:C→A of integer degrees m,n,k, (f⋆g)⋆h=f⋆(g⋆h) after
transporting degree (m+n)+k to m+(n+k) by associativity of addition. Here f⋆g=μ_A(f⊗g)Δ_C, with
tensor sign (-1)^{np} on left input degree p for |g|=n. -/
theorem conv_assoc {m n p : ℤ}
    (f : HomComplex.Cochain C A m) (g : HomComplex.Cochain C A n)
    (h : HomComplex.Cochain C A p) :
    cast (congrArg (HomComplex.Cochain C A) (add_assoc m n p))
        (conv (conv f g) h) =
      conv f (conv g h) := by
  apply HomComplex.Cochain.ext
  intro r s hrs
  rw [cochain_cast_v (add_assoc m n p)]
  have eL : conv (conv f g) h =
      (((((HomComplex.Cochain.ofHom (ComonObj.comul (X := C))).comp
        (HomComplex.Cochain.ofHom (HomologicalComplex.tensorHom
          (ComonObj.comul (X := C)) (𝟙 C))) (zero_add 0)).comp
        (HomComplex.Cochain.tensor (HomComplex.Cochain.tensor f g) h)
        (zero_add ((m + n) + p))).comp
        (HomComplex.Cochain.ofHom (HomologicalComplex.tensorHom
          (MonObj.mul (X := A)) (𝟙 A)))
        (add_zero ((m + n) + p))).comp
        (HomComplex.Cochain.ofHom (MonObj.mul (X := A)))
        (add_zero ((m + n) + p))) := by
    rw [conv_eq (conv f g) h, tensor_conv_factor_left f g h]
    rw [← HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain _ _ _
      (show (m + n) + p + 0 = (m + n) + p from add_zero _)]
    rw [← HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain _ _ _
      (show 0 + ((m + n) + p) = (m + n) + p from zero_add _)]
  have eR : conv f (conv g h) =
      (((((HomComplex.Cochain.ofHom (ComonObj.comul (X := C))).comp
        (HomComplex.Cochain.ofHom (HomologicalComplex.tensorHom
          (𝟙 C) (ComonObj.comul (X := C)))) (zero_add 0)).comp
        (HomComplex.Cochain.tensor f (HomComplex.Cochain.tensor g h))
        (zero_add (m + (n + p)))).comp
        (HomComplex.Cochain.ofHom (HomologicalComplex.tensorHom
          (𝟙 A) (MonObj.mul (X := A))))
        (add_zero (m + (n + p)))).comp
        (HomComplex.Cochain.ofHom (MonObj.mul (X := A)))
        (add_zero (m + (n + p)))) := by
    rw [conv_eq f (conv g h), tensor_conv_factor_right f g h]
    rw [← HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain _ _ _
      (show m + (n + p) + 0 = m + (n + p) from add_zero _)]
    rw [← HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain _ _ _
      (show 0 + (m + (n + p)) = m + (n + p) from zero_add _)]
  rw [eL, eR]
  exact conv_assoc_hmid_middle_v f g h (by omega : r + ((m + n) + p) = s)

/-- Let R be a commutative ring, C a dg R-coalgebra and A a dg R-algebra, both integer cochain
complexes. Assume all graded tensor coproducts exist, tensoring preserves zero on both sides,
tensoring commutes with the coproducts used for reassociation, and fourfold summand inclusions
determine maps. Write e=ε_C≫η_A:C→A for the degree-zero cochain formed from the coalgebra counit
and algebra unit. For |f|=n and r+0+n=s, the following identities hold:
(Δ_C≫(ε_C⊗id_C))_r=(λ_C⁻¹)_r and ((η_A⊗id_A)≫μ_A)_s=(λ_A)_s; (id_C⊗id_C)≫(e⊗f)=(id_C≫e)⊗(id_C≫f)
as cochains. With I the tensor-unit complex and σ:I_0≅R,
(λ_C⁻¹)_r=λ_{C_r}⁻¹≫(σ⁻¹⊗id_{C_r})≫ι^{I,C}_{0,r,r}. Identifying 0+n with n leaves the C_r→A_s
component of e⋆f unchanged. The unitors have directions λ_X:I⊗X→X. -/
private theorem conv_one_left_transport {n : ℤ}
    (f : HomComplex.Cochain C A n) (r s : ℤ) (hrs : r + (0 + n) = s) :
    ((((HomComplex.Cochain.ofHom (ComonObj.comul (X := C))).comp
      (HomComplex.Cochain.ofHom (ComonObj.counit (X := C) ▷ C))
      (zero_add 0))).v r r (add_zero r) =
      (HomComplex.Cochain.ofHom (λ_ C).inv).v r r (add_zero r)) ∧
    ((((HomComplex.Cochain.ofHom (MonObj.one (X := A) ▷ A))).comp
      (HomComplex.Cochain.ofHom (MonObj.mul (X := A)))
      (zero_add 0))).v s s (add_zero s) =
      (HomComplex.Cochain.ofHom (λ_ A).hom).v s s (add_zero s) ∧
    ((HomComplex.Cochain.ofHom
      (HomologicalComplex.tensorHom (𝟙 C) (𝟙 C))).comp
      (HomComplex.Cochain.tensor (convOne (R := R) (C := C) (A := A)) f)
      (zero_add (0 + n))) =
      HomComplex.Cochain.tensor
        ((HomComplex.Cochain.ofHom (𝟙 C)).comp
          (convOne (R := R) (C := C) (A := A)) (zero_add 0))
        ((HomComplex.Cochain.ofHom (𝟙 C)).comp f (zero_add n)) ∧
    ((HomologicalComplex.leftUnitor' C).inv r =
      (λ_ (C.X r)).inv ≫
        (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (𝟙_ (ModuleCat R))).inv) ▷ (C.X r)) ≫
        HomologicalComplex.ιTensorObj
          (HomologicalComplex.tensorUnit (ModuleCat R) (ComplexShape.up ℤ)) C
          0 r r (zero_add r)) ∧
    ((cast (congrArg (HomComplex.Cochain C A) (zero_add n))
      (conv (convOne (R := R) (C := C) (A := A)) f)).v r s (by omega : r + n = s) =
      (conv (convOne (R := R) (C := C) (A := A)) f).v r s hrs) := by
  exact ⟨HomComplex.Cochain.congr_v ofHom_counit_slide r r (add_zero r),
    HomComplex.Cochain.congr_v ofHom_one_slide s s (add_zero s),
    HomComplex.Cochain.ofHom_tensorHom_comp_tensor (𝟙 C) (𝟙 C)
      (convOne (R := R) (C := C) (A := A)) f,
    HomologicalComplex.leftUnitor'_inv C r,
    cochain_cast_v (zero_add n) (conv (convOne (R := R) (C := C) (A := A)) f)
      r s (by omega : r + n = s)⟩

/-- Let R be a commutative ring, C a dg R-coalgebra and A a dg R-algebra, both integer cochain
complexes. Assume all graded tensor coproducts exist, tensoring preserves zero on both sides,
tensoring commutes with the coproducts used for reassociation, and fourfold summand inclusions
determine maps. Write e=ε_C≫η_A:C→A for the degree-zero cochain formed from the coalgebra counit
and algebra unit. For |f|=n and r+0+n=s,
(-1)^{n·0}(e_0⊗f_r)≫ι^A_{0,r+n,s}=(e_0⊗f_r)≫ι^A_{0,r+n,s}. Here ι^A is the inclusion into
(A⊗A)_s; the equality removes the Koszul sign on the zero first-index summand. -/
private theorem tensor_convOne_surviving_sign {n : ℤ}
    (f : HomComplex.Cochain C A n) (r s : ℤ) (hrs : r + (0 + n) = s) :
    (n * 0).negOnePow •
      ((convOne (R := R) (C := C) (A := A)).v 0 (0 + 0) rfl ⊗ₘ
        f.v r (r + n) rfl) ≫
      HomologicalComplex.ιTensorObj A A (0 + 0) (r + n) s (by omega) =
    ((convOne (R := R) (C := C) (A := A)).v 0 (0 + 0) rfl ⊗ₘ
      f.v r (r + n) rfl) ≫
    HomologicalComplex.ιTensorObj A A (0 + 0) (r + n) s (by omega) := by
  simp

/-- Let R be a commutative ring and A a dg R-algebra, with integer grading. Assume all graded tensor
coproducts exist, tensoring preserves zero on both sides, tensoring commutes with the coproducts
used for reassociation, and fourfold summand inclusions determine maps. Write I for the
tensor-unit complex concentrated in degree zero and η_A:I→A for the algebra unit. For every
integer i≠0, the degree-zero cochain induced by η_A has zero I_i→A_i component, because I_i is
zero. -/
private theorem one_vanish (i : ℤ) (hi : i ≠ 0) :
    (HomComplex.Cochain.ofHom (MonObj.one (X := A))).v i i (by omega) = 0 := by
  rw [HomComplex.Cochain.ofHom_v]
  have h0 : IsZero
      ((HomologicalComplex.tensorUnit (ModuleCat R) (ComplexShape.up ℤ)).X i) :=
    HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
      (𝟙_ (ModuleCat R)) i hi
  exact h0.eq_of_src _ _

/-- Let R be a commutative ring and A a dg R-algebra, with integer grading. Assume all graded tensor
coproducts exist, tensoring preserves zero on both sides, tensoring commutes with the coproducts
used for reassociation, and fourfold summand inclusions determine maps. Write I for the
tensor-unit complex concentrated in degree zero and η_A:I→A for the algebra unit. For integers
i,j with i+0=j and i≠0, the I_i→A_j component of the degree-zero unit cochain is zero. -/
private theorem one_vanish_general (i j : ℤ) (hij : i + (0 : ℤ) = j)
    (hi : i ≠ 0) :
    (HomComplex.Cochain.ofHom (MonObj.one (X := A))).v i j hij = 0 := by
  have hj : i = j := by omega
  subst hj
  exact one_vanish i hi

omit [ComonObj C] in
/-- Let R be a commutative ring and A a dg R-algebra, with integer grading. Assume all graded tensor
coproducts exist, tensoring preserves zero on both sides, tensoring commutes with the coproducts
used for reassociation, and fourfold summand inclusions determine maps. Write I for the
tensor-unit complex concentrated in degree zero and η_A:I→A for the algebra unit. Let C be any
integer cochain complex and g:C→A have degree n. For p≠0 and any q, (-1)^{np}((η_A)_p⊗g_q)=0 as
a map I_p⊗C_q→A_p⊗A_{q+n}. -/
private theorem tensor_one_summand_vanish {n : ℤ}
    (g : HomComplex.Cochain C A n) (i₁ i₂ : ℤ) (hi₁ : i₁ ≠ 0) :
    (n * i₁).negOnePow •
      ((HomComplex.Cochain.ofHom (MonObj.one (X := A))).v i₁ (i₁ + 0) rfl ⊗ₘ
        g.v i₂ (i₂ + n) rfl) = 0 := by
  have h0 : (HomComplex.Cochain.ofHom (MonObj.one (X := A))).v i₁ (i₁ + 0) rfl = 0 :=
    one_vanish_general i₁ (i₁ + 0) rfl hi₁
  rw [h0, MonoidalPreadditive.zero_tensor]
  simp

omit [ComonObj C] in
/-- Let R be a commutative ring and A a dg R-algebra, with integer grading. Assume all graded tensor
coproducts exist, tensoring preserves zero on both sides, tensoring commutes with the coproducts
used for reassociation, and fourfold summand inclusions determine maps. Write I for the
tensor-unit complex concentrated in degree zero and η_A:I→A for the algebra unit. Let C be any
integer cochain complex and g:C→A have degree n. If r+0+n=s, p+q=r and p≠0, then
ι^{I,C}_{p,q,r}≫(η_A⊗g)_{r,s}=0. The inclusion is into (I⊗C)_r, and the tensor component maps to
(A⊗A)_s. -/
private theorem tensor_one_support_collapse {n : ℤ}
    (g : HomComplex.Cochain C A n) (r s : ℤ) (hrs : r + (0 + n) = s)
    (i₁ i₂ : ℤ) (hij : i₁ + i₂ = r) (hi₁ : i₁ ≠ 0) :
    HomologicalComplex.ιMapBifunctor (𝟙_ (CochainComplex (ModuleCat R) ℤ)) C
        (curriedTensor (ModuleCat R))
        (ComplexShape.up ℤ) i₁ i₂ r hij ≫
      (HomComplex.Cochain.tensor
        (HomComplex.Cochain.ofHom (MonObj.one (X := A))) g).v
        r s hrs = 0 := by
  rw [HomComplex.Cochain.tensor_v, HomologicalComplex.ι_mapBifunctorDesc]
  dsimp only
  have h0 : (HomComplex.Cochain.ofHom (MonObj.one (X := A))).v i₁ (i₁ + 0) rfl = 0 :=
    one_vanish_general i₁ (i₁ + 0) rfl hi₁
  rw [h0, MonoidalPreadditive.zero_tensor]
  simp

omit [ComonObj C] in
/-- Let R be a commutative ring and A a dg R-algebra, with integer grading. Assume all graded tensor
coproducts exist, tensoring preserves zero on both sides, tensoring commutes with the coproducts
used for reassociation, and fourfold summand inclusions determine maps. Write I for the
tensor-unit complex concentrated in degree zero and η_A:I→A for the algebra unit. Let C be any
integer cochain complex and g:C→A have degree n. For r+0+n=s,
ι^{I,C}_{0,r,r}≫(η_A⊗g)_{r,s}=((η_A)_0⊗g_r)≫ι^A_{0,r+n,s}, with sign (-1)^{n·0}=1. For every
p+q=r with p≠0, ι^{I,C}_{p,q,r}≫(η_A⊗g)_{r,s}=0. The target inclusions belong to (A⊗A)_s. -/
private theorem tensor_one_desc_singleton {n : ℤ}
    (g : HomComplex.Cochain C A n) (r s : ℤ) (hrs : r + (0 + n) = s) :
    (HomologicalComplex.ιMapBifunctor (𝟙_ (CochainComplex (ModuleCat R) ℤ)) C
        (curriedTensor (ModuleCat R))
        (ComplexShape.up ℤ) 0 r r (zero_add r) ≫
      (HomComplex.Cochain.tensor
        (HomComplex.Cochain.ofHom (MonObj.one (X := A))) g).v
        r s hrs =
      (n * 0).negOnePow •
        ((HomComplex.Cochain.ofHom (MonObj.one (X := A))).v 0 (0 + 0) rfl ⊗ₘ
          g.v r (r + n) rfl) ≫
        HomologicalComplex.ιTensorObj A A (0 + 0) (r + n) s (by omega)) ∧
    (∀ (i₁ i₂ : ℤ) (hij : i₁ + i₂ = r) (_hi₁ : i₁ ≠ 0),
      HomologicalComplex.ιMapBifunctor (𝟙_ (CochainComplex (ModuleCat R) ℤ)) C
        (curriedTensor (ModuleCat R))
        (ComplexShape.up ℤ) i₁ i₂ r hij ≫
      (HomComplex.Cochain.tensor
        (HomComplex.Cochain.ofHom (MonObj.one (X := A))) g).v
        r s hrs = 0) := by
  exact ⟨by rw [HomComplex.Cochain.tensor_v, HomologicalComplex.ι_mapBifunctorDesc],
    fun i₁ i₂ hij hi₁ => tensor_one_support_collapse g r s hrs i₁ i₂ hij hi₁⟩

/-- Let R be a commutative ring, C a dg R-coalgebra and A a dg R-algebra, both integer cochain
complexes. Assume all graded tensor coproducts exist, tensoring preserves zero on both sides,
tensoring commutes with the coproducts used for reassociation, and fourfold summand inclusions
determine maps. Write e=ε_C≫η_A:C→A for the degree-zero cochain formed from the coalgebra counit
and algebra unit. For a degree-n cochain f:C→A, e⊗f=(ε_C⊗id_C)≫(η_A⊗(id_C≫f)) as degree-(0+n)
cochains C⊗C→A⊗A. The intermediate source is I⊗C, with I the tensor-unit complex concentrated in
degree zero. -/
private theorem tensor_convOne_middle_interchange {n : ℤ}
    (f : HomComplex.Cochain C A n) :
    HomComplex.Cochain.tensor (convOne (R := R) (C := C) (A := A)) f =
      ((HomComplex.Cochain.ofHom
        (HomologicalComplex.tensorHom (ComonObj.counit (X := C)) (𝟙 C))).comp
        (HomComplex.Cochain.tensor
          (HomComplex.Cochain.ofHom (MonObj.one (X := A)))
          ((HomComplex.Cochain.ofHom (𝟙 C)).comp f (zero_add n)))
        (zero_add (0 + n))) := by
  have hConv : (convOne (R := R) (C := C) (A := A)) =
      (HomComplex.Cochain.ofHom (ComonObj.counit (X := C))).comp
        (HomComplex.Cochain.ofHom (MonObj.one (X := A))) (zero_add 0) := rfl
  have e_pre := HomComplex.Cochain.ofHom_tensorHom_comp_tensor
    (ComonObj.counit (X := C)) (𝟙 C)
    (HomComplex.Cochain.ofHom (MonObj.one (X := A))) f
  rw [← hConv] at e_pre
  have hid : ((HomComplex.Cochain.ofHom (𝟙 C)).comp f (zero_add n)) = f := by
    rw [HomComplex.Cochain.id_comp]
  rw [hid] at e_pre ⊢
  exact e_pre.symm

/-- Let R be a commutative ring, C a dg R-coalgebra and A a dg R-algebra, both integer cochain
complexes. Assume all graded tensor coproducts exist, tensoring preserves zero on both sides,
tensoring commutes with the coproducts used for reassociation, and fourfold summand inclusions
determine maps. Write e=ε_C≫η_A:C→A for the degree-zero cochain formed from the coalgebra counit
and algebra unit. For every homogeneous degree-n cochain f:C→A, e⋆f=f after identifying 0+n with
n. Convolution is f⋆g=μ_A(f⊗g)Δ_C; in e⊗f the only surviving first input index is zero, so its
Koszul sign is one. -/
theorem conv_one_left {n : ℤ} (f : HomComplex.Cochain C A n) :
    cast (congrArg (HomComplex.Cochain C A) (zero_add n))
      (conv (convOne (R := R) (C := C) (A := A)) f) = f := by
  apply HomComplex.Cochain.ext
  intro r s hrs
  rw [cochain_cast_v (zero_add n)]
  have eConv := conv_eq (convOne (R := R) (C := C) (A := A)) f
  have hMid := tensor_convOne_middle_interchange f
  have hid : ((HomComplex.Cochain.ofHom (𝟙 C)).comp f (zero_add n)) = f := by
    rw [HomComplex.Cochain.id_comp]
  rw [hid] at hMid
  have hMid_v := HomComplex.Cochain.congr_v hMid r s (by omega : r + (0 + n) = s)
  have hTrans := conv_one_left_transport f r s (by omega)
  obtain ⟨hC_v, hA_v, _, hU, _⟩ := hTrans
  have hWhiskerC : (HomologicalComplex.tensorHom
      (ComonObj.counit (X := C)) (𝟙 C)).f r =
      (ComonObj.counit (X := C) ▷ C).f r := rfl
  have hWhiskerA : (HomologicalComplex.tensorHom
      (MonObj.one (X := A)) (𝟙 A)).f s =
      (MonObj.one (X := A) ▷ A).f s := rfl
  have hOneV : (HomComplex.Cochain.ofHom (MonObj.one (X := A))).v 0 0 (add_zero 0) =
      (MonObj.one (X := A)).f 0 :=
    HomComplex.Cochain.ofHom_v _ _
  have hIotaOne := HomologicalComplex.ιTensorObj_tensorHom
    (MonObj.one (X := A)) (𝟙 A) 0 (r + n) s (by omega)
  have hIdA : ((𝟙 A : A ⟶ A).f (r + n)) = 𝟙 (A.X (r + n)) := rfl
  have hLamBridge : (λ_ A).hom.f s = (HomologicalComplex.leftUnitor A).hom.f s := rfl
  have hStep : (HomologicalComplex.ιTensorObj (𝟙_ (CochainComplex (ModuleCat R) ℤ)) A
        0 (r + n) (r + n) (by omega) ≫
        (HomologicalComplex.leftUnitor A).hom.f (r + n)) =
      (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (𝟙_ (ModuleCat R))).hom ▷ A.X (r + n)) ≫ (λ_ (A.X (r + n))).hom) :=
    HomologicalComplex.ιTensorObj_leftUnitor_hom A (r + n)
  have hWhiskerS : ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (𝟙_ (ModuleCat R))).hom ▷ A.X (r + n)) =
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (𝟙_ (ModuleCat R))).hom ⊗ₘ 𝟙 (A.X (r + n))) := rfl
  have hS : ((((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (𝟙_ (ModuleCat R))).inv ⊗ₘ 𝟙 (A.X (r + n))) ≫
      (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (𝟙_ (ModuleCat R))).hom ▷ A.X (r + n)) ≫ (λ_ (A.X (r + n))).hom))) =
      (λ_ (A.X (r + n))).hom := by
    rw [hWhiskerS, ← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom,
      Iso.inv_hom_id]
    simp
  have hWhiskerF : ((𝟙 (𝟙_ (ModuleCat R)) ⊗ₘ f.v r (r + n) rfl)) =
      ((𝟙_ (ModuleCat R)) ◁ f.v r (r + n) rfl) := rfl
  have hIotaIdx : HomologicalComplex.ιTensorObj A A (0 + 0) (r + n) s (by omega) =
      HomologicalComplex.ιTensorObj A A 0 (r + n) s (by omega) := by
    congr 1
  have hTail : ((((MonObj.one (X := A)).f 0 ⊗ₘ (𝟙 A : A ⟶ A).f (r + n))) ≫
      (HomologicalComplex.ιTensorObj A A 0 (r + n) s (by omega) ≫
        (MonObj.mul (X := A)).f s)) =
      (HomologicalComplex.ιTensorObj (𝟙_ (CochainComplex (ModuleCat R) ℤ)) A
        0 (r + n) s (by omega) ≫
        ((HomologicalComplex.tensorHom (MonObj.one (X := A)) (𝟙 A)).f s ≫
          (MonObj.mul (X := A)).f s)) := by
    rw [← Category.assoc, ← hIotaOne, Category.assoc]
  have hIdx : (HomComplex.Cochain.ofHom (MonObj.one (X := A))).v 0 (0 + 0) rfl =
      (HomComplex.Cochain.ofHom (MonObj.one (X := A))).v 0 0 (add_zero 0) := by
    congr 1
  have hInner := tensor_one_desc_singleton f r s (by omega : r + (0 + n) = s)
  have hSignInner : (n * 0).negOnePow = (1 : ℤˣ) := by simp
  have hUnitorBridge : (λ_ C).inv.f r = (HomologicalComplex.leftUnitor' C).inv r := rfl
  have hIotaBridge : (HomologicalComplex.tensorUnit (ModuleCat R) (ComplexShape.up ℤ)).ιTensorObj
      C 0 r r (by omega) =
      HomologicalComplex.ιMapBifunctor (𝟙_ (CochainComplex (ModuleCat R) ℤ)) C
        (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ) 0 r r (zero_add r) := rfl
  have hCollapse : (HomologicalComplex.ιMapBifunctor (𝟙_ (CochainComplex (ModuleCat R) ℤ)) C
        (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ) 0 r r (zero_add r) ≫
      (((HomComplex.Cochain.ofHom (MonObj.one (X := A))).tensor f).v r s
        (by omega : r + (0 + n) = s) ≫ (MonObj.mul (X := A)).f s)) =
      (((n * 0).negOnePow •
        ((HomComplex.Cochain.ofHom (MonObj.one (X := A))).v 0 (0 + 0) rfl ⊗ₘ
          f.v r (r + n) rfl) ≫
        HomologicalComplex.ιTensorObj A A (0 + 0) (r + n) s (by omega)) ≫
        (MonObj.mul (X := A)).f s) := by
    rw [← Category.assoc, hInner.1]
  have hFactor : (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (𝟙_ (ModuleCat R))).inv ≫ (MonObj.one (X := A)).f 0) ⊗ₘ f.v r (r + n) rfl) =
      ((𝟙 (𝟙_ (ModuleCat R)) ⊗ₘ f.v r (r + n) rfl) ≫
        (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (𝟙_ (ModuleCat R))).inv ≫ (MonObj.one (X := A)).f 0) ⊗ₘ
          𝟙 (A.X (r + n)))) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [Category.id_comp, Category.comp_id]
  have hSplit : ((((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (𝟙_ (ModuleCat R))).inv ≫ (MonObj.one (X := A)).f 0) ⊗ₘ 𝟙 (A.X (r + n)))) =
      (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (𝟙_ (ModuleCat R))).inv ⊗ₘ 𝟙 (A.X (r + n))) ≫
        ((MonObj.one (X := A)).f 0 ⊗ₘ 𝟙 (A.X (r + n)))) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [Category.comp_id]
  rw [eConv]
  rw [HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain _ _ _
    (show (0 + n) + 0 = 0 + n from add_zero _)]
  simp only [HomComplex.Cochain.comp_zero_cochain_v,
    HomComplex.Cochain.zero_cochain_comp_v, HomComplex.Cochain.ofHom_v] at hC_v hA_v ⊢
  rw [hMid_v] at ⊢
  rw [HomComplex.Cochain.zero_cochain_comp_v] at ⊢
  rw [HomComplex.Cochain.ofHom_v] at ⊢
  rw [hWhiskerC] at ⊢
  simp only [← Category.assoc] at ⊢
  rw [hC_v] at ⊢
  simp only [Category.assoc] at ⊢
  rw [hUnitorBridge] at ⊢
  rw [hU] at ⊢
  simp only [Category.assoc] at ⊢
  rw [hIotaBridge] at ⊢
  rw [hCollapse] at ⊢
  rw [hSignInner, one_smul] at ⊢
  rw [hIdx, hOneV] at ⊢
  nth_rewrite 2 [← Category.assoc] at ⊢
  rw [MonoidalCategory.whiskerRight_comp_tensorHom_assoc] at ⊢
  rw [hFactor] at ⊢
  rw [hSplit] at ⊢
  simp only [Category.assoc] at ⊢
  rw [← hIdA] at ⊢
  rw [hIotaIdx] at ⊢
  rw [hTail, hWhiskerA] at ⊢
  rw [hA_v] at ⊢
  rw [hIdA] at ⊢
  subst hrs
  rw [hLamBridge] at ⊢
  rw [hStep] at ⊢
  rw [hS] at ⊢
  rw [hWhiskerF] at ⊢
  rw [MonoidalCategory.leftUnitor_naturality] at ⊢
  simp at ⊢

omit [ComonObj C] in
/-- Let R be a commutative ring and A a dg R-algebra, with integer grading. Assume all graded tensor
coproducts exist, tensoring preserves zero on both sides, tensoring commutes with the coproducts
used for reassociation, and fourfold summand inclusions determine maps. Write I for the
tensor-unit complex concentrated in degree zero and η_A:I→A for the algebra unit. Let C be any
integer cochain complex and g:C→A have degree n. For q≠0 and any p, (-1)^{0·p}(g_p⊗(η_A)_q)=0 as
a map C_p⊗I_q→A_{p+n}⊗A_q. -/
private theorem tensor_summand_vanish_one {n : ℤ}
    (g : HomComplex.Cochain C A n) (i₁ i₂ : ℤ) (hi₂ : i₂ ≠ 0) :
    (0 * i₁).negOnePow •
      (g.v i₁ (i₁ + n) rfl ⊗ₘ
        (HomComplex.Cochain.ofHom (MonObj.one (X := A))).v i₂ (i₂ + 0) rfl) = 0 := by
  have h0 : (HomComplex.Cochain.ofHom (MonObj.one (X := A))).v i₂ (i₂ + 0) rfl = 0 :=
    one_vanish_general i₂ (i₂ + 0) rfl hi₂
  rw [h0, MonoidalPreadditive.tensor_zero]
  simp

omit [ComonObj C] in
/-- Let R be a commutative ring and A a dg R-algebra, with integer grading. Assume all graded tensor
coproducts exist, tensoring preserves zero on both sides, tensoring commutes with the coproducts
used for reassociation, and fourfold summand inclusions determine maps. Write I for the
tensor-unit complex concentrated in degree zero and η_A:I→A for the algebra unit. Let C be any
integer cochain complex and g:C→A have degree n. If r+n+0=s, p+q=r and q≠0, then
ι^{C,I}_{p,q,r}≫(g⊗η_A)_{r,s}=0. The inclusion is into (C⊗I)_r, and the tensor component maps to
(A⊗A)_s. -/
private theorem tensor_support_collapse_one {n : ℤ}
    (g : HomComplex.Cochain C A n) (r s : ℤ) (hrs : r + (n + 0) = s)
    (i₁ i₂ : ℤ) (hij : i₁ + i₂ = r) (hi₂ : i₂ ≠ 0) :
    HomologicalComplex.ιMapBifunctor C (𝟙_ (CochainComplex (ModuleCat R) ℤ))
        (curriedTensor (ModuleCat R))
        (ComplexShape.up ℤ) i₁ i₂ r hij ≫
      (HomComplex.Cochain.tensor g
        (HomComplex.Cochain.ofHom (MonObj.one (X := A)))).v
        r s hrs = 0 := by
  rw [HomComplex.Cochain.tensor_v, HomologicalComplex.ι_mapBifunctorDesc]
  dsimp only
  have h0 : (HomComplex.Cochain.ofHom (MonObj.one (X := A))).v i₂ (i₂ + 0) rfl = 0 :=
    one_vanish_general i₂ (i₂ + 0) rfl hi₂
  rw [h0, MonoidalPreadditive.tensor_zero]
  simp

omit [ComonObj C] in
/-- Let R be a commutative ring and A a dg R-algebra, with integer grading. Assume all graded tensor
coproducts exist, tensoring preserves zero on both sides, tensoring commutes with the coproducts
used for reassociation, and fourfold summand inclusions determine maps. Write I for the
tensor-unit complex concentrated in degree zero and η_A:I→A for the algebra unit. Let C be any
integer cochain complex and g:C→A have degree n. For r+n+0=s,
ι^{C,I}_{r,0,r}≫(g⊗η_A)_{r,s}=(g_r⊗(η_A)_0)≫ι^A_{r+n,0,s}, with sign (-1)^{0·r}=1. For every
p+q=r with q≠0, ι^{C,I}_{p,q,r}≫(g⊗η_A)_{r,s}=0. The target inclusions belong to (A⊗A)_s. -/
private theorem tensor_desc_singleton_one {n : ℤ}
    (g : HomComplex.Cochain C A n) (r s : ℤ) (hrs : r + (n + 0) = s) :
    (HomologicalComplex.ιMapBifunctor C (𝟙_ (CochainComplex (ModuleCat R) ℤ))
        (curriedTensor (ModuleCat R))
        (ComplexShape.up ℤ) r 0 r (add_zero r) ≫
      (HomComplex.Cochain.tensor g
        (HomComplex.Cochain.ofHom (MonObj.one (X := A)))).v
        r s hrs =
      (0 * r).negOnePow •
        (g.v r (r + n) rfl ⊗ₘ
          (HomComplex.Cochain.ofHom (MonObj.one (X := A))).v 0 (0 + 0) rfl) ≫
        HomologicalComplex.ιTensorObj A A (r + n) (0 + 0) s (by omega)) ∧
    (∀ (i₁ i₂ : ℤ) (hij : i₁ + i₂ = r) (_hi₂ : i₂ ≠ 0),
      HomologicalComplex.ιMapBifunctor C (𝟙_ (CochainComplex (ModuleCat R) ℤ))
        (curriedTensor (ModuleCat R))
        (ComplexShape.up ℤ) i₁ i₂ r hij ≫
      (HomComplex.Cochain.tensor g
        (HomComplex.Cochain.ofHom (MonObj.one (X := A)))).v
        r s hrs = 0) := by
  exact ⟨by rw [HomComplex.Cochain.tensor_v, HomologicalComplex.ι_mapBifunctorDesc],
    fun i₁ i₂ hij hi₂ => tensor_support_collapse_one g r s hrs i₁ i₂ hij hi₂⟩

/-- Let R be a commutative ring, C a dg R-coalgebra and A a dg R-algebra, both integer cochain
complexes. Assume all graded tensor coproducts exist, tensoring preserves zero on both sides,
tensoring commutes with the coproducts used for reassociation, and fourfold summand inclusions
determine maps. Write e=ε_C≫η_A:C→A for the degree-zero cochain formed from the coalgebra counit
and algebra unit. For a degree-n cochain f:C→A, f⊗e=(id_C⊗ε_C)≫((id_C≫f)⊗η_A) as degree-(n+0)
cochains C⊗C→A⊗A. The intermediate source is C⊗I, with I the tensor-unit complex concentrated in
degree zero. -/
private theorem tensor_f_convOne_middle_interchange {n : ℤ}
    (f : HomComplex.Cochain C A n) :
    HomComplex.Cochain.tensor f (convOne (R := R) (C := C) (A := A)) =
      ((HomComplex.Cochain.ofHom
        (HomologicalComplex.tensorHom (𝟙 C) (ComonObj.counit (X := C)))).comp
        (HomComplex.Cochain.tensor
          ((HomComplex.Cochain.ofHom (𝟙 C)).comp f (zero_add n))
          (HomComplex.Cochain.ofHom (MonObj.one (X := A))))
        (zero_add (n + 0))) := by
  have hConv : (convOne (R := R) (C := C) (A := A)) =
      (HomComplex.Cochain.ofHom (ComonObj.counit (X := C))).comp
        (HomComplex.Cochain.ofHom (MonObj.one (X := A))) (zero_add 0) := rfl
  have e_pre := HomComplex.Cochain.ofHom_tensorHom_comp_tensor
    (𝟙 C) (ComonObj.counit (X := C))
    f (HomComplex.Cochain.ofHom (MonObj.one (X := A)))
  rw [← hConv] at e_pre
  have hid : ((HomComplex.Cochain.ofHom (𝟙 C)).comp f (zero_add n)) = f := by
    rw [HomComplex.Cochain.id_comp]
  rw [hid] at e_pre ⊢
  exact e_pre.symm

/-- Let R be a commutative ring, C a dg R-coalgebra and A a dg R-algebra, both integer cochain
complexes. Assume all graded tensor coproducts exist, tensoring preserves zero on both sides,
tensoring commutes with the coproducts used for reassociation, and fourfold summand inclusions
determine maps. Write e=ε_C≫η_A:C→A for the degree-zero cochain formed from the coalgebra counit
and algebra unit. For every homogeneous degree-n cochain f:C→A, f⋆e=f after identifying n+0 with
n. Convolution is f⋆g=μ_A(f⊗g)Δ_C; the degree-zero right factor contributes Koszul sign one. -/
theorem conv_one_right {n : ℤ} (f : HomComplex.Cochain C A n) :
    cast (congrArg (HomComplex.Cochain C A) (add_zero n))
      (conv f (convOne (R := R) (C := C) (A := A))) = f := by
  apply HomComplex.Cochain.ext
  intro r s hrs
  rw [cochain_cast_v (add_zero n)]
  have eConv := conv_eq f (convOne (R := R) (C := C) (A := A))
  have hMid := tensor_f_convOne_middle_interchange f
  have hid : ((HomComplex.Cochain.ofHom (𝟙 C)).comp f (zero_add n)) = f := by
    rw [HomComplex.Cochain.id_comp]
  rw [hid] at hMid
  have hMid_v := HomComplex.Cochain.congr_v hMid r s (by omega : r + (n + 0) = s)
  have hTrans := conv_one_right_transport f r s (by omega)
  obtain ⟨hC_v, hA_v, _, hU, _⟩ := hTrans
  have hWhiskerCR : (HomologicalComplex.tensorHom
      (𝟙 C) (ComonObj.counit (X := C))).f r =
      (C ◁ ComonObj.counit (X := C)).f r := rfl
  have hInner := tensor_desc_singleton_one f r s (by omega : r + (n + 0) = s)
  have hSignInner : (0 * r).negOnePow = (1 : ℤˣ) := by simp
  have hUnitorBridge : (ρ_ C).inv.f r = (HomologicalComplex.rightUnitor' C).inv r := rfl
  have hIotaBridge : HomologicalComplex.ιTensorObj C
      (HomologicalComplex.tensorUnit (ModuleCat R) (ComplexShape.up ℤ))
      r 0 r (by omega) =
      HomologicalComplex.ιMapBifunctor C (𝟙_ (CochainComplex (ModuleCat R) ℤ))
        (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ) r 0 r (add_zero r) := rfl
  have hCollapse : (HomologicalComplex.ιMapBifunctor C (𝟙_ (CochainComplex (ModuleCat R) ℤ))
        (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ) r 0 r (add_zero r) ≫
      ((HomComplex.Cochain.tensor f
        (HomComplex.Cochain.ofHom (MonObj.one (X := A)))).v r s
        (by omega : r + (n + 0) = s) ≫ (MonObj.mul (X := A)).f s)) =
      (((0 * r).negOnePow •
        (f.v r (r + n) rfl ⊗ₘ
          (HomComplex.Cochain.ofHom (MonObj.one (X := A))).v 0 (0 + 0) rfl) ≫
        HomologicalComplex.ιTensorObj A A (r + n) (0 + 0) s (by omega)) ≫
        (MonObj.mul (X := A)).f s) := by
    rw [← Category.assoc, hInner.1]
  have hWhiskerA : (HomologicalComplex.tensorHom
      (𝟙 A) (MonObj.one (X := A))).f s =
      (A ◁ MonObj.one (X := A)).f s := rfl
  have hOneV : (HomComplex.Cochain.ofHom (MonObj.one (X := A))).v 0 0 (add_zero 0) =
      (MonObj.one (X := A)).f 0 :=
    HomComplex.Cochain.ofHom_v _ _
  have hIotaOne := HomologicalComplex.ιTensorObj_tensorHom
    (𝟙 A) (MonObj.one (X := A)) (r + n) 0 s (by omega)
  have hIdA : ((𝟙 A : A ⟶ A).f (r + n)) = 𝟙 (A.X (r + n)) := rfl
  have hIdx : (HomComplex.Cochain.ofHom (MonObj.one (X := A))).v 0 (0 + 0) rfl =
      (HomComplex.Cochain.ofHom (MonObj.one (X := A))).v 0 0 (add_zero 0) := by
    congr 1
  have hIotaIdx : HomologicalComplex.ιTensorObj A A (r + n) (0 + 0) s (by omega) =
      HomologicalComplex.ιTensorObj A A (r + n) 0 s (by omega) := by
    congr 1
  have hFactor : (((f.v r (r + n) rfl ⊗ₘ
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (𝟙_ (ModuleCat R))).inv ≫ (MonObj.one (X := A)).f 0)))) =
      (((f.v r (r + n) rfl ⊗ₘ 𝟙 (𝟙_ (ModuleCat R))) ≫
        ((𝟙 (A.X (r + n))) ⊗ₘ
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (𝟙_ (ModuleCat R))).inv ≫ (MonObj.one (X := A)).f 0)))) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [Category.comp_id, Category.id_comp]
  have hSplit : ((((𝟙 (A.X (r + n))) ⊗ₘ
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (𝟙_ (ModuleCat R))).inv ≫ (MonObj.one (X := A)).f 0)))) =
      ((((𝟙 (A.X (r + n))) ⊗ₘ
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (𝟙_ (ModuleCat R))).inv) ≫
        ((𝟙 (A.X (r + n))) ⊗ₘ (MonObj.one (X := A)).f 0))) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [Category.comp_id]
  have hTail : ((((((𝟙 A : A ⟶ A).f (r + n) ⊗ₘ (MonObj.one (X := A)).f 0))) ≫
      (HomologicalComplex.ιTensorObj A A (r + n) 0 s (by omega) ≫
        (MonObj.mul (X := A)).f s))) =
      (HomologicalComplex.ιTensorObj A (𝟙_ (CochainComplex (ModuleCat R) ℤ))
        (r + n) 0 s (by omega) ≫
        ((HomologicalComplex.tensorHom (𝟙 A) (MonObj.one (X := A))).f s ≫
          (MonObj.mul (X := A)).f s)) := by
    rw [← Category.assoc, ← hIotaOne, Category.assoc]
  have hLamBridge : (ρ_ A).hom.f s = (HomologicalComplex.rightUnitor A).hom.f s := rfl
  have hStep : (HomologicalComplex.ιTensorObj A (𝟙_ (CochainComplex (ModuleCat R) ℤ))
        (r + n) 0 (r + n) (by omega) ≫
        (HomologicalComplex.rightUnitor A).hom.f (r + n)) =
      (((A.X (r + n) ◁ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (𝟙_ (ModuleCat R))).hom) ≫ (ρ_ (A.X (r + n))).hom)) :=
    HomologicalComplex.ιTensorObj_rightUnitor_hom A (r + n)
  have hWhiskerS : ((A.X (r + n)) ◁
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (𝟙_ (ModuleCat R))).hom) =
      (𝟙 (A.X (r + n)) ⊗ₘ
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (𝟙_ (ModuleCat R))).hom) := rfl
  have hS : (((((𝟙 (A.X (r + n))) ⊗ₘ
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (𝟙_ (ModuleCat R))).inv) ≫
      (((A.X (r + n)) ◁ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (𝟙_ (ModuleCat R))).hom) ≫ (ρ_ (A.X (r + n))).hom))) =
      (ρ_ (A.X (r + n))).hom) := by
    rw [hWhiskerS, ← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom,
      Iso.inv_hom_id]
    simp
  have hWhiskerF : ((f.v r (r + n) rfl ⊗ₘ 𝟙 (𝟙_ (ModuleCat R)))) =
      ((f.v r (r + n) rfl ▷ 𝟙_ (ModuleCat R))) := rfl
  rw [eConv]
  rw [HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain _ _ _
    (show (n + 0) + 0 = n + 0 from add_zero _)]
  simp only [HomComplex.Cochain.comp_zero_cochain_v,
    HomComplex.Cochain.zero_cochain_comp_v, HomComplex.Cochain.ofHom_v] at hC_v hA_v ⊢
  rw [hMid_v] at ⊢
  rw [HomComplex.Cochain.zero_cochain_comp_v] at ⊢
  rw [HomComplex.Cochain.ofHom_v] at ⊢
  rw [hWhiskerCR] at ⊢
  simp only [← Category.assoc] at ⊢
  rw [hC_v] at ⊢
  simp only [Category.assoc] at ⊢
  rw [hUnitorBridge] at ⊢
  rw [hU] at ⊢
  simp only [Category.assoc] at ⊢
  rw [hIotaBridge] at ⊢
  rw [hCollapse] at ⊢
  rw [hSignInner, one_smul] at ⊢
  rw [hIdx, hOneV] at ⊢
  nth_rewrite 2 [← Category.assoc] at ⊢
  rw [MonoidalCategory.whiskerLeft_comp_tensorHom_assoc] at ⊢
  rw [hFactor] at ⊢
  rw [hSplit] at ⊢
  simp only [Category.assoc] at ⊢
  rw [← hIdA] at ⊢
  rw [hIotaIdx] at ⊢
  rw [hTail, hWhiskerA] at ⊢
  rw [hA_v] at ⊢
  rw [hIdA] at ⊢
  subst hrs
  rw [hLamBridge] at ⊢
  rw [hStep] at ⊢
  rw [hS] at ⊢
  rw [hWhiskerF] at ⊢
  rw [MonoidalCategory.rightUnitor_naturality] at ⊢
  simp at ⊢

end CochainComplex
