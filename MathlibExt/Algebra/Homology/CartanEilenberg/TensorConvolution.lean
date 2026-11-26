/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module


public import MathlibExt.Algebra.Homology.CartanEilenberg.Bicomplex
public import MathlibExt.Algebra.Homology.MonoidalPreservesColimits
public import MathlibExt.Algebra.Homology.TensorDifferentialDownNat
public import MathlibExt.Algebra.Homology.TensorHomFunctoriality
public import MathlibExt.Algebra.Homology.TensorUnitor
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

/-!
# Tensor convolution of a Cartan–Eilenberg bicomplex

Let R be commutative, K,L nonnegative R-module complexes and P a Cartan–Eilenberg resolution of
L. Tensoring K with every resolution-degree row of P gives a bicomplex. Its entry (a,q) is the
finite sum of Kᵢ ⊗ PTⱼ,ₐ over i+j=q.

The outer differential tensors the resolution differential with id_K. The inner differential is
d_K ⊗ id + (-1)^i id ⊗ d_row on an (i,j) summand, with the degree-zero terms omitted. Specified
maps in both factors give strict maps of these bicomplexes.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace HomologicalComplex

variable {R : Type u} [CommRing R]
variable {K K' K₁ K₂ K₃ L L' L₁ L₂ L₃ :
  ChainComplex (ModuleCat.{u} R) ℕ}

/-- Let R be a commutative ring, K,L nonnegative chain complexes of R-modules, and P a
Cartan–Eilenberg resolution of L. The bicomplex has resolution index a and inner tensor degree
q. For each a, its row is the ordinary tensor complex K ⊗ P.bicomplex.Xₐ. The degree-q entry is
the finite direct sum of Kᵢ ⊗ PTⱼ,ₐ over i+j=q, with both axes shaped as down-ℕ. -/
noncomputable def kunnethCEBicomplex (K : ChainComplex (ModuleCat.{u} R) ℕ)
    {L : ChainComplex (ModuleCat.{u} R) ℕ}
    (P : CartanEilenbergResolution L) :
    HomologicalComplex₂ (ModuleCat.{u} R)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  ((tensorLeft K).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    P.bicomplex

@[simp]
theorem kunnethCEBicomplex_X (K : ChainComplex (ModuleCat.{u} R) ℕ)
    {L : ChainComplex (ModuleCat.{u} R) ℕ}
    (P : CartanEilenbergResolution L) (p : ℕ) :
    (kunnethCEBicomplex K P).X p =
      tensorObj K (P.bicomplex.X p) :=
  rfl

@[simp]
theorem kunnethCEBicomplex_d (K : ChainComplex (ModuleCat.{u} R) ℕ)
    {L : ChainComplex (ModuleCat.{u} R) ℕ}
    (P : CartanEilenbergResolution L) (p p' : ℕ) :
    (kunnethCEBicomplex K P).d p p' =
      tensorHom (𝟙 K) (P.bicomplex.d p p') :=
  rfl

@[simp]
theorem kunnethCEBicomplex_X_X (K : ChainComplex (ModuleCat.{u} R) ℕ)
    {L : ChainComplex (ModuleCat.{u} R) ℕ}
    (P : CartanEilenbergResolution L) (p q : ℕ) :
    ((kunnethCEBicomplex K P).X p).X q =
      (tensorObj K (P.bicomplex.X p)).X q :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Let R be commutative, f : K → K′ a map of nonnegative R-module complexes, and g : P.bicomplex →
P′.bicomplex a specified map of Cartan–Eilenberg bicomplexes. Tensoring f and each row map of g
gives a strict map of the two tensor-convolution bicomplexes. -/
noncomputable def kunnethCEBicomplexMap
    {P : CartanEilenbergResolution L}
    {P' : CartanEilenbergResolution L'}
    (f : K ⟶ K') (g : P.bicomplex ⟶ P'.bicomplex) :
    kunnethCEBicomplex K P ⟶ kunnethCEBicomplex K' P' where
  f p := tensorHom f (g.f p)
  comm' p p' _ := by
    rw [kunnethCEBicomplex_d, kunnethCEBicomplex_d]
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
    simp only [Category.comp_id, Category.id_comp]
    rw [g.comm p p']

@[simp]
theorem kunnethCEBicomplexMap_f
    {P : CartanEilenbergResolution L}
    {P' : CartanEilenbergResolution L'}
    (f : K ⟶ K') (g : P.bicomplex ⟶ P'.bicomplex) (p : ℕ) :
    (kunnethCEBicomplexMap f g).f p = tensorHom f (g.f p) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem kunnethCEBicomplexMap_id
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    {L : ChainComplex (ModuleCat.{u} R) ℕ}
    (P : CartanEilenbergResolution L) :
    kunnethCEBicomplexMap (𝟙 K) (𝟙 P.bicomplex) =
      𝟙 (kunnethCEBicomplex K P) := by
  apply Hom.ext
  funext p
  exact tensorHom_id_id K (P.bicomplex.X p)

set_option backward.isDefEq.respectTransparency false in
@[reassoc, simp]
theorem kunnethCEBicomplexMap_comp
    {P₁ : CartanEilenbergResolution L₁}
    {P₂ : CartanEilenbergResolution L₂}
    {P₃ : CartanEilenbergResolution L₃}
    (f₁ : K₁ ⟶ K₂) (f₂ : K₂ ⟶ K₃)
    (g₁ : P₁.bicomplex ⟶ P₂.bicomplex)
    (g₂ : P₂.bicomplex ⟶ P₃.bicomplex) :
    kunnethCEBicomplexMap f₁ g₁ ≫
        kunnethCEBicomplexMap f₂ g₂ =
      kunnethCEBicomplexMap (f₁ ≫ f₂) (g₁ ≫ g₂) := by
  apply Hom.ext
  funext p
  exact tensorHom_comp_tensorHom f₁ f₂ (g₁.f p) (g₂.f p)

set_option backward.isDefEq.respectTransparency false in
/-- Let R be a commutative ring, K,L nonnegative chain complexes of R-modules, and P a
Cartan–Eilenberg resolution of L. The bicomplex has resolution index a and inner tensor degree
q. On a homogeneous inner summand Kᵢ ⊗ PTⱼ,ₐ₊₁ with i+j=q, the resolution differential a+1 → a
is id_{Kᵢ} ⊗ d_PTⱼ^{a+1,a}, followed by its injection into the degree-q row. -/
@[reassoc]
theorem ιTensorObj_comp_kunnethCEBicomplex_d
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    {L : ChainComplex (ModuleCat.{u} R) ℕ}
    (P : CartanEilenbergResolution L)
    (p i j q : ℕ) (hij : i + j = q) :
    ιTensorObj K (P.bicomplex.X (p + 1)) i j q hij ≫
        ((kunnethCEBicomplex K P).d (p + 1) p).f q =
      (𝟙 (K.X i) ⊗ₘ ((P.bicomplex.d (p + 1) p).f j)) ≫
        ιTensorObj K (P.bicomplex.X p) i j q hij := by
  simpa only [kunnethCEBicomplex_d, HomologicalComplex.id_f] using
    ιTensorObj_tensorHom
      (𝟙 K) (P.bicomplex.d (p + 1) p) i j q hij

set_option backward.isDefEq.respectTransparency false in
/-- Let R be a commutative ring, K,L nonnegative chain complexes of R-modules, and P a
Cartan–Eilenberg resolution of L. The bicomplex has resolution index a and inner tensor degree
q. On the inner summand of degrees i,j with i+j=n+1, the inner differential is d_K ⊗ id plus
(-1)^i times id ⊗ d_row. The first term is zero if i=0 and the second is zero if j=0; otherwise
they inject into degrees (i-1,j) and (i,j-1) of total n. -/
theorem ιTensorObj_comp_kunnethCEBicomplex_X_d
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    {L : ChainComplex (ModuleCat.{u} R) ℕ}
    (P : CartanEilenbergResolution L)
    (p i j n : ℕ) (h : i + j = n + 1) :
    ιTensorObj K (P.bicomplex.X p) i j (n + 1) h ≫
        ((kunnethCEBicomplex K P).X p).d (n + 1) n =
      (if hi : i = 0 then
          (0 : K.X i ⊗ (P.bicomplex.X p).X j ⟶
            ((kunnethCEBicomplex K P).X p).X n)
        else
          (K.d i (i - 1) ⊗ₘ 𝟙 ((P.bicomplex.X p).X j)) ≫
            ιTensorObj K (P.bicomplex.X p) (i - 1) j n (by omega)) +
      (if hj : j = 0 then
          (0 : K.X i ⊗ (P.bicomplex.X p).X j ⟶
            ((kunnethCEBicomplex K P).X p).X n)
        else
          ((-1 : ℤ) ^ i) •
            ((𝟙 (K.X i) ⊗ₘ (P.bicomplex.X p).d j (j - 1)) ≫
              ιTensorObj K (P.bicomplex.X p) i (j - 1) n (by omega))) := by
  exact ιTensorObj_comp_d_down_nat K (P.bicomplex.X p) i j n h

end HomologicalComplex

end
