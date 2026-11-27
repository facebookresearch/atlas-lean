/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.Cyclic
public import MathlibExt.Algebra.Homology.Embedding.PositiveNat
public import Mathlib.Algebra.Homology.Embedding.Restriction

/-!
# Adjacent multiplication and the bar augmentation

Let k be a commutative ring and A a nonunital associative ring with a
k-module structure and k-bilinear multiplication. The bar complex P has
P_n = A ⊗[k] A^{⊗(n+1)}. Its differential from P_{n+1} to P_n is the
alternating sum of the n+2 adjacent multiplications in an ordered word of
length n+3. Thus d_1(a ⊗ b ⊗ c) = ab ⊗ c − a ⊗ bc.

The augmentation P_0 → A multiplies its two factors, and ε d_1 = 0.
The module category has carrier universe max{u,v} for k : Type u and
A : Type v; the augmentation target is A lifted to that same universe.

Reference: J.-L. Loday, Cyclic Homology, §1.1, for the adjacent-product
bar differential.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct

universe u v

namespace ModuleCat.Algebra.Hochschild.AdjacentBar

variable (k : Type u) (A : Type v) [CommRing k] [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]

/-- For a commutative ring k and a nonunital associative ring A with
k-bilinear multiplication, the bar chain complex over k has
P_n = A ⊗[k] A^{⊗(n+1)}. Its boundary alternates the adjacent
multiplications of an ordered word. It is the positive-degree part of the
b′ complex, with degree n+1 placed in bar degree n. -/
def underlyingBar : ChainComplex (ModuleCat.{max u v} k) ℕ :=
  (ModuleCat.Algebra.Hochschild.NonUnital.bPrimeComplex k A).restriction
    ComplexShape.positiveNatEmbedding

/-- For a nonunital associative ring A with k-bilinear multiplication over
a commutative ring k, the degree-n object of its bar complex is the
k-module A ⊗[k] A^{⊗(n+1)}. Hence an elementary bar chain has n+2 ordered
algebra factors. -/
theorem underlyingBar_X (n : ℕ) :
    (underlyingBar k A).X n = ModuleCat.of k (A ⊗[k] TensorPower k (n + 1) A) := rfl

/-- For a commutative ring k and a nonunital associative k-bilinear ring A,
the boundary P_{n+1} → P_n of the bar complex is
∑_{i=0}^{n+1} (−1)^i δ_i, where δ_i multiplies positions i and i+1
of the length-(n+3) word and leaves all other positions in order. -/
theorem underlyingBar_d (n : ℕ) :
    (underlyingBar k A).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        ModuleCat.Algebra.Hochschild.NonUnital.regularFace k A (n + 1) i.castSucc :=
  ModuleCat.Algebra.Hochschild.NonUnital.bPrimeComplex_d k A (n + 1)

/-- For a commutative ring k and a nonunital associative k-bilinear ring A,
the degree-zero object A ⊗[k] A^{⊗0} of the b′ complex is linearly
equivalent to A. Under A^{⊗0} ≃ k this is the right unit isomorphism
A ⊗[k] k ≃ A, sending a ⊗ r to r • a. -/
def underlyingBarZeroCoordinate :
    (ModuleCat.Algebra.Hochschild.NonUnital.bPrimeComplex k A).X 0 ≃ₗ[k] A :=
  (TensorProduct.congr (LinearEquiv.refl k A) (TensorPower.zeroEquiv k A)).trans
    (TensorProduct.rid k A)

/-- For a commutative ring k and a nonunital associative k-bilinear ring A,
the bar augmentation is the k-linear multiplication map
ε : P_0 = A ⊗[k] A → A, with ε(a ⊗ b) = ab. -/
def underlyingBarAugmentationLinear : (underlyingBar k A).X 0 →ₗ[k] A :=
  (underlyingBarZeroCoordinate k A).toLinearMap.comp
    ((ModuleCat.Algebra.Hochschild.NonUnital.bPrimeComplex k A).d 1 0).hom

/-- For k : Type u a commutative ring and A : Type v a nonunital
associative ring with k-bilinear multiplication, multiplication defines
the bar augmentation P_0 → ULift A in ModuleCat at universe max{u,v}.
It sends a ⊗ b to the lift of ab. -/
def underlyingBarAugmentation :
    (underlyingBar k A).X 0 ⟶ ModuleCat.of k (ULift.{max u v} A) :=
  ModuleCat.ofHom ((ULift.moduleEquiv.symm.toLinearMap : A →ₗ[k] ULift.{max u v} A).comp
    (underlyingBarAugmentationLinear k A))

/-- For a commutative ring k and a nonunital associative k-bilinear ring A,
the unit isomorphism A ⊗[k] A^{⊗0} ≃ A sends
a ⊗ tprod(z) to a for every empty family z : Fin 0 → A. -/
theorem underlyingBarZeroCoordinate_tprod (a : A) (z : Fin 0 → A) :
    underlyingBarZeroCoordinate k A (a ⊗ₜ[k] PiTensorProduct.tprod k z) = a := by
  change (TensorProduct.rid k A)
    ((TensorProduct.congr (LinearEquiv.refl k A) (TensorPower.zeroEquiv k A))
      (a ⊗ₜ[k] PiTensorProduct.tprod k z)) = a
  rw [TensorProduct.congr_tmul]
  change (TensorProduct.rid k A) (a ⊗ₜ[k] (PiTensorProduct.isEmptyEquiv (Fin 0))
    (PiTensorProduct.tprod k z)) = a
  rw [PiTensorProduct.isEmptyEquiv_apply_tprod, TensorProduct.rid_tmul, one_smul]

/-- For a commutative ring k and a nonunital associative k-bilinear ring A,
the multiplication augmentation sends
a ⊗ tprod(z) to a z_0 for every one-entry family z : Fin 1 → A. -/
theorem underlyingBarAugmentationLinear_tprod (a : A) (z : Fin 1 → A) :
    underlyingBarAugmentationLinear k A (a ⊗ₜ[k] PiTensorProduct.tprod k z) = a * z 0 := by
  change underlyingBarZeroCoordinate k A
    (((ModuleCat.Algebra.Hochschild.NonUnital.bPrimeComplex k A).d 1 0).hom
      (a ⊗ₜ[k] PiTensorProduct.tprod k z)) = _
  rw [ModuleCat.Algebra.Hochschild.NonUnital.bPrimeComplex_d_one_tprod,
    underlyingBarZeroCoordinate_tprod]

/-- For a commutative ring k and a nonunital associative ring A with
k-bilinear multiplication, the bar augmentation satisfies ε d_1 = 0.
On a three-factor tensor this is (ab)c − a(bc) = 0; the categorical
augmentation has the lifted k-module A as target. -/
theorem underlyingBar_d_augmentation :
    (underlyingBar k A).d 1 0 ≫ underlyingBarAugmentation k A = 0 := by
  let K : ChainComplex (ModuleCat.{max u v} k) ℕ :=
    ModuleCat.Algebra.Hochschild.NonUnital.bPrimeComplex k A
  let tail : K.X 0 ⟶ ModuleCat.of k (ULift.{max u v} A) :=
    ModuleCat.ofHom
      ((ULift.moduleEquiv.symm.toLinearMap : A →ₗ[k] ULift.{max u v} A).comp
        (underlyingBarZeroCoordinate k A).toLinearMap)
  have hd : (underlyingBar k A).d 1 0 = K.d 2 1 := by
    exact HomologicalComplex.restriction_d K ComplexShape.positiveNatEmbedding 1 0
  have haug : underlyingBarAugmentation k A = K.d 1 0 ≫ tail := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  have hfirst : (underlyingBar k A).d 1 0 ≫ underlyingBarAugmentation k A =
      K.d 2 1 ≫ (K.d 1 0 ≫ tail) :=
    congrArg₂ (fun (d : K.X 2 ⟶ K.X 1)
        (a : K.X 1 ⟶ ModuleCat.of k (ULift.{max u v} A)) => d ≫ a) hd haug
  have hassoc : K.d 2 1 ≫ (K.d 1 0 ≫ tail) =
      (K.d 2 1 ≫ K.d 1 0) ≫ tail :=
    (Category.assoc (K.d 2 1) (K.d 1 0) tail).symm
  have hzero : (K.d 2 1 ≫ K.d 1 0) ≫ tail = 0 :=
    (congrArg (fun d : K.X 2 ⟶ K.X 0 => d ≫ tail)
      (K.d_comp_d 2 1 0)).trans (zero_comp : (0 : K.X 2 ⟶ K.X 0) ≫ tail = 0)
  exact hfirst.trans (hassoc.trans hzero)

end ModuleCat.Algebra.Hochschild.AdjacentBar
