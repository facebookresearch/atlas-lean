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

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.ComplexShapeSigns
public import Mathlib.CategoryTheory.Monoidal.Preadditive

import MathlibExt.Algebra.Homology.TensorHomFunctoriality
import MathlibExt.Algebra.Homology.TensorUnitor

/-!
# Heterogeneous tensor product of cochains

For cochain complexes in a preadditive monoidal category, this module supplies
the canonical heterogeneous tensor product of homogeneous cochains on distinct
factors, with the Koszul sign, both functoriality directions, and associator
coherence.

For `f : Cochain C₁ A₁ m` and `g : Cochain C₂ A₂ n`, the canonical product
`Cochain.tensor f g : Cochain (C₁ ⊗ C₂) (A₁ ⊗ A₂) (m + n)` acts on the
`(i₁, i₂)`-summand (`i₁ + i₂ = r`) by the Koszul rule
`(f ⊗ g)(x ⊗ y) = (-1) ^ (n * i₁) • (f x ⊗ g y)`,
where the sign is `Int.negOnePow (n * i₁)` viewed in `ℤˣ` acting through the
ambient `ℤ`-linear structure on morphisms. Binary tensors require
`GradedObject.HasTensor` on the exact source/target graded pairs involved;
associativity additionally requires `HasGoodTensor₁₂Tensor` and
`HasGoodTensorTensor₂₃` on the exact source/target graded triples involved.
Complex-level tensor and associator instances follow from these graded
assumptions through the pinned `HomologicalComplex` monoidal API.

The public surface includes
`HomComplex.Cochain.tensor` with computation rule `Cochain.tensor_v`,
precomposition `Cochain.ofHom_tensorHom_comp_tensor`,
postcomposition `Cochain.tensor_comp_ofHom_tensorHom`, signed interchange
`Cochain.tensor_comp_tensor`, degree-zero functoriality `Cochain.tensor_ofHom`,
left additivity and zero, degree-preserving right-identity extension
`Cochain.tensorRightId`, associativity `Cochain.tensor_assoc` on six
independently named complexes, component Leibniz `Cochain.tensor_δ_v` for
`δ (tensor f g)`, and unitor transport
`Cochain.leftUnitor_inv_comp_tensor_ofHom_id_comp_leftUnitor` /
`Cochain.rightUnitor_inv_comp_tensor_ofHom_id_comp_rightUnitor`.
The same-source/target
specialization is `tensorCochain_eq_tensor` in
`MathlibExt/RingTheory/DifferentialGraded/TwistingCochain.lean`, not here.

## Primary source

Summand assembly, summand induction, and associator transport are the
pinned `HomologicalComplex` API: `mapBifunctorDesc`,
`mapBifunctor.hom_ext`, `mapBifunctor₁₂.ι_eq`, `mapBifunctor₂₃.ι_eq`, and
`ι_mapBifunctorAssociatorX_hom`, closed by
`MonoidalCategory.associator_naturality`. The Koszul sign follows the
pinned tensor-complex vertical sign `(up ℤ).ε`
(`ComplexShape.ε_up_ℤ`); see the grading record in
`MathlibExt/RingTheory/DifferentialGraded/TwistingCochain.lean`. The
same-source/target specialization is bridged downstream by
`tensorCochain_eq_tensor` there.

## Nonclaims

* No convolution product or unit law is defined or proved here.
* No totalization, twisting bijection, Eilenberg--Zilber/Alexander--Whitney,
  adjunction, or derived/Koszul/model claim.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

namespace CochainComplex

variable {C₁ C₂ A₁ A₂ : CochainComplex C ℤ}

namespace HomComplex.Cochain

variable [MonoidalCategory C]
  [(curriedTensor C).Additive] [∀ X₁, ((curriedTensor C).obj X₁).Additive]

/-- Canonical heterogeneous tensor product of homogeneous cochains, of degree
`m + n`. This is the single public tensor constructor in this module. -/
noncomputable def tensor {m n : ℤ}
    (f : Cochain C₁ A₁ m) (g : Cochain C₂ A₂ n)
    [GradedObject.HasTensor C₁.X C₂.X] [GradedObject.HasTensor A₁.X A₂.X] :
    Cochain (HomologicalComplex.tensorObj C₁ C₂)
      (HomologicalComplex.tensorObj A₁ A₂) (m + n) :=
  HomComplex.Cochain.mk fun r s hrs =>
    HomologicalComplex.mapBifunctorDesc (F := curriedTensor C)
      (c := ComplexShape.up ℤ) fun i₁ i₂ hij =>
      have h12 : i₁ + i₂ = r := hij
      (n * i₁).negOnePow •
        (f.v i₁ (i₁ + m) rfl ⊗ₘ g.v i₂ (i₂ + n) rfl) ≫
      HomologicalComplex.ιTensorObj A₁ A₂ (i₁ + m) (i₂ + n) s (by omega)

/-- Computation rule for the heterogeneous tensor product of cochains. This is
the intentional new simp rule of this module. -/
@[simp]
theorem tensor_v {m n : ℤ} (f : Cochain C₁ A₁ m)
    (g : Cochain C₂ A₂ n) (r s : ℤ) (hrs : r + (m + n) = s)
    [GradedObject.HasTensor C₁.X C₂.X] [GradedObject.HasTensor A₁.X A₂.X] :
    (tensor f g).v r s hrs =
      HomologicalComplex.mapBifunctorDesc (F := curriedTensor C)
        (c := ComplexShape.up ℤ) fun i₁ i₂ hij =>
        have h12 : i₁ + i₂ = r := hij
        (n * i₁).negOnePow •
          (f.v i₁ (i₁ + m) rfl ⊗ₘ g.v i₂ (i₂ + n) rfl) ≫
        HomologicalComplex.ιTensorObj A₁ A₂ (i₁ + m) (i₂ + n) s (by omega) := rfl

variable {B₁ B₂ : CochainComplex C ℤ}

/-- Precomposing a tensor product of cochains with a tensor product of complex
morphisms factors through the precomposed cochains. -/
theorem ofHom_tensorHom_comp_tensor {m n : ℤ}
    (φ₁ : B₁ ⟶ C₁) (φ₂ : B₂ ⟶ C₂)
    (f : Cochain C₁ A₁ m) (g : Cochain C₂ A₂ n)
    [GradedObject.HasTensor B₁.X B₂.X]
    [GradedObject.HasTensor C₁.X C₂.X] [GradedObject.HasTensor A₁.X A₂.X] :
    (ofHom (HomologicalComplex.tensorHom φ₁ φ₂)).comp
        (tensor f g) (zero_add (m + n)) =
      tensor ((ofHom φ₁).comp f (zero_add m))
        ((ofHom φ₂).comp g (zero_add n)) := by
  apply HomComplex.Cochain.ext
  intro r s hrs
  apply HomologicalComplex.mapBifunctor.hom_ext (c := ComplexShape.up ℤ)
  intro i₁ i₂ hh
  simp only [tensor_v, HomComplex.Cochain.zero_cochain_comp_v,
    HomComplex.Cochain.ofHom_v,
    HomologicalComplex.ι_mapBifunctorDesc,
    HomologicalComplex.ι_mapBifunctorMap_assoc,
    curriedTensor_map_app, curriedTensor_obj_map,
    Linear.comp_units_smul]
  simp only [← Category.assoc, ← MonoidalCategory.tensorHom_def,
    MonoidalCategory.tensorHom_comp_tensorHom]

/-- Postcomposing a tensor product of cochains with a tensor product of
complex morphisms factors through the postcomposed cochains. -/
theorem tensor_comp_ofHom_tensorHom {m n : ℤ}
    (f : Cochain C₁ A₁ m) (g : Cochain C₂ A₂ n)
    (φ₁ : A₁ ⟶ B₁) (φ₂ : A₂ ⟶ B₂)
    [GradedObject.HasTensor C₁.X C₂.X]
    [GradedObject.HasTensor A₁.X A₂.X] [GradedObject.HasTensor B₁.X B₂.X] :
    (tensor f g).comp (ofHom (HomologicalComplex.tensorHom φ₁ φ₂))
        (add_zero (m + n)) =
      tensor (f.comp (ofHom φ₁) (add_zero m))
        (g.comp (ofHom φ₂) (add_zero n)) := by
  apply HomComplex.Cochain.ext
  intro r s hrs
  apply HomologicalComplex.mapBifunctor.hom_ext (c := ComplexShape.up ℤ)
  intro i₁ i₂ hh
  simp only [tensor_v, HomComplex.Cochain.comp_zero_cochain_v,
    HomComplex.Cochain.ofHom_v,
    HomologicalComplex.ι_mapBifunctorDesc,
    HomologicalComplex.ι_mapBifunctorDesc_assoc,
    HomologicalComplex.ι_mapBifunctorMap,
    curriedTensor_map_app, curriedTensor_obj_map, Category.assoc,
    Linear.units_smul_comp]
  simp only [← Category.assoc,
    MonoidalCategory.tensorHom_comp_whiskerRight,
    MonoidalCategory.tensorHom_comp_whiskerLeft]

private theorem eqToHom_tensor_comp_ιTensorObj
    (K L : CochainComplex C ℤ)
    [GradedObject.HasTensor K.X L.X]
    {i₁ i₂ j₁ j₂ r : ℤ} (h₁ : i₁ = j₁) (h₂ : i₂ = j₂)
    (hi : i₁ + i₂ = r) (hj : j₁ + j₂ = r) :
    (eqToHom (congrArg (fun i => K.X i) h₁) ⊗ₘ
        eqToHom (congrArg (fun i => L.X i) h₂)) ≫
      HomologicalComplex.ιTensorObj K L j₁ j₂ r hj =
        HomologicalComplex.ιTensorObj K L i₁ i₂ r hi := by
  subst j₁
  subst j₂
  simp only [eqToHom_refl, MonoidalCategory.id_tensorHom_id,
    Category.id_comp]

/-- Tensoring degree-zero cochains induced by complex morphisms agrees with
the degree-zero cochain induced by their tensor product. -/
theorem tensor_ofHom
    {X₁ X₂ Y₁ Y₂ : CochainComplex C ℤ}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
    [GradedObject.HasTensor X₁.X X₂.X]
    [GradedObject.HasTensor Y₁.X Y₂.X] :
    tensor (ofHom f) (ofHom g) =
      ofHom (HomologicalComplex.tensorHom f g) := by
  apply HomComplex.Cochain.ext₀
  intro r
  rw [tensor_v, ofHom_v]
  apply HomologicalComplex.mapBifunctor.hom_ext (c := ComplexShape.up ℤ)
  intro i₁ i₂ hi
  have hij : i₁ + i₂ = r := hi
  rw [HomologicalComplex.ι_mapBifunctorDesc,
    HomologicalComplex.ι_mapBifunctorMap]
  simp only [zero_mul, Int.negOnePow_zero, one_smul, ofHom, ofHoms, mk_v,
    curriedTensor_map_app, curriedTensor_obj_map]
  rw [← MonoidalCategory.tensorHom_comp_tensorHom, Category.assoc]
  rw [eqToHom_tensor_comp_ιTensorObj Y₁ Y₂
    (add_zero i₁).symm (add_zero i₂).symm hij (by omega)]
  rw [MonoidalCategory.tensorHom_def, Category.assoc]

/-- Tensoring identity zero-cochains gives the identity zero-cochain. -/
@[simp]
theorem tensor_ofHom_id_id
    (X Y : CochainComplex C ℤ)
    [GradedObject.HasTensor X.X Y.X] :
    tensor (ofHom (𝟙 X)) (ofHom (𝟙 Y)) =
      ofHom (𝟙 (HomologicalComplex.tensorObj X Y)) := by
  rw [tensor_ofHom, HomologicalComplex.tensorHom_id_id]

/-- Heterogeneous tensor-of-composites interchange with Koszul sign
`(n₂ * m₁).negOnePow`. -/
theorem tensor_comp_tensor {m₁ n₁ m₂ n₂ : ℤ}
    (a₁ : Cochain C₁ A₁ m₁) (b₁ : Cochain A₁ B₁ n₁)
    (a₂ : Cochain C₂ A₂ m₂) (b₂ : Cochain A₂ B₂ n₂)
    [GradedObject.HasTensor C₁.X C₂.X] [GradedObject.HasTensor A₁.X A₂.X]
    [GradedObject.HasTensor B₁.X B₂.X] :
    (tensor a₁ a₂).comp (tensor b₁ b₂)
      (by omega : (m₁ + m₂) + (n₁ + n₂) = (m₁ + n₁) + (m₂ + n₂)) =
      (n₂ * m₁).negOnePow •
        tensor (a₁.comp b₁ rfl) (a₂.comp b₂ rfl) := by
  apply HomComplex.Cochain.ext
  intro r s hrs
  rw [HomComplex.Cochain.comp_v _ _ _ r (r + (m₁ + m₂)) s (by omega) (by omega),
    tensor_v, tensor_v, HomComplex.Cochain.units_smul_v, tensor_v]
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
  have key : ∀ (y₁ y₂ : ℤ) (hy₁ : (i₁ + m₁) + n₁ = y₁)
      (hy₂ : (i₂ + m₂) + n₂ = y₂) (hι : y₁ + y₂ = s),
      (b₁.v (i₁ + m₁) y₁ hy₁ ⊗ₘ b₂.v (i₂ + m₂) y₂ hy₂) ≫
        HomologicalComplex.ιTensorObj B₁ B₂ y₁ y₂ s hι =
      (b₁.v (i₁ + m₁) ((i₁ + m₁) + n₁) rfl ⊗ₘ
        b₂.v (i₂ + m₂) ((i₂ + m₂) + n₂) rfl) ≫
        HomologicalComplex.ιTensorObj B₁ B₂
          ((i₁ + m₁) + n₁) ((i₂ + m₂) + n₂) s (by omega) := by
    intro y₁ y₂ hy₁ hy₂ hι
    subst hy₁
    subst hy₂
    rfl
  rw [key _ _ (add_assoc i₁ m₁ n₁) (add_assoc i₂ m₂ n₂) (by omega)]

/-- The heterogeneous tensor product is additive in its left cochain. -/
theorem tensor_add_left [MonoidalPreadditive C] {m n : ℤ}
    (f₁ f₂ : Cochain C₁ A₁ m) (g : Cochain C₂ A₂ n)
    [GradedObject.HasTensor C₁.X C₂.X]
    [GradedObject.HasTensor A₁.X A₂.X] :
    tensor (f₁ + f₂) g = tensor f₁ g + tensor f₂ g := by
  apply HomComplex.Cochain.ext
  intro r s hrs
  rw [tensor_v, HomComplex.Cochain.add_v, tensor_v, tensor_v]
  apply HomologicalComplex.mapBifunctor.hom_ext (c := ComplexShape.up ℤ)
  intro i₁ i₂ hi
  simp only [HomologicalComplex.ι_mapBifunctorDesc,
    HomComplex.Cochain.add_v, MonoidalPreadditive.add_tensor,
    smul_add, Preadditive.add_comp, Preadditive.comp_add]

/-- Tensoring with zero on the left gives the zero cochain. -/
@[simp]
theorem tensor_zero_left [MonoidalPreadditive C] {m n : ℤ}
    (g : Cochain C₂ A₂ n)
    [GradedObject.HasTensor C₁.X C₂.X]
    [GradedObject.HasTensor A₁.X A₂.X] :
    tensor (0 : Cochain C₁ A₁ m) g = 0 := by
  apply HomComplex.Cochain.ext
  intro r s hrs
  rw [tensor_v]
  apply HomologicalComplex.mapBifunctor.hom_ext (c := ComplexShape.up ℤ)
  intro i₁ i₂ hi
  simp only [HomologicalComplex.ι_mapBifunctorDesc,
    HomComplex.Cochain.zero_v, MonoidalPreadditive.zero_tensor,
    smul_zero, zero_comp, comp_zero]

/-- Tensoring with zero on the right gives the zero cochain. -/
@[simp]
theorem tensor_zero_right [MonoidalPreadditive C] {m n : ℤ}
    (f : Cochain C₁ A₁ m)
    [GradedObject.HasTensor C₁.X C₂.X]
    [GradedObject.HasTensor A₁.X A₂.X] :
    tensor f (0 : Cochain C₂ A₂ n) = 0 := by
  apply HomComplex.Cochain.ext
  intro r s hrs
  rw [tensor_v]
  apply HomologicalComplex.mapBifunctor.hom_ext (c := ComplexShape.up ℤ)
  intro i₁ i₂ hi
  simp only [HomologicalComplex.ι_mapBifunctorDesc,
    HomComplex.Cochain.zero_v, MonoidalPreadditive.tensor_zero,
    smul_zero, zero_comp, comp_zero]

/-- The heterogeneous tensor product is additive in its right cochain. -/
theorem tensor_add_right [MonoidalPreadditive C] {m n : ℤ}
    (f : Cochain C₁ A₁ m) (g₁ g₂ : Cochain C₂ A₂ n)
    [GradedObject.HasTensor C₁.X C₂.X] [GradedObject.HasTensor A₁.X A₂.X] :
    tensor f (g₁ + g₂) = tensor f g₁ + tensor f g₂ := by
  apply HomComplex.Cochain.ext
  intro r s hrs
  rw [tensor_v, HomComplex.Cochain.add_v, tensor_v, tensor_v]
  apply HomologicalComplex.mapBifunctor.hom_ext (c := ComplexShape.up ℤ)
  intro i₁ i₂ hi
  simp only [HomologicalComplex.ι_mapBifunctorDesc, HomComplex.Cochain.add_v,
    MonoidalPreadditive.tensor_add, smul_add, Preadditive.add_comp,
    Preadditive.comp_add]

/-- Tensor a cochain with the identity on an unchanged right factor, retaining
the original displayed degree rather than `m + 0`. -/
noncomputable def tensorRightId
    {P Q : CochainComplex C ℤ} {m : ℤ}
    (a : Cochain P Q m) (T : CochainComplex C ℤ)
    [GradedObject.HasTensor P.X T.X]
    [GradedObject.HasTensor Q.X T.X] :
    Cochain (HomologicalComplex.tensorObj P T)
      (HomologicalComplex.tensorObj Q T) m :=
  Cochain.mk fun r s hrs =>
    (tensor a (ofHom (𝟙 T))).v r s (by omega)

/-- Component formula for `tensorRightId`. -/
@[simp]
theorem tensorRightId_v
    {P Q T : CochainComplex C ℤ} {m : ℤ}
    (a : Cochain P Q m)
    [GradedObject.HasTensor P.X T.X]
    [GradedObject.HasTensor Q.X T.X]
    (r s : ℤ) (hrs : r + m = s) :
    (tensorRightId a T).v r s hrs =
      (tensor a (ofHom (𝟙 T))).v r s (by omega) :=
  rfl

/-- In degree one, `tensorRightId` is the heterogeneous tensor with the
identity zero-cochain, with the displayed degree normalized. -/
theorem tensorRightId_one
    {P Q T : CochainComplex C ℤ}
    (a : Cochain P Q 1)
    [GradedObject.HasTensor P.X T.X]
    [GradedObject.HasTensor Q.X T.X] :
    tensorRightId a T = tensor a (ofHom (𝟙 T)) := by
  apply HomComplex.Cochain.ext
  intro r s hrs
  rfl

/-- Composition commutes with extension across an unchanged tensor factor. -/
@[simp]
theorem tensorRightId_comp
    {P Q S T : CochainComplex C ℤ} {m n mn : ℤ}
    [GradedObject.HasTensor P.X T.X]
    [GradedObject.HasTensor Q.X T.X]
    [GradedObject.HasTensor S.X T.X]
    (a : Cochain P Q m) (b : Cochain Q S n) (h : m + n = mn) :
    (tensorRightId a T).comp (tensorRightId b T) h =
      tensorRightId (a.comp b h) T := by
  subst mn
  apply HomComplex.Cochain.ext
  intro r s hrs
  have hraw := tensor_comp_tensor a b (ofHom (𝟙 T)) (ofHom (𝟙 T))
  have hraw' :
      (tensor a (ofHom (𝟙 T))).comp
          (tensor b (ofHom (𝟙 T))) (by omega) =
        tensor (a.comp b rfl) (ofHom (𝟙 T)) := by
    simpa only [zero_mul, Int.negOnePow_zero, one_smul,
      HomComplex.Cochain.comp_id] using hraw
  have hv := congrArg (fun z => z.v r s (by omega)) hraw'
  rw [HomComplex.Cochain.comp_v _ _ rfl r (r + m) s rfl (by omega)]
  simp only [tensorRightId_v]
  rw [HomComplex.Cochain.comp_v _ _ _ r (r + m) s (by omega) (by omega)] at hv
  exact hv

/-- Addition commutes with extension across an unchanged tensor factor. -/
@[simp]
theorem tensorRightId_add [MonoidalPreadditive C]
    {P Q T : CochainComplex C ℤ} {m : ℤ}
    [GradedObject.HasTensor P.X T.X]
    [GradedObject.HasTensor Q.X T.X]
    (a b : Cochain P Q m) :
    tensorRightId (a + b) T = tensorRightId a T + tensorRightId b T := by
  apply HomComplex.Cochain.ext
  intro r s hrs
  have hv := congrArg (fun z => z.v r s (by omega))
    (tensor_add_left a b (ofHom (𝟙 T)))
  simpa only [tensorRightId_v, HomComplex.Cochain.add_v] using hv

/-- Zero commutes with extension across an unchanged tensor factor. -/
@[simp]
theorem tensorRightId_zero [MonoidalPreadditive C]
    {P Q T : CochainComplex C ℤ} {m : ℤ}
    [GradedObject.HasTensor P.X T.X]
    [GradedObject.HasTensor Q.X T.X] :
    tensorRightId (0 : Cochain P Q m) T = 0 := by
  apply HomComplex.Cochain.ext
  intro r s hrs
  have hv := congrArg (fun z => z.v r s (by omega))
    (tensor_zero_left (C₁ := P) (A₁ := Q) (m := m) (ofHom (𝟙 T)))
  simpa only [tensorRightId_v, HomComplex.Cochain.zero_v] using hv

/-- Koszul exponent identity for reassociating iterated tensors: the 23-first
total on 12-associated maps agrees with the 12-first total on 23-associated
maps. -/
private lemma tensor_assoc_sign (n p i₁ i₂ : ℤ) :
    (p * (i₁ + i₂)).negOnePow * (n * i₁).negOnePow =
      ((n + p) * i₁).negOnePow * (p * i₂).negOnePow := by
  rw [← Int.negOnePow_add, ← Int.negOnePow_add]
  congr 1
  rw [mul_add, add_mul]
  ac_rfl

variable {C₃ A₃ : CochainComplex C ℤ}

/-- Associativity coherence for heterogeneous tensor products of cochains,
transported along the low-level complex associators. Binary and ternary
tensor assumptions are the exact source/target graded pairs/triples involved;
complex-level tensor and associator instances follow from them through the
pinned monoidal API. -/
theorem tensor_assoc {m n p : ℤ}
    (f : Cochain C₁ A₁ m) (g : Cochain C₂ A₂ n) (h : Cochain C₃ A₃ p)
    [GradedObject.HasTensor C₁.X C₂.X] [GradedObject.HasTensor A₁.X A₂.X]
    [GradedObject.HasTensor C₂.X C₃.X] [GradedObject.HasTensor A₂.X A₃.X]
    [GradedObject.HasTensor (HomologicalComplex.tensorObj C₁ C₂).X C₃.X]
    [GradedObject.HasTensor (HomologicalComplex.tensorObj A₁ A₂).X A₃.X]
    [GradedObject.HasTensor C₁.X (HomologicalComplex.tensorObj C₂ C₃).X]
    [GradedObject.HasTensor A₁.X (HomologicalComplex.tensorObj A₂ A₃).X]
    [GradedObject.HasGoodTensor₁₂Tensor C₁.X C₂.X C₃.X]
    [GradedObject.HasGoodTensorTensor₂₃ C₁.X C₂.X C₃.X]
    [GradedObject.HasGoodTensor₁₂Tensor A₁.X A₂.X A₃.X]
    [GradedObject.HasGoodTensorTensor₂₃ A₁.X A₂.X A₃.X] :
    ((tensor f g).tensor h).comp
        (ofHom (HomologicalComplex.associator A₁ A₂ A₃).hom)
        (add_zero (m + n + p)) =
      (ofHom (HomologicalComplex.associator C₁ C₂ C₃).hom).comp
        (tensor f (tensor g h)) (by omega) := by
  apply HomComplex.Cochain.ext
  intro r s hrs
  rw [HomComplex.Cochain.comp_v _ _ _ r s s hrs (add_zero s),
    HomComplex.Cochain.comp_v _ _ _ r r s (add_zero r) (by omega),
    HomComplex.Cochain.ofHom_v, HomComplex.Cochain.ofHom_v]
  apply HomologicalComplex.mapBifunctor₁₂.hom_ext
  intro i₁ i₂ i₃ hii
  have h12_3 : (i₁ + i₂) + i₃ = r := hii
  have assocC_eq : (HomologicalComplex.associator C₁ C₂ C₃).hom.f r =
      (HomologicalComplex.mapBifunctorAssociatorX
        (MonoidalCategory.curriedAssociatorNatIso C)
        C₁ C₂ C₃ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) r).hom :=
    rfl
  have assocA_eq : (HomologicalComplex.associator A₁ A₂ A₃).hom.f s =
      (HomologicalComplex.mapBifunctorAssociatorX
        (MonoidalCategory.curriedAssociatorNatIso C)
        A₁ A₂ A₃ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) s).hom :=
    rfl
  rw [assocC_eq, assocA_eq]
  rw [HomologicalComplex.ι_mapBifunctorAssociatorX_hom_assoc
    (associator := MonoidalCategory.curriedAssociatorNatIso C)
    (F₁₂ := curriedTensor C) (G := curriedTensor C)
    (F := curriedTensor C) (G₂₃ := curriedTensor C)
    (K₁ := C₁) (K₂ := C₂) (K₃ := C₃)
    (c₁₂ := ComplexShape.up ℤ) (c₂₃ := ComplexShape.up ℤ) (c₄ := ComplexShape.up ℤ)
    (i₁ := i₁) (i₂ := i₂) (i₃ := i₃) (j := r) (h := hii)]
  rw [HomologicalComplex.mapBifunctor₁₂.ι_eq
    (F₁₂ := curriedTensor C) (G := curriedTensor C)
    (K₁ := C₁) (K₂ := C₂) (K₃ := C₃)
    (c₁₂ := ComplexShape.up ℤ) (c₄ := ComplexShape.up ℤ)
    (i₁ := i₁) (i₂ := i₂) (i₃ := i₃) (i₁₂ := i₁ + i₂) (j := r)
    (h₁₂ := rfl) (h := h12_3)]
  have h1_23 : i₁ + (i₂ + i₃) = r := by omega
  rw [HomologicalComplex.mapBifunctor₂₃.ι_eq
    (F := curriedTensor C) (G₂₃ := curriedTensor C)
    (K₁ := C₁) (K₂ := C₂) (K₃ := C₃)
    (c₁₂ := ComplexShape.up ℤ) (c₂₃ := ComplexShape.up ℤ) (c₄ := ComplexShape.up ℤ)
    (i₁ := i₁) (i₂ := i₂) (i₃ := i₃) (i₂₃ := i₂ + i₃) (j := r)
    (h₂₃ := rfl) (h := h1_23)]
  have hLeftSummand :
      HomologicalComplex.ιMapBifunctor (HomologicalComplex.tensorObj C₁ C₂) C₃
        (curriedTensor C) (ComplexShape.up ℤ) (i₁ + i₂) i₃ r h12_3 ≫
        ((tensor f g).tensor h).v r s hrs =
      (p * (i₁ + i₂)).negOnePow •
        (((tensor f g).v (i₁ + i₂) ((i₁ + i₂) + (m + n)) rfl ⊗ₘ
            h.v i₃ (i₃ + p) rfl) ≫
          HomologicalComplex.ιTensorObj (HomologicalComplex.tensorObj A₁ A₂) A₃
            ((i₁ + i₂) + (m + n)) (i₃ + p) s (by omega)) := by
    rw [tensor_v]
    rw [HomologicalComplex.ι_mapBifunctorDesc
      (K₁ := HomologicalComplex.tensorObj C₁ C₂) (K₂ := C₃)
      (F := curriedTensor C) (c := ComplexShape.up ℤ)
      (i₁ := i₁ + i₂) (i₂ := i₃) (h := h12_3)]
    simp only [Linear.units_smul_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hLeftSummand]
  simp only [tensor_v, Category.assoc, MonoidalCategory.curriedTensor_obj_obj,
    curriedTensor_map_app, Linear.units_smul_comp, Linear.comp_units_smul]
  have hs : (i₁ + m) + (i₂ + n) + (i₃ + p) = s := by omega
  have hs12Shape :
      (ComplexShape.up ℤ).r (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (i₁ + m, i₂ + n, i₃ + p) = s := by
    change (i₁ + m) + (i₂ + n) + (i₃ + p) = s
    exact hs
  -- Local scalar transports through binary tensors.
  have smul_tensor_left : ∀ {W X Y Z : C} (φ : W ⟶ X) (ψ : Y ⟶ Z) (a : ℤˣ),
      (a • φ) ⊗ₘ ψ = a • (φ ⊗ₘ ψ) := by
    intro W X Y Z φ ψ a
    calc (a • φ) ⊗ₘ ψ
        = ((curriedTensor C).map (a • φ)).app Y ≫ X ◁ ψ := by
          rw [MonoidalCategory.tensorHom_def]
          simp only [curriedTensor_map_app]
        _ = a • (((curriedTensor C).map φ).app Y ≫ X ◁ ψ) := by
          rw [Functor.map_units_smul, NatTrans.app_units_zsmul,
            Linear.units_smul_comp]
        _ = a • (φ ⊗ₘ ψ) := by
          congr 1
          rw [MonoidalCategory.tensorHom_def]
          simp only [curriedTensor_map_app]
  have tensor_smul_right : ∀ {W X Y Z : C} (φ : W ⟶ X) (ψ : Y ⟶ Z) (a : ℤˣ),
      φ ⊗ₘ (a • ψ) = a • (φ ⊗ₘ ψ) := by
    intro W X Y Z φ ψ a
    calc φ ⊗ₘ (a • ψ)
        = φ ▷ Y ≫ ((curriedTensor C).obj X).map (a • ψ) := by
          rw [MonoidalCategory.tensorHom_def]
          simp only [curriedTensor_obj_map]
        _ = a • (φ ▷ Y ≫ ((curriedTensor C).obj X).map ψ) := by
          rw [Functor.map_units_smul, Linear.comp_units_smul]
        _ = a • (φ ⊗ₘ ψ) := by
          congr 1
          rw [MonoidalCategory.tensorHom_def]
          simp only [curriedTensor_obj_map]
  -- Localize the remaining RHS inner descriptor at its native degree.
  set f0 := f.v i₁ (i₁ + m) rfl with hf0
  set g0 := g.v i₂ (i₂ + n) rfl with hg0
  set h0 := h.v i₃ (i₃ + p) rfl with hh0
  set iC := HomologicalComplex.ιMapBifunctor C₂ C₃ (curriedTensor C)
    (ComplexShape.up ℤ) i₂ i₃ (i₂ + i₃) rfl with hiC
  set j₂₃ := i₂ + i₃ + (n + p) with hj₂₃
  set D := (tensor g h).v (i₂ + i₃) j₂₃ hj₂₃.symm with hD
  set iA := HomologicalComplex.ιMapBifunctor A₂ A₃ (curriedTensor C)
    (ComplexShape.up ℤ) (i₂ + n) (i₃ + p) j₂₃ (by rw [hj₂₃]; simp; omega) with hiA
  have hdesc : iC ≫ D = ((p * i₂).negOnePow • (g0 ⊗ₘ h0)) ≫ iA := by
    have hA : HomologicalComplex.ιTensorObj A₂ A₃ (i₂ + n) (i₃ + p)
        j₂₃ (by omega) = iA := by
      rw [hiA]
    rw [hiC, hD, hg0, hh0, HomComplex.Cochain.tensor_v,
      HomologicalComplex.ι_mapBifunctorDesc]
    simp [hA]
  set outerInclusion : (A₁.X (i₁ + m) ⊗
      (HomologicalComplex.tensorObj A₂ A₃).X j₂₃ ⟶
      (HomologicalComplex.tensorObj A₁
        (HomologicalComplex.tensorObj A₂ A₃)).X s) :=
    HomologicalComplex.ιTensorObj A₁ (HomologicalComplex.tensorObj A₂ A₃)
      (i₁ + m) j₂₃ s (by omega) with houter
  have hscalar_rhs : ((((n + p) * i₁).negOnePow • (f0 ⊗ₘ D)) ≫ outerInclusion) =
      (((((n + p) * i₁).negOnePow • f0) ⊗ₘ D) ≫ outerInclusion) := by
    rw [smul_tensor_left]
  conv_rhs =>
    rw [HomologicalComplex.ι_mapBifunctorDesc]
    rw [← hf0]
    rw [← HomComplex.Cochain.tensor_v]
    rw [← hD]
    rw [← houter]
    rw [← Linear.units_smul_comp]
    rw [hscalar_rhs]
    rw [MonoidalCategory.tensorHom_def]
    rw [curriedTensor_obj_map]
    rw [Category.assoc]
    rw [MonoidalCategory.whisker_exchange_assoc]
    rw [← MonoidalCategory.whiskerLeft_comp_assoc]
    rw [hdesc]
  conv_rhs =>
    rw [MonoidalCategory.whiskerLeft_comp_assoc]
  rw [← MonoidalCategory.tensorHom_def_assoc]
  rw [tensor_smul_right]
  rw [smul_tensor_left]
  have e_inner : HomologicalComplex.ιTensorObj A₁ A₂ (i₁ + m) (i₂ + n)
      (i₁ + i₂ + (m + n)) (by omega) = HomologicalComplex.ιMapBifunctor A₁ A₂
      (curriedTensor C) (ComplexShape.up ℤ) (i₁ + m) (i₂ + n)
      (i₁ + i₂ + (m + n)) (by change (i₁ + m) + (i₂ + n) = _; omega) := by
    unfold HomologicalComplex.ιTensorObj
    rfl
  conv_lhs =>
    rw [MonoidalCategory.tensorHom_def _ h0]
    rw [Category.assoc]
    simp only [← MonoidalCategory.comp_whiskerRight_assoc,
      HomologicalComplex.ι_mapBifunctorDesc, e_inner]
  have e_outer : (HomologicalComplex.tensorObj A₁ A₂).ιTensorObj A₃
      (i₁ + i₂ + (m + n)) (i₃ + p) s (by omega) =
      (HomologicalComplex.mapBifunctor A₁ A₂ (curriedTensor C)
      (ComplexShape.up ℤ)).ιMapBifunctor A₃ (curriedTensor C)
      (ComplexShape.up ℤ) (i₁ + i₂ + (m + n)) (i₃ + p) s
      (by change (i₁ + i₂ + (m + n)) + (i₃ + p) = _; omega) := by
    unfold HomologicalComplex.ιTensorObj HomologicalComplex.tensorObj
    rfl
  rw [e_outer]
  set Y0 := (((curriedTensor C).map (HomologicalComplex.ιMapBifunctor A₁ A₂
    (curriedTensor C) (ComplexShape.up ℤ) (i₁ + m) (i₂ + n)
    (i₁ + i₂ + (m + n)) _)).app (A₃.X (i₃ + p))) with hY0
  set O0 := ((HomologicalComplex.mapBifunctor A₁ A₂ (curriedTensor C)
    (ComplexShape.up ℤ)).ιMapBifunctor A₃ (curriedTensor C)
    (ComplexShape.up ℤ) (i₁ + i₂ + (m + n)) (i₃ + p) s _) with hO0
  have hfold : Y0 ≫ O0 = HomologicalComplex.mapBifunctor₁₂.ι
      (curriedTensor C) (curriedTensor C) A₁ A₂ A₃ (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (i₁ + m) (i₂ + n) (i₃ + p) s hs12Shape := by
    rw [hY0, hO0]
    exact (HomologicalComplex.mapBifunctor₁₂.ι_eq
      (F₁₂ := curriedTensor C) (G := curriedTensor C)
      (K₁ := A₁) (K₂ := A₂) (K₃ := A₃)
      (c₁₂ := ComplexShape.up ℤ) (c₄ := ComplexShape.up ℤ)
      (i₁ := i₁ + m) (i₂ := i₂ + n) (i₃ := i₃ + p)
      (i₁₂ := i₁ + i₂ + (m + n)) (j := s)
      (h₁₂ := by change (i₁ + m) + (i₂ + n) = _; omega)
      (h := by change (i₁ + i₂ + (m + n)) + (i₃ + p) = _; omega)).symm
  rw [← assocA_eq]
  have hY0_eq : (HomologicalComplex.ιMapBifunctor A₁ A₂ (curriedTensor C)
      (ComplexShape.up ℤ) (i₁ + m) (i₂ + n)
        (i₁ + i₂ + (m + n))
        (by change (i₁ + m) + (i₂ + n) = _; omega) ▷
      A₃.X (i₃ + p)) = Y0 := by
    rw [← curriedTensor_map_app, ← hY0]
  conv_lhs =>
    rw [← Linear.units_smul_comp]
    rw [← curriedTensor_map_app, ← NatTrans.app_units_zsmul,
      ← Functor.map_units_smul, curriedTensor_map_app,
      ← Linear.units_smul_comp]
    rw [← curriedTensor_map_app]
    simp only [← Linear.units_smul_comp]
    rw [Functor.map_comp, NatTrans.comp_app,
      curriedTensor_map_app, curriedTensor_map_app]
    rw [Category.assoc (f := _ ▷ C₃.X i₃), ← MonoidalCategory.whisker_exchange_assoc,
      hY0_eq, ← Category.assoc (f := Y0), hfold]
  conv_lhs =>
    rw [← curriedTensor_map_app, Functor.map_units_smul,
      NatTrans.app_units_zsmul, curriedTensor_map_app]
    rw [Linear.units_smul_comp]
  rw [assocA_eq]
  rw [HomologicalComplex.ι_mapBifunctorAssociatorX_hom
    (associator := MonoidalCategory.curriedAssociatorNatIso C)
    (F₁₂ := curriedTensor C) (G := curriedTensor C)
    (F := curriedTensor C) (G₂₃ := curriedTensor C)
    (K₁ := A₁) (K₂ := A₂) (K₃ := A₃)
    (c₁₂ := ComplexShape.up ℤ) (c₂₃ := ComplexShape.up ℤ) (c₄ := ComplexShape.up ℤ)
    (i₁ := i₁ + m) (i₂ := i₂ + n) (i₃ := i₃ + p) (j := s) (h := hs12Shape)]
  have assocA_bridge :
      ((((MonoidalCategory.curriedAssociatorNatIso C).hom.app
        (A₁.X (i₁ + m))).app (A₂.X (i₂ + n))).app
        (A₃.X (i₃ + p))) =
      (α_ (A₁.X (i₁ + m)) (A₂.X (i₂ + n)) (A₃.X (i₃ + p))).hom := rfl
  have assocC_bridge :
      ((((MonoidalCategory.curriedAssociatorNatIso C).hom.app
        (C₁.X i₁)).app (C₂.X i₂)).app
        (C₃.X i₃)) =
      (α_ (C₁.X i₁) (C₂.X i₂) (C₃.X i₃)).hom := rfl
  -- Fully concrete post-naturality tensor morphism (avoids semireducible head).
  set rightTensor : C₁.X i₁ ⊗ (C₂.X i₂ ⊗ C₃.X i₃) ⟶
      A₁.X (i₁ + m) ⊗ (A₂.X (i₂ + n) ⊗ A₃.X (i₃ + p)) :=
    ((n * i₁).negOnePow • f.v i₁ (i₁ + m) rfl) ⊗ₘ
      (g.v i₂ (i₂ + n) rfl ⊗ₘ h0) with hRightTensor
  have hNatur : ((((n * i₁).negOnePow • f.v i₁ (i₁ + m) rfl) ⊗ₘ
        g.v i₂ (i₂ + n) rfl) ⊗ₘ h0) ≫
        (α_ (A₁.X (i₁ + m)) (A₂.X (i₂ + n)) (A₃.X (i₃ + p))).hom =
      (α_ (C₁.X i₁) (C₂.X i₂) (C₃.X i₃)).hom ≫ rightTensor := by
    rw [hRightTensor]
    exact MonoidalCategory.associator_naturality
      ((n * i₁).negOnePow • f.v i₁ (i₁ + m) rfl)
      (g.v i₂ (i₂ + n) rfl) h0
  rw [assocA_bridge, assocC_bridge]
  rw [← MonoidalCategory.tensorHom_def_assoc]
  let W23 : (A₁.X (i₁ + m) ⊗ (A₂.X (i₂ + n) ⊗ A₃.X (i₃ + p)) ⟶
      (HomologicalComplex.tensorObj A₁ (HomologicalComplex.tensorObj A₂ A₃)).X s) :=
    HomologicalComplex.mapBifunctor₂₃.ι (curriedTensor C) (curriedTensor C) A₁ A₂ A₃
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (i₁ + m) (i₂ + n) (i₃ + p) s hs12Shape
  have hW23 : W23 = HomologicalComplex.mapBifunctor₂₃.ι (curriedTensor C) (curriedTensor C) A₁ A₂ A₃
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (i₁ + m) (i₂ + n) (i₃ + p) s hs12Shape := rfl
  rw [← hW23]
  rw [← Category.assoc]
  rw [← smul_tensor_left]
  rw [hNatur]
  rw [Category.assoc]
  rw [← Linear.comp_units_smul, ← Linear.comp_units_smul]
  rw [Iso.cancel_iso_hom_left]
  have h₂₃ : (i₂ + n) + (i₃ + p) = j₂₃ := by rw [hj₂₃]; omega
  have h_outer_j : (i₁ + m) + j₂₃ = s := by rw [hj₂₃]; omega
  have hW23Expanded : W23 = (A₁.X (i₁ + m) ◁ iA) ≫ outerInclusion := by
    rw [hW23]
    rw [HomologicalComplex.mapBifunctor₂₃.ι_eq
      (F := curriedTensor C) (G₂₃ := curriedTensor C)
      (K₁ := A₁) (K₂ := A₂) (K₃ := A₃)
      (c₁₂ := ComplexShape.up ℤ) (c₂₃ := ComplexShape.up ℤ) (c₄ := ComplexShape.up ℤ)
      (i₁ := i₁ + m) (i₂ := i₂ + n) (i₃ := i₃ + p)
      (i₂₃ := j₂₃) (j := s)
      (h₂₃ := h₂₃)
      (h := h_outer_j)]
    rw [curriedTensor_obj_map]
  rw [hW23Expanded]
  rw [Linear.comp_units_smul]
  rw [Linear.units_smul_comp]
  rw [hRightTensor]
  rw [smul_tensor_left]
  -- Fully concrete base for the remaining scalar tail (r89).
  let base : C₁.X i₁ ⊗ (C₂.X i₂ ⊗ C₃.X i₃) ⟶
      (HomologicalComplex.tensorObj A₁ (HomologicalComplex.tensorObj A₂ A₃)).X s :=
    (f0 ⊗ₘ (g0 ⊗ₘ h0)) ≫ ((A₁.X (i₁ + m) ◁ iA) ≫ outerInclusion)
  have hbase : base =
      (f0 ⊗ₘ (g0 ⊗ₘ h0)) ≫ ((A₁.X (i₁ + m) ◁ iA) ≫ outerInclusion) := rfl
  have hLHS :
      ((((p * (i₁ + i₂)).negOnePow) •
        ((((n * i₁).negOnePow) •
          (f.v i₁ (i₁ + m) rfl ⊗ₘ
            (g.v i₂ (i₂ + n) rfl ⊗ₘ h0))) ≫
          ((A₁.X (i₁ + m) ◁ iA) ≫ outerInclusion)))) =
      ((((p * (i₁ + i₂)).negOnePow * (n * i₁).negOnePow)) • base) := by
    simp only [hbase, ← hf0, ← hg0, Linear.units_smul_comp, smul_smul]
  have hRHS :
      ((p * i₂).negOnePow •
        ((((n + p) * i₁).negOnePow • (f0 ⊗ₘ (g0 ⊗ₘ h0))) ≫
          ((A₁.X (i₁ + m) ◁ iA) ≫ outerInclusion))) =
      ((((p * i₂).negOnePow * ((n + p) * i₁).negOnePow)) • base) := by
    simp only [hbase, Linear.units_smul_comp, smul_smul]
  rw [hLHS, hRHS]
  rw [mul_comm ((p * i₂).negOnePow) (((n + p) * i₁).negOnePow)]
  rw [tensor_assoc_sign]

/-- Component-level Leibniz rule for the heterogeneous tensor product of
cochains: `δ` of `tensor f g` is `tensor (δ f) g` plus
`(-1) ^ m • tensor f (δ g)`, as maps out of `(tensorObj C₁ C₂).X r`.

Orientation follows the pinned `HomComplex.δ` (Conrad signs,
`HomComplex.δ_comp`): differentiating a composite differentiates the right
factor first, so the right/second-factor differential term carries `(-1) ^ m`
where `m` is the left degree. The tensor Koszul sign stays `(-1) ^ (n * i₁)` on the
`(i₁, i₂)`-summand, matching the pinned tensor-complex vertical sign
`(up ℤ).ε` on the second factor (`ComplexShape.ε_up_ℤ`). -/
theorem tensor_δ_v {m n : ℤ} (f : Cochain C₁ A₁ m) (g : Cochain C₂ A₂ n)
    (r s : ℤ) (hrs : r + (m + n + 1) = s)
    [GradedObject.HasTensor C₁.X C₂.X] [GradedObject.HasTensor A₁.X A₂.X]
    [MonoidalPreadditive C] :
    (HomComplex.δ (m + n) (m + n + 1) (tensor f g)).v r s hrs =
      (tensor (HomComplex.δ m (m + 1) f) g).v r s (by omega) +
        m.negOnePow •
          (tensor f (HomComplex.δ n (n + 1) g)).v r s (by omega) := by
  rw [HomComplex.δ_v _ _ rfl _ _ _ _ _ _ rfl rfl]
  simp only [tensor_v]
  rw [HomologicalComplex.mapBifunctor.d_eq, HomologicalComplex.mapBifunctor.d_eq]
  simp only [Preadditive.comp_add, Preadditive.add_comp, smul_add]
  apply HomologicalComplex.mapBifunctor.hom_ext (c := ComplexShape.up ℤ)
  intro i₁ i₂ hh
  have hij : i₁ + i₂ = r := hh
  have hR1 : (ComplexShape.up ℤ).Rel (i₁ + m) (i₁ + (m + 1)) := by
    rw [ComplexShape.up_Rel]; omega
  have hR2 : (ComplexShape.up ℤ).Rel (i₂ + n) (i₂ + (n + 1)) := by
    rw [ComplexShape.up_Rel]; omega
  have hC1 : (ComplexShape.up ℤ).Rel i₁ (i₁ + 1) := by rw [ComplexShape.up_Rel]
  have hC2 : (ComplexShape.up ℤ).Rel i₂ (i₂ + 1) := by rw [ComplexShape.up_Rel]
  have eA1 : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) ⟨i₁ + (m + 1), i₂ + n⟩ = s := by
    have hs : (i₁ + (m + 1)) + (i₂ + n) = s := by omega
    exact hs
  have eA2 : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) ⟨i₁ + m, i₂ + (n + 1)⟩ = s := by
    have hs : (i₁ + m) + (i₂ + (n + 1)) = s := by omega
    exact hs
  have eC1 : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) ⟨i₁ + 1, i₂⟩ = r + 1 := by
    have hr : (i₁ + 1) + i₂ = r + 1 := by omega
    exact hr
  have eC2 : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) ⟨i₁, i₂ + 1⟩ = r + 1 := by
    have hr : i₁ + (i₂ + 1) = r + 1 := by omega
    exact hr
  -- Local scalar transports through binary tensors (as in `tensor_assoc`).
  have smul_tensor_left : ∀ {W X Y Z : C} (φ : W ⟶ X) (ψ : Y ⟶ Z) (a : ℤˣ),
      (a • φ) ⊗ₘ ψ = a • (φ ⊗ₘ ψ) := by
    intro W X Y Z φ ψ a
    calc (a • φ) ⊗ₘ ψ
        = ((curriedTensor C).map (a • φ)).app Y ≫ X ◁ ψ := by
          rw [MonoidalCategory.tensorHom_def]
          simp only [curriedTensor_map_app]
        _ = a • (((curriedTensor C).map φ).app Y ≫ X ◁ ψ) := by
          rw [Functor.map_units_smul, NatTrans.app_units_zsmul,
            Linear.units_smul_comp]
        _ = a • (φ ⊗ₘ ψ) := by
          congr 1
          rw [MonoidalCategory.tensorHom_def]
          simp only [curriedTensor_map_app]
  have tensor_smul_right : ∀ {W X Y Z : C} (φ : W ⟶ X) (ψ : Y ⟶ Z) (a : ℤˣ),
      φ ⊗ₘ (a • ψ) = a • (φ ⊗ₘ ψ) := by
    intro W X Y Z φ ψ a
    calc φ ⊗ₘ (a • ψ)
        = φ ▷ Y ≫ ((curriedTensor C).obj X).map (a • ψ) := by
          rw [MonoidalCategory.tensorHom_def]
          simp only [curriedTensor_obj_map]
        _ = a • (φ ▷ Y ≫ ((curriedTensor C).obj X).map ψ) := by
          rw [Functor.map_units_smul, Linear.comp_units_smul]
        _ = a • (φ ⊗ₘ ψ) := by
          congr 1
          rw [MonoidalCategory.tensorHom_def]
          simp only [curriedTensor_obj_map]
  have hsmul_left : ∀ {W X Y Z : C} (k : ℤˣ) (φ : W ⟶ X) (ψ : Y ⟶ Z),
      ((k • φ) ⊗ₘ ψ) = k • (φ ⊗ₘ ψ) := fun k φ ψ => smul_tensor_left φ ψ k
  have hsmul_right : ∀ {W X Y Z : C} (k : ℤˣ) (φ : W ⟶ X) (ψ : Y ⟶ Z),
      (φ ⊗ₘ (k • ψ)) = k • (φ ⊗ₘ ψ) := fun k φ ψ => tensor_smul_right φ ψ k
  have hε1 : ∀ _x : ℤ × ℤ, ComplexShape.ε₁ (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) _x = 1 := fun _x => rfl
  have hε2 : ∀ _x : ℤ × ℤ, ComplexShape.ε₂ (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) _x = (_x.1).negOnePow :=
    fun _x => rfl
  have u2 : ∀ _Y : (C₁.X i₁ ⊗ C₂.X i₂ ⟶
      (HomologicalComplex.tensorObj A₁ A₂).X s),
      (n * i₁).negOnePow • ((i₁ + m).negOnePow • _Y) =
        m.negOnePow • (((n + 1) * i₁).negOnePow • _Y) := by
    intro _Y
    have hExp : (n * i₁ + (i₁ + m)) = (m + (n + 1) * i₁) := by
      rw [add_mul, one_mul]; omega
    rw [smul_smul, smul_smul, ← Int.negOnePow_add, ← Int.negOnePow_add, hExp]
  have u3 : ∀ _Y : (C₁.X i₁ ⊗ C₂.X i₂ ⟶
      (HomologicalComplex.tensorObj A₁ A₂).X s),
      (m + n + 1).negOnePow • ((n * (i₁ + 1)).negOnePow • _Y) =
        (n * i₁).negOnePow • ((m + 1).negOnePow • _Y) := by
    intro _Y
    have hExp : ((m + n + 1) + n * (i₁ + 1)) = ((n * i₁ + (m + 1)) + (n + n)) := by
      rw [mul_add, mul_one]; omega
    rw [smul_smul, smul_smul, ← Int.negOnePow_add, ← Int.negOnePow_add, hExp,
      Int.negOnePow_add, Int.negOnePow_even _ ⟨n, rfl⟩, mul_one]
  have u4 : ∀ _Y : (C₁.X i₁ ⊗ C₂.X i₂ ⟶
      (HomologicalComplex.tensorObj A₁ A₂).X s),
      (m + n + 1).negOnePow • (i₁.negOnePow • ((n * i₁).negOnePow • _Y)) =
        m.negOnePow • ((((n + 1) * i₁).negOnePow • ((n + 1).negOnePow • _Y))) := by
    intro _Y
    simp only [smul_smul, ← Int.negOnePow_add]
    congr 1
    congr 1
    rw [add_mul, one_mul]
    omega
  simp only [Preadditive.comp_add, Linear.comp_units_smul,
    HomologicalComplex.ι_mapBifunctorDesc,
    HomologicalComplex.ι_mapBifunctorDesc_assoc,
    HomologicalComplex.mapBifunctor.ι_D₁_assoc,
    HomologicalComplex.mapBifunctor.ι_D₂_assoc]
  rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ hC1 _ _ eC1,
    HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ _ hC2 _ eC2]
  simp only [Linear.units_smul_comp, Category.assoc,
    HomologicalComplex.ι_mapBifunctorDesc]
  simp only [Linear.comp_units_smul,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂]
  rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ hR1 _ _ eA1,
    HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ _ hR2 _ eA2]
  simp only [hε1, hε2, one_smul, curriedTensor_map_app, curriedTensor_obj_map,
    ← Category.assoc, MonoidalCategory.whiskerRight_comp_tensorHom,
    MonoidalCategory.whiskerLeft_comp_tensorHom,
    MonoidalCategory.tensorHom_comp_whiskerRight]
  rw [HomComplex.δ_v _ _ rfl f i₁ (i₁ + (m + 1)) _ (i₁ + m) (i₁ + 1) (by omega) rfl,
    HomComplex.δ_v _ _ rfl g i₂ (i₂ + (n + 1)) _ (i₂ + n) (i₂ + 1) (by omega) rfl]
  simp only [Preadditive.add_comp, smul_add,
    Linear.comp_units_smul, Linear.units_smul_comp,
    MonoidalPreadditive.add_tensor, MonoidalPreadditive.tensor_add,
    hsmul_left, hsmul_right, ← Category.assoc]
  rw [MonoidalCategory.tensorHom_comp_whiskerLeft]
  rw [u2, u3, u4]
  have key13 : ∀ (x : ℤ) (hfx : (i₁ + 1) + m = x) (hix : x + (i₂ + n) = s),
      (n * i₁).negOnePow • (m + 1).negOnePow •
        (C₁.d i₁ (i₁ + 1) ≫ f.v (i₁ + 1) x hfx ⊗ₘ g.v i₂ (i₂ + n) rfl) ≫
        HomologicalComplex.ιTensorObj A₁ A₂ x (i₂ + n) s hix =
      (n * i₁).negOnePow • (m + 1).negOnePow •
        (C₁.d i₁ (i₁ + 1) ≫ f.v (i₁ + 1) (i₁ + (m + 1)) (by omega) ⊗ₘ
          g.v i₂ (i₂ + n) rfl) ≫
        HomologicalComplex.ιTensorObj A₁ A₂ (i₁ + (m + 1)) (i₂ + n) s (by omega) := by
    intro x hfx hix
    have hxR : x = i₁ + (m + 1) := by omega
    subst hxR
    rfl
  have key24 : ∀ (y : ℤ) (hgy : (i₂ + 1) + n = y) (hiy : (i₁ + m) + y = s),
      m.negOnePow • ((n + 1) * i₁).negOnePow • (n + 1).negOnePow •
        (f.v i₁ (i₁ + m) rfl ⊗ₘ C₂.d i₂ (i₂ + 1) ≫ g.v (i₂ + 1) y hgy) ≫
        HomologicalComplex.ιTensorObj A₁ A₂ (i₁ + m) y s hiy =
      m.negOnePow • ((n + 1) * i₁).negOnePow • (n + 1).negOnePow •
        (f.v i₁ (i₁ + m) rfl ⊗ₘ C₂.d i₂ (i₂ + 1) ≫ g.v (i₂ + 1) (i₂ + (n + 1))
          (by omega)) ≫
        HomologicalComplex.ιTensorObj A₁ A₂ (i₁ + m) (i₂ + (n + 1)) s (by omega) := by
    intro y hgy hiy
    have hyR : y = i₂ + (n + 1) := by omega
    subst hyR
    rfl
  rw [key13, key24]
  abel

section Unitor

variable [HasZeroObject C]
variable [∀ X₂, PreservesColimit (Functor.empty.{0} C)
  ((curriedTensor C).flip.obj X₂)]

variable {K L : CochainComplex C ℤ}

/-- Component calculation for conjugating `tensor (ofHom 𝟙) f` by the
left unitors. -/
private theorem tensor_ofHom_id_comp_leftUnitor_v {n : ℤ}
    (f : Cochain K L n) (r s : ℤ) (hrs : r + n = s) :
    (((ofHom (HomologicalComplex.leftUnitor K).inv).comp
      (tensor
        (ofHom (𝟙 (HomologicalComplex.tensorUnit C (ComplexShape.up ℤ)))) f)
      (by omega : 0 + (0 + n) = n)).comp
      (ofHom (HomologicalComplex.leftUnitor L).hom) (add_zero n)).v r s hrs =
        f.v r s hrs := by
  have hs : s = r + n := by omega
  cases hs
  rw [HomComplex.Cochain.comp_v _ _ _ r (r + n) (r + n)
    hrs (add_zero (r + n))]
  rw [HomComplex.Cochain.comp_v _ _ _ r r (r + n)
    (add_zero r) (by omega)]
  rw [HomComplex.Cochain.ofHom_v, HomComplex.Cochain.ofHom_v]
  let I := HomologicalComplex.tensorUnit C (ComplexShape.up ℤ)
  let unitId := ofHom (𝟙 I)
  have hInv : (HomologicalComplex.leftUnitor K).inv.f r =
      (HomologicalComplex.leftUnitor' K).inv r := rfl
  rw [hInv, HomologicalComplex.leftUnitor'_inv]
  have hStep :
      HomologicalComplex.ιTensorObj I L 0 (r + n) (r + n)
          (zero_add (r + n)) ≫
          (HomologicalComplex.leftUnitor L).hom.f (r + n) =
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (𝟙_ C)).hom ▷ L.X (r + n)) ≫
          (λ_ (L.X (r + n))).hom :=
    HomologicalComplex.ιTensorObj_leftUnitor_hom L (r + n)
  have hUnitId : unitId.v 0 (0 + 0) rfl = 𝟙 (I.X 0) := by
    dsimp only [unitId]
    have hCanonical :
        (ofHom (𝟙 I)).v 0 0 (add_zero 0) = 𝟙 (I.X 0) := by
      rw [HomComplex.Cochain.ofHom_v, HomologicalComplex.id_f]
    exact hCanonical
  have hIotaIdx :
      HomologicalComplex.ιTensorObj I L (0 + 0) (r + n) (r + n)
          (by omega) =
        HomologicalComplex.ιTensorObj I L 0 (r + n) (r + n)
          (zero_add (r + n)) := by
    congr 1
  have hTail :
      ((𝟙 (I.X 0) ⊗ₘ f.v r (r + n) rfl) ≫
          HomologicalComplex.ιTensorObj I L (0 + 0) (r + n)
            (r + n) (by omega)) ≫
          (HomologicalComplex.leftUnitor L).hom.f (r + n) =
        (𝟙 (I.X 0) ⊗ₘ f.v r (r + n) rfl) ≫
          (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (𝟙_ C)).hom ▷ L.X (r + n)) ≫
            (λ_ (L.X (r + n))).hom) := by
    rw [hIotaIdx, Category.assoc, hStep]
  let singleIso := HomologicalComplex.singleObjXSelf
    (ComplexShape.up ℤ) 0 (𝟙_ C)
  have hSingle :
      ((singleIso.inv ⊗ₘ 𝟙 (K.X r)) ≫
          (𝟙 (I.X 0) ⊗ₘ f.v r (r + n) rfl)) ≫
          (singleIso.hom ⊗ₘ 𝟙 (L.X (r + n))) =
        𝟙 (𝟙_ C) ⊗ₘ f.v r (r + n) rfl := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom,
      MonoidalCategory.tensorHom_comp_tensorHom]
    have hIso : (singleIso.inv ≫ 𝟙 (I.X 0)) ≫ singleIso.hom =
        𝟙 (𝟙_ C) := by
      rw [Category.comp_id, Iso.inv_hom_id]
    rw [hIso]
    rw [Category.id_comp, Category.comp_id]
  have hWhisker :
      𝟙 (𝟙_ C) ⊗ₘ f.v r (r + n) rfl =
        (𝟙_ C) ◁ f.v r (r + n) rfl :=
    MonoidalCategory.id_tensorHom (𝟙_ C) _
  have hNaturality :=
    MonoidalCategory.leftUnitor_naturality (f.v r (r + n) rfl)
  have hNaturalityPre := congrArg
    ((λ_ (K.X r)).inv ≫ ·) hNaturality
  have hNaturalityCancel :
      (λ_ (K.X r)).inv ≫
          ((λ_ (K.X r)).hom ≫ f.v r (r + n) rfl) =
        f.v r (r + n) rfl := by
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hNaturalityFinal := hNaturalityPre.trans hNaturalityCancel
  have hCollapse :
      HomologicalComplex.ιTensorObj I K 0 r r (zero_add r) ≫
          ((tensor unitId f).v r (r + n) (by omega) ≫
            (HomologicalComplex.leftUnitor L).hom.f (r + n)) =
        (((n * 0).negOnePow •
            (unitId.v 0 (0 + 0) rfl ⊗ₘ f.v r (r + n) rfl) ≫
          HomologicalComplex.ιTensorObj I L (0 + 0) (r + n)
            (r + n) (by omega)) ≫
          (HomologicalComplex.leftUnitor L).hom.f (r + n)) := by
    rw [← Category.assoc, tensor_v,
      HomologicalComplex.ι_mapBifunctorDesc]
  simp only [Category.assoc]
  rw [hCollapse]
  rw [mul_zero, Int.negOnePow_zero, one_smul, hUnitId]
  rw [hTail]
  have hWhiskerInv : (singleIso.inv ▷ K.X r) =
      singleIso.inv ⊗ₘ 𝟙 (K.X r) :=
    (MonoidalCategory.tensorHom_id singleIso.inv (K.X r)).symm
  have hWhiskerHom : (singleIso.hom ▷ L.X (r + n)) =
      singleIso.hom ⊗ₘ 𝟙 (L.X (r + n)) :=
    (MonoidalCategory.tensorHom_id singleIso.hom (L.X (r + n))).symm
  rw [hWhiskerInv, hWhiskerHom]
  let first := singleIso.inv ⊗ₘ 𝟙 (K.X r)
  let middle := 𝟙 (I.X 0) ⊗ₘ f.v r (r + n) rfl
  let last := singleIso.hom ⊗ₘ 𝟙 (L.X (r + n))
  let post := (λ_ (L.X (r + n))).hom
  have hAssocFour : first ≫ (middle ≫ (last ≫ post)) =
      ((first ≫ middle) ≫ last) ≫ post := by
    simp only [Category.assoc]
  have hSinglePost := congrArg (· ≫ post) hSingle
  have hInner : first ≫ (middle ≫ (last ≫ post)) =
      (𝟙 (𝟙_ C) ⊗ₘ f.v r (r + n) rfl) ≫ post :=
    hAssocFour.trans hSinglePost
  rw [hInner, hWhisker]
  exact hNaturalityFinal

/-- Tensoring a cochain on the left with the identity of the tensor unit,
then conjugating by the complex left unitors, recovers the cochain. -/
theorem leftUnitor_inv_comp_tensor_ofHom_id_comp_leftUnitor {n : ℤ}
    (f : Cochain K L n) :
    ((ofHom (HomologicalComplex.leftUnitor K).inv).comp
      (tensor
        (ofHom (𝟙 (HomologicalComplex.tensorUnit C (ComplexShape.up ℤ)))) f)
      (by omega : 0 + (0 + n) = n)).comp
      (ofHom (HomologicalComplex.leftUnitor L).hom) (add_zero n) = f := by
  apply HomComplex.Cochain.ext
  intro r s hrs
  exact tensor_ofHom_id_comp_leftUnitor_v f r s hrs

end Unitor

section RightUnitor

variable [HasZeroObject C]
variable [∀ X₁, PreservesColimit (Functor.empty.{0} C)
  ((curriedTensor C).obj X₁)]

variable {K L : CochainComplex C ℤ}

/-- Component calculation for conjugating `tensor f (ofHom 𝟙)` by the
right unitors. -/
private theorem rightUnitor_inv_comp_tensor_ofHom_id_v {n : ℤ}
    (f : Cochain K L n) (r s : ℤ) (hrs : r + n = s) :
    (((ofHom (HomologicalComplex.rightUnitor K).inv).comp
      (tensor f
        (ofHom (𝟙 (HomologicalComplex.tensorUnit C (ComplexShape.up ℤ)))))
      (by omega : 0 + (n + 0) = n)).comp
      (ofHom (HomologicalComplex.rightUnitor L).hom) (add_zero n)).v r s hrs =
        f.v r s hrs := by
  have hs : s = r + n := by omega
  cases hs
  rw [HomComplex.Cochain.comp_v _ _ _ r (r + n) (r + n)
    hrs (add_zero (r + n))]
  rw [HomComplex.Cochain.comp_v _ _ _ r r (r + n)
    (add_zero r) (by omega)]
  rw [HomComplex.Cochain.ofHom_v, HomComplex.Cochain.ofHom_v]
  let I := HomologicalComplex.tensorUnit C (ComplexShape.up ℤ)
  let unitId := ofHom (𝟙 I)
  have hInv : (HomologicalComplex.rightUnitor K).inv.f r =
      (HomologicalComplex.rightUnitor' K).inv r := rfl
  rw [hInv, HomologicalComplex.rightUnitor'_inv]
  have hStep :
      HomologicalComplex.ιTensorObj L I (r + n) 0 (r + n)
          (add_zero (r + n)) ≫
          (HomologicalComplex.rightUnitor L).hom.f (r + n) =
        (L.X (r + n) ◁
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (𝟙_ C)).hom) ≫
          (ρ_ (L.X (r + n))).hom :=
    HomologicalComplex.ιTensorObj_rightUnitor_hom L (r + n)
  have hUnitId : unitId.v 0 (0 + 0) rfl = 𝟙 (I.X 0) := by
    dsimp only [unitId]
    have hCanonical :
        (ofHom (𝟙 I)).v 0 0 (add_zero 0) = 𝟙 (I.X 0) := by
      rw [HomComplex.Cochain.ofHom_v, HomologicalComplex.id_f]
    exact hCanonical
  have hIotaIdx :
      HomologicalComplex.ιTensorObj L I (r + n) (0 + 0) (r + n)
          (by omega) =
        HomologicalComplex.ιTensorObj L I (r + n) 0 (r + n)
          (add_zero (r + n)) := by
    congr 1
  have hTail :
      ((f.v r (r + n) rfl ⊗ₘ 𝟙 (I.X 0)) ≫
          HomologicalComplex.ιTensorObj L I (r + n) (0 + 0)
            (r + n) (by omega)) ≫
          (HomologicalComplex.rightUnitor L).hom.f (r + n) =
        (f.v r (r + n) rfl ⊗ₘ 𝟙 (I.X 0)) ≫
          ((L.X (r + n) ◁
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
              (𝟙_ C)).hom) ≫
            (ρ_ (L.X (r + n))).hom) := by
    rw [hIotaIdx, Category.assoc, hStep]
  let singleIso := HomologicalComplex.singleObjXSelf
    (ComplexShape.up ℤ) 0 (𝟙_ C)
  have hSingle :
      ((𝟙 (K.X r) ⊗ₘ singleIso.inv) ≫
          (f.v r (r + n) rfl ⊗ₘ 𝟙 (I.X 0))) ≫
          (𝟙 (L.X (r + n)) ⊗ₘ singleIso.hom) =
        f.v r (r + n) rfl ⊗ₘ 𝟙 (𝟙_ C) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom,
      MonoidalCategory.tensorHom_comp_tensorHom]
    have hIso : (singleIso.inv ≫ 𝟙 (I.X 0)) ≫ singleIso.hom =
        𝟙 (𝟙_ C) := by
      rw [Category.comp_id, Iso.inv_hom_id]
    rw [hIso]
    rw [Category.id_comp, Category.comp_id]
  have hWhisker :
      f.v r (r + n) rfl ⊗ₘ 𝟙 (𝟙_ C) =
        f.v r (r + n) rfl ▷ (𝟙_ C) :=
    MonoidalCategory.tensorHom_id _ (𝟙_ C)
  have hNaturality :=
    MonoidalCategory.rightUnitor_naturality (f.v r (r + n) rfl)
  have hNaturalityPre := congrArg
    ((ρ_ (K.X r)).inv ≫ ·) hNaturality
  have hNaturalityCancel :
      (ρ_ (K.X r)).inv ≫
          ((ρ_ (K.X r)).hom ≫ f.v r (r + n) rfl) =
        f.v r (r + n) rfl := by
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hNaturalityFinal := hNaturalityPre.trans hNaturalityCancel
  have hCollapse :
      HomologicalComplex.ιTensorObj K I r 0 r (add_zero r) ≫
          ((tensor f unitId).v r (r + n) (by omega) ≫
            (HomologicalComplex.rightUnitor L).hom.f (r + n)) =
        (((0 * r).negOnePow •
            (f.v r (r + n) rfl ⊗ₘ unitId.v 0 (0 + 0) rfl) ≫
          HomologicalComplex.ιTensorObj L I (r + n) (0 + 0)
            (r + n) (by omega)) ≫
          (HomologicalComplex.rightUnitor L).hom.f (r + n)) := by
    rw [← Category.assoc, tensor_v,
      HomologicalComplex.ι_mapBifunctorDesc]
  simp only [Category.assoc]
  rw [hCollapse]
  rw [zero_mul, Int.negOnePow_zero, one_smul, hUnitId]
  rw [hTail]
  have hWhiskerInv : (K.X r ◁ singleIso.inv) =
      𝟙 (K.X r) ⊗ₘ singleIso.inv :=
    (MonoidalCategory.id_tensorHom (K.X r) singleIso.inv).symm
  have hWhiskerHom : (L.X (r + n) ◁ singleIso.hom) =
      𝟙 (L.X (r + n)) ⊗ₘ singleIso.hom :=
    (MonoidalCategory.id_tensorHom (L.X (r + n)) singleIso.hom).symm
  rw [hWhiskerInv, hWhiskerHom]
  let first := 𝟙 (K.X r) ⊗ₘ singleIso.inv
  let middle := f.v r (r + n) rfl ⊗ₘ 𝟙 (I.X 0)
  let last := 𝟙 (L.X (r + n)) ⊗ₘ singleIso.hom
  let post := (ρ_ (L.X (r + n))).hom
  have hAssocFour : first ≫ (middle ≫ (last ≫ post)) =
      ((first ≫ middle) ≫ last) ≫ post := by
    simp only [Category.assoc]
  have hSinglePost := congrArg (· ≫ post) hSingle
  have hInner : first ≫ (middle ≫ (last ≫ post)) =
      (f.v r (r + n) rfl ⊗ₘ 𝟙 (𝟙_ C)) ≫ post :=
    hAssocFour.trans hSinglePost
  rw [hInner, hWhisker]
  exact hNaturalityFinal

/-- Tensoring a cochain on the right with the identity of the tensor unit,
then conjugating by the complex right unitors, recovers the cochain. -/
theorem rightUnitor_inv_comp_tensor_ofHom_id_comp_rightUnitor {n : ℤ}
    (f : Cochain K L n) :
    ((ofHom (HomologicalComplex.rightUnitor K).inv).comp
      (tensor f
        (ofHom (𝟙 (HomologicalComplex.tensorUnit C (ComplexShape.up ℤ)))))
      (by omega : 0 + (n + 0) = n)).comp
      (ofHom (HomologicalComplex.rightUnitor L).hom) (add_zero n) = f := by
  apply HomComplex.Cochain.ext
  intro r s hrs
  exact rightUnitor_inv_comp_tensor_ofHom_id_v f r s hrs

end RightUnitor

end HomComplex.Cochain

end CochainComplex
