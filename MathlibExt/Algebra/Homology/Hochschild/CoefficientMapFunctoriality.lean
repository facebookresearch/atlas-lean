/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricPositiveNaturality
public import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-!
# Functoriality of coefficient and algebra maps

Coefficient tensor maps preserve identities and composition and
induce maps of normalized and quotient complexes. Nonunital algebra
maps act on raw chains; simplicial maps require unit preservation.
Algebra universes are independent, and categorical coefficients use
an explicit common carrier category.
-/

@[expose] public section
noncomputable section
open CategoryTheory Opposite
open scoped Simplicial TensorProduct MonoidalCategory
universe u v₁ v₂ v₃ z w₁ w₂ w₃

namespace ModuleCat.Algebra.Hochschild

section
variable {k : Type u} [CommRing k]
  {A : Type v₁} [Ring A] [Algebra k A]
  {B : Type v₂} [Ring B] [Algebra k B]
  {M N : Type (max u v₁ v₂ z)} [AddCommGroup M] [AddCommGroup N]
  [Module k M] [Module k N]
  [Module A M]
  [Module Aᵐᵒᵖ M] [SMulCommClass A Aᵐᵒᵖ M]
  [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M]
  [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]
  [Module B N]
  [Module Bᵐᵒᵖ N] [SMulCommClass B Bᵐᵒᵖ N]
  [SMulCommClass k B N] [SMulCommClass k Bᵐᵒᵖ N]
  [IsScalarTower k B N] [IsScalarTower k Bᵐᵒᵖ N]

/-- Action-law witnesses do not change the common-carrier chain map. -/
theorem map_witness_independent (g : A →ₙₐ[k] B) (f : M →ₗ[k] N)
    (hl hl' : ∀ a m, f (a • m) = g a • f m)
    (hr hr' : ∀ a m, f (MulOpposite.op a • m) = MulOpposite.op (g a) • f m) :
    map.{u, v₁, v₂, max u v₁ v₂ z} g f hl hr =
      map.{u, v₁, v₂, max u v₁ v₂ z} g f hl' hr' := by
  cases Subsingleton.elim hl hl'
  cases Subsingleton.elim hr hr'
  rfl

end


namespace Symmetric

section Regular
variable {k : Type u} [CommRing k]
  {A : Type v₁} [Ring A] [Algebra k A]
  {B : Type v₂} [Ring B] [Algebra k B]
  {C : Type v₃} [Ring C] [Algebra k C]

/-- The lifted regular identity is the original coefficient identity. -/
theorem regularCoefficientMap_id :
    (regularCoefficientMap (NonUnitalAlgHom.id k A) :
      ULift.{w₁} A →ₗ[k] ULift.{w₁} A) = LinearMap.id := by
  apply LinearMap.ext
  intro a
  apply ULift.ext
  rfl

/-- Regular maps compose across independent algebra and coefficient-lift worlds. -/
theorem regularCoefficientMap_comp (g : A →ₙₐ[k] B) (h : B →ₙₐ[k] C) :
    (regularCoefficientMap h : ULift.{w₂} B →ₗ[k] ULift.{w₃} C).comp
        (regularCoefficientMap g : ULift.{w₁} A →ₗ[k] ULift.{w₂} B) =
      (regularCoefficientMap (h.comp g) : ULift.{w₁} A →ₗ[k] ULift.{w₃} C) := by
  apply LinearMap.ext
  intro a
  apply ULift.ext
  rfl

end Regular

section
variable {k : Type u} [CommRing k]
  {A : Type v₁} [CommRing A] [Algebra k A]
  {M : Type (max u v₁ z)} [AddCommGroup M]
  [Module k M]
  [Module A M]
  [IsScalarTower k A M]

attribute [local instance] opModule actionsComm kOpComm kOpTower
attribute [local instance] ModuleCat.Algebra.Hochschild.uliftSMulCommClass

/-- The bar degree identity is obtained by cancelling the original coordinates. -/
theorem coefficientBarMapComponent_id (n : ℕ) :
    coefficientBarMapComponent.{u, v₁, v₁, max u v₁ z}
      (AlgHom.id k A) (LinearMap.id : M →ₗ[k] M) n =
        𝟙 ((coefficientBar k A M).obj (op ⦋n⦌)) := by
  have hi : linearMap (AlgHom.id k A).toNonUnitalAlgHom
      (LinearMap.id : M →ₗ[k] M) n = LinearMap.id := by
    change linearMap (NonUnitalAlgHom.id k A) (LinearMap.id : M →ₗ[k] M) n = _
    exact linearMap_id n
  change (coefficientBarObjIso k A M n).hom ≫
    ModuleCat.ofHom (linearMap (AlgHom.id k A).toNonUnitalAlgHom
      (LinearMap.id : M →ₗ[k] M) n) ≫ (coefficientBarObjIso k A M n).inv = _
  rw [hi]
  change (coefficientBarObjIso k A M n).hom ≫ 𝟙 _ ≫
    (coefficientBarObjIso k A M n).inv = _
  simp only [Category.id_comp, Iso.hom_inv_id]

/-- The native bar morphism has the identity degree maps. -/
theorem coefficientBarMap_id :
    coefficientBarMap.{u, v₁, v₁, max u v₁ z}
      (AlgHom.id k A) (LinearMap.id : M →ₗ[k] M) (by intro a m; simp only [LinearMap.id_apply, AlgHom.id_apply]) =
        𝟙 (coefficientBar k A M) := by
  apply NatTrans.ext
  funext q
  obtain ⟨q⟩ := q
  cases q with
  | mk n =>
    simp only [coefficientBarMap, SimplicialObject.homOfComponents_app_mk]
    exact coefficientBarMapComponent_id n

/-- The symmetric raw identity follows from the tensor identity law. -/
theorem coefficientChainMap_id :
    coefficientChainMap.{u, v₁, v₁, max u v₁ z}
      (AlgHom.id k A) (LinearMap.id : M →ₗ[k] M) (by intro a m; simp only [LinearMap.id_apply, AlgHom.id_apply]) =
        𝟙 (chainComplex k A M) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  exact linearMap_id n

/-- The native normalization functor sends the bar identity to the normalized identity. -/
theorem normalizedCoefficientMap_id :
    normalizedCoefficientMap.{u, v₁, v₁, max u v₁ z}
      (AlgHom.id k A) (LinearMap.id : M →ₗ[k] M) (by intro a m; simp only [LinearMap.id_apply, AlgHom.id_apply]) =
        𝟙 (normalizedChainComplex k A M) := by
  let X := coefficientBar k A M
  let e : AlgebraicTopology.NormalizedQuotient.obj X ≅ normalizedChainComplex k A M :=
    ModuleCat.Algebra.Hochschild.normalizationIso k A M
  let b : X ⟶ X := coefficientBarMap.{u, v₁, v₁, max u v₁ z}
    (AlgHom.id k A) (LinearMap.id : M →ₗ[k] M)
    (by intro a m; simp only [LinearMap.id_apply, AlgHom.id_apply])
  have hb : b = 𝟙 X := coefficientBarMap_id
  have hq : AlgebraicTopology.NormalizedQuotient.map b = 𝟙 _ := by
    rw [hb]
    exact AlgebraicTopology.NormalizedQuotient.map_id X
  change e.inv ≫ AlgebraicTopology.NormalizedQuotient.map b ≫ e.hom = _
  rw [hq]
  simp only [Category.id_comp, Iso.inv_hom_id]

end

section
variable {k : Type u} [CommRing k]
  {A : Type v₁} [CommRing A] [Algebra k A]
  {B : Type v₂} [CommRing B] [Algebra k B]
  {M N : Type (max u v₁ v₂ z)} [AddCommGroup M] [AddCommGroup N]
  [Module k M] [Module k N]
  [Module A M]
  [IsScalarTower k A M]
  [Module B N]
  [IsScalarTower k B N]

attribute [local instance] opModule actionsComm kOpComm kOpTower
attribute [local instance] ModuleCat.Algebra.Hochschild.uliftSMulCommClass

/-- Bar maps do not depend on the chosen proof of coefficient compatibility. -/
theorem coefficientBarMap_witness_independent (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf hg : ∀ a m, f (a • m) = g a • f m) :
    coefficientBarMap.{u, v₁, v₂, max u v₁ v₂ z} g f hf =
      coefficientBarMap.{u, v₁, v₂, max u v₁ v₂ z} g f hg := by
  cases Subsingleton.elim hf hg
  rfl

/-- The raw chain map ignores the proof witness, not its input action law. -/
theorem coefficientChainMap_witness_independent (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf hg : ∀ a m, f (a • m) = g a • f m) :
    coefficientChainMap.{u, v₁, v₂, max u v₁ v₂ z} g f hf =
      coefficientChainMap.{u, v₁, v₂, max u v₁ v₂ z} g f hg := by
  cases Subsingleton.elim hf hg
  rfl

/-- Normalized maps ignore the compatibility proof witness. -/
theorem normalizedCoefficientMap_witness_independent (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf hg : ∀ a m, f (a • m) = g a • f m) :
    normalizedCoefficientMap.{u, v₁, v₂, max u v₁ v₂ z} g f hf =
      normalizedCoefficientMap.{u, v₁, v₂, max u v₁ v₂ z} g f hg := by
  cases Subsingleton.elim hf hg
  rfl

end

section
variable {k : Type u} [CommRing k]
  {A : Type v₁} [CommRing A] [Algebra k A]
  {B : Type v₂} [CommRing B] [Algebra k B]
  {C : Type v₃} [CommRing C] [Algebra k C]
  {M N P : Type (max u v₁ v₂ v₃ z)} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module k M] [Module k N] [Module k P]
  [Module A M]
  [IsScalarTower k A M]
  [Module B N]
  [IsScalarTower k B N]
  [Module C P]
  [IsScalarTower k C P]

attribute [local instance] opModule actionsComm kOpComm kOpTower
attribute [local instance] ModuleCat.Algebra.Hochschild.uliftSMulCommClass

/-- Composition retains the coefficient-bar coordinates in every degree. -/
theorem coefficientBarMapComponent_comp (g : A →ₐ[k] B) (h : B →ₐ[k] C)
    (f : M →ₗ[k] N) (f' : N →ₗ[k] P) (n : ℕ) :
    coefficientBarMapComponent.{u, v₁, v₂, max u v₁ v₂ v₃ z} g f n ≫
      coefficientBarMapComponent.{u, v₂, v₃, max u v₁ v₂ v₃ z} h f' n =
    coefficientBarMapComponent.{u, v₁, v₃, max u v₁ v₂ v₃ z} (h.comp g) (f'.comp f) n := by
  apply (cancel_epi (coefficientBarObjIso k A M n).inv).1
  apply (cancel_mono (coefficientBarObjIso k C P n).hom).1
  simp only [coefficientBarMapComponent, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  apply ModuleCat.hom_ext
  exact linearMap_comp g.toNonUnitalAlgHom h.toNonUnitalAlgHom f f' n

/-- The simplicial constructor's component law gives parameter composition. -/
theorem coefficientBarMap_comp (g : A →ₐ[k] B) (h : B →ₐ[k] C)
    (f : M →ₗ[k] N) (f' : N →ₗ[k] P)
    (hf : ∀ a m, f (a • m) = g a • f m)
    (hf' : ∀ b n, f' (b • n) = h b • f' n) :
    coefficientBarMap.{u, v₁, v₂, max u v₁ v₂ v₃ z} g f hf ≫
      coefficientBarMap.{u, v₂, v₃, max u v₁ v₂ v₃ z} h f' hf' =
    coefficientBarMap.{u, v₁, v₃, max u v₁ v₂ v₃ z} (h.comp g) (f'.comp f)
      (fun a m => (congrArg f' (hf a m)).trans (hf' (g a) (f m))) := by
  apply NatTrans.ext
  funext q
  obtain ⟨q⟩ := q
  cases q with
  | mk n =>
    simp only [NatTrans.comp_app, coefficientBarMap,
      SimplicialObject.homOfComponents_app_mk]
    exact coefficientBarMapComponent_comp g h f f' n

/-- The original coefficient tensor composition gives symmetric chain composition. -/
theorem coefficientChainMap_comp (g : A →ₐ[k] B) (h : B →ₐ[k] C)
    (f : M →ₗ[k] N) (f' : N →ₗ[k] P)
    (hf : ∀ a m, f (a • m) = g a • f m)
    (hf' : ∀ b n, f' (b • n) = h b • f' n) :
    coefficientChainMap.{u, v₁, v₂, max u v₁ v₂ v₃ z} g f hf ≫
      coefficientChainMap.{u, v₂, v₃, max u v₁ v₂ v₃ z} h f' hf' =
    coefficientChainMap.{u, v₁, v₃, max u v₁ v₂ v₃ z} (h.comp g) (f'.comp f)
      (fun a m => (congrArg f' (hf a m)).trans (hf' (g a) (f m))) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  exact linearMap_comp g.toNonUnitalAlgHom h.toNonUnitalAlgHom f f' n

/-- Native normalization functoriality and coordinate cancellation give composition. -/
theorem normalizedCoefficientMap_comp (g : A →ₐ[k] B) (h : B →ₐ[k] C)
    (f : M →ₗ[k] N) (f' : N →ₗ[k] P)
    (hf : ∀ a m, f (a • m) = g a • f m)
    (hf' : ∀ b n, f' (b • n) = h b • f' n) :
    normalizedCoefficientMap.{u, v₁, v₂, max u v₁ v₂ v₃ z} g f hf ≫
      normalizedCoefficientMap.{u, v₂, v₃, max u v₁ v₂ v₃ z} h f' hf' =
    normalizedCoefficientMap.{u, v₁, v₃, max u v₁ v₂ v₃ z} (h.comp g) (f'.comp f)
      (fun a m => (congrArg f' (hf a m)).trans (hf' (g a) (f m))) := by
  let X := coefficientBar k A M
  let Y := coefficientBar k B N
  let Z := coefficientBar k C P
  let eA : AlgebraicTopology.NormalizedQuotient.obj X ≅ normalizedChainComplex k A M :=
    ModuleCat.Algebra.Hochschild.normalizationIso k A M
  let eB : AlgebraicTopology.NormalizedQuotient.obj Y ≅ normalizedChainComplex k B N :=
    ModuleCat.Algebra.Hochschild.normalizationIso k B N
  let eC : AlgebraicTopology.NormalizedQuotient.obj Z ≅ normalizedChainComplex k C P :=
    ModuleCat.Algebra.Hochschild.normalizationIso k C P
  let b₁ : X ⟶ Y := coefficientBarMap.{u, v₁, v₂, max u v₁ v₂ v₃ z} g f hf
  let b₂ : Y ⟶ Z := coefficientBarMap.{u, v₂, v₃, max u v₁ v₂ v₃ z} h f' hf'
  let b₃ : X ⟶ Z := coefficientBarMap.{u, v₁, v₃, max u v₁ v₂ v₃ z} (h.comp g) (f'.comp f)
    (fun a m => (congrArg f' (hf a m)).trans (hf' (g a) (f m)))
  have hb : b₁ ≫ b₂ = b₃ := coefficientBarMap_comp g h f f' hf hf'
  let q₁ := AlgebraicTopology.NormalizedQuotient.map b₁
  let q₂ := AlgebraicTopology.NormalizedQuotient.map b₂
  let q₃ := AlgebraicTopology.NormalizedQuotient.map b₃
  have hq : q₁ ≫ q₂ = q₃ :=
    (AlgebraicTopology.NormalizedQuotient.map_comp b₁ b₂).symm.trans
      (congrArg (fun b : X ⟶ Z => AlgebraicTopology.NormalizedQuotient.map b) hb)
  change (eA.inv ≫ q₁ ≫ eB.hom) ≫ (eB.inv ≫ q₂ ≫ eC.hom) = eA.inv ≫ q₃ ≫ eC.hom
  calc
    _ = eA.inv ≫ (q₁ ≫ q₂) ≫ eC.hom := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = _ := by rw [hq]

end

private theorem positiveProjection_epi
    {k : Type u} [CommRing k] [MonoidalCategory (ModuleCat.{w₁} k)]
    [MonoidalPreadditive (ModuleCat.{w₁} k)]
    {K₁ K₂ K₃ : ChainComplex (ModuleCat.{w₁} k) ℕ}
    (Q : HomologicalComplex.ChainGradedPairing K₁ K₂ K₃)
    (h₁ : K₁.d 1 0 = 0) (h₂ : K₂.d 1 0 = 0) :
    Epi (HomologicalComplex.ChainGradedPairing.positiveImageProjection Q h₁ h₂) := by
  apply HomologicalComplex.epi_of_epi_f
  intro n
  rw [ModuleCat.epi_iff_surjective]
  exact Submodule.mkQ_surjective _

section
variable {k : Type u} [CommRing k]
  {A : Type v₁} [CommRing A] [Algebra k A]
  {M : Type (max u v₁ z)} [AddCommGroup M]
  [Module k M]
  [Module A M]
  [IsScalarTower k A M]

attribute [local instance] opModule actionsComm kOpComm kOpTower
attribute [local instance] ModuleCat.Algebra.Hochschild.uliftSMulCommClass

/-- The quotient projection law and raw chain identity give the quotient identity. -/
theorem positiveQuotientMap_id :
  letI : MonoidalCategoryStruct (ModuleCat.{max u v₁ z} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max u v₁ z} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v₁ z} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max u v₁ z} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v₁ z} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max u v₁ z} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v₁ z} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max u v₁ z} (R := k)
  positiveQuotientMap.{u, v₁, v₁, max u v₁ z}
    (AlgHom.id k A) (LinearMap.id : M →ₗ[k] M)
      (by intro a m; simp only [LinearMap.id_apply, AlgHom.id_apply]) = 𝟙 _ := by
  let : MonoidalCategoryStruct (ModuleCat.{max u v₁ z} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max u v₁ z} (R := k)
  let : MonoidalCategory (ModuleCat.{max u v₁ z} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max u v₁ z} (R := k)
  let : MonoidalPreadditive (ModuleCat.{max u v₁ z} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max u v₁ z} (R := k)
  let : MonoidalLinear k (ModuleCat.{max u v₁ z} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max u v₁ z} (R := k)
  let π := HomologicalComplex.ChainGradedPairing.positiveImageProjection
    (pairing k A M) (boundary_one_zero k A (ULift.{max u v₁ z} A)) (boundary_one_zero k A M)
  let : Epi π := positiveProjection_epi _ _ _
  apply (cancel_epi π).1
  rw [positiveQuotientMap_projection, coefficientChainMap_id]
  simp only [Category.id_comp, Category.comp_id]
  rfl

end

section
variable {k : Type u} [CommRing k]
  {A : Type v₁} [CommRing A] [Algebra k A]
  {B : Type v₂} [CommRing B] [Algebra k B]
  {M N : Type (max u v₁ v₂ z)} [AddCommGroup M] [AddCommGroup N]
  [Module k M] [Module k N]
  [Module A M]
  [IsScalarTower k A M]
  [Module B N]
  [IsScalarTower k B N]

attribute [local instance] opModule actionsComm kOpComm kOpTower
attribute [local instance] ModuleCat.Algebra.Hochschild.uliftSMulCommClass

/-- Actual quotient maps ignore only the proof witness of the coefficient action law. -/
theorem positiveQuotientMap_witness_independent (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf hg : ∀ a m, f (a • m) = g a • f m) :
  letI : MonoidalCategoryStruct (ModuleCat.{max u v₁ v₂ z} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max u v₁ v₂ z} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v₁ v₂ z} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max u v₁ v₂ z} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v₁ v₂ z} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max u v₁ v₂ z} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v₁ v₂ z} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max u v₁ v₂ z} (R := k)
  positiveQuotientMap.{u, v₁, v₂, max u v₁ v₂ z} g f hf =
    positiveQuotientMap.{u, v₁, v₂, max u v₁ v₂ z} g f hg := by
  let : MonoidalCategoryStruct (ModuleCat.{max u v₁ v₂ z} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max u v₁ v₂ z} (R := k)
  let : MonoidalCategory (ModuleCat.{max u v₁ v₂ z} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max u v₁ v₂ z} (R := k)
  let : MonoidalPreadditive (ModuleCat.{max u v₁ v₂ z} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max u v₁ v₂ z} (R := k)
  let : MonoidalLinear k (ModuleCat.{max u v₁ v₂ z} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max u v₁ v₂ z} (R := k)
  cases Subsingleton.elim hf hg
  rfl

end

section
variable {k : Type u} [CommRing k]
  {A : Type v₁} [CommRing A] [Algebra k A]
  {B : Type v₂} [CommRing B] [Algebra k B]
  {C : Type v₃} [CommRing C] [Algebra k C]
  {M N P : Type (max u v₁ v₂ v₃ z)} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module k M] [Module k N] [Module k P]
  [Module A M]
  [IsScalarTower k A M]
  [Module B N]
  [IsScalarTower k B N]
  [Module C P]
  [IsScalarTower k C P]

attribute [local instance] opModule actionsComm kOpComm kOpTower
attribute [local instance] ModuleCat.Algebra.Hochschild.uliftSMulCommClass

/-- The proved coefficient-map composition descends through the original quotient. -/
theorem positiveQuotientMap_comp (g : A →ₐ[k] B) (h : B →ₐ[k] C)
    (f : M →ₗ[k] N) (f' : N →ₗ[k] P)
    (hf : ∀ a m, f (a • m) = g a • f m)
    (hf' : ∀ b n, f' (b • n) = h b • f' n) :
  letI : MonoidalCategoryStruct (ModuleCat.{max u v₁ v₂ v₃ z} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max u v₁ v₂ v₃ z} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v₁ v₂ v₃ z} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max u v₁ v₂ v₃ z} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v₁ v₂ v₃ z} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max u v₁ v₂ v₃ z} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v₁ v₂ v₃ z} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max u v₁ v₂ v₃ z} (R := k)
  positiveQuotientMap.{u, v₁, v₂, max u v₁ v₂ v₃ z} g f hf ≫
    positiveQuotientMap.{u, v₂, v₃, max u v₁ v₂ v₃ z} h f' hf' =
  positiveQuotientMap.{u, v₁, v₃, max u v₁ v₂ v₃ z} (h.comp g) (f'.comp f)
    (fun a m => (congrArg f' (hf a m)).trans (hf' (g a) (f m))) := by
  let : MonoidalCategoryStruct (ModuleCat.{max u v₁ v₂ v₃ z} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max u v₁ v₂ v₃ z} (R := k)
  let : MonoidalCategory (ModuleCat.{max u v₁ v₂ v₃ z} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max u v₁ v₂ v₃ z} (R := k)
  let : MonoidalPreadditive (ModuleCat.{max u v₁ v₂ v₃ z} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max u v₁ v₂ v₃ z} (R := k)
  let : MonoidalLinear k (ModuleCat.{max u v₁ v₂ v₃ z} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max u v₁ v₂ v₃ z} (R := k)
  let π := HomologicalComplex.ChainGradedPairing.positiveImageProjection
    (pairing k A M) (boundary_one_zero k A (ULift.{max u v₁ v₂ v₃ z} A)) (boundary_one_zero k A M)
  let : Epi π := positiveProjection_epi _ _ _
  apply (cancel_epi π).1
  rw [← Category.assoc, positiveQuotientMap_projection, Category.assoc,
    positiveQuotientMap_projection, ← Category.assoc, coefficientChainMap_comp,
    ← positiveQuotientMap_projection]

end

end Symmetric
end ModuleCat.Algebra.Hochschild
