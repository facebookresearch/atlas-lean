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

public import MathlibExt.RingTheory.DifferentialGraded.TwistingAugmentationFactor
public import MathlibExt.RingTheory.DifferentialGraded.TensorPowers
public import MathlibExt.RingTheory.DifferentialGraded.ReducedKernels

/-!
# Reduced coproducts and finite coradical-stage predicates

Let C be a cochain comonoid of modules over a commutative ring R, with the stated graded
tensor coproduct, empty-colimit preservation and iterated tensor coherence structures. For η :
I → C, set L_η = λ_C⁻¹ ≫ (η ⊗ id), R_η = ρ_C⁻¹ ≫ (id ⊗ η), and U_η = ε_C ≫ λ_I⁻¹ ≫ (η ⊗ η).
Reduced data require η to preserve the canonical unit comonoid, Δ_C = b + L_η + R_η − U_η, and
vanishing of b on η and on both counit legs. The canonical expression b = Δ_C−L_η−R_η+U_η has
these properties when η preserves counit and coproduct.

For any b : C → C ⊗ C, define b^{[0]} = λ_C⁻¹ and b^{[n+1]} = b ≫ (b^{[n]} ⊗ id), landing in
the left-associated power P_{n+1}(C). Stage n in degree i is the kernel condition
b^{[n+1]}_i(x)=0. Elementwise conilpotence consists of reduced data together with exhaustion
by these stages, with a bound allowed to depend on the degree and element.

For reduced data, the map b descends through Q = Coker(η) after projecting both tensor legs,
giving a coassociative map Q → Q ⊗ Q. Coassociative finite iterates split into blocks of
lengths m+1 and n+1 through the tensor-power comparison. The reduced maps and their quotient
descents obey the stated projection and naturality equations.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

namespace CochainComplex

variable {R : Type*} [CommRing R]
variable {C : CochainComplex (ModuleCat R) ℤ}

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

variable [ComonObj C]

/-- Reduced coproduct data for a coaugmentation.

For a cochain comonoid C with coaugmentation η : I → C, a map b : C → C ⊗ C satisfies
IsRedComul when η is a comonoid morphism from the canonical unit, Δ_C = b + L_η + R_η − U_η, η
≫ b = 0, and b vanishes after either counit tensor leg. Here L_η = λ_C⁻¹ ≫ (η ⊗ id), R_η =
ρ_C⁻¹ ≫ (id ⊗ η), and U_η = ε_C ≫ λ_I⁻¹ ≫ (η ⊗ η). -/
def IsRedComul (η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C)
    (Δbar : C ⟶ HomologicalComplex.tensorObj C C) : Prop :=
  (letI := ComonObj.instTensorUnit (CochainComplex (ModuleCat R) ℤ)
    ; IsComonHom η) ∧
    ComonObj.comul (X := C) =
      Δbar +
        ((HomologicalComplex.leftUnitor C).inv ≫
          HomologicalComplex.tensorHom η (𝟙 C)) +
        ((HomologicalComplex.rightUnitor C).inv ≫
          HomologicalComplex.tensorHom (𝟙 C) η) -
        (ComonObj.counit (X := C) ≫
          (HomologicalComplex.leftUnitor _).inv ≫
          HomologicalComplex.tensorHom η η) ∧
    η ≫ Δbar = 0 ∧
    Δbar ≫ HomologicalComplex.tensorHom (ComonObj.counit (X := C)) (𝟙 C) = 0 ∧
    Δbar ≫ HomologicalComplex.tensorHom (𝟙 C) (ComonObj.counit (X := C)) = 0

/-- Finite left-associated iterates of a reduced-coproduct map.

For any cochain map b : C → C ⊗ C, define b^{[0]} = λ_C⁻¹ : C → P₁(C) and b^{[n+1]} = b ≫
(b^{[n]} ⊗ id_C). Thus b^{[n]} lands in the recursive tensor power P_{n+1}(C). The stated
graded tensor and unit structures define these finite maps. -/
noncomputable def redComulPowFrom
    (Δbar : C ⟶ HomologicalComplex.tensorObj C C) :
    ∀ n, C ⟶ tensorPowObj C (n + 1)
  | 0 => (HomologicalComplex.leftUnitor C).symm.hom
  | n + 1 => Δbar ≫ HomologicalComplex.tensorHom (redComulPowFrom Δbar n) (𝟙 C)

omit [∀ (X : ModuleCat R), PreservesColimit (Functor.empty.{0} (ModuleCat R))
  ((curriedTensor (ModuleCat R)).obj X)] [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃] [ComonObj C] in
/-- Initial reduced-coproduct iterate.

For b : C → C ⊗ C, redComulPowFrom b 0 is λ_C⁻¹ : C → I ⊗ C = P₁(C), retaining the initial
unit factor. -/
@[simp]
theorem redComulPowFrom_zero
    (Δbar : C ⟶ HomologicalComplex.tensorObj C C) :
    redComulPowFrom Δbar 0 = (HomologicalComplex.leftUnitor C).symm.hom :=
  rfl

omit [∀ (X : ModuleCat R), PreservesColimit (Functor.empty.{0} (ModuleCat R))
  ((curriedTensor (ModuleCat R)).obj X)] [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃] [ComonObj C] in
/-- Successor reduced-coproduct iterate.

For b : C → C ⊗ C and n : ℕ, redComulPowFrom b (n+1) is b followed by redComulPowFrom b n on
the left tensor factor and identity on the right. Its target is P_{n+2}(C). -/
@[simp]
theorem redComulPowFrom_succ
    (Δbar : C ⟶ HomologicalComplex.tensorObj C C) (n : ℕ) :
    redComulPowFrom Δbar (n + 1) =
      Δbar ≫ HomologicalComplex.tensorHom (redComulPowFrom Δbar n) (𝟙 C) :=
  rfl

/-- Finite-stage vanishing in an iterated reduced coproduct.

For b : C → C ⊗ C, n : ℕ, i : ℤ and x ∈ C_i, IsInFilt b n i x means that the degree-i
component of b^{[n+1]} annihilates x. The iterate has n+2 tensor factors, and stage zero is
the kernel condition for b up to unit comparison. -/
def IsInFilt (Δbar : C ⟶ HomologicalComplex.tensorObj C C) (n : ℕ) (i : ℤ)
    (x : C.X i) : Prop :=
  ((redComulPowFrom Δbar (n + 1)).f i) x = 0

/-- Elementwise exhaustion by reduced-coproduct stages.

For η : I → C and b : C → C ⊗ C, require IsRedComul η b and, for every degree i and element x
∈ C_i, some natural stage n with b^{[n+1]}_i(x)=0. The bound may depend on both i and x. -/
def IsConilpotent (η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C)
    (Δbar : C ⟶ HomologicalComplex.tensorObj C C) : Prop :=
  IsRedComul η Δbar ∧ ∀ (i : ℤ) (x : C.X i), ∃ n, IsInFilt Δbar n i x

omit [∀ (X : ModuleCat R), PreservesColimit (Functor.empty.{0} (ModuleCat R))
  ((curriedTensor (ModuleCat R)).obj X)] [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃] [ComonObj C] in
/-- Zero element in every reduced-coproduct stage.

For every b : C → C ⊗ C, stage n and integer degree i, the zero element of C_i satisfies
IsInFilt b n i, since each iterate component is linear. -/
theorem IsInFilt_zero (Δbar : C ⟶ HomologicalComplex.tensorObj C C)
    (n : ℕ) (i : ℤ) :
    IsInFilt Δbar n i 0 :=
  map_zero _

/-- Reduced coproduct on a coaugmentation quotient.

For IsRedComul η b, let Q = Coker(η) with projection π : C → Q. The map b ≫ (π ⊗ π)
annihilates η and therefore descends uniquely to ρ : Q → Q ⊗ Q. This defines redComul η b. -/
noncomputable def redComul
    (η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C)
    (Δbar : C ⟶ HomologicalComplex.tensorObj C C)
    (h : IsRedComul η Δbar) :
    coaugCoideal η ⟶
      HomologicalComplex.tensorObj (coaugCoideal η) (coaugCoideal η) := by
  refine coaugCoideal_desc η
    (Δbar ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
      (coaugCoidealπ η)) ?_
  rw [← Category.assoc, h.2.2.1, zero_comp]

/-- Projection equation for the descended reduced coproduct.

For Q = Coker(η), π : C → Q and reduced data IsRedComul η b, the descended map ρ satisfies π ≫
ρ = b ≫ (π ⊗ π). -/
theorem redComul_π
    (η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C)
    (Δbar : C ⟶ HomologicalComplex.tensorObj C C)
    (h : IsRedComul η Δbar) :
    coaugCoidealπ η ≫ redComul η Δbar h =
      Δbar ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
        (coaugCoidealπ η) := by
  unfold redComul
  exact coaugCoideal_π_desc η _ _

/-- Uniqueness of a descended reduced coproduct.

For reduced data IsRedComul η b, any g : Q → Q ⊗ Q satisfying π ≫ g = b ≫ (π ⊗ π) equals
redComul η b. This is uniqueness in the cokernel universal property. -/
theorem redComul_unique
    (η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C)
    (Δbar : C ⟶ HomologicalComplex.tensorObj C C)
    (h : IsRedComul η Δbar)
    (g : coaugCoideal η ⟶ HomologicalComplex.tensorObj (coaugCoideal η)
      (coaugCoideal η))
    (hg : coaugCoidealπ η ≫ g = Δbar ≫ HomologicalComplex.tensorHom
      (coaugCoidealπ η) (coaugCoidealπ η)) :
    g = redComul η Δbar h := by
  unfold redComul
  exact coaugCoideal_desc_unique η _ _ g hg

/-- Agreement of full and reduced coproducts after quotienting both legs.

For IsRedComul η b and Q = Coker(η), Δ_C ≫ (π ⊗ π) = b ≫ (π ⊗ π). The two
single-coaugmentation terms and the double-coaugmentation term vanish because η ≫ π = 0. -/
theorem redComul_legTransfer
    (η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C)
    (Δbar : C ⟶ HomologicalComplex.tensorObj C C)
    (h : IsRedComul η Δbar) :
    ComonObj.comul (X := C) ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
        (coaugCoidealπ η) =
      Δbar ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
        (coaugCoidealπ η) := by
  have hdecomp := h.2.1
  have hL : ((HomologicalComplex.leftUnitor C).inv ≫
      HomologicalComplex.tensorHom η (𝟙 C)) ≫
      HomologicalComplex.tensorHom (coaugCoidealπ η) (coaugCoidealπ η) = 0 := by
    rw [Category.assoc, HomologicalComplex.tensorHom_comp_tensorHom,
      coaugCoideal_condition, zero_tensorHom, comp_zero]
  have hR : ((HomologicalComplex.rightUnitor C).inv ≫
      HomologicalComplex.tensorHom (𝟙 C) η) ≫
      HomologicalComplex.tensorHom (coaugCoidealπ η) (coaugCoidealπ η) = 0 := by
    rw [Category.assoc, HomologicalComplex.tensorHom_comp_tensorHom,
      coaugCoideal_condition, tensorHom_zero, comp_zero]
  have hU : (ComonObj.counit (X := C) ≫
      (HomologicalComplex.leftUnitor _).inv ≫
        HomologicalComplex.tensorHom η η) ≫
      HomologicalComplex.tensorHom (coaugCoidealπ η) (coaugCoidealπ η) = 0 := by
    rw [Category.assoc, Category.assoc, HomologicalComplex.tensorHom_comp_tensorHom,
      coaugCoideal_condition, zero_tensorHom, comp_zero,
      comp_zero]
  rw [hdecomp, Preadditive.sub_comp, Preadditive.add_comp,
    Preadditive.add_comp, hL, hR, hU, add_zero, add_zero, sub_zero]

/-- Coassociativity of the descended reduced coproduct.

For reduced data IsRedComul η b, the map ρ : Q → Q ⊗ Q on Q = Coker(η) satisfies ρ ≫ (id_Q ⊗
ρ) = ρ ≫ (ρ ⊗ id_Q) ≫ α_{Q,Q,Q}. This states coassociativity of the reduced map. -/
theorem redComul_coassoc
    (η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C)
    (Δbar : C ⟶ HomologicalComplex.tensorObj C C)
    (h : IsRedComul η Δbar) :
    redComul η Δbar h ≫
        coaugCoideal η ◁ redComul η Δbar h =
      redComul η Δbar h ≫
        (redComul η Δbar h ▷ coaugCoideal η) ≫
        (α_ (coaugCoideal η) (coaugCoideal η) (coaugCoideal η)).hom := by
  have hπ := redComul_π η Δbar h
  have hleg := redComul_legTransfer η Δbar h
  have hdecomp := h.2.1
  have hη : η ≫ (Δbar ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
      (coaugCoidealπ η)) = 0 := by
    rw [← Category.assoc, h.2.2.1, zero_comp]
  have hLHS : coaugCoidealπ η ≫ (redComul η Δbar h ≫
      coaugCoideal η ◁ redComul η Δbar h) =
      Δbar ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
        (Δbar ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
          (coaugCoidealπ η)) := by
    erw [← Category.assoc, hπ, Category.assoc,
      MonoidalCategory.tensorHom_comp_whiskerLeft, hπ]
    rfl
  have hRHS : coaugCoidealπ η ≫ (redComul η Δbar h ≫
      (redComul η Δbar h ▷ coaugCoideal η) ≫
        (α_ (coaugCoideal η) (coaugCoideal η) (coaugCoideal η)).hom) =
      Δbar ≫ ((HomologicalComplex.tensorHom
        (Δbar ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
          (coaugCoidealπ η)) (coaugCoidealπ η)) ≫
        (α_ (coaugCoideal η) (coaugCoideal η)
          (coaugCoideal η)).hom) := by
    erw [← Category.assoc (coaugCoidealπ η) (redComul η Δbar h)
      ((redComul η Δbar h ▷ coaugCoideal η) ≫
        (α_ (coaugCoideal η) (coaugCoideal η) (coaugCoideal η)).hom), hπ,
      ← Category.assoc
        (Δbar ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
          (coaugCoidealπ η))
        (redComul η Δbar h ▷ coaugCoideal η)
        (α_ (coaugCoideal η) (coaugCoideal η) (coaugCoideal η)).hom,
      Category.assoc Δbar
        (HomologicalComplex.tensorHom (coaugCoidealπ η) (coaugCoidealπ η))
        (redComul η Δbar h ▷ coaugCoideal η),
      MonoidalCategory.tensorHom_comp_whiskerRight, hπ, Category.assoc]
  have hbase := ComonObj.comul_assoc C
  have hpost : (ComonObj.comul (X := C) ≫
      C ◁ ComonObj.comul (X := C)) ≫
        HomologicalComplex.tensorHom (coaugCoidealπ η)
          (HomologicalComplex.tensorHom (coaugCoidealπ η) (coaugCoidealπ η)) =
      (ComonObj.comul (X := C) ≫ ((ComonObj.comul (X := C) ▷ C) ≫
        (α_ C C C).hom)) ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
          (HomologicalComplex.tensorHom (coaugCoidealπ η)
            (coaugCoidealπ η)) := by
    rw [hbase]
  erw [Category.assoc (ComonObj.comul (X := C))
    (C ◁ ComonObj.comul (X := C))
    (HomologicalComplex.tensorHom (coaugCoidealπ η)
      (HomologicalComplex.tensorHom (coaugCoidealπ η) (coaugCoidealπ η))),
    MonoidalCategory.whiskerLeft_comp_tensorHom] at hpost
  have hnat : (HomologicalComplex.tensorHom
      (HomologicalComplex.tensorHom (coaugCoidealπ η) (coaugCoidealπ η))
        (coaugCoidealπ η)) ≫
        (α_ (coaugCoideal η) (coaugCoideal η) (coaugCoideal η)).hom =
      (α_ C C C).hom ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
        (HomologicalComplex.tensorHom (coaugCoidealπ η)
          (coaugCoidealπ η)) :=
    MonoidalCategory.associator_naturality (coaugCoidealπ η)
      (coaugCoidealπ η) (coaugCoidealπ η)
  erw [Category.assoc (ComonObj.comul (X := C))
    ((ComonObj.comul (X := C) ▷ C) ≫ (α_ C C C).hom)
    (HomologicalComplex.tensorHom (coaugCoidealπ η)
      (HomologicalComplex.tensorHom (coaugCoidealπ η) (coaugCoidealπ η))),
    Category.assoc (ComonObj.comul (X := C) ▷ C) (α_ C C C).hom
    (HomologicalComplex.tensorHom (coaugCoidealπ η)
      (HomologicalComplex.tensorHom (coaugCoidealπ η) (coaugCoidealπ η))),
    ← hnat,
    ← Category.assoc (ComonObj.comul (X := C) ▷ C)
      (HomologicalComplex.tensorHom
        (HomologicalComplex.tensorHom (coaugCoidealπ η) (coaugCoidealπ η))
        (coaugCoidealπ η))
      (α_ (coaugCoideal η) (coaugCoideal η) (coaugCoideal η)).hom,
    MonoidalCategory.whiskerRight_comp_tensorHom] at hpost
  rw [hleg] at hpost
  have hSL : ComonObj.comul (X := C) ≫ HomologicalComplex.tensorHom
      (coaugCoidealπ η) (Δbar ≫ HomologicalComplex.tensorHom
        (coaugCoidealπ η) (coaugCoidealπ η)) =
      Δbar ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
        (Δbar ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
          (coaugCoidealπ η)) := by
    have V1 : ((HomologicalComplex.leftUnitor C).inv ≫
        HomologicalComplex.tensorHom η (𝟙 C)) ≫
        HomologicalComplex.tensorHom (coaugCoidealπ η)
          (Δbar ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
            (coaugCoidealπ η)) = 0 := by
      rw [Category.assoc, HomologicalComplex.tensorHom_comp_tensorHom,
        coaugCoideal_condition, zero_tensorHom, comp_zero]
    have V2 : ((HomologicalComplex.rightUnitor C).inv ≫
        HomologicalComplex.tensorHom (𝟙 C) η) ≫
        HomologicalComplex.tensorHom (coaugCoidealπ η)
          (Δbar ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
            (coaugCoidealπ η)) = 0 := by
      rw [Category.assoc, HomologicalComplex.tensorHom_comp_tensorHom, hη,
        tensorHom_zero, comp_zero]
    have V3 : (ComonObj.counit (X := C) ≫
        (HomologicalComplex.leftUnitor _).inv ≫
          HomologicalComplex.tensorHom η η) ≫
        HomologicalComplex.tensorHom (coaugCoidealπ η)
          (Δbar ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
            (coaugCoidealπ η)) = 0 := by
      rw [Category.assoc, Category.assoc,
        HomologicalComplex.tensorHom_comp_tensorHom, coaugCoideal_condition,
        hη, zero_tensorHom, comp_zero, comp_zero]
    rw [hdecomp, Preadditive.sub_comp, Preadditive.add_comp,
      Preadditive.add_comp, V1, V2, V3, add_zero, add_zero, sub_zero]
  have hSR : ComonObj.comul (X := C) ≫
      ((HomologicalComplex.tensorHom
        (Δbar ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
          (coaugCoidealπ η)) (coaugCoidealπ η)) ≫
        (α_ (coaugCoideal η) (coaugCoideal η)
          (coaugCoideal η)).hom) =
      Δbar ≫ ((HomologicalComplex.tensorHom
        (Δbar ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
          (coaugCoidealπ η)) (coaugCoidealπ η)) ≫
        (α_ (coaugCoideal η) (coaugCoideal η)
          (coaugCoideal η)).hom) := by
    have V4 : ((HomologicalComplex.leftUnitor C).inv ≫
        HomologicalComplex.tensorHom η (𝟙 C)) ≫
        ((HomologicalComplex.tensorHom
          (Δbar ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
            (coaugCoidealπ η)) (coaugCoidealπ η)) ≫
          (α_ (coaugCoideal η) (coaugCoideal η)
            (coaugCoideal η)).hom) = 0 := by
      rw [Category.assoc,
        ← Category.assoc (HomologicalComplex.tensorHom η (𝟙 C))
          (HomologicalComplex.tensorHom
            (Δbar ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
              (coaugCoidealπ η)) (coaugCoidealπ η))
          (α_ (coaugCoideal η) (coaugCoideal η) (coaugCoideal η)).hom,
        HomologicalComplex.tensorHom_comp_tensorHom, hη, zero_tensorHom,
        zero_comp, comp_zero]
    have V5 : ((HomologicalComplex.rightUnitor C).inv ≫
        HomologicalComplex.tensorHom (𝟙 C) η) ≫
        ((HomologicalComplex.tensorHom
          (Δbar ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
            (coaugCoidealπ η)) (coaugCoidealπ η)) ≫
          (α_ (coaugCoideal η) (coaugCoideal η)
            (coaugCoideal η)).hom) = 0 := by
      rw [Category.assoc,
        ← Category.assoc (HomologicalComplex.tensorHom (𝟙 C) η)
          (HomologicalComplex.tensorHom
            (Δbar ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
              (coaugCoidealπ η)) (coaugCoidealπ η))
          (α_ (coaugCoideal η) (coaugCoideal η) (coaugCoideal η)).hom,
        HomologicalComplex.tensorHom_comp_tensorHom, coaugCoideal_condition,
        tensorHom_zero, zero_comp, comp_zero]
    have V6 : (ComonObj.counit (X := C) ≫
        (HomologicalComplex.leftUnitor _).inv ≫
          HomologicalComplex.tensorHom η η) ≫
        ((HomologicalComplex.tensorHom
          (Δbar ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
            (coaugCoidealπ η)) (coaugCoidealπ η)) ≫
          (α_ (coaugCoideal η) (coaugCoideal η)
            (coaugCoideal η)).hom) = 0 := by
      rw [Category.assoc, Category.assoc,
        ← Category.assoc (HomologicalComplex.tensorHom η η)
          (HomologicalComplex.tensorHom
            (Δbar ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
              (coaugCoidealπ η)) (coaugCoidealπ η))
          (α_ (coaugCoideal η) (coaugCoideal η) (coaugCoideal η)).hom,
        HomologicalComplex.tensorHom_comp_tensorHom, hη,
        coaugCoideal_condition, zero_tensorHom, zero_comp,
        comp_zero, comp_zero]
    rw [hdecomp, Preadditive.sub_comp, Preadditive.add_comp,
      Preadditive.add_comp, V4, V5, V6, add_zero, add_zero, sub_zero]
  have hdone : Δbar ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
      (Δbar ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
        (coaugCoidealπ η)) =
      Δbar ≫ ((HomologicalComplex.tensorHom
        (Δbar ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
          (coaugCoidealπ η)) (coaugCoidealπ η)) ≫
        (α_ (coaugCoideal η) (coaugCoideal η)
          (coaugCoideal η)).hom) := by
    rw [← hSL, ← hSR]
    exact hpost
  have key : coaugCoidealπ η ≫ (redComul η Δbar h ≫
      coaugCoideal η ◁ redComul η Δbar h) =
      coaugCoidealπ η ≫ (redComul η Δbar h ≫
        (redComul η Δbar h ▷ coaugCoideal η) ≫
        (α_ (coaugCoideal η) (coaugCoideal η)
          (coaugCoideal η)).hom) := by
    rw [hLHS, hRHS]
    exact hdone
  exact Cofork.IsColimit.hom_ext (cokernelIsCokernel η) key

private theorem redComulUnitTensorStep
    {D : Type*} [Category D] [MonoidalCategory D] {X P : D}
    (δ : X ⟶ X ⊗ X) (f : X ⟶ P) :
    (δ ≫ (f ⊗ₘ 𝟙 X)) ≫
        (((ρ_ P).inv ⊗ₘ 𝟙 X) ≫ (α_ P (𝟙_ D) X).hom) =
      δ ≫ (f ⊗ₘ (λ_ X).inv) := by
  have hTri : ((ρ_ P).inv ⊗ₘ 𝟙 X) ≫ (α_ P (𝟙_ D) X).hom =
      𝟙 P ⊗ₘ (λ_ X).inv := by
    simpa only [MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom] using
      MonoidalCategory.triangle_assoc_comp_right_inv P X
  rw [hTri, Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom]
  simp only [Category.comp_id, Category.id_comp]

private theorem redComulCoassocTensorStep
    {D : Type*} [Category D] [MonoidalCategory D] {X P Q A : D}
    (δ : X ⟶ X ⊗ X)
    (hcoassoc : δ ≫ (𝟙 X ⊗ₘ δ) =
      δ ≫ (δ ⊗ₘ 𝟙 X) ≫ (α_ X X X).hom)
    (f : X ⟶ P) (g : X ⟶ Q) (r : X ⟶ A) (a : A ⟶ P ⊗ Q)
    (h : r ≫ a = δ ≫ (f ⊗ₘ g)) :
    (δ ≫ (r ⊗ₘ 𝟙 X)) ≫ ((a ⊗ₘ 𝟙 X) ≫ (α_ P Q X).hom) =
      δ ≫ (f ⊗ₘ (δ ≫ (g ⊗ₘ 𝟙 X))) := by
  have hLeft : (r ⊗ₘ 𝟙 X) ≫ (a ⊗ₘ 𝟙 X) = (r ≫ a) ⊗ₘ 𝟙 X := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]
  have hSplit : (δ ≫ (f ⊗ₘ g)) ⊗ₘ 𝟙 X =
      (δ ⊗ₘ 𝟙 X) ≫ ((f ⊗ₘ g) ⊗ₘ 𝟙 X) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]
  have hAssoc : ((f ⊗ₘ g) ⊗ₘ 𝟙 X) ≫ (α_ P Q X).hom =
      (α_ X X X).hom ≫ (f ⊗ₘ (g ⊗ₘ 𝟙 X)) :=
    MonoidalCategory.associator_naturality f g (𝟙 X)
  calc
    _ = δ ≫ (((r ⊗ₘ 𝟙 X) ≫ (a ⊗ₘ 𝟙 X)) ≫ (α_ P Q X).hom) := by
      simp only [Category.assoc]
    _ = δ ≫ (((r ≫ a) ⊗ₘ 𝟙 X) ≫ (α_ P Q X).hom) := by rw [hLeft]
    _ = δ ≫ (((δ ≫ (f ⊗ₘ g)) ⊗ₘ 𝟙 X) ≫ (α_ P Q X).hom) := by rw [h]
    _ = δ ≫ (δ ⊗ₘ 𝟙 X) ≫ (α_ X X X).hom ≫ (f ⊗ₘ (g ⊗ₘ 𝟙 X)) := by
      rw [hSplit]
      simp only [Category.assoc]
      rw [hAssoc]
    _ = δ ≫ (𝟙 X ⊗ₘ δ) ≫ (f ⊗ₘ (g ⊗ₘ 𝟙 X)) := by
      simpa only [Category.assoc] using
        congrArg (fun k => k ≫ (f ⊗ₘ (g ⊗ₘ 𝟙 X))) hcoassoc.symm
    _ = _ := by
      rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp]

omit [ComonObj C] in
/-- Block-splitting identity for coassociative reduced iterates.

Let b : C → C ⊗ C satisfy b ≫ (id ⊗ b) = b ≫ (b ⊗ id) ≫ α. With the stated tensor-power
coherence, b^{[m+1+n]} followed by P_{m+n+2}(C) ≅ P_{m+1}(C) ⊗ P_{n+1}(C) equals b ≫ (b^{[m]}
⊗ b^{[n]}), for all natural m,n. This statement uses an arbitrary coassociative map b. -/
theorem redComulPowFrom_split
    (Δbar : C ⟶ HomologicalComplex.tensorObj C C)
    (hcoassoc : Δbar ≫ HomologicalComplex.tensorHom (𝟙 C) Δbar =
      Δbar ≫ HomologicalComplex.tensorHom Δbar (𝟙 C) ≫ (α_ C C C).hom)
    (m n : ℕ) :
    redComulPowFrom Δbar (m + 1 + n) ≫
      (tensorPowObj_add C (m + 1) (n + 1)).hom =
    Δbar ≫ HomologicalComplex.tensorHom (redComulPowFrom Δbar m)
      (redComulPowFrom Δbar n) := by
  induction n with
  | zero =>
    have hR0 : redComulPowFrom Δbar 0 =
        (HomologicalComplex.leftUnitor C).symm.hom := rfl
    have hRsucc : redComulPowFrom Δbar (m + 1) =
        Δbar ≫ HomologicalComplex.tensorHom (redComulPowFrom Δbar m)
          (𝟙 C) := rfl
    have hE0 : (eqToIso (congrArg (tensorPowObj C)
        (Nat.add_zero (m + 1)))).hom = 𝟙 _ := rfl
    have hAdd0 : (tensorPowObj_add C (m + 1) 0).hom =
        (HomologicalComplex.rightUnitor (tensorPowObj C (m + 1))).symm.hom := by
      rw [tensorPowObj_add_zero_right, hE0,
        CategoryTheory.Category.id_comp]
    have hE1 : (eqToIso (congrArg (tensorPowObj C)
        (Nat.add_succ (m + 1) 0))).hom = 𝟙 _ := rfl
    have hIso0 : (tensorIsoRight (tensorPowObj_add C (m + 1) 0)).hom =
        HomologicalComplex.tensorHom
          (tensorPowObj_add C (m + 1) 0).hom (𝟙 C) := rfl
    have hAdd1 : (tensorPowObj_add C (m + 1) 1).hom =
        HomologicalComplex.tensorHom
          (HomologicalComplex.rightUnitor
            (tensorPowObj C (m + 1))).symm.hom (𝟙 C) ≫
          (HomologicalComplex.associator (tensorPowObj C (m + 1))
            (tensorPowObj C 0) C).hom := by
      have hDef : (tensorPowObj_add C (m + 1) 1).hom =
          (eqToIso (congrArg (tensorPowObj C)
            (Nat.add_succ (m + 1) 0))).hom ≫
            (tensorIsoRight (tensorPowObj_add C (m + 1) 0)).hom ≫
            (HomologicalComplex.associator (tensorPowObj C (m + 1))
              (tensorPowObj C 0) C).hom := rfl
      rw [hDef, hE1, CategoryTheory.Category.id_comp, hIso0, hAdd0]
      rfl
    change redComulPowFrom Δbar (m + 1) ≫
        (tensorPowObj_add C (m + 1) 1).hom =
      Δbar ≫ HomologicalComplex.tensorHom (redComulPowFrom Δbar m)
        (redComulPowFrom Δbar 0)
    simp only [hRsucc, hR0, hAdd1]
    change (Δbar ≫ HomologicalComplex.tensorHom (redComulPowFrom Δbar m)
          (𝟙 C)) ≫
        (HomologicalComplex.tensorHom (HomologicalComplex.rightUnitor
          (tensorPowObj C (m + 1))).symm.hom (𝟙 C) ≫
          (HomologicalComplex.associator (tensorPowObj C (m + 1))
            (HomologicalComplex.tensorUnit (ModuleCat R)
              (ComplexShape.up ℤ)) C).hom) =
      Δbar ≫ HomologicalComplex.tensorHom (redComulPowFrom Δbar m)
        (HomologicalComplex.leftUnitor C).symm.hom
    exact redComulUnitTensorStep
      (D := CochainComplex (ModuleCat R) ℤ) Δbar (redComulPowFrom Δbar m)
  | succ k ih =>
    have hRsucc : redComulPowFrom Δbar (m + 1 + (k + 1)) =
        Δbar ≫ HomologicalComplex.tensorHom
          (redComulPowFrom Δbar (m + 1 + k)) (𝟙 C) := rfl
    have hE : (eqToIso (congrArg (tensorPowObj C)
        (Nat.add_succ (m + 1) (k + 1)))).hom = 𝟙 _ := rfl
    have hAdd : (tensorPowObj_add C (m + 1) (k + 1 + 1)).hom =
        HomologicalComplex.tensorHom
          (tensorPowObj_add C (m + 1) (k + 1)).hom (𝟙 C) ≫
          (HomologicalComplex.associator _ _ _).hom := by
      have hDef : (tensorPowObj_add C (m + 1) (k + 1 + 1)).hom =
          (eqToIso (congrArg (tensorPowObj C)
            (Nat.add_succ (m + 1) (k + 1)))).hom ≫
            (tensorIsoRight
              (tensorPowObj_add C (m + 1) (k + 1))).hom ≫
            (HomologicalComplex.associator _ _ _).hom := rfl
      rw [hDef, hE, CategoryTheory.Category.id_comp]
      rfl
    have hRstep : redComulPowFrom Δbar (k + 1) =
        Δbar ≫ HomologicalComplex.tensorHom (redComulPowFrom Δbar k)
          (𝟙 C) := rfl
    simp only [hRsucc, hAdd, hRstep]
    change (Δbar ≫ HomologicalComplex.tensorHom (redComulPowFrom Δbar (m + 1 + k))
          (𝟙 C)) ≫
        (HomologicalComplex.tensorHom (tensorPowObj_add C (m + 1) (k + 1)).hom
          (𝟙 C) ≫
          (HomologicalComplex.associator (tensorPowObj C (m + 1))
            (tensorPowObj C (k + 1)) C).hom) =
      Δbar ≫ HomologicalComplex.tensorHom (redComulPowFrom Δbar m)
        (Δbar ≫ HomologicalComplex.tensorHom (redComulPowFrom Δbar k) (𝟙 C))
    exact redComulCoassocTensorStep
      (D := CochainComplex (ModuleCat R) ℤ) Δbar hcoassoc
      (redComulPowFrom Δbar m) (redComulPowFrom Δbar k)
      (redComulPowFrom Δbar (m + 1 + k))
      (tensorPowObj_add C (m + 1) (k + 1)).hom ih

/-- Block splitting of descended reduced-coproduct iterates.

For ρ = redComul η b on Q = Coker(η), its coassociativity gives ρ^{[m+1+n]} followed by the
power-splitting comparison equal to ρ ≫ (ρ^{[m]} ⊗ ρ^{[n]}). The factors have lengths m+1 and
n+1. -/
theorem redComulPowFrom_split_redComul
    (η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C)
    (Δbar : C ⟶ HomologicalComplex.tensorObj C C)
    (h : IsRedComul η Δbar) (m n : ℕ) :
    redComulPowFrom (redComul η Δbar h) (m + 1 + n) ≫
      (tensorPowObj_add (coaugCoideal η) (m + 1) (n + 1)).hom =
    (redComul η Δbar h) ≫ HomologicalComplex.tensorHom
      (redComulPowFrom (redComul η Δbar h) m)
      (redComulPowFrom (redComul η Δbar h) n) := by
  have hbase := redComul_coassoc η Δbar h
  have hcoassoc : (redComul η Δbar h) ≫
        HomologicalComplex.tensorHom (𝟙 (coaugCoideal η))
          (redComul η Δbar h) =
      (redComul η Δbar h) ≫
        HomologicalComplex.tensorHom (redComul η Δbar h)
          (𝟙 (coaugCoideal η)) ≫
        (α_ (coaugCoideal η) (coaugCoideal η)
          (coaugCoideal η)).hom := by
    have hL : HomologicalComplex.tensorHom (𝟙 (coaugCoideal η))
          (redComul η Δbar h) =
        (coaugCoideal η ◁ redComul η Δbar h) := by
      change MonoidalCategory.tensorHom (𝟙 (coaugCoideal η))
        (redComul η Δbar h) = _
      rw [MonoidalCategory.id_tensorHom]
    have hR : HomologicalComplex.tensorHom (redComul η Δbar h)
          (𝟙 (coaugCoideal η)) =
        (redComul η Δbar h ▷ coaugCoideal η) := by
      change MonoidalCategory.tensorHom (redComul η Δbar h)
        (𝟙 (coaugCoideal η)) = _
      rw [MonoidalCategory.tensorHom_id]
    rw [hL, hR]
    exact hbase
  exact redComulPowFrom_split _ hcoassoc m n

/-- Naturality of compatible reduced coproduct data.

Let C,D be cochain comonoids with IsRedComul η_C b_C and IsRedComul η_D b_D. For a comonoid
map u : C → D satisfying η_C ≫ u = η_D, u ≫ b_D = b_C ≫ (u ⊗ u). The reduced maps are
determined by the full coproducts and coaugmentation terms. -/
theorem redComulCandidate_naturality
    {D : CochainComplex (ModuleCat R) ℤ} [ComonObj D]
    {ηC : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C}
    {ηD : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ D}
    {ΔbarC : C ⟶ HomologicalComplex.tensorObj C C}
    {ΔbarD : D ⟶ HomologicalComplex.tensorObj D D}
    (hRedC : IsRedComul ηC ΔbarC) (hRedD : IsRedComul ηD ΔbarD)
    (u : C ⟶ D) [IsComonHom u]
    (hη : ηC ≫ u = ηD) :
    u ≫ ΔbarD = ΔbarC ≫ HomologicalComplex.tensorHom u u := by
  have hC := hRedC.2.1
  have hD := hRedD.2.1
  have hcomul : u ≫ ComonObj.comul (X := D) =
      ComonObj.comul (X := C) ≫ HomologicalComplex.tensorHom u u :=
    IsComonHom.hom_comul u
  have hcounit : u ≫ ComonObj.counit (X := D) = ComonObj.counit (X := C) :=
    IsComonHom.hom_counit u
  have hL : u ≫ ((HomologicalComplex.leftUnitor D).inv ≫
      HomologicalComplex.tensorHom ηD (𝟙 D)) =
      ((HomologicalComplex.leftUnitor C).inv ≫
        HomologicalComplex.tensorHom ηC (𝟙 C)) ≫
        HomologicalComplex.tensorHom u u := by
    have hbridgeC : (HomologicalComplex.leftUnitor C).inv = (λ_ C).inv := rfl
    have hbridgeD : (HomologicalComplex.leftUnitor D).inv = (λ_ D).inv := rfl
    have hnat := MonoidalCategory.leftUnitor_inv_naturality u
    have e : (𝟙_ (CochainComplex (ModuleCat R) ℤ) ◁ u) =
        HomologicalComplex.tensorHom (𝟙 _) u := rfl
    have hLHS : u ≫ ((HomologicalComplex.leftUnitor D).inv ≫
          HomologicalComplex.tensorHom ηD (𝟙 D)) =
        (HomologicalComplex.leftUnitor C).inv ≫
          HomologicalComplex.tensorHom ηD u := by
      rw [hbridgeD, ← Category.assoc, hnat, e, Category.assoc,
        HomologicalComplex.tensorHom_comp_tensorHom,
        Category.id_comp, Category.comp_id, hbridgeC]
    have hRHS : ((HomologicalComplex.leftUnitor C).inv ≫
          HomologicalComplex.tensorHom ηC (𝟙 C)) ≫
          HomologicalComplex.tensorHom u u =
        (HomologicalComplex.leftUnitor C).inv ≫
          HomologicalComplex.tensorHom ηD u := by
      rw [Category.assoc, HomologicalComplex.tensorHom_comp_tensorHom,
        hη, Category.id_comp]
    exact hLHS.trans hRHS.symm
  have hR : u ≫ ((HomologicalComplex.rightUnitor D).inv ≫
      HomologicalComplex.tensorHom (𝟙 D) ηD) =
      ((HomologicalComplex.rightUnitor C).inv ≫
        HomologicalComplex.tensorHom (𝟙 C) ηC) ≫
        HomologicalComplex.tensorHom u u := by
    have hbridgeC : (HomologicalComplex.rightUnitor C).inv = (ρ_ C).inv := rfl
    have hbridgeD : (HomologicalComplex.rightUnitor D).inv = (ρ_ D).inv := rfl
    have hnat := MonoidalCategory.rightUnitor_inv_naturality u
    have e : (u ▷ 𝟙_ (CochainComplex (ModuleCat R) ℤ)) =
        HomologicalComplex.tensorHom u (𝟙 _) := rfl
    have hLHS : u ≫ ((HomologicalComplex.rightUnitor D).inv ≫
          HomologicalComplex.tensorHom (𝟙 D) ηD) =
        (HomologicalComplex.rightUnitor C).inv ≫
          HomologicalComplex.tensorHom u ηD := by
      rw [hbridgeD, ← Category.assoc, hnat, e, Category.assoc,
        HomologicalComplex.tensorHom_comp_tensorHom,
        Category.comp_id, Category.id_comp, hbridgeC]
    have hRHS : ((HomologicalComplex.rightUnitor C).inv ≫
          HomologicalComplex.tensorHom (𝟙 C) ηC) ≫
          HomologicalComplex.tensorHom u u =
        (HomologicalComplex.rightUnitor C).inv ≫
          HomologicalComplex.tensorHom u ηD := by
      rw [Category.assoc, HomologicalComplex.tensorHom_comp_tensorHom,
        hη, Category.id_comp]
    exact hLHS.trans hRHS.symm
  have hU : u ≫ (ComonObj.counit (X := D) ≫
      (HomologicalComplex.leftUnitor _).inv ≫
        HomologicalComplex.tensorHom ηD ηD) =
      (ComonObj.counit (X := C) ≫
        (HomologicalComplex.leftUnitor _).inv ≫
        HomologicalComplex.tensorHom ηC ηC) ≫
        HomologicalComplex.tensorHom u u := by
    have e : HomologicalComplex.tensorHom ηC ηC ≫
        HomologicalComplex.tensorHom u u =
        HomologicalComplex.tensorHom ηD ηD := by
      rw [HomologicalComplex.tensorHom_comp_tensorHom, hη]
    have hLHS : u ≫ (ComonObj.counit (X := D) ≫
          (HomologicalComplex.leftUnitor _).inv ≫
          HomologicalComplex.tensorHom ηD ηD) =
        ComonObj.counit (X := C) ≫
          (HomologicalComplex.leftUnitor _).inv ≫
          HomologicalComplex.tensorHom ηD ηD := by
      rw [← Category.assoc, hcounit]
    have hRHS : (ComonObj.counit (X := C) ≫
          (HomologicalComplex.leftUnitor _).inv ≫
          HomologicalComplex.tensorHom ηC ηC) ≫
          HomologicalComplex.tensorHom u u =
        ComonObj.counit (X := C) ≫
          (HomologicalComplex.leftUnitor _).inv ≫
          HomologicalComplex.tensorHom ηD ηD := by
      simp only [Category.assoc]
      rw [e]
    exact hLHS.trans hRHS.symm
  rw [hD, hC] at hcomul
  simp only [Preadditive.comp_add, Preadditive.comp_sub,
    Preadditive.add_comp, Preadditive.sub_comp, hL, hR, hU] at hcomul
  simp only [sub_eq_add_neg] at hcomul
  exact add_right_cancel (add_right_cancel (add_right_cancel hcomul))

/-- Naturality on coaugmentation quotients from a compatible projection square.

Suppose C,D have reduced data, u : D → C and u_Q : Q_D → Q_C satisfy π_D ≫ u_Q = u ≫ π_C and u
≫ b_C = b_D ≫ (u ⊗ u). Then u_Q ≫ ρ_C = ρ_D ≫ (u_Q ⊗ u_Q) for the descended reduced
coproducts. -/
theorem coideal_redComul_naturality
    (η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C)
    (Δbar : C ⟶ HomologicalComplex.tensorObj C C)
    (hRed : IsRedComul η Δbar)
    {D : CochainComplex (ModuleCat R) ℤ}
    [ComonObj D]
    (ηD : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ D)
    (ΔbarD : D ⟶ HomologicalComplex.tensorObj D D)
    (hRedD : IsRedComul ηD ΔbarD)
    (u : D ⟶ C)
    (uC : coaugCoideal ηD ⟶ coaugCoideal η)
    (hπ : coaugCoidealπ ηD ≫ uC = u ≫ coaugCoidealπ η)
    (hΔ : u ≫ Δbar =
      ΔbarD ≫ HomologicalComplex.tensorHom u u) :
    uC ≫ redComul η Δbar hRed =
      redComul ηD ΔbarD hRedD ≫
        HomologicalComplex.tensorHom uC uC := by
  apply Cofork.IsColimit.hom_ext (cokernelIsCokernel ηD)
  calc coaugCoidealπ ηD ≫
          (uC ≫ redComul η Δbar hRed) =
        u ≫ (coaugCoidealπ η ≫ redComul η Δbar hRed) := by
        rw [← Category.assoc, hπ, Category.assoc]
    _ = u ≫ (Δbar ≫ HomologicalComplex.tensorHom (coaugCoidealπ η)
          (coaugCoidealπ η)) := by
        rw [redComul_π]
    _ = ΔbarD ≫ HomologicalComplex.tensorHom (u ≫ coaugCoidealπ η)
          (u ≫ coaugCoidealπ η) := by
        rw [← Category.assoc, hΔ, Category.assoc,
          HomologicalComplex.tensorHom_comp_tensorHom]
    _ = ΔbarD ≫ HomologicalComplex.tensorHom (coaugCoidealπ ηD ≫ uC)
          (coaugCoidealπ ηD ≫ uC) := by
        rw [← hπ]
    _ = (ΔbarD ≫ HomologicalComplex.tensorHom (coaugCoidealπ ηD)
          (coaugCoidealπ ηD)) ≫
          HomologicalComplex.tensorHom uC uC := by
        rw [← HomologicalComplex.tensorHom_comp_tensorHom]
        simp only [Category.assoc]
    _ = coaugCoidealπ ηD ≫ (redComul ηD ΔbarD hRedD ≫
          HomologicalComplex.tensorHom uC uC) := by
        rw [← redComul_π, Category.assoc]

/-- Canonical reduced-coproduct expression.

For η : I → C in a cochain comonoid, define b = Δ_C − L_η − R_η + U_η, where L_η = λ_C⁻¹ ≫ (η
⊗ id), R_η = ρ_C⁻¹ ≫ (id ⊗ η), and U_η = ε_C ≫ λ_I⁻¹ ≫ (η ⊗ η). The signs retain the two
subtracted single-coaugmentation terms and added double term. -/
noncomputable def canonRedComul
    (η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C) :
    C ⟶ HomologicalComplex.tensorObj C C :=
  ComonObj.comul (X := C) -
    ((HomologicalComplex.leftUnitor C).inv ≫
      HomologicalComplex.tensorHom η (𝟙 C)) -
    ((HomologicalComplex.rightUnitor C).inv ≫
      HomologicalComplex.tensorHom (𝟙 C) η) +
    (ComonObj.counit (X := C) ≫
      (HomologicalComplex.leftUnitor (𝟙_ (CochainComplex (ModuleCat R) ℤ))).inv ≫
      HomologicalComplex.tensorHom η η)

set_option linter.style.haveILetI false in
/-- Reduced-coproduct laws from the coaugmentation counit and coproduct equations.

If η ≫ ε_C = id_I and η ≫ Δ_C = λ_I⁻¹ ≫ (η ⊗ η), then canonRedComul η satisfies IsRedComul η.
These two hypotheses make η a comonoid morphism from the canonical tensor-unit comonoid and
imply all three reduced vanishing equations. -/
theorem canonIsRedComul
    (η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C)
    (hcounit : η ≫ (ComonObj.counit (X := C)) = 𝟙 (𝟙_ (CochainComplex (ModuleCat R) ℤ)))
    (hcomul : η ≫ ComonObj.comul (X := C) =
      (HomologicalComplex.leftUnitor _).inv ≫
        HomologicalComplex.tensorHom η η) :
    IsRedComul η (canonRedComul η) := by
  letI := ComonObj.instTensorUnit (CochainComplex (ModuleCat R) ℤ)
  have hHom : IsComonHom η := { hom_counit := hcounit, hom_comul := hcomul }
  have hUnitors : (HomologicalComplex.leftUnitor
        (𝟙_ (CochainComplex (ModuleCat R) ℤ))).inv =
      (HomologicalComplex.rightUnitor
        (𝟙_ (CochainComplex (ModuleCat R) ℤ))).inv := by
    have hLU : HomologicalComplex.leftUnitor
          (𝟙_ (CochainComplex (ModuleCat R) ℤ)) =
        MonoidalCategory.leftUnitor _ := rfl
    have hRU : HomologicalComplex.rightUnitor
          (𝟙_ (CochainComplex (ModuleCat R) ℤ)) =
        MonoidalCategory.rightUnitor _ := rfl
    rw [hLU, hRU]
    have hIso : MonoidalCategory.leftUnitor
          (𝟙_ (CochainComplex (ModuleCat R) ℤ)) =
        MonoidalCategory.rightUnitor
          (𝟙_ (CochainComplex (ModuleCat R) ℤ)) :=
      Iso.ext (MonoidalCategory.unitors_equal
        (C := CochainComplex (ModuleCat R) ℤ))
    rw [hIso]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hHom
  · have hdecomp : ComonObj.comul (X := C) =
        canonRedComul η +
          ((HomologicalComplex.leftUnitor C).inv ≫
            HomologicalComplex.tensorHom η (𝟙 C)) +
          ((HomologicalComplex.rightUnitor C).inv ≫
            HomologicalComplex.tensorHom (𝟙 C) η) -
          (ComonObj.counit (X := C) ≫
            (HomologicalComplex.leftUnitor (𝟙_ (CochainComplex (ModuleCat R) ℤ))).inv ≫
            HomologicalComplex.tensorHom η η) := by
      unfold canonRedComul
      abel
    exact hdecomp
  · have hηL : η ≫
          ((HomologicalComplex.leftUnitor _).inv ≫
            HomologicalComplex.tensorHom η
              (𝟙 C)) =
        (HomologicalComplex.leftUnitor _).inv ≫
          HomologicalComplex.tensorHom η
            η := by
      rw [← Category.assoc]
      have hnat : η ≫
            (HomologicalComplex.leftUnitor _).inv =
          (HomologicalComplex.leftUnitor _).inv ≫
            HomologicalComplex.tensorHom
              (𝟙 (𝟙_ (CochainComplex (ModuleCat R) ℤ)))
              η :=
        MonoidalCategory.leftUnitor_inv_naturality _
      rw [hnat, Category.assoc, HomologicalComplex.tensorHom_comp_tensorHom,
        Category.id_comp, Category.comp_id]
    have hηR : η ≫
          ((HomologicalComplex.rightUnitor C).inv ≫
            HomologicalComplex.tensorHom (𝟙 C)
              η) =
        (HomologicalComplex.rightUnitor
          (𝟙_ (CochainComplex (ModuleCat R) ℤ))).inv ≫
          HomologicalComplex.tensorHom η
            η := by
      rw [← Category.assoc]
      have hnat : η ≫
            (HomologicalComplex.rightUnitor C).inv =
          (HomologicalComplex.rightUnitor
            (𝟙_ (CochainComplex (ModuleCat R) ℤ))).inv ≫
            HomologicalComplex.tensorHom η
              (𝟙 (𝟙_ (CochainComplex (ModuleCat R) ℤ))) :=
        MonoidalCategory.rightUnitor_inv_naturality η
      rw [hnat, Category.assoc, HomologicalComplex.tensorHom_comp_tensorHom,
        Category.comp_id, Category.id_comp]
    have hηU : η ≫
          (ComonObj.counit (X := C) ≫
          (HomologicalComplex.leftUnitor
            (𝟙_ (CochainComplex (ModuleCat R) ℤ))).inv ≫
          HomologicalComplex.tensorHom η
            η) =
        (HomologicalComplex.leftUnitor
          (𝟙_ (CochainComplex (ModuleCat R) ℤ))).inv ≫
          HomologicalComplex.tensorHom η
            η := by
      rw [← Category.assoc, ← Category.assoc, hcounit, Category.id_comp]
    have hEq : (HomologicalComplex.leftUnitor
            (𝟙_ (CochainComplex (ModuleCat R) ℤ))).inv ≫
            HomologicalComplex.tensorHom η
              η =
          (HomologicalComplex.rightUnitor
            (𝟙_ (CochainComplex (ModuleCat R) ℤ))).inv ≫
            HomologicalComplex.tensorHom η
              η := by
      rw [hUnitors]
    change η ≫ canonRedComul η = 0
    unfold canonRedComul
    rw [Preadditive.comp_add, Preadditive.comp_sub, Preadditive.comp_sub,
      hcomul, hηL, hηR, hηU, ← hEq]
    abel
  · have hΔε : ComonObj.comul (X := C) ≫
          HomologicalComplex.tensorHom (ComonObj.counit (X := C))
            (𝟙 C) =
        (HomologicalComplex.leftUnitor _).inv :=
      ComonObj.counit_comul _
    have hLε : ((HomologicalComplex.leftUnitor _).inv ≫
            HomologicalComplex.tensorHom η
              (𝟙 C)) ≫
            HomologicalComplex.tensorHom (ComonObj.counit (X := C))
              (𝟙 C) =
        (HomologicalComplex.leftUnitor _).inv := by
      rw [Category.assoc, HomologicalComplex.tensorHom_comp_tensorHom,
        hcounit, Category.id_comp, HomologicalComplex.tensorHom_id_id]
      rfl
    have hRε : ((HomologicalComplex.rightUnitor _).inv ≫
            HomologicalComplex.tensorHom (𝟙 C)
              η) ≫
            HomologicalComplex.tensorHom (ComonObj.counit (X := C))
              (𝟙 C) =
        (HomologicalComplex.rightUnitor _).inv ≫
          HomologicalComplex.tensorHom (ComonObj.counit (X := C))
            η := by
      rw [Category.assoc, HomologicalComplex.tensorHom_comp_tensorHom,
        Category.id_comp, Category.comp_id]
    have hUε : (ComonObj.counit (X := C) ≫
            (HomologicalComplex.leftUnitor _).inv ≫
            HomologicalComplex.tensorHom η
              η) ≫
            HomologicalComplex.tensorHom (ComonObj.counit (X := C))
              (𝟙 C) =
        (ComonObj.counit (X := C)) ≫
          (HomologicalComplex.leftUnitor _).inv ≫
          HomologicalComplex.tensorHom
            (𝟙 (𝟙_ (CochainComplex (ModuleCat R) ℤ)))
            η := by
      rw [Category.assoc, Category.assoc,
        HomologicalComplex.tensorHom_comp_tensorHom, Category.comp_id, hcounit]
    have hRU : (HomologicalComplex.rightUnitor _).inv ≫
            HomologicalComplex.tensorHom (ComonObj.counit (X := C))
              η =
          (ComonObj.counit (X := C)) ≫
            (HomologicalComplex.leftUnitor _).inv ≫
            HomologicalComplex.tensorHom
              (𝟙 (𝟙_ (CochainComplex (ModuleCat R) ℤ)))
              η := by
      have hfactor : HomologicalComplex.tensorHom
              (ComonObj.counit (X := C))
              η =
            HomologicalComplex.tensorHom (ComonObj.counit (X := C))
              (𝟙 (𝟙_ (CochainComplex (ModuleCat R) ℤ))) ≫
              HomologicalComplex.tensorHom (𝟙 (𝟙_ (CochainComplex (ModuleCat R) ℤ)))
                η := by
        rw [HomologicalComplex.tensorHom_comp_tensorHom, Category.comp_id,
          Category.id_comp]
      have hnatR : (HomologicalComplex.rightUnitor _).inv ≫
              HomologicalComplex.tensorHom (ComonObj.counit (X := C))
                (𝟙 (𝟙_ (CochainComplex (ModuleCat R) ℤ))) =
            (ComonObj.counit (X := C)) ≫
              (HomologicalComplex.rightUnitor _).inv :=
        (MonoidalCategory.rightUnitor_inv_naturality _).symm
      rw [hfactor, ← Category.assoc, hnatR, Category.assoc, hUnitors]
    change canonRedComul η ≫
      HomologicalComplex.tensorHom (ComonObj.counit (X := C))
        (𝟙 C) = 0
    unfold canonRedComul
    rw [Preadditive.add_comp, Preadditive.sub_comp, Preadditive.sub_comp,
      hΔε, hLε, hRε, hUε, ← hRU]
    abel
  · have hΔε : ComonObj.comul (X := C) ≫
          HomologicalComplex.tensorHom (𝟙 C)
            (ComonObj.counit (X := C)) =
        (HomologicalComplex.rightUnitor
          C).inv :=
      ComonObj.comul_counit C
    have hRε : ((HomologicalComplex.rightUnitor _).inv ≫
            HomologicalComplex.tensorHom (𝟙 C)
              η) ≫
            HomologicalComplex.tensorHom (𝟙 C)
              (ComonObj.counit (X := C)) =
        (HomologicalComplex.rightUnitor _).inv := by
      rw [Category.assoc, HomologicalComplex.tensorHom_comp_tensorHom,
        Category.id_comp, hcounit, HomologicalComplex.tensorHom_id_id]
      rfl
    have hLε : ((HomologicalComplex.leftUnitor _).inv ≫
            HomologicalComplex.tensorHom η
              (𝟙 C)) ≫
            HomologicalComplex.tensorHom (𝟙 C)
              (ComonObj.counit (X := C)) =
        (HomologicalComplex.leftUnitor _).inv ≫
          HomologicalComplex.tensorHom η
            (ComonObj.counit (X := C)) := by
      rw [Category.assoc, HomologicalComplex.tensorHom_comp_tensorHom,
        Category.comp_id, Category.id_comp]
    have hUε : (ComonObj.counit (X := C) ≫
            (HomologicalComplex.leftUnitor _).inv ≫
            HomologicalComplex.tensorHom η
              η) ≫
            HomologicalComplex.tensorHom (𝟙 C)
              (ComonObj.counit (X := C)) =
        (ComonObj.counit (X := C)) ≫
          (HomologicalComplex.leftUnitor _).inv ≫
          HomologicalComplex.tensorHom η
            (𝟙 (𝟙_ (CochainComplex (ModuleCat R) ℤ))) := by
      rw [Category.assoc, Category.assoc,
        HomologicalComplex.tensorHom_comp_tensorHom, Category.comp_id, hcounit]
    have hLU : (HomologicalComplex.leftUnitor _).inv ≫
            HomologicalComplex.tensorHom η
              (ComonObj.counit (X := C)) =
          (ComonObj.counit (X := C)) ≫
            (HomologicalComplex.leftUnitor _).inv ≫
            HomologicalComplex.tensorHom η
              (𝟙 (𝟙_ (CochainComplex (ModuleCat R) ℤ))) := by
      have hfactor : HomologicalComplex.tensorHom η
              (ComonObj.counit (X := C)) =
            HomologicalComplex.tensorHom
              (𝟙 (𝟙_ (CochainComplex (ModuleCat R) ℤ)))
              (ComonObj.counit (X := C)) ≫
              HomologicalComplex.tensorHom η
                (𝟙 (𝟙_ (CochainComplex (ModuleCat R) ℤ))) := by
        rw [HomologicalComplex.tensorHom_comp_tensorHom, Category.id_comp,
          Category.comp_id]
      have hnatL : (HomologicalComplex.leftUnitor _).inv ≫
              HomologicalComplex.tensorHom
                (𝟙 (𝟙_ (CochainComplex (ModuleCat R) ℤ)))
                (ComonObj.counit (X := C)) =
            (ComonObj.counit (X := C)) ≫
              (HomologicalComplex.leftUnitor _).inv :=
        (MonoidalCategory.leftUnitor_inv_naturality _).symm
      rw [hfactor, ← Category.assoc, hnatL, Category.assoc]
    change canonRedComul η ≫
      HomologicalComplex.tensorHom (𝟙 C)
        (ComonObj.counit (X := C)) = 0
    unfold canonRedComul
    rw [Preadditive.add_comp, Preadditive.sub_comp, Preadditive.sub_comp,
      hΔε, hLε, hRε, hUε, ← hLU]
    abel

end CochainComplex
