/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.ModuleCat.TensorProjectiveResolutionUniverse
public import MathlibExt.Algebra.Homology.TripleTensor

/-!
# Associativity of tensor-total projective resolutions

The signed tensor total associator compares the two ordered
parenthesizations. Its degree-zero map is the module tensor associator,
and it intertwines the tensor augmentations. Positive Tor vanishing
constructs the iterated projective resolutions.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped ModuleCat.UniverseTensor ZeroObject

universe u v

namespace ModuleCat.UniverseTensor

variable (R : Type u) [CommRing R]
local notation "c" => ComplexShape.down ℕ

private theorem tensorRightPreservesFiniteColimits (M : ModuleCat.{max u v} R) :
    PreservesFiniteColimits (tensorRight M) := by
  have : PreservesFiniteColimits (tensorLeft M) := nativeTensorLeft_preservesFiniteColimits R M
  exact preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)

local instance (M : ModuleCat.{max u v} R) : PreservesFiniteCoproducts (tensorLeft M) := by
  have : PreservesFiniteColimits (tensorLeft M) := nativeTensorLeft_preservesFiniteColimits R M
  infer_instance

local instance (M : ModuleCat.{max u v} R) : PreservesFiniteCoproducts (tensorRight M) := by
  have : PreservesFiniteColimits (tensorRight M) := tensorRightPreservesFiniteColimits R M
  infer_instance

local instance (K L U : ChainComplex (ModuleCat.{max u v} R) ℕ) :
    HomologicalComplex.HasGoodTensor₁₂ K L U := by
  intro n q
  change PreservesColimit _ (tensorRight (U.X q))
  infer_instance

local instance (K L U : ChainComplex (ModuleCat.{max u v} R) ℕ) :
    HomologicalComplex.HasGoodTensor₂₃ K L U := by
  intro p n
  change PreservesColimit _ (tensorLeft (K.X p))
  infer_instance

/-- The stock ordered total associator for actual module complexes. Tensor
right exactness supplies its coproduct hypotheses in both original universes. -/
def tensorTotalAssociator (P Q U : ChainComplex (ModuleCat.{max u v} R) ℕ) :
    HomologicalComplex.tensorObj (HomologicalComplex.tensorObj P Q) U ≅
      HomologicalComplex.tensorObj P (HomologicalComplex.tensorObj Q U) :=
  HomologicalComplex.associator P Q U

private theorem isIso_ιTensorObj_zero
    (K L : ChainComplex (ModuleCat.{max u v} R) ℕ) :
    IsIso (HomologicalComplex.ιTensorObj K L 0 0 0 rfl) := by
  let B := (((curriedTensor (ModuleCat.{max u v} R)).mapBifunctorHomologicalComplex c c).obj K).obj L
  let π := ComplexShape.π c c c
  let I := π ⁻¹' {0}
  let point : I := ⟨(0, 0), rfl⟩
  let : Unique I := {
    default := point
    uniq := fun i => by
      apply Subtype.ext
      change i.val = (0, 0)
      have hi : i.val.1 + i.val.2 = 0 := i.property
      exact Prod.ext (by omega) (by omega)
  }
  let A := B.toGradedObject.mapObjFun π 0
  change IsIso (Sigma.ι A (default : I))
  rw [← coproductUniqueIso_inv]
  infer_instance

variable {M N V : ModuleCat.{max u v} R}

/-- The literal left-parenthesized augmentation of three original chain complexes. -/
def tensorLeftTripleAugmentation
    (P Q U : ChainComplex (ModuleCat.{max u v} R) ℕ)
    (π : P ⟶ (ChainComplex.single₀ (ModuleCat.{max u v} R)).obj M)
    (ρ : Q ⟶ (ChainComplex.single₀ (ModuleCat.{max u v} R)).obj N)
    (τ : U ⟶ (ChainComplex.single₀ (ModuleCat.{max u v} R)).obj V) :
    HomologicalComplex.tensorObj (HomologicalComplex.tensorObj P Q) U ⟶
      (ChainComplex.single₀ (ModuleCat.{max u v} R)).obj ((M ⊗ N) ⊗ V) :=
  tensorAugmentation.{u,v} (K := HomologicalComplex.tensorObj P Q) (L := U)
    (M := M ⊗ N) (N := V) R
      (tensorAugmentation.{u,v} (K := P) (L := Q) (M := M) (N := N) R π ρ) τ

/-- The literal right-parenthesized augmentation of three original chain complexes. -/
def tensorRightTripleAugmentation
    (P Q U : ChainComplex (ModuleCat.{max u v} R) ℕ)
    (π : P ⟶ (ChainComplex.single₀ (ModuleCat.{max u v} R)).obj M)
    (ρ : Q ⟶ (ChainComplex.single₀ (ModuleCat.{max u v} R)).obj N)
    (τ : U ⟶ (ChainComplex.single₀ (ModuleCat.{max u v} R)).obj V) :
    HomologicalComplex.tensorObj P (HomologicalComplex.tensorObj Q U) ⟶
      (ChainComplex.single₀ (ModuleCat.{max u v} R)).obj (M ⊗ (N ⊗ V)) :=
  tensorAugmentation.{u,v} (K := P) (L := HomologicalComplex.tensorObj Q U)
    (M := M) (N := N ⊗ V) R π
      (tensorAugmentation.{u,v} (K := Q) (L := U) (M := N) (N := V) R ρ τ)

private theorem isIso_tensorTripleLeftιZero
    (P Q U : ChainComplex (ModuleCat.{max u v} R) ℕ) :
    IsIso (HomologicalComplex.ιTensorObj₃Left P Q U 0 0 0 0 rfl) := by
  rw [HomologicalComplex.ιTensorObj₃Left_eq P Q U 0 0 0 0 0 rfl rfl]
  let f := HomologicalComplex.ιTensorObj P Q 0 0 0 rfl
  let g := HomologicalComplex.ιTensorObj (HomologicalComplex.tensorObj P Q) U 0 0 0 rfl
  have : IsIso f := isIso_ιTensorObj_zero R P Q
  have : IsIso g := isIso_ιTensorObj_zero R (HomologicalComplex.tensorObj P Q) U
  have : IsIso ((tensorRight (U.X 0)).map f) := inferInstance
  change IsIso (((tensorRight (U.X 0)).map f) ≫ g)
  infer_instance

private theorem tensorTripleLeftAugmentation_zero
    (P Q U : ChainComplex (ModuleCat.{max u v} R) ℕ)
    (π : P ⟶ (ChainComplex.single₀ (ModuleCat.{max u v} R)).obj M)
    (ρ : Q ⟶ (ChainComplex.single₀ (ModuleCat.{max u v} R)).obj N)
    (τ : U ⟶ (ChainComplex.single₀ (ModuleCat.{max u v} R)).obj V) :
    HomologicalComplex.ιTensorObj₃Left P Q U 0 0 0 0 rfl ≫
      (tensorAugmentation.{u,v} (K := HomologicalComplex.tensorObj P Q) (L := U)
      (M := M ⊗ N) (N := V) R
      (tensorAugmentation.{u,v} (K := P) (L := Q) (M := M) (N := N) R π ρ) τ).f 0 = (π.f 0 ⊗ₘ ρ.f 0) ⊗ₘ τ.f 0 := by
  let A := HomologicalComplex.tensorObj P Q
  let a : P.X 0 ⟶ M := π.f 0
  let b : Q.X 0 ⟶ N := ρ.f 0
  let d : U.X 0 ⟶ V := τ.f 0
  let a' : A.X 0 ⟶ M ⊗ N := (tensorAugmentation.{u,v} (K := P) (L := Q) (M := M) (N := N) R π ρ).f 0
  let ιPQ : P.X 0 ⊗ Q.X 0 ⟶ A.X 0 := HomologicalComplex.ιTensorObj P Q 0 0 0 rfl
  have hA : ιPQ ≫ a' = a ⊗ₘ b := ι_tensorAugmentation_zero R π ρ
  let ιL : A.X 0 ⊗ U.X 0 ⟶ (HomologicalComplex.tensorObj A U).X 0 :=
    HomologicalComplex.ιTensorObj A U 0 0 0 rfl
  let δ : (HomologicalComplex.tensorObj A U).X 0 ⟶ (M ⊗ N) ⊗ V :=
    (tensorAugmentation.{u,v} (K := HomologicalComplex.tensorObj P Q) (L := U)
      (M := M ⊗ N) (N := V) R (tensorAugmentation.{u,v} (K := P) (L := Q) (M := M) (N := N) R π ρ) τ).f 0
  have hT : ιL ≫ δ = a' ⊗ₘ d :=
    ι_tensorAugmentation_zero R (tensorAugmentation.{u,v} (K := P) (L := Q) (M := M) (N := N) R π ρ) τ
  have h : (ιPQ ▷ U.X 0) ≫ (a' ⊗ₘ d) = (a ⊗ₘ b) ⊗ₘ d := by
    rw [← tensorHom_id, tensorHom_comp_tensorHom, hA, Category.id_comp]
  rw [HomologicalComplex.ιTensorObj₃Left_eq P Q U 0 0 0 0 0 rfl rfl]
  change ((ιPQ ▷ U.X 0) ≫ ιL) ≫ δ = (a ⊗ₘ b) ⊗ₘ d
  exact (Category.assoc _ _ _).trans ((congrArg (fun f => (ιPQ ▷ U.X 0) ≫ f) hT).trans h)

private theorem tensorTripleRightAugmentation_zero
    (P Q U : ChainComplex (ModuleCat.{max u v} R) ℕ)
    (π : P ⟶ (ChainComplex.single₀ (ModuleCat.{max u v} R)).obj M)
    (ρ : Q ⟶ (ChainComplex.single₀ (ModuleCat.{max u v} R)).obj N)
    (τ : U ⟶ (ChainComplex.single₀ (ModuleCat.{max u v} R)).obj V) :
    HomologicalComplex.ιTensorObj₃Right P Q U 0 0 0 0 rfl ≫
      (tensorAugmentation.{u,v} (K := P) (L := HomologicalComplex.tensorObj Q U)
      (M := M) (N := N ⊗ V) R π
        (tensorAugmentation.{u,v} (K := Q) (L := U) (M := N) (N := V) R ρ τ)).f 0 = π.f 0 ⊗ₘ (ρ.f 0 ⊗ₘ τ.f 0) := by
  let B := HomologicalComplex.tensorObj Q U
  let a : P.X 0 ⟶ M := π.f 0
  let b : Q.X 0 ⟶ N := ρ.f 0
  let d : U.X 0 ⟶ V := τ.f 0
  let b' : B.X 0 ⟶ N ⊗ V := (tensorAugmentation.{u,v} (K := Q) (L := U) (M := N) (N := V) R ρ τ).f 0
  let ιQU : Q.X 0 ⊗ U.X 0 ⟶ B.X 0 := HomologicalComplex.ιTensorObj Q U 0 0 0 rfl
  have hB : ιQU ≫ b' = b ⊗ₘ d := ι_tensorAugmentation_zero R ρ τ
  let ιR : P.X 0 ⊗ B.X 0 ⟶ (HomologicalComplex.tensorObj P B).X 0 :=
    HomologicalComplex.ιTensorObj P B 0 0 0 rfl
  let δ : (HomologicalComplex.tensorObj P B).X 0 ⟶ M ⊗ (N ⊗ V) :=
    (tensorAugmentation.{u,v} (K := P) (L := HomologicalComplex.tensorObj Q U)
      (M := M) (N := N ⊗ V) R π
        (tensorAugmentation.{u,v} (K := Q) (L := U) (M := N) (N := V) R ρ τ)).f 0
  have hT : ιR ≫ δ = a ⊗ₘ b' :=
    ι_tensorAugmentation_zero R π (tensorAugmentation.{u,v} (K := Q) (L := U) (M := N) (N := V) R ρ τ)
  have h : (P.X 0 ◁ ιQU) ≫ (a ⊗ₘ b') = a ⊗ₘ (b ⊗ₘ d) := by
    rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp, hB]
  rw [HomologicalComplex.ιTensorObj₃Right_eq P Q U 0 0 0 0 0 rfl rfl]
  change ((P.X 0 ◁ ιQU) ≫ ιR) ≫ δ = a ⊗ₘ (b ⊗ₘ d)
  exact (Category.assoc _ _ _).trans ((congrArg (fun f => (P.X 0 ◁ ιQU) ≫ f) hT).trans h)

private theorem tensorAssociator_comp_of_basis
    {X Y Z S T : ModuleCat.{max u v} R}
    (a : X ⟶ M) (b : Y ⟶ N) (d : Z ⟶ V)
    (j : (X ⊗ Y) ⊗ Z ⟶ S) [Epi j] (k : X ⊗ (Y ⊗ Z) ⟶ T)
    (E : S ⟶ T) (δ : S ⟶ (M ⊗ N) ⊗ V) (δ' : T ⟶ M ⊗ (N ⊗ V))
    (hE : j ≫ E = (α_ X Y Z).hom ≫ k)
    (hL : j ≫ δ = (a ⊗ₘ b) ⊗ₘ d)
    (hR : k ≫ δ' = a ⊗ₘ (b ⊗ₘ d)) :
    E ≫ δ' = δ ≫ (α_ M N V).hom := by
  apply (cancel_epi j).1
  calc
    _ = (j ≫ E) ≫ δ' := (Category.assoc _ _ _).symm
    _ = ((α_ X Y Z).hom ≫ k) ≫ δ' := congrArg (fun f => f ≫ δ') hE
    _ = (α_ X Y Z).hom ≫ (a ⊗ₘ (b ⊗ₘ d)) := by rw [Category.assoc, hR]
    _ = ((a ⊗ₘ b) ⊗ₘ d) ≫ (α_ M N V).hom := (associator_naturality a b d).symm
    _ = (j ≫ δ) ≫ (α_ M N V).hom := congrArg (fun f => f ≫ (α_ M N V).hom) hL.symm
    _ = _ := Category.assoc _ _ _

private theorem tensorAugmentation_associator_zero
    (P Q U : ChainComplex (ModuleCat.{max u v} R) ℕ)
    (π : P ⟶ (ChainComplex.single₀ (ModuleCat.{max u v} R)).obj M)
    (ρ : Q ⟶ (ChainComplex.single₀ (ModuleCat.{max u v} R)).obj N)
    (τ : U ⟶ (ChainComplex.single₀ (ModuleCat.{max u v} R)).obj V) :
    (tensorTotalAssociator.{u,v} R P Q U).hom.f 0 ≫
      (tensorRightTripleAugmentation.{u,v} R P Q U π ρ τ).f 0 =
        (tensorLeftTripleAugmentation.{u,v} R P Q U π ρ τ).f 0 ≫
          ((ChainComplex.single₀ (ModuleCat.{max u v} R)).map (α_ M N V).hom).f 0 := by
  let j := HomologicalComplex.ιTensorObj₃Left P Q U 0 0 0 0 rfl
  let k := HomologicalComplex.ιTensorObj₃Right P Q U 0 0 0 0 rfl
  have : IsIso j := isIso_tensorTripleLeftιZero.{u,v} R P Q U
  have : Epi j := inferInstance
  let a : P.X 0 ⟶ M := π.f 0
  let b : Q.X 0 ⟶ N := ρ.f 0
  let d : U.X 0 ⟶ V := τ.f 0
  let δ := (tensorLeftTripleAugmentation.{u,v} R P Q U π ρ τ).f 0
  let δ' := (tensorRightTripleAugmentation.{u,v} R P Q U π ρ τ).f 0
  let E := tensorTotalAssociator.{u,v} R P Q U
  have hE : j ≫ E.hom.f 0 = (α_ (P.X 0) (Q.X 0) (U.X 0)).hom ≫ k :=
    HomologicalComplex.ιTensorObj₃Left_associator_hom P Q U 0 0 0 0 rfl
  have hL : j ≫ δ = (a ⊗ₘ b) ⊗ₘ d := tensorTripleLeftAugmentation_zero.{u,v} R P Q U π ρ τ
  have hR : k ≫ δ' = a ⊗ₘ (b ⊗ₘ d) := tensorTripleRightAugmentation_zero.{u,v} R P Q U π ρ τ
  change E.hom.f 0 ≫ δ' = δ ≫ (α_ M N V).hom
  exact tensorAssociator_comp_of_basis.{u,v} R a b d j k (E.hom.f 0) δ δ' hE hL hR

/-- The stock ordered tensor-total associator carries the literal iterated
chain augmentations by the original coefficient tensor associator. -/
theorem tensorAugmentation_associator
    (P Q U : ChainComplex (ModuleCat.{max u v} R) ℕ)
    (π : P ⟶ (ChainComplex.single₀ (ModuleCat.{max u v} R)).obj M)
    (ρ : Q ⟶ (ChainComplex.single₀ (ModuleCat.{max u v} R)).obj N)
    (τ : U ⟶ (ChainComplex.single₀ (ModuleCat.{max u v} R)).obj V) :
    (tensorTotalAssociator.{u,v} R P Q U).hom ≫
      tensorRightTripleAugmentation.{u,v} R P Q U π ρ τ =
        tensorLeftTripleAugmentation.{u,v} R P Q U π ρ τ ≫
          (ChainComplex.single₀ (ModuleCat.{max u v} R)).map (α_ M N V).hom := by
  apply (ChainComplex.toSingle₀Equiv _ _).injective
  apply Subtype.ext
  exact tensorAugmentation_associator_zero.{u,v} R P Q U π ρ τ


/-- The original ordered total associator is a genuine resolution map between
both actual iterated tensor resolutions. All four vanishing hypotheses are
literal positive native Tor conditions for the original coefficients. -/
def tensorProjectiveResolutionAssociatorHom
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N) (U : ProjectiveResolution V)
    (hPQ : ∀ n : ℕ, IsZero (((Tor (ModuleCat.{max u v} R) (n + 1)).obj M).obj N))
    (hQU : ∀ n : ℕ, IsZero (((Tor (ModuleCat.{max u v} R) (n + 1)).obj N).obj V))
    (hPQU : ∀ n : ℕ, IsZero (((Tor (ModuleCat.{max u v} R) (n + 1)).obj (M ⊗ N)).obj V))
    (hPQU' : ∀ n : ℕ, IsZero (((Tor (ModuleCat.{max u v} R) (n + 1)).obj M).obj (N ⊗ V))) :
    ProjectiveResolution.Hom
      (tensorProjectiveResolution.{u,v} R (tensorProjectiveResolution.{u,v} R P Q hPQ) U hPQU)
      (tensorProjectiveResolution.{u,v} R P (tensorProjectiveResolution.{u,v} R Q U hQU) hPQU')
      (α_ M N V).hom where
  hom := (tensorTotalAssociator.{u,v} R P.complex Q.complex U.complex).hom
  hom_f_zero_comp_π_f_zero := by
    have h := congrArg (fun f => f.f 0)
      (tensorAugmentation_associator.{u,v} R P.complex Q.complex U.complex P.π Q.π U.π)
    exact h

/-- The constructed resolution comparison is the stock ordered tensor total
isomorphism on the original complexes. -/
theorem tensorProjectiveResolutionAssociatorHom_isIso
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N) (U : ProjectiveResolution V)
    (hPQ : ∀ n : ℕ, IsZero (((Tor (ModuleCat.{max u v} R) (n + 1)).obj M).obj N))
    (hQU : ∀ n : ℕ, IsZero (((Tor (ModuleCat.{max u v} R) (n + 1)).obj N).obj V))
    (hPQU : ∀ n : ℕ, IsZero (((Tor (ModuleCat.{max u v} R) (n + 1)).obj (M ⊗ N)).obj V))
    (hPQU' : ∀ n : ℕ, IsZero (((Tor (ModuleCat.{max u v} R) (n + 1)).obj M).obj (N ⊗ V))) :
    IsIso (tensorProjectiveResolutionAssociatorHom.{u,v} R P Q U hPQ hQU hPQU hPQU').hom := by
  change IsIso (tensorTotalAssociator.{u,v} R P.complex Q.complex U.complex).hom
  infer_instance

end ModuleCat.UniverseTensor
