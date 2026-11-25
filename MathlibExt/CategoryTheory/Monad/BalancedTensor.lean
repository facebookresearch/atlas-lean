/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import MathlibExt.CategoryTheory.Monad.BarAugmentation

/-!
# Balanced tensor products of monadic modules

For a monad `T`, a right module `R`, and a left module `L`, the balanced tensor product
`R ⊗_T L` is the coequalizer of the two degree-one Bar faces `balanceFst` and `balanceSnd`.
Its projection is a balanced pairing, and the pairing gives an augmentation of the Bar.
The coequalizer universal property defines maps of balanced tensor products from compatible
module morphisms and proves their identity and composition laws.

The degree-`n` Bar term is `R(T^n(L(-)))`, expressed as
`L.functor ⋙ monadPow T n ⋙ R.functor`.

## References

* J. P. May, *The Geometry of Iterated Loop Spaces*, Lecture Notes in Mathematics 271,
  Springer, 1972, Chapter 9, Construction 9.6 and Remark 9.12,
  <https://doi.org/10.1007/BFb0067491>.
-/

@[expose] public section

namespace CategoryTheory
namespace Monad

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {A : Type u₃} [Category.{v₃} A]
variable {T : Monad C} {R : RightModule T D} {L : LeftModule A T}

/-- First degree-one bar face (right action), the left leg of balancing. -/
noncomputable abbrev balanceFst (T : Monad C) (R : RightModule T D) (L : LeftModule A T) :
    barObj T R L 1 ⟶ barObj T R L 0 :=
  barFace (T := T) (R := R) (L := L) 0 (0 : Fin 2)

/-- Second degree-one bar face (left action), the right leg of balancing. -/
noncomputable abbrev balanceSnd (T : Monad C) (R : RightModule T D) (L : LeftModule A T) :
    barObj T R L 1 ⟶ barObj T R L 0 :=
  barFace (T := T) (R := R) (L := L) 0 (1 : Fin 2)

/-- The first balancing face is the zeroth face of `barData` in degree one. -/
@[simp]
theorem balanceFst_δ : balanceFst T R L = (barData T R L).δ (0 : Fin 2) := rfl

/-- The second balancing face is the first face of `barData` in degree one. -/
@[simp]
theorem balanceSnd_δ : balanceSnd T R L = (barData T R L).δ (1 : Fin 2) := rfl

variable [Limits.HasCoequalizer (balanceFst T R L) (balanceSnd T R L)]

/-- Ordinary balanced tensor `R ⊗_T L`: coequalizer of the degree-one faces. -/
noncomputable abbrev balancedTensor (T : Monad C) (R : RightModule T D)
    (L : LeftModule A T)
    [Limits.HasCoequalizer (balanceFst T R L) (balanceSnd T R L)] : A ⥤ D :=
  Limits.coequalizer (f := balanceFst T R L) (g := balanceSnd T R L)

/-- Canonical projection from degree zero onto the balanced tensor. -/
noncomputable abbrev balancedTensorπ (T : Monad C) (R : RightModule T D)
    (L : LeftModule A T)
    [Limits.HasCoequalizer (balanceFst T R L) (balanceSnd T R L)] :
    barObj T R L 0 ⟶ balancedTensor T R L :=
  Limits.coequalizer.π (f := balanceFst T R L) (g := balanceSnd T R L)

/-- The projection coequalizes the two balancing faces. -/
theorem balancedTensor_condition :
    balanceFst T R L ≫ balancedTensorπ T R L =
      balanceSnd T R L ≫ balancedTensorπ T R L :=
  Limits.coequalizer.condition (f := balanceFst T R L) (g := balanceSnd T R L)

/-- Universal map out of the balanced tensor. -/
noncomputable def balancedTensorDesc {Q : A ⥤ D} (k : barObj T R L 0 ⟶ Q)
    (h : balanceFst T R L ≫ k = balanceSnd T R L ≫ k) :
    balancedTensor T R L ⟶ Q :=
  Limits.coequalizer.desc (f := balanceFst T R L) (g := balanceSnd T R L) k h

/-- The projection followed by the induced map recovers the input. -/
@[simp]
theorem balancedTensorDesc_π {Q : A ⥤ D} (k : barObj T R L 0 ⟶ Q)
    (h : balanceFst T R L ≫ k = balanceSnd T R L ≫ k) :
    balancedTensorπ T R L ≫ balancedTensorDesc k h = k :=
  Limits.coequalizer.π_desc k h

/-- Maps out of the tensor are fixed by precomposition with the projection. -/
@[ext]
theorem balancedTensor_hom_ext {Q : A ⥤ D} {u v : balancedTensor T R L ⟶ Q}
    (h : balancedTensorπ T R L ≫ u = balancedTensorπ T R L ≫ v) : u = v :=
  Limits.coequalizer.hom_ext h

/-- The projection equalizes the degree-one faces, hence is balanced. -/
theorem balancedTensorπ_balanced :
    IsBalancedPairing (T := T) (R := R) (L := L) (balancedTensorπ T R L) := by
  rw [isBalancedPairing_iff_action_eq]
  intro a
  have h := congrArg (fun (t : barObj T R L 1 ⟶ _) => t.app a)
    (balancedTensor_condition (T := T) (R := R) (L := L))
  simp only [NatTrans.comp_app] at h
  have e0 : (balanceFst T R L).app a =
      R.action.app (L.functor.obj a) := rfl
  have e1 : (balanceSnd T R L).app a =
      R.functor.map (L.action.app a) := rfl
  rw [e0, e1] at h
  exact h

/-- Pointwise action equation satisfied by the tensor projection. -/
theorem balancedTensorπ_action_eq (a : A) :
    R.action.app (L.functor.obj a) ≫ (balancedTensorπ T R L).app a =
      R.functor.map (L.action.app a) ≫ (balancedTensorπ T R L).app a :=
  isBalancedPairing_iff_action_eq.mp balancedTensorπ_balanced a

/-- Bundled balanced pairing targeted at the ordinary tensor. -/
noncomputable def balancedTensorPairing (T : Monad C) (R : RightModule T D)
    (L : LeftModule A T)
    [Limits.HasCoequalizer (balanceFst T R L) (balanceSnd T R L)] :
    BalancedPairing T R L where
  target := balancedTensor T R L
  pairing := balancedTensorπ T R L
  balanced := balancedTensorπ_balanced

/-- Augmented simplicial bar over the tensor, via `toSimplicialAugmented`. -/
noncomputable def balancedTensorAugmented (T : Monad C) (R : RightModule T D)
    (L : LeftModule A T)
    [Limits.HasCoequalizer (balanceFst T R L) (balanceSnd T R L)] :
    SimplicialObject.Augmented (A ⥤ D) :=
  (balancedTensorPairing T R L).toSimplicialAugmented

/-- The augmentation lies over the two-sided bar. -/
@[simp]
theorem balancedTensorAugmented_left (T : Monad C) (R : RightModule T D)
    (L : LeftModule A T)
    [Limits.HasCoequalizer (balanceFst T R L) (balanceSnd T R L)] :
    (balancedTensorAugmented T R L).left = twoSidedBar T R L := rfl

/-- The augmentation points at the balanced tensor. -/
@[simp]
theorem balancedTensorAugmented_right (T : Monad C) (R : RightModule T D)
    (L : LeftModule A T)
    [Limits.HasCoequalizer (balanceFst T R L) (balanceSnd T R L)] :
    (balancedTensorAugmented T R L).right = balancedTensor T R L := rfl

section Functoriality

variable {R' : RightModule T D} {L' : LeftModule A T}
variable [Limits.HasCoequalizer (balanceFst T R' L') (balanceSnd T R' L')]
variable {R'' : RightModule T D} {L'' : LeftModule A T}
variable [Limits.HasCoequalizer (balanceFst T R'' L'') (balanceSnd T R'' L'')]

omit [Limits.HasCoequalizer (balanceFst T R L) (balanceSnd T R L)] [Limits.HasCoequalizer
  (balanceFst T R' L') (balanceSnd T R' L')] in
/-- `barMap` commutes with the first balancing face. -/
theorem barMap_balanceFst (fR : R ⟶ R') (fL : L ⟶ L') :
    barMap fR fL 1 ≫ balanceFst T R' L' = balanceFst T R L ≫ barMap fR fL 0 :=
  barMap_barFace fR fL 0 (0 : Fin 2)

omit [Limits.HasCoequalizer (balanceFst T R L) (balanceSnd T R L)] [Limits.HasCoequalizer
  (balanceFst T R' L') (balanceSnd T R' L')] in
/-- `barMap` commutes with the second balancing face. -/
theorem barMap_balanceSnd (fR : R ⟶ R') (fL : L ⟶ L') :
    barMap fR fL 1 ≫ balanceSnd T R' L' = balanceSnd T R L ≫ barMap fR fL 0 :=
  barMap_barFace fR fL 0 (1 : Fin 2)

omit [Limits.HasCoequalizer (balanceFst T R L) (balanceSnd T R L)] in
/-- Degree-zero `barMap` followed by the target projection coequalizes. -/
theorem balancedTensorMap_condition (fR : R ⟶ R') (fL : L ⟶ L') :
    balanceFst T R L ≫ (barMap fR fL 0 ≫ balancedTensorπ T R' L') =
      balanceSnd T R L ≫ (barMap fR fL 0 ≫ balancedTensorπ T R' L') := by
  have hc := balancedTensor_condition (T := T) (R := R') (L := L')
  have e0 := barMap_balanceFst fR fL
  have e1 := barMap_balanceSnd fR fL
  calc balanceFst T R L ≫ (barMap fR fL 0 ≫ balancedTensorπ T R' L')
      = (balanceFst T R L ≫ barMap fR fL 0) ≫ balancedTensorπ T R' L' := by
        rw [← Category.assoc]
    _ = (barMap fR fL 1 ≫ balanceFst T R' L') ≫ balancedTensorπ T R' L' := by
        rw [← e0]
    _ = barMap fR fL 1 ≫ (balanceFst T R' L' ≫ balancedTensorπ T R' L') := by
        rw [Category.assoc]
    _ = barMap fR fL 1 ≫ (balanceSnd T R' L' ≫ balancedTensorπ T R' L') := by
        rw [hc]
    _ = (barMap fR fL 1 ≫ balanceSnd T R' L') ≫ balancedTensorπ T R' L' := by
        rw [← Category.assoc]
    _ = (balanceSnd T R L ≫ barMap fR fL 0) ≫ balancedTensorπ T R' L' := by
        rw [e1]
    _ = balanceSnd T R L ≫ (barMap fR fL 0 ≫ balancedTensorπ T R' L') := by
        rw [Category.assoc]

/-- Induced map on tensors from compatible module morphisms. -/
noncomputable def balancedTensorMap (fR : R ⟶ R') (fL : L ⟶ L') :
    balancedTensor T R L ⟶ balancedTensor T R' L' :=
  Limits.coequalizer.desc (f := balanceFst T R L) (g := balanceSnd T R L)
    (barMap fR fL 0 ≫ balancedTensorπ T R' L')
    (balancedTensorMap_condition fR fL)

/-- The induced map is computed on the projection by degree-zero `barMap`. -/
@[simp]
theorem balancedTensorMap_π (fR : R ⟶ R') (fL : L ⟶ L') :
    balancedTensorπ T R L ≫ balancedTensorMap fR fL =
      barMap fR fL 0 ≫ balancedTensorπ T R' L' :=
  Limits.coequalizer.π_desc (barMap fR fL 0 ≫ balancedTensorπ T R' L')
    (balancedTensorMap_condition fR fL)

/-- Identity on tensors; degree-zero shadow of `twoSidedBarHom_id`. -/
@[simp]
theorem balancedTensorMap_id :
    balancedTensorMap (𝟙 R) (𝟙 L) = 𝟙 (balancedTensor T R L) := by
  apply balancedTensor_hom_ext
  rw [balancedTensorMap_π, barMap_id, Category.id_comp, Category.comp_id]

/-- Composition on tensors; degree-zero shadow of `twoSidedBarHom_comp`. -/
theorem balancedTensorMap_comp (fR : R ⟶ R') (gR : R' ⟶ R'')
    (fL : L ⟶ L') (gL : L' ⟶ L'') :
    balancedTensorMap fR fL ≫ balancedTensorMap gR gL =
      balancedTensorMap (fR ≫ gR) (fL ≫ gL) := by
  apply balancedTensor_hom_ext
  rw [← Category.assoc, balancedTensorMap_π, Category.assoc, balancedTensorMap_π,
    balancedTensorMap_π, ← Category.assoc, barMap_comp]

/-- Induced map of augmented bars, over `twoSidedBarHom` and the tensor map. -/
noncomputable def balancedTensorAugmentedMap (fR : R ⟶ R') (fL : L ⟶ L') :
    balancedTensorAugmented T R L ⟶ balancedTensorAugmented T R' L' :=
  BalancedPairing.toSimplicialAugmentedMap (balancedTensorPairing T R L)
    (balancedTensorPairing T R' L') fR fL (balancedTensorMap fR fL)
    (balancedTensorMap_π fR fL).symm

/-- The augmented map lies over `twoSidedBarHom`. -/
@[simp]
theorem balancedTensorAugmentedMap_left (fR : R ⟶ R') (fL : L ⟶ L') :
    (balancedTensorAugmentedMap fR fL).left = twoSidedBarHom fR fL := rfl

/-- The augmented map points along the induced tensor map. -/
@[simp]
theorem balancedTensorAugmentedMap_right (fR : R ⟶ R') (fL : L ⟶ L') :
    (balancedTensorAugmentedMap fR fL).right = balancedTensorMap fR fL := rfl

/-- Identity augmented map; balanced shadow of `twoSidedBarHom_id`. -/
theorem balancedTensorAugmentedMap_id :
    balancedTensorAugmentedMap (𝟙 R) (𝟙 L) = 𝟙 (balancedTensorAugmented T R L) := by
  refine SimplicialObject.Augmented.hom_ext _ _ ?_ ?_
  · have e1 : (balancedTensorAugmentedMap (𝟙 R) (𝟙 L)).left =
        twoSidedBarHom (𝟙 R) (𝟙 L) := by
      simp only [balancedTensorAugmentedMap_left]
      rfl
    have e2 : twoSidedBarHom (𝟙 R) (𝟙 L) =
        𝟙 (twoSidedBar T R L) :=
      twoSidedBarHom_id _ _
    have e3 : (𝟙 (twoSidedBar T R L)) =
        𝟙 (balancedTensorAugmented T R L).left :=
      rfl
    exact e1.trans (e2.trans e3)
  · have e1r : (balancedTensorAugmentedMap (𝟙 R) (𝟙 L)).right =
        balancedTensorMap (𝟙 R) (𝟙 L) := by
      simp only [balancedTensorAugmentedMap_right]
      rfl
    have e2r : balancedTensorMap (𝟙 R) (𝟙 L) = 𝟙 (balancedTensor T R L) :=
      balancedTensorMap_id
    have e3r : (𝟙 (balancedTensor T R L)) = 𝟙 (balancedTensorAugmented T R L).right :=
      rfl
    exact e1r.trans (e2r.trans e3r)

/-- Composition of augmented maps; balanced shadow of `twoSidedBarHom_comp`. -/
theorem balancedTensorAugmentedMap_comp (fR : R ⟶ R') (gR : R' ⟶ R'')
    (fL : L ⟶ L') (gL : L' ⟶ L'') :
    balancedTensorAugmentedMap fR fL ≫ balancedTensorAugmentedMap gR gL =
      balancedTensorAugmentedMap (fR ≫ gR) (fL ≫ gL) := by
  refine SimplicialObject.Augmented.hom_ext _ _ ?_ ?_
  · have f1 : (balancedTensorAugmentedMap fR fL ≫ balancedTensorAugmentedMap gR gL).left =
        twoSidedBarHom fR fL ≫ twoSidedBarHom gR gL := by
      rw [Comma.comp_left]
      simp only [balancedTensorAugmentedMap_left]
      rfl
    have f2 : twoSidedBarHom fR fL ≫ twoSidedBarHom gR gL =
        twoSidedBarHom (fR ≫ gR) (fL ≫ gL) :=
      twoSidedBarHom_comp fR gR fL gL
    have f3 : twoSidedBarHom (fR ≫ gR) (fL ≫ gL) =
        (balancedTensorAugmentedMap (fR ≫ gR) (fL ≫ gL)).left := by
      simp only [balancedTensorAugmentedMap_left]
    exact f1.trans (f2.trans f3)
  · have g1 : (balancedTensorAugmentedMap fR fL ≫ balancedTensorAugmentedMap gR gL).right =
        balancedTensorMap fR fL ≫ balancedTensorMap gR gL := by
      rw [Comma.comp_right]
      simp only [balancedTensorAugmentedMap_right]
      rfl
    have g2 : balancedTensorMap fR fL ≫ balancedTensorMap gR gL =
        balancedTensorMap (fR ≫ gR) (fL ≫ gL) :=
      balancedTensorMap_comp fR gR fL gL
    have g3 : balancedTensorMap (fR ≫ gR) (fL ≫ gL) =
        (balancedTensorAugmentedMap (fR ≫ gR) (fL ≫ gL)).right := by
      simp only [balancedTensorAugmentedMap_right]
    exact g1.trans (g2.trans g3)

end Functoriality

end Monad
end CategoryTheory
