/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.BasedPathLoop
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationSequenceContractible

/-!
# Path, loop, and connecting-map consumers

Persistent clients for endpoint computations, based-loop fibrations, the
penultimate multiplication index, and both branches of connecting-map
bijectivity.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory HomotopicalAlgebra MonoidalCategory Simplicial
open scoped Simplicial SSet.modelCategoryQuillen

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.PathLoopFibrationSequenceTests

universe u v

section PathSpace

variable (X : SSet.{u})

example : SSet.{u} := SSet.pathSpace X

example : X ⟶ SSet.pathSpace X := SSet.constPath X

example :
    MonoidalClosed.uncurry (SSet.constPath X) =
      CartesianMonoidalCategory.snd (Δ[1] : SSet.{u}) X :=
  SSet.uncurry_constPath X

example : SSet.pathSpace X ⟶ X := SSet.eval₀

example : SSet.pathSpace X ⟶ X := SSet.eval₁

variable {A B : SSet.{u}} (h : A ⟶ SSet.pathSpace B)

example :
    h ≫ (SSet.eval₀ : SSet.pathSpace B ⟶ B) =
      SSet.ι₀ ≫ (β_ A (Δ[1] : SSet.{u})).hom ≫
        MonoidalClosed.uncurry h :=
  SSet.comp_eval₀_eq_ι₀_braiding_uncurry h

example :
    h ≫ (SSet.eval₁ : SSet.pathSpace B ⟶ B) =
      SSet.ι₁ ≫ (β_ A (Δ[1] : SSet.{u})).hom ≫
        MonoidalClosed.uncurry h :=
  SSet.comp_eval₁_eq_ι₁_braiding_uncurry h

variable {Y : SSet.{u}} (f : X ⟶ Y)

example :
    (ihom (Δ[1] : SSet.{u})).map f ≫
        (SSet.eval₀ : SSet.pathSpace Y ⟶ Y) =
      (SSet.eval₀ : SSet.pathSpace X ⟶ X) ≫ f :=
  SSet.pathSpace_map_eval₀ f

example :
    (ihom (Δ[1] : SSet.{u})).map f ≫
        (SSet.eval₁ : SSet.pathSpace Y ⟶ Y) =
      (SSet.eval₁ : SSet.pathSpace X ⟶ X) ≫ f :=
  SSet.pathSpace_map_eval₁ f

example :
    f ≫ SSet.constPath Y =
      SSet.constPath X ≫ (ihom (Δ[1] : SSet.{u})).map f :=
  SSet.constPath_naturality f

/- These component clients consume the public laws through this file's
higher-level imports, without unfolding the opaque PathSpace definitions. -/
example (a : SimplexCategoryᵒᵖ) :
    ((ihom (Δ[1] : SSet.{u})).map f ≫
        (SSet.eval₀ : SSet.pathSpace Y ⟶ Y)).app a =
      ((SSet.eval₀ : SSet.pathSpace X ⟶ X) ≫ f).app a :=
  congr_app (SSet.pathSpace_map_eval₀ f) a

example (a : SimplexCategoryᵒᵖ) :
    (f ≫ SSet.constPath Y).app a =
      (SSet.constPath X ≫ (ihom (Δ[1] : SSet.{u})).map f).app a :=
  congr_app (SSet.constPath_naturality f) a

variable (Z : SSet.{u}) (g : Y ⟶ Z)

example :
    (ihom (Δ[1] : SSet.{u})).map f ≫
        (SSet.eval₁ : SSet.pathSpace Y ⟶ Y) ≫ g =
      (SSet.eval₁ : SSet.pathSpace X ⟶ X) ≫ f ≫ g :=
  SSet.pathSpace_map_eval₁_assoc f g

example : SSet.pathSpace X ⟶ X ⊗ X := SSet.evalPair

example :
    SSet.evalPair (X := X) ≫ CartesianMonoidalCategory.fst X X =
      SSet.eval₀ :=
  SSet.evalPair_fst

example :
    SSet.evalPair (X := X) ≫ CartesianMonoidalCategory.snd X X =
      SSet.eval₁ :=
  SSet.evalPair_snd

example :
    (SSet.eval₀ : SSet.pathSpace X ⟶ X) ≫ SSet.constPath X =
      (MonoidalClosed.pre
        (SSet.const (X := (Δ[1] : SSet.{u}))
          (SSet.stdSimplex.obj₀Equiv.{u}.symm 0))).app X :=
  SSet.eval₀_constPath_eq_pre_constZero X

example : SSet.constPath X ≫ SSet.eval₀ = 𝟙 X := by simp

example : SSet.constPath X ≫ SSet.eval₁ = 𝟙 X := by simp

example :
    SSet.constPath X ≫ SSet.evalPair =
      CartesianMonoidalCategory.lift (𝟙 X) (𝟙 X) := by
  simp

variable [SSet.KanComplex X]

example : SSet.KanComplex (SSet.pathSpace X) := inferInstance

example : Fibration (SSet.evalPair (X := X)) := inferInstance

example : Fibration (SSet.eval₀ (X := X)) := inferInstance

example : Fibration (SSet.eval₁ (X := X)) := inferInstance

end PathSpace

section PathSpaceUniverses

variable {X₀ Y₀ : SSet.{0}} (f₀ : X₀ ⟶ Y₀)
variable {X₁ Y₁ : SSet.{1}} (f₁ : X₁ ⟶ Y₁)
variable {Xₘ Yₘ : SSet.{max u v}} (fₘ : Xₘ ⟶ Yₘ)

example :
    (ihom (Δ[1] : SSet.{0})).map f₀ ≫
        (SSet.eval₀ : SSet.pathSpace Y₀ ⟶ Y₀) =
      (SSet.eval₀ : SSet.pathSpace X₀ ⟶ X₀) ≫ f₀ :=
  SSet.pathSpace_map_eval₀ f₀

example :
    (ihom (Δ[1] : SSet.{1})).map f₁ ≫
        (SSet.eval₁ : SSet.pathSpace Y₁ ⟶ Y₁) =
      (SSet.eval₁ : SSet.pathSpace X₁ ⟶ X₁) ≫ f₁ :=
  SSet.pathSpace_map_eval₁ f₁

example :
    fₘ ≫ SSet.constPath Yₘ =
      SSet.constPath Xₘ ≫
        (ihom (Δ[1] : SSet.{max u v})).map fₘ :=
  SSet.constPath_naturality fₘ

end PathSpaceUniverses

section BasedPaths

variable (X : SSet.{u}) [SSet.KanComplex X] (x : X _⦋0⦌)

example : SSet.{u} := SSet.basedPath X x

example : SSet.basedPath X x _⦋0⦌ := SSet.basedPathPoint X x

example : SSet.basedPath X x ⟶ X := SSet.basedPathProj X x

example : SSet.{u} := SSet.loopSpace X x

example : (SSet.basedPathProj X x).app _ (SSet.basedPathPoint X x) = x := by
  simp

example : Fibration (SSet.basedPathProj X x) := inferInstance

example : SSet.KanComplex (SSet.basedPath X x) := inferInstance

example : SSet.KanComplex (SSet.loopSpace X x) := inferInstance

example : SSet.FibrationSequence.{u} := SSet.loopFibrationSequence X x

example : (SSet.loopFibrationSequence X x).E = SSet.basedPath X x := rfl

example : (SSet.loopFibrationSequence X x).B = X := rfl

example : (SSet.loopFibrationSequence X x).p = SSet.basedPathProj X x := rfl

example : (SSet.loopFibrationSequence X x).e = SSet.basedPathPoint X x := rfl

example : (SSet.loopFibrationSequence X x).b = x := rfl

example (n : ℕ) :
    Subsingleton
      (SSet.KanComplex.π n (SSet.basedPath X x)
        (SSet.basedPathPoint X x)) :=
  SSet.subsingleton_pi_basedPath X x n

example (n : ℕ) :
    Function.Bijective
      ((SSet.loopFibrationSequence X x).connectingMap n) :=
  SSet.FibrationSequence.connectingMap_bijective_of_subsingleton_total
    (SSet.loopFibrationSequence X x)
    (SSet.subsingleton_pi_basedPath X x) n

example :
    Function.Bijective
      ((SSet.loopFibrationSequence X x).connectingMap 0) :=
  SSet.FibrationSequence.connectingMap_bijective_of_subsingleton_total
    (SSet.loopFibrationSequence X x)
    (SSet.subsingleton_pi_basedPath X x) 0

end BasedPaths

section PenultimateMultiplication

variable {X : SSet.{u}} [SSet.KanComplex X] {x : X _⦋0⦌} {n : ℕ}
  {p q r : X.PtSimplex (n + 2) x}

example (h : SSet.PtSimplex.MulStruct p q r (Fin.last n).castSucc) :
    SSet.KanComplex.π.mk p * SSet.KanComplex.π.mk q =
      SSet.KanComplex.π.mk r :=
  SSet.PtSimplex.MulStruct.mul_eq_penultimate h

end PenultimateMultiplication

section ConnectingMap

variable (S : SSet.FibrationSequence.{u})

example (n : ℕ) (a b : SSet.KanComplex.π (n + 2) S.B S.b) :
    S.connectingMap (n + 1) (a * b) =
      S.connectingMap (n + 1) a * S.connectingMap (n + 1) b :=
  S.connectingMap_mul n a b

example (g₁ g₂ : SSet.KanComplex.π 1 S.B S.b)
    (h : S.connectingMap 0 g₁ = S.connectingMap 0 g₂) :
    ∃ v : SSet.KanComplex.π 1 S.E S.e,
      g₂ = g₁ * SSet.KanComplex.π.map S.p S.hb 1 v :=
  S.eq_mul_of_connectingMap_zero_eq g₁ g₂ h

variable (hE : ∀ n, Subsingleton (SSet.KanComplex.π n S.E S.e))

example : Function.Bijective (S.connectingMap 0) :=
  S.connectingMap_bijective_of_subsingleton_total hE 0

example (n : ℕ) : Function.Bijective (S.connectingMap (n + 1)) :=
  S.connectingMap_bijective_of_subsingleton_total hE (n + 1)

end ConnectingMap

#print axioms SSet.pathSpace_map_eval₀
#print axioms SSet.pathSpace_map_eval₁
#print axioms SSet.constPath_naturality
#print axioms SSet.uncurry_constPath
#print axioms SSet.comp_eval₀_eq_ι₀_braiding_uncurry
#print axioms SSet.comp_eval₁_eq_ι₁_braiding_uncurry

end MathlibExtTest.AlgebraicTopology.SimplicialSet.PathLoopFibrationSequenceTests
