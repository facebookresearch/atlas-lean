/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.DayConvolution.DayFunctorClosedSymmetric

/-!
# Original Day internal-Hom source projections

The original Day evaluation on every tensor generator is the uncurry of its
original end projection. The same generator equation derives the complete
source precomposition formula for the actual end-based Day closed structure.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uI vI uV vV
open CategoryTheory MonoidalCategory Limits
open scoped MonoidalClosed ExternalProduct

namespace CategoryTheory.MonoidalCategory.DayFunctor

variable {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [MonoidalClosed V]
  [∀ (F G : I ⥤ V), (tensor I).HasPointwiseLeftKanExtension (F ⊠ G)]
  [(Functor.fromPUnit.{0} (𝟙_ I)).HasPointwiseLeftKanExtension
    (Functor.fromPUnit.{0} (𝟙_ V))]
  [∀ (v : V) (d : I), PreservesColimitsOfShape
    (CostructuredArrow (tensor I) d) (tensorLeft v)]
  [∀ (v : V) (d : I), PreservesColimitsOfShape
    (CostructuredArrow (tensor I) d) (tensorRight v)]
  [∀ (v : V) (d : I), PreservesColimitsOfShape
    (CostructuredArrow (Functor.fromPUnit.{0} (𝟙_ I)) d) (tensorLeft v)]
  [∀ (v : V) (d : I), PreservesColimitsOfShape
    (CostructuredArrow (Functor.fromPUnit.{0} (𝟙_ I)) d) (tensorRight v)]
  [∀ (v : V) (d : I × I), PreservesColimitsOfShape
    (CostructuredArrow ((𝟭 I).prod (Functor.fromPUnit.{0} (𝟙_ I))) d) (tensorRight v)]
  [∀ (v : V) (d : I × I), PreservesColimitsOfShape
    (CostructuredArrow ((tensor I).prod (𝟭 I)) d) (tensorRight v)]
  [∀ (F G : I ⥤ V) (c : I), HasEnd
    ((dayConvolutionInternalHomDiagramFunctor F).obj G |>.obj c)]


/-- The unchanged original Day evaluation on every coend pair is exactly the
uncurry of its original end projection. -/
theorem evaluation_generator (F G : DayFunctor I V) (j n : I) :
    (DayFunctor.η F ((ihom F).obj G)).app (j, n) ≫
      ((ihom.ev F).app G).natTrans.app (j ⊗ n) =
    MonoidalClosed.uncurry
      (end_.π ((dayConvolutionInternalHomDiagramFunctor F.functor).obj
        G.functor |>.obj n) j) := by
  let (X Y : DayFunctor I V) : DayConvolution X.functor Y.functor :=
    LawfulDayConvolutionMonoidalCategoryStruct.convolution I V (DayFunctor I V) X Y
  exact DayConvolutionInternalHom.unit_app_ev_app_app
    (C := I) (V := V) (F := F.functor) (G := G.functor)
    (H := ((ihom F).obj G).functor) _ j n

/-- Every complete original Day source map acts on every original end
projection by the actual scalar closed pre-map. -/
theorem internalHomPre {P Q : DayFunctor I V} (f : P ⟶ Q)
    (G : DayFunctor I V) (n j : I) :
    ((MonoidalClosed.pre f).app G).natTrans.app n ≫
      end_.π ((dayConvolutionInternalHomDiagramFunctor P.functor).obj
        G.functor |>.obj n) j =
    end_.π ((dayConvolutionInternalHomDiagramFunctor Q.functor).obj
      G.functor |>.obj n) j ≫
      (MonoidalClosed.pre (f.natTrans.app j)).app (G.functor.obj (j ⊗ n)) := by
  let HP := (ihom P).obj G
  let HQ := (ihom Q).obj G
  let p : HQ ⟶ HP := (MonoidalClosed.pre f).app G
  have hClosed : (P ◁ p) ≫ (ihom.ev P).app G =
      (f ▷ HQ) ≫ (ihom.ev Q).app G :=
    MonoidalClosed.id_tensor_pre_app_comp_ev f G
  have h := congrArg
    (fun z : P ⊗ HQ ⟶ G =>
      (DayFunctor.η P HQ).app (j, n) ≫ z.natTrans.app (j ⊗ n)) hClosed
  have hL :=
    LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit_comp_ι_map_whiskerLeft_app
    V P p j n
  change (DayFunctor.η P HQ).app (j, n) ≫ (P ◁ p).natTrans.app (j ⊗ n) =
    (P.functor.obj j ◁ p.natTrans.app n) ≫ (DayFunctor.η P HP).app (j, n) at hL
  have hR :=
    LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit_comp_ι_map_whiskerRight_app
    I V f HQ j n
  change (DayFunctor.η P HQ).app (j, n) ≫ (f ▷ HQ).natTrans.app (j ⊗ n) =
    (f.natTrans.app j ▷ HQ.functor.obj n) ≫ (DayFunctor.η Q HQ).app (j, n) at hR
  simp only [DayFunctor.comp_natTrans, NatTrans.comp_app] at h
  rw [← Category.assoc, hL, Category.assoc, evaluation_generator,
    ← Category.assoc, hR, Category.assoc, evaluation_generator] at h
  let Z := G.functor.obj (j ⊗ n)
  let πP : HP.functor.obj n ⟶ (ihom (P.functor.obj j)).obj Z :=
    end_.π ((dayConvolutionInternalHomDiagramFunctor P.functor).obj G.functor |>.obj n) j
  let πQ : HQ.functor.obj n ⟶ (ihom (Q.functor.obj j)).obj Z :=
    end_.π ((dayConvolutionInternalHomDiagramFunctor Q.functor).obj G.functor |>.obj n) j
  change p.natTrans.app n ≫ πP =
    πQ ≫ (MonoidalClosed.pre (f.natTrans.app j)).app Z
  apply MonoidalClosed.uncurry_injective (A := P.functor.obj j)
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_pre_app]
  exact h

end CategoryTheory.MonoidalCategory.DayFunctor
