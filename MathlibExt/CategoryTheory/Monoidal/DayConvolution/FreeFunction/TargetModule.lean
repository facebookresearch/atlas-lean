/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.DayConvolution.FreeFunction.ModuleComparison

/-!
# Target modules for free function-spectrum comparisons

Under the stated Day and limit hypotheses, an isomorphism from the
shifted-cotensor object to a target module lifts to a module isomorphism when
it satisfies the full coefficient-pair action equation. Tensor-generator
extensionality proves the required linearity. The resulting comparison from
the free-source Hom module retains both the original end comparison and the
target map, with explicit forward, inverse and component formulas.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uI vI uV vV
open CategoryTheory MonoidalCategory Limits
open scoped MonoidalClosed ExternalProduct CategoryTheory.MonObj

namespace NativeOmegaRecovery.FullFreeFunctionTargetModule

variable {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]
  [MonoidalClosed V] [∀ a b : I, HasCoproductsOfShape (a ⟶ b) V]
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
  [HasEqualizers (DayFunctor I V)]

private abbrev pair {A : CommMon (DayFunctor I V)}
    (T : Mod (DayFunctor I V) A.X) (a n : I) :=
  FullFreeFunctionModuleComparison.pairAction (I := I) (V := V) (A := A) T a n

omit [MonoidalClosed V] [∀ a b : I, HasCoproductsOfShape (a ⟶ b) V]
  [∀ (F G : I ⥤ V) (c : I), HasEnd
    ((dayConvolutionInternalHomDiagramFunctor F).obj G |>.obj c)]
  [HasEqualizers (DayFunctor I V)] in
private theorem linear_of_pair (A : CommMon (DayFunctor I V))
    (T K : Mod (DayFunctor I V) A.X) (t : T.X ≅ K.X)
    (hPair : ∀ a n, pair T a n ≫ t.hom.natTrans.app (a ⊗ n) =
      (A.X.functor.obj a ◁ t.hom.natTrans.app n) ≫ pair K a n) :
    T.mod.smul ≫ t.hom = (A.X ◁ t.hom) ≫ K.mod.smul := by
  apply DayFunctor.tensor_hom_ext
  intro a n
  have hw :=
    LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit_comp_ι_map_whiskerLeft_app
      V A.X t.hom a n
  change (DayFunctor.η A.X T.X).app (a, n) ≫
      (A.X ◁ t.hom).natTrans.app (a ⊗ n) =
    (A.X.functor.obj a ◁ t.hom.natTrans.app n) ≫ (DayFunctor.η A.X K.X).app (a, n) at hw
  have hTail := congrArg
    (fun z : A.X.functor.obj a ⊗ T.X.functor.obj n ⟶
      (A.X ⊗ K.X).functor.obj (a ⊗ n) => z ≫ K.mod.smul.natTrans.app (a ⊗ n)) hw
  have hs := hPair a n
  dsimp only [pair, FullFreeFunctionModuleComparison.pairAction] at hs
  simp only [DayFunctor.comp_natTrans, NatTrans.comp_app]
  have hTail' : (DayFunctor.η A.X T.X).app (a, n) ≫
      (A.X ◁ t.hom).natTrans.app (a ⊗ n) ≫ K.mod.smul.natTrans.app (a ⊗ n) =
    (A.X.functor.obj a ◁ t.hom.natTrans.app n) ≫
      (DayFunctor.η A.X K.X).app (a, n) ≫ K.mod.smul.natTrans.app (a ⊗ n) := by
    simpa only [Category.assoc] using hTail
  simpa only [Category.assoc] using hs.trans hTail'.symm

omit [MonoidalClosed V] [∀ a b : I, HasCoproductsOfShape (a ⟶ b) V]
  [∀ (F G : I ⥤ V) (c : I), HasEnd
    ((dayConvolutionInternalHomDiagramFunctor F).obj G |>.obj c)]
  [HasEqualizers (DayFunctor I V)] in
private def iso_of_pair (A : CommMon (DayFunctor I V))
    (T K : Mod (DayFunctor I V) A.X) (t : T.X ≅ K.X)
    (hPair : ∀ a n, pair T a n ≫ t.hom.natTrans.app (a ⊗ n) =
      (A.X.functor.obj a ◁ t.hom.natTrans.app n) ≫ pair K a n) : T ≅ K := by
  letI : ModObj A.X T.X := T.mod
  letI : ModObj A.X K.X := K.mod
  have h := linear_of_pair A T K t hPair
  letI : IsModHom A.X t.hom := ⟨h⟩
  have hi : K.mod.smul ≫ t.inv = (A.X ◁ t.inv) ≫ T.mod.smul :=
    IsModHom.smul_hom (A := A.X) (f := t.inv)
  exact { hom := Mod.Hom.mk' t.hom h, inv := Mod.Hom.mk' t.inv hi
          hom_inv_id := by apply Mod.hom_ext; exact t.hom_inv_id
          inv_hom_id := by apply Mod.hom_ext; exact t.inv_hom_id }

/-- An actual target module with the derived original full pair formula is
isomorphic to the lawfully transported original free-function module. -/
def targetIso (A : CommMon (DayFunctor I V)) (r : I) (M : V)
    (N K : Mod (DayFunctor I V) A.X)
    (t : (NativeOmegaPreparation.DayIndexOrder.rightTargetFunctor r M).obj N.X ≅ K.X)
    (hPair : ∀ a n,
      FullFreeFunctionPair.targetAction A r M N a n ≫ t.hom.natTrans.app (a ⊗ n) =
        (A.X.functor.obj a ◁ t.hom.natTrans.app n) ≫
          FullFreeFunctionModuleComparison.pairAction (A := A) K a n) :
    FullFreeFunctionModuleComparison.targetModule A r M N ≅ K := by
  let T := FullFreeFunctionModuleComparison.targetModule A r M N
  have hT (a n : I) : FullFreeFunctionModuleComparison.pairAction (A := A) T a n ≫ t.hom.natTrans.app (a ⊗ n) =
      (A.X.functor.obj a ◁ t.hom.natTrans.app n) ≫ FullFreeFunctionModuleComparison.pairAction (A := A) K a n := by
    let G := (NativeOmegaPreparation.DayIndexOrder.rightTargetFunctor r M).obj N.X
    have h := congrArg
      (fun z : A.X.functor.obj a ⊗ G.functor.obj n ⟶ G.functor.obj (a ⊗ n) =>
        z ≫ t.hom.natTrans.app (a ⊗ n))
      (FullFreeFunctionModuleComparison.target_pair A r M N a n)
    exact h.trans (hPair a n)
  let e : T.X ≅ K.X := t
  letI : ModObj A.X T.X := T.mod
  letI : ModObj A.X K.X := K.mod
  have h : T.mod.smul ≫ e.hom = (A.X ◁ e.hom) ≫ K.mod.smul := by
    apply DayFunctor.tensor_hom_ext
    intro a n
    have hw :=
      LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit_comp_ι_map_whiskerLeft_app
        V A.X e.hom a n
    change (DayFunctor.η A.X T.X).app (a, n) ≫
        (A.X ◁ e.hom).natTrans.app (a ⊗ n) =
      (A.X.functor.obj a ◁ e.hom.natTrans.app n) ≫ (DayFunctor.η A.X K.X).app (a, n) at hw
    have hTail := congrArg
      (fun z : A.X.functor.obj a ⊗ T.X.functor.obj n ⟶
        (A.X ⊗ K.X).functor.obj (a ⊗ n) => z ≫ K.mod.smul.natTrans.app (a ⊗ n)) hw
    have hs : FullFreeFunctionModuleComparison.pairAction (A := A) T a n ≫
        e.hom.natTrans.app (a ⊗ n) =
      (A.X.functor.obj a ◁ e.hom.natTrans.app n) ≫
        FullFreeFunctionModuleComparison.pairAction (A := A) K a n := hT a n
    dsimp only [FullFreeFunctionModuleComparison.pairAction] at hs
    simp only [DayFunctor.comp_natTrans, NatTrans.comp_app]
    have hTail' : (DayFunctor.η A.X T.X).app (a, n) ≫
        (A.X ◁ e.hom).natTrans.app (a ⊗ n) ≫ K.mod.smul.natTrans.app (a ⊗ n) =
      (A.X.functor.obj a ◁ e.hom.natTrans.app n) ≫
        (DayFunctor.η A.X K.X).app (a, n) ≫ K.mod.smul.natTrans.app (a ⊗ n) := by
      simpa only [Category.assoc] using hTail
    simpa only [Category.assoc] using hs.trans hTail'.symm
  letI : IsModHom A.X e.hom := ⟨h⟩
  have hi : K.mod.smul ≫ e.inv = (A.X ◁ e.inv) ≫ T.mod.smul :=
    IsModHom.smul_hom (A := A.X) (f := e.inv)
  exact { hom := Mod.Hom.mk' e.hom h, inv := Mod.Hom.mk' e.inv hi
          hom_inv_id := by apply Mod.hom_ext; exact e.hom_inv_id
          inv_hom_id := by apply Mod.hom_ext; exact e.inv_hom_id }

/-- Both original free-unit/end maps give the full actual module comparison,
using the independently derived target action and original target iso. -/
def comparison (A : CommMon (DayFunctor I V)) (r : I) (M : V)
    (N K : Mod (DayFunctor I V) A.X)
    (t : (NativeOmegaPreparation.DayIndexOrder.rightTargetFunctor r M).obj N.X ≅ K.X)
    (hPair : ∀ a n,
      FullFreeFunctionPair.targetAction A r M N a n ≫ t.hom.natTrans.app (a ⊗ n) =
        (A.X.functor.obj a ◁ t.hom.natTrans.app n) ≫
          FullFreeFunctionModuleComparison.pairAction (A := A) K a n) :
    FullFreeFunctionModuleComparison.homModule A r M N ≅ K :=
  FullFreeFunctionModuleComparison.comparison A r M N ≪≫ targetIso A r M N K t hPair

/-- The whole forward module map remains the original end comparison and actual target map. -/
theorem comparison_hom (A : CommMon (DayFunctor I V)) (r : I) (M : V)
    (N K : Mod (DayFunctor I V) A.X)
    (t : (NativeOmegaPreparation.DayIndexOrder.rightTargetFunctor r M).obj N.X ≅ K.X)
    (hPair : ∀ a n,
      FullFreeFunctionPair.targetAction A r M N a n ≫ t.hom.natTrans.app (a ⊗ n) =
        (A.X.functor.obj a ◁ t.hom.natTrans.app n) ≫
          FullFreeFunctionModuleComparison.pairAction (A := A) K a n) :
    (comparison A r M N K t hPair).hom.hom =
      (FullFreeFunctionPair.comparison A r M N).hom ≫ t.hom := rfl

/-- The whole inverse remains the original inverse target map and end extension. -/
theorem comparison_inv (A : CommMon (DayFunctor I V)) (r : I) (M : V)
    (N K : Mod (DayFunctor I V) A.X)
    (t : (NativeOmegaPreparation.DayIndexOrder.rightTargetFunctor r M).obj N.X ≅ K.X)
    (hPair : ∀ a n,
      FullFreeFunctionPair.targetAction A r M N a n ≫ t.hom.natTrans.app (a ⊗ n) =
        (A.X.functor.obj a ◁ t.hom.natTrans.app n) ≫
          FullFreeFunctionModuleComparison.pairAction (A := A) K a n) :
    (comparison A r M N K t hPair).inv.hom =
      t.inv ≫ (FullFreeFunctionPair.comparison A r M N).inv := rfl

/-- Every whole forward component retains the original free-unit/end/braid map. -/
theorem comparison_hom_component (A : CommMon (DayFunctor I V)) (r : I) (M : V)
    (N K : Mod (DayFunctor I V) A.X)
    (t : (NativeOmegaPreparation.DayIndexOrder.rightTargetFunctor r M).obj N.X ≅ K.X)
    (hPair : ∀ a n,
      FullFreeFunctionPair.targetAction A r M N a n ≫ t.hom.natTrans.app (a ⊗ n) =
        (A.X.functor.obj a ◁ t.hom.natTrans.app n) ≫
          FullFreeFunctionModuleComparison.pairAction (A := A) K a n) (n : I) :
    (comparison A r M N K t hPair).hom.hom.natTrans.app n =
      (FullFreeFunctionPair.comparison A r M N).hom.natTrans.app n ≫ t.hom.natTrans.app n := rfl

/-- Every inverse component retains the same complete inverse end-extension map. -/
theorem comparison_inv_component (A : CommMon (DayFunctor I V)) (r : I) (M : V)
    (N K : Mod (DayFunctor I V) A.X)
    (t : (NativeOmegaPreparation.DayIndexOrder.rightTargetFunctor r M).obj N.X ≅ K.X)
    (hPair : ∀ a n,
      FullFreeFunctionPair.targetAction A r M N a n ≫ t.hom.natTrans.app (a ⊗ n) =
        (A.X.functor.obj a ◁ t.hom.natTrans.app n) ≫
          FullFreeFunctionModuleComparison.pairAction (A := A) K a n) (n : I) :
    (comparison A r M N K t hPair).inv.hom.natTrans.app n =
      t.inv.natTrans.app n ≫ (FullFreeFunctionPair.comparison A r M N).inv.natTrans.app n := rfl

end NativeOmegaRecovery.FullFreeFunctionTargetModule
