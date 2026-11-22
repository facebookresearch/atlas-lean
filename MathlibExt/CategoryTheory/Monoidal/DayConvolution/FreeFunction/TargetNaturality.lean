/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.DayConvolution.FreeFunction.TargetModule
public import MathlibExt.CategoryTheory.Monoidal.DayConvolution.FreeFunction.Naturality

/-!
# Naturality of free-module target comparisons

Under the displayed Day-convolution Kan-extension and tensor-colimit hypotheses, compares a
supplied module target functor with the free internal-Hom target. The component formula retains
the forgetful-functor comparison and its compatibility with the coefficient action.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uI vI uV vV
open CategoryTheory MonoidalCategory Limits
open scoped MonoidalClosed ExternalProduct CategoryTheory.MonObj

namespace NativeOmegaRecovery.FullFreeFunctionTargetNaturality
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

private abbrev freeDiagram (r : I) (M : V) : DayFunctor I V :=
  .mk ((evaluationLeftAdjoint V r).obj M)

set_option maxHeartbeats 1000000 in
/-- Naturality of the actual full target sequence comparison and its derived
pair equations gives the original free-function module NatIso on every target map. -/
def comparison (A : CommMon (DayFunctor I V)) (r : I) (M : V)
    (K : Mod (DayFunctor I V) A.X ⥤ Mod (DayFunctor I V) A.X)
    (t : Mod.forget (D := DayFunctor I V) A.X ⋙
      NativeOmegaPreparation.DayIndexOrder.rightTargetFunctor r M ≅
        K ⋙ Mod.forget (D := DayFunctor I V) A.X)
    (hPair : ∀ N a n,
      FullFreeFunctionPair.targetAction A r M N a n ≫ (t.app N).hom.natTrans.app (a ⊗ n) =
        (A.X.functor.obj a ◁ (t.app N).hom.natTrans.app n) ≫
          FullFreeFunctionModuleComparison.pairAction (A := A) (K.obj N) a n) :
    Mod.internalHom A ((Mod.free A.X).obj ((DayFunctor.mk ((evaluationLeftAdjoint V r).obj M)))) ≅ K :=
  NatIso.ofComponents
    (fun N => FullFreeFunctionTargetModule.comparison A r M N (K.obj N) (t.app N) (hPair N))
    (by
      intro N N' f
      apply Mod.hom_ext
      change ((Mod.internalHom A ((Mod.free A.X).obj (freeDiagram r M))).map f).hom ≫
          (FullFreeFunctionTargetModule.comparison A r M N' (K.obj N') (t.app N')
              (hPair N')).hom.hom =
        (FullFreeFunctionTargetModule.comparison A r M N (K.obj N) (t.app N) (hPair N)).hom.hom ≫
          (K.map f).hom
      let H := Mod.internalHom A ((Mod.free A.X).obj (freeDiagram r M))
      let G := NativeOmegaPreparation.DayIndexOrder.rightTargetFunctor r M
      let m : (H.obj N).X ⟶ (H.obj N').X := (H.map f).hom
      let k : (K.obj N).X ⟶ (K.obj N').X := (K.map f).hom
      let e : (H.obj N).X ⟶ G.obj N.X := (FullFreeFunctionPair.comparison A r M N).hom
      let e' : (H.obj N').X ⟶ G.obj N'.X := (FullFreeFunctionPair.comparison A r M N').hom
      let b : G.obj N.X ⟶ G.obj N'.X := G.map f.hom
      let τ : G.obj N.X ⟶ (K.obj N).X := (t.app N).hom
      let τ' : G.obj N'.X ⟶ (K.obj N').X := (t.app N').hom
      let c : (H.obj N).X ⟶ (K.obj N).X :=
        (FullFreeFunctionTargetModule.comparison A r M N (K.obj N) (t.app N) (hPair N)).hom.hom
      let c' : (H.obj N').X ⟶ (K.obj N').X :=
        (FullFreeFunctionTargetModule.comparison A r M N' (K.obj N') (t.app N') (hPair N')).hom.hom
      have hc : c = e ≫ τ := FullFreeFunctionTargetModule.comparison_hom A r M N
        (K.obj N) (t.app N) (hPair N)
      have hc' : c' = e' ≫ τ' := FullFreeFunctionTargetModule.comparison_hom A r M N'
        (K.obj N') (t.app N') (hPair N')
      have h : m ≫ e' = e ≫ b := FullFreeFunctionNaturality.forward_naturality A r M f
      have ht : b ≫ τ' = τ ≫ k := t.hom.naturality f
      change m ≫ c' = c ≫ k
      calc
        _ = m ≫ (e' ≫ τ') := congrArg (fun z => m ≫ z) hc'
        _ = (m ≫ e') ≫ τ' := (Category.assoc m e' τ').symm
        _ = (e ≫ b) ≫ τ' := congrArg (fun z => z ≫ τ') h
        _ = e ≫ (b ≫ τ') := Category.assoc e b τ'
        _ = e ≫ (τ ≫ k) := congrArg (fun z => e ≫ z) ht
        _ = (e ≫ τ) ≫ k := (Category.assoc e τ k).symm
        _ = c ≫ k := congrArg (fun z => z ≫ k) hc.symm)

/-- Every full target NatIso component is the original full module comparison. -/
theorem hom_app (A : CommMon (DayFunctor I V)) (r : I) (M : V)
    (K : Mod (DayFunctor I V) A.X ⥤ Mod (DayFunctor I V) A.X)
    (t : Mod.forget (D := DayFunctor I V) A.X ⋙
      NativeOmegaPreparation.DayIndexOrder.rightTargetFunctor r M ≅
        K ⋙ Mod.forget (D := DayFunctor I V) A.X)
    (hPair : ∀ N a n,
      FullFreeFunctionPair.targetAction A r M N a n ≫ (t.app N).hom.natTrans.app (a ⊗ n) =
        (A.X.functor.obj a ◁ (t.app N).hom.natTrans.app n) ≫
          FullFreeFunctionModuleComparison.pairAction (A := A) (K.obj N) a n)
    (N : Mod (DayFunctor I V) A.X) :
    (comparison A r M K t hPair).hom.app N =
      (FullFreeFunctionTargetModule.comparison A r M N (K.obj N) (t.app N) (hPair N)).hom := rfl

/-- Its entire underlying map keeps the actual original end comparison and target map. -/
theorem hom_app_hom (A : CommMon (DayFunctor I V)) (r : I) (M : V)
    (K : Mod (DayFunctor I V) A.X ⥤ Mod (DayFunctor I V) A.X)
    (t : Mod.forget (D := DayFunctor I V) A.X ⋙
      NativeOmegaPreparation.DayIndexOrder.rightTargetFunctor r M ≅
        K ⋙ Mod.forget (D := DayFunctor I V) A.X)
    (hPair : ∀ N a n,
      FullFreeFunctionPair.targetAction A r M N a n ≫ (t.app N).hom.natTrans.app (a ⊗ n) =
        (A.X.functor.obj a ◁ (t.app N).hom.natTrans.app n) ≫
          FullFreeFunctionModuleComparison.pairAction (A := A) (K.obj N) a n)
    (N : Mod (DayFunctor I V) A.X) :
    ((comparison A r M K t hPair).hom.app N).hom =
      (FullFreeFunctionPair.comparison A r M N).hom ≫ (t.app N).hom :=
  FullFreeFunctionTargetModule.comparison_hom A r M N (K.obj N) (t.app N) (hPair N)

/-- Every level of that full map retains the original free-unit/end/braid component. -/
theorem hom_app_component (A : CommMon (DayFunctor I V)) (r : I) (M : V)
    (K : Mod (DayFunctor I V) A.X ⥤ Mod (DayFunctor I V) A.X)
    (t : Mod.forget (D := DayFunctor I V) A.X ⋙
      NativeOmegaPreparation.DayIndexOrder.rightTargetFunctor r M ≅
        K ⋙ Mod.forget (D := DayFunctor I V) A.X)
    (hPair : ∀ N a n,
      FullFreeFunctionPair.targetAction A r M N a n ≫ (t.app N).hom.natTrans.app (a ⊗ n) =
        (A.X.functor.obj a ◁ (t.app N).hom.natTrans.app n) ≫
          FullFreeFunctionModuleComparison.pairAction (A := A) (K.obj N) a n)
    (N : Mod (DayFunctor I V) A.X) (n : I) :
    ((comparison A r M K t hPair).hom.app N).hom.natTrans.app n =
      (FullFreeFunctionPair.comparison A r M N).hom.natTrans.app n ≫
        (t.app N).hom.natTrans.app n :=
  FullFreeFunctionTargetModule.comparison_hom_component A r M N (K.obj N) (t.app N) (hPair N) n

end NativeOmegaRecovery.FullFreeFunctionTargetNaturality
