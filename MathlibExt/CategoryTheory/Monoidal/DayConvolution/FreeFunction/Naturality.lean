/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.DayConvolution.FreeFunction.Pair
public import MathlibExt.CategoryTheory.Monoidal.DayConvolution.InternalHomSource
public import MathlibExt.CategoryTheory.Monoidal.Mod.FreeInternalHom

/-!
# Naturality of free-source Day internal Hom comparisons

For a commutative Day monoid, the free-source internal Hom comparison assembles into a
natural isomorphism in the target module. Its component formulas retain free evaluation,
end projection and index braiding, and source precomposition is characterized by the
free adjunct at the identity index.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uI vI uV vV
open CategoryTheory MonoidalCategory Limits
open scoped MonoidalClosed ExternalProduct CategoryTheory.MonObj

namespace NativeOmegaRecovery.FullFreeFunctionNaturality

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

/-- The exact selected Day end family supplies the unchanged free-diagram end. -/
local instance originalFreeEnd (r : I) (M : V) (G : I ⥤ V) (n : I) :
    HasEnd (NativeOmegaPreparation.OrdinaryFreeEnd.diagram r M (tensorRight n ⋙ G)) := by
  change HasEnd ((dayConvolutionInternalHomDiagramFunctor
    ((evaluationLeftAdjoint V r).obj M)).obj G |>.obj n)
  infer_instance

/-- The same original free-unit/end/braid maps assemble over every complete
original target module morphism. -/
def comparison (A : CommMon (DayFunctor I V)) (r : I) (M : V) :
    Mod.internalHom A ((Mod.free A.X).obj
      (DayFunctor.mk ((evaluationLeftAdjoint V r).obj M))) ⋙
      Mod.forget (D := DayFunctor I V) A.X ≅
    Mod.forget (D := DayFunctor I V) A.X ⋙
      NativeOmegaPreparation.DayIndexOrder.rightTargetFunctor r M :=
  CategoryTheory.Mod.FreeInternalHom.comparison A
      (DayFunctor.mk ((evaluationLeftAdjoint V r).obj M)) ≪≫
    Functor.isoWhiskerLeft (Mod.forget (D := DayFunctor I V) A.X)
      (NativeOmegaPreparation.DayFreeEnd.comparison r M ≪≫
        NativeOmegaPreparation.DayIndexOrder.comparison r M)

/-- The complete forward target-natural map is the original comparison map. -/
theorem comparison_hom_app (A : CommMon (DayFunctor I V)) (r : I) (M : V)
    (N : Mod (DayFunctor I V) A.X) :
    (comparison A r M).hom.app N = (FullFreeFunctionPair.comparison A r M N).hom := rfl

/-- The complete inverse target-natural map is the original inverse comparison map. -/
theorem comparison_inv_app (A : CommMon (DayFunctor I V)) (r : I) (M : V)
    (N : Mod (DayFunctor I V) A.X) :
    (comparison A r M).inv.app N = (FullFreeFunctionPair.comparison A r M N).inv := rfl

/-- Every entire original target module arrow commutes with full forward comparison. -/
theorem forward_naturality (A : CommMon (DayFunctor I V)) (r : I) (M : V)
    {N N' : Mod (DayFunctor I V) A.X} (f : N ⟶ N') :
    ((Mod.internalHom A ((Mod.free A.X).obj
      (DayFunctor.mk ((evaluationLeftAdjoint V r).obj M)))).map f).hom ≫
      (FullFreeFunctionPair.comparison A r M N').hom =
    (FullFreeFunctionPair.comparison A r M N).hom ≫
      (NativeOmegaPreparation.DayIndexOrder.rightTargetFunctor r M).map f.hom :=
  (comparison A r M).hom.naturality f

/-- The original inverse retains the same complete target-morphism naturality. -/
theorem inverse_naturality (A : CommMon (DayFunctor I V)) (r : I) (M : V)
    {N N' : Mod (DayFunctor I V) A.X} (f : N ⟶ N') :
    (NativeOmegaPreparation.DayIndexOrder.rightTargetFunctor r M).map f.hom ≫
      (FullFreeFunctionPair.comparison A r M N').inv =
    (FullFreeFunctionPair.comparison A r M N).inv ≫
      ((Mod.internalHom A ((Mod.free A.X).obj
        (DayFunctor.mk ((evaluationLeftAdjoint V r).obj M)))).map f).hom :=
  (comparison A r M).inv.naturality f

/-- Each complete original comparison component keeps actual module free-unit
evaluation, original end evaluation and the original beta_(r,n). -/
theorem forward_component (A : CommMon (DayFunctor I V)) (r : I) (M : V)
    (N : Mod (DayFunctor I V) A.X) (n : I) :
    (FullFreeFunctionPair.comparison A r M N).hom.natTrans.app n =
      (Mod.FreeInternalHom.forward A (DayFunctor.mk ((evaluationLeftAdjoint V r).obj M))
        N).natTrans.app n ≫
        NativeOmegaPreparation.OrdinaryFreeEnd.forward r M (tensorRight n ⋙ N.X.functor) ≫
        (ihom M).map (N.X.functor.map (β_ r n).hom) := rfl

omit [HasEqualizers (DayFunctor I V)] in
/-- The original Day free-end comparison after an arbitrary complete Day source
map is determined by its literal identity-index free adjunct. -/
theorem day_free_source_projection (r s : I) (M M' : V)
    (f : (DayFunctor.mk ((evaluationLeftAdjoint V s).obj M')) ⟶
      (DayFunctor.mk ((evaluationLeftAdjoint V r).obj M))) (G : DayFunctor I V) (n : I) :
    ((MonoidalClosed.pre f).app G).natTrans.app n ≫
      ((NativeOmegaPreparation.DayFreeEnd.comparison s M' ≪≫
        NativeOmegaPreparation.DayIndexOrder.comparison s M').app G).hom.natTrans.app n =
    end_.π ((dayConvolutionInternalHomDiagramFunctor
      (DayFunctor.mk ((evaluationLeftAdjoint V r).obj M)).functor).obj
      G.functor |>.obj n) s ≫
      (MonoidalClosed.pre
        (Sigma.ι (fun _ : s ⟶ s => M') (𝟙 s) ≫ f.natTrans.app s)).app
          (G.functor.obj (s ⊗ n)) ≫
      (ihom M').map (G.functor.map (β_ s n).hom) := by
  let T := G.functor.obj (s ⊗ n)
  let Hr := (ihom (freeDiagram r M)).obj G
  let Hs := (ihom (freeDiagram s M')).obj G
  let p : Hr.functor.obj n ⟶ Hs.functor.obj n :=
    ((MonoidalClosed.pre f).app G).natTrans.app n
  let πr : Hr.functor.obj n ⟶ (ihom ((freeDiagram r M).functor.obj s)).obj T :=
    end_.π ((dayConvolutionInternalHomDiagramFunctor (freeDiagram r M).functor).obj
      G.functor |>.obj n) s
  let πs : Hs.functor.obj n ⟶ (ihom ((freeDiagram s M').functor.obj s)).obj T :=
    end_.π ((dayConvolutionInternalHomDiagramFunctor (freeDiagram s M').functor).obj
      G.functor |>.obj n) s
  let g : M' ⟶ (freeDiagram s M').functor.obj s :=
    Sigma.ι (fun _ : s ⟶ s => M') (𝟙 s)
  let b : (ihom M').obj T ⟶ (ihom M').obj (G.functor.obj (n ⊗ s)) :=
    (ihom M').map (G.functor.map (β_ s n).hom)
  have hp : p ≫ πs = πr ≫ (MonoidalClosed.pre (f.natTrans.app s)).app T :=
    DayFunctor.internalHomPre f G n s
  have hpre := congrArg
    (fun z : ihom ((freeDiagram r M).functor.obj s) ⟶ ihom M' => z.app T)
    (MonoidalClosed.pre_map g (f.natTrans.app s))
  simp only [NatTrans.comp_app] at hpre
  change p ≫ ((πs ≫ (MonoidalClosed.pre g).app T) ≫ b) =
    πr ≫ (MonoidalClosed.pre (g ≫ f.natTrans.app s)).app T ≫ b
  simp only [Category.assoc]
  have h := congrArg
    (fun z : Hr.functor.obj n ⟶ (ihom ((freeDiagram s M').functor.obj s)).obj T =>
      z ≫ (MonoidalClosed.pre g).app T ≫ b) hp
  have ht := congrArg
    (fun z : (ihom ((freeDiagram r M).functor.obj s)).obj T ⟶ (ihom M').obj T =>
      πr ≫ z ≫ b) hpre.symm
  have hStep : p ≫ πs ≫ (MonoidalClosed.pre g).app T ≫ b =
      πr ≫ (MonoidalClosed.pre (f.natTrans.app s)).app T ≫
        (MonoidalClosed.pre g).app T ≫ b := by
    simpa only [Category.assoc] using h
  have hTail : πr ≫ (MonoidalClosed.pre (f.natTrans.app s)).app T ≫
      (MonoidalClosed.pre g).app T ≫ b =
        πr ≫ (MonoidalClosed.pre (g ≫ f.natTrans.app s)).app T ≫ b := by
    simpa only [Category.assoc] using ht
  exact hStep.trans hTail

end NativeOmegaRecovery.FullFreeFunctionNaturality
