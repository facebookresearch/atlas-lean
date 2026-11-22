/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.DayConvolution.FreeFunction.Pair
public import MathlibExt.CategoryTheory.Monoidal.Mod.IsoTransport

/-!
# Free-source Day internal Hom comparisons as module isomorphisms

The free-source Day internal Hom comparison transports the module structure to its
shifted-cotensor target. Under the stated Kan-extension, tensor-preservation, end and
equalizer hypotheses, the forward and inverse maps are module morphisms and the induced
coefficient action satisfies the generator-pair formula.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uI vI uV vV
open CategoryTheory MonoidalCategory Limits
open scoped MonoidalClosed ExternalProduct CategoryTheory.MonObj

namespace NativeOmegaRecovery.FullFreeFunctionModuleComparison

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

/-- The actual original free-source internal-Hom module. -/
abbrev homModule (A : CommMon (DayFunctor I V)) (r : I) (M : V)
    (N : Mod (DayFunctor I V) A.X) :=
  (Mod.internalHom A ((Mod.free A.X).obj
    (DayFunctor.mk ((evaluationLeftAdjoint V r).obj M)))).obj N

/-- The unchanged right-index target obtains its full module laws from the
existing lawful transport of the actual original module and end comparison. -/
def targetModule (A : CommMon (DayFunctor I V)) (r : I) (M : V)
    (N : Mod (DayFunctor I V) A.X) : Mod (DayFunctor I V) A.X :=
  ModuleIsoTransport.object A.X (homModule A r M N) (FullFreeFunctionPair.comparison A r M N)

/-- The actual original two full underlying maps are inverse module morphisms
by the existing lawful module transport, without a supplied action dictionary. -/
def comparison (A : CommMon (DayFunctor I V)) (r : I) (M : V)
    (N : Mod (DayFunctor I V) A.X) : homModule A r M N ≅ targetModule A r M N :=
  ModuleIsoTransport.iso A.X (homModule A r M N) (FullFreeFunctionPair.comparison A r M N)

/-- The complete forward module map remains the original full free-unit/end/braid map. -/
theorem comparison_hom (A : CommMon (DayFunctor I V)) (r : I) (M : V)
    (N : Mod (DayFunctor I V) A.X) :
    (comparison A r M N).hom.hom = (FullFreeFunctionPair.comparison A r M N).hom := rfl

/-- The complete module inverse remains the original full inverse map. -/
theorem comparison_inv (A : CommMon (DayFunctor I V)) (r : I) (M : V)
    (N : Mod (DayFunctor I V) A.X) :
    (comparison A r M N).inv.hom = (FullFreeFunctionPair.comparison A r M N).inv := rfl

/-- The original Day tensor generator followed by the actual full module scalar action. -/
abbrev pairAction {A : CommMon (DayFunctor I V)}
    (N : Mod (DayFunctor I V) A.X) (a n : I) :=
  (DayFunctor.η A.X N.X).app (a, n) ≫ N.mod.smul.natTrans.app (a ⊗ n)

omit [MonoidalClosed V] [∀ a b : I, HasCoproductsOfShape (a ⟶ b) V]
  [∀ (F G : I ⥤ V) (c : I), HasEnd
    ((dayConvolutionInternalHomDiagramFunctor F).obj G |>.obj c)]
  [HasEqualizers (DayFunctor I V)] in
/-- Every actual full Day-module morphism preserves every original tensor generator. -/
private theorem pair_morphism (A : CommMon (DayFunctor I V))
    {X Y : Mod (DayFunctor I V) A.X} (f : X ⟶ Y) (a n : I) :
    pairAction X a n ≫ f.hom.natTrans.app (a ⊗ n) =
      (A.X.functor.obj a ◁ f.hom.natTrans.app n) ≫ pairAction Y a n := by
  let m := f.hom
  let γX := X.mod.smul
  let γY := Y.mod.smul
  let iX := (DayFunctor.η A.X X.X).app (a, n)
  let iY := (DayFunctor.η A.X Y.X).app (a, n)
  have hModule : γX ≫ m = (A.X ◁ m) ≫ γY := f.isModHom.smul_hom
  have hApp : γX.natTrans.app (a ⊗ n) ≫ m.natTrans.app (a ⊗ n) =
      (A.X ◁ m).natTrans.app (a ⊗ n) ≫ γY.natTrans.app (a ⊗ n) := by
    have h := congrArg (fun z : A.X ⊗ X.X ⟶ Y.X => z.natTrans.app (a ⊗ n)) hModule
    simpa only [DayFunctor.comp_natTrans, NatTrans.comp_app] using h
  have hW :=
    LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit_comp_ι_map_whiskerLeft_app
      V A.X m a n
  change iX ≫ (A.X ◁ m).natTrans.app (a ⊗ n) =
    (A.X.functor.obj a ◁ m.natTrans.app n) ≫ iY at hW
  change (iX ≫ γX.natTrans.app (a ⊗ n)) ≫ m.natTrans.app (a ⊗ n) =
    (A.X.functor.obj a ◁ m.natTrans.app n) ≫ iY ≫ γY.natTrans.app (a ⊗ n)
  calc
    _ = iX ≫ (A.X ◁ m).natTrans.app (a ⊗ n) ≫ γY.natTrans.app (a ⊗ n) := by
      simpa only [Category.assoc] using congrArg
        (fun z : (A.X ⊗ X.X).functor.obj (a ⊗ n) ⟶ Y.X.functor.obj (a ⊗ n) => iX ≫ z) hApp
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun z => z ≫ γY.natTrans.app (a ⊗ n)) hW

/-- The complete original Day-generator equation for the lawfully transported
right-target module, with the actual original action and coefficient maps. -/
def targetPairEquation (A : CommMon (DayFunctor I V)) (r : I) (M : V)
    (N : Mod (DayFunctor I V) A.X) (a n : I) : Prop :=
  pairAction (A := A) (targetModule A r M N) a n =
    FullFreeFunctionPair.targetAction A r M N a n

/-- The transported genuine module retains the full original shifted-cotensor
pair formula; this is derived from the actual module iso and original pair square. -/
theorem target_pair (A : CommMon (DayFunctor I V)) (r : I) (M : V)
    (N : Mod (DayFunctor I V) A.X) (a n : I) :
    pairAction (targetModule A r M N) a n = FullFreeFunctionPair.targetAction A r M N a n := by
  let H := homModule A r M N
  let K := targetModule A r M N
  let e : H.X ≅ K.X := FullFreeFunctionPair.comparison A r M N
  let R : DayFunctor I V ⥤ V := (DayFunctor.equiv I V).functor ⋙ (evaluation I V).obj n
  let en := R.mapIso (X := H.X) (Y := K.X) e
  let : IsIso (e.hom.natTrans.app n) := by
    change IsIso en.hom
    infer_instance
  apply (cancel_epi (A.X.functor.obj a ◁ e.hom.natTrans.app n)).1
  have hM : pairAction H a n ≫ e.hom.natTrans.app (a ⊗ n) =
      (A.X.functor.obj a ◁ e.hom.natTrans.app n) ≫ pairAction K a n := by
    have h := pair_morphism A (comparison A r M N).hom a n
    simpa only [comparison_hom] using h
  have hF : pairAction H a n ≫ e.hom.natTrans.app (a ⊗ n) =
      (A.X.functor.obj a ◁ e.hom.natTrans.app n) ≫
        FullFreeFunctionPair.targetAction A r M N a n := by
    let p : A.X.functor.obj a ⊗ H.X.functor.obj n ⟶ H.X.functor.obj (a ⊗ n) :=
      (DayFunctor.η A.X H.X).app (a, n) ≫ H.mod.smul.natTrans.app (a ⊗ n)
    let φ : H.X.functor.obj (a ⊗ n) ⟶ K.X.functor.obj (a ⊗ n) :=
      e.hom.natTrans.app (a ⊗ n)
    let ψ : H.X.functor.obj n ⟶ K.X.functor.obj n := e.hom.natTrans.app n
    let g : A.X.functor.obj a ⊗ K.X.functor.obj n ⟶ K.X.functor.obj (a ⊗ n) :=
      FullFreeFunctionPair.targetAction A r M N a n
    have h : (DayFunctor.η A.X H.X).app (a, n) ≫
        H.mod.smul.natTrans.app (a ⊗ n) ≫ φ = (A.X.functor.obj a ◁ ψ) ≫ g :=
      FullFreeFunctionPair.pair_square A r M N a n
    change p ≫ φ = (A.X.functor.obj a ◁ ψ) ≫ g
    exact (Category.assoc ((DayFunctor.η A.X H.X).app (a, n))
      (H.mod.smul.natTrans.app (a ⊗ n)) φ).trans h
  exact hM.symm.trans hF

/-- Every full original target pair satisfies that actual generator equation. -/
theorem target_pair_equation (A : CommMon (DayFunctor I V)) (r : I) (M : V)
    (N : Mod (DayFunctor I V) A.X) (a n : I) : targetPairEquation A r M N a n :=
  target_pair A r M N a n

end NativeOmegaRecovery.FullFreeFunctionModuleComparison
