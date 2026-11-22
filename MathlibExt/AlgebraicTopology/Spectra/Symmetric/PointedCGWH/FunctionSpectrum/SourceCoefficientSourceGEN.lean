/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.FreeSourceEvaluation
import MathlibExt.CategoryTheory.Monoidal.Closed.UnitEvaluation
import MathlibExt.CategoryTheory.Monoidal.DayConvolution.FreeFunction.ClosedProjection
import MathlibExt.CategoryTheory.Monoidal.Mod.FreeInternalHom
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.SourceCoefficientFirstSource

/-!
# Original zero-source unit and end equations for the native source generator

The original free-diagram generator maps to the actual Day tensor unit.
The complete original zero-free end inverse is its Day-unit transpose, and
the original module free extension retains the same coefficient contraction
and target module action. These are the unit/end prerequisites of the whole
first-source GEN equation.
-/

set_option autoImplicit false
noncomputable section
universe uI vI uV vV
open CategoryTheory MonoidalCategory Limits
open scoped MonoidalClosed ExternalProduct CategoryTheory.MonObj

namespace NativeOmegaRecovery.FreeFunctionSourceEvaluation

variable {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]
  [MonoidalClosed V] [∀ a b : I, HasCoproductsOfShape (a ⟶ b) V]
  [∀ (F G : I ⥤ V) (c : I), HasEnd
    ((dayConvolutionInternalHomDiagramFunctor F).obj G |>.obj c)]

private abbrev zeroEndSourceDiagram (r : I) (M : V) : DayFunctor I V :=
  .mk ((evaluationLeftAdjoint V r).obj M)

local instance genZeroEndOriginalFreeEnd (r : I) (M : V) (G : I ⥤ V) (n : I) :
    HasEnd (NativeOmegaPreparation.OrdinaryFreeEnd.diagram r M (tensorRight n ⋙ G)) := by
  change HasEnd ((dayConvolutionInternalHomDiagramFunctor
    ((evaluationLeftAdjoint V r).obj M)).obj G |>.obj n)
  infer_instance

/-- Every original zero-free end generator keeps the actual chosen scalar unit,
index unitor and original target map before normalization. -/
theorem original_zero_inverse_end_generator (N : DayFunctor I V) (n a : I)
    (f : (𝟙_ I) ⟶ a) :
    (N.functor.map (ρ_ n).inv ≫
        MonoidalClosed.unitNatIso.hom.app (N.functor.obj (n ⊗ (𝟙_ I)))) ≫
      ((NativeOmegaPreparation.DayFreeEnd.comparison (𝟙_ I) (𝟙_ V) ≪≫
        NativeOmegaPreparation.DayIndexOrder.comparison (𝟙_ I) (𝟙_ V)).app N).inv.natTrans.app n ≫
      end_.π ((dayConvolutionInternalHomDiagramFunctor
          (zeroEndSourceDiagram (𝟙_ I) (𝟙_ V)).functor).obj N.functor |>.obj n) a ≫
      (MonoidalClosed.pre (Sigma.ι (fun _ : (𝟙_ I) ⟶ a => 𝟙_ V) f)).app
        (N.functor.obj (a ⊗ n)) =
    MonoidalClosed.curry
      ((λ_ (N.functor.obj n)).hom ≫ N.functor.map ((λ_ n).inv ≫ (f ▷ n))) := by
  let X := N.functor.obj n
  let T₀ := N.functor.obj ((𝟙_ I) ⊗ n)
  let T₁ := N.functor.obj (n ⊗ (𝟙_ I))
  let G := tensorRight n ⋙ N.functor
  let l := N.functor.map (ρ_ n).inv
  let b := N.functor.map (β_ (𝟙_ I) n).inv
  let k := N.functor.map (f ▷ n)
  let i : (ihom (𝟙_ V)).obj T₀ ⟶
      end_ (NativeOmegaPreparation.OrdinaryFreeEnd.diagram (𝟙_ I) (𝟙_ V) G) :=
    NativeOmegaPreparation.OrdinaryFreeEnd.inverse (𝟙_ I) (𝟙_ V) G
  let π : end_ (NativeOmegaPreparation.OrdinaryFreeEnd.diagram (𝟙_ I) (𝟙_ V) G) ⟶
      (ihom (∐ fun _ : (𝟙_ I) ⟶ a => 𝟙_ V)).obj (N.functor.obj (a ⊗ n)) :=
    end_.π (NativeOmegaPreparation.OrdinaryFreeEnd.diagram (𝟙_ I) (𝟙_ V) G) a
  let g : 𝟙_ V ⟶ ∐ fun _ : (𝟙_ I) ⟶ a => 𝟙_ V :=
    Sigma.ι (fun _ : (𝟙_ I) ⟶ a => 𝟙_ V) f
  let q : (∐ fun _ : (𝟙_ I) ⟶ a => 𝟙_ V) ⊗ ((ihom (𝟙_ V)).obj T₀) ⟶
      N.functor.obj (a ⊗ n) :=
    NativeOmegaPreparation.OrdinaryFreeEnd.parameterExtension
      (𝟙_ I) (𝟙_ V) G ((ihom (𝟙_ V)).obj T₀) ((ihom.ev (𝟙_ V)).app T₀) a
  have hi : i ≫ π = MonoidalClosed.curry q :=
    NativeOmegaPreparation.OrdinaryFreeEnd.inverse_π (𝟙_ I) (𝟙_ V) G a
  have hq : (g ▷ ((ihom (𝟙_ V)).obj T₀)) ≫ q =
      (ihom.ev (𝟙_ V)).app T₀ ≫ k :=
    NativeOmegaPreparation.OrdinaryFreeEnd.parameterExtension_ι
      (𝟙_ I) (𝟙_ V) G ((ihom (𝟙_ V)).obj T₀) ((ihom.ev (𝟙_ V)).app T₀) a f
  have hu : MonoidalClosed.unitNatIso.hom.app T₁ ≫ (ihom (𝟙_ V)).map b =
      b ≫ MonoidalClosed.unitNatIso.hom.app T₀ :=
    (MonoidalClosed.unitNatIso.hom.naturality b).symm
  change (l ≫ MonoidalClosed.unitNatIso.hom.app T₁) ≫
      ((ihom (𝟙_ V)).map b ≫ i) ≫ π ≫
      (MonoidalClosed.pre g).app (N.functor.obj (a ⊗ n)) = _
  simp only [Category.assoc]
  rw [← Category.assoc i π, hi]
  rw [MonoidalClosed.curry_pre_app, hq]
  rw [← Category.assoc (MonoidalClosed.unitNatIso.hom.app T₁)
    ((ihom (𝟙_ V)).map b), hu]
  apply MonoidalClosed.uncurry_injective
  simp only [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry,
    Category.assoc]
  rw [← Category.assoc ((𝟙_ V) ◁ MonoidalClosed.unitNatIso.hom.app T₀)
    ((ihom.ev (𝟙_ V)).app T₀)]
  rw [← MonoidalClosed.uncurry_eq,
    CategoryTheory.EnrichedAdjunctionHom.UnitValue.unitNatIso_hom_uncurry]
  rw [← whiskerLeft_comp_assoc, leftUnitor_naturality_assoc]
  dsimp only [l, b, k]
  simp only [← N.functor.map_comp, Category.assoc]
  rw [braiding_inv_tensorUnit_left]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

end NativeOmegaRecovery.FreeFunctionSourceEvaluation


set_option autoImplicit false
noncomputable section
open CategoryTheory MonoidalCategory Limits
open scoped MonoidalClosed ExternalProduct CategoryTheory.MonObj

namespace NativeOmegaRecovery.FreeFunctionSourceEvaluation

private theorem tensor_zero_hom_ext
    {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
    {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]
    [MonoidalClosed V] [∀ a b : I, HasCoproductsOfShape (a ⟶ b) V]
    (X : V) (a : I) {Z : V}
    {p q : (∐ fun _ : (𝟙_ I) ⟶ a => 𝟙_ V) ⊗ X ⟶ Z}
    (h : ∀ f : (𝟙_ I) ⟶ a,
      (Sigma.ι (fun _ : (𝟙_ I) ⟶ a => 𝟙_ V) f ▷ X) ≫ p =
        (Sigma.ι (fun _ : (𝟙_ I) ⟶ a => 𝟙_ V) f ▷ X) ≫ q) : p = q := by
  apply (cancel_epi (preservesColimitIso (tensorRight X)
    (Discrete.functor (fun _ : (𝟙_ I) ⟶ a => 𝟙_ V))).inv).mp
  apply colimit.hom_ext
  rintro ⟨f⟩
  simp only [ι_preservesColimitIso_inv_assoc]
  exact h f

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

private abbrev sourceDiagram (r : I) (M : V) : DayFunctor I V :=
  .mk ((evaluationLeftAdjoint V r).obj M)

/-- The original free-diagram adjunction maps its zero generator to the actual
chosen Day tensor-unit generator. -/
def originalZeroDiagramUnit : sourceDiagram (𝟙_ I) (𝟙_ V) ⟶ (𝟙_ (DayFunctor I V)) :=
  (DayFunctor.equiv I V).inverse.map
    (((evaluationAdjunctionRight V (𝟙_ I)).homEquiv (𝟙_ V)
      (𝟙_ (DayFunctor I V)).functor).symm
      (LawfulDayConvolutionMonoidalCategoryStruct.unitUnit I V (DayFunctor I V)))

omit [SymmetricCategory I] [BraidedCategory V] [MonoidalClosed V] [∀ (F G : I ⥤ V) (c : I), HasEnd
  ((dayConvolutionInternalHomDiagramFunctor F).obj G |>.obj c)] in
/-- The zero free-diagram unit sends each coproduct injection to the Day-unit
generator followed by its index map. -/
@[reassoc]
theorem original_zero_diagram_unit_ι (a : I) (f : (𝟙_ I) ⟶ a) :
    Sigma.ι (fun _ : (𝟙_ I) ⟶ a => 𝟙_ V) f ≫
      originalZeroDiagramUnit.natTrans.app a =
    LawfulDayConvolutionMonoidalCategoryStruct.unitUnit I V (DayFunctor I V) ≫
      (𝟙_ (DayFunctor I V)).functor.map f := by
  simp only [originalZeroDiagramUnit, evaluationAdjunctionRight,
    Adjunction.mkOfHomEquiv_homEquiv]
  change Sigma.ι (fun _ : (𝟙_ I) ⟶ a => 𝟙_ V) f ≫
    Sigma.desc (fun h : (𝟙_ I) ⟶ a =>
      LawfulDayConvolutionMonoidalCategoryStruct.unitUnit I V (DayFunctor I V) ≫
        (𝟙_ (DayFunctor I V)).functor.map h) = _
  rw [Sigma.ι_comp_desc]

omit [SymmetricCategory I] [BraidedCategory V] [MonoidalClosed V]
  [∀ (F G : I ⥤ V) (c : I), HasEnd
    ((dayConvolutionInternalHomDiagramFunctor F).obj G |>.obj c)] in
/-- The original Day unitor evaluates every actual zero-free generator using
its original index arrow. -/
theorem original_zero_unit_generator_eval (N : DayFunctor I V) (n a : I)
    (f : (𝟙_ I) ⟶ a) :
    (Sigma.ι (fun _ : (𝟙_ I) ⟶ a => 𝟙_ V) f ▷ N.functor.obj n) ≫
      (DayFunctor.η (sourceDiagram (𝟙_ I) (𝟙_ V)) N).app (a, n) ≫
      ((originalZeroDiagramUnit ▷ N) ≫ (λ_ N).hom).natTrans.app (a ⊗ n) =
    (λ_ (N.functor.obj n)).hom ≫ N.functor.map ((λ_ n).inv ≫ (f ▷ n)) := by
  let U := (𝟙_ (DayFunctor I V))
  let P := sourceDiagram (𝟙_ I) (𝟙_ V)
  let u : P ⟶ U := originalZeroDiagramUnit
  let X := N.functor.obj n
  let g : 𝟙_ V ⟶ P.functor.obj a := Sigma.ι (fun _ : (𝟙_ I) ⟶ a => 𝟙_ V) f
  let ηP : P.functor.obj a ⊗ X ⟶ (P ⊗ N).functor.obj (a ⊗ n) :=
    (DayFunctor.η P N).app (a, n)
  let ηU : U.functor.obj a ⊗ X ⟶ (U ⊗ N).functor.obj (a ⊗ n) :=
    (DayFunctor.η U N).app (a, n)
  let ηU₀ : U.functor.obj (𝟙_ I) ⊗ X ⟶ (U ⊗ N).functor.obj ((𝟙_ I) ⊗ n) :=
    (DayFunctor.η U N).app ((𝟙_ I), n)
  let v : (P ⊗ N).functor.obj (a ⊗ n) ⟶ (U ⊗ N).functor.obj (a ⊗ n) :=
    (u ▷ N).natTrans.app (a ⊗ n)
  let l : (U ⊗ N).functor.obj (a ⊗ n) ⟶ N.functor.obj (a ⊗ n) :=
    (λ_ N).hom.natTrans.app (a ⊗ n)
  let l₀ : (U ⊗ N).functor.obj ((𝟙_ I) ⊗ n) ⟶ N.functor.obj ((𝟙_ I) ⊗ n) :=
    (λ_ N).hom.natTrans.app ((𝟙_ I) ⊗ n)
  let _ : DayConvolution U.functor N.functor :=
    LawfulDayConvolutionMonoidalCategoryStruct.convolution I V (DayFunctor I V) U N
  let ν : 𝟙_ V ⟶ U.functor.obj (𝟙_ I) :=
    LawfulDayConvolutionMonoidalCategoryStruct.unitUnit I V (DayFunctor I V)
  have hw : ηP ≫ v = (u.natTrans.app a ▷ X) ≫ ηU :=
    LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit_comp_ι_map_whiskerRight_app
      I V u N a n
  have hg : g ≫ u.natTrans.app a =
      ν ≫ U.functor.map f :=
    original_zero_diagram_unit_ι a f
  have hη : (U.functor.map f ▷ X) ≫ ηU =
      ηU₀ ≫ (U ⊗ N).functor.map (f ▷ n) := by
    have h := DayConvolution.unit_naturality U.functor N.functor f (𝟙 n)
    change (U.functor.map f ⊗ₘ N.functor.map (𝟙 n)) ≫ ηU =
      ηU₀ ≫ (U ⊗ N).functor.map (f ⊗ₘ 𝟙 n) at h
    simpa only [N.functor.map_id, tensorHom_id] using h
  have hUnitorNat : (U ⊗ N).functor.map (f ▷ n) ≫ l = l₀ ≫ N.functor.map (f ▷ n) :=
    (λ_ N).hom.natTrans.naturality (f ▷ n)
  have hunit : (ν ▷ X) ≫
      ηU₀ ≫ l₀ = (λ_ X).hom ≫ N.functor.map (λ_ n).inv :=
    LawfulDayConvolutionMonoidalCategoryStruct.leftUnitor_hom_unit_app V N n
  change (g ▷ X) ≫ ηP ≫ v ≫ l = _
  rw [reassoc_of% hw, ← comp_whiskerRight_assoc, hg]
  simp only [comp_whiskerRight, Category.assoc]
  rw [reassoc_of% hη, hUnitorNat, reassoc_of% hunit]
  simp only [X, Functor.map_comp]

/-- The same full zero-free inverse comparison is the original Day unit
transpose, retaining the actual chosen scalar and index unit components. -/
theorem original_zero_end_inverse_unit (N : DayFunctor I V) (n : I) :
    (N.functor.map (ρ_ n).inv ≫
        MonoidalClosed.unitNatIso.hom.app (N.functor.obj (n ⊗ (𝟙_ I)))) ≫
      ((NativeOmegaPreparation.DayFreeEnd.comparison (𝟙_ I) (𝟙_ V) ≪≫
        NativeOmegaPreparation.DayIndexOrder.comparison (𝟙_ I) (𝟙_ V)).app N).inv.natTrans.app n =
    (MonoidalClosed.curry ((originalZeroDiagramUnit ▷ N) ≫ (λ_ N).hom)).natTrans.app n := by
  let P := sourceDiagram (𝟙_ I) (𝟙_ V)
  let q : P ⊗ N ⟶ N := (originalZeroDiagramUnit ▷ N) ≫ (λ_ N).hom
  apply end_.hom_ext
  intro a
  let π : end_ ((dayConvolutionInternalHomDiagramFunctor P.functor).obj
      N.functor |>.obj n) ⟶
      (ihom (∐ fun _ : (𝟙_ I) ⟶ a => 𝟙_ V)).obj (N.functor.obj (a ⊗ n)) :=
    end_.π ((dayConvolutionInternalHomDiagramFunctor P.functor).obj
      N.functor |>.obj n) a
  let t : (∐ fun _ : (𝟙_ I) ⟶ a => 𝟙_ V) ⊗ N.functor.obj n ⟶
      N.functor.obj (a ⊗ n) :=
    (DayFunctor.η P N).app (a, n) ≫ q.natTrans.app (a ⊗ n)
  have hπ := NativeOmegaPreparation.DayClosedProjection.curry_π P N N q n a
  change (MonoidalClosed.curry q).natTrans.app n ≫ π =
    MonoidalClosed.curry t at hπ
  apply MonoidalClosed.uncurry_injective
  apply tensor_zero_hom_ext
  intro f
  let v₀ : N.functor.obj n ⟶
      (ihom (𝟙_ V)).obj (N.functor.obj (n ⊗ (𝟙_ I))) :=
    N.functor.map (ρ_ n).inv ≫
      MonoidalClosed.unitNatIso.hom.app (N.functor.obj (n ⊗ (𝟙_ I)))
  let d : (ihom (𝟙_ V)).obj (N.functor.obj (n ⊗ (𝟙_ I))) ⟶ end_
      ((dayConvolutionInternalHomDiagramFunctor P.functor).obj N.functor |>.obj n) :=
    ((NativeOmegaPreparation.DayFreeEnd.comparison (𝟙_ I) (𝟙_ V) ≪≫
      NativeOmegaPreparation.DayIndexOrder.comparison (𝟙_ I) (𝟙_ V)).app N).inv.natTrans.app n
  let v : N.functor.obj n ⟶ end_
      ((dayConvolutionInternalHomDiagramFunctor P.functor).obj N.functor |>.obj n) := v₀ ≫ d
  let g : 𝟙_ V ⟶ ∐ fun _ : (𝟙_ I) ⟶ a => 𝟙_ V := Sigma.ι (fun _ : (𝟙_ I) ⟶ a => 𝟙_ V) f
  have hBase : (v ≫ π) ≫ (MonoidalClosed.pre g).app (N.functor.obj (a ⊗ n)) =
      MonoidalClosed.curry ((λ_ (N.functor.obj n)).hom ≫
        N.functor.map ((λ_ n).inv ≫ (f ▷ n))) := by
    have h := original_zero_inverse_end_generator N n a f
    exact (Category.assoc v π ((MonoidalClosed.pre g).app (N.functor.obj (a ⊗ n)))).trans
      ((Category.assoc v₀ d
        (π ≫ (MonoidalClosed.pre g).app (N.functor.obj (a ⊗ n)))).trans h)
  have hL := congrArg MonoidalClosed.uncurry hBase
  rw [MonoidalClosed.uncurry_pre_app, MonoidalClosed.uncurry_curry] at hL
  have hR : (Sigma.ι (fun _ : (𝟙_ I) ⟶ a => 𝟙_ V) f ▷ N.functor.obj n) ≫
      MonoidalClosed.uncurry ((MonoidalClosed.curry q).natTrans.app n ≫ π) =
      (λ_ (N.functor.obj n)).hom ≫ N.functor.map ((λ_ n).inv ≫ (f ▷ n)) := by
    rw [hπ, MonoidalClosed.uncurry_curry]
    exact original_zero_unit_generator_eval N n a f
  exact hL.trans hR.symm

end NativeOmegaRecovery.FreeFunctionSourceEvaluation


set_option autoImplicit false
noncomputable section
open CategoryTheory MonoidalCategory Limits
open scoped MonoidalClosed CategoryTheory.MonObj
universe uC vC

namespace NativeOmegaRecovery.OriginalFreeUnitExtension

variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [BraidedCategory C]
  [MonoidalClosed C] [HasEqualizers C] (A : CommMon C)

omit [MonoidalClosed C] [HasEqualizers C] in
/-- The original parameterized free extension of a given actual unit map is
the full original target module action after its original coefficient unitor. -/
theorem parameterExtension_unit (P : C) (e : P ⟶ (𝟙_ C)) (N : Mod C A.X) :
    Mod.FreeInternalHom.parameterExtension A P N.X N ((e ▷ N.X) ≫ (λ_ N.X).hom) =
      (((A.X ◁ e) ≫ (ρ_ A.X).hom) ▷ N.X) ≫ N.mod.smul := by
  have ht : (α_ A.X (𝟙_ C) N.X).hom ≫ (A.X ◁ (λ_ N.X).hom) =
      (ρ_ A.X).hom ▷ N.X := by
    monoidal
  simp only [Mod.FreeInternalHom.parameterExtension, whiskerLeft_comp,
    comp_whiskerRight, Category.assoc]
  rw [← associator_naturality_middle_assoc]
  rw [← Category.assoc (α_ A.X (𝟙_ C) N.X).hom (A.X ◁ (λ_ N.X).hom), ht]

/-- The given whole free inverse retains the actual equalizer inclusion and
becomes the transpose of the same full module action at the original unit map. -/
theorem inverse_unit_ι (P : C) (e : P ⟶ (𝟙_ C)) (N : Mod C A.X) :
    MonoidalClosed.curry ((e ▷ N.X) ≫ (λ_ N.X).hom) ≫
      Mod.FreeInternalHom.inverse A P N ≫
      Mod.internalHomι A ((Mod.free A.X).obj P) N =
    MonoidalClosed.curry ((((A.X ◁ e) ≫ (ρ_ A.X).hom) ▷ N.X) ≫ N.mod.smul) := by
  rw [Mod.FreeInternalHom.inverse_ι]
  change MonoidalClosed.curry ((e ▷ N.X) ≫ (λ_ N.X).hom) ≫
      MonoidalClosed.curry
        (Mod.FreeInternalHom.parameterExtension A P ((ihom P).obj N.X) N ((ihom.ev P).app N.X)) =
    MonoidalClosed.curry ((((A.X ◁ e) ≫ (ρ_ A.X).hom) ▷ N.X) ≫ N.mod.smul)
  rw [← MonoidalClosed.curry_natural_left]
  rw [Mod.FreeInternalHom.parameterExtension_precompose]
  rw [MonoidalClosed.whiskerLeft_curry_ihom_ev_app]
  exact congrArg MonoidalClosed.curry (parameterExtension_unit A P e N)

end NativeOmegaRecovery.OriginalFreeUnitExtension


set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory Limits
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed CategoryTheory.MonObj

namespace NativeOmegaRecovery.NativeSymmetricSourceGEN

private abbrev I := Operad.SmallFinBijGroupoid
private abbrev V := PointedCGWH.{u, v}
private abbrev S := PointedCGWH.sphereSequence.{u, v}
private abbrev A := PointedCGWH.sphereSequenceCommMon.{u, v}
private abbrev Sequence := PointedCGWH.SymmetricSequence.{u, v}
private abbrev P₀ : Sequence.{u, v} :=
  .mk ((evaluationLeftAdjoint V.{u, v} (𝟙_ I)).obj (𝟙_ V.{u, v}))

attribute [local instance] Operad.SmallFinBijGroupoid.instMonoidalCategory
  Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  PointedCGWH.EnrichedMapping.hasSmallLimits
  NativeOmegaPreparation.SymmetricFunction.sequenceCoequalizers
  NativeOmegaPreparation.SymmetricFunction.sequenceEqualizers
  NativeOmegaPreparation.SymmetricFunction.sequenceClosed
  PointedCGWH.originalSymmetricSequenceMonoidal
  PointedCGWH.originalSymmetricSequenceBraided PointedCGWH.originalSymmetricSequenceSymmetric
  PointedCGWH.SymmetricFunctionFactories.indexedCoproducts
  PointedCGWH.SymmetricFunctionFactories.tensorExtensions
  PointedCGWH.SymmetricFunctionFactories.unitExtensions
  PointedCGWH.SymmetricFunctionFactories.tensorLeftTensorShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightTensorShape
  PointedCGWH.SymmetricFunctionFactories.tensorLeftUnitShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightUnitShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightMixedUnitShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightTripleShape
  PointedCGWH.SymmetricFunctionFactories.internalHomEnds

open PointedCGWH.SymmetricModulePresentation
open NativeSymmetricFreeSource

/-- The actual original free-forgetful adjunction contracts the genuine zero-free
module to the original regular sphere module using the actual Day unit. -/
def actualZeroFreeContraction :
    freeModule.{u, v} (𝟙_ I) (𝟙_ V.{u, v}) ⟶ Mod.regular S.{u, v} :=
  ((Mod.freeForgetAdjunction S.{u, v}).homEquiv P₀.{u, v} (Mod.regular S.{u, v})).symm
    (FreeFunctionSourceEvaluation.originalZeroDiagramUnit ≫
      (η : 𝟙_ Sequence.{u, v} ⟶ S.{u, v}))

/-- Its entire original underlying map is the actual coefficient right-unitor
contraction, with no change to either original module object. -/
theorem actualZeroFreeContraction_hom :
    actualZeroFreeContraction.{u, v}.hom =
      (S.{u, v} ◁ FreeFunctionSourceEvaluation.originalZeroDiagramUnit) ≫ (ρ_ S.{u, v}).hom := by
  let u₀ : P₀.{u, v} ⟶ (𝟙_ Sequence.{u, v}) :=
    FreeFunctionSourceEvaluation.originalZeroDiagramUnit
  let η₀ : (𝟙_ Sequence.{u, v}) ⟶ S.{u, v} := η
  let μ₀ : S.{u, v} ⊗ S.{u, v} ⟶ S.{u, v} := μ
  have hRaw := Mod.freeForgetAdjunction_homEquiv_symm_apply_hom S.{u, v}
    (Mod.regular S.{u, v}) (u₀ ≫ η₀)
  change actualZeroFreeContraction.{u, v}.hom =
    𝟙 (S.{u, v} ⊗ P₀.{u, v}) ≫ (S.{u, v} ◁ (u₀ ≫ η₀)) ≫ μ₀ at hRaw
  have hTensor : S.{u, v} ◁ (u₀ ≫ η₀) =
      (S.{u, v} ◁ u₀) ≫ (S.{u, v} ◁ η₀) := whiskerLeft_comp _ _ _
  have hUnit : (S.{u, v} ◁ η₀) ≫ μ₀ = (ρ_ S.{u, v}).hom := MonObj.mul_one S.{u, v}
  have hValue : 𝟙 (S.{u, v} ⊗ P₀.{u, v}) ≫ (S.{u, v} ◁ (u₀ ≫ η₀)) ≫ μ₀ =
      (S.{u, v} ◁ u₀) ≫ (ρ_ S.{u, v}).hom := by
    rw [Category.id_comp, hTensor, Category.assoc, hUnit]
  exact hRaw.trans hValue

/-- The SAME complete Day free adjunction evaluates this contraction at the
original sphere coefficient unit. -/
theorem actualZeroFreeContraction_adjunct :
    (Mod.dayFreeAtEvaluationAdjunction S.{u, v} (𝟙_ I)).homEquiv
      (𝟙_ V.{u, v}) (Mod.regular S.{u, v}) actualZeroFreeContraction.{u, v} =
    PointedCGWH.sphereCopowerLaxData.{u, v}.epsilon := by
  let U := (𝟙_ Sequence.{u, v})
  let u₀ : P₀.{u, v} ⟶ U := FreeFunctionSourceEvaluation.originalZeroDiagramUnit
  let η₀ : U ⟶ S.{u, v} := η
  let q : P₀.{u, v} ⟶ S.{u, v} := u₀ ≫ η₀
  let ι₀ : 𝟙_ V.{u, v} ⟶ P₀.{u, v}.functor.obj (𝟙_ I) :=
    Sigma.ι (fun _ : (𝟙_ I) ⟶ (𝟙_ I) => 𝟙_ V.{u, v}) (𝟙 (𝟙_ I))
  let u₁ : P₀.{u, v}.functor.obj (𝟙_ I) ⟶ U.functor.obj (𝟙_ I) :=
    u₀.natTrans.app (𝟙_ I)
  let η₁ : U.functor.obj (𝟙_ I) ⟶ S.{u, v}.functor.obj (𝟙_ I) :=
    η₀.natTrans.app (𝟙_ I)
  let ν : 𝟙_ V.{u, v} ⟶ U.functor.obj (𝟙_ I) :=
    LawfulDayConvolutionMonoidalCategoryStruct.unitUnit I V.{u, v} (DayFunctor I V.{u, v})
  have hq : (Mod.freeForgetAdjunction S.{u, v}).homEquiv P₀.{u, v}
      (Mod.regular S.{u, v}) actualZeroFreeContraction.{u, v} = q :=
    Equiv.apply_symm_apply _ q
  have hUnit := FreeFunctionSourceEvaluation.original_zero_diagram_unit_ι
    (I := I) (V := V.{u, v}) (𝟙_ I) (𝟙 (𝟙_ I))
  change ι₀ ≫ u₁ = ν ≫ U.functor.map (𝟙 (𝟙_ I)) at hUnit
  have hUnit' : ι₀ ≫ u₁ = ν :=
    hUnit.trans ((congrArg (fun z => ν ≫ z) (U.functor.map_id (𝟙_ I))).trans (Category.comp_id ν))
  have hEpsilon : ν ≫ η₁ = PointedCGWH.sphereCopowerLaxData.{u, v}.epsilon :=
    PointedCGWH.sphereCopowerLaxData_one.{u, v}
  rw [Mod.dayFreeAtEvaluationAdjunction_homEquiv]
  change ι₀ ≫ (((Mod.freeForgetAdjunction S.{u, v}).homEquiv P₀.{u, v}
    (Mod.regular S.{u, v}) actualZeroFreeContraction.{u, v}).natTrans.app (𝟙_ I)) = _
  have hValue := congrArg
    (fun z : P₀.{u, v} ⟶ S.{u, v} => ι₀ ≫ z.natTrans.app (𝟙_ I)) hq
  change ι₀ ≫ (((Mod.freeForgetAdjunction S.{u, v}).homEquiv P₀.{u, v}
    (Mod.regular S.{u, v}) actualZeroFreeContraction.{u, v}).natTrans.app (𝟙_ I)) =
      ι₀ ≫ u₁ ≫ η₁ at hValue
  exact hValue.trans ((Category.assoc ι₀ u₁ η₁).symm.trans
    ((congrArg (fun z => z ≫ η₁) hUnit').trans hEpsilon))

/-- Both original free maps retain the full native extension of that same sphere unit. -/
theorem actualZeroFreeContraction_native_extend :
    (NativeOmegaPreparation.SymmetricNativeFree.operatorComparison.{u, v} (𝟙_ I)).inv.app
        (𝟙_ V.{u, v}) ≫ moduleToOperator.{u, v}.map actualZeroFreeContraction.{u, v} =
      Free.extend (PointedCGWH.symmetricOperatorObj.{u, v} (𝟙_ I)) (𝟙_ V.{u, v})
        (toOperatorFunctor (Mod.regular S.{u, v}))
        PointedCGWH.sphereCopowerLaxData.{u, v}.epsilon := by
  have hp := FreeAdjunctionSource.point moduleOperatorEquivalence.{u, v}
    (PointedCGWH.symmetricOperatorObj.{u, v} (𝟙_ I))
    (Mod.dayFreeAt S.{u, v} (𝟙_ I)) (Mod.dayEvaluation S.{u, v} (𝟙_ I))
    (Mod.dayFreeAtEvaluationAdjunction S.{u, v} (𝟙_ I))
    (NativeOmegaPreparation.SymmetricNativeFree.evaluationIso.{u, v} (𝟙_ I))
    actualZeroFreeContraction.{u, v}
  change (Mod.dayFreeAtEvaluationAdjunction S.{u, v} (𝟙_ I)).homEquiv
      (𝟙_ V.{u, v}) (Mod.regular S.{u, v}) actualZeroFreeContraction.{u, v} ≫ 𝟙 _ =
    Free.evaluate (PointedCGWH.symmetricOperatorObj.{u, v} (𝟙_ I)) (𝟙_ V.{u, v})
      (toOperatorFunctor (Mod.regular S.{u, v}))
      ((NativeOmegaPreparation.SymmetricNativeFree.operatorComparison.{u, v} (𝟙_ I)).inv.app
        (𝟙_ V.{u, v}) ≫ moduleToOperator.{u, v}.map actualZeroFreeContraction.{u, v}) at hp
  rw [Category.comp_id, actualZeroFreeContraction_adjunct] at hp
  have h := Free.extend_evaluate (PointedCGWH.symmetricOperatorObj.{u, v} (𝟙_ I))
    (𝟙_ V.{u, v}) (toOperatorFunctor (Mod.regular S.{u, v}))
    ((NativeOmegaPreparation.SymmetricNativeFree.operatorComparison.{u, v} (𝟙_ I)).inv.app
      (𝟙_ V.{u, v}) ≫ moduleToOperator.{u, v}.map actualZeroFreeContraction.{u, v})
  rw [← hp] at h
  exact h.symm

/-- The same original whole zero contraction equation has its small native
argument aliases reduced before either original inverse component is selected. -/
theorem actualZeroFreeContraction_native_extend_public :
    dsimp% only [I, V, S] (type_of% actualZeroFreeContraction_native_extend.{u, v}) := by
  have h := actualZeroFreeContraction_native_extend.{u, v}
  dsimp only [I, V, S] at h
  exact h

open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK

/-- The same full native scalar extension retains every original coefficient
input and the actual whole operator action. -/
theorem raw_unit_extension_generator {J : Type} [EnrichedCategory V.{u, v} J]
    (a b : J) (K : V.{u, v}) (D : K ⟶ (a ⟶[V.{u, v}] b))
    (X : EnrichedFunctorCat V.{u, v} J) (q : (𝟙_ V.{u, v}) ⟶ X.toEnrichedFunctor.obj a) :
    D ≫ (λ_ (a ⟶[V.{u, v}] b)).inv ≫
      component (Free.extend a (𝟙_ V.{u, v}) X q) b =
    (ρ_ K).inv ≫ (K ◁ q) ≫ CurrentFree.action a b K D X := by
  let Y := X.toEnrichedFunctor.obj a
  let H := (a ⟶[V.{u, v}] b)
  let p := MonoidalClosed.uncurry (X.toEnrichedFunctor.map a b)
  have hL : D ≫ (λ_ H).inv ≫ (q ▷ H) ≫ p =
      (λ_ K).inv ≫ (q ▷ K) ≫ (Y ◁ D) ≫ p := by
    rw [reassoc_of% leftUnitor_inv_naturality D, whisker_exchange_assoc]
  have hR : (ρ_ K).inv ≫ (K ◁ q) ≫ (D ▷ Y) ≫ (β_ Y H).inv ≫ p =
      (λ_ K).inv ≫ (q ▷ K) ≫ (Y ◁ D) ≫ p := by
    rw [reassoc_of% BraidedCategory.braiding_inv_naturality_left D Y]
    rw [reassoc_of% BraidedCategory.braiding_inv_naturality_right K q]
    rw [braiding_inv_tensorUnit_left]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [Free.extend_component]
  simpa only [Free.extensionComponent, tensorHom_id, CurrentFree.action, Y, H, p,
    Category.assoc] using hL.trans hR.symm

end NativeOmegaRecovery.NativeSymmetricSourceGEN


namespace NativeOmegaRecovery.OriginalDaySourceData

variable {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [MonoidalCategory (DayFunctor I V)]
  [∀ a b : I, HasCoproductsOfShape (a ⟶ b) V]

omit [∀ a b : I, HasCoproductsOfShape (a ⟶ b) V] in
/-- Equal coefficient objects and heterogeneously equal monoid data identify
their complete module types. -/
theorem moduleType_of_original_data (P Q : DayFunctor I V)
    (m : MonObj P) (m' : MonObj Q) (hP : P = Q) (hm : HEq m m') :
    (letI : MonObj P := m; Mod (DayFunctor I V) P) =
      (letI : MonObj Q := m'; Mod (DayFunctor I V) Q) := by
  cases hP
  cases hm
  rfl

/-- The Day free-module functors agree heterogeneously under the stated
coefficient object and monoid identifications. -/
theorem dayFree_of_original_data (P Q : DayFunctor I V)
    (m : MonObj P) (m' : MonObj Q) (hP : P = Q) (hm : HEq m m') (r : I) :
    HEq (letI : MonObj P := m; Mod.dayFreeAt P r)
      (letI : MonObj Q := m'; Mod.dayFreeAt Q r) := by
  cases hP
  cases hm
  rfl

/-- The Day free/evaluation adjunctions agree heterogeneously under the same
coefficient object and monoid identifications. -/
theorem dayAdjunction_of_original_data (P Q : DayFunctor I V)
    (m : MonObj P) (m' : MonObj Q) (hP : P = Q) (hm : HEq m m') (r : I) :
    HEq (letI : MonObj P := m; Mod.dayFreeAtEvaluationAdjunction P r)
      (letI : MonObj Q := m'; Mod.dayFreeAtEvaluationAdjunction Q r) := by
  cases hP
  cases hm
  rfl

end NativeOmegaRecovery.OriginalDaySourceData

namespace NativeOmegaRecovery.NativeSymmetricSourceGEN.MonoidReadbacks

private abbrev I := Operad.SmallFinBijGroupoid
private abbrev V := PointedCGWH.{u, v}
private abbrev S := PointedCGWH.sphereSequence.{u, v}
private abbrev A := PointedCGWH.sphereSequenceCommMon.{u, v}
private abbrev Sequence := PointedCGWH.SymmetricSequence.{u, v}

attribute [local instance] Operad.SmallFinBijGroupoid.instMonoidalCategory
  Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  PointedCGWH.EnrichedMapping.hasSmallLimits
  NativeOmegaPreparation.SymmetricFunction.sequenceCoequalizers
  NativeOmegaPreparation.SymmetricFunction.sequenceEqualizers
  NativeOmegaPreparation.SymmetricFunction.sequenceClosed
  PointedCGWH.originalSymmetricSequenceMonoidal
  PointedCGWH.originalSymmetricSequenceBraided PointedCGWH.originalSymmetricSequenceSymmetric
  PointedCGWH.SymmetricFunctionFactories.indexedCoproducts

open NativeOmegaRecovery.NativeScalarCoefficient
open NativeOmegaRecovery.NativeSymmetricFreeFunction

/-- The complete actual monoid identifies the entire original module type. -/
theorem original_module_type :
    (letI : MonObj A.{u, v}.X := A.{u, v}.mon; Mod Sequence.{u, v} A.{u, v}.X) =
      OriginalModule.{u, v} :=
  OriginalDaySourceData.moduleType_of_original_data A.{u, v}.X S.{u, v}
    A.{u, v}.mon PointedCGWH.sphereSequenceMonObj.{u, v}
    sphereCoefficient_obj_eq.{u, v} (heq_of_eq sphereCoefficient_mon_eq.{u, v})

/-- Both complete original free-at-index functors retain all source values and maps. -/
theorem original_day_free_functor (r : I) :
    HEq (letI : MonObj A.{u, v}.X := A.{u, v}.mon; Mod.dayFreeAt A.{u, v}.X r)
      (Mod.dayFreeAt S.{u, v} r) :=
  OriginalDaySourceData.dayFree_of_original_data A.{u, v}.X S.{u, v}
    A.{u, v}.mon PointedCGWH.sphereSequenceMonObj.{u, v}
    sphereCoefficient_obj_eq.{u, v} (heq_of_eq sphereCoefficient_mon_eq.{u, v}) r

/-- Unit, counit, Hom equivalence and triangles are the same complete original adjunction. -/
theorem original_day_free_adjunction (r : I) :
    HEq (letI : MonObj A.{u, v}.X := A.{u, v}.mon; Mod.dayFreeAtEvaluationAdjunction A.{u, v}.X r)
      (Mod.dayFreeAtEvaluationAdjunction S.{u, v} r) :=
  OriginalDaySourceData.dayAdjunction_of_original_data A.{u, v}.X S.{u, v}
    A.{u, v}.mon PointedCGWH.sphereSequenceMonObj.{u, v}
    sphereCoefficient_obj_eq.{u, v} (heq_of_eq sphereCoefficient_mon_eq.{u, v}) r


end NativeOmegaRecovery.NativeSymmetricSourceGEN.MonoidReadbacks



set_option autoImplicit false
noncomputable section
open CategoryTheory MonoidalCategory Limits
open scoped MonoidalClosed ExternalProduct CategoryTheory.MonObj

private theorem compose_original_source_word
    {W : Type uV} [Category.{vV} W] {X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ X₈ : W}
    (z : X₀ ⟶ X₁) (d : X₁ ⟶ X₂) (i : X₂ ⟶ X₃)
    (p : X₃ ⟶ X₄) (c : X₄ ⟶ X₈) (j : X₃ ⟶ X₅)
    (π : X₅ ⟶ X₆) (g : X₆ ⟶ X₇) (b : X₇ ⟶ X₈)
    (r : X₀ ⟶ X₂) (k : X₀ ⟶ X₅) (a : X₀ ⟶ X₇)
    (hp : p ≫ c = j ≫ π ≫ g ≫ b) (hz : z ≫ d = r)
    (hu : r ≫ i ≫ j = k) (hc : k ≫ π ≫ g = a) :
    z ≫ (d ≫ i) ≫ (p ≫ c) = a ≫ b := by
  rw [hp]
  simp only [Category.assoc]
  rw [← Category.assoc z d, hz]
  rw [reassoc_of% hu, reassoc_of% hc]

private theorem scalar_curry_projection_pre
    {W : Type uV} [Category.{vV} W] [MonoidalCategory W] [MonoidalClosed W]
    {X Y P H T : W} {c : X ⟶ H} {π : H ⟶ (ihom Y).obj T} {g : P ⟶ Y}
    {t : Y ⊗ X ⟶ T} {a : P ⊗ X ⟶ T}
    (hπ : c ≫ π = MonoidalClosed.curry t) (hg : (g ▷ X) ≫ t = a) :
    c ≫ π ≫ (MonoidalClosed.pre g).app T = MonoidalClosed.curry a := by
  exact (Category.assoc c π ((MonoidalClosed.pre g).app T)).symm.trans
    ((congrArg (fun w => w ≫ (MonoidalClosed.pre g).app T) hπ).trans
      ((MonoidalClosed.curry_pre_app g t).trans (congrArg MonoidalClosed.curry hg)))

private theorem source_chain_associativity
    {W : Type uV} [Category.{vV} W] {X₀ X₁ X₂ X₃ X₄ : W}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃) (d : X₃ ⟶ X₄) :
    (a ≫ b ≫ c) ≫ d = a ≫ b ≫ c ≫ d :=
  (Category.assoc a (b ≫ c) d).trans
    (congrArg (fun w => a ≫ w) (Category.assoc b c d))

namespace NativeOmegaRecovery.FreeFunctionSourceEvaluation

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
  [HasEqualizers (DayFunctor I V)] [HasCoequalizers (DayFunctor I V)]
  (A : CommMon (DayFunctor I V))

omit [HasCoequalizers (DayFunctor I V)] in
/-- The inverse component of the actual full free-source comparison is the
original Day inverse followed by the actual module free extension. -/
theorem original_free_source_comparison_inverse_component (r : I) (M : V)
    (N : Mod (DayFunctor I V) A.X) (n : I) :
    (FullFreeFunctionPair.comparison A r M N).inv.natTrans.app n =
      ((NativeOmegaPreparation.DayFreeEnd.comparison r M ≪≫
        NativeOmegaPreparation.DayIndexOrder.comparison r M).app N.X).inv.natTrans.app n ≫
      (Mod.FreeInternalHom.inverse A (sourceDiagram r M) N).natTrans.app n := by
  have h : (FullFreeFunctionPair.comparison A r M N).inv =
      ((NativeOmegaPreparation.DayFreeEnd.comparison r M ≪≫
        NativeOmegaPreparation.DayIndexOrder.comparison r M).app N.X).inv ≫
      Mod.FreeInternalHom.inverse A (sourceDiagram r M) N := by
    change (Mod.FreeInternalHom.iso A (sourceDiagram r M) N ≪≫
      ((NativeOmegaPreparation.DayFreeEnd.comparison r M ≪≫
        NativeOmegaPreparation.DayIndexOrder.comparison r M).app N.X)).inv = _
    exact Iso.trans_inv (Mod.FreeInternalHom.iso A (sourceDiagram r M) N)
      ((NativeOmegaPreparation.DayFreeEnd.comparison r M ≪≫
        NativeOmegaPreparation.DayIndexOrder.comparison r M).app N.X)
  have h' := congrArg (fun w => w.natTrans.app n) h
  have hDot := DayFunctor.comp_natTrans
    ((NativeOmegaPreparation.DayFreeEnd.comparison r M ≪≫
      NativeOmegaPreparation.DayIndexOrder.comparison r M).app N.X).inv
    (Mod.FreeInternalHom.inverse A (sourceDiagram r M) N)
  have hApp := congrArg (fun w => w.app n) hDot
  have hComp : (((NativeOmegaPreparation.DayFreeEnd.comparison r M ≪≫
        NativeOmegaPreparation.DayIndexOrder.comparison r M).app N.X).inv ≫
      Mod.FreeInternalHom.inverse A (sourceDiagram r M) N).natTrans.app n =
      ((NativeOmegaPreparation.DayFreeEnd.comparison r M ≪≫
        NativeOmegaPreparation.DayIndexOrder.comparison r M).app N.X).inv.natTrans.app n ≫
      (Mod.FreeInternalHom.inverse A (sourceDiagram r M) N).natTrans.app n := by
    simpa only [NatTrans.comp_app] using hApp
  exact h'.trans hComp

/-- The module tensor structure for the given commutative Day coefficient. -/
local instance genZeroModuleMonoidal : MonoidalCategory (Mod (DayFunctor I V) A.X) :=
  Mod.instMonoidalCategory A
/-- The module internal Hom structure for the given commutative Day coefficient. -/
local instance genZeroModuleClosed : MonoidalClosed (Mod (DayFunctor I V) A.X) :=
  Mod.instMonoidalClosed A

omit [SymmetricCategory I] [BraidedCategory V]
  [∀ (a b : I), HasCoproductsOfShape (a ⟶ b) V]
  [∀ (F G : I ⥤ V) (c : I), HasEnd (((dayConvolutionInternalHomDiagramFunctor F).obj G).obj c)]
  [HasEqualizers (DayFunctor I V)] [HasCoequalizers (DayFunctor I V)]
  [MonoidalClosed V] in
/-- Original Day tensor naturality retains an entire parameter and action arrow. -/
theorem original_day_generator_action
    (P Q R : DayFunctor I V) (e : P ⟶ Q) (α : Q ⊗ R ⟶ R)
    (s n : I) (K : V) (g : K ⟶ P.functor.obj s) :
    (g ▷ R.functor.obj n) ≫ (DayFunctor.η P R).app (s, n) ≫
      ((e ▷ R) ≫ α).natTrans.app (s ⊗ n) =
    ((g ≫ e.natTrans.app s) ▷ R.functor.obj n) ≫
      (DayFunctor.η Q R).app (s, n) ≫ α.natTrans.app (s ⊗ n) := by
  let X := R.functor.obj n
  let ηP : P.functor.obj s ⊗ X ⟶ (P ⊗ R).functor.obj (s ⊗ n) :=
    (DayFunctor.η P R).app (s, n)
  let ηQ : Q.functor.obj s ⊗ X ⟶ (Q ⊗ R).functor.obj (s ⊗ n) :=
    (DayFunctor.η Q R).app (s, n)
  let e₀ : (P ⊗ R).functor.obj (s ⊗ n) ⟶ (Q ⊗ R).functor.obj (s ⊗ n) :=
    (e ▷ R).natTrans.app (s ⊗ n)
  let a₀ : (Q ⊗ R).functor.obj (s ⊗ n) ⟶ R.functor.obj (s ⊗ n) :=
    α.natTrans.app (s ⊗ n)
  have hw : ηP ≫ e₀ = (e.natTrans.app s ▷ X) ≫ ηQ :=
    LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit_comp_ι_map_whiskerRight_app
      I V e R s n
  change (g ▷ X) ≫ ηP ≫ e₀ ≫ a₀ = ((g ≫ e.natTrans.app s) ▷ X) ≫ ηQ ≫ a₀
  rw [reassoc_of% hw]
  exact (Category.assoc (g ▷ X) (e.natTrans.app s ▷ X) (ηQ ≫ a₀)).symm.trans
    (congrArg (fun z : K ⊗ X ⟶ Q.functor.obj s ⊗ X => z ≫ ηQ ≫ a₀)
      (comp_whiskerRight g (e.natTrans.app s) X).symm)

/-- The complete original source word at its actual module and scalar endpoints. -/
def originalZeroSourceWord (s : I) (M' : V)
    (f : (Mod.free A.X).obj (sourceDiagram s M') ⟶
      (Mod.free A.X).obj (sourceDiagram (𝟙_ I) (𝟙_ V)))
    (N : Mod (DayFunctor I V) A.X) (n : I) :
    N.X.functor.obj n ⟶ (ihom M').obj (N.X.functor.obj (n ⊗ s)) :=
    (N.X.functor.map (ρ_ n).inv ≫
        MonoidalClosed.unitNatIso.hom.app (N.X.functor.obj (n ⊗ (𝟙_ I)))) ≫
      (FullFreeFunctionPair.comparison A (𝟙_ I) (𝟙_ V) N).inv.natTrans.app n ≫
      ((MonoidalClosed.pre f).app N).hom.natTrans.app n ≫
      (FullFreeFunctionPair.comparison A s M' N).hom.natTrans.app n

/-- The complete original module action transpose on the same original generator. -/
def originalZeroSourceAction (s : I) (M' : V)
    (f : (Mod.free A.X).obj (sourceDiagram s M') ⟶
      (Mod.free A.X).obj (sourceDiagram (𝟙_ I) (𝟙_ V)))
    (N : Mod (DayFunctor I V) A.X) (n : I) :
    N.X.functor.obj n ⟶ (ihom M').obj (N.X.functor.obj (n ⊗ s)) :=
    MonoidalClosed.curry
      (((Sigma.ι (fun _ : s ⟶ s => M') (𝟙 s) ≫
            ((Mod.freeForgetAdjunction A.X).unit.app (sourceDiagram s M')).natTrans.app s ≫
            f.hom.natTrans.app s ≫
            ((A.X ◁ originalZeroDiagramUnit) ≫ (ρ_ A.X).hom).natTrans.app s) ▷
          N.X.functor.obj n) ≫
        (DayFunctor.η A.X N.X).app (s, n) ≫ N.mod.smul.natTrans.app (s ⊗ n)) ≫
      (ihom M').map (N.X.functor.map (β_ s n).hom)

/-- The original full module source projection at the actual zero-free source. -/
private theorem original_zero_parameter_projection (s : I) (M' : V)
    (f : (Mod.free A.X).obj (sourceDiagram s M') ⟶
      (Mod.free A.X).obj (sourceDiagram (𝟙_ I) (𝟙_ V)))
    (N : Mod (DayFunctor I V) A.X) (n : I) :
    ((MonoidalClosed.pre f).app N).hom.natTrans.app n ≫
      (FullFreeFunctionPair.comparison A s M' N).hom.natTrans.app n =
    (Mod.internalHomι A ((Mod.free A.X).obj (sourceDiagram (𝟙_ I) (𝟙_ V))) N).natTrans.app n ≫
      end_.π ((dayConvolutionInternalHomDiagramFunctor
        ((Mod.free A.X).obj (sourceDiagram (𝟙_ I) (𝟙_ V))).X.functor).obj
        N.X.functor |>.obj n) s ≫
      (MonoidalClosed.pre
        (Sigma.ι (fun _ : s ⟶ s => M') (𝟙 s) ≫
          ((Mod.freeForgetAdjunction A.X).unit.app (sourceDiagram s M')).natTrans.app s ≫
          f.hom.natTrans.app s)).app (N.X.functor.obj (s ⊗ n)) ≫
      (ihom M').map (N.X.functor.map (β_ s n).hom) := by
  exact module_source_projection A (𝟙_ I) s (𝟙_ V) M' f N n

/-- The literal original zero-free source word is the transpose of the full
target module action at the actual original source generator and unit contraction. -/
theorem original_zero_source_action_projection (s : I) (M' : V)
    (f : (Mod.free A.X).obj (sourceDiagram s M') ⟶
      (Mod.free A.X).obj (sourceDiagram (𝟙_ I) (𝟙_ V)))
    (N : Mod (DayFunctor I V) A.X) (n : I) :
    originalZeroSourceWord A s M' f N n = originalZeroSourceAction A s M' f N n := by
  have hOriginal := original_zero_parameter_projection A s M' f N n
  let P := sourceDiagram (𝟙_ I) (𝟙_ V)
  let F := (Mod.free A.X).obj P
  let H₀ := (Mod.internalHom A F).obj N
  let E := end_ ((dayConvolutionInternalHomDiagramFunctor F.X.functor).obj
    N.X.functor |>.obj n)
  let d := (NativeOmegaPreparation.DayFreeEnd.comparison (𝟙_ I) (𝟙_ V) ≪≫
    NativeOmegaPreparation.DayIndexOrder.comparison (𝟙_ I) (𝟙_ V)).app N.X
  let z := N.X.functor.map (ρ_ n).inv ≫
    MonoidalClosed.unitNatIso.hom.app (N.X.functor.obj (n ⊗ (𝟙_ I)))
  let i : ((ihom P).obj N.X).functor.obj n ⟶ H₀.X.functor.obj n :=
    (Mod.FreeInternalHom.inverse A P N).natTrans.app n
  let j : H₀.X.functor.obj n ⟶ E := (Mod.internalHomι A F N).natTrans.app n
  let π : E ⟶ (ihom (F.X.functor.obj s)).obj (N.X.functor.obj (s ⊗ n)) :=
    end_.π ((dayConvolutionInternalHomDiagramFunctor F.X.functor).obj
    N.X.functor |>.obj n) s
  let g := Sigma.ι (fun _ : s ⟶ s => M') (𝟙 s) ≫
    ((Mod.freeForgetAdjunction A.X).unit.app (sourceDiagram s M')).natTrans.app s ≫
    f.hom.natTrans.app s
  let e : F.X ⟶ A.X := (A.X ◁ originalZeroDiagramUnit) ≫ (ρ_ A.X).hom
  let q₀ : P ⊗ N.X ⟶ N.X := (originalZeroDiagramUnit ▷ N.X) ≫ (λ_ N.X).hom
  let q : F.X ⊗ N.X ⟶ N.X := (e ▷ N.X) ≫ N.mod.smul
  let b := (ihom M').map (N.X.functor.map (β_ s n).hom)
  have hz : z ≫ d.inv.natTrans.app n = (MonoidalClosed.curry q₀).natTrans.app n :=
    original_zero_end_inverse_unit N.X n
  have hu : (MonoidalClosed.curry q₀).natTrans.app n ≫ i ≫ j =
      (MonoidalClosed.curry q).natTrans.app n := by
    have h := congrArg (fun w => w.natTrans.app n)
      (OriginalFreeUnitExtension.inverse_unit_ι A P originalZeroDiagramUnit N)
    exact h
  have hπ : (MonoidalClosed.curry q).natTrans.app n ≫ π =
      MonoidalClosed.curry
        ((DayFunctor.η F.X N.X).app (s, n) ≫ q.natTrans.app (s ⊗ n)) :=
    NativeOmegaPreparation.DayClosedProjection.curry_π F.X N.X N.X q n s
  have hq : ((g ▷ N.X.functor.obj n) ≫
      (DayFunctor.η F.X N.X).app (s, n) ≫ q.natTrans.app (s ⊗ n)) =
      ((g ≫ e.natTrans.app s) ▷ N.X.functor.obj n) ≫
        (DayFunctor.η A.X N.X).app (s, n) ≫ N.mod.smul.natTrans.app (s ⊗ n) :=
    original_day_generator_action F.X A.X N.X e N.mod.smul s n M' g
  let X := N.X.functor.obj n
  let T := N.X.functor.obj (s ⊗ n)
  let t : F.X.functor.obj s ⊗ X ⟶ T :=
    (DayFunctor.η F.X N.X).app (s, n) ≫ q.natTrans.app (s ⊗ n)
  let a : M' ⊗ X ⟶ T :=
    ((g ≫ e.natTrans.app s) ▷ X) ≫
      (DayFunctor.η A.X N.X).app (s, n) ≫ N.mod.smul.natTrans.app (s ⊗ n)
  let pre : (ihom (F.X.functor.obj s)).obj T ⟶ (ihom M').obj T :=
    (MonoidalClosed.pre g).app T
  let Hₛ := (Mod.internalHom A ((Mod.free A.X).obj (sourceDiagram s M'))).obj N
  let p : H₀.X.functor.obj n ⟶ Hₛ.X.functor.obj n :=
    ((MonoidalClosed.pre f).app N).hom.natTrans.app n
  let c : Hₛ.X.functor.obj n ⟶ (ihom M').obj (N.X.functor.obj (n ⊗ s)) :=
    (FullFreeFunctionPair.comparison A s M' N).hom.natTrans.app n
  have hC := scalar_curry_projection_pre (g := g) (t := t) (a := a) hπ hq
  have hp : p ≫ c = j ≫ π ≫ pre ≫ b := hOriginal
  have hInv : (FullFreeFunctionPair.comparison A (𝟙_ I) (𝟙_ V) N).inv.natTrans.app n =
      d.inv.natTrans.app n ≫ i :=
    original_free_source_comparison_inverse_component A (𝟙_ I) (𝟙_ V) N n
  have hSource : originalZeroSourceWord A s M' f N n =
      z ≫ (d.inv.natTrans.app n ≫ i) ≫ (p ≫ c) := by
    exact congrArg (fun w => z ≫ w ≫ (p ≫ c)) hInv
  have hAction : MonoidalClosed.curry a ≫ b = originalZeroSourceAction A s M' f N n := by
    have hGenerator := source_chain_associativity
      (Sigma.ι (fun _ : s ⟶ s => M') (𝟙 s))
      (((Mod.freeForgetAdjunction A.X).unit.app (sourceDiagram s M')).natTrans.app s)
      (f.hom.natTrans.app s) (e.natTrans.app s)
    have h := congrArg (fun w : M' ⟶ A.X.functor.obj s =>
      MonoidalClosed.curry ((w ▷ X) ≫
        (DayFunctor.η A.X N.X).app (s, n) ≫ N.mod.smul.natTrans.app (s ⊗ n)) ≫ b)
      hGenerator
    exact h
  have hJoin := compose_original_source_word z (d.inv.natTrans.app n) i p c j π pre b
    ((MonoidalClosed.curry q₀).natTrans.app n) ((MonoidalClosed.curry q).natTrans.app n)
    (MonoidalClosed.curry a) hp hz hu hC
  exact hSource.trans (hJoin.trans hAction)

/-- The literal original all-output equation is the complete proved source/action equality. -/
theorem original_zero_source_action_projection_literal (s : I) (M' : V)
    (f : (Mod.free A.X).obj (sourceDiagram s M') ⟶
      (Mod.free A.X).obj (sourceDiagram (𝟙_ I) (𝟙_ V)))
    (N : Mod (DayFunctor I V) A.X) (n : I) :
    dsimp% only [originalZeroSourceWord, originalZeroSourceAction]
      (originalZeroSourceWord A s M' f N n = originalZeroSourceAction A s M' f N n) :=
  original_zero_source_action_projection A s M' f N n

end NativeOmegaRecovery.FreeFunctionSourceEvaluation
