/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex

module

public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.CategoryTheory.Limits.Opposites
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import MathlibExt.AlgebraicTopology.ModelCategory.FiniteResolutionTensor
public import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedDerivedMapping
public import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedFramings
public import MathlibExt.AlgebraicTopology.SimplexCategory.Reedy
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetModelStructure
public import MathlibExt.AlgebraicTopology.SimplicialSet.StdSimplexFirstContraction
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHomotopyEquivWeakHomotopy
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizedHomotopyEquiv
public import MathlibExt.CategoryTheory.Reedy.FiniteBoundaries
public import MathlibExt.CategoryTheory.Reedy.Boundary

/-!
# The original cotensor Hom equivalence and all three naturalities

Both actual parametrized adjunctions of the compatible action identify morphisms into
the actual cotensor with simplicial maps into the original enriched Hom. Every source,
simplicial-parameter, and target map is retained, in both directions of the equivalence.
-/

section

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Opposite
open scoped SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.CompatibleCotensorFraming

variable {C : Type u} [Category.{v} C] [ModelCategory C] [SimplicialCategory C]
variable (a : CompatibleSimplicialMapping.Action C)

/-- The full original tensor/Hom and tensor/cotensor adjunctions give this actual equivalence. -/
def homEquiv (X : C) (K : SSet.{v}) (Y : C) :
    (X ⟶ (a.cotensor.obj (op K)).obj Y) ≃ (K ⟶ SimplicialCategory.sHom X Y) :=
  (a.tensorCotensor.homEquiv (X₁ := K) (X₂ := X) (X₃ := Y)).symm.trans
    (a.tensorHom.homEquiv (X₁ := X) (X₂ := K) (X₃ := Y))

/-- Original source precomposition is the same original enriched precomposition. -/
theorem homEquiv_source {X X' : C} (i : X ⟶ X') (K : SSet.{v}) (Y : C)
    (h : X' ⟶ (a.cotensor.obj (op K)).obj Y) :
    homEquiv a X K Y (i ≫ h) = homEquiv a X' K Y h ≫
      ((SimplicialCategory.sHomFunctor C).map i.op).app Y := by
  change a.tensorHom.homEquiv (a.tensorCotensor.homEquiv.symm (i ≫ h)) =
    a.tensorHom.homEquiv (a.tensorCotensor.homEquiv.symm h) ≫ _
  rw [a.tensorCotensor.homEquiv_symm_naturality_two]
  exact a.tensorHom.homEquiv_naturality_one i _

/-- Every original simplicial parameter map becomes the same original simplex precomposition. -/
theorem homEquiv_parameter (X : C) {K L : SSet.{v}} (k : K ⟶ L) (Y : C)
    (h : X ⟶ (a.cotensor.obj (op L)).obj Y) :
    homEquiv a X K Y (h ≫ (a.cotensor.map k.op).app Y) = k ≫ homEquiv a X L Y h := by
  change a.tensorHom.homEquiv
      (a.tensorCotensor.homEquiv.symm (h ≫ (a.cotensor.map k.op).app Y)) =
    k ≫ a.tensorHom.homEquiv (a.tensorCotensor.homEquiv.symm h)
  rw [a.tensorCotensor.homEquiv_symm_naturality_one]
  exact a.tensorHom.homEquiv_naturality_two k _

/-- Original target postcomposition becomes the same original enriched postcomposition. -/
theorem homEquiv_target (X : C) (K : SSet.{v}) {Y Y' : C} (p : Y ⟶ Y')
    (h : X ⟶ (a.cotensor.obj (op K)).obj Y) :
    homEquiv a X K Y' (h ≫ (a.cotensor.obj (op K)).map p) = homEquiv a X K Y h ≫
      ((SimplicialCategory.sHomFunctor C).obj (op X)).map p := by
  change a.tensorHom.homEquiv
      (a.tensorCotensor.homEquiv.symm (h ≫ (a.cotensor.obj (op K)).map p)) =
    a.tensorHom.homEquiv (a.tensorCotensor.homEquiv.symm h) ≫ _
  rw [a.tensorCotensor.homEquiv_symm_naturality_three]
  exact a.tensorHom.homEquiv_naturality_three p _

/-- The inverse equivalence retains every original source map. -/
theorem homEquiv_symm_source {X X' : C} (i : X ⟶ X') (K : SSet.{v}) (Y : C)
    (h : K ⟶ SimplicialCategory.sHom X' Y) :
    (homEquiv a X K Y).symm (h ≫ ((SimplicialCategory.sHomFunctor C).map i.op).app Y) =
      i ≫ (homEquiv a X' K Y).symm h := by
  apply (homEquiv a X K Y).injective
  rw [Equiv.apply_symm_apply, homEquiv_source, Equiv.apply_symm_apply]
  rfl

/-- The inverse equivalence retains every original simplicial parameter map. -/
theorem homEquiv_symm_parameter (X : C) {K L : SSet.{v}} (k : K ⟶ L) (Y : C)
    (h : L ⟶ SimplicialCategory.sHom X Y) :
    (homEquiv a X K Y).symm (k ≫ h) =
      (homEquiv a X L Y).symm h ≫ (a.cotensor.map k.op).app Y := by
  apply (homEquiv a X K Y).injective
  rw [Equiv.apply_symm_apply, homEquiv_parameter, Equiv.apply_symm_apply]

/-- The inverse equivalence retains every original target map. -/
theorem homEquiv_symm_target (X : C) (K : SSet.{v}) {Y Y' : C} (p : Y ⟶ Y')
    (h : K ⟶ SimplicialCategory.sHom X Y) :
    (homEquiv a X K Y').symm (h ≫ ((SimplicialCategory.sHomFunctor C).obj (op X)).map p) =
      (homEquiv a X K Y).symm h ≫ (a.cotensor.obj (op K)).map p := by
  apply (homEquiv a X K Y').injective
  rw [Equiv.apply_symm_apply, homEquiv_target, Equiv.apply_symm_apply]
  rfl

end HomotopicalAlgebra.CompatibleCotensorFraming

end
end
end

section



/-!
# The genuine rotated cotensor adjunction and its model laws

The full original Hom equivalence constructs the actual adjunction from the opposite
enriched Hom functor into the fixed-target cotensor. The compatible source PP laws give
its Quillen property. Brown's lemma then supplies weak preservation on original cofibrant
simplicial sets; no frame or Hom-complex outcome is a premise.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Limits Opposite
open scoped SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.CompatibleCotensorFraming

variable {C : Type u} [Category.{v} C] [ModelCategory C] [SimplicialCategory C]
variable (a : CompatibleSimplicialMapping.Action C)

/-- The original enriched Hom into the fixed target, with its actual variance rotated. -/
def mappingToOpposite (Y : C) : C ⥤ SSet.{v}ᵒᵖ :=
  ((SimplicialCategory.sHomFunctor C).flip.obj Y).rightOp

/-- The original fixed-target cotensor keeps every original simplicial parameter map. -/
def cotensorAt (Y : C) : SSet.{v}ᵒᵖ ⥤ C := a.cotensor.flip.obj Y

/-- The actual rotated adjunction is constructed from both complete source adjunctions. -/
def cotensorAdjunction (Y : C) : mappingToOpposite (C := C) Y ⊣ cotensorAt a Y :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X K => (CategoryTheory.opEquiv (op (SimplicialCategory.sHom X Y)) K).trans
        (homEquiv a X K.unop Y).symm
      homEquiv_naturality_left_symm := by
        intro X' X K i h
        apply Quiver.Hom.unop_inj
        change homEquiv a X' K.unop Y (i ≫ h) = homEquiv a X K.unop Y h ≫
          ((SimplicialCategory.sHomFunctor C).map i.op).app Y
        exact homEquiv_source a i K.unop Y h
      homEquiv_naturality_right := by
        intro X K L f k
        change (homEquiv a X L.unop Y).symm (k.unop ≫ f.unop) =
          (homEquiv a X K.unop Y).symm f.unop ≫ (a.cotensor.map k).app Y
        exact homEquiv_symm_parameter a X k.unop Y f.unop }

/-- The rotated adjunction's original source PP laws give its actual Quillen property. -/
theorem cotensor_isQuillen (Y : C) [IsFibrant Y] :
    (cotensorAdjunction a Y).IsQuillenAdjunction := by
  constructor
  · intro X X' i hi
    rw [cofibrations_op]
    change fibrations SSet.{v} (((SimplicialCategory.sHomFunctor C).map i.op).app Y)
    exact CompatibleSimplicialMapping.sm7_fibration a
      (CompatibleSimplicialMapping.terminalCorner a i Y) hi
      ((fibration_iff (terminal.from Y)).mp inferInstance)
  · intro X X' i hi
    rw [trivialCofibrations_op]
    change trivialFibrations SSet.{v} (((SimplicialCategory.sHomFunctor C).map i.op).app Y)
    exact CompatibleSimplicialMapping.sm7_trivial_left a
      (CompatibleSimplicialMapping.terminalCorner a i Y) hi
      ((fibration_iff (terminal.from Y)).mp inferInstance)

/-- The actual fixed-target cotensor preserves original opposite cofibrations as fibrations. -/
theorem cotensor_map_fibration (Y : C) [IsFibrant Y] {K L : SSet.{v}} (k : K ⟶ L)
    (hk : cofibrations SSet.{v} k) : fibrations C ((a.cotensor.map k.op).app Y) := by
  let _ : (cotensorAdjunction a Y).IsQuillenAdjunction := cotensor_isQuillen a Y
  exact (CategoryTheory.Adjunction.IsQuillenAdjunction.preservesFibrations
    (adj := cotensorAdjunction a Y)) k.op hk

/-- Brown's theorem preserves the same original weak map between cofibrant simplicial sets. -/
theorem cotensor_map_weak (Y : C) [IsFibrant Y] {K L : SSet.{v}} (k : K ⟶ L)
    [WeakEquivalence k] [IsCofibrant K] [IsCofibrant L] :
    WeakEquivalence ((a.cotensor.map k.op).app Y) := by
  let _ : (cotensorAdjunction a Y).IsQuillenAdjunction := cotensor_isQuillen a Y
  let _ : IsFibrant (op K) :=
    (isFibrant_iff_of_isTerminal (initial.to K).op initialIsInitial.op).mpr (by
      apply (fibration_iff _).mpr
      rw [fibrations_op]
      exact mem_cofibrations (initial.to K))
  let _ : IsFibrant (op L) :=
    (isFibrant_iff_of_isTerminal (initial.to L).op initialIsInitial.op).mpr (by
      apply (fibration_iff _).mpr
      rw [fibrations_op]
      exact mem_cofibrations (initial.to L))
  exact CategoryTheory.Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_fibrant
    (adj := cotensorAdjunction a Y) k.op

end HomotopicalAlgebra.CompatibleCotensorFraming

end
end
end

section



/-!
# The actual cotensor simplicial object and original enriched Hom calculation

Every degree and every face/degeneracy is the original cotensor applied to the original
standard simplex. Both source adjunctions and native standard-simplex Yoneda construct
the full Hom-complex isomorphism, retaining all original source and target maps.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Opposite Simplicial
open scoped SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.CompatibleCotensorFraming

variable {C : Type u} [Category.{v} C] [ModelCategory C] [SimplicialCategory C]
variable (a : CompatibleSimplicialMapping.Action C)

/-- The genuine original cotensor simplicial functor on every original target object. -/
@[implicit_reducible]
def resolution : C ⥤ SimplicialObject C :=
  a.cotensor.flip ⋙
    (Functor.whiskeringLeft SimplexCategoryᵒᵖ SSet.{v}ᵒᵖ C).obj SSet.stdSimplex.op

/-- Each original degree is the actual cotensor by the same original standard simplex. -/
theorem resolution_obj (Y : C) (n : SimplexCategoryᵒᵖ) :
    ((resolution a).obj Y).obj n = (a.cotensor.obj (op (SSet.stdSimplex.obj n.unop))).obj Y := rfl

/-- Every original simplicial operator is the original cotensor of the original simplex map. -/
theorem resolution_map (Y : C) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    ((resolution a).obj Y).map f =
      (a.cotensor.map (SSet.stdSimplex.map f.unop).op).app Y := rfl

/-- Every target morphism is the same original cotensor target-map component. -/
theorem resolution_map_target {Y Y' : C} (p : Y ⟶ Y') (n : SimplexCategoryᵒᵖ) :
    ((resolution a).map p).app n =
      (a.cotensor.obj (op (SSet.stdSimplex.obj n.unop))).map p := rfl

/-- The actual right Hom complex of this original cotensor simplicial object. -/
abbrev complex (X Y : C) : SSet.{v} := ResolutionHomComplex.right X ((resolution a).obj Y)

/-- Both actual adjunctions and actual Yoneda identify each original Hom-complex degree. -/
def degreeEquiv (X Y : C) (n : SimplexCategoryᵒᵖ) :
    (complex a X Y).obj n ≃ (SimplicialCategory.sHom X Y).obj n :=
  (homEquiv a X (SSet.stdSimplex.obj n.unop) Y).trans SSet.yonedaEquiv

/-- The degree equivalence retains every original face and degeneracy map. -/
theorem degreeEquiv_simplex (X Y : C) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    (h : X ⟶ (a.cotensor.obj (op (SSet.stdSimplex.obj n.unop))).obj Y) :
    degreeEquiv a X Y m ((complex a X Y).map f h) =
      (SimplicialCategory.sHom X Y).map f (degreeEquiv a X Y n h) := by
  rw [ResolutionHomComplex.right_map_apply, resolution_map]
  change SSet.yonedaEquiv
      (homEquiv a X (SSet.stdSimplex.obj m.unop) Y
        (h ≫ (a.cotensor.map (SSet.stdSimplex.map f.unop).op).app Y)) =
    (SimplicialCategory.sHom X Y).map f (SSet.yonedaEquiv
      (homEquiv a X (SSet.stdSimplex.obj n.unop) Y h))
  rw [homEquiv_parameter]
  exact (uliftYonedaEquiv_naturality _ f).symm

/-- The degree equivalence retains every original source precomposition. -/
theorem degreeEquiv_source {X X' : C} (i : X ⟶ X') (Y : C) (n : SimplexCategoryᵒᵖ)
    (h : X' ⟶ (a.cotensor.obj (op (SSet.stdSimplex.obj n.unop))).obj Y) :
    degreeEquiv a X Y n (i ≫ h) =
      (((SimplicialCategory.sHomFunctor C).map i.op).app Y).app n
        (degreeEquiv a X' Y n h) := by
  change SSet.yonedaEquiv (homEquiv a X (SSet.stdSimplex.obj n.unop) Y (i ≫ h)) = _
  rw [homEquiv_source]
  exact uliftYonedaEquiv_comp _ _

/-- The degree equivalence retains every original target postcomposition. -/
theorem degreeEquiv_target (X : C) {Y Y' : C} (p : Y ⟶ Y') (n : SimplexCategoryᵒᵖ)
    (h : X ⟶ (a.cotensor.obj (op (SSet.stdSimplex.obj n.unop))).obj Y) :
    degreeEquiv a X Y' n (h ≫ (a.cotensor.obj (op (SSet.stdSimplex.obj n.unop))).map p) =
      (((SimplicialCategory.sHomFunctor C).obj (op X)).map p).app n (degreeEquiv a X Y n h) := by
  change SSet.yonedaEquiv (homEquiv a X (SSet.stdSimplex.obj n.unop) Y'
    (h ≫ (a.cotensor.obj (op (SSet.stdSimplex.obj n.unop))).map p)) = _
  rw [homEquiv_target]
  exact uliftYonedaEquiv_comp _ _

/-- The whole actual right Hom complex is the original enriched Hom simplicial set. -/
def complexIso (X Y : C) : complex a X Y ≅ SimplicialCategory.sHom X Y :=
  NatIso.ofComponents (fun n => (degreeEquiv a X Y n).toIso) (by
    intro n m f
    ext h
    exact degreeEquiv_simplex a X Y f h)

/-- The whole original cotensor Hom bifunctor, with constant cosimplicial sources. -/
def complexBifunctor : Cᵒᵖ ⥤ C ⥤ SSet.{v} :=
  ResolutionHomComplex.ofFunctors (CosimplicialObject.const C) (resolution a)

/-- The full actual original enriched-Hom calculation is natural in both original variables. -/
def calculation : complexBifunctor a ≅ SimplicialCategory.sHomFunctor C :=
  NatIso.ofComponents (fun X =>
    NatIso.ofComponents (fun Y => complexIso a X.unop Y) (by
      intro Y Y' p
      ext n h
      exact degreeEquiv_target a X.unop p n h)) (by
        intro X X' i
        ext Y n h
        exact degreeEquiv_source a i.unop Y n h)

end HomotopicalAlgebra.CompatibleCotensorFraming

end
end
end

section



/-!
# Full original Q/R cotensor Hom calculation

The actual cotensor simplicial functor is applied to the same original generated R.
The source is the constant cosimplicial object on the same original Q. Their actual
Hom complex is naturally isomorphic to the existing original mixed mapping bifunctor.
Both functions of the isomorphism and every original Q/R and simplex map are retained.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w u v

open CategoryTheory Opposite Simplicial
open scoped SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.CompatibleCotensorFraming

variable {C : Type u} [Category.{v} C] [ModelCategory C] [SimplicialCategory C]
variable (a : CompatibleSimplicialMapping.Action C)
variable {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
variable (d : CofibrantGenerationData C κ)

open GeneratedFunctorialReplacements

/-- The actual cotensor simplicial functor on the same original generated R objects and maps. -/
def originalResolution : C ⥤ SimplicialObject C := R d ⋙ resolution a

/-- Every degree uses the same original generated R object and original standard simplex. -/
theorem originalResolution_obj (Y : C) (n : SimplexCategoryᵒᵖ) :
    ((originalResolution a d).obj Y).obj n =
      (a.cotensor.obj (op (SSet.stdSimplex.obj n.unop))).obj ((R d).obj Y) := rfl

/-- Every original face/degeneracy is the same original cotensor parameter-map component. -/
theorem originalResolution_map (Y : C) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    ((originalResolution a d).obj Y).map f =
      (a.cotensor.map (SSet.stdSimplex.map f.unop).op).app ((R d).obj Y) := rfl

/-- Every original target morphism remains the same original R map inside the same cotensor. -/
theorem originalResolution_map_target {Y Y' : C} (p : Y ⟶ Y') (n : SimplexCategoryᵒᵖ) :
    ((originalResolution a d).map p).app n =
      (a.cotensor.obj (op (SSet.stdSimplex.obj n.unop))).map ((R d).map p) := rfl

/-- The full genuine resolution Hom bifunctor on the same original Q and R arrows. -/
def originalComplex : Cᵒᵖ ⥤ C ⥤ SSet.{v} :=
  ResolutionHomComplex.ofFunctors (Q d ⋙ CosimplicialObject.const C) (originalResolution a d)

/-- The actual original resolution Hom spaces equal the existing original mixed mapping bifunctor.
-/
def originalCalculation : originalComplex a d ≅ GeneratedDerivedMapping.bifunctor d :=
  NatIso.ofComponents (fun X =>
    NatIso.ofComponents (fun Y => complexIso a ((Q d).obj X.unop) ((R d).obj Y)) (by
      intro Y Y' p
      ext n h
      exact degreeEquiv_target a ((Q d).obj X.unop) ((R d).map p) n h)) (by
        intro X X' i
        ext Y n h
        exact degreeEquiv_source a ((Q d).map i.unop) ((R d).obj Y) n h)

/-- The represented-map function retains both original replacements and the actual adjunction. -/
theorem originalCalculation_hom_app (X Y : C) (n : SimplexCategoryᵒᵖ)
    (h : (Q d).obj X ⟶ (a.cotensor.obj (op (SSet.stdSimplex.obj n.unop))).obj ((R d).obj Y)) :
    ((((originalCalculation a d).hom.app (op X)).app Y).app n) h =
      SSet.yonedaEquiv (homEquiv a ((Q d).obj X) (SSet.stdSimplex.obj n.unop) ((R d).obj Y) h) :=
        rfl

/-- The inverse represented-map function retains the same original cotensor and Q/R endpoints. -/
theorem originalCalculation_inv_app (X Y : C) (n : SimplexCategoryᵒᵖ)
    (h : (GeneratedDerivedMapping.space d X Y).obj n) :
    ((((originalCalculation a d).inv.app (op X)).app Y).app n) h =
      (homEquiv a ((Q d).obj X) (SSet.stdSimplex.obj n.unop) ((R d).obj Y)).symm
        (SSet.yonedaEquiv.symm h) := rfl

end HomotopicalAlgebra.CompatibleCotensorFraming

end
end
end

section



/-!
# Every original standard-simplex map is a realization weak equivalence

The original collapse has the original first-vertex section. The proved directed
first-vertex contraction gives a genuine homotopy equivalence after realization.
The selected Kan--Quillen model detects that weak equivalence. Every original simplex
map then satisfies the same collapse triangle, so two-out-of-three proves its weakness.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v

open CategoryTheory HomotopicalAlgebra Simplicial
open scoped SSet.modelCategoryQuillen

namespace SSet.StandardSimplexWeakMaps

/-- The original scalar collapse of the same original standard simplex. -/
def collapse (n : SimplexCategory) : SSet.stdSimplex.{v}.obj n ⟶ Δ[0] :=
  SSet.stdSimplex.map (SimplexCategory.const n ⦋0⦌ 0)

/-- The original first-vertex section of that same collapse. -/
def firstSection (n : SimplexCategory) : Δ[0] ⟶ SSet.stdSimplex.{v}.obj n :=
  SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ n 0)

/-- The original source-side composite is the same original constant first-vertex map. -/
theorem collapse_firstSection (n : SimplexCategory) :
    collapse.{v} n ≫ firstSection n =
        SSet.const (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (n.len + 1))) := by
  apply SSet.yonedaEquiv.injective
  apply SSet.stdSimplex.ext
  intro i
  rfl

/-- The original target-side composite is exactly the original identity of the point simplex. -/
theorem firstSection_collapse (n : SimplexCategory) :
    firstSection.{v} n ≫ collapse n = 𝟙 (Δ[0] : SSet.{v}) := by
  apply SSet.yonedaEquiv.injective
  apply SSet.stdSimplex.ext
  intro i
  change (0 : Fin 1) = i
  exact Subsingleton.elim _ _

/-- The original first-vertex contraction gives the required genuine directed source homotopy. -/
def contraction (n : SimplexCategory) :
    SSet.Homotopy (collapse.{v} n ≫ firstSection n) (𝟙 (SSet.stdSimplex.obj n)) := by
  rw [collapse_firstSection]
  exact SSet.stdSimplex.homotopyConstFirstId n.len

/-- The actual realized collapse and first section form a genuine homotopy equivalence. -/
def realizedCollapseEquiv (n : SimplexCategory) :
    ContinuousMap.HomotopyEquiv (SSet.toTop.obj (SSet.stdSimplex.{v}.obj n))
      (SSet.toTop.obj (Δ[0] : SSet.{v})) :=
  SSet.realizedHomotopyEquiv _ _ (collapse n) (firstSection n) (contraction n) (by
    rw [firstSection_collapse]
    exact SSet.RelativeMorphism.Homotopy.refl
      (SSet.RelativeMorphism.botEquiv.symm (𝟙 (Δ[0] : SSet.{v}))))

/-- The same original collapse is weak in the actual selected realization model. -/
theorem collapse_weak (n : SimplexCategory) : WeakEquivalence (collapse.{v} n) := by
  apply (weakEquivalence_iff _).mpr
  change TopCat.weakHomotopyEquivalences (SSet.toTop.map (collapse n))
  exact TopCat.mem_of_eq_toFun (realizedCollapseEquiv n) rfl

/-- Every original simplex map retains its whole original collapse triangle. -/
theorem map_collapse {n m : SimplexCategory} (f : n ⟶ m) :
    SSet.stdSimplex.{v}.map f ≫ collapse m = collapse n := by
  rw [collapse, ← Functor.map_comp]
  congr 1

/-- Every actual original standard-simplex map is weak, in every original SSet universe. -/
theorem map_weak {n m : SimplexCategory} (f : n ⟶ m) :
    WeakEquivalence (SSet.stdSimplex.{v}.map f) := by
  let _ : WeakEquivalence (collapse.{v} n) := collapse_weak n
  let _ : WeakEquivalence (collapse.{v} m) := collapse_weak m
  exact weakEquivalence_of_postcomp_of_fac (map_collapse f)

end SSet.StandardSimplexWeakMaps

end
end
end

section



/-!
# Genuine homotopical constancy of the original cotensor simplicial objects

Every simplicial set is cofibrant in the selected Kan--Quillen model. The proved
standard-simplex weakness and actual rotated Quillen/Brown result make every original
face/degeneracy weak. The original generated R supplies the actual fibrant target.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w u v

open CategoryTheory Limits Opposite Simplicial
open scoped SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.CompatibleCotensorFraming

/-- Every actual simplicial set is cofibrant in the same selected simplicial-set model. -/
theorem simplicial_isCofibrant (K : SSet.{v}) : IsCofibrant K := by
  apply (cofibration_iff (initial.to K)).mpr
  change Mono (initial.to K)
  infer_instance

variable {C : Type u} [Category.{v} C] [ModelCategory C] [SimplicialCategory C]
variable (a : CompatibleSimplicialMapping.Action C)

/-- Every actual cotensor face or degeneracy is weak at the same original fibrant target. -/
theorem resolution_map_weak (Y : C) [IsFibrant Y] {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    WeakEquivalence (((resolution a).obj Y).map f) := by
  let _ : IsCofibrant (SSet.stdSimplex.{v}.obj n.unop) := simplicial_isCofibrant _
  let _ : IsCofibrant (SSet.stdSimplex.{v}.obj m.unop) := simplicial_isCofibrant _
  let _ : WeakEquivalence (SSet.stdSimplex.{v}.map f.unop) :=
    SSet.StandardSimplexWeakMaps.map_weak f.unop
  exact cotensor_map_weak a Y (SSet.stdSimplex.map f.unop)

variable {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
variable (d : CofibrantGenerationData C κ)

/-- All original cotensor-frame structure maps are weak at the same original generated R endpoint.
-/
theorem originalResolution_map_weak (Y : C) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    WeakEquivalence (((originalResolution a d).obj Y).map f) := by
  let _ : IsFibrant ((GeneratedFunctorialReplacements.R d).obj Y) :=
    GeneratedFunctorialReplacements.R_isFibrant d Y
  exact resolution_map_weak a _ f

end HomotopicalAlgebra.CompatibleCotensorFraming

end
end
end

section



/-!
# The actual natural degree-zero cotensor identification

The original enriched category identifies its zero simplices with its original morphisms.
Together with both source adjunctions this constructs the actual natural isomorphism
from the original target to its cotensor by the original point simplex.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Opposite Simplicial
open scoped MonoidalCategory SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.CompatibleCotensorFraming

variable {C : Type u} [Category.{v} C] [SimplicialCategory C]

/-- Underlying original source composition agrees with the original enriched zero-simplex map. -/
theorem ordinaryZero_source {X X' Y : C} (i : X ⟶ X') (f : X' ⟶ Y) :
    (eHomWhiskerRight SSet i Y).app (op ⦋0⦌)
      (SimplicialCategory.homEquiv' X' Y f) = SimplicialCategory.homEquiv' X Y (i ≫ f) := by
  change ((eHomEquiv SSet f ≫ eHomWhiskerRight SSet i Y).app (op ⦋0⦌)) PUnit.unit =
    (eHomEquiv SSet (i ≫ f)).app (op ⦋0⦌) PUnit.unit
  rw [eHomEquiv_comp]
  rfl

/-- Underlying original target composition agrees with the original enriched zero-simplex map. -/
theorem ordinaryZero_target {X Y Y' : C} (f : X ⟶ Y) (p : Y ⟶ Y') :
    (eHomWhiskerLeft SSet X p).app (op ⦋0⦌)
      (SimplicialCategory.homEquiv' X Y f) = SimplicialCategory.homEquiv' X Y' (f ≫ p) := by
  change ((eHomEquiv SSet f ≫ eHomWhiskerLeft SSet X p).app (op ⦋0⦌)) PUnit.unit =
    (eHomEquiv SSet (f ≫ p)).app (op ⦋0⦌) PUnit.unit
  rw [eHomEquiv_comp]
  rfl

/-- The inverse underlying-Hom identification retains the original source map. -/
theorem ordinaryZero_symm_source {X X' Y : C} (i : X ⟶ X')
    (f : (SimplicialCategory.sHom X' Y).obj (op ⦋0⦌)) :
    (SimplicialCategory.homEquiv' X Y).symm
        ((eHomWhiskerRight SSet i Y).app (op ⦋0⦌) f) =
      i ≫ (SimplicialCategory.homEquiv' X' Y).symm f := by
  apply (SimplicialCategory.homEquiv' X Y).symm_apply_eq.mpr
  simpa only [Equiv.apply_symm_apply] using
    ordinaryZero_source i ((SimplicialCategory.homEquiv' X' Y).symm f)

/-- The inverse underlying-Hom identification retains the original target map. -/
theorem ordinaryZero_symm_target {X Y Y' : C} (p : Y ⟶ Y')
    (f : (SimplicialCategory.sHom X Y).obj (op ⦋0⦌)) :
    (SimplicialCategory.homEquiv' X Y').symm
        ((eHomWhiskerLeft SSet X p).app (op ⦋0⦌) f) =
      (SimplicialCategory.homEquiv' X Y).symm f ≫ p := by
  apply (SimplicialCategory.homEquiv' X Y').symm_apply_eq.mpr
  simpa only [Equiv.apply_symm_apply] using
    ordinaryZero_target ((SimplicialCategory.homEquiv' X Y).symm f) p

variable [ModelCategory C] (a : CompatibleSimplicialMapping.Action C)

/-- The actual point cotensor represents the same original ordinary target. -/
def zeroHomEquiv (X Y : C) : (X ⟶ (a.cotensor.obj (op (Δ[0] : SSet.{v}))).obj Y) ≃ (X ⟶ Y) :=
  (homEquiv a X Δ[0] Y).trans (SSet.yonedaEquiv.trans (SimplicialCategory.homEquiv' X Y).symm)

/-- The point cotensor equivalence keeps every original source morphism. -/
theorem zeroHomEquiv_source {X X' Y : C} (i : X ⟶ X')
    (h : X' ⟶ (a.cotensor.obj (op (Δ[0] : SSet.{v}))).obj Y) :
    zeroHomEquiv a X Y (i ≫ h) = i ≫ zeroHomEquiv a X' Y h := by
  calc
    _ = (SimplicialCategory.homEquiv' X Y).symm (degreeEquiv a X Y (op ⦋0⦌) (i ≫ h)) := rfl
    _ = (SimplicialCategory.homEquiv' X Y).symm
        ((((SimplicialCategory.sHomFunctor C).map i.op).app Y).app (op ⦋0⦌)
          (degreeEquiv a X' Y (op ⦋0⦌) h)) :=
      congrArg (SimplicialCategory.homEquiv' X Y).symm (degreeEquiv_source a i Y (op ⦋0⦌) h)
    _ = i ≫ (SimplicialCategory.homEquiv' X' Y).symm (degreeEquiv a X' Y (op ⦋0⦌) h) :=
      ordinaryZero_symm_source i _
    _ = _ := rfl

/-- The point cotensor equivalence keeps every original target morphism. -/
theorem zeroHomEquiv_target (X : C) {Y Y' : C} (p : Y ⟶ Y')
    (h : X ⟶ (a.cotensor.obj (op (Δ[0] : SSet.{v}))).obj Y) :
    zeroHomEquiv a X Y' (h ≫ (a.cotensor.obj (op (Δ[0] : SSet.{v}))).map p) =
      zeroHomEquiv a X Y h ≫ p := by
  calc
    _ = (SimplicialCategory.homEquiv' X Y').symm
        (degreeEquiv a X Y' (op ⦋0⦌) (h ≫ (a.cotensor.obj (op (Δ[0] : SSet.{v}))).map p)) := rfl
    _ = (SimplicialCategory.homEquiv' X Y').symm
        ((((SimplicialCategory.sHomFunctor C).obj (op X)).map p).app (op ⦋0⦌)
          (degreeEquiv a X Y (op ⦋0⦌) h)) :=
      congrArg (SimplicialCategory.homEquiv' X Y').symm (degreeEquiv_target a X p (op ⦋0⦌) h)
    _ = (SimplicialCategory.homEquiv' X Y).symm (degreeEquiv a X Y (op ⦋0⦌) h) ≫ p :=
      ordinaryZero_symm_target p _
    _ = _ := rfl

/-- The actual forward degree-zero arrow is the representing image of the original identity. -/
def zeroUnit (Y : C) : Y ⟶ (a.cotensor.obj (op (Δ[0] : SSet.{v}))).obj Y :=
  (zeroHomEquiv a Y Y).symm (𝟙 Y)

/-- The actual inverse degree-zero arrow is the representing evaluation of the original identity. -/
def zeroCounit (Y : C) : (a.cotensor.obj (op (Δ[0] : SSet.{v}))).obj Y ⟶ Y :=
  zeroHomEquiv a _ Y (𝟙 _)

theorem zeroUnit_zeroCounit (Y : C) : zeroUnit a Y ≫ zeroCounit a Y = 𝟙 Y := by
  have h := zeroHomEquiv_source a (zeroUnit a Y)
    (𝟙 ((a.cotensor.obj (op (Δ[0] : SSet.{v}))).obj Y))
  rw [Category.comp_id] at h
  change zeroUnit a Y ≫ zeroHomEquiv a _ Y (𝟙 _) = 𝟙 Y
  rw [← h]
  exact (zeroHomEquiv a Y Y).apply_symm_apply _

theorem zeroCounit_zeroUnit (Y : C) :
    zeroCounit a Y ≫ zeroUnit a Y = 𝟙 ((a.cotensor.obj (op (Δ[0] : SSet.{v}))).obj Y) := by
  apply (zeroHomEquiv a _ Y).injective
  rw [zeroHomEquiv_source]
  change zeroCounit a Y ≫ (zeroHomEquiv a Y Y) ((zeroHomEquiv a Y Y).symm (𝟙 Y)) = _
  rw [Equiv.apply_symm_apply, Category.comp_id]
  rfl

/-- The same actual point cotensor is naturally isomorphic to the original target. -/
def zeroIso (Y : C) : Y ≅ (a.cotensor.obj (op (Δ[0] : SSet.{v}))).obj Y where
  hom := zeroUnit a Y
  inv := zeroCounit a Y
  hom_inv_id := zeroUnit_zeroCounit a Y
  inv_hom_id := zeroCounit_zeroUnit a Y

/-- The entire actual forward degree-zero arrow is natural in every original target morphism. -/
theorem zeroUnit_naturality {Y Y' : C} (p : Y ⟶ Y') :
    p ≫ zeroUnit a Y' = zeroUnit a Y ≫ (a.cotensor.obj (op (Δ[0] : SSet.{v}))).map p := by
  apply (zeroHomEquiv a Y Y').injective
  rw [zeroHomEquiv_source, zeroHomEquiv_target]
  simp only [zeroUnit, Equiv.apply_symm_apply, Category.comp_id, Category.id_comp]

/-- The complete degree-zero natural iso retains the same original cotensor functor. -/
def zeroFunctorIso : 𝟭 C ≅ a.cotensor.obj (op (Δ[0] : SSet.{v})) :=
  NatIso.ofComponents (zeroIso a) (by
    intro Y Y' p
    exact zeroUnit_naturality a p)

end HomotopicalAlgebra.CompatibleCotensorFraming

end
end
end

section



/-!
# Original cotensor coaugmentations and original generated R degree-zero arrows

The actual point cotensor iso followed by the original scalar simplex collapse constructs
the full natural coaugmentation. Applying the same original R retains the original RY
endpoint, degree-zero iso, original unit rY, every original target map, and all structure
weakness. No coaugmentation, weak-constancy, or frame outcome is a premise.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w u v

open CategoryTheory Limits Opposite Simplicial
open scoped SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.CompatibleCotensorFraming

variable {C : Type u} [Category.{v} C] [ModelCategory C] [SimplicialCategory C]
variable (a : CompatibleSimplicialMapping.Action C)

/-- The actual coaugmentation uses the original zero iso and original scalar simplex collapse. -/
def coaugmentation : SimplicialObject.const C ⟶ resolution a where
  app Y :=
    { app n := zeroUnit a Y ≫
        (a.cotensor.map (SSet.StandardSimplexWeakMaps.collapse n.unop).op).app Y
      naturality n m f := by
        change 𝟙 Y ≫ (zeroUnit a Y ≫
            (a.cotensor.map (SSet.StandardSimplexWeakMaps.collapse m.unop).op).app Y) =
          (zeroUnit a Y ≫ (a.cotensor.map (SSet.StandardSimplexWeakMaps.collapse n.unop).op).app Y)
              ≫
            (a.cotensor.map (SSet.stdSimplex.map f.unop).op).app Y
        rw [Category.id_comp, Category.assoc]
        congr 1
        rw [← NatTrans.comp_app, ← Functor.map_comp, ← op_comp,
          SSet.StandardSimplexWeakMaps.map_collapse] }
  naturality Y Y' p := by
    ext n
    change p ≫ (zeroUnit a Y' ≫
        (a.cotensor.map (SSet.StandardSimplexWeakMaps.collapse n.unop).op).app Y') =
      (zeroUnit a Y ≫ (a.cotensor.map (SSet.StandardSimplexWeakMaps.collapse n.unop).op).app Y) ≫
        (a.cotensor.obj (op (SSet.stdSimplex.obj n.unop))).map p
    rw [← Category.assoc, zeroUnit_naturality, Category.assoc, NatTrans.naturality]
    exact (Category.assoc _ _ _).symm

/-- Each actual coaugmentation degree retains both original maps. -/
theorem coaugmentation_app (Y : C) (n : SimplexCategoryᵒᵖ) :
    ((coaugmentation a).app Y).app n = zeroUnit a Y ≫
      (a.cotensor.map (SSet.StandardSimplexWeakMaps.collapse n.unop).op).app Y := rfl

/-- The original coaugmentation is weak at every actual fibrant target. -/
theorem coaugmentation_weak (Y : C) [IsFibrant Y] (n : SimplexCategoryᵒᵖ) :
    WeakEquivalence (((coaugmentation a).app Y).app n) := by
  let _ : IsIso (zeroUnit a Y) := by change IsIso (zeroIso a Y).hom; infer_instance
  let _ : IsCofibrant (SSet.stdSimplex.{v}.obj n.unop) := simplicial_isCofibrant _
  let _ : IsCofibrant (Δ[0] : SSet.{v}) := simplicial_isCofibrant _
  let _ : WeakEquivalence (SSet.StandardSimplexWeakMaps.collapse.{v} n.unop) :=
    SSet.StandardSimplexWeakMaps.collapse_weak n.unop
  let _ : WeakEquivalence
      ((a.cotensor.map (SSet.StandardSimplexWeakMaps.collapse n.unop).op).app Y) :=
    cotensor_map_weak a Y (SSet.StandardSimplexWeakMaps.collapse n.unop)
  change WeakEquivalence (zeroUnit a Y ≫ _)
  infer_instance

variable {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
variable (d : CofibrantGenerationData C κ)

open GeneratedFunctorialReplacements

/-- The original RY is naturally identified with degree zero of the actual cotensor resolution. -/
def originalZeroIso : R d ≅ originalResolution a d ⋙
    (evaluation SimplexCategoryᵒᵖ C).obj (op ⦋0⦌) :=
  NatIso.ofComponents (fun Y => zeroIso a ((R d).obj Y)) (by
    intro Y Y' p
    exact zeroUnit_naturality a ((R d).map p))

/-- The actual degree-zero arrow is the same representing unit at the same original RY. -/
theorem originalZeroIso_hom (Y : C) :
    (originalZeroIso a d).hom.app Y = zeroUnit a ((R d).obj Y) := rfl

/-- The actual inverse degree-zero arrow is the same representing evaluation at original RY. -/
theorem originalZeroIso_inv (Y : C) :
    (originalZeroIso a d).inv.app Y = zeroCounit a ((R d).obj Y) := rfl

/-- The original R functor carries every original target map through the complete coaugmentation. -/
def originalCoaugmentation : R d ⋙ SimplicialObject.const C ⟶ originalResolution a d :=
  Functor.whiskerLeft (R d) (coaugmentation a)

/-- The same original R unit is retained in the complete actual augmented cotensor resolution. -/
def originalAugmentation : SimplicialObject.const C ⟶ originalResolution a d :=
  (SimplicialObject.const C).leftUnitor.inv ≫
    Functor.whiskerRight (unit d) (SimplicialObject.const C) ≫ originalCoaugmentation a d

/-- Each actual original augmentation degree retains the entire original rY arrow. -/
theorem originalAugmentation_app (Y : C) (n : SimplexCategoryᵒᵖ) :
    ((originalAugmentation a d).app Y).app n = (unit d).app Y ≫ zeroUnit a ((R d).obj Y) ≫
      (a.cotensor.map (SSet.StandardSimplexWeakMaps.collapse n.unop).op).app ((R d).obj Y) := by
  change 𝟙 Y ≫ ((unit d).app Y ≫ (zeroUnit a ((R d).obj Y) ≫ _)) = _
  exact Category.id_comp _

/-- Every original RY coaugmentation degree is weak by the genuine fibrancy of the same RY. -/
theorem originalCoaugmentation_weak (Y : C) (n : SimplexCategoryᵒᵖ) :
    WeakEquivalence (((originalCoaugmentation a d).app Y).app n) := by
  let _ : IsFibrant ((R d).obj Y) := R_isFibrant d Y
  exact coaugmentation_weak a _ n

/-- Every original augmented degree is weak, retaining the same original generated rY. -/
theorem originalAugmentation_weak (Y : C) (n : SimplexCategoryᵒᵖ) :
    WeakEquivalence (((originalAugmentation a d).app Y).app n) := by
  let _ : WeakEquivalence ((unit d).app Y) := (weakEquivalence_iff _).mpr (unit_weak d Y)
  let _ : WeakEquivalence (((originalCoaugmentation a d).app Y).app n) :=
    originalCoaugmentation_weak a d Y n
  change WeakEquivalence (𝟙 Y ≫ ((unit d).app Y ≫ _))
  infer_instance

end HomotopicalAlgebra.CompatibleCotensorFraming

end
end
end

section



/-!
# Entire original represented points under the actual compatible cotensor calculation

The whole original constant-Q map and original rY augmented cotensor frame give the
represented right-complex point. Its actual calculation is the entire original mixed
enriched point, retaining q, the input map, and r. Native point Yoneda proves equality
of the entire SSet arrows; no unit or point-compatibility outcome is an input.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w u v

open CategoryTheory Opposite Simplicial
open scoped MonoidalCategory SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.CompatibleCotensorMappingPoints

open CompatibleCotensorFraming GeneratedFunctorialReplacements

variable {C : Type u} [Category.{v} C] [ModelCategory C] [SimplicialCategory C]
variable (a : CompatibleSimplicialMapping.Action C)
variable {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
variable (d : CofibrantGenerationData C κ)

/-- The entire represented point retains the same original q/input/r augmented cotensor morphism. -/
def point {X Y : C} (f : X ⟶ Y) :
    𝟙_ SSet.{v} ⟶ ((originalComplex a d).obj (op X)).obj Y :=
  eHomEquiv SSet ((SimplicialObject.const C).map ((counit d).app X ≫ f) ≫
    (originalAugmentation a d).app Y) ≫
      (ResolutionHomComplex.CanonicalEnrichment.rightIso
        ((Q d).obj X) ((originalResolution a d).obj Y)).inv

/-- Every original simplex of the point retains the entire same original constant-Q and augmentation
word. -/
theorem point_simplex {X Y : C} (f : X ⟶ Y) (n : SimplexCategoryᵒᵖ)
    (t : (𝟙_ SSet.{v}).obj n) :
    (point a d f).app n t = (counit d).app X ≫ f ≫ ((originalAugmentation a d).app Y).app n := by
  change ((SimplicialObject.const C).map ((counit d).app X ≫ f) ≫
    (originalAugmentation a d).app Y).app n = _
  exact Category.assoc _ _ _

/-- The actual zero augmented degree retains the same original rY and point-cotensor unit. -/
theorem augmentation_zero (Y : C) :
    ((originalAugmentation a d).app Y).app (op ⦋0⦌) = (unit d).app Y ≫
        zeroUnit a ((R d).obj Y) := by
  rw [originalAugmentation_app]
  change (unit d).app Y ≫ zeroUnit a ((R d).obj Y) ≫
    (a.cotensor.map (SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0)).op).app ((R d).obj Y) =
        _
  rw [SimplexCategory.const_eq_id, CategoryTheory.Functor.map_id, op_id,
    CategoryTheory.Functor.map_id,
    NatTrans.id_app, Category.comp_id]

/-- The original cotensor calculation carries this entire point to the same original mixed q/input/r
point. -/
theorem point_calculation {X Y : C} (f : X ⟶ Y) :
    point a d f ≫ ((originalCalculation a d).hom.app (op X)).app Y =
      eHomEquiv SSet ((counit d).app X ≫ f ≫ (unit d).app Y) := by
  apply (SimplicialCategory.sHom ((Q d).obj X) ((R d).obj Y)).unitHomEquiv.injective
  change (((originalCalculation a d).hom.app (op X)).app Y).app (op ⦋0⦌)
      ((point a d f).app (op ⦋0⦌) PUnit.unit) =
    SimplicialCategory.homEquiv' ((Q d).obj X) ((R d).obj Y)
      ((counit d).app X ≫ f ≫ (unit d).app Y)
  have hpoint : (point a d f).app (op ⦋0⦌) PUnit.unit =
      (counit d).app X ≫ f ≫ ((unit d).app Y ≫ zeroUnit a ((R d).obj Y)) :=
    (point_simplex a d f (op ⦋0⦌) PUnit.unit).trans
      (congrArg (fun h => (counit d).app X ≫ f ≫ h) (augmentation_zero a d Y))
  have hcal := originalCalculation_hom_app a d X Y (op ⦋0⦌)
    ((point a d f).app (op ⦋0⦌) PUnit.unit)
  apply hcal.trans
  apply (congrArg (fun h => SSet.yonedaEquiv
    (homEquiv a ((Q d).obj X) (Δ[0] : SSet.{v}) ((R d).obj Y) h)) hpoint).trans
  apply (SimplicialCategory.homEquiv' ((Q d).obj X) ((R d).obj Y)).symm.injective
  change zeroHomEquiv a ((Q d).obj X) ((R d).obj Y)
      ((counit d).app X ≫ f ≫ ((unit d).app Y ≫ zeroUnit a ((R d).obj Y))) =
    (SimplicialCategory.homEquiv' ((Q d).obj X) ((R d).obj Y)).symm
      (SimplicialCategory.homEquiv' ((Q d).obj X) ((R d).obj Y)
        ((counit d).app X ≫ f ≫ (unit d).app Y))
  rw [Equiv.symm_apply_apply]
  have h := zeroHomEquiv_source a ((counit d).app X ≫ f ≫ (unit d).app Y)
    (zeroUnit a ((R d).obj Y))
  simpa only [Category.assoc, zeroUnit, Equiv.apply_symm_apply, Category.comp_id] using h

/-- The scalar identity point gives the entire same original mixed replacement unit. -/
theorem unit_calculation (X : C) :
    point a d (𝟙 X) ≫ ((originalCalculation a d).hom.app (op X)).app X =
      GeneratedDerivedMapping.mixedUnit d X := by
  change _ = eHomEquiv SSet ((counit d).app X ≫ (unit d).app X)
  exact (point_calculation a d (𝟙 X)).trans
    (congrArg (fun f : (Q d).obj X ⟶ (R d).obj X => eHomEquiv SSet f)
      (congrArg (fun f => (counit d).app X ≫ f) (Category.id_comp ((unit d).app X))))

end HomotopicalAlgebra.CompatibleCotensorMappingPoints

end
end
end

section



/-!
# The actual finite cotensor matching cone from the original standard boundary

The proved original Reedy face-boundary colimit becomes a limit under the actual
matching/op-latching equivalence. The genuine rotated cotensor right adjoint preserves
that finite limit. Every resulting leg is the original cotensor of the original face leg.
No matching-cone or frame outcome is supplied as a premise.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Limits Opposite Simplicial
open scoped SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.CompatibleCotensorFraming

open ReedyStructure.BoundaryOpposite

/-- The original simplex matching index is the same original opposite face index. -/
@[implicit_reducible]
def simplexMatchingEquivalence (j : SimplexCategory) :
    SimplexCategory.reedyOp.Matching (op j) ≌ (SimplexCategory.reedy.Latching j)ᵒᵖ :=
  equivalence SimplexCategory.reedy j

/-- The original simplex parameter diagram retains the exact original opposite face coefficients. -/
def simplexParameterDiagramIso (j : SimplexCategory) :
    SimplexCategory.reedyOp.matchingDiagram SSet.stdSimplex.{v}.op (op j) ≅
      (simplexMatchingEquivalence j).functor ⋙
        (SimplexCategory.reedy.latchingDiagram SSet.stdSimplex j).op :=
  diagramIso SimplexCategory.reedy SSet.stdSimplex j

/-- The actual original matching parameter cone has the opposite original standard boundary point.
-/
@[implicit_reducible]
def parameterMatchingCone (j : SimplexCategory) :
    Cone (SimplexCategory.reedyOp.matchingDiagram SSet.stdSimplex.{v}.op (op j)) :=
  (Cone.postcompose (simplexParameterDiagramIso j).inv).obj
    ((SSet.StandardSimplexBoundaryColimit.boundaryCocone j).op.whisker
      (simplexMatchingEquivalence j).functor)

/-- The parameter matching limit is derived from the actual proved original face colimit. -/
def parameterMatchingIsLimit (j : SimplexCategory) : IsLimit (parameterMatchingCone.{v} j) :=
  (IsLimit.postcomposeInvEquiv (simplexParameterDiagramIso j)
    ((SSet.StandardSimplexBoundaryColimit.boundaryCocone j).op.whisker
      (simplexMatchingEquivalence j).functor)).symm
    ((SSet.StandardSimplexBoundaryColimit.isColimit j).op.whiskerEquivalence
      (simplexMatchingEquivalence j))

variable {C : Type u} [Category.{v} C] [ModelCategory C] [SimplicialCategory C]
variable (a : CompatibleSimplicialMapping.Action C)

/-- The original proper-face leg with its full original standard-simplex and boundary types. -/
@[implicit_reducible]
def matchingFaceMap (j : SimplexCategory) (b : SimplexCategory.reedyOp.Matching (op j)) :
    SSet.stdSimplex.{v}.obj (SimplexCategory.reedyOp.matchingTarget b).unop ⟶
      (SSet.boundary j.len : SSet.{v}) :=
  (SSet.StandardSimplexBoundaryColimit.boundaryCocone j).ι.app
    ((simplexMatchingEquivalence j).functor.obj b).unop

/-- The original typed face leg keeps the same entire original simplex boundary arrow. -/
theorem matchingFaceMap_ι (j : SimplexCategory) (b : SimplexCategory.reedyOp.Matching (op j)) :
    matchingFaceMap.{v} j b ≫ (SSet.boundary j.len).ι =
      SSet.stdSimplex.map (SimplexCategory.reedyOp.matchingArrow b).unop :=
  SSet.StandardSimplexBoundaryColimit.boundaryCocone_ι
    ((simplexMatchingEquivalence j).functor.obj b).unop

/-- The genuine matching cone is the original cotensor right adjoint's image of that actual limit.
-/
@[implicit_reducible]
def cotensorMatchingCone (Y : C) (j : SimplexCategory) :
    Cone (SimplexCategory.reedyOp.matchingDiagram ((resolution a).obj Y) (op j)) :=
  (cotensorAt a Y).mapCone (parameterMatchingCone j)

/-- The matching cone point is the actual cotensor by the same original standard boundary. -/
theorem cotensorMatchingCone_point (Y : C) (j : SimplexCategory) :
    (cotensorMatchingCone a Y j).pt =
      (a.cotensor.obj (op (SSet.boundary j.len : SSet.{v}))).obj Y := rfl

/-- Every actual matching projection is the cotensor of the same original proper-face leg. -/
theorem cotensorMatchingCone_π_raw (Y : C) (j : SimplexCategory)
    (b : SimplexCategory.reedyOp.Matching (op j)) :
    (cotensorMatchingCone a Y j).π.app b =
      (a.cotensor.map
        ((SSet.StandardSimplexBoundaryColimit.boundaryCocone j).ι.app
          ((simplexMatchingEquivalence j).functor.obj b).unop).op).app Y := by
  exact congrArg (cotensorAt a Y).map
    (Category.comp_id (((SSet.StandardSimplexBoundaryColimit.boundaryCocone j).ι.app
      ((simplexMatchingEquivalence j).functor.obj b).unop).op))

/-- Every matching projection is the same fully typed original cotensor face leg. -/
theorem cotensorMatchingCone_π (Y : C) (j : SimplexCategory)
    (b : SimplexCategory.reedyOp.Matching (op j)) :
    (cotensorMatchingCone a Y j).π.app b =
      (a.cotensor.map (matchingFaceMap.{v} j b).op).app Y :=
  cotensorMatchingCone_π_raw a Y j b

/-- Right-adjoint preservation proves the complete actual matching limit on the original coefficient
diagram. -/
def cotensorMatchingIsLimit (Y : C) (j : SimplexCategory) : IsLimit
    (cotensorMatchingCone a Y j) := by
  letI : PreservesLimitsOfSize.{0, 0} (cotensorAt a Y) :=
    (cotensorAdjunction a Y).rightAdjoint_preservesLimits
  exact isLimitOfPreserves (cotensorAt a Y) (parameterMatchingIsLimit j)

/-- The boundary map has exactly the same original face/projection composite as the matching map. -/
theorem boundaryMap_matching_projection (Y : C) (j : SimplexCategory)
    (b : SimplexCategory.reedyOp.Matching (op j)) :
    (a.cotensor.map (SSet.boundary j.len).ι.op).app Y ≫ (cotensorMatchingCone a Y j).π.app b =
      ((resolution a).obj Y).map (SimplexCategory.reedyOp.matchingArrow b) := by
  rw [cotensorMatchingCone_π, ← NatTrans.comp_app, ← Functor.map_comp, ← op_comp,
    matchingFaceMap_ι]
  rfl

/-- The original matching map to the proved cone is exactly the original cotensor boundary map. -/
theorem matchingMapWith_eq_boundaryMap (Y : C) (j : SimplexCategory) :
    SimplexCategory.reedyOp.matchingMapWith ((resolution a).obj Y) (op j)
      (cotensorMatchingCone a Y j) (cotensorMatchingIsLimit a Y j) =
        (a.cotensor.map (SSet.boundary j.len).ι.op).app Y := by
  apply (cotensorMatchingIsLimit a Y j).hom_ext
  intro b
  rw [SimplexCategory.reedyOp.matchingMapWith_π]
  exact (boundaryMap_matching_projection a Y j b).symm

end HomotopicalAlgebra.CompatibleCotensorFraming

end
end
end

section



/-!
# Genuine finite matching fibrations of the original cotensor frame

The original standard-boundary inclusion is an actual simplicial cofibration. The
actual rotated Quillen right adjoint sends its opposite to a fibration. The proved
original matching cone identifies this same arrow with every canonical or complete
caller matching map, retaining every original projection and original RY endpoint.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w u v

open CategoryTheory Limits Opposite Simplicial
open scoped SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.CompatibleCotensorFraming

variable {C : Type u} [Category.{v} C] [ModelCategory C] [SimplicialCategory C]
variable (a : CompatibleSimplicialMapping.Action C)

/-- The original finite matching object is the actual cotensor of the original standard boundary. -/
def matchingBoundaryIso (Y : C) (j : SimplexCategory) :
    limit (SimplexCategory.reedyOp.matchingDiagram ((resolution a).obj Y) (op j)) ≅
      (cotensorMatchingCone a Y j).pt :=
  ((cotensorMatchingIsLimit a Y j).conePointUniqueUpToIso (limit.isLimit _)).symm

/-- Each inverse canonical projection is the same original cotensor face projection. -/
@[reassoc]
theorem matchingBoundaryIso_inv_π (Y : C) (j : SimplexCategory)
    (b : SimplexCategory.reedyOp.Matching (op j)) :
    (matchingBoundaryIso a Y j).inv ≫
      limit.π (SimplexCategory.reedyOp.matchingDiagram ((resolution a).obj Y) (op j)) b =
        (cotensorMatchingCone a Y j).π.app b :=
  (cotensorMatchingIsLimit a Y j).conePointUniqueUpToIso_hom_comp (limit.isLimit _) b

/-- The original full canonical matching map has the same entire cotensor boundary arrow. -/
theorem matchingMap_eq_boundary (Y : C) (j : SimplexCategory) :
    ReedyStructure.matchingMap SimplexCategory.reedyOp ((resolution a).obj Y) (op j) ≫
      (matchingBoundaryIso a Y j).hom = (a.cotensor.map (SSet.boundary j.len).ι.op).app Y := by
  apply (cancel_mono (matchingBoundaryIso a Y j).inv).mp
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply limit.hom_ext
  intro b
  calc
    _ = ((resolution a).obj Y).map (SimplexCategory.reedyOp.matchingArrow b) :=
      ReedyStructure.matchingMap_π SimplexCategory.reedyOp _ _ b
    _ = (a.cotensor.map (SSet.boundary j.len).ι.op).app Y ≫
        (cotensorMatchingCone a Y j).π.app b := (boundaryMap_matching_projection a Y j b).symm
    _ = _ :=
      (congrArg (fun h => (a.cotensor.map (SSet.boundary j.len).ι.op).app Y ≫ h)
        (matchingBoundaryIso_inv_π a Y j b)).symm.trans
        (Category.assoc _ _ _).symm

/-- The actual original cotensor boundary map is a fibration at every original fibrant target. -/
theorem boundaryMap_fibration (Y : C) [IsFibrant Y] (j : SimplexCategory) :
    fibrations C ((a.cotensor.map (SSet.boundary j.len).ι.op).app Y) := by
  have h : cofibrations SSet.{v} (SSet.boundary j.len).ι := by
    change Mono (SSet.boundary j.len).ι
    infer_instance
  exact cotensor_map_fibration a Y _ h

/-- Every complete caller matching cone retains the same actual matching fibration class. -/
theorem matchingMapWith_fibration (Y : C) [IsFibrant Y] (j : SimplexCategory)
    (c : Cone (SimplexCategory.reedyOp.matchingDiagram ((resolution a).obj Y) (op j)))
    (hc : IsLimit c) :
    fibrations C (SimplexCategory.reedyOp.matchingMapWith ((resolution a).obj Y) (op j) c hc) := by
  let e := (cotensorMatchingIsLimit a Y j).conePointUniqueUpToIso hc
  have hfac : (a.cotensor.map (SSet.boundary j.len).ι.op).app Y ≫ e.hom =
      SimplexCategory.reedyOp.matchingMapWith ((resolution a).obj Y) (op j) c hc := by
    rw [← matchingMapWith_eq_boundaryMap a Y j]
    exact (cotensorMatchingIsLimit a Y j).lift_comp_conePointUniqueUpToIso_hom hc
  rw [← hfac]
  let _ : Fibration e.hom := by infer_instance
  exact (fibrations C).comp_mem _ _ (boundaryMap_fibration a Y j) (mem_fibrations e.hom)

/-- All original finite canonical matching maps of the actual cotensor frame are fibrations. -/
theorem matchingMap_fibration (Y : C) [IsFibrant Y] (j : SimplexCategory) :
    fibrations C
      (ReedyStructure.matchingMap SimplexCategory.reedyOp ((resolution a).obj Y) (op j)) :=
  matchingMapWith_fibration a Y j (limit.cone _) (limit.isLimit _)

variable {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
variable (d : CofibrantGenerationData C κ)

/-- The same original generated RY supplies every actual canonical cotensor-frame matching
fibration. -/
theorem originalMatchingMap_fibration (Y : C) (j : SimplexCategoryᵒᵖ) :
    fibrations C
      (ReedyStructure.matchingMap SimplexCategory.reedyOp ((originalResolution a d).obj Y) j) := by
  let _ : IsFibrant ((GeneratedFunctorialReplacements.R d).obj Y) :=
    GeneratedFunctorialReplacements.R_isFibrant d Y
  exact matchingMap_fibration a _ j.unop

/-- The original complete caller matching cone also retains the same original RY fibration. -/
theorem originalMatchingMapWith_fibration (Y : C) (j : SimplexCategoryᵒᵖ)
    (c : Cone (SimplexCategory.reedyOp.matchingDiagram ((originalResolution a d).obj Y) j))
    (hc : IsLimit c) :
    fibrations C
        (SimplexCategory.reedyOp.matchingMapWith ((originalResolution a d).obj Y) j c hc) := by
  let _ : IsFibrant ((GeneratedFunctorialReplacements.R d).obj Y) :=
    GeneratedFunctorialReplacements.R_isFibrant d Y
  exact matchingMapWith_fibration a _ j.unop c hc

end HomotopicalAlgebra.CompatibleCotensorFraming

end
end
end

section



/-!
# Actual model objects and enriched-Hom fibrancy of compatible cotensor frames

The proved original matching fibrations recognize the actual Reedy model objects.
The same original cofibrant source and fibrant target make the original enriched Hom
fibrant, and its actual Hom-complex iso transports that fibrancy. Independent original
model and replacement choices retain their original cardinals and morphisms.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe wM wR u v

open CategoryTheory Opposite Simplicial
open scoped SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.CompatibleCotensorFraming

variable {C : Type u} [Category.{v} C] [ModelCategory C] [SimplicialCategory C]
variable (a : CompatibleSimplicialMapping.Action C)

/-- The genuine actual right Hom complex is fibrant at the original cofibrant/fibrant endpoints. -/
theorem complex_isFibrant (X Y : C) [IsCofibrant X] [IsFibrant Y] :
    IsFibrant (complex a X Y) := by
  let _ : IsFibrant (SimplicialCategory.sHom X Y) :=
    CompatibleSimplicialMapping.mapping_isFibrant a X Y
  exact isFibrant_of_fibration (complexIso a X Y).hom

variable {κM : Cardinal.{wM}} [Fact κM.IsRegular] [OrderBot κM.ord.ToType]
variable (m : CofibrantGenerationData C κM)

/-- The same actual cotensor simplicial object is fibrant in the independently selected original
Reedy model. -/
theorem resolution_model_isFibrant (Y : C) [IsFibrant Y] :
    letI := GeneratedFramingModels.simplicialModel m
    IsFibrant ((resolution a).obj Y) := by
  apply (GeneratedFramingModels.simplicial_isFibrant_iff m _).mpr
  intro j
  exact (fibration_iff _).mpr (matchingMap_fibration a Y j.unop)

variable {κR : Cardinal.{wR}} [Fact κR.IsRegular] [OrderBot κR.ord.ToType]
variable (d : CofibrantGenerationData C κR)

/-- The same original RY cotensor frame is actually fibrant for independent original
model/replacement choices. -/
theorem originalResolution_model_isFibrant (Y : C) :
    letI := GeneratedFramingModels.simplicialModel m
    IsFibrant ((originalResolution a d).obj Y) := by
  apply (GeneratedFramingModels.simplicial_isFibrant_iff m _).mpr
  intro j
  exact (fibration_iff _).mpr (originalMatchingMap_fibration a d Y j)

/-- The same original generated Q/R Hom complex is a fibrant actual simplicial mapping space. -/
theorem originalComplex_isFibrant (X Y : C) :
    IsFibrant (((originalComplex a d).obj (op X)).obj Y) := by
  let _ : IsCofibrant ((GeneratedFunctorialReplacements.Q d).obj X) :=
    GeneratedFunctorialReplacements.Q_isCofibrant d X
  let _ : IsFibrant ((GeneratedFunctorialReplacements.R d).obj Y) :=
    GeneratedFunctorialReplacements.R_isFibrant d Y
  exact complex_isFibrant a _ _

end HomotopicalAlgebra.CompatibleCotensorFraming

end
end
end
