/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.OriginalInnerDiagonalCoend
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.InnerMapping
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.DiagramScalarAdjunctions
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Inner realization and the cotensor frame adjunction

Inner weighted realization is left adjoint to the simplicial diagram of pointwise cotensors by
standard simplices. The Hom equivalence is constructed from tensor-cotensor transposition on
every coend coefficient, with inverse maps and naturality in both diagram and target variables.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open MonoidalCategory MonoidalClosed
open scoped Simplicial SimplicialSpace.Inner SSet.modelCategoryQuillen

namespace SimplicialSpace.OriginalInnerRealization

private abbrev Presheaves := SimplicialPresheaf.{u} SimplexCategory

private def rawTensorScalarTransformation {K L : SSet.{u}} (j : K ⟶ L) :
    SimplicialPresheaf.scalarTensorFixed (D := SimplexCategory) K ⟶
      SimplicialPresheaf.scalarTensorFixed (D := SimplexCategory) L where
  app A := (SimplicialPresheaf.scalarTensor.obj A).map j
  naturality _ _ f := ((SimplicialPresheaf.scalarTensor.map f).naturality j).symm

/-- The actual contravariant cotensor map is the mate of the original scalar tensor map. -/
private theorem rawCotensorMate_eq {K L : SSet.{u}} (j : K ⟶ L) :
    conjugateEquiv (SimplicialPresheaf.scalarTensorCotensorAdjunction (D := SimplexCategory) L)
        (SimplicialPresheaf.scalarTensorCotensorAdjunction (D := SimplexCategory) K)
        (rawTensorScalarTransformation j) =
      (SimplicialPresheaf.scalarCotensor (D := SimplexCategory)).map j.op := by
  apply NatTrans.ext
  funext Z
  apply
      ((SimplicialPresheaf.scalarTensorCotensorAdjunction (D := SimplexCategory) K).homEquiv _
        Z).symm.injective
  simp only [Adjunction.homEquiv_counit]
  rw [conjugateEquiv_counit]
  ext d : 1
  dsimp only [rawTensorScalarTransformation, SimplicialPresheaf.scalarTensorFixed]
  simp only [NatTrans.comp_app, SimplicialPresheaf.scalarTensorCotensorAdjunction_counit_app]
  change ((ihom L).obj (Z.obj d) ◁ j) ≫
      (β_ L ((ihom L).obj (Z.obj d))).inv ≫ (ihom.ev L).app (Z.obj d) =
    ((pre j).app (Z.obj d) ▷ K) ≫
      (β_ K ((ihom K).obj (Z.obj d))).inv ≫ (ihom.ev K).app (Z.obj d)
  rw [BraidedCategory.braiding_inv_naturality_right_assoc,
    BraidedCategory.braiding_inv_naturality_left_assoc]
  exact congrArg (fun g => (β_ K ((ihom L).obj (Z.obj d))).inv ≫ g)
    (id_tensor_pre_app_comp_ev j (Z.obj d)).symm

/-- Scalar transposition retains its actual contravariant cotensor map and both adjunction
counits. -/
theorem rawScalarTransposition {K L : SSet.{u}} (j : K ⟶ L)
    (X Z : SimplicialPresheaf.{u} SimplexCategory)
    (b : (SimplicialPresheaf.scalarTensorFixed L).obj X ⟶ Z) :
    (SimplicialPresheaf.scalarTensorCotensorAdjunction K).homEquiv X Z
        ((SimplicialPresheaf.scalarTensor.obj X).map j ≫ b) =
      (SimplicialPresheaf.scalarTensorCotensorAdjunction L).homEquiv X Z b ≫
        ((SimplicialPresheaf.scalarCotensor.map j.op).app Z) := by
  let A := SimplicialPresheaf.scalarTensorCotensorAdjunction (D := SimplexCategory) K
  let B := SimplicialPresheaf.scalarTensorCotensorAdjunction (D := SimplexCategory) L
  let t := rawTensorScalarTransformation j
  let b' := B.homEquiv X Z b
  have mate := conjugateEquiv_counit B A t Z
  rw [rawCotensorMate_eq] at mate
  apply (A.homEquiv X Z).symm.injective
  rw [Equiv.symm_apply_apply]
  have hbc : (B.homEquiv X Z).symm b' =
      (SimplicialPresheaf.scalarTensorFixed L).map b' ≫ B.counit.app Z :=
    B.homEquiv_counit X Z b'
  have hb : (SimplicialPresheaf.scalarTensorFixed L).map b' ≫ B.counit.app Z = b :=
    hbc.symm.trans ((B.homEquiv X Z).symm_apply_apply b)
  change t.app X ≫ b = (A.homEquiv X Z).symm
    (b' ≫ (SimplicialPresheaf.scalarCotensor.map j.op).app Z)
  rw [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    mate, ← Category.assoc, t.naturality b', Category.assoc, hb]

/-- Transport the actual native pointwise scalar cotensor through the designated original
carrier. -/
def innerCotensorBifunctor : SSet.{u}ᵒᵖ ⥤ SimplicialSpace.{u} ⥤ SimplicialSpace.{u} :=
  SimplicialPresheaf.scalarCotensor (D := SimplexCategory) ⋙
    (Functor.whiskeringLeft SimplicialSpace.{u} Presheaves Presheaves).obj forget ⋙
    (Functor.whiskeringRight SimplicialSpace.{u} Presheaves SimplicialSpace.{u}).obj
        ofSimplicialObject

/-- The candidate right adjoint is the complete simplicial cotensor diagram of the actual inner
frame. -/
def innerRealizationRightFunctor : SimplicialSpace.{u} ⥤ SimplicialObject SimplicialSpace.{u} :=
  (SSet.stdSimplex.op ⋙ innerCotensorBifunctor).flip

/-- Every right-adjoint value is the actual original pointwise inner cotensor, not an outer
power. -/
theorem innerRealizationRightFunctor_obj (Z : SimplicialSpace.{u}) (m : SimplexCategoryᵒᵖ) :
    (innerRealizationRightFunctor.obj Z).obj m =
      (innerCotensor (SSet.stdSimplex.obj m.unop)).obj Z := rfl

/-- The actual weighted coend is a functor on the entire original coefficient diagram. -/
def innerRealizationFunctor : SimplicialObject SimplicialSpace.{u} ⥤ SimplicialSpace.{u} :=
  (Functor.whiskeringRight SimplexCategoryᵒᵖ SimplicialSpace.{u}
      (SimplexCategory ⥤ SimplicialSpace.{u})).obj
      (innerTensorBifunctor ⋙
        (Functor.whiskeringLeft SimplexCategory SSet.{u} SimplicialSpace.{u}).obj SSet.stdSimplex) ⋙
    coendFunctor SimplexCategory SimplicialSpace.{u}

/-- Transpose every actual coend inclusion by the original coefficient tensor/cotensor
adjunction. -/
def coendTranspose {X : SimplicialObject SimplicialSpace.{u}} {Z : SimplicialSpace.{u}}
    (a : innerRealization X ⟶ Z) : X ⟶ innerRealizationRightFunctor.obj Z where
  app m := InducedCategory.homMk
    ((SimplicialPresheaf.scalarTensorCotensorAdjunction (SSet.stdSimplex.obj m.unop)).homEquiv
      (X.obj m).diagram Z.diagram ((coend.ι (innerRealizationBifunctor X) m.unop ≫ a).hom))
  naturality m n f := by
    apply InducedCategory.hom_ext
    let K := SSet.stdSimplex.obj n.unop
    let L := SSet.stdSimplex.obj m.unop
    let j : K ⟶ L := SSet.stdSimplex.map f.unop
    let A := SimplicialPresheaf.scalarTensorCotensorAdjunction (D := SimplexCategory) K
    let B := SimplicialPresheaf.scalarTensorCotensorAdjunction (D := SimplexCategory) L
    let a' : coend (innerRealizationBifunctor X) ⟶ Z := a
    let bn : (SimplicialPresheaf.scalarTensorFixed K).obj (X.obj n).diagram ⟶ Z.diagram :=
      (coend.ι (innerRealizationBifunctor X) n.unop ≫ a').hom
    let bm : (SimplicialPresheaf.scalarTensorFixed L).obj (X.obj m).diagram ⟶ Z.diagram :=
      (coend.ι (innerRealizationBifunctor X) m.unop ≫ a').hom
    change (X.map f).hom ≫ A.homEquiv (X.obj n).diagram Z.diagram bn =
      B.homEquiv (X.obj m).diagram Z.diagram bm ≫
        (SimplicialPresheaf.scalarCotensor.map j.op).app Z.diagram
    rw [← rawScalarTransposition j, ← A.homEquiv_naturality_left]
    apply (A.homEquiv (X.obj m).diagram Z.diagram).symm.injective
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    have relation : (SimplicialPresheaf.scalarTensorFixed K).map ((X.map f).hom) ≫
          (coend.ι (innerRealizationBifunctor X) n.unop).hom =
        (SimplicialPresheaf.scalarTensor.obj (X.obj m).diagram).map j ≫
          (coend.ι (innerRealizationBifunctor X) m.unop).hom :=
      congrArg (fun t => t.hom) (coend.condition (innerRealizationBifunctor X) f.unop)
    have hp : (SimplicialPresheaf.scalarTensorFixed K).map ((X.map f).hom) ≫ bn =
        (SimplicialPresheaf.scalarTensor.obj (X.obj m).diagram).map j ≫ bm := by
      change (SimplicialPresheaf.scalarTensorFixed K).map ((X.map f).hom) ≫
          ((coend.ι (innerRealizationBifunctor X) n.unop).hom ≫ a'.hom) =
        (SimplicialPresheaf.scalarTensor.obj (X.obj m).diagram).map j ≫
          ((coend.ι (innerRealizationBifunctor X) m.unop).hom ≫ a'.hom)
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun t => t ≫ a'.hom) relation).trans (Category.assoc _ _ _))
    exact hp

/-- The original inverse transposition on each complete coend coefficient. -/
def coendUntransposeComponent {X : SimplicialObject SimplicialSpace.{u}} {Z : SimplicialSpace.{u}}
    (b : X ⟶ innerRealizationRightFunctor.obj Z) (m : SimplexCategory) :
    ((innerRealizationBifunctor X).obj (op m)).obj m ⟶ Z :=
  InducedCategory.homMk
    (((SimplicialPresheaf.scalarTensorCotensorAdjunction (SSet.stdSimplex.obj m)).homEquiv
      (X.obj (op m)).diagram Z.diagram).symm ((b.app (op m)).hom))

/-- Full diagram naturality gives the exact cowedge relation for the inverse components. -/
theorem coendUntransposeComponent_condition {X : SimplicialObject SimplicialSpace.{u}}
    {Z : SimplicialSpace.{u}} (b : X ⟶ innerRealizationRightFunctor.obj Z)
    {i j : SimplexCategory} (f : i ⟶ j) :
    ((innerRealizationBifunctor X).map f.op).app i ≫ coendUntransposeComponent b i =
      ((innerRealizationBifunctor X).obj (op j)).map f ≫ coendUntransposeComponent b j := by
  apply InducedCategory.hom_ext
  let K := SSet.stdSimplex.{u}.obj i
  let L := SSet.stdSimplex.{u}.obj j
  let A := SimplicialPresheaf.scalarTensorCotensorAdjunction (D := SimplexCategory) K
  let B := SimplicialPresheaf.scalarTensorCotensorAdjunction (D := SimplexCategory) L
  let bi : (X.obj (op i)).diagram ⟶
      (SimplicialPresheaf.scalarCotensor.obj (op K)).obj Z.diagram := (b.app (op i)).hom
  let bj : (X.obj (op j)).diagram ⟶
      (SimplicialPresheaf.scalarCotensor.obj (op L)).obj Z.diagram := (b.app (op j)).hom
  let c : (SimplicialPresheaf.scalarTensor.obj (X.obj (op j)).diagram).obj
      (SSet.stdSimplex.obj j) ⟶ Z.diagram :=
    (B.homEquiv (X.obj (op j)).diagram Z.diagram).symm bj
  change (SimplicialPresheaf.scalarTensorFixed K).map ((X.map f.op).hom) ≫
      (A.homEquiv (X.obj (op i)).diagram Z.diagram).symm bi =
    (SimplicialPresheaf.scalarTensor.obj (X.obj (op j)).diagram).map (SSet.stdSimplex.map f) ≫ c
  apply (A.homEquiv (X.obj (op j)).diagram Z.diagram).injective
  have hleft : A.homEquiv (X.obj (op j)).diagram Z.diagram
        ((SimplicialPresheaf.scalarTensorFixed K).map ((X.map f.op).hom) ≫
          (A.homEquiv (X.obj (op i)).diagram Z.diagram).symm bi) =
      (X.map f.op).hom ≫ bi := by
    rw [A.homEquiv_naturality_left, Equiv.apply_symm_apply]
  have hscalar := rawScalarTransposition (SSet.stdSimplex.map f)
    (X.obj (op j)).diagram Z.diagram c
  have hcancel : B.homEquiv (X.obj (op j)).diagram Z.diagram c = bj :=
    (B.homEquiv (X.obj (op j)).diagram Z.diagram).apply_symm_apply bj
  have hright : A.homEquiv (X.obj (op j)).diagram Z.diagram
        ((SimplicialPresheaf.scalarTensor.obj (X.obj (op j)).diagram).map
          (SSet.stdSimplex.map f) ≫ c) =
      bj ≫ (SimplicialPresheaf.scalarCotensor.map (SSet.stdSimplex.map f).op).app Z.diagram :=
    hscalar.trans (congrArg
      (fun t => t ≫
          (SimplicialPresheaf.scalarCotensor.map (SSet.stdSimplex.map f).op).app Z.diagram)
      hcancel)
  have hn : (X.map f.op).hom ≫ bi =
      bj ≫ (SimplicialPresheaf.scalarCotensor.map (SSet.stdSimplex.map f).op).app Z.diagram :=
    congrArg (fun t => t.hom) (b.naturality f.op)
  exact hleft.trans (hn.trans hright.symm)

/-- The inverse map is the actual native coend descent of all original coefficient components. -/
def coendUntranspose {X : SimplicialObject SimplicialSpace.{u}} {Z : SimplicialSpace.{u}}
    (b : X ⟶ innerRealizationRightFunctor.obj Z) : innerRealization X ⟶ Z :=
  coend.desc (coendUntransposeComponent b) (fun {_ _} f => coendUntransposeComponent_condition b f)

/-- Every original coefficient is recovered by the actual universal descent. -/
theorem coendUntranspose_inclusion {X : SimplicialObject SimplicialSpace.{u}}
    {Z : SimplicialSpace.{u}}
    (b : X ⟶ innerRealizationRightFunctor.obj Z) (m : SimplexCategory) :
    coend.ι (innerRealizationBifunctor X) m ≫ coendUntranspose b = coendUntransposeComponent b m :=
  coend.ι_desc _ _ m

/-- Both transpositions give the whole original coend morphism back, by all coefficient
inclusions. -/
theorem coendUntranspose_transpose {X : SimplicialObject SimplicialSpace.{u}}
    {Z : SimplicialSpace.{u}}
    (a : innerRealization X ⟶ Z) : coendUntranspose (coendTranspose a) = a := by
  apply coend.hom_ext
  intro m
  rw [coendUntranspose_inclusion]
  apply InducedCategory.hom_ext
  exact ((SimplicialPresheaf.scalarTensorCotensorAdjunction (SSet.stdSimplex.obj m)).homEquiv
    (X.obj (op m)).diagram Z.diagram).symm_apply_apply _

/-- The inverse then forward transposition retains every full original diagram component. -/
theorem coendTranspose_untranspose {X : SimplicialObject SimplicialSpace.{u}}
    {Z : SimplicialSpace.{u}}
    (b : X ⟶ innerRealizationRightFunctor.obj Z) : coendTranspose (coendUntranspose b) = b := by
  apply NatTrans.ext
  funext m
  apply InducedCategory.hom_ext
  let A := SimplicialPresheaf.scalarTensorCotensorAdjunction (D := SimplexCategory)
    (SSet.stdSimplex.obj m.unop)
  change A.homEquiv (X.obj m).diagram Z.diagram
      ((coend.ι (innerRealizationBifunctor X) m.unop ≫ coendUntranspose b).hom) =
    (b.app m).hom
  rw [coendUntranspose_inclusion]
  exact (A.homEquiv (X.obj m).diagram Z.diagram).apply_symm_apply _

/-- The full coend/cotensor Hom equivalence is constructed from the actual two inverse
transpositions. -/
def innerRealizationHomEquiv (X : SimplicialObject SimplicialSpace.{u}) (Z : SimplicialSpace.{u}) :
    (innerRealization X ⟶ Z) ≃ (X ⟶ innerRealizationRightFunctor.obj Z) where
  toFun := coendTranspose
  invFun := coendUntranspose
  left_inv := coendUntranspose_transpose
  right_inv := coendTranspose_untranspose

/-- Source naturality is the same original coefficient map, through every coend inclusion. -/
theorem innerRealizationHomEquiv_naturality_left_symm
    {X' X : SimplicialObject SimplicialSpace.{u}} (f : X' ⟶ X) (Z : SimplicialSpace.{u})
    (b : X ⟶ innerRealizationRightFunctor.obj Z) :
    innerRealizationFunctor.map f ≫ (innerRealizationHomEquiv X Z).symm b =
      (innerRealizationHomEquiv X' Z).symm (f ≫ b) := by
  let g : coend (innerRealizationBifunctor X) ⟶ Z := coendUntranspose b
  let g' : coend (innerRealizationBifunctor X') ⟶ Z := coendUntranspose (f ≫ b)
  change coend.map (innerRealizationBifunctorMap f) ≫ g = g'
  apply coend.hom_ext
  intro m
  have hg : coend.ι (innerRealizationBifunctor X) m ≫ g = coendUntransposeComponent b m :=
    coendUntranspose_inclusion b m
  have hg' : coend.ι (innerRealizationBifunctor X') m ≫ g' =
      coendUntransposeComponent (f ≫ b) m := coendUntranspose_inclusion (f ≫ b) m
  rw [coend.ι_map_assoc, hg, hg']
  apply InducedCategory.hom_ext
  let A := SimplicialPresheaf.scalarTensorCotensorAdjunction (D := SimplexCategory)
    (SSet.stdSimplex.obj m)
  change (SimplicialPresheaf.scalarTensorFixed (SSet.stdSimplex.obj m)).map
        ((f.app (op m)).hom) ≫
      (A.homEquiv (X.obj (op m)).diagram Z.diagram).symm ((b.app (op m)).hom) =
    (A.homEquiv (X'.obj (op m)).diagram Z.diagram).symm
      ((f.app (op m)).hom ≫ (b.app (op m)).hom)
  exact (A.homEquiv_naturality_left_symm ((f.app (op m)).hom) ((b.app (op m)).hom)).symm

/-- Target naturality retains the actual pointwise cotensor target map in every original degree. -/
theorem innerRealizationHomEquiv_naturality_right
    (X : SimplicialObject SimplicialSpace.{u}) {Z Z' : SimplicialSpace.{u}}
    (p : Z ⟶ Z') (a : innerRealization X ⟶ Z) :
    innerRealizationHomEquiv X Z' (a ≫ p) =
      innerRealizationHomEquiv X Z a ≫ innerRealizationRightFunctor.map p := by
  apply NatTrans.ext
  funext m
  apply InducedCategory.hom_ext
  let A := SimplicialPresheaf.scalarTensorCotensorAdjunction (D := SimplexCategory)
    (SSet.stdSimplex.obj m.unop)
  let a' : coend (innerRealizationBifunctor X) ⟶ Z := a
  change A.homEquiv (X.obj m).diagram Z'.diagram
      (((coend.ι (innerRealizationBifunctor X) m.unop ≫ a').hom) ≫ p.hom) =
    A.homEquiv (X.obj m).diagram Z.diagram
        ((coend.ι (innerRealizationBifunctor X) m.unop ≫ a').hom) ≫
      (SimplicialPresheaf.scalarCotensor.obj (op (SSet.stdSimplex.obj m.unop))).map p.hom
  exact A.homEquiv_naturality_right
    ((coend.ι (innerRealizationBifunctor X) m.unop ≫ a').hom) p.hom

/-- The actual INNER weighted coend is left adjoint to the original scalar cotensor frame
diagram. -/
def innerRealizationAdjunction : innerRealizationFunctor.{u} ⊣ innerRealizationRightFunctor :=
  Adjunction.mkOfHomEquiv
    { homEquiv := innerRealizationHomEquiv
      homEquiv_naturality_left_symm := fun f b =>
          (innerRealizationHomEquiv_naturality_left_symm f _ b).symm
      homEquiv_naturality_right := fun a p => innerRealizationHomEquiv_naturality_right _ p a }

end SimplicialSpace.OriginalInnerRealization
