/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.DerivedFunctorCoherence
public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenOrdinaryHoHom

/-!
# The full derived adjunction for the original chosen replacements

All four derived conditions are proved from the original model and Quillen
functors. The resulting adjunction retains the original comparison maps and
the source unit and counit equations on every represented arrow.
-/

@[expose] public section

noncomputable section

universe uC uD uE vC vD vE

open CategoryTheory MorphismProperty Functor
open HomotopicalAlgebra.DerivedFunctorCoherence

namespace HomotopicalAlgebra.DerivedAdjunctionCoherence

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {D : Type uD} [Category.{vD} D] [ModelCategory D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [adj.IsQuillenAdjunction]
  (q : GeneratedFunctorialReplacements.Data (C := C))
  (r : GeneratedFunctorialReplacements.Data (C := D))

/-- The actual derived adjunction and all four proved universal properties for the chosen Q/R
records. -/
def chosenDerivedAdjunctionData : QuillenDerivedAdjunctionData adj := by
  let α := leftComparison adj q
  let β := rightComparison adj r
  let : (left adj q).IsLeftDerivedFunctor α (weakEquivalences C) := leftIsDerived adj q
  let : (right adj r).IsRightDerivedFunctor β (weakEquivalences D) := rightIsDerived adj r
  let hLR := leftPostcomposeIsDerived adj q (right adj r)
  let hRL := rightPostcomposeIsDerived adj r (left adj q)
  let : (left adj q ⋙ right adj r).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ whiskerRight α (right adj r)) (weakEquivalences C) := hLR
  let : (right adj r ⋙ left adj q).IsRightDerivedFunctor
      (whiskerRight β (left adj q) ≫ (Functor.associator _ _ _).hom) (weakEquivalences D) := hRL
  exact
    { leftDerived := left adj q
      rightDerived := right adj r
      leftComparison := α
      rightComparison := β
      leftIsDerived := inferInstance
      rightIsDerived := inferInstance
      leftCompositeIsDerived := hLR
      rightCompositeIsDerived := hRL
      adjunction := adj.derived (weakEquivalences C) (weakEquivalences D) α β }

/-- The complete original chosen left and right functors form the actual full derived adjunction. -/
abbrev chosenAdjunction : left adj q ⊣ right adj r :=
  (chosenDerivedAdjunctionData adj q r).adjunction

/-- The whole derived unit retains the original source unit and both actual comparison
transformations. -/
theorem unit_fac (X : C) :
    (chosenAdjunction adj q r).unit.app ((projection C).obj X) ≫
      (right adj r).map ((leftComparison adj q).app X) =
    (projection C).map (adj.unit.app X) ≫ (rightComparison adj r).app (L.obj X) := by
  let : (left adj q ⋙ right adj r).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ whiskerRight (leftComparison adj q) (right adj r))
      (weakEquivalences C) := leftPostcomposeIsDerived adj q (right adj r)
  exact adj.derivedη_fac_app (weakEquivalences C) (leftComparison adj q) (rightComparison adj r) X

/-- The whole derived counit retains the same original source counit and both chosen comparisons. -/
theorem counit_fac (Y : D) :
    (left adj q).map ((rightComparison adj r).app Y) ≫
      (chosenAdjunction adj q r).counit.app ((projection D).obj Y) =
    (leftComparison adj q).app (R.obj Y) ≫ (projection D).map (adj.counit.app Y) := by
  let : (right adj r ⋙ left adj q).IsRightDerivedFunctor
      (whiskerRight (rightComparison adj r) (left adj q) ≫ (Functor.associator _ _ _).hom)
      (weakEquivalences D) := rightPostcomposeIsDerived adj r (left adj q)
  exact adj.derivedε_fac_app (weakEquivalences D) (leftComparison adj q) (rightComparison adj r) Y

/-- The actual full derived Hom equivalence on every pair of localization objects. -/
abbrev homEquiv (X : (weakEquivalences C).Localization) (Y : (weakEquivalences D).Localization) :
    ((left adj q).obj X ⟶ Y) ≃ (X ⟶ (right adj r).obj Y) :=
  (chosenAdjunction adj q r).homEquiv X Y

/-- Every represented original adjunct is preserved by the same derived unit and comparison maps. -/
theorem homEquiv_source_map (X : C) (Y : D) (f : L.obj X ⟶ Y) :
    homEquiv adj q r ((projection C).obj X) ((projection D).obj Y)
      ((leftComparison adj q).app X ≫ (projection D).map f) =
    (projection C).map (adj.homEquiv X Y f) ≫ (rightComparison adj r).app Y := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc, unit_fac, Category.assoc]
  have hn : (projection C).map (R.map f) ≫ (rightComparison adj r).app Y =
      (rightComparison adj r).app (L.obj X) ≫ (right adj r).map ((projection D).map f) :=
    (rightComparison adj r).naturality f
  change (projection C).map (adj.unit.app X) ≫
      ((rightComparison adj r).app (L.obj X) ≫ (right adj r).map ((projection D).map f)) = _
  rw [← hn, ← Category.assoc, ← Functor.map_comp]
  rfl

/-- Every inverse original adjunct keeps the same chosen left comparison and derived counit. -/
theorem homEquiv_source_map_symm (X : C) (Y : D) (g : X ⟶ R.obj Y) :
    (homEquiv adj q r ((projection C).obj X) ((projection D).obj Y)).symm
      ((projection C).map g ≫ (rightComparison adj r).app Y) =
    (leftComparison adj q).app X ≫ (projection D).map ((adj.homEquiv X Y).symm g) := by
  apply (homEquiv adj q r ((projection C).obj X) ((projection D).obj Y)).injective
  rw [Equiv.apply_symm_apply, homEquiv_source_map, Equiv.apply_symm_apply]

/-- The original ordinary-Ho adjunction is evaluated on the actual chosen cofibrant and fibrant
objects. -/
def originalHomEquiv (X : C) (Y : D) :
    ((projection D).obj (L.obj (q.Q.obj X)) ⟶ (projection D).obj (r.R.obj Y)) ≃
      ((projection C).obj (q.Q.obj X) ⟶ (projection C).obj (R.obj (r.R.obj Y))) := by
  let : IsCofibrant (q.Q.obj X) := q.q_cofibrant X
  let : IsFibrant (r.R.obj Y) := r.r_fibrant Y
  exact QuillenOrdinaryHoHom.homEquiv adj _ _

/-- The complete derived Hom function agrees with both original replacements and the full
ordinary-Ho transpose. -/
theorem homEquiv_original (X : C) (Y : D)
    (f : (left adj q).obj ((projection C).obj X) ⟶ (projection D).obj Y) :
    (projection C).map (q.q.app X)
      ≫ homEquiv adj q r ((projection C).obj X) ((projection D).obj Y) f =
      originalHomEquiv adj q r X Y (f ≫ (projection D).map (r.r.app Y)) := by
  let : IsCofibrant (q.Q.obj X) := q.q_cofibrant X
  let : IsCofibrant (L.obj (q.Q.obj X)) :=
    Adjunction.IsQuillenAdjunction.preservesCofibrantObjects (adj := adj) inferInstance
  let : IsFibrant (r.R.obj Y) := r.r_fibrant Y
  let : IsIso ((rightComparison adj r).app (r.R.obj Y)) := rightComparison_isIso adj r _
  obtain ⟨g, hg⟩ := map_surjective_of_isLocalization (projection D)
    (L.obj (q.Q.obj X)) (r.R.obj Y) (f ≫ (projection D).map (r.r.app Y))
  apply (cancel_mono ((rightComparison adj r).app (r.R.obj Y))).mp
  have ho : originalHomEquiv adj q r X Y ((projection D).map g) =
      (projection C).map (adj.homEquiv (q.Q.obj X) (r.R.obj Y) g) :=
    QuillenOrdinaryHoHom.homEquiv_map adj _ _ g
  rw [hg] at ho
  have hl : (leftComparison adj q).app (q.Q.obj X) ≫ (projection D).map g =
      (left adj q).map ((projection C).map (q.q.app X)) ≫ (f ≫ (projection D).map (r.r.app Y)) :=
    congrArg₂ (fun a b => a ≫ b) (left_map_q adj q X).symm hg
  calc
    ((projection C).map (q.q.app X) ≫
        homEquiv adj q r ((projection C).obj X) ((projection D).obj Y) f) ≫
          (rightComparison adj r).app (r.R.obj Y) =
        (projection C).map (q.q.app X) ≫
          (homEquiv adj q r ((projection C).obj X) ((projection D).obj Y) f ≫
            (right adj r).map ((projection D).map (r.r.app Y))) := by
      exact (Category.assoc _ _ _).trans
        (congrArg (fun z => (projection C).map (q.q.app X) ≫
          (homEquiv adj q r ((projection C).obj X) ((projection D).obj Y) f ≫ z))
            (right_map_r adj r Y).symm)
    _ = (projection C).map (q.q.app X) ≫
        homEquiv adj q r ((projection C).obj X) ((projection D).obj (r.R.obj Y))
          (f ≫ (projection D).map (r.r.app Y)) :=
      congrArg (fun z => (projection C).map (q.q.app X) ≫ z)
        ((chosenAdjunction adj q r).homEquiv_naturality_right f
          ((projection D).map (r.r.app Y))).symm
    _ = homEquiv adj q r ((projection C).obj (q.Q.obj X)) ((projection D).obj (r.R.obj Y))
        ((left adj q).map ((projection C).map (q.q.app X)) ≫
          (f ≫ (projection D).map (r.r.app Y))) :=
      ((chosenAdjunction adj q r).homEquiv_naturality_left ((projection C).map (q.q.app X))
        (f ≫ (projection D).map (r.r.app Y))).symm
    _ = (projection C).map (adj.homEquiv (q.Q.obj X) (r.R.obj Y) g) ≫
        (rightComparison adj r).app (r.R.obj Y) :=
      (congrArg (homEquiv adj q r ((projection C).obj (q.Q.obj X))
        ((projection D).obj (r.R.obj Y))) hl).symm.trans
        (homEquiv_source_map adj q r (q.Q.obj X) (r.R.obj Y) g)
    _ = originalHomEquiv adj q r X Y (f ≫ (projection D).map (r.r.app Y)) ≫
        (rightComparison adj r).app (r.R.obj Y) :=
      congrArg (fun z => z ≫ (rightComparison adj r).app (r.R.obj Y)) ho.symm

/-- The entire inverse derived Hom function retains the same two original maps and inverse
ordinary adjunct. -/
theorem homEquiv_original_symm (X : C) (Y : D)
    (g : (projection C).obj X ⟶ (right adj r).obj ((projection D).obj Y)) :
    (homEquiv adj q r ((projection C).obj X) ((projection D).obj Y)).symm g ≫
        (projection D).map (r.r.app Y) =
      (originalHomEquiv adj q r X Y).symm ((projection C).map (q.q.app X) ≫ g) := by
  apply (originalHomEquiv adj q r X Y).injective
  exact ((homEquiv_original adj q r X Y _).symm.trans
    (congrArg (fun z => (projection C).map (q.q.app X) ≫ z)
      ((homEquiv adj q r ((projection C).obj X) ((projection D).obj Y)).apply_symm_apply g))).trans
        ((originalHomEquiv adj q r X Y).apply_symm_apply _).symm

section CompositionMates

variable {E : Type uE} [Category.{vE} E] [ModelCategory E]
  {M : D ⥤ E} {S : E ⥤ D} (adj₂ : M ⊣ S) [adj₂.IsQuillenAdjunction]
  (s : GeneratedFunctorialReplacements.Data (C := E))

/-- Both original compositors preserve the entire derived unit on all source-localization objects.
-/
theorem composition_unit_mate :
    ((chosenAdjunction adj q r).comp (chosenAdjunction adj₂ r s)).unit ≫
        whiskerRight (leftCompositionIso adj adj₂ q r).hom (right adj₂ s ⋙ right adj r) =
      (chosenAdjunction (adj.comp adj₂) q s).unit ≫
        whiskerLeft (left (adj.comp adj₂) q) (rightCompositionIso adj adj₂ r s).hom := by
  let A := left adj q
  let B := right adj r
  let A₂ := left adj₂ r
  let B₂ := right adj₂ s
  let A₃ := left (adj.comp adj₂) q
  let B₃ := right (adj.comp adj₂) s
  let α := leftComparison (adj.comp adj₂) q
  let c := (leftCompositionIso adj adj₂ q r).hom
  let d := (rightCompositionIso adj adj₂ r s).hom
  let : (A₃ ⋙ (B₂ ⋙ B)).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ whiskerRight α (B₂ ⋙ B)) (weakEquivalences C) :=
    leftPostcomposeIsDerived (adj.comp adj₂) q (B₂ ⋙ B)
  apply Functor.leftDerived_ext (A₃ ⋙ (B₂ ⋙ B))
    ((Functor.associator _ _ _).inv ≫ whiskerRight α (B₂ ⋙ B)) (weakEquivalences C)
  ext X
  let Z := (projection C).obj X
  let a := (leftComparison adj q).app X
  let b := (leftComparison adj₂ r).app (L.obj X)
  let u₁ := (chosenAdjunction adj q r).unit.app Z
  let u₂ := (chosenAdjunction adj₂ r s).unit.app (A.obj Z)
  have hη : a ≫ (chosenAdjunction adj₂ r s).unit.app ((projection D).obj (L.obj X)) =
      u₂ ≫ B₂.map (A₂.map a) := (chosenAdjunction adj₂ r s).unit.naturality a
  have hβ : (projection C).map (R.map (adj₂.unit.app (L.obj X))) ≫
      (rightComparison adj r).app (S.obj (M.obj (L.obj X))) =
    (rightComparison adj r).app (L.obj X) ≫ B.map ((projection D).map (adj₂.unit.app (L.obj X))) :=
      (rightComparison adj r).naturality (adj₂.unit.app (L.obj X))
  have hL : c.app Z ≫ α.app X = A₂.map a ≫ b := leftComposition_fac_app adj adj₂ q r X
  have hR : (rightComparison (adj.comp adj₂) s).app (M.obj (L.obj X)) ≫
      d.app ((projection E).obj (M.obj (L.obj X))) =
    (rightComparison adj r).app (S.obj (M.obj (L.obj X))) ≫
      B.map ((rightComparison adj₂ s).app (M.obj (L.obj X))) :=
        rightComposition_fac_app adj adj₂ r s (M.obj (L.obj X))
  have hd : B₃.map (α.app X) ≫ d.app ((projection E).obj (M.obj (L.obj X))) =
      d.app (A₃.obj Z) ≫ B.map (B₂.map (α.app X)) := d.naturality (α.app X)
  change (((chosenAdjunction adj q r).comp (chosenAdjunction adj₂ r s)).unit.app Z ≫
      B.map (B₂.map (c.app Z))) ≫ (𝟙 _ ≫ B.map (B₂.map (α.app X))) =
    ((chosenAdjunction (adj.comp adj₂) q s).unit.app Z ≫ d.app (A₃.obj Z)) ≫
      (𝟙 _ ≫ B.map (B₂.map (α.app X)))
  simp only [Category.id_comp]
  have hleft : (((chosenAdjunction adj q r).comp (chosenAdjunction adj₂ r s)).unit.app Z ≫
      B.map (B₂.map (c.app Z))) ≫ B.map (B₂.map (α.app X)) =
    (projection C).map (adj.unit.app X) ≫ (projection C).map (R.map (adj₂.unit.app (L.obj X))) ≫
      (rightComparison adj r).app (S.obj (M.obj (L.obj X))) ≫
        B.map ((rightComparison adj₂ s).app (M.obj (L.obj X))) := by
    rw [Adjunction.comp_unit_app]
    change ((u₁ ≫ B.map u₂) ≫ B.map (B₂.map (c.app Z))) ≫ B.map (B₂.map (α.app X)) = _
    conv_lhs =>
      simp only [Category.assoc]
      rw [← B.map_comp (B₂.map (c.app Z)) (B₂.map (α.app X)), ← B₂.map_comp (c.app Z) (α.app X), hL]
      rw [B₂.map_comp (A₂.map a) b, B.map_comp]
      rw [← Category.assoc (B.map u₂) (B.map (B₂.map (A₂.map a))) (B.map (B₂.map b))]
      rw [← B.map_comp u₂ (B₂.map (A₂.map a)), ← hη, B.map_comp]
    change u₁ ≫ (B.map a
      ≫ B.map ((chosenAdjunction adj₂ r s).unit.app ((projection D).obj (L.obj X)))) ≫
      B.map (B₂.map b) = _
    conv_lhs => simp only [Category.assoc]
    rw [← Category.assoc u₁ (B.map a), unit_fac]
    change ((projection C).map (adj.unit.app X) ≫ (rightComparison adj r).app (L.obj X)) ≫
      B.map ((chosenAdjunction adj₂ r s).unit.app ((projection D).obj (L.obj X)))
        ≫ B.map (B₂.map b) = _
    conv_lhs =>
      simp only [Category.assoc]
      rw [← B.map_comp, unit_fac adj₂ r s (L.obj X), B.map_comp]
      rw [← Category.assoc ((rightComparison adj r).app (L.obj X)), ← hβ]
      simp only [Category.assoc]
  have hright : ((chosenAdjunction (adj.comp adj₂) q s).unit.app Z ≫ d.app (A₃.obj Z)) ≫
      B.map (B₂.map (α.app X)) =
    (projection C).map (adj.unit.app X) ≫ (projection C).map (R.map (adj₂.unit.app (L.obj X))) ≫
      (rightComparison adj r).app (S.obj (M.obj (L.obj X))) ≫
        B.map ((rightComparison adj₂ s).app (M.obj (L.obj X))) := by
    rw [Category.assoc, ← hd, ← Category.assoc, unit_fac]
    change ((projection C).map ((adj.comp adj₂).unit.app X) ≫
      (rightComparison (adj.comp adj₂) s).app (M.obj (L.obj X))) ≫
        d.app ((projection E).obj (M.obj (L.obj X))) = _
    rw [Category.assoc, hR, Adjunction.comp_unit_app, Functor.map_comp, Category.assoc]
  exact hleft.trans hright.symm

/-- The full derived Hom adjunction commutes with both original composition comparison functions. -/
theorem composition_hom_mate (X : (weakEquivalences C).Localization)
  (Y : (weakEquivalences E).Localization)
    (f : (left (adj.comp adj₂) q).obj X ⟶ Y) :
    (((chosenAdjunction adj q r).comp (chosenAdjunction adj₂ r s)).homEquiv X Y)
        ((leftCompositionIso adj adj₂ q r).hom.app X ≫ f) =
      homEquiv (adj.comp adj₂) q s X Y f ≫ (rightCompositionIso adj adj₂ r s).hom.app Y := by
  let B := right adj₂ s ⋙ right adj r
  let G := right (adj.comp adj₂) s
  let c := (leftCompositionIso adj adj₂ q r).hom
  let d := (rightCompositionIso adj adj₂ r s).hom
  have hu : ((chosenAdjunction adj q r).comp (chosenAdjunction adj₂ r s)).unit.app X
    ≫ B.map (c.app X) =
      (chosenAdjunction (adj.comp adj₂) q s).unit.app X ≫ d.app ((left (adj.comp adj₂) q).obj X) :=
    congr_app (composition_unit_mate adj q r adj₂ s) X
  have hn : G.map f ≫ d.app Y = d.app ((left (adj.comp adj₂) q).obj X) ≫ B.map f := d.naturality f
  calc
    (((chosenAdjunction adj q r).comp (chosenAdjunction adj₂ r s)).homEquiv X Y) (c.app X ≫ f) =
        (((chosenAdjunction adj q r).comp (chosenAdjunction adj₂ r s)).unit.app X
          ≫ B.map (c.app X)) ≫
          B.map f := by rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
    _ = ((chosenAdjunction (adj.comp adj₂) q s).unit.app X
      ≫ d.app ((left (adj.comp adj₂) q).obj X)) ≫
        B.map f := congrArg (fun z => z ≫ B.map f) hu
    _ = ((chosenAdjunction (adj.comp adj₂) q s).unit.app X ≫ G.map f) ≫ d.app Y :=
      (Category.assoc _ _ _).trans ((congrArg
        (fun z => (chosenAdjunction (adj.comp adj₂) q s).unit.app X ≫ z)
        hn.symm).trans (Category.assoc _ _ _).symm)
    _ = homEquiv (adj.comp adj₂) q s X Y f ≫ d.app Y :=
      congrArg (fun z => z ≫ d.app Y)
        ((chosenAdjunction (adj.comp adj₂) q s).homEquiv_unit X Y f).symm

/-- Both original compositors preserve the entire derived counit on every target-localization
object. -/
theorem composition_counit_mate :
    whiskerRight (rightCompositionIso adj adj₂ r s).hom (left adj q ⋙ left adj₂ r) ≫
        ((chosenAdjunction adj q r).comp (chosenAdjunction adj₂ r s)).counit =
      whiskerLeft (right (adj.comp adj₂) s) (leftCompositionIso adj adj₂ q r).hom ≫
        (chosenAdjunction (adj.comp adj₂) q s).counit := by
  ext Y
  let A := left adj q ⋙ left adj₂ r
  let G := right (adj.comp adj₂) s
  let c := (leftCompositionIso adj adj₂ q r).hom
  let d := (rightCompositionIso adj adj₂ r s).hom
  let ε := ((chosenAdjunction adj q r).comp (chosenAdjunction adj₂ r s)).counit.app Y
  let ε' := (chosenAdjunction (adj.comp adj₂) q s).counit.app Y
  apply (((chosenAdjunction adj q r).comp (chosenAdjunction adj₂ r s)).homEquiv (G.obj Y)
    Y).injective
  change (((chosenAdjunction adj q r).comp (chosenAdjunction adj₂ r s)).homEquiv (G.obj Y) Y)
      (A.map (d.app Y) ≫ ε) =
    (((chosenAdjunction adj q r).comp (chosenAdjunction adj₂ r s)).homEquiv (G.obj Y) Y)
      (c.app (G.obj Y) ≫ ε')
  have hc : (((chosenAdjunction adj q r).comp (chosenAdjunction adj₂ r s)).homEquiv _ Y) ε = 𝟙 _ :=
    (congrArg (((chosenAdjunction adj q r).comp (chosenAdjunction adj₂ r s)).homEquiv _ Y)
      (((chosenAdjunction adj q r).comp (chosenAdjunction adj₂ r s)).homEquiv_symm_id Y)).symm.trans
        ((((chosenAdjunction adj q r).comp (chosenAdjunction adj₂ r s)).homEquiv
          _ Y).apply_symm_apply _)
  have hc' : homEquiv (adj.comp adj₂) q s (G.obj Y) Y ε' = 𝟙 _ :=
    (congrArg (homEquiv (adj.comp adj₂) q s (G.obj Y) Y)
      ((chosenAdjunction (adj.comp adj₂) q s).homEquiv_symm_id Y)).symm.trans
        ((homEquiv (adj.comp adj₂) q s (G.obj Y) Y).apply_symm_apply _)
  calc
    (((chosenAdjunction adj q r).comp (chosenAdjunction adj₂ r s)).homEquiv (G.obj Y) Y)
        (A.map (d.app Y) ≫ ε) = d.app Y ≫ 𝟙 _ :=
      (((chosenAdjunction adj q r).comp (chosenAdjunction adj₂ r s)).homEquiv_naturality_left
        (d.app Y) ε).trans
        (congrArg (fun z => d.app Y ≫ z) hc)
    _ = 𝟙 _ ≫ d.app Y := (Category.comp_id _).trans (Category.id_comp _).symm
    _ = homEquiv (adj.comp adj₂) q s (G.obj Y) Y ε' ≫ d.app Y :=
      congrArg (fun z => z ≫ d.app Y) hc'.symm
    _ = (((chosenAdjunction adj q r).comp (chosenAdjunction adj₂ r s)).homEquiv (G.obj Y) Y)
        (c.app (G.obj Y) ≫ ε') := (composition_hom_mate adj q r adj₂ s (G.obj Y) Y ε').symm

end CompositionMates

end HomotopicalAlgebra.DerivedAdjunctionCoherence
