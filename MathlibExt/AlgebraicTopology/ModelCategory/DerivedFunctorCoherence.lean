/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedReplacementConstruction
public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenDerivedAdjunction
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives

/-!
# Derived functors from the original chosen replacements

The original functorial replacement records determine the complete functors
on the weak localizations. Their map functions and comparison transformations
retain the original Q, R, q and r. Quillen Brown preservation and the native
cofibrant/fibrant derivability structures prove the universal properties.
-/

@[expose] public section

noncomputable section

universe uC uD uE uF uG vC vD vE vF vG

open CategoryTheory Limits MorphismProperty
open CategoryTheory.Functor

namespace HomotopicalAlgebra.DerivedFunctorCoherence

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {D : Type uD} [Category.{vD} D] [ModelCategory D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [adj.IsQuillenAdjunction]

/-- The original canonical weak localization. -/
abbrev projection (C : Type uC) [Category.{vC} C] [ModelCategory C] := (weakEquivalences C).Q

/-- The complete original functor before passing to the source localization. -/
abbrev leftRaw (q : GeneratedFunctorialReplacements.Data (C := C)) : C ⥤ (weakEquivalences
  D).Localization :=
  q.Q ⋙ L ⋙ projection D

/-- The original right functor on every chosen fibrant replacement. -/
abbrev rightRaw (r : GeneratedFunctorialReplacements.Data (C := D)) : D ⥤ (weakEquivalences
  C).Localization :=
  r.R ⋙ R ⋙ projection C

include adj in
/-- Actual Quillen Brown preservation inverts every original weak arrow after Q. -/
theorem leftRaw_inverts (q : GeneratedFunctorialReplacements.Data (C := C)) :
    (weakEquivalences C).IsInvertedBy (leftRaw (L := L) q) := by
  intro X Y f hf
  let : IsCofibrant (q.Q.obj X) := q.q_cofibrant X
  let : IsCofibrant (q.Q.obj Y) := q.q_cofibrant Y
  let : WeakEquivalence (q.Q.map f) := (weakEquivalence_iff _).mpr (q.q_map_weak f hf)
  let : WeakEquivalence (L.map (q.Q.map f)) :=
    Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant (adj := adj) _
  exact Localization.inverts (projection D) (weakEquivalences D) _ (mem_weakEquivalences _)

include adj in
/-- Actual right Quillen Brown preservation inverts the original R-image of every weak arrow. -/
theorem rightRaw_inverts (r : GeneratedFunctorialReplacements.Data (C := D)) :
    (weakEquivalences D).IsInvertedBy (rightRaw (R := R) r) := by
  intro X Y f hf
  let : IsFibrant (r.R.obj X) := r.r_fibrant X
  let : IsFibrant (r.R.obj Y) := r.r_fibrant Y
  let : WeakEquivalence (r.R.map f) := (weakEquivalence_iff _).mpr (r.r_map_weak f hf)
  let : WeakEquivalence (R.map (r.R.map f)) :=
    Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_fibrant (adj := adj) _
  exact Localization.inverts (projection C) (weakEquivalences C) _ (mem_weakEquivalences _)

/-- The complete original chosen left derived functor on all objects and morphisms. -/
def left (q : GeneratedFunctorialReplacements.Data (C := C)) :
    (weakEquivalences C).Localization ⥤ (weakEquivalences D).Localization :=
  Localization.Construction.lift (leftRaw (L := L) q) (leftRaw_inverts adj q)

/-- The complete original chosen right derived functor. -/
def right (r : GeneratedFunctorialReplacements.Data (C := D)) :
    (weakEquivalences D).Localization ⥤ (weakEquivalences C).Localization :=
  Localization.Construction.lift (rightRaw (R := R) r) (rightRaw_inverts adj r)

/-- Projection keeps the entire original Q and left functor. -/
theorem left_projection (q : GeneratedFunctorialReplacements.Data (C := C)) :
    projection C ⋙ left adj q = leftRaw (L := L) q :=
  Localization.Construction.fac _ _

/-- Projection keeps the entire original R and right functor. -/
theorem right_projection (r : GeneratedFunctorialReplacements.Data (C := D)) :
    projection D ⋙ right adj r = rightRaw (R := R) r :=
  Localization.Construction.fac _ _

/-- The literal original represented-map function is preserved by the left derived functor. -/
theorem left_map (q : GeneratedFunctorialReplacements.Data (C := C)) {X Y : C} (f : X ⟶ Y) :
    (left adj q).map ((projection C).map f) = (projection D).map (L.map (q.Q.map f)) :=
  Functor.congr_hom (left_projection adj q) f

/-- The literal original R-map and right-functor map survive the localization. -/
theorem right_map (r : GeneratedFunctorialReplacements.Data (C := D)) {X Y : D} (f : X ⟶ Y) :
    (right adj r).map ((projection D).map f) = (projection C).map (R.map (r.R.map f)) :=
  Functor.congr_hom (right_projection adj r) f

/-- The whole chosen left comparison has the original replacement counit. -/
def leftComparison (q : GeneratedFunctorialReplacements.Data (C := C)) :
    projection C ⋙ left adj q ⟶ L ⋙ projection D :=
  (eqToIso (left_projection adj q)).hom ≫ whiskerRight q.q (L ⋙ projection D) ≫
    (Functor.leftUnitor (L ⋙ projection D)).hom

/-- The whole chosen right comparison has the original replacement unit. -/
def rightComparison (r : GeneratedFunctorialReplacements.Data (C := D)) :
    R ⋙ projection C ⟶ projection D ⋙ right adj r :=
  (Functor.leftUnitor (R ⋙ projection C)).inv ≫ whiskerRight r.r (R ⋙ projection C) ≫
    (eqToIso (right_projection adj r)).inv

/-- Every left comparison component is the original left image of the original q map. -/
theorem leftComparison_app (q : GeneratedFunctorialReplacements.Data (C := C)) (X : C) :
    (leftComparison adj q).app X = (projection D).map (L.map (q.q.app X)) := by
  simp only [leftComparison, NatTrans.comp_app, eqToIso.hom, eqToHom_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app]
  change eqToHom rfl ≫ (projection D).map (L.map (q.q.app X)) = _
  exact Category.id_comp _

/-- Every right comparison component is the original right image of r. -/
theorem rightComparison_app (r : GeneratedFunctorialReplacements.Data (C := D)) (Y : D) :
    (rightComparison adj r).app Y = (projection C).map (R.map (r.r.app Y)) := by
  simp only [rightComparison, NatTrans.comp_app, Functor.leftUnitor_inv_app, Category.id_comp,
    Functor.whiskerRight_app, eqToIso.inv, eqToHom_app]
  change (projection C).map (R.map (r.r.app Y)) ≫ eqToHom rfl = _
  exact Category.comp_id _

include adj in
/-- The original left functor is derivable on the genuine cofibrant subcategory. -/
theorem leftSourceDerives : (CofibrantObject.localizerMorphism C).Derives (L ⋙ projection D) := by
  intro X Y f hf
  let : WeakEquivalence f.hom := by
    rw [← weakEquivalence_iff_of_objectProperty, weakEquivalence_iff]
    exact hf
  let : WeakEquivalence (L.map f.hom) :=
    Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant (adj := adj) _
  exact Localization.inverts (projection D) (weakEquivalences D) (L.map f.hom)
    (mem_weakEquivalences (L.map f.hom))

include adj in
/-- The original right functor is derivable on the genuine fibrant subcategory. -/
theorem rightSourceDerives : (FibrantObject.localizerMorphism D).Derives (R ⋙ projection C) := by
  intro X Y f hf
  let : WeakEquivalence f.hom := by
    rw [← weakEquivalence_iff_of_objectProperty, weakEquivalence_iff]
    exact hf
  let : WeakEquivalence (R.map f.hom) :=
    Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_fibrant (adj := adj) _
  exact Localization.inverts (projection C) (weakEquivalences C) (R.map f.hom)
    (mem_weakEquivalences (R.map f.hom))

/-- The chosen left comparison is invertible at every actual cofibrant object. -/
theorem leftComparison_isIso (q : GeneratedFunctorialReplacements.Data (C := C))
    (X : C) [IsCofibrant X] : IsIso ((leftComparison adj q).app X) := by
  rw [leftComparison_app]
  let : IsCofibrant (q.Q.obj X) := q.q_cofibrant X
  let : IsCofibrant ((𝟭 C).obj X) := inferInstanceAs (IsCofibrant X)
  let : WeakEquivalence (q.q.app X) := (weakEquivalence_iff _).mpr (q.q_trivialFibration X).2
  let : WeakEquivalence (L.map (q.q.app X)) :=
    Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant (adj := adj) _
  exact Localization.inverts (projection D) (weakEquivalences D) _ (mem_weakEquivalences _)

/-- The chosen right comparison is invertible at every original fibrant object. -/
theorem rightComparison_isIso (r : GeneratedFunctorialReplacements.Data (C := D))
    (Y : D) [IsFibrant Y] : IsIso ((rightComparison adj r).app Y) := by
  rw [rightComparison_app]
  let : IsFibrant (r.R.obj Y) := r.r_fibrant Y
  let : IsFibrant ((𝟭 D).obj Y) := inferInstanceAs (IsFibrant Y)
  let : WeakEquivalence (r.r.app Y) := (weakEquivalence_iff _).mpr (r.r_trivialCofibration Y).2
  let : WeakEquivalence (R.map (r.r.app Y)) :=
    Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_fibrant (adj := adj) _
  exact Localization.inverts (projection C) (weakEquivalences C) _ (mem_weakEquivalences _)

/-- The full left universal property follows from the actual source derivability structure. -/
theorem leftIsDerived (q : GeneratedFunctorialReplacements.Data (C := C)) :
    (left adj q).IsLeftDerivedFunctor (leftComparison adj q) (weakEquivalences C) :=
  (leftSourceDerives adj).isLeftDerivedFunctor_of_isIso _ (fun X => leftComparison_isIso adj q
    X.obj)

/-- The full right universal property is constructed from the actual fibrant derivability structure.
-/
theorem rightIsDerived (r : GeneratedFunctorialReplacements.Data (C := D)) :
    (right adj r).IsRightDerivedFunctor (rightComparison adj r) (weakEquivalences D) :=
  (rightSourceDerives adj).isRightDerivedFunctor_of_isIso _ (fun Y => rightComparison_isIso adj r
    Y.obj)

/-- The chosen left derived functor lifts the original Q-composite through weak localization. -/
local instance leftLifting (q : GeneratedFunctorialReplacements.Data (C := C)) :
    Localization.Lifting (projection C) (weakEquivalences C) (leftRaw (L := L) q) (left adj q) :=
  ⟨eqToIso (left_projection adj q)⟩

/-- The chosen right derived functor lifts the original R-composite through weak localization. -/
local instance rightLifting (r : GeneratedFunctorialReplacements.Data (C := D)) :
    Localization.Lifting (projection D) (weakEquivalences D) (rightRaw (R := R) r) (right adj r) :=
  ⟨eqToIso (right_projection adj r)⟩

section NaturalTransformations

variable {L' : C ⥤ D} {R' : D ⥤ C} (adj' : L' ⊣ R') [adj'.IsQuillenAdjunction]

/-- The actual original natural transformation lifts through the same chosen Q functor. -/
def leftNat (q : GeneratedFunctorialReplacements.Data (C := C)) (τ : L ⟶ L') :
    left adj q ⟶ left adj' q :=
  Localization.liftNatTrans (projection C) (weakEquivalences C) _ _ _ _
    (whiskerLeft q.Q (whiskerRight τ (projection D)))

/-- The actual original right natural transformation retains the same chosen R functor. -/
def rightNat (r : GeneratedFunctorialReplacements.Data (C := D)) (τ : R ⟶ R') :
    right adj r ⟶ right adj' r :=
  Localization.liftNatTrans (projection D) (weakEquivalences D) _ _ _ _
    (whiskerLeft r.R (whiskerRight τ (projection C)))

/-- Every projected left component is the original transformation on the chosen replacement. -/
theorem leftNat_app (q : GeneratedFunctorialReplacements.Data (C := C)) (τ : L ⟶ L') (X : C) :
    (leftNat adj adj' q τ).app ((projection C).obj X) = (projection D).map (τ.app (q.Q.obj X)) := by
  rw [leftNat, Localization.liftNatTrans_app]
  simp only [Localization.Lifting.iso, eqToIso.hom, eqToIso.inv, eqToHom_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  change eqToHom rfl ≫ (projection D).map (τ.app (q.Q.obj X)) ≫ eqToHom rfl = _
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- Every original projected right component retains the transformation on R. -/
theorem rightNat_app (r : GeneratedFunctorialReplacements.Data (C := D)) (τ : R ⟶ R') (Y : D) :
    (rightNat adj adj' r τ).app ((projection D).obj Y) = (projection C).map (τ.app (r.R.obj
      Y)) := by
  rw [rightNat, Localization.liftNatTrans_app]
  simp only [Localization.Lifting.iso, eqToIso.hom, eqToIso.inv, eqToHom_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  change eqToHom rfl ≫ (projection C).map (τ.app (r.R.obj Y)) ≫ eqToHom rfl = _
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

end NaturalTransformations

/-- The whole left identity transformation is retained on all localized morphisms. -/
theorem leftNat_id (q : GeneratedFunctorialReplacements.Data (C := C)) :
    leftNat adj adj q (𝟙 L) = 𝟙 (left adj q) := by
  apply Localization.natTrans_ext (projection C) (weakEquivalences C)
  intro X
  rw [leftNat_app]
  exact (projection D).map_id _

/-- The entire right identity transformation is the actual localized identity. -/
theorem rightNat_id (r : GeneratedFunctorialReplacements.Data (C := D)) :
    rightNat adj adj r (𝟙 R) = 𝟙 (right adj r) := by
  apply Localization.natTrans_ext (projection D) (weakEquivalences D)
  intro X
  rw [rightNat_app]
  exact (projection C).map_id _

section NaturalComposition

variable {L' L'' : C ⥤ D} {R' R'' : D ⥤ C}
  (adj' : L' ⊣ R') [adj'.IsQuillenAdjunction] (adj'' : L'' ⊣ R'') [adj''.IsQuillenAdjunction]

/-- All original left natural transformations retain their full vertical composition. -/
theorem leftNat_comp (q : GeneratedFunctorialReplacements.Data (C := C)) (τ : L ⟶ L') (σ : L' ⟶
  L'') :
    leftNat adj adj' q τ ≫ leftNat adj' adj'' q σ = leftNat adj adj'' q (τ ≫ σ) := by
  apply Localization.natTrans_ext (projection C) (weakEquivalences C)
  intro X
  simp only [NatTrans.comp_app, leftNat_app, Functor.map_comp]
  rfl

/-- All original right transformation maps retain the actual vertical composition. -/
theorem rightNat_comp (r : GeneratedFunctorialReplacements.Data (C := D)) (τ : R ⟶ R') (σ : R' ⟶
  R'') :
    rightNat adj adj' r τ ≫ rightNat adj' adj'' r σ = rightNat adj adj'' r (τ ≫ σ) := by
  apply Localization.natTrans_ext (projection D) (weakEquivalences D)
  intro X
  simp only [NatTrans.comp_app, rightNat_app, Functor.map_comp]
  rfl

end NaturalComposition

section Composable

variable {E : Type uE} [Category.{vE} E] [ModelCategory E]
  {M : D ⥤ E} {S : E ⥤ D} (adj₂ : M ⊣ S) [adj₂.IsQuillenAdjunction]
  (qC : GeneratedFunctorialReplacements.Data (C := C))
  (qD : GeneratedFunctorialReplacements.Data (C := D))

/-- Both original chosen intermediate functors are kept in the projected left composite. -/
theorem leftComposite_projection :
    projection C ⋙ (left adj qC ⋙ left adj₂ qD) = qC.Q ⋙ L ⋙ qD.Q ⋙ M ⋙ projection E := by
  change (projection C ⋙ left adj qC) ⋙ left adj₂ qD = _
  rw [left_projection]
  change qC.Q ⋙ L ⋙ (projection D ⋙ left adj₂ qD) = _
  rw [left_projection]

/-- The original q map at the actual intermediate cofibrant object gives the entire raw compositor.
-/
def leftCompositionRaw :
    qC.Q ⋙ L ⋙ qD.Q ⋙ M ⋙ projection E ⟶ qC.Q ⋙ L ⋙ M ⋙ projection E where
  app X := (projection E).map (M.map (qD.q.app (L.obj (qC.Q.obj X))))
  naturality X Y f := by
    have h := qD.q.naturality (L.map (qC.Q.map f))
    have hh := congrArg (fun t => (projection E).map (M.map t)) h
    simpa only [Functor.id_map, Functor.map_comp, Functor.comp_map] using hh

include adj adj₂ in
/-- Actual Quillen preservation proves global invertibility of the original intermediate q
transformation. -/
theorem leftCompositionRaw_isIso : IsIso (leftCompositionRaw (L := L) (M := M) qC qD) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  let : IsCofibrant (qC.Q.obj X) := qC.q_cofibrant X
  let : IsCofibrant (L.obj (qC.Q.obj X)) :=
    Adjunction.IsQuillenAdjunction.preservesCofibrantObjects (adj := adj) inferInstance
  let : IsCofibrant (qD.Q.obj (L.obj (qC.Q.obj X))) := qD.q_cofibrant _
  let : IsCofibrant ((𝟭 D).obj (L.obj (qC.Q.obj X))) := inferInstanceAs (IsCofibrant (L.obj
    (qC.Q.obj X)))
  let : WeakEquivalence (qD.q.app (L.obj (qC.Q.obj X))) :=
    (weakEquivalence_iff _).mpr (qD.q_trivialFibration _).2
  let : WeakEquivalence (M.map (qD.q.app (L.obj (qC.Q.obj X)))) :=
    Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant (adj := adj₂) _
  exact Localization.inverts (projection E) (weakEquivalences E) _ (mem_weakEquivalences _)

/-- The actual full left composition comparison, with both inverse natural transformations. -/
def leftCompositionIso : left adj qC ⋙ left adj₂ qD ≅ left (adj.comp adj₂) qC := by
  let : IsIso (leftCompositionRaw (L := L) (M := M) qC qD) := leftCompositionRaw_isIso adj adj₂
    qC qD
  letI : Localization.Lifting (projection C) (weakEquivalences C)
      (qC.Q ⋙ L ⋙ qD.Q ⋙ M ⋙ projection E) (left adj qC ⋙ left adj₂ qD) :=
    ⟨eqToIso (leftComposite_projection adj adj₂ qC qD)⟩
  letI : Localization.Lifting (projection C) (weakEquivalences C)
      (qC.Q ⋙ L ⋙ M ⋙ projection E) (left (adj.comp adj₂) qC) :=
    ⟨eqToIso (left_projection (adj.comp adj₂) qC)⟩
  exact Localization.liftNatIso (projection C) (weakEquivalences C) _ _ _ _
    (asIso (leftCompositionRaw (L := L) (M := M) qC qD))

/-- Every original projected composition map is exactly the same M-image of the original q map. -/
theorem leftCompositionIso_app (X : C) :
    (leftCompositionIso adj adj₂ qC qD).hom.app ((projection C).obj X) =
      (projection E).map (M.map (qD.q.app (L.obj (qC.Q.obj X)))) := by
  simp only [leftCompositionIso, Localization.liftNatIso_hom, Localization.liftNatTrans_app]
  change (eqToHom (leftComposite_projection adj adj₂ qC qD)).app X ≫
    (projection E).map (M.map (qD.q.app (L.obj (qC.Q.obj X)))) ≫
      (eqToHom (left_projection (adj.comp adj₂) qC).symm).app X = _
  simp only [eqToHom_app]
  change eqToHom rfl ≫ (projection E).map (M.map (qD.q.app (L.obj (qC.Q.obj X)))) ≫ eqToHom rfl = _
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

end Composable

section RightComposable

variable {E : Type uE} [Category.{vE} E] [ModelCategory E]
  {M : D ⥤ E} {S : E ⥤ D} (adj₂ : M ⊣ S) [adj₂.IsQuillenAdjunction]
  (rD : GeneratedFunctorialReplacements.Data (C := D))
  (rE : GeneratedFunctorialReplacements.Data (C := E))

/-- The complete right composite projection retains both original chosen R functors. -/
theorem rightComposite_projection :
    projection E ⋙ (right adj₂ rE ⋙ right adj rD) = rE.R ⋙ S ⋙ rD.R ⋙ R ⋙ projection C := by
  change (projection E ⋙ right adj₂ rE) ⋙ right adj rD = _
  rw [right_projection]
  change rE.R ⋙ S ⋙ (projection D ⋙ right adj rD) = _
  rw [right_projection]

/-- The entire original r map produces the right compositor before source localization. -/
def rightCompositionRaw :
    rE.R ⋙ S ⋙ R ⋙ projection C ⟶ rE.R ⋙ S ⋙ rD.R ⋙ R ⋙ projection C where
  app Y := (projection C).map (R.map (rD.r.app (S.obj (rE.R.obj Y))))
  naturality X Y f := by
    have h := rD.r.naturality (S.map (rE.R.map f))
    have hh := congrArg (fun t => (projection C).map (R.map t)) h
    simpa only [Functor.id_map, Functor.map_comp, Functor.comp_map] using hh

include adj adj₂ in
/-- Both original right Quillen laws make the whole raw r compositor invertible. -/
theorem rightCompositionRaw_isIso : IsIso (rightCompositionRaw (R := R) (S := S) rD rE) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro Y
  let : IsFibrant (rE.R.obj Y) := rE.r_fibrant Y
  let : IsFibrant (S.obj (rE.R.obj Y)) :=
    Adjunction.IsQuillenAdjunction.preservesFibrantObjects (adj := adj₂) inferInstance
  let : IsFibrant (rD.R.obj (S.obj (rE.R.obj Y))) := rD.r_fibrant _
  let : IsFibrant ((𝟭 D).obj (S.obj (rE.R.obj Y))) := inferInstanceAs (IsFibrant (S.obj (rE.R.obj
    Y)))
  let : WeakEquivalence (rD.r.app (S.obj (rE.R.obj Y))) :=
    (weakEquivalence_iff _).mpr (rD.r_trivialCofibration _).2
  let : WeakEquivalence (R.map (rD.r.app (S.obj (rE.R.obj Y)))) :=
    Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_fibrant (adj := adj) _
  exact Localization.inverts (projection C) (weakEquivalences C) _ (mem_weakEquivalences _)

/-- The whole right composition comparison with both original inverse transformations. -/
def rightCompositionIso : right (adj.comp adj₂) rE ≅ right adj₂ rE ⋙ right adj rD := by
  let : IsIso (rightCompositionRaw (R := R) (S := S) rD rE) := rightCompositionRaw_isIso adj adj₂
    rD rE
  letI : Localization.Lifting (projection E) (weakEquivalences E)
      (rE.R ⋙ S ⋙ rD.R ⋙ R ⋙ projection C) (right adj₂ rE ⋙ right adj rD) :=
    ⟨eqToIso (rightComposite_projection adj adj₂ rD rE)⟩
  letI : Localization.Lifting (projection E) (weakEquivalences E)
      (rE.R ⋙ S ⋙ R ⋙ projection C) (right (adj.comp adj₂) rE) :=
    ⟨eqToIso (right_projection (adj.comp adj₂) rE)⟩
  exact Localization.liftNatIso (projection E) (weakEquivalences E) _ _ _ _
    (asIso (rightCompositionRaw (R := R) (S := S) rD rE))

/-- The original projected right comparison is the original R-image of the intermediate r map. -/
theorem rightCompositionIso_app (Y : E) :
    (rightCompositionIso adj adj₂ rD rE).hom.app ((projection E).obj Y) =
      (projection C).map (R.map (rD.r.app (S.obj (rE.R.obj Y)))) := by
  simp only [rightCompositionIso, Localization.liftNatIso_hom, Localization.liftNatTrans_app]
  change (eqToHom (right_projection (adj.comp adj₂) rE)).app Y ≫
    (projection C).map (R.map (rD.r.app (S.obj (rE.R.obj Y)))) ≫
      (eqToHom (rightComposite_projection adj adj₂ rD rE).symm).app Y = _
  simp only [eqToHom_app]
  change eqToHom rfl ≫ (projection C).map (R.map (rD.r.app (S.obj (rE.R.obj Y)))) ≫ eqToHom rfl = _
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

end RightComposable

section Identity

variable (q : GeneratedFunctorialReplacements.Data (C := C))

/-- The original natural q transformation is globally invertible after the original localization. -/
theorem qLocalized_isIso : IsIso (whiskerRight q.q (projection C)) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  exact Localization.inverts (projection C) (weakEquivalences C) (q.q.app X) (q.q_trivialFibration
    X).2

/-- The original natural r transformation is globally invertible after the same localization. -/
theorem rLocalized_isIso : IsIso (whiskerRight q.r (projection C)) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  exact Localization.inverts (projection C) (weakEquivalences C) (q.r.app X) (q.r_trivialCofibration
    X).2

/-- The actual original identity comparison is the localized whole q counit. -/
def leftIdentityIso : left (Adjunction.id (C := C)) q ≅ 𝟭 (weakEquivalences C).Localization := by
  let : IsIso (whiskerRight q.q (projection C)) := qLocalized_isIso q
  letI : Localization.Lifting (projection C) (weakEquivalences C)
      (q.Q ⋙ projection C) (left (Adjunction.id (C := C)) q) := ⟨eqToIso (left_projection
        (Adjunction.id (C := C)) q)⟩
  exact Localization.liftNatIso (projection C) (weakEquivalences C) _ _ _ _
    (asIso (whiskerRight q.q (projection C)) ≪≫ Functor.leftUnitor (projection C))

/-- The actual right identity comparison keeps the whole original r unit and its inverse. -/
def rightIdentityIso : 𝟭 (weakEquivalences C).Localization ≅ right (Adjunction.id (C := C)) q := by
  let : IsIso (whiskerRight q.r (projection C)) := rLocalized_isIso q
  letI : Localization.Lifting (projection C) (weakEquivalences C)
      (q.R ⋙ projection C) (right (Adjunction.id (C := C)) q) := ⟨eqToIso (right_projection
        (Adjunction.id (C := C)) q)⟩
  exact Localization.liftNatIso (projection C) (weakEquivalences C) _ _ _ _
    ((Functor.leftUnitor (projection C)).symm ≪≫ asIso (whiskerRight q.r (projection C)))

/-- The projected left identity is exactly the original q arrow. -/
theorem leftIdentityIso_app (X : C) :
    (leftIdentityIso q).hom.app ((projection C).obj X) = (projection C).map (q.q.app X) := by
  simp only [leftIdentityIso, Localization.liftNatIso_hom, Localization.liftNatTrans_app]
  change (eqToHom (left_projection (Adjunction.id (C := C)) q)).app X ≫
    ((projection C).map (q.q.app X) ≫ 𝟙 _) ≫ (Functor.rightUnitor (projection C)).inv.app X = _
  simp only [eqToHom_app, Functor.rightUnitor_inv_app]
  change eqToHom rfl ≫ ((projection C).map (q.q.app X) ≫ 𝟙 _) ≫ 𝟙 _ = _
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- The projected right identity is the same original r arrow. -/
theorem rightIdentityIso_app (X : C) :
    (rightIdentityIso q).hom.app ((projection C).obj X) = (projection C).map (q.r.app X) := by
  simp only [rightIdentityIso, Localization.liftNatIso_hom, Localization.liftNatTrans_app]
  change (Functor.rightUnitor (projection C)).hom.app X ≫
    (𝟙 _ ≫ (projection C).map (q.r.app X)) ≫ (eqToHom (right_projection (Adjunction.id (C := C))
      q).symm).app X = _
  simp only [Functor.rightUnitor_hom_app, eqToHom_app]
  change 𝟙 _ ≫ (𝟙 _ ≫ (projection C).map (q.r.app X)) ≫ eqToHom rfl = _
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

end Identity

section Postcomposition

variable {E : Type uE} [Category.{vE} E]

/-- Every postcomposition retains the actual chosen left derived comparison and its universal
property. -/
theorem leftPostcomposeIsDerived (q : GeneratedFunctorialReplacements.Data (C := C))
    (H : (weakEquivalences D).Localization ⥤ E) :
    (left adj q ⋙ H).IsLeftDerivedFunctor
      ((Functor.associator (projection C) (left adj q) H).inv ≫ whiskerRight (leftComparison adj
        q) H)
      (weakEquivalences C) := by
  have h : (CofibrantObject.localizerMorphism C).Derives ((L ⋙ projection D) ⋙ H) := by
    intro X Y f hf
    let : IsIso ((projection D).map (L.map f.hom)) :=
      leftSourceDerives adj f hf
    change IsIso (H.map ((projection D).map (L.map f.hom)))
    infer_instance
  apply h.isLeftDerivedFunctor_of_isIso
  intro X
  let : IsIso ((leftComparison adj q).app X.obj) := leftComparison_isIso adj q X.obj
  change IsIso (𝟙 _ ≫ H.map ((leftComparison adj q).app X.obj))
  infer_instance

/-- Every postcomposition keeps the same original right comparison and all its universal maps. -/
theorem rightPostcomposeIsDerived (r : GeneratedFunctorialReplacements.Data (C := D))
    (H : (weakEquivalences C).Localization ⥤ E) :
    (right adj r ⋙ H).IsRightDerivedFunctor
      (whiskerRight (rightComparison adj r) H ≫
        (Functor.associator (projection D) (right adj r) H).hom) (weakEquivalences D) := by
  have h : (FibrantObject.localizerMorphism D).Derives ((R ⋙ projection C) ⋙ H) := by
    intro X Y f hf
    let : IsIso ((projection C).map (R.map f.hom)) :=
      rightSourceDerives adj f hf
    change IsIso (H.map ((projection C).map (R.map f.hom)))
    infer_instance
  apply h.isRightDerivedFunctor_of_isIso
  intro Y
  let : IsIso ((rightComparison adj r).app Y.obj) := rightComparison_isIso adj r Y.obj
  change IsIso (H.map ((rightComparison adj r).app Y.obj) ≫ 𝟙 _)
  infer_instance

end Postcomposition

section Associativity

variable {E : Type uE} [Category.{vE} E] [ModelCategory E]
  {F : Type uF} [Category.{vF} F] [ModelCategory F]
  {M : D ⥤ E} {S : E ⥤ D} (adj₂ : M ⊣ S) [adj₂.IsQuillenAdjunction]
  {N : E ⥤ F} {T : F ⥤ E} (adj₃ : N ⊣ T) [adj₃.IsQuillenAdjunction]
  (qC : GeneratedFunctorialReplacements.Data (C := C))
  (qD : GeneratedFunctorialReplacements.Data (C := D))
  (qE : GeneratedFunctorialReplacements.Data (C := E))

/-- The two full left composition routes agree with the original functor associator retained. -/
theorem left_associativity :
    whiskerRight (leftCompositionIso adj adj₂ qC qD).hom (left adj₃ qE) ≫
        (leftCompositionIso (adj.comp adj₂) adj₃ qC qE).hom =
      (Functor.associator (left adj qC) (left adj₂ qD) (left adj₃ qE)).hom ≫
        whiskerLeft (left adj qC) (leftCompositionIso adj₂ adj₃ qD qE).hom ≫
          (leftCompositionIso adj (adj₂.comp adj₃) qC qD).hom := by
  apply Localization.natTrans_ext (projection C) (weakEquivalences C)
  intro X
  change (left adj₃ qE).map ((leftCompositionIso adj adj₂ qC qD).hom.app ((projection C).obj X)) ≫
      (leftCompositionIso (adj.comp adj₂) adj₃ qC qE).hom.app ((projection C).obj X) =
    𝟙 _ ≫ (leftCompositionIso adj₂ adj₃ qD qE).hom.app ((projection D).obj (L.obj (qC.Q.obj X))) ≫
      (leftCompositionIso adj (adj₂.comp adj₃) qC qD).hom.app ((projection C).obj X)
  rw [leftCompositionIso_app, leftCompositionIso_app, leftCompositionIso_app,
    leftCompositionIso_app, Category.id_comp]
  change (left adj₃ qE).map ((projection E).map (M.map (qD.q.app (L.obj (qC.Q.obj X))))) ≫
      (projection F).map (N.map (qE.q.app (M.obj (L.obj (qC.Q.obj X))))) =
    (projection F).map (N.map (qE.q.app (M.obj (qD.Q.obj (L.obj (qC.Q.obj X)))))) ≫
      (projection F).map (N.map (M.map (qD.q.app (L.obj (qC.Q.obj X)))))
  rw [left_map]
  have hn : qE.Q.map (M.map (qD.q.app (L.obj (qC.Q.obj X)))) ≫ qE.q.app (M.obj (L.obj (qC.Q.obj
    X))) =
      qE.q.app (M.obj (qD.Q.obj (L.obj (qC.Q.obj X)))) ≫ M.map (qD.q.app (L.obj (qC.Q.obj X))) :=
    qE.q.naturality (M.map (qD.q.app (L.obj (qC.Q.obj X))))
  change (projection F).map (N.map (qE.Q.map (M.map (qD.q.app (L.obj (qC.Q.obj X)))))) ≫
      (projection F).map (N.map (qE.q.app (M.obj (L.obj (qC.Q.obj X))))) =
    (projection F).map (N.map (qE.q.app (M.obj (qD.Q.obj (L.obj (qC.Q.obj X)))))) ≫
      (projection F).map (N.map (M.map (qD.q.app (L.obj (qC.Q.obj X)))))
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (fun a => (projection F).map (N.map a)) hn

/-- Both original right compositor routes retain the full associator and the original r naturality
square. -/
theorem right_associativity (rF : GeneratedFunctorialReplacements.Data (C := F)) :
    (rightCompositionIso (adj.comp adj₂) adj₃ qE rF).hom ≫
        whiskerLeft (right adj₃ rF) (rightCompositionIso adj adj₂ qD qE).hom =
      (rightCompositionIso adj (adj₂.comp adj₃) qD rF).hom ≫
        whiskerRight (rightCompositionIso adj₂ adj₃ qE rF).hom (right adj qD) ≫
          (Functor.associator (right adj₃ rF) (right adj₂ qE) (right adj qD)).hom := by
  apply Localization.natTrans_ext (projection F) (weakEquivalences F)
  intro Y
  change (rightCompositionIso (adj.comp adj₂) adj₃ qE rF).hom.app ((projection F).obj Y) ≫
      (rightCompositionIso adj adj₂ qD qE).hom.app ((projection E).obj (T.obj (rF.R.obj Y))) =
    (rightCompositionIso adj (adj₂.comp adj₃) qD rF).hom.app ((projection F).obj Y) ≫
      (right adj qD).map ((rightCompositionIso adj₂ adj₃ qE rF).hom.app ((projection F).obj Y)) ≫
        𝟙 _
  rw [rightCompositionIso_app, rightCompositionIso_app, rightCompositionIso_app,
    rightCompositionIso_app, Category.comp_id]
  change (projection C).map (R.map (S.map (qE.r.app (T.obj (rF.R.obj Y))))) ≫
      (projection C).map (R.map (qD.r.app (S.obj (qE.R.obj (T.obj (rF.R.obj Y)))))) =
    (projection C).map (R.map (qD.r.app (S.obj (T.obj (rF.R.obj Y))))) ≫
      (right adj qD).map ((projection D).map (S.map (qE.r.app (T.obj (rF.R.obj Y)))))
  rw [right_map]
  have hn : S.map (qE.r.app (T.obj (rF.R.obj Y))) ≫ qD.r.app (S.obj (qE.R.obj (T.obj (rF.R.obj
    Y)))) =
      qD.r.app (S.obj (T.obj (rF.R.obj Y))) ≫ qD.R.map (S.map (qE.r.app (T.obj (rF.R.obj Y)))) :=
    qD.r.naturality (S.map (qE.r.app (T.obj (rF.R.obj Y))))
  change (projection C).map (R.map (S.map (qE.r.app (T.obj (rF.R.obj Y))))) ≫
      (projection C).map (R.map (qD.r.app (S.obj (qE.R.obj (T.obj (rF.R.obj Y)))))) =
    (projection C).map (R.map (qD.r.app (S.obj (T.obj (rF.R.obj Y))))) ≫
      (projection C).map (R.map (qD.R.map (S.map (qE.r.app (T.obj (rF.R.obj Y))))))
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (fun a => (projection C).map (R.map a)) hn

end Associativity

section CompositeUniversalMaps

variable {E : Type uE} [Category.{vE} E] [ModelCategory E]
  {M : D ⥤ E} {S : E ⥤ D} (adj₂ : M ⊣ S) [adj₂.IsQuillenAdjunction]
  (qC : GeneratedFunctorialReplacements.Data (C := C))
  (qD : GeneratedFunctorialReplacements.Data (C := D))

/-- The original two left counit comparisons form the full composite universal comparison. -/
def leftCompositeComparison : projection C ⋙ (left adj qC ⋙ left adj₂ qD) ⟶ (L ⋙ M) ⋙ projection
  E :=
  (Functor.associator _ _ _).inv ≫ whiskerRight (leftComparison adj qC) (left adj₂ qD) ≫
    (Functor.associator _ _ _).hom ≫ whiskerLeft L (leftComparison adj₂ qD) ≫
      (Functor.associator _ _ _).inv

/-- The full composite comparison retains the two actual original component maps. -/
theorem leftCompositeComparison_app (X : C) :
    (leftCompositeComparison adj adj₂ qC qD).app X =
      (left adj₂ qD).map ((leftComparison adj qC).app X) ≫ (leftComparison adj₂ qD).app (L.obj
        X) := by
  simp only [leftCompositeComparison, NatTrans.comp_app, Functor.associator_inv_app,
    Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.id_comp, Category.comp_id]

/-- The full left compositor is compatible with the two original universal comparisons. -/
theorem leftComposition_fac_app (X : C) :
    (leftCompositionIso adj adj₂ qC qD).hom.app ((projection C).obj X) ≫
        (leftComparison (adj.comp adj₂) qC).app X =
      (left adj₂ qD).map ((leftComparison adj qC).app X) ≫ (leftComparison adj₂ qD).app (L.obj
        X) := by
  rw [leftCompositionIso_app, leftComparison_app, leftComparison_app, leftComparison_app]
  change (projection E).map (M.map (qD.q.app (L.obj (qC.Q.obj X)))) ≫
      (projection E).map (M.map (L.map (qC.q.app X))) =
    (left adj₂ qD).map ((projection D).map (L.map (qC.q.app X))) ≫
      (projection E).map (M.map (qD.q.app (L.obj X)))
  rw [left_map]
  change (projection E).map (M.map (qD.q.app (L.obj (qC.Q.obj X)))) ≫
      (projection E).map (M.map (L.map (qC.q.app X))) =
    (projection E).map (M.map (qD.Q.map (L.map (qC.q.app X)))) ≫
      (projection E).map (M.map (qD.q.app (L.obj X)))
  have hn : qD.Q.map (L.map (qC.q.app X)) ≫ qD.q.app (L.obj X) =
      qD.q.app (L.obj (qC.Q.obj X)) ≫ L.map (qC.q.app X) := qD.q.naturality (L.map (qC.q.app X))
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (fun a => (projection E).map (M.map a)) hn.symm

/-- The whole left compositor obeys the full original comparison equation. -/
theorem leftComposition_fac :
    whiskerLeft (projection C) (leftCompositionIso adj adj₂ qC qD).hom ≫
        leftComparison (adj.comp adj₂) qC = leftCompositeComparison adj adj₂ qC qD := by
  ext X
  exact (leftComposition_fac_app adj adj₂ qC qD X).trans (leftCompositeComparison_app adj adj₂ qC qD
    X).symm

/-- The whole right compositor retains both source comparison maps in their actual order. -/
theorem rightComposition_fac_app (rE : GeneratedFunctorialReplacements.Data (C := E)) (Y : E) :
    (rightComparison (adj.comp adj₂) rE).app Y ≫
        (rightCompositionIso adj adj₂ qD rE).hom.app ((projection E).obj Y) =
      (rightComparison adj qD).app (S.obj Y) ≫ (right adj qD).map ((rightComparison adj₂ rE).app
        Y) := by
  rw [rightComparison_app, rightCompositionIso_app, rightComparison_app, rightComparison_app]
  change (projection C).map (R.map (S.map (rE.r.app Y))) ≫
      (projection C).map (R.map (qD.r.app (S.obj (rE.R.obj Y)))) =
    (projection C).map (R.map (qD.r.app (S.obj Y))) ≫
      (right adj qD).map ((projection D).map (S.map (rE.r.app Y)))
  rw [right_map]
  change (projection C).map (R.map (S.map (rE.r.app Y))) ≫
      (projection C).map (R.map (qD.r.app (S.obj (rE.R.obj Y)))) =
    (projection C).map (R.map (qD.r.app (S.obj Y))) ≫
      (projection C).map (R.map (qD.R.map (S.map (rE.r.app Y))))
  have hn : S.map (rE.r.app Y) ≫ qD.r.app (S.obj (rE.R.obj Y)) =
      qD.r.app (S.obj Y) ≫ qD.R.map (S.map (rE.r.app Y)) := qD.r.naturality (S.map (rE.r.app Y))
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (fun a => (projection C).map (R.map a)) hn

end CompositeUniversalMaps

section Units

variable (qC : GeneratedFunctorialReplacements.Data (C := C))
  (qD : GeneratedFunctorialReplacements.Data (C := D))

/-- The full left source-unit law is derived by the original universal property, without assuming
Qq=qQ. -/
theorem left_unit_source :
    (leftCompositionIso (Adjunction.id (C := C)) adj qC qC).hom =
      whiskerRight (leftIdentityIso qC).hom (left adj qC) ≫ (Functor.leftUnitor (left adj
        qC)).hom := by
  let : (left adj qC).IsLeftDerivedFunctor (leftComparison adj qC) (weakEquivalences C) :=
    leftIsDerived adj qC
  apply Functor.leftDerived_ext (left adj qC) (leftComparison adj qC) (weakEquivalences C)
  ext X
  change (leftCompositionIso (Adjunction.id (C := C)) adj qC qC).hom.app ((projection C).obj X) ≫
      (leftComparison adj qC).app X =
    ((left adj qC).map ((leftIdentityIso qC).hom.app ((projection C).obj X)) ≫ 𝟙 _) ≫
      (leftComparison adj qC).app X
  rw [leftIdentityIso_app]
  change (leftCompositionIso (Adjunction.id (C := C)) adj qC qC).hom.app ((projection C).obj X) ≫
      (leftComparison adj qC).app X = (left adj qC).map ((projection C).map (qC.q.app X)) ≫
      (leftComparison adj qC).app X
  have hf := leftComposition_fac_app (Adjunction.id (C := C)) adj qC qC X
  change (leftCompositionIso (Adjunction.id (C := C)) adj qC qC).hom.app ((projection C).obj X) ≫
      (leftComparison adj qC).app X = (left adj qC).map ((leftComparison (Adjunction.id (C := C))
        qC).app X) ≫
      (leftComparison adj qC).app X at hf
  rw [leftComparison_app] at hf
  exact hf

/-- The full target-unit law keeps the original intermediate replacement counit. -/
theorem left_unit_target :
    (leftCompositionIso adj (Adjunction.id (C := D)) qC qD).hom =
      whiskerLeft (left adj qC) (leftIdentityIso qD).hom ≫ (Functor.rightUnitor (left adj
        qC)).hom := by
  apply Localization.natTrans_ext (projection C) (weakEquivalences C)
  intro X
  change (leftCompositionIso adj (Adjunction.id (C := D)) qC qD).hom.app ((projection C).obj X) =
    (leftIdentityIso qD).hom.app ((projection D).obj (L.obj (qC.Q.obj X))) ≫ 𝟙 _
  rw [leftIdentityIso_app]
  change (leftCompositionIso adj (Adjunction.id (C := D)) qC qD).hom.app ((projection C).obj X) =
    (projection D).map (qD.q.app (L.obj (qC.Q.obj X))) ≫ 𝟙 _
  exact (leftCompositionIso_app adj (Adjunction.id (C := D)) qC qD X).trans (Category.comp_id
    _).symm

/-- The full right source-unit law follows from the original right universal property. -/
theorem right_unit_source :
    (rightCompositionIso adj (Adjunction.id (C := D)) qD qD).hom =
      (Functor.leftUnitor (right adj qD)).inv ≫ whiskerRight (rightIdentityIso qD).hom (right adj
        qD) := by
  let : (right adj qD).IsRightDerivedFunctor (rightComparison adj qD) (weakEquivalences D) :=
    rightIsDerived adj qD
  apply Functor.rightDerived_ext (right adj qD) (rightComparison adj qD) (weakEquivalences D)
  ext Y
  change (rightComparison adj qD).app Y ≫
      (rightCompositionIso adj (Adjunction.id (C := D)) qD qD).hom.app ((projection D).obj Y) =
    (rightComparison adj qD).app Y ≫
      (𝟙 _ ≫ (right adj qD).map ((rightIdentityIso qD).hom.app ((projection D).obj Y)))
  rw [rightIdentityIso_app]
  change (rightComparison adj qD).app Y ≫
      (rightCompositionIso adj (Adjunction.id (C := D)) qD qD).hom.app ((projection D).obj Y) =
    (rightComparison adj qD).app Y ≫ (right adj qD).map ((projection D).map (qD.r.app Y))
  have hf := rightComposition_fac_app adj (Adjunction.id (C := D)) qD qD Y
  change (rightComparison adj qD).app Y ≫
      (rightCompositionIso adj (Adjunction.id (C := D)) qD qD).hom.app ((projection D).obj Y) =
    (rightComparison adj qD).app Y ≫ (right adj qD).map ((rightComparison (Adjunction.id (C := D))
      qD).app Y) at hf
  rw [rightComparison_app] at hf
  exact hf

/-- The right target-unit law retains the same original localized r map. -/
theorem right_unit_target :
    (rightCompositionIso (Adjunction.id (C := C)) adj qC qD).hom =
      (Functor.rightUnitor (right adj qD)).inv ≫ whiskerLeft (right adj qD) (rightIdentityIso
        qC).hom := by
  apply Localization.natTrans_ext (projection D) (weakEquivalences D)
  intro Y
  change (rightCompositionIso (Adjunction.id (C := C)) adj qC qD).hom.app ((projection D).obj Y) =
    𝟙 _ ≫ (rightIdentityIso qC).hom.app ((projection C).obj (R.obj (qD.R.obj Y)))
  rw [rightIdentityIso_app]
  change (rightCompositionIso (Adjunction.id (C := C)) adj qC qD).hom.app ((projection D).obj Y) =
    𝟙 _ ≫ (projection C).map (qC.r.app (R.obj (qD.R.obj Y)))
  exact (rightCompositionIso_app (Adjunction.id (C := C)) adj qC qD Y).trans (Category.id_comp
    _).symm

end Units

/-- The source unit coherence identifies the two actual Q-replacement paths after the chosen left
functor. -/
theorem left_map_q (q : GeneratedFunctorialReplacements.Data (C := C)) (X : C) :
    (left adj q).map ((projection C).map (q.q.app X)) = (leftComparison adj q).app (q.Q.obj X) := by
  have h := congr_app (left_unit_source adj q) ((projection C).obj X)
  change (leftCompositionIso (Adjunction.id (C := C)) adj q q).hom.app ((projection C).obj X) =
    (left adj q).map ((leftIdentityIso q).hom.app ((projection C).obj X)) ≫ 𝟙 _ at h
  rw [leftCompositionIso_app, leftIdentityIso_app] at h
  change (projection D).map (L.map (q.q.app (q.Q.obj X))) =
    (left adj q).map ((projection C).map (q.q.app X)) at h
  exact h.symm.trans (leftComparison_app adj q (q.Q.obj X)).symm

/-- The source right-unit coherence retains both original R-replacement paths. -/
theorem right_map_r (r : GeneratedFunctorialReplacements.Data (C := D)) (Y : D) :
    (right adj r).map ((projection D).map (r.r.app Y)) = (rightComparison adj r).app (r.R.obj
      Y) := by
  have h := congr_app (right_unit_source adj r) ((projection D).obj Y)
  change (rightCompositionIso adj (Adjunction.id (C := D)) r r).hom.app ((projection D).obj Y) =
    𝟙 _ ≫ (right adj r).map ((rightIdentityIso r).hom.app ((projection D).obj Y)) at h
  rw [rightCompositionIso_app, rightIdentityIso_app] at h
  change (projection C).map (R.map (r.r.app (r.R.obj Y))) =
    (right adj r).map ((projection D).map (r.r.app Y)) at h
  exact h.symm.trans (rightComparison_app adj r (r.R.obj Y)).symm

section Pentagon

variable {E : Type uE} [Category.{vE} E] [ModelCategory E]
  {F : Type uF} [Category.{vF} F] [ModelCategory F]
  {G : Type uG} [Category.{vG} G] [ModelCategory G]
  {M : D ⥤ E} {S : E ⥤ D} (adj₂ : M ⊣ S) [adj₂.IsQuillenAdjunction]
  {N : E ⥤ F} {T : F ⥤ E} (adj₃ : N ⊣ T) [adj₃.IsQuillenAdjunction]
  {P : F ⥤ G} {U : G ⥤ F} (adj₄ : P ⊣ U) [adj₄.IsQuillenAdjunction]
  (qC : GeneratedFunctorialReplacements.Data (C := C))
  (qD : GeneratedFunctorialReplacements.Data (C := D))
  (qE : GeneratedFunctorialReplacements.Data (C := E))
  (qF : GeneratedFunctorialReplacements.Data (C := F))

/-- The complete four-functor left pentagon retains both original associators and all compositor
maps. -/
theorem left_pentagon :
    whiskerRight (whiskerRight (leftCompositionIso adj adj₂ qC qD).hom (left adj₃ qE)) (left adj₄
      qF) ≫
        whiskerRight (leftCompositionIso (adj.comp adj₂) adj₃ qC qE).hom (left adj₄ qF) ≫
          (leftCompositionIso ((adj.comp adj₂).comp adj₃) adj₄ qC qF).hom =
      (Functor.associator (left adj qC ⋙ left adj₂ qD) (left adj₃ qE) (left adj₄ qF)).hom ≫
        (Functor.associator (left adj qC) (left adj₂ qD) (left adj₃ qE ⋙ left adj₄ qF)).hom ≫
          whiskerLeft (left adj qC) (whiskerLeft (left adj₂ qD) (leftCompositionIso adj₃ adj₄ qE
            qF).hom) ≫
            whiskerLeft (left adj qC) (leftCompositionIso adj₂ (adj₃.comp adj₄) qD qE).hom ≫
              (leftCompositionIso adj (adj₂.comp (adj₃.comp adj₄)) qC qD).hom := by
  apply Localization.natTrans_ext (projection C) (weakEquivalences C)
  intro X
  let A := L.obj (qC.Q.obj X)
  let a := qD.q.app A
  let b := qE.q.app (M.obj A)
  let b' := qE.q.app (M.obj (qD.Q.obj A))
  let c := qF.q.app (N.obj (M.obj A))
  let c' := qF.q.app (N.obj (qE.Q.obj (M.obj (qD.Q.obj A))))
  have hE : qE.Q.map (M.map a) ≫ b = b' ≫ M.map a := qE.q.naturality (M.map a)
  have hF : qF.Q.map (N.map (b' ≫ M.map a)) ≫ c = c' ≫ N.map (b' ≫ M.map a) :=
    qF.q.naturality (N.map (b' ≫ M.map a))
  change (left adj₄ qF).map ((left adj₃ qE).map
      ((leftCompositionIso adj adj₂ qC qD).hom.app ((projection C).obj X))) ≫
    (left adj₄ qF).map ((leftCompositionIso (adj.comp adj₂) adj₃ qC qE).hom.app ((projection C).obj
      X)) ≫
      (leftCompositionIso ((adj.comp adj₂).comp adj₃) adj₄ qC qF).hom.app ((projection C).obj X) =
    𝟙 _ ≫ 𝟙 _ ≫
      (leftCompositionIso adj₃ adj₄ qE qF).hom.app ((projection E).obj (M.obj (qD.Q.obj A))) ≫
        (leftCompositionIso adj₂ (adj₃.comp adj₄) qD qE).hom.app ((projection D).obj A) ≫
          (leftCompositionIso adj (adj₂.comp (adj₃.comp adj₄)) qC qD).hom.app ((projection C).obj X)
  rw [leftCompositionIso_app, leftCompositionIso_app, leftCompositionIso_app,
    leftCompositionIso_app, leftCompositionIso_app, leftCompositionIso_app]
  change (left adj₄ qF).map ((left adj₃ qE).map ((projection E).map (M.map a))) ≫
    (left adj₄ qF).map ((projection F).map (N.map b)) ≫ (projection G).map (P.map c) =
      𝟙 _ ≫ 𝟙 _ ≫ (projection G).map (P.map c') ≫
        (projection G).map (P.map (N.map b')) ≫ (projection G).map (P.map (N.map (M.map a)))
  rw [left_map]
  change (left adj₄ qF).map ((projection F).map (N.map (qE.Q.map (M.map a)))) ≫
    (left adj₄ qF).map ((projection F).map (N.map b)) ≫ (projection G).map (P.map c) =
      𝟙 _ ≫ 𝟙 _ ≫ (projection G).map (P.map c') ≫
        (projection G).map (P.map (N.map b')) ≫ (projection G).map (P.map (N.map (M.map a)))
  rw [left_map, left_map]
  change (projection G).map (P.map (qF.Q.map (N.map (qE.Q.map (M.map a))))) ≫
      (projection G).map (P.map (qF.Q.map (N.map b))) ≫ (projection G).map (P.map c) =
    𝟙 _ ≫ 𝟙 _ ≫ (projection G).map (P.map c') ≫
      (projection G).map (P.map (N.map b')) ≫ (projection G).map (P.map (N.map (M.map a)))
  simp only [Category.id_comp]
  have hn : qF.Q.map (N.map (qE.Q.map (M.map a))) ≫ qF.Q.map (N.map b) ≫ c =
      c' ≫ N.map b' ≫ N.map (M.map a) := by
    rw [← Category.assoc, ← Functor.map_comp, ← Functor.map_comp, hE, hF, Functor.map_comp]
  exact by
    simpa only [Functor.map_comp] using congrArg (fun z => (projection G).map (P.map z)) hn

/-- The full right four-functor pentagon keeps the reversed original functors and both whole
associators. -/
theorem right_pentagon (rG : GeneratedFunctorialReplacements.Data (C := G)) :
    (rightCompositionIso ((adj.comp adj₂).comp adj₃) adj₄ qF rG).hom ≫
        whiskerLeft (right adj₄ rG) (rightCompositionIso (adj.comp adj₂) adj₃ qE qF).hom ≫
          whiskerLeft (right adj₄ rG) (whiskerLeft (right adj₃ qF) (rightCompositionIso adj adj₂ qD
            qE).hom) =
      (rightCompositionIso adj (adj₂.comp (adj₃.comp adj₄)) qD rG).hom ≫
        whiskerRight (rightCompositionIso adj₂ (adj₃.comp adj₄) qE rG).hom (right adj qD) ≫
          whiskerRight (whiskerRight (rightCompositionIso adj₃ adj₄ qF rG).hom (right adj₂ qE))
            (right adj qD) ≫
            (Functor.associator (right adj₄ rG ⋙ right adj₃ qF) (right adj₂ qE) (right adj
              qD)).hom ≫
              (Functor.associator (right adj₄ rG) (right adj₃ qF) (right adj₂ qE ⋙ right adj
                qD)).hom := by
  apply Localization.natTrans_ext (projection G) (weakEquivalences G)
  intro Y
  let A := U.obj (rG.R.obj Y)
  let a := qF.r.app A
  let b := qE.r.app (T.obj (qF.R.obj A))
  let b' := qE.r.app (T.obj A)
  let c := qD.r.app (S.obj (qE.R.obj (T.obj (qF.R.obj A))))
  let c' := qD.r.app (S.obj (T.obj A))
  have hE : T.map a ≫ b = b' ≫ qE.R.map (T.map a) := qE.r.naturality (T.map a)
  have hD : S.map (b' ≫ qE.R.map (T.map a)) ≫ c =
      c' ≫ qD.R.map (S.map (b' ≫ qE.R.map (T.map a))) :=
    qD.r.naturality (S.map (b' ≫ qE.R.map (T.map a)))
  change (rightCompositionIso ((adj.comp adj₂).comp adj₃) adj₄ qF rG).hom.app ((projection G).obj
    Y) ≫
      (rightCompositionIso (adj.comp adj₂) adj₃ qE qF).hom.app ((projection F).obj A) ≫
        (rightCompositionIso adj adj₂ qD qE).hom.app ((projection E).obj (T.obj (qF.R.obj A))) =
    (rightCompositionIso adj (adj₂.comp (adj₃.comp adj₄)) qD rG).hom.app ((projection G).obj Y) ≫
      (right adj qD).map ((rightCompositionIso adj₂ (adj₃.comp adj₄) qE rG).hom.app ((projection
        G).obj Y)) ≫
        (right adj qD).map ((right adj₂ qE).map
          ((rightCompositionIso adj₃ adj₄ qF rG).hom.app ((projection G).obj Y))) ≫ 𝟙 _ ≫ 𝟙 _
  rw [rightCompositionIso_app, rightCompositionIso_app, rightCompositionIso_app,
    rightCompositionIso_app, rightCompositionIso_app, rightCompositionIso_app]
  change (projection C).map (R.map (S.map (T.map a))) ≫ (projection C).map (R.map (S.map b)) ≫
      (projection C).map (R.map c) = (projection C).map (R.map c') ≫
        (right adj qD).map ((projection D).map (S.map b')) ≫
          (right adj qD).map ((right adj₂ qE).map ((projection E).map (T.map a))) ≫ 𝟙 _ ≫ 𝟙 _
  rw [right_map]
  change (projection C).map (R.map (S.map (T.map a))) ≫ (projection C).map (R.map (S.map b)) ≫
      (projection C).map (R.map c) = (projection C).map (R.map c') ≫
        (projection C).map (R.map (qD.R.map (S.map b'))) ≫
          (right adj qD).map ((right adj₂ qE).map ((projection E).map (T.map a))) ≫ 𝟙 _ ≫ 𝟙 _
  rw [right_map]
  change (projection C).map (R.map (S.map (T.map a))) ≫ (projection C).map (R.map (S.map b)) ≫
      (projection C).map (R.map c) = (projection C).map (R.map c') ≫
        (projection C).map (R.map (qD.R.map (S.map b'))) ≫
          (right adj qD).map ((projection D).map (S.map (qE.R.map (T.map a)))) ≫ 𝟙 _ ≫ 𝟙 _
  rw [right_map]
  change (projection C).map (R.map (S.map (T.map a))) ≫ (projection C).map (R.map (S.map b)) ≫
      (projection C).map (R.map c) = (projection C).map (R.map c') ≫
        (projection C).map (R.map (qD.R.map (S.map b'))) ≫
          (projection C).map (R.map (qD.R.map (S.map (qE.R.map (T.map a))))) ≫ 𝟙 _ ≫ 𝟙 _
  simp only [Category.comp_id]
  have hn : S.map (T.map a) ≫ S.map b ≫ c =
      c' ≫ qD.R.map (S.map b') ≫ qD.R.map (S.map (qE.R.map (T.map a))) := by
    rw [← Category.assoc, ← Functor.map_comp, hE, hD, Functor.map_comp, Functor.map_comp]
  exact by
    simpa only [Functor.map_comp] using congrArg (fun z => (projection C).map (R.map z)) hn

end Pentagon

end HomotopicalAlgebra.DerivedFunctorCoherence
