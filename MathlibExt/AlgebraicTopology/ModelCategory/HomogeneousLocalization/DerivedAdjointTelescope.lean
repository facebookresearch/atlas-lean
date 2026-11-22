/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.DerivedAdjunctionCoherence
public import MathlibExt.CategoryTheory.Monoidal.HomogeneousLocalization.AdjointTelescope

/-!
# The original beta adjunct and its derived current-stage diagram

The same chosen Q/R factors derive the original Quillen adjunction and the
original beta action.  The derived coaugmentation agrees with the original
point-set adjunct followed by the actual right comparison.  Starting the
original diagram at the chosen fibrant replacement makes every stage
fibrant; the resulting projected diagram is naturally isomorphic to the
whole derived beta diagram, with every transition and source arrow kept.

This comparison does not assert beta locality or a localization property.
It requires no equation between differently ordered coaugmentation powers.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory MorphismProperty
open CategoryTheory.Functor.Iteration
open CategoryTheory.HomogeneousLocalization
open HomotopicalAlgebra.DerivedFunctorCoherence

namespace HomotopicalAlgebra.HomogeneousDerivedAdjointTelescope

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {L T : C ⥤ C} (adj : L ⊣ T) [adj.IsQuillenAdjunction]
  (q r : GeneratedFunctorialReplacements.Data (C := C))
  (b : L ⟶ 𝟭 C)

/-- The derived beta action is the actual Q-lift and the original identity comparison. -/
def beta : left adj q ⟶ 𝟭 (weakEquivalences C).Localization :=
  leftNat adj (Adjunction.id (C := C)) q b ≫ (leftIdentityIso q).hom

/-- Every represented beta map retains the original left comparison and action. -/
theorem beta_projection (X : C) :
    (beta adj q b).app ((projection C).obj X) =
      (leftComparison adj q).app X ≫ (projection C).map (b.app X) := by
  simp only [beta, NatTrans.comp_app, leftNat_app, leftIdentityIso_app, leftComparison_app]
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (fun f => (projection C).map f) (b.naturality (q.q.app X)).symm

/-- The actual derived beta transition uses the same full derived adjunction. -/
def coaugmentation : 𝟭 (weakEquivalences C).Localization ⟶ right adj r :=
  AdjointTelescope.coaugmentation (DerivedAdjunctionCoherence.chosenAdjunction adj q r) (beta adj q b)

/-- The whole derived transition is the original adjunct and its chosen right comparison. -/
theorem coaugmentation_projection (X : C) :
    (coaugmentation adj q r b).app ((projection C).obj X) =
      (projection C).map ((AdjointTelescope.coaugmentation adj b).app X) ≫
        (rightComparison adj r).app X := by
  rw [coaugmentation, AdjointTelescope.coaugmentation_adjunct, beta_projection]
  rw [DerivedAdjunctionCoherence.homEquiv_source_map, AdjointTelescope.coaugmentation_adjunct]

/-- The genuine derived current-stage diagram retains the same original beta action. -/
def derivedDiagramFunctor :
    (weakEquivalences C).Localization ⥤ (ℕ ⥤ (weakEquivalences C).Localization) :=
  AdjointTelescope.diagramFunctor (coaugmentation adj q r b)

/-- The original point-set stages begin at the same chosen fibrant replacement. -/
def stage (n : ℕ) (X : C) : C := (iterate T n).obj (r.R.obj X)

include adj in
/-- Right Quillen preservation proves fibrancy of every actual original stage. -/
theorem stage_fibrant (n : ℕ) (X : C) : IsFibrant (stage (T := T) r n X) :=
  preserves T IsFibrant (Adjunction.IsQuillenAdjunction.preservesFibrantObjects (adj := adj))
    n (r.R.obj X) (r.r_fibrant X)

/-- The original replacement unit is inverted by the original weak localization. -/
instance localizedRUnitIsIso (X : C) : IsIso ((projection C).map (r.r.app X)) :=
  Localization.inverts (projection C) (weakEquivalences C) _ (r.r_trivialCofibration X).2

/-- The comparison keeps each original right comparison and the inverse original R unit. -/
def stageIso : (n : ℕ) → (X : C) →
    (projection C).obj (stage (T := T) r n X) ≅
      (iterate (right adj r) n).obj ((projection C).obj X)
  | 0, X => (asIso ((projection C).map (r.r.app X))).symm
  | n + 1, X => by
    letI : IsFibrant (stage (T := T) r n X) := stage_fibrant adj r n X
    letI : IsIso ((rightComparison adj r).app (stage (T := T) r n X)) :=
      rightComparison_isIso adj r _
    exact asIso ((rightComparison adj r).app (stage (T := T) r n X)) ≪≫
      (right adj r).mapIso (stageIso n X)

/-- The zero comparison is exactly the inverse original localized R unit. -/
theorem stageIso_zero_hom (X : C) :
    (stageIso adj r 0 X).hom = inv ((projection C).map (r.r.app X)) := rfl

/-- The successor comparison keeps the actual right comparison in the original order. -/
theorem stageIso_succ_hom (n : ℕ) (X : C) :
    (stageIso adj r (n + 1) X).hom =
      (rightComparison adj r).app (stage (T := T) r n X) ≫
        (right adj r).map ((stageIso adj r n X).hom) := rfl

/-- Every original module or source arrow survives the entire stage comparison. -/
theorem stageIso_naturality (n : ℕ) {X Y : C} (f : X ⟶ Y) :
    (projection C).map ((iterate T n).map (r.R.map f)) ≫ (stageIso adj r n Y).hom =
      (stageIso adj r n X).hom ≫ (iterate (right adj r) n).map ((projection C).map f) := by
  induction n with
  | zero =>
    change (projection C).map (r.R.map f) ≫ inv ((projection C).map (r.r.app Y)) =
      inv ((projection C).map (r.r.app X)) ≫ (projection C).map f
    apply (cancel_mono ((projection C).map (r.r.app Y))).mp
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    have hr : f ≫ r.r.app Y = r.r.app X ≫ r.R.map f := r.r.naturality f
    rw [← Functor.map_comp, hr, Functor.map_comp, ← Category.assoc,
      IsIso.inv_hom_id, Category.id_comp]
  | succ n ih =>
    change (projection C).map (T.map ((iterate T n).map (r.R.map f))) ≫
        ((rightComparison adj r).app (stage (T := T) r n Y) ≫
          (right adj r).map ((stageIso adj r n Y).hom)) =
      ((rightComparison adj r).app (stage (T := T) r n X) ≫
        (right adj r).map ((stageIso adj r n X).hom)) ≫
          (right adj r).map ((iterate (right adj r) n).map ((projection C).map f))
    have hn : (projection C).map (T.map ((iterate T n).map (r.R.map f))) ≫
        (rightComparison adj r).app (stage (T := T) r n Y) =
      (rightComparison adj r).app (stage (T := T) r n X) ≫
        (right adj r).map ((projection C).map ((iterate T n).map (r.R.map f))) :=
      (rightComparison adj r).naturality ((iterate T n).map (r.R.map f))
    rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp, ih, Functor.map_comp,
      ← Category.assoc]

/-- Every actual beta transition commutes with the whole derived comparison. -/
theorem stageIso_transition (n : ℕ) (X : C) :
    (projection C).map ((AdjointTelescope.coaugmentation adj b).app (stage (T := T) r n X)) ≫
        (stageIso adj r (n + 1) X).hom =
      (stageIso adj r n X).hom ≫
        (coaugmentation adj q r b).app ((iterate (right adj r) n).obj ((projection C).obj X)) := by
  rw [stageIso_succ_hom, ← Category.assoc, ← coaugmentation_projection]
  exact ((coaugmentation adj q r b).naturality ((stageIso adj r n X).hom)).symm

/-- The original point-set diagram with its actual fibrant initial object. -/
def nativeDiagramFunctor : C ⥤ (ℕ ⥤ C) :=
  r.R ⋙ AdjointTelescope.betaDiagramFunctor adj b

/-- All original point-set stages and arrows are projected into the ordinary homotopy category. -/
def projectedDiagramFunctor : C ⥤ (ℕ ⥤ (weakEquivalences C).Localization) :=
  nativeDiagramFunctor adj r b ⋙
    (Functor.whiskeringRight ℕ C (weakEquivalences C).Localization).obj (projection C)

/-- The complete point-set-to-derived diagram map keeps every original transition. -/
def diagramMap (X : C) :
    (projectedDiagramFunctor adj r b).obj X ⟶
      (derivedDiagramFunctor adj q r b).obj ((projection C).obj X) :=
  NatTrans.ofSequence (fun n => (stageIso adj r n X).hom) (fun n => by
    change (projection C).map ((AdjointTelescope.diagram (AdjointTelescope.coaugmentation adj b)
        (r.R.obj X)).map (homOfLE (Nat.le_succ n))) ≫ (stageIso adj r (n + 1) X).hom =
      (stageIso adj r n X).hom ≫
        (AdjointTelescope.diagram (coaugmentation adj q r b) ((projection C).obj X)).map
          (homOfLE (Nat.le_succ n))
    exact (congrArg (fun f => (projection C).map f ≫ (stageIso adj r (n + 1) X).hom)
      (AdjointTelescope.diagram_map_succ _ _ n)).trans
        ((stageIso_transition adj q r b n X).trans
          (congrArg (fun f => (stageIso adj r n X).hom ≫ f)
            (AdjointTelescope.diagram_map_succ _ _ n)).symm))

/-- The actual whole diagram map is invertible, since every original stage comparison is invertible. -/
def diagramIso (X : C) :
    (projectedDiagramFunctor adj r b).obj X ≅
      (derivedDiagramFunctor adj q r b).obj ((projection C).obj X) := by
  letI : IsIso (diagramMap adj q r b X) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro n
    exact inferInstanceAs (IsIso ((stageIso adj r n X).hom))
  exact asIso (diagramMap adj q r b X)

/-- Both diagram directions and every original source map form the same natural isomorphism. -/
def diagramComparison :
    projectedDiagramFunctor adj r b ≅ projection C ⋙ derivedDiagramFunctor adj q r b :=
  NatIso.ofComponents (diagramIso adj q r b) (by
    intro X Y f
    apply NatTrans.ext
    funext n
    exact stageIso_naturality adj r n f)

end HomotopicalAlgebra.HomogeneousDerivedAdjointTelescope
