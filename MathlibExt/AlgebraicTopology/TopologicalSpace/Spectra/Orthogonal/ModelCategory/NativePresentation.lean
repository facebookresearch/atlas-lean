/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.CanonicalProjectiveModels
import MathlibExt.CategoryTheory.MorphismProperty.AdjointFamilyReindex
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.NativeOperatorIndex

/-!
# Actual orthogonal native operator presentation APIs

Degree evaluation, free objects, full coend actions and their naturality use
the proved native operator index. The actual original δ and block-swapped ν
maps expose isometry and sphere actions. No right-module reconstruction,
zero-sphere comparison, source-model dictionary or mapping-space replacement
is supplied here.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra MorphismProperty
open scoped MonoidalClosed CGWH.modelCategory

namespace PointedCGWH.Spectra.Orthogonal.NativePresentation

open CategoryTheory.Spectra

/-- The canonical full native operator-functor carrier, with its concrete presentation accessors. -/
abbrev Carrier := PointedCGWH.Spectra.Orthogonal.Spectrum.{u, v}

/-- Every original dimension labels its exact native operator object. -/
theorem ofIndex_surjective : Function.Surjective (OrthogonalOperatorIndex.ofIndex.{u, v}) := by
  intro x
  rcases x with ⟨n⟩
  exact ⟨n, rfl⟩

/-- Evaluation at the original dimension in the actual native carrier. -/
def evaluation (n : OrthogonalIndex) : Carrier.{u, v} ⥤ PointedCGWH.{u, v} :=
  EnrichedFunctorCat.evaluation (OrthogonalOperatorIndex.ofIndex.{u, v} n)

/-- The actual original dimension level, retaining its native topology. -/
abbrev level (F : Carrier.{u, v}) (n : OrthogonalIndex) : PointedCGWH.{u, v} :=
  F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n)

/-- The whole original unit-graded transformation component at a dimension. -/
abbrev levelMap {F G : Carrier.{u, v}} (f : F ⟶ G) (n : OrthogonalIndex) :
    level F n ⟶ level G n :=
  EnrichedFunctorCat.component f (OrthogonalOperatorIndex.ofIndex.{u, v} n)

/-- The complete native coend Hom acts on the original dimension levels. -/
def fullAction (F : Carrier.{u, v}) (n k : OrthogonalIndex) :
    level F n ⊗ OrthogonalOperatorIndex.hom.{u, v} n k ⟶ level F k :=
  MonoidalClosed.uncurry (F.toEnrichedFunctor.map
    (OrthogonalOperatorIndex.ofIndex.{u, v} n) (OrthogonalOperatorIndex.ofIndex.{u, v} k))

/-- Restrict the whole native action along an ACTUAL coefficient map. -/
def coefficientAction (F : Carrier.{u, v}) (n k : OrthogonalIndex)
    {M : PointedCGWH.{u, v}} (α : M ⟶ OrthogonalOperatorIndex.hom.{u, v} n k) :
    level F n ⊗ M ⟶ level F k :=
  level F n ◁ α ≫ fullAction F n k

/-- Whole transformation naturality retains every original native coefficient parameter. -/
theorem coefficientAction_naturality {F G : Carrier.{u, v}} (f : F ⟶ G)
    (n k : OrthogonalIndex) {M : PointedCGWH.{u, v}}
    (α : M ⟶ OrthogonalOperatorIndex.hom.{u, v} n k) :
    coefficientAction F n k α ≫ levelMap f k =
      (levelMap f n ▷ M) ≫ coefficientAction G n k α := by
  have h := f.uncurriedNaturality
    (OrthogonalOperatorIndex.ofIndex.{u, v} n) (OrthogonalOperatorIndex.ofIndex.{u, v} k)
  change fullAction F n k ≫ levelMap f k =
    (levelMap f n ⊗ₘ 𝟙 (OrthogonalOperatorIndex.hom.{u, v} n k)) ≫ fullAction G n k at h
  rw [tensorHom_id] at h
  dsimp only [coefficientAction]
  rw [Category.assoc, h, ← Category.assoc, whisker_exchange, Category.assoc]

/-- The actual native isometry coefficient acts through the original δ map. -/
def isometryAction (F : Carrier.{u, v}) (n k : OrthogonalIndex) :
    level F n ⊗ OrthogonalIndex.hom.{u, v} n k ⟶ level F k :=
  coefficientAction F n k (OrthogonalOperatorIndex.delta.{u, v} n k)

/-- Isometry-action naturality holds on the full original native Hom object. -/
theorem isometryAction_naturality {F G : Carrier.{u, v}} (f : F ⟶ G) (n k : OrthogonalIndex) :
    isometryAction F n k ≫ levelMap f k =
      (levelMap f n ▷ OrthogonalIndex.hom.{u, v} n k) ≫ isometryAction G n k :=
  coefficientAction_naturality f n k _

/-- The original block-swapped ν exposes the actual right-oriented sphere action. -/
def sphereAction (F : Carrier.{u, v}) (n a : OrthogonalIndex) :
    level F n ⊗ PointedCGWH.orthogonalSphere.{u, v} a ⟶ level F (n + a) :=
  coefficientAction F n (n + a) (OrthogonalOperatorIndex.nu.{u, v} n a)

/-- The original sphere action retains naturality on the entire sphere object. -/
theorem sphereAction_naturality {F G : Carrier.{u, v}} (f : F ⟶ G) (n a : OrthogonalIndex) :
    sphereAction F n a ≫ levelMap f (n + a) =
      (levelMap f n ▷ PointedCGWH.orthogonalSphere.{u, v} a) ≫ sphereAction G n a :=
  coefficientAction_naturality f n (n + a) _

/-- Free generation at the original dimension uses the actual FULL operator Hom. -/
def freeAt (n : OrthogonalIndex) : PointedCGWH.{u, v} ⥤ Carrier.{u, v} :=
  EnrichedFunctorCat.Free.functor (OrthogonalOperatorIndex.ofIndex.{u, v} n)

/-- Every free level is the whole original coefficient tensor native coend Hom. -/
theorem freeAt_level (n k : OrthogonalIndex) (X : PointedCGWH.{u, v}) :
    level ((freeAt n).obj X) k = X ⊗ OrthogonalOperatorIndex.hom.{u, v} n k := rfl

/-- Every mapped coefficient arrow keeps its full original tensor map at every degree. -/
theorem freeAt_map_level (n : OrthogonalIndex) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (k : OrthogonalIndex) :
    levelMap ((freeAt n).map f) k = f ▷ OrthogonalOperatorIndex.hom.{u, v} n k :=
  EnrichedFunctorCat.Free.coefficientMap_component _ f _

/-- The complete free sphere action uses the actual ν and native coend composition. -/
theorem freeAt_sphereAction (n k a : OrthogonalIndex) (X : PointedCGWH.{u, v}) :
    sphereAction ((freeAt n).obj X) k a =
      (X ⊗ OrthogonalOperatorIndex.hom.{u, v} n k) ◁ OrthogonalOperatorIndex.nu.{u, v} k a ≫
        (α_ X (OrthogonalOperatorIndex.hom.{u, v} n k)
          (OrthogonalOperatorIndex.hom.{u, v} k (k + a))).hom ≫
        X ◁ eComp PointedCGWH.{u, v} (OrthogonalOperatorIndex.ofIndex.{u, v} n)
          (OrthogonalOperatorIndex.ofIndex.{u, v} k)
          (OrthogonalOperatorIndex.ofIndex.{u, v} (k + a)) := by
  change (_ ◁ _ ≫ MonoidalClosed.uncurry
    ((EnrichedFunctorCat.Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} n)
      X).toEnrichedFunctor.map
      (OrthogonalOperatorIndex.ofIndex.{u, v} k)
      (OrthogonalOperatorIndex.ofIndex.{u, v} (k + a)))) = _
  rw [EnrichedFunctorCat.Free.object_uncurry_map]
  rfl

/-- The actual free/evaluation adjunction on the full native operator carrier. -/
def freeAtEvaluationAdjunction (n : OrthogonalIndex) : freeAt n ⊣ evaluation n :=
  EnrichedFunctorCat.Free.adjunction (OrthogonalOperatorIndex.ofIndex.{u, v} n)

/-- The entire forward Hom map evaluates the actual ORIGINAL coend identity. -/
theorem homEquiv_forward (n : OrthogonalIndex) (X : PointedCGWH.{u, v}) (F : Carrier.{u, v})
    (t : (freeAt n).obj X ⟶ F) :
    (freeAtEvaluationAdjunction n).homEquiv X F t =
      (ρ_ X).inv ≫ X ◁ eId PointedCGWH.{u, v} (OrthogonalOperatorIndex.ofIndex.{u, v} n) ≫
        levelMap t n := by
  change (EnrichedFunctorCat.Free.adjunction _).homEquiv X F t = _
  rw [EnrichedFunctorCat.Free.adjunction_homEquiv]
  rfl

/-- The entire inverse Hom map is the genuine enriched extension on full operator Homs. -/
theorem homEquiv_inverse (n : OrthogonalIndex) (X : PointedCGWH.{u, v}) (F : Carrier.{u, v})
    (f : X ⟶ level F n) :
    ((freeAtEvaluationAdjunction n).homEquiv X F).symm f =
      EnrichedFunctorCat.Free.extend (OrthogonalOperatorIndex.ofIndex.{u, v} n) X F f := by
  change ((EnrichedFunctorCat.Free.adjunction _).homEquiv X F).symm f = _
  rw [EnrichedFunctorCat.Free.adjunction_homEquiv]
  rfl

/-- The extended original level map keeps the whole coefficient action at every target degree. -/
theorem homEquiv_inverse_level (n : OrthogonalIndex) (X : PointedCGWH.{u, v}) (F : Carrier.{u, v})
    (f : X ⟶ level F n) (k : OrthogonalIndex) :
    levelMap (((freeAtEvaluationAdjunction n).homEquiv X F).symm f) k =
      (f ▷ OrthogonalOperatorIndex.hom.{u, v} n k) ≫ fullAction F n k := by
  rw [homEquiv_inverse]
  change EnrichedFunctorCat.component (EnrichedFunctorCat.Free.extend _ X F f) _ = _
  rw [EnrichedFunctorCat.Free.extend_component]
  change (f ⊗ₘ 𝟙 (OrthogonalOperatorIndex.hom.{u, v} n k)) ≫ fullAction F n k = _
  rw [tensorHom_id]

/-- Literal original degree/free-boundary labels retain every original base arrow. -/
def boundaryGenerators : MorphismProperty Carrier.{u, v} :=
  MorphismProperty.adjointFamilyGenerators (freeAt.{u, v})
    PointedCGWH.realizedBoundaryInclusions.{u, v}

/-- Literal original degree/free-horn labels retain every original base arrow. -/
def hornGenerators : MorphismProperty Carrier.{u, v} :=
  MorphismProperty.adjointFamilyGenerators (freeAt.{u, v}) PointedCGWH.realizedHornInclusions.{u, v}

/-- The whole original degree-labelled I family is exactly the actual native I family. -/
theorem boundaryGenerators_eq : boundaryGenerators.{u, v} =
    EnrichedProjective.generators (A := OrthogonalOperatorIndex.{u, v})
      PointedCGWH.realizedBoundaryInclusions.{u, v} :=
  MorphismProperty.adjointFamilyGenerators_reindex OrthogonalOperatorIndex.ofIndex
    ofIndex_surjective _ _

/-- The whole original degree-labelled J family is exactly the actual native J family. -/
theorem hornGenerators_eq : hornGenerators.{u, v} =
    EnrichedProjective.generators (A := OrthogonalOperatorIndex.{u, v})
      PointedCGWH.realizedHornInclusions.{u, v} :=
  MorphismProperty.adjointFamilyGenerators_reindex OrthogonalOperatorIndex.ofIndex
    ofIndex_surjective _ _

/-- Actual native weak equivalences are detected at every original dimension. -/
theorem weakEquivalences_iff {F G : Carrier.{u, v}} (f : F ⟶ G) :
    let _ : ModelCategory Carrier.{u, v} := PointedCGWH.Spectra.Orthogonal.levelModel
    weakEquivalences Carrier.{u, v} f ↔ ∀ n : OrthogonalIndex,
      weakEquivalences PointedCGWH.{u, v} (levelMap f n) := by
  let _ : ModelCategory Carrier.{u, v} := PointedCGWH.Spectra.Orthogonal.levelModel
  change PointedCGWH.Spectra.Orthogonal.levelModel.categoryWithWeakEquivalences.weakEquivalences f ↔
    ∀ n : OrthogonalIndex, weakEquivalences PointedCGWH.{u, v} (levelMap f n)
  rw [PointedCGWH.Spectra.Orthogonal.levelModel_weakEquivalences,
    EvaluationTransfer.evaluationProperty_iff]
  constructor
  · intro h n
    exact h (OrthogonalOperatorIndex.ofIndex.{u, v} n)
  · intro h x
    obtain ⟨n, rfl⟩ := ofIndex_surjective x
    exact h n

/-- Actual native fibrations are detected at every original dimension. -/
theorem fibrations_iff {F G : Carrier.{u, v}} (f : F ⟶ G) :
    let _ : ModelCategory Carrier.{u, v} := PointedCGWH.Spectra.Orthogonal.levelModel
    fibrations Carrier.{u, v} f ↔ ∀ n : OrthogonalIndex,
      fibrations PointedCGWH.{u, v} (levelMap f n) := by
  let _ : ModelCategory Carrier.{u, v} := PointedCGWH.Spectra.Orthogonal.levelModel
  change PointedCGWH.Spectra.Orthogonal.levelModel.categoryWithFibrations.fibrations f ↔
    ∀ n : OrthogonalIndex, fibrations PointedCGWH.{u, v} (levelMap f n)
  rw [PointedCGWH.Spectra.Orthogonal.levelModel_fibrations,
    EvaluationTransfer.evaluationProperty_iff]
  constructor
  · intro h n
    exact h (OrthogonalOperatorIndex.ofIndex.{u, v} n)
  · intro h x
    obtain ⟨n, rfl⟩ := ofIndex_surjective x
    exact h n

/-- Actual native trivial fibrations are detected at every original dimension. -/
theorem trivialFibrations_iff {F G : Carrier.{u, v}} (f : F ⟶ G) :
    let _ : ModelCategory Carrier.{u, v} := PointedCGWH.Spectra.Orthogonal.levelModel
    trivialFibrations Carrier.{u, v} f ↔ ∀ n : OrthogonalIndex,
      trivialFibrations PointedCGWH.{u, v} (levelMap f n) := by
  let _ : ModelCategory Carrier.{u, v} := PointedCGWH.Spectra.Orthogonal.levelModel
  change trivialFibrations Carrier.{u, v} f ↔ ∀ n : OrthogonalIndex,
    trivialFibrations PointedCGWH.{u, v} (levelMap f n)
  rw [PointedCGWH.Spectra.Orthogonal.levelModel_trivialFibrations,
    EvaluationTransfer.evaluationProperty_iff]
  constructor
  · intro h n
    exact h (OrthogonalOperatorIndex.ofIndex.{u, v} n)
  · intro h x
    obtain ⟨n, rfl⟩ := ofIndex_surjective x
    exact h n

/-- Actual native cofibrations use the whole original degree-labelled free-I family. -/
theorem cofibrations_eq :
    let _ : ModelCategory Carrier.{u, v} := PointedCGWH.Spectra.Orthogonal.levelModel
    cofibrations Carrier.{u, v} = boundaryGenerators.{u, v}.rlp.llp := by
  let _ : ModelCategory Carrier.{u, v} := PointedCGWH.Spectra.Orthogonal.levelModel
  change PointedCGWH.Spectra.Orthogonal.levelModel.categoryWithCofibrations.cofibrations =
    boundaryGenerators.{u, v}.rlp.llp
  rw [PointedCGWH.Spectra.Orthogonal.levelModel_cofibrations, boundaryGenerators_eq]

/-- Actual native trivial cofibrations use the whole original degree-labelled free-J family. -/
theorem trivialCofibrations_eq :
    let _ : ModelCategory Carrier.{u, v} := PointedCGWH.Spectra.Orthogonal.levelModel
    trivialCofibrations Carrier.{u, v} = hornGenerators.{u, v}.rlp.llp := by
  let _ : ModelCategory Carrier.{u, v} := PointedCGWH.Spectra.Orthogonal.levelModel
  change trivialCofibrations Carrier.{u, v} = hornGenerators.{u, v}.rlp.llp
  rw [PointedCGWH.Spectra.Orthogonal.levelModel_trivialCofibrations, hornGenerators_eq]

/-- The actual original-dimensional free/evaluation adjunction is Quillen
for the canonical native level model. -/
theorem freeAtEvaluation_isQuillenAdjunction (n : OrthogonalIndex) :
    let _ : ModelCategory Carrier.{u, v} := PointedCGWH.Spectra.Orthogonal.levelModel
    (freeAtEvaluationAdjunction n).IsQuillenAdjunction := by
  exact PointedCGWH.Spectra.Orthogonal.freeAtEvaluation_isQuillenAdjunction
    (OrthogonalOperatorIndex.ofIndex n)

end PointedCGWH.Spectra.Orthogonal.NativePresentation
