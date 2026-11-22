/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.OrderedLoop.Iteration

/-!
# The complete original evaluated loop-iteration family

Every stage of the actual ordered loop iteration has a full natural
isomorphism from original level evaluation to the actual iterated
sphere-one internal Hom of the original successor-level evaluation.
Both component maps and naturalities on every original spectrum map
are retained. These are full point-set functor identities before any
homotopy telescope or free function-spectrum identification.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v u₁ v₁
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalClosed CGWH.modelCategory

private theorem map_eq_naturality
    {C : Type u₁} [Category.{v₁} C] {A B : C} {f g : A ⟶ B} (h : f = g) :
    f ≫ 𝟙 B = 𝟙 A ≫ g :=
  (Category.comp_id f).trans (h.trans (Category.id_comp g).symm)

namespace PointedCGWH.SequentialSpectrum.OrderedLoop
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

/-- This is the actual repeated original sphere-one internal-Hom functor with all original maps. -/
def loopPower : ℕ → (PointedCGWH.{u, v} ⥤ PointedCGWH.{u, v})
  | 0 => 𝟭 _
  | n + 1 => loopPower n ⋙ ihom PointedCGWH.sphereOne

/-- The whole original one-step evaluation is naturally the original successor loop functor. -/
def levelEvaluationIso (m : ℕ) :
    functor.{u, v} ⋙ CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne m ≅
      CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne (m + 1) ⋙
        ihom PointedCGWH.sphereOne :=
  NatIso.ofComponents (fun X => Iso.refl ((functor.obj X).level m)) (fun f => by
    exact map_eq_naturality (functor_map_levelMap f m))

/-- Every full evaluated iterate is the SAME iterated internal Hom on the SAME original level. -/
def iterationEvaluationIso : ∀ n m : ℕ,
    iterate.{u, v} n ⋙ CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne m ≅
      CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne (m + n) ⋙ loopPower n
  | 0, m =>
    (CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne m).leftUnitor ≪≫
      (CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne m).rightUnitor.symm
  | n + 1, m =>
    CategoryTheory.Functor.associator (iterate n) functor
        (CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne m) ≪≫
      CategoryTheory.Functor.isoWhiskerLeft (iterate n) (levelEvaluationIso m) ≪≫
      (CategoryTheory.Functor.associator (iterate n)
        (CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne (m + 1))
        (ihom PointedCGWH.sphereOne)).symm ≪≫
      CategoryTheory.Functor.isoWhiskerRight (iterationEvaluationIso n (m + 1))
        (ihom PointedCGWH.sphereOne) ≪≫
      CategoryTheory.Functor.associator
        (CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne (m + 1 + n))
        (loopPower n) (ihom PointedCGWH.sphereOne) ≪≫
      CategoryTheory.Functor.isoWhiskerRight
        (eqToIso (congrArg
          (fun k : ℕ => CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne k)
          (show m + 1 + n = m + (n + 1) by omega)))
        (loopPower n ⋙ ihom PointedCGWH.sphereOne)

/-- Every actual original spectrum retains its full evaluated component Iso, in both directions. -/
def iterationEvaluationIsoComponent (n m : ℕ) (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    ((iterate n).obj X).level m ≅ (loopPower n).obj (X.level (m + n)) :=
  (iterationEvaluationIso n m).app X

/-- All original input maps commute with the entire forward evaluated-iteration Iso. -/
theorem iterationEvaluationIso_naturality (n m : ℕ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    PointedCGWH.SequentialSpectrum.levelMap ((iterate n).map f) m ≫
        (iterationEvaluationIsoComponent n m Y).hom =
      (iterationEvaluationIsoComponent n m X).hom ≫
        (loopPower n).map (PointedCGWH.SequentialSpectrum.levelMap f (m + n)) :=
  (iterationEvaluationIso n m).hom.naturality f

/-- All original input maps commute with the entire inverse evaluated-iteration Iso. -/
theorem iterationEvaluationIso_inv_naturality (n m : ℕ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    (loopPower n).map (PointedCGWH.SequentialSpectrum.levelMap f (m + n)) ≫
        (iterationEvaluationIsoComponent n m Y).inv =
      (iterationEvaluationIsoComponent n m X).inv ≫
        PointedCGWH.SequentialSpectrum.levelMap ((iterate n).map f) m :=
  (iterationEvaluationIso n m).inv.naturality f

/-- BOTH complete evaluated maps compose to the original identity on the actual original stage. -/
theorem iterationEvaluationIso_hom_inv (n m : ℕ) (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (iterationEvaluationIsoComponent n m X).hom ≫ (iterationEvaluationIsoComponent n m X).inv =
      𝟙 (((iterate n).obj X).level m) := (iterationEvaluationIsoComponent n m X).hom_inv_id

/-- BOTH complete evaluated maps compose to the original identity on the actual looped level. -/
theorem iterationEvaluationIso_inv_hom (n m : ℕ) (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (iterationEvaluationIsoComponent n m X).inv ≫ (iterationEvaluationIsoComponent n m X).hom =
      𝟙 ((loopPower n).obj (X.level (m + n))) := (iterationEvaluationIsoComponent n m X).inv_hom_id

/-- The entire dependent component-Iso function is retained on ALL original stages and degrees. -/
theorem iterationEvaluationIsoComponent_whole :
    (fun (n m : ℕ) (X : PointedCGWH.SequentialSpectrum.{u, v}) =>
      iterationEvaluationIsoComponent n m X) =
      (fun n m X => (iterationEvaluationIso n m).app X) := rfl

/--
Every actual original transition retains the SAME original successor transpose at every level.
-/
theorem iterateUnit_levelMap (n : ℕ) (X : PointedCGWH.SequentialSpectrum.{u, v}) (m : ℕ) :
    PointedCGWH.SequentialSpectrum.levelMap ((iterateUnit n).app X) m =
      PointedCGWH.SequentialSpectrum.adjointStructureMap ((iterate n).obj X) m :=
  (congrArg (fun f => PointedCGWH.SequentialSpectrum.levelMap f m)
    (iterateUnit_app n X)).trans (unit_levelMap ((iterate n).obj X) m)

end PointedCGWH.SequentialSpectrum.OrderedLoop
