/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.OrderedLoop.GroupEvaluation

/-!
# Exact association of the original loop powers and iterated units

The SAME original loopPower and iterate definitions associate as whole
endofunctors, including their complete map functions. Their one-step
prefix comparisons are the actual equality isomorphisms. The original
whole equation functor_map_unit then proves that each original iterate
unit is the iteration of the SAME original input unit through this exact
prefix comparison. No symmetry or interchange structure on the original
sequential index is inferred.
-/

set_option autoImplicit false
noncomputable section
universe u v u₁ v₁
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.limits CGWH.modelCategory MonoidalClosed

private theorem originalWholePowerAssociation
    {C : Type u₁} [Category.{v₁} C] (R : C ⥤ C) (F : ℕ → (C ⥤ C))
    (hZero : F 0 = 𝟭 C) (hSucc : ∀ n, F (n + 1) = F n ⋙ R) (n m : ℕ) :
    F (n + m) = F n ⋙ F m := by
  induction m with
  | zero =>
    change F n = F n ⋙ F 0
    exact (congrArg (fun G : C ⥤ C => F n ⋙ G) hZero).symm
  | succ m hm =>
    change F ((n + m) + 1) = F n ⋙ F (m + 1)
    exact (hSucc (n + m)).trans
      ((congrArg (fun G : C ⥤ C => G ⋙ R) hm).trans
        (congrArg (fun G : C ⥤ C => F n ⋙ G) (hSucc m)).symm)

private theorem originalWholePowerPrefix
    {C : Type u₁} [Category.{v₁} C] (R : C ⥤ C) (F : ℕ → (C ⥤ C))
    (hZero : F 0 = 𝟭 C) (hSucc : ∀ n, F (n + 1) = F n ⋙ R) (n : ℕ) :
    F (n + 1) = R ⋙ F n := by
  induction n with
  | zero =>
    exact (hSucc 0).trans
      ((congrArg (fun G : C ⥤ C => G ⋙ R) hZero).trans
        (congrArg (fun G : C ⥤ C => R ⋙ G) hZero).symm)
  | succ n hn =>
    exact (hSucc (n + 1)).trans
      ((congrArg (fun G : C ⥤ C => G ⋙ R) hn).trans
        (congrArg (fun G : C ⥤ C => R ⋙ G) (hSucc n)).symm)

namespace PointedCGWH.SequentialSpectrum.OrderedLoop.AssociationGeometry

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

/-- The SAME original loop powers associate as complete original endofunctors. -/
theorem loopPower_add (n m : ℕ) :
    loopPower.{u, v} (n + m) = loopPower n ⋙ loopPower m :=
  originalWholePowerAssociation PointedCGWH.loop loopPower rfl (fun _ => rfl) n m

/-- The SAME original loop power admits its exact one-loop prefix association. -/
theorem loopPower_succ_prefix (n : ℕ) :
    loopPower.{u, v} (n + 1) = PointedCGWH.loop ⋙ loopPower n :=
  originalWholePowerPrefix PointedCGWH.loop loopPower rfl (fun _ => rfl) n

/-- These repeated powers of the SAME endofunctor commute as whole functors. -/
theorem loopPower_comp_commute (n m : ℕ) :
    loopPower.{u, v} n ⋙ loopPower m = loopPower m ⋙ loopPower n :=
  (loopPower_add n m).symm.trans
    ((congrArg loopPower (Nat.add_comm n m)).trans (loopPower_add m n))

/-- The complete original association is the equality Iso of the SAME original powers. -/
def loopPowerAddNatIso (n m : ℕ) :
    loopPower.{u, v} (n + m) ≅ loopPower n ⋙ loopPower m :=
  eqToIso (loopPower_add n m)

/-- Both full original associated map functions obey the complete forward comparison. -/
theorem loopPowerAddNatIso_hom_naturality (n m : ℕ)
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    (loopPower (n + m)).map f ≫ (loopPowerAddNatIso n m).hom.app Y =
      (loopPowerAddNatIso n m).hom.app X ≫ (loopPower m).map ((loopPower n).map f) :=
  (loopPowerAddNatIso n m).hom.naturality f

/-- Both full original associated map functions obey the complete inverse comparison. -/
theorem loopPowerAddNatIso_inv_naturality (n m : ℕ)
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    (loopPower m).map ((loopPower n).map f) ≫ (loopPowerAddNatIso n m).inv.app Y =
      (loopPowerAddNatIso n m).inv.app X ≫ (loopPower (n + m)).map f :=
  (loopPowerAddNatIso n m).inv.naturality f

/-- The exact whole forward loop association retains the original actual object equality. -/
theorem loopPowerAddNatIso_hom_app (n m : ℕ) (X : PointedCGWH.{u, v}) :
    (loopPowerAddNatIso n m).hom.app X =
      eqToHom (Functor.congr_obj (loopPower_add n m) X) :=
  eqToHom_app (loopPower_add n m) X

/-- The exact whole inverse loop association retains the same original object equality. -/
theorem loopPowerAddNatIso_inv_app (n m : ℕ) (X : PointedCGWH.{u, v}) :
    (loopPowerAddNatIso n m).inv.app X =
      eqToHom (Functor.congr_obj (loopPower_add n m).symm X) :=
  eqToHom_app (loopPower_add n m).symm X

/-- The SAME original spectrum iterations associate as complete original endofunctors. -/
theorem iterate_add (n m : ℕ) :
    iterate.{u, v} (n + m) = iterate n ⋙ iterate m :=
  originalWholePowerAssociation functor iterate rfl (fun _ => rfl) n m

/-- The SAME original ordered iteration has its exact original one-step prefix association. -/
theorem iterate_succ_prefix (n : ℕ) :
    iterate.{u, v} (n + 1) = functor ⋙ iterate n :=
  originalWholePowerPrefix functor iterate rfl (fun _ => rfl) n

/-- The complete original prefix comparison is the exact equality Iso of the SAME original
iterate. -/
def iteratePrefixNatIso (n : ℕ) :
    iterate.{u, v} (n + 1) ≅ functor ⋙ iterate n :=
  eqToIso (iterate_succ_prefix n)

/-- Every entire original spectrum input map retains the full forward prefix naturality. -/
theorem iteratePrefixNatIso_hom_naturality (n : ℕ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    (iterate (n + 1)).map f ≫ (iteratePrefixNatIso n).hom.app Y =
      (iteratePrefixNatIso n).hom.app X ≫ (iterate n).map (functor.map f) :=
  (iteratePrefixNatIso n).hom.naturality f

/-- Every entire original spectrum input map retains the full inverse prefix naturality. -/
theorem iteratePrefixNatIso_inv_naturality (n : ℕ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    (iterate n).map (functor.map f) ≫ (iteratePrefixNatIso n).inv.app Y =
      (iteratePrefixNatIso n).inv.app X ≫ (iterate (n + 1)).map f :=
  (iteratePrefixNatIso n).inv.naturality f

/-- The full original prefix component is the exact original object equality map. -/
theorem iteratePrefixNatIso_hom_app (n : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (iteratePrefixNatIso n).hom.app X =
      eqToHom (Functor.congr_obj (iterate_succ_prefix n) X) :=
  eqToHom_app (iterate_succ_prefix n) X

/-- The full inverse prefix component is the inverse exact original object equality map. -/
theorem iteratePrefixNatIso_inv_app (n : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (iteratePrefixNatIso n).inv.app X =
      eqToHom (Functor.congr_obj (iterate_succ_prefix n).symm X) :=
  eqToHom_app (iterate_succ_prefix n).symm X

/-- Iterating the SAME original input unit gives the SAME full original unit at the original
stage. -/
theorem iterate_map_unit_prefix_cast (n : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (iterate n).map (unit.app X) ≫
        eqToHom (Functor.congr_obj (iterate_succ_prefix n).symm X) =
      unit.app ((iterate n).obj X) := by
  induction n with
  | zero =>
    have hCast : eqToHom (Functor.congr_obj (iterate_succ_prefix 0).symm X) =
        𝟙 (functor.obj X) := rfl
    exact (congrArg (fun r => unit.app X ≫ r) hCast).trans (Category.comp_id (unit.app X))
  | succ n hn =>
    have hCast : eqToHom (Functor.congr_obj (iterate_succ_prefix (n + 1)).symm X) =
        functor.map (eqToHom (Functor.congr_obj (iterate_succ_prefix n).symm X)) := by
      rw [eqToHom_map]
      rfl
    exact (congrArg (fun r => functor.map ((iterate n).map (unit.app X)) ≫ r) hCast).trans
      ((functor.map_comp ((iterate n).map (unit.app X))
          (eqToHom (Functor.congr_obj (iterate_succ_prefix n).symm X))).symm.trans
        ((congrArg functor.map hn).trans (functor_map_unit ((iterate n).obj X))))

/-- The full original input-unit family is iterated and identified through the actual prefix Iso. -/
def originalIterateInputUnit (n : ℕ) : iterate.{u, v} n ⟶ iterate (n + 1) :=
  Functor.whiskerRight unit (iterate n) ≫ (iteratePrefixNatIso n).inv

/-- The whole input-unit transition component retains the actual original iterated map and cast. -/
theorem originalIterateInputUnit_app (n : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (originalIterateInputUnit n).app X =
      (iterate n).map (unit.app X) ≫
        eqToHom (Functor.congr_obj (iterate_succ_prefix n).symm X) := by
  change (iterate n).map (unit.app X) ≫ (iteratePrefixNatIso n).inv.app X = _
  rw [iteratePrefixNatIso_inv_app]

/-- The entire SAME original iterate unit equals the iterated SAME original input-unit family. -/
theorem iterateUnit_eq_originalInputUnit (n : ℕ) :
    iterateUnit.{u, v} n = originalIterateInputUnit n := by
  apply NatTrans.ext
  funext X
  rw [iterateUnit_app, originalIterateInputUnit_app]
  exact (iterate_map_unit_prefix_cast n X).symm

/-- Every original stage is retained in the WHOLE original dependent unit function equality. -/
theorem iterateUnit_eq_originalInputUnit_whole :
    (fun n : ℕ => iterateUnit.{u, v} n) = (fun n => originalIterateInputUnit n) := by
  funext n
  exact iterateUnit_eq_originalInputUnit n

/-- All entire original input squares commute with the SAME original prefix unit transition. -/
theorem originalIterateInputUnit_naturality (n : ℕ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    (iterate n).map f ≫ (originalIterateInputUnit n).app Y =
      (originalIterateInputUnit n).app X ≫ (iterate (n + 1)).map f :=
  (originalIterateInputUnit n).naturality f

end PointedCGWH.SequentialSpectrum.OrderedLoop.AssociationGeometry
