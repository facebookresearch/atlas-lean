/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Comonad.BarResolution
public import MathlibExt.AlgebraicTopology.SimplicialObject.RightExtraDegeneracyHomotopy
public import MathlibExt.AlgebraicTopology.SimplicialObject.DataExtraToSimplicial
public import MathlibExt.AlgebraicTopology.SimplicialObject.DataAugmentedComparison
public import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence
public import Mathlib.CategoryTheory.Retract

/-!
# Asphericity of canonical comonad resolutions

The canonical augmented resolution of a cotriple-projective object has an actual
normalized quasi-isomorphism to that object. A counit section directly supplies
the terminal-face contraction; no coalgebra law for that section is assumed.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite AlgebraicTopology
open scoped Simplicial

universe v u

namespace CategoryTheory.Comonad

variable {C : Type u} [Category.{v} C]

/-- A genuine counit section supplies the terminal-face extra degeneracy on the data. -/
def resolutionAugmentedDataRightExtraOfCounitSection (G : Comonad C) (P : C)
    (s : P ⟶ G.obj P) (hs : s ≫ G.ε.app P = 𝟙 P) :
    SimplicialObject.Data.Augmented.RightExtraDegeneracy
      (resolutionAugmentedData G P) where
  s' := by
    change P ⟶ G.obj P
    exact s
  s n := by
    change (comonadPow G (n + 1)).obj P ⟶ (comonadPow G ((n + 1) + 1)).obj P
    exact (comonadPow G (n + 1)).map s
  s'_comp_ε := by
    change s ≫ G.ε.app P = 𝟙 P
    exact hs
  s₀_comp_δ₀ := by
    change G.map s ≫ G.ε.app (G.obj P) = G.ε.app P ≫ s
    exact G.ε.naturality s
  s_comp_δ_last n := by
    change (comonadPow G (n + 1)).map s ≫
      cobarEpsilonAtPos G (n + 1) (Fin.last (n + 1)) P = 𝟙 _
    simp only [cobarEpsilonAtPos_rev, Fin.rev_last]
    have hε := epsilonAtPos_zero_eq G n P
    exact (congrArg
      (fun f : (comonadPow G (n + 1)).obj (G.obj P) ⟶
          (comonadPow G (n + 1)).obj P => (comonadPow G (n + 1)).map s ≫ f) hε).trans
        (((comonadPow G (n + 1)).map_comp s (G.ε.app P)).symm.trans
          ((congrArg (fun f : P ⟶ P => (comonadPow G (n + 1)).map f) hs).trans
            ((comonadPow G (n + 1)).map_id P)))
  s_comp_δ n i := by
    change (comonadPow G ((n + 1) + 1)).map s ≫
        cobarEpsilonAtPos G ((n + 1) + 1) i.castSucc P =
      cobarEpsilonAtPos G (n + 1) i P ≫ (comonadPow G (n + 1)).map s
    simp only [cobarEpsilonAtPos_rev, Fin.rev_castSucc]
    exact epsilonAtPos_naturality G (n + 1) i.rev s
  s_comp_σ n i := by
    change (comonadPow G (n + 1)).map s ≫
        cobarDeltaAtPos G ((n + 1) + 1) i.castSucc P =
      cobarDeltaAtPos G (n + 1) i P ≫ (comonadPow G ((n + 1) + 1)).map s
    simp only [cobarDeltaAtPos_rev, Fin.rev_castSucc]
    exact deltaAtPos_naturality G (n + 1) i.rev s

/-- Transport the data contraction to the actual canonical resolution functor. -/
def resolutionRightExtraOfCounitSection (G : Comonad C) (P : C)
    (s : P ⟶ G.obj P) (hs : s ≫ G.ε.app P = 𝟙 P) :
    SimplicialObject.Augmented.RightExtraDegeneracy (resolutionAugmented G P) := by
  let ed := resolutionAugmentedDataRightExtraOfCounitSection G P s hs
  have hX : resolutionAugmented G P =
      (resolutionAugmentedData G P).toSimplicialAugmented := by
    unfold resolutionAugmented resolutionAugmentedFunctor
    change SimplicialObject.Data.Augmented.toSimplicialFunctor.obj
      (resolutionAugmentedData G P) = (resolutionAugmentedData G P).toSimplicialAugmented
    exact SimplicialObject.Data.Augmented.toSimplicialFunctor_obj_eq _
  exact hX.symm ▸ ed.toSimplicial

section Homology

variable [Preadditive C] [HasZeroObject C]

local instance resolutionAlternatingHasHomology (G : Comonad C) (P : C)
    [∀ n : ℕ, ((alternatingFaceMapComplex C).obj (resolutionAugmented G P).left).HasHomology n] :
    ∀ n : ℕ,
      ((SimplicialObject.Augmented.drop ⋙ alternatingFaceMapComplex C).obj
        (resolutionAugmented G P)).HasHomology n := by
  intro n
  change ((alternatingFaceMapComplex C).obj (resolutionAugmented G P).left).HasHomology n
  infer_instance

local instance resolutionPointSingleHasHomology (G : Comonad C) (P : C) :
    ∀ n : ℕ,
      ((SimplicialObject.Augmented.point ⋙ ChainComplex.single₀ C).obj
        (resolutionAugmented G P)).HasHomology n := by
  intro n
  change ((ChainComplex.single₀ C).obj (resolutionAugmented G P).right).HasHomology n
  infer_instance

/-- A counit section supplies a contraction of the actual full augmentation. -/
theorem resolutionAugmentation_quasiIso_of_counitSection (G : Comonad C) (P : C)
    (s : P ⟶ G.obj P) (hs : s ≫ G.ε.app P = 𝟙 P)
    [∀ n : ℕ, ((alternatingFaceMapComplex C).obj (resolutionAugmented G P).left).HasHomology n] :
    QuasiIso (AlternatingFaceMapComplex.ε.app (resolutionAugmented G P)) := by
  let ed := resolutionRightExtraOfCounitSection G P s hs
  exact ed.quasiIso_augmentation

end Homology

section Abelian

variable [Abelian C]

/-- The actual Moore inclusion and native augmentation, with the actual point transport. -/
def normalizedResolutionAugmentation (G : Comonad C) (P : C) :
    (normalizedMooreComplex C).obj (resolutionAugmented G P).left ⟶
      (ChainComplex.single₀ C).obj P :=
  inclusionOfMooreComplexMap (resolutionAugmented G P).left ≫
    AlternatingFaceMapComplex.ε.app (resolutionAugmented G P) ≫
      (ChainComplex.single₀ C).map (eqToHom (resolutionAugmented_point G P))

/-- Its degree-zero map is induced by the actual counit, with native normalization inclusion. -/
theorem normalizedResolutionAugmentation_f_zero (G : Comonad C) (P : C) :
    (normalizedResolutionAugmentation G P).f 0 =
      (inclusionOfMooreComplexMap (resolutionAugmented G P).left).f 0 ≫ G.ε.app P := by
  dsimp only [normalizedResolutionAugmentation, HomologicalComplex.comp_f]
  rw [AlternatingFaceMapComplex.ε_app_f_zero, resolutionAugmented_hom_zero,
    ChainComplex.single₀_map_f_zero]
  change _ ≫ G.ε.app P ≫ 𝟙 P = _
  exact (Category.assoc _ _ _).symm.trans (Category.comp_id _)

/-- A cotriple-projective object's actual normalized augmentation is a quasi-isomorphism. -/
theorem normalizedResolutionAugmentation_quasiIso_of_counitSection (G : Comonad C) (P : C)
    (s : P ⟶ G.obj P) (hs : s ≫ G.ε.app P = 𝟙 P) :
    QuasiIso (normalizedResolutionAugmentation G P) := by
  let hfull : QuasiIso (AlternatingFaceMapComplex.ε.app (resolutionAugmented G P)) :=
    resolutionAugmentation_quasiIso_of_counitSection G P s hs
  let hinc : QuasiIso (inclusionOfMooreComplexMap (resolutionAugmented G P).left) :=
    (DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
      (Y := (resolutionAugmented G P).left)).quasiIso_hom
  dsimp only [normalizedResolutionAugmentation]
  infer_instance

/-- The genuine degree-zero homology isomorphism is induced by the actual augmentation. -/
def normalizedResolutionHomologyZeroIso (G : Comonad C) (P : C)
    (s : P ⟶ G.obj P) (hs : s ≫ G.ε.app P = 𝟙 P) :
    ((normalizedMooreComplex C).obj (resolutionAugmented G P).left).homology 0 ≅ P := by
  letI hα : QuasiIso (normalizedResolutionAugmentation G P) :=
    normalizedResolutionAugmentation_quasiIso_of_counitSection G P s hs
  exact asIso (HomologicalComplex.homologyMap (normalizedResolutionAugmentation G P) 0) ≪≫
    HomologicalComplex.singleObjHomologySelfIso (ComplexShape.down ℕ) 0 P

/-- The characteristic uses the actual induced map, not an arbitrary degree-zero isomorphism. -/
theorem normalizedResolutionHomologyZeroIso_homologyMap (G : Comonad C) (P : C)
    (s : P ⟶ G.obj P) (hs : s ≫ G.ε.app P = 𝟙 P) :
    HomologicalComplex.homologyMap (normalizedResolutionAugmentation G P) 0 =
      (normalizedResolutionHomologyZeroIso G P s hs).hom ≫
        (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.down ℕ) 0 P).inv := by
  let hα : QuasiIso (normalizedResolutionAugmentation G P) :=
    normalizedResolutionAugmentation_quasiIso_of_counitSection G P s hs
  change _ = (_ ≫ (HomologicalComplex.singleObjHomologySelfIso
    (ComplexShape.down ℕ) 0 P).hom) ≫ _
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact (asIso_hom _).symm

/-- Actual positive normalized homology vanishes for a counit-section object. -/
theorem isZero_normalizedResolution_homology_succ (G : Comonad C) (P : C)
    (s : P ⟶ G.obj P) (hs : s ≫ G.ε.app P = 𝟙 P) (n : ℕ) :
    IsZero (((normalizedMooreComplex C).obj (resolutionAugmented G P).left).homology (n + 1)) := by
  let hα : QuasiIso (normalizedResolutionAugmentation G P) :=
    normalizedResolutionAugmentation_quasiIso_of_counitSection G P s hs
  have hzero : IsZero (((ChainComplex.single₀ C).obj P).homology (n + 1)) := by
    rw [← HomologicalComplex.exactAt_iff_isZero_homology]
    exact ChainComplex.exactAt_succ_single_obj P n
  exact hzero.of_iso
    (asIso (HomologicalComplex.homologyMap (normalizedResolutionAugmentation G P) (n + 1)))

end Abelian

end CategoryTheory.Comonad

end
