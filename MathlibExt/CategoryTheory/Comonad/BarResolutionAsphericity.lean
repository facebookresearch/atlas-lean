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
# Counit sections and homology of comonad resolutions

Let G be a comonad on C and P an object with s : P → G(P) satisfying s ≫ ε_P = id_P. The
canonical augmented resolution has degree-n object G^{n+1}(P). The maps s' = s and s_n =
G^{n+1}(s) give a right extra degeneracy: its last face retracts s_n, and the other face and
degeneracy equations follow from comonad naturality.

In a preadditive category with zero object and homology for all alternating-resolution terms,
its alternating augmentation is a quasi-isomorphism. In an abelian category, Moore inclusion
gives the normalized augmentation α : N(Res_G P) → P[0]. It is a quasi-isomorphism, induces
H₀(N(Res_G P)) ≅ P and makes every positive homology object zero. The section is required only
to split the counit; the category worlds are independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite AlgebraicTopology
open scoped Simplicial

universe v u

namespace CategoryTheory.Comonad

variable {C : Type u} [Category.{v} C]

/-- Right extra degeneracy from a comonad counit section.

For G, P and s : P → G(P) with s ≫ ε_P = id, define the extra degree-minus-one map as s and
the degree-n map as G^{n+1}(s). These satisfy the right extra-degeneracy identities for the
canonical augmented resolution data. -/
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

/-- Right extra degeneracy on the canonical comonad resolution.

For a counit section s : P → G(P), convert the extra-degeneracy data to the augmented
simplicial resolution Res_G(P). Its component maps are the same section and iterated comonad
images. -/
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

/-- Homology existence for the dropped augmented resolution.

In a preadditive category with zero object, if every degree of the alternating complex of
Res_G(P).left has homology, the same homology instances apply to the complex obtained by
dropping the augmented resolution and then applying the alternating-face functor. -/
local instance resolutionAlternatingHasHomology (G : Comonad C) (P : C)
    [∀ n : ℕ, ((alternatingFaceMapComplex C).obj (resolutionAugmented G P).left).HasHomology n] :
    ∀ n : ℕ,
      ((SimplicialObject.Augmented.drop ⋙ alternatingFaceMapComplex C).obj
        (resolutionAugmented G P)).HasHomology n := by
  intro n
  change ((alternatingFaceMapComplex C).obj (resolutionAugmented G P).left).HasHomology n
  infer_instance

/-- Homology existence for the single-term augmentation point.

In a preadditive category with zero object, the point of Res_G(P), viewed as a chain complex
concentrated in degree zero, has homology in every natural degree. -/
local instance resolutionPointSingleHasHomology (G : Comonad C) (P : C) :
    ∀ n : ℕ,
      ((SimplicialObject.Augmented.point ⋙ ChainComplex.single₀ C).obj
        (resolutionAugmented G P)).HasHomology n := by
  intro n
  change ((ChainComplex.single₀ C).obj (resolutionAugmented G P).right).HasHomology n
  infer_instance

/-- Quasi-isomorphism of a comonad resolution augmentation from a counit section.

Let C be preadditive with zero object and all homology objects of the alternating resolution
defined. A section s : P → G(P) of ε_P gives a quasi-isomorphism from its alternating chain
complex to the augmentation point concentrated in degree zero. -/
theorem resolutionAugmentation_quasiIso_of_counitSection (G : Comonad C) (P : C)
    (s : P ⟶ G.obj P) (hs : s ≫ G.ε.app P = 𝟙 P)
    [∀ n : ℕ, ((alternatingFaceMapComplex C).obj (resolutionAugmented G P).left).HasHomology n] :
    QuasiIso (AlternatingFaceMapComplex.ε.app (resolutionAugmented G P)) := by
  let ed := resolutionRightExtraOfCounitSection G P s hs
  exact ed.quasiIso_augmentation

end Homology

section Abelian

variable [Abelian C]

/-- Normalized chain augmentation of a comonad resolution.

In an abelian category, define α : N(Res_G(P).left) → P[0] by Moore inclusion, the alternating
augmentation and the canonical identification of the resolution's augmentation point with P. -/
def normalizedResolutionAugmentation (G : Comonad C) (P : C) :
    (normalizedMooreComplex C).obj (resolutionAugmented G P).left ⟶
      (ChainComplex.single₀ C).obj P :=
  inclusionOfMooreComplexMap (resolutionAugmented G P).left ≫
    AlternatingFaceMapComplex.ε.app (resolutionAugmented G P) ≫
      (ChainComplex.single₀ C).map (eqToHom (resolutionAugmented_point G P))

/-- Degree-zero component of the normalized comonad augmentation.

For a comonad G on an abelian category, α₀ equals the degree-zero Moore inclusion followed by
the counit ε_P : G(P) → P. -/
theorem normalizedResolutionAugmentation_f_zero (G : Comonad C) (P : C) :
    (normalizedResolutionAugmentation G P).f 0 =
      (inclusionOfMooreComplexMap (resolutionAugmented G P).left).f 0 ≫ G.ε.app P := by
  dsimp only [normalizedResolutionAugmentation, HomologicalComplex.comp_f]
  rw [AlternatingFaceMapComplex.ε_app_f_zero, resolutionAugmented_hom_zero,
    ChainComplex.single₀_map_f_zero]
  change _ ≫ G.ε.app P ≫ 𝟙 P = _
  exact (Category.assoc _ _ _).symm.trans (Category.comp_id _)

/-- Normalized comonad augmentation for an object with split counit.

In an abelian category, if s : P → G(P) satisfies s ≫ ε_P = id_P, the normalized augmentation
α : N(Res_G(P)) → P[0] is a quasi-isomorphism. -/
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

/-- Degree-zero homology isomorphism of a split-counit resolution.

For a comonad G in an abelian category and a counit section on P, the map on H₀ induced by the
normalized augmentation, followed by the single-term homology identification, gives
H₀(N(Res_G(P))) ≅ P. -/
def normalizedResolutionHomologyZeroIso (G : Comonad C) (P : C)
    (s : P ⟶ G.obj P) (hs : s ≫ G.ε.app P = 𝟙 P) :
    ((normalizedMooreComplex C).obj (resolutionAugmented G P).left).homology 0 ≅ P := by
  letI hα : QuasiIso (normalizedResolutionAugmentation G P) :=
    normalizedResolutionAugmentation_quasiIso_of_counitSection G P s hs
  exact asIso (HomologicalComplex.homologyMap (normalizedResolutionAugmentation G P) 0) ≪≫
    HomologicalComplex.singleObjHomologySelfIso (ComplexShape.down ℕ) 0 P

/-- Characteristic map of the resolution homology-zero comparison.

Let e : H₀(N(Res_G(P))) ≅ P be induced by the normalized augmentation α. Then H₀(α) = e.hom
followed by the inverse of the canonical H₀(P[0]) ≅ P comparison. -/
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

/-- Vanishing of positive homology of a split-counit resolution.

For G on an abelian category and s : P → G(P) splitting ε_P, H_{n+1}(N(Res_G(P))) is a zero
object for every n : ℕ. The normalized augmentation identifies it with the positive homology
of P[0]. -/
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
