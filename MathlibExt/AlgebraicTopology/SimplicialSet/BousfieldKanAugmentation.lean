/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanHocolim
public import MathlibExt.AlgebraicTopology.SimplicialObject.ToAugmented

/-!
# Bousfield--Kan augmentations

A cocone from a simplicial-set diagram in any universe to a constant diagram
induces an augmentation of the terminal-weight ordinary bar and hence an
augmentation of its Bousfield--Kan diagonal. This file gives the data-level
construction, weighted-summand computation laws, and naturality for maps of
cocones.

The `AugmentationOf` section mirrors this API as `bkAugmentationOf` over
diagrams in `SSet.{max uJ vJ w'}`, for clients whose indexing categories
live in smaller universes than their simplicial sets. The extra level does
not infer at concrete levels, so those clients pass it explicitly; the
canonical declarations above keep their original inferable signatures.

No simplex-resolution, contraction, weak-equivalence, realization, Quillen
Theorem A, or Waldhausen additivity statement is made here.
-/

@[expose] public section

open CategoryTheory Limits Opposite Simplicial

universe uJ vJ

namespace SSet

section Augmentation

variable {J : Type uJ} [Category.{vJ} J]
variable {D E : J ⥤ SSet.{max uJ vJ}} {Z Z' : SSet.{max uJ vJ}}

/-- A cocone absorbs the transported first-face component of a replacement
chain. -/
theorem srepFaceZeroComponent_comp_cocone
    (τ : D ⟶ (Functor.const J).obj Z) {n : ℕ}
    (s : SrepBridge.SrepIdx J (n + 1)) :
    SrepBridge.srepFaceZeroComponent D s ≫
        τ.app (SrepBridge.srepDropFirst s).left =
      τ.app s.left := by
  let a : s.left ⟶ (SrepBridge.srepDropFirst s).left :=
    eqToHom (SrepBridge.srepLeftZero s) ≫ s.map' 0 1 ≫
      eqToHom (SrepBridge.srepDropFirst_left s).symm
  have hcomp : SrepBridge.srepFaceZeroComponent D s = D.map a := by
    simp only [SrepBridge.srepFaceZeroComponent, a, Functor.map_comp,
      eqToHom_map]
  rw [hcomp]
  calc
    D.map a ≫ τ.app (SrepBridge.srepDropFirst s).left =
        τ.app s.left ≫ ((Functor.const J).obj Z).map a := τ.naturality a
    _ = τ.app s.left := by
      rw [Functor.const_obj_map]
      apply Category.comp_id

/-- A cocone absorbs the transported last-face component of a replacement
chain. -/
theorem srepFaceLastComponent_comp_cocone
    (τ : D ⟶ (Functor.const J).obj Z) {n : ℕ}
    (s : SrepBridge.SrepIdx J (n + 1)) :
    SrepBridge.srepFaceLastComponent D s ≫
        τ.app (SrepBridge.srepDropLast s).left =
      τ.app s.left := by
  let a : s.left ⟶ (SrepBridge.srepDropLast s).left :=
    eqToHom (SrepBridge.srepDropLast_left s).symm
  have hcomp : SrepBridge.srepFaceLastComponent D s = D.map a := by
    simp only [SrepBridge.srepFaceLastComponent, a, eqToHom_map]
  rw [hcomp]
  calc
    D.map a ≫ τ.app (SrepBridge.srepDropLast s).left =
        τ.app s.left ≫ ((Functor.const J).obj Z).map a := τ.naturality a
    _ = τ.app s.left := by
      rw [Functor.const_obj_map]
      apply Category.comp_id

/-- Degree-zero augmentation of the terminal-weight ordinary bar, obtained by
descending the cocone component `τ.app p.1.left` on each weighted summand. -/
noncomputable def wbarAugmentationZero
    (τ : D ⟶ (Functor.const J).obj Z) :
    StrictOrdinaryWeightedBar.wbarObj (CategoryBar.replUnit J) D 0 ⟶ Z :=
  StrictOrdinaryWeightedBar.wbarDesc (CategoryBar.replUnit J) D 0
    (fun p => τ.app p.1.left)

theorem wbarAugmentationZero_isBalanced
    (τ : D ⟶ (Functor.const J).obj Z) :
    SimplicialObject.Data.IsBalanced
      (X := StrictOrdinaryWeightedBar.wbarData (CategoryBar.replUnit J) D)
      (wbarAugmentationZero τ) := by
  refine Limits.Sigma.hom_ext _ _ (fun p => ?_)
  let p0 := StrictOrdinaryWeightedBar.wFaceZeroIdx
    (CategoryBar.replUnit J) 0 p
  let p1 := StrictOrdinaryWeightedBar.wFaceLastIdx
    (CategoryBar.replUnit J) 0 p
  have hzero :
      (StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D 1 p ≫
          StrictOrdinaryWeightedBar.wbarδ (CategoryBar.replUnit J) D 0 0) ≫
            wbarAugmentationZero τ =
        τ.app p.1.left := by
    have hface := StrictOrdinaryWeightedBar.wbarFaceZero_ι
      (CategoryBar.replUnit J) D 0 p
    have hdesc := StrictOrdinaryWeightedBar.wbarDesc_ι
      (CategoryBar.replUnit J) D 0 (fun p => τ.app p.1.left) p0
    calc
      _ = (SrepBridge.srepFaceZeroComponent D p.1 ≫
            StrictOrdinaryWeightedBar.wbarIncl
              (CategoryBar.replUnit J) D 0 p0) ≫
              wbarAugmentationZero τ := by
          apply congrArg (fun z => z ≫ wbarAugmentationZero τ)
          rw [StrictOrdinaryWeightedBar.wbarδ_zero]
          exact hface
      _ = SrepBridge.srepFaceZeroComponent D p.1 ≫
            (StrictOrdinaryWeightedBar.wbarIncl
              (CategoryBar.replUnit J) D 0 p0 ≫
              wbarAugmentationZero τ) := Category.assoc _ _ _
      _ = SrepBridge.srepFaceZeroComponent D p.1 ≫
            τ.app p0.1.left :=
          congrArg (fun z => SrepBridge.srepFaceZeroComponent D p.1 ≫ z) hdesc
      _ = τ.app p.1.left := by
          change SrepBridge.srepFaceZeroComponent D p.1 ≫
            τ.app (SrepBridge.srepDropFirst p.1).left = τ.app p.1.left
          exact srepFaceZeroComponent_comp_cocone τ p.1
  have hone :
      (StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D 1 p ≫
          StrictOrdinaryWeightedBar.wbarδ (CategoryBar.replUnit J) D 0 1) ≫
            wbarAugmentationZero τ =
        τ.app p.1.left := by
    have hlast : (1 : Fin 2) = Fin.last 1 := rfl
    have hface := StrictOrdinaryWeightedBar.wbarFaceLast_ι
      (CategoryBar.replUnit J) D 0 p
    have hdesc := StrictOrdinaryWeightedBar.wbarDesc_ι
      (CategoryBar.replUnit J) D 0 (fun p => τ.app p.1.left) p1
    calc
      _ = (SrepBridge.srepFaceLastComponent D p.1 ≫
          StrictOrdinaryWeightedBar.wbarIncl
            (CategoryBar.replUnit J) D 0 p1) ≫
            wbarAugmentationZero τ := by
          apply congrArg (fun z => z ≫ wbarAugmentationZero τ)
          rw [hlast, StrictOrdinaryWeightedBar.wbarδ_last]
          exact hface
      _ = SrepBridge.srepFaceLastComponent D p.1 ≫
          (StrictOrdinaryWeightedBar.wbarIncl
            (CategoryBar.replUnit J) D 0 p1 ≫
            wbarAugmentationZero τ) := Category.assoc _ _ _
      _ = SrepBridge.srepFaceLastComponent D p.1 ≫
          τ.app p1.1.left :=
        congrArg (fun z => SrepBridge.srepFaceLastComponent D p.1 ≫ z) hdesc
      _ = τ.app p.1.left := by
          change SrepBridge.srepFaceLastComponent D p.1 ≫
            τ.app (SrepBridge.srepDropLast p.1).left = τ.app p.1.left
          exact srepFaceLastComponent_comp_cocone τ p.1
  exact hzero.trans hone.symm

/-- Data-level terminal-weight bar augmentation induced by a cocone. -/
noncomputable def wbarAugmentationData
    (τ : D ⟶ (Functor.const J).obj Z) :
    StrictOrdinaryWeightedBar.wbarData (CategoryBar.replUnit J) D ⟶
      SimplicialObject.Data.constData Z :=
  SimplicialObject.Data.balancedHom (wbarAugmentationZero_isBalanced τ)

/-- Every degree of the data augmentation is the coproduct-descended cocone
map at the left endpoint of each chain. -/
theorem wbarAugmentationData_app
    (τ : D ⟶ (Functor.const J).obj Z) (n : ℕ) :
    (wbarAugmentationData τ).app n =
      StrictOrdinaryWeightedBar.wbarDesc (CategoryBar.replUnit J) D n
        (fun p => τ.app p.1.left) := by
  induction n with
  | zero =>
      change (wbarAugmentationData τ).app 0 = wbarAugmentationZero τ
      unfold wbarAugmentationData
      exact SimplicialObject.Data.balancedHom_app_zero
        (wbarAugmentationZero_isBalanced τ)
  | succ n ih =>
      have hs : (wbarAugmentationData τ).app (n + 1) =
          StrictOrdinaryWeightedBar.wbarδ (CategoryBar.replUnit J) D n 0 ≫
            (wbarAugmentationData τ).app n := by
        rfl
      rw [hs, ih]
      refine Limits.Sigma.hom_ext _ _ (fun p => ?_)
      let p0 := StrictOrdinaryWeightedBar.wFaceZeroIdx
        (CategoryBar.replUnit J) n p
      have hface := StrictOrdinaryWeightedBar.wbarFaceZero_ι
        (CategoryBar.replUnit J) D n p
      have hdesc := StrictOrdinaryWeightedBar.wbarDesc_ι
        (CategoryBar.replUnit J) D n (fun p => τ.app p.1.left) p0
      have hdescTop := StrictOrdinaryWeightedBar.wbarDesc_ι
        (CategoryBar.replUnit J) D (n + 1) (fun p => τ.app p.1.left) p
      calc
        _ = (StrictOrdinaryWeightedBar.wbarIncl
              (CategoryBar.replUnit J) D (n + 1) p ≫
              StrictOrdinaryWeightedBar.wbarδ
                (CategoryBar.replUnit J) D n 0) ≫
              StrictOrdinaryWeightedBar.wbarDesc
                (CategoryBar.replUnit J) D n
                  (fun p => τ.app p.1.left) :=
            (Category.assoc _ _ _).symm
        _ = (SrepBridge.srepFaceZeroComponent D p.1 ≫
              StrictOrdinaryWeightedBar.wbarIncl
                (CategoryBar.replUnit J) D n p0) ≫
              StrictOrdinaryWeightedBar.wbarDesc
                (CategoryBar.replUnit J) D n
                  (fun p => τ.app p.1.left) := by
            apply congrArg (fun z => z ≫
              StrictOrdinaryWeightedBar.wbarDesc
                (CategoryBar.replUnit J) D n
                  (fun p => τ.app p.1.left))
            rw [StrictOrdinaryWeightedBar.wbarδ_zero]
            exact hface
        _ = SrepBridge.srepFaceZeroComponent D p.1 ≫
              (StrictOrdinaryWeightedBar.wbarIncl
                (CategoryBar.replUnit J) D n p0 ≫
                StrictOrdinaryWeightedBar.wbarDesc
                  (CategoryBar.replUnit J) D n
                    (fun p => τ.app p.1.left)) := Category.assoc _ _ _
        _ = SrepBridge.srepFaceZeroComponent D p.1 ≫
              τ.app p0.1.left :=
            congrArg (fun z => SrepBridge.srepFaceZeroComponent D p.1 ≫ z) hdesc
        _ = τ.app p.1.left := by
            change SrepBridge.srepFaceZeroComponent D p.1 ≫
              τ.app (SrepBridge.srepDropFirst p.1).left = τ.app p.1.left
            exact srepFaceZeroComponent_comp_cocone τ p.1
        _ = StrictOrdinaryWeightedBar.wbarIncl
              (CategoryBar.replUnit J) D (n + 1) p ≫
              StrictOrdinaryWeightedBar.wbarDesc
                (CategoryBar.replUnit J) D (n + 1)
                  (fun p => τ.app p.1.left) := by
            exact hdescTop.symm

/-- Terminal-weight bar augmentation as a map to the constant simplicial
object. -/
noncomputable def wbarAugmentation
    (τ : D ⟶ (Functor.const J).obj Z) :
    StrictOrdinaryWeightedBar.wbarSimplicial (CategoryBar.replUnit J) D ⟶
      (SimplicialObject.const SSet.{max uJ vJ}).obj Z :=
  SimplicialObject.Data.toSimplicialFunctor.map (wbarAugmentationData τ) ≫
    (SimplicialObject.Data.constDataIso Z).hom

/-- Degree computation for the terminal-weight bar augmentation. -/
@[simp]
theorem wbarAugmentation_app_mk
    (τ : D ⟶ (Functor.const J).obj Z) (n : ℕ) :
    (wbarAugmentation τ).app (op ⦋n⦌) =
      StrictOrdinaryWeightedBar.wbarDesc (CategoryBar.replUnit J) D n
        (fun p => τ.app p.1.left) := by
  unfold wbarAugmentation StrictOrdinaryWeightedBar.wbarSimplicial
  change
    (SimplicialObject.Data.toSimplicialFunctor.map
        (wbarAugmentationData τ)).app (op ⦋n⦌) ≫
      (SimplicialObject.Data.constDataIso Z).hom.app (op ⦋n⦌) = _
  rw [SimplicialObject.Data.toSimplicialFunctor_map_app_mk,
    SimplicialObject.Data.constDataIso_hom_app_mk]
  exact (Category.comp_id ((wbarAugmentationData τ).app n)).trans
    (wbarAugmentationData_app τ n)

/-- Bousfield--Kan augmentation induced by a cocone. -/
noncomputable def bkAugmentation
    (τ : D ⟶ (Functor.const J).obj Z) :
    bkHocolim D ⟶ Z :=
  simplicialDiagonalFunctor.map (wbarAugmentation τ) ≫
    (diagonalConstIso Z).hom

/-- The Bousfield--Kan augmentation restricts on each weighted summand to the
corresponding cocone component. -/
theorem bkAugmentation_app_mk_ι
    (τ : D ⟶ (Functor.const J).obj Z) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n) :
    (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit J) D n p).app (op ⦋n⦌) ≫
      (bkAugmentation τ).app (op ⦋n⦌) =
    (τ.app p.1.left).app (op ⦋n⦌) := by
  unfold bkAugmentation bkHocolim diagonalConstIso
  change
    (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit J) D n p).app (op ⦋n⦌) ≫
      ((wbarAugmentation τ).app (op ⦋n⦌)).app (op ⦋n⦌) = _
  rw [wbarAugmentation_app_mk]
  exact congrArg (fun q => q.app (op ⦋n⦌))
    (StrictOrdinaryWeightedBar.wbarDesc_ι
      (CategoryBar.replUnit J) D n (fun p => τ.app p.1.left) p)

/-- Degree computation for the Bousfield--Kan augmentation. -/
@[simp]
theorem bkAugmentation_app_mk
    (τ : D ⟶ (Functor.const J).obj Z) (n : ℕ) :
    (bkAugmentation τ).app (op ⦋n⦌) =
      (StrictOrdinaryWeightedBar.wbarDesc
        (CategoryBar.replUnit J) D n
          (fun p => τ.app p.1.left)).app (op ⦋n⦌) := by
  unfold bkAugmentation bkHocolim diagonalConstIso
  change ((wbarAugmentation τ).app (op ⦋n⦌)).app (op ⦋n⦌) ≫ 𝟙 _ = _
  rw [Category.comp_id, wbarAugmentation_app_mk]

/-- Naturality of the Bousfield--Kan augmentation for a map of cocones. -/
theorem bkAugmentation_naturality
    (α : D ⟶ E)
    (τ : D ⟶ (Functor.const J).obj Z)
    (τ' : E ⟶ (Functor.const J).obj Z') (u : Z ⟶ Z')
    (h : ∀ j, α.app j ≫ τ'.app j = τ.app j ≫ u) :
    bkHocolimMap α ≫ bkAugmentation τ' = bkAugmentation τ ≫ u := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  have hn :
      StrictOrdinaryWeightedBar.wbarMapF
          (W := CategoryBar.replUnit J) n α ≫
        StrictOrdinaryWeightedBar.wbarDesc
          (CategoryBar.replUnit J) E n (fun p => τ'.app p.1.left) =
      StrictOrdinaryWeightedBar.wbarDesc
          (CategoryBar.replUnit J) D n (fun p => τ.app p.1.left) ≫ u := by
    refine Limits.Sigma.hom_ext _ _ (fun p => ?_)
    have hmap := StrictOrdinaryWeightedBar.wbarMapF_ι n α p
    have hdescE := StrictOrdinaryWeightedBar.wbarDesc_ι
      (CategoryBar.replUnit J) E n (fun p => τ'.app p.1.left) p
    have hdescD := StrictOrdinaryWeightedBar.wbarDesc_ι
      (CategoryBar.replUnit J) D n (fun p => τ.app p.1.left) p
    calc
      _ = (StrictOrdinaryWeightedBar.wbarIncl
            (CategoryBar.replUnit J) D n p ≫
            StrictOrdinaryWeightedBar.wbarMapF n α) ≫
          StrictOrdinaryWeightedBar.wbarDesc
            (CategoryBar.replUnit J) E n (fun p => τ'.app p.1.left) :=
        (Category.assoc _ _ _).symm
      _ = ((α.app p.1.left ≫
            StrictOrdinaryWeightedBar.wbarIncl
              (CategoryBar.replUnit J) E n p) ≫
          StrictOrdinaryWeightedBar.wbarDesc
            (CategoryBar.replUnit J) E n (fun p => τ'.app p.1.left)) := by
        exact congrArg (fun z => z ≫
          StrictOrdinaryWeightedBar.wbarDesc
            (CategoryBar.replUnit J) E n
              (fun p => τ'.app p.1.left)) hmap
      _ = α.app p.1.left ≫
          (StrictOrdinaryWeightedBar.wbarIncl
            (CategoryBar.replUnit J) E n p ≫
            StrictOrdinaryWeightedBar.wbarDesc
              (CategoryBar.replUnit J) E n
                (fun p => τ'.app p.1.left)) := Category.assoc _ _ _
      _ = α.app p.1.left ≫ τ'.app p.1.left := by
        exact congrArg (fun z => α.app p.1.left ≫ z) hdescE
      _ = τ.app p.1.left ≫ u := h p.1.left
      _ = (StrictOrdinaryWeightedBar.wbarIncl
            (CategoryBar.replUnit J) D n p ≫
            StrictOrdinaryWeightedBar.wbarDesc
              (CategoryBar.replUnit J) D n
                (fun p => τ.app p.1.left)) ≫ u := by
        exact congrArg (fun z => z ≫ u) hdescD.symm
      _ = StrictOrdinaryWeightedBar.wbarIncl
            (CategoryBar.replUnit J) D n p ≫
          (StrictOrdinaryWeightedBar.wbarDesc
            (CategoryBar.replUnit J) D n
              (fun p => τ.app p.1.left) ≫ u) := Category.assoc _ _ _
  rw [NatTrans.comp_app, NatTrans.comp_app,
    bkHocolimMap_app_mk, bkAugmentation_app_mk,
    bkAugmentation_app_mk]
  change
    (StrictOrdinaryWeightedBar.wbarMapF
        (W := CategoryBar.replUnit J) n α).app (op ⦋n⦌) ≫
      (StrictOrdinaryWeightedBar.wbarDesc
        (CategoryBar.replUnit J) E n
          (fun p => τ'.app p.1.left)).app (op ⦋n⦌) =
    (StrictOrdinaryWeightedBar.wbarDesc
        (CategoryBar.replUnit J) D n
          (fun p => τ.app p.1.left)).app (op ⦋n⦌) ≫
      u.app (op ⦋n⦌)
  exact congrArg (fun q => q.app (op ⦋n⦌)) hn

end Augmentation

section AugmentationOf

universe w'

variable {J : Type uJ} [Category.{vJ} J]
variable {D₀ E₀ : J ⥤ SSet.{max uJ vJ w'}} {Z₀ Z₁ : SSet.{max uJ vJ w'}}

-- Generalized-target variants: diagrams land in `SSet.{max uJ vJ w'}`
-- so one common universe can serve smaller indexing categories. The
-- target level does not infer at concrete levels; clients pass it
-- explicitly. Proofs mirror the canonical versions above.

/-- A cocone absorbs the transported first-face component of a replacement
chain. -/
theorem srepFaceZeroComponent_comp_coconeOf
    (τ : D₀ ⟶ (Functor.const J).obj Z₀) {n : ℕ}
    (s : SrepBridge.SrepIdx J (n + 1)) :
    SrepBridge.srepFaceZeroComponent D₀ s ≫
        τ.app (SrepBridge.srepDropFirst s).left =
      τ.app s.left := by
  let a : s.left ⟶ (SrepBridge.srepDropFirst s).left :=
    eqToHom (SrepBridge.srepLeftZero s) ≫ s.map' 0 1 ≫
      eqToHom (SrepBridge.srepDropFirst_left s).symm
  have hcomp : SrepBridge.srepFaceZeroComponent D₀ s = D₀.map a := by
    simp only [SrepBridge.srepFaceZeroComponent, a, Functor.map_comp,
      eqToHom_map]
  rw [hcomp]
  calc
    D₀.map a ≫ τ.app (SrepBridge.srepDropFirst s).left =
        τ.app s.left ≫ ((Functor.const J).obj Z₀).map a := τ.naturality a
    _ = τ.app s.left := by
      rw [Functor.const_obj_map]
      apply Category.comp_id

/-- A cocone absorbs the transported last-face component of a replacement
chain. -/
theorem srepFaceLastComponent_comp_coconeOf
    (τ : D₀ ⟶ (Functor.const J).obj Z₀) {n : ℕ}
    (s : SrepBridge.SrepIdx J (n + 1)) :
    SrepBridge.srepFaceLastComponent D₀ s ≫
        τ.app (SrepBridge.srepDropLast s).left =
      τ.app s.left := by
  let a : s.left ⟶ (SrepBridge.srepDropLast s).left :=
    eqToHom (SrepBridge.srepDropLast_left s).symm
  have hcomp : SrepBridge.srepFaceLastComponent D₀ s = D₀.map a := by
    simp only [SrepBridge.srepFaceLastComponent, a, eqToHom_map]
  rw [hcomp]
  calc
    D₀.map a ≫ τ.app (SrepBridge.srepDropLast s).left =
        τ.app s.left ≫ ((Functor.const J).obj Z₀).map a := τ.naturality a
    _ = τ.app s.left := by
      rw [Functor.const_obj_map]
      apply Category.comp_id

/-- Degree-zero augmentation of the terminal-weight ordinary bar, obtained by
descending the cocone component `τ.app p.1.left` on each weighted summand. -/
noncomputable def wbarAugmentationZeroOf
    (τ : D₀ ⟶ (Functor.const J).obj Z₀) :
    StrictOrdinaryWeightedBar.wbarObj (CategoryBar.replUnit J) D₀ 0 ⟶ Z₀ :=
  StrictOrdinaryWeightedBar.wbarDesc (CategoryBar.replUnit J) D₀ 0
    (fun p => τ.app p.1.left)

theorem wbarAugmentationZeroOf_isBalanced
    (τ : D₀ ⟶ (Functor.const J).obj Z₀) :
    SimplicialObject.Data.IsBalanced
      (X := StrictOrdinaryWeightedBar.wbarData (CategoryBar.replUnit J) D₀)
      (wbarAugmentationZeroOf τ) := by
  refine Limits.Sigma.hom_ext _ _ (fun p => ?_)
  let p0 := StrictOrdinaryWeightedBar.wFaceZeroIdx
    (CategoryBar.replUnit J) 0 p
  let p1 := StrictOrdinaryWeightedBar.wFaceLastIdx
    (CategoryBar.replUnit J) 0 p
  have hzero :
      (StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D₀ 1 p ≫
          StrictOrdinaryWeightedBar.wbarδ (CategoryBar.replUnit J) D₀ 0 0) ≫
            wbarAugmentationZeroOf τ =
        τ.app p.1.left := by
    have hface := StrictOrdinaryWeightedBar.wbarFaceZero_ι
      (CategoryBar.replUnit J) D₀ 0 p
    have hdesc := StrictOrdinaryWeightedBar.wbarDesc_ι
      (CategoryBar.replUnit J) D₀ 0 (fun p => τ.app p.1.left) p0
    calc
      _ = (SrepBridge.srepFaceZeroComponent D₀ p.1 ≫
            StrictOrdinaryWeightedBar.wbarIncl
              (CategoryBar.replUnit J) D₀ 0 p0) ≫
              wbarAugmentationZeroOf τ := by
          apply congrArg (fun z => z ≫ wbarAugmentationZeroOf τ)
          rw [StrictOrdinaryWeightedBar.wbarδ_zero]
          exact hface
      _ = SrepBridge.srepFaceZeroComponent D₀ p.1 ≫
            (StrictOrdinaryWeightedBar.wbarIncl
              (CategoryBar.replUnit J) D₀ 0 p0 ≫
              wbarAugmentationZeroOf τ) := Category.assoc _ _ _
      _ = SrepBridge.srepFaceZeroComponent D₀ p.1 ≫
            τ.app p0.1.left :=
          congrArg (fun z => SrepBridge.srepFaceZeroComponent D₀ p.1 ≫ z) hdesc
      _ = τ.app p.1.left := by
          change SrepBridge.srepFaceZeroComponent D₀ p.1 ≫
            τ.app (SrepBridge.srepDropFirst p.1).left = τ.app p.1.left
          exact srepFaceZeroComponent_comp_coconeOf τ p.1
  have hone :
      (StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D₀ 1 p ≫
          StrictOrdinaryWeightedBar.wbarδ (CategoryBar.replUnit J) D₀ 0 1) ≫
            wbarAugmentationZeroOf τ =
        τ.app p.1.left := by
    have hlast : (1 : Fin 2) = Fin.last 1 := rfl
    have hface := StrictOrdinaryWeightedBar.wbarFaceLast_ι
      (CategoryBar.replUnit J) D₀ 0 p
    have hdesc := StrictOrdinaryWeightedBar.wbarDesc_ι
      (CategoryBar.replUnit J) D₀ 0 (fun p => τ.app p.1.left) p1
    calc
      _ = (SrepBridge.srepFaceLastComponent D₀ p.1 ≫
          StrictOrdinaryWeightedBar.wbarIncl
            (CategoryBar.replUnit J) D₀ 0 p1) ≫
            wbarAugmentationZeroOf τ := by
          apply congrArg (fun z => z ≫ wbarAugmentationZeroOf τ)
          rw [hlast, StrictOrdinaryWeightedBar.wbarδ_last]
          exact hface
      _ = SrepBridge.srepFaceLastComponent D₀ p.1 ≫
          (StrictOrdinaryWeightedBar.wbarIncl
            (CategoryBar.replUnit J) D₀ 0 p1 ≫
            wbarAugmentationZeroOf τ) := Category.assoc _ _ _
      _ = SrepBridge.srepFaceLastComponent D₀ p.1 ≫
          τ.app p1.1.left :=
        congrArg (fun z => SrepBridge.srepFaceLastComponent D₀ p.1 ≫ z) hdesc
      _ = τ.app p.1.left := by
          change SrepBridge.srepFaceLastComponent D₀ p.1 ≫
            τ.app (SrepBridge.srepDropLast p.1).left = τ.app p.1.left
          exact srepFaceLastComponent_comp_coconeOf τ p.1
  exact hzero.trans hone.symm

/-- Data-level terminal-weight bar augmentation induced by a cocone. -/
noncomputable def wbarAugmentationDataOf
    (τ : D₀ ⟶ (Functor.const J).obj Z₀) :
    StrictOrdinaryWeightedBar.wbarData (CategoryBar.replUnit J) D₀ ⟶
      SimplicialObject.Data.constData Z₀ :=
  SimplicialObject.Data.balancedHom (wbarAugmentationZeroOf_isBalanced τ)

/-- Every degree of the data augmentation is the coproduct-descended cocone
map at the left endpoint of each chain. -/
theorem wbarAugmentationDataOf_app
    (τ : D₀ ⟶ (Functor.const J).obj Z₀) (n : ℕ) :
    (wbarAugmentationDataOf τ).app n =
      StrictOrdinaryWeightedBar.wbarDesc (CategoryBar.replUnit J) D₀ n
        (fun p => τ.app p.1.left) := by
  induction n with
  | zero =>
      change (wbarAugmentationDataOf τ).app 0 = wbarAugmentationZeroOf τ
      unfold wbarAugmentationDataOf
      exact SimplicialObject.Data.balancedHom_app_zero
        (wbarAugmentationZeroOf_isBalanced τ)
  | succ n ih =>
      have hs : (wbarAugmentationDataOf τ).app (n + 1) =
          StrictOrdinaryWeightedBar.wbarδ (CategoryBar.replUnit J) D₀ n 0 ≫
            (wbarAugmentationDataOf τ).app n := by
        rfl
      rw [hs, ih]
      refine Limits.Sigma.hom_ext _ _ (fun p => ?_)
      let p0 := StrictOrdinaryWeightedBar.wFaceZeroIdx
        (CategoryBar.replUnit J) n p
      have hface := StrictOrdinaryWeightedBar.wbarFaceZero_ι
        (CategoryBar.replUnit J) D₀ n p
      have hdesc := StrictOrdinaryWeightedBar.wbarDesc_ι
        (CategoryBar.replUnit J) D₀ n (fun p => τ.app p.1.left) p0
      have hdescTop := StrictOrdinaryWeightedBar.wbarDesc_ι
        (CategoryBar.replUnit J) D₀ (n + 1) (fun p => τ.app p.1.left) p
      calc
        _ = (StrictOrdinaryWeightedBar.wbarIncl
              (CategoryBar.replUnit J) D₀ (n + 1) p ≫
              StrictOrdinaryWeightedBar.wbarδ
                (CategoryBar.replUnit J) D₀ n 0) ≫
              StrictOrdinaryWeightedBar.wbarDesc
                (CategoryBar.replUnit J) D₀ n
                  (fun p => τ.app p.1.left) :=
            (Category.assoc _ _ _).symm
        _ = (SrepBridge.srepFaceZeroComponent D₀ p.1 ≫
              StrictOrdinaryWeightedBar.wbarIncl
                (CategoryBar.replUnit J) D₀ n p0) ≫
              StrictOrdinaryWeightedBar.wbarDesc
                (CategoryBar.replUnit J) D₀ n
                  (fun p => τ.app p.1.left) := by
            apply congrArg (fun z => z ≫
              StrictOrdinaryWeightedBar.wbarDesc
                (CategoryBar.replUnit J) D₀ n
                  (fun p => τ.app p.1.left))
            rw [StrictOrdinaryWeightedBar.wbarδ_zero]
            exact hface
        _ = SrepBridge.srepFaceZeroComponent D₀ p.1 ≫
              (StrictOrdinaryWeightedBar.wbarIncl
                (CategoryBar.replUnit J) D₀ n p0 ≫
                StrictOrdinaryWeightedBar.wbarDesc
                  (CategoryBar.replUnit J) D₀ n
                    (fun p => τ.app p.1.left)) := Category.assoc _ _ _
        _ = SrepBridge.srepFaceZeroComponent D₀ p.1 ≫
              τ.app p0.1.left :=
            congrArg (fun z => SrepBridge.srepFaceZeroComponent D₀ p.1 ≫ z) hdesc
        _ = τ.app p.1.left := by
            change SrepBridge.srepFaceZeroComponent D₀ p.1 ≫
              τ.app (SrepBridge.srepDropFirst p.1).left = τ.app p.1.left
            exact srepFaceZeroComponent_comp_coconeOf τ p.1
        _ = StrictOrdinaryWeightedBar.wbarIncl
              (CategoryBar.replUnit J) D₀ (n + 1) p ≫
              StrictOrdinaryWeightedBar.wbarDesc
                (CategoryBar.replUnit J) D₀ (n + 1)
                  (fun p => τ.app p.1.left) := by
            exact hdescTop.symm

/-- Terminal-weight bar augmentation as a map to the constant simplicial
object. -/
noncomputable def wbarAugmentationOf
    (τ : D₀ ⟶ (Functor.const J).obj Z₀) :
    StrictOrdinaryWeightedBar.wbarSimplicial (CategoryBar.replUnit J) D₀ ⟶
      (SimplicialObject.const SSet.{max uJ vJ w'}).obj Z₀ :=
  SimplicialObject.Data.toSimplicialFunctor.map (wbarAugmentationDataOf τ) ≫
    (SimplicialObject.Data.constDataIso Z₀).hom

/-- Degree computation for the terminal-weight bar augmentation. -/
@[simp]
theorem wbarAugmentationOf_app_mk
    (τ : D₀ ⟶ (Functor.const J).obj Z₀) (n : ℕ) :
    (wbarAugmentationOf τ).app (op ⦋n⦌) =
      StrictOrdinaryWeightedBar.wbarDesc (CategoryBar.replUnit J) D₀ n
        (fun p => τ.app p.1.left) := by
  unfold wbarAugmentationOf StrictOrdinaryWeightedBar.wbarSimplicial
  change
    (SimplicialObject.Data.toSimplicialFunctor.map
        (wbarAugmentationDataOf τ)).app (op ⦋n⦌) ≫
      (SimplicialObject.Data.constDataIso Z₀).hom.app (op ⦋n⦌) = _
  rw [SimplicialObject.Data.toSimplicialFunctor_map_app_mk,
    SimplicialObject.Data.constDataIso_hom_app_mk]
  exact (Category.comp_id ((wbarAugmentationDataOf τ).app n)).trans
    (wbarAugmentationDataOf_app τ n)

/-- Bousfield--Kan augmentation induced by a cocone. -/
noncomputable def bkAugmentationOf
    (τ : D₀ ⟶ (Functor.const J).obj Z₀) :
    bkHocolimOf D₀ ⟶ Z₀ :=
  simplicialDiagonalFunctor.map (wbarAugmentationOf τ) ≫
    (diagonalConstIso Z₀).hom

/-- The Bousfield--Kan augmentation restricts on each weighted summand to the
corresponding cocone component. -/
theorem bkAugmentationOf_app_mk_ι
    (τ : D₀ ⟶ (Functor.const J).obj Z₀) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n) :
    (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit J) D₀ n p).app (op ⦋n⦌) ≫
      (bkAugmentationOf τ).app (op ⦋n⦌) =
    (τ.app p.1.left).app (op ⦋n⦌) := by
  unfold bkAugmentationOf bkHocolimOf diagonalConstIso
  change
    (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit J) D₀ n p).app (op ⦋n⦌) ≫
      ((wbarAugmentationOf τ).app (op ⦋n⦌)).app (op ⦋n⦌) = _
  rw [wbarAugmentationOf_app_mk]
  exact congrArg (fun q => q.app (op ⦋n⦌))
    (StrictOrdinaryWeightedBar.wbarDesc_ι
      (CategoryBar.replUnit J) D₀ n (fun p => τ.app p.1.left) p)

/-- Degree computation for the Bousfield--Kan augmentation. -/
@[simp]
theorem bkAugmentationOf_app_mk
    (τ : D₀ ⟶ (Functor.const J).obj Z₀) (n : ℕ) :
    (bkAugmentationOf τ).app (op ⦋n⦌) =
      (StrictOrdinaryWeightedBar.wbarDesc
        (CategoryBar.replUnit J) D₀ n
          (fun p => τ.app p.1.left)).app (op ⦋n⦌) := by
  unfold bkAugmentationOf bkHocolimOf diagonalConstIso
  change ((wbarAugmentationOf τ).app (op ⦋n⦌)).app (op ⦋n⦌) ≫ 𝟙 _ = _
  rw [Category.comp_id, wbarAugmentationOf_app_mk]

/-- Naturality of the Bousfield--Kan augmentation for a map of cocones. -/
theorem bkAugmentationOf_naturality
    (α : D₀ ⟶ E₀)
    (τ : D₀ ⟶ (Functor.const J).obj Z₀)
    (τ' : E₀ ⟶ (Functor.const J).obj Z₁) (u : Z₀ ⟶ Z₁)
    (h : ∀ j, α.app j ≫ τ'.app j = τ.app j ≫ u) :
    bkHocolimMapOf α ≫ bkAugmentationOf τ' = bkAugmentationOf τ ≫ u := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  have hn :
      StrictOrdinaryWeightedBar.wbarMapF
          (W := CategoryBar.replUnit J) n α ≫
        StrictOrdinaryWeightedBar.wbarDesc
          (CategoryBar.replUnit J) E₀ n (fun p => τ'.app p.1.left) =
      StrictOrdinaryWeightedBar.wbarDesc
          (CategoryBar.replUnit J) D₀ n (fun p => τ.app p.1.left) ≫ u := by
    refine Limits.Sigma.hom_ext _ _ (fun p => ?_)
    have hmap := StrictOrdinaryWeightedBar.wbarMapF_ι n α p
    have hdescE := StrictOrdinaryWeightedBar.wbarDesc_ι
      (CategoryBar.replUnit J) E₀ n (fun p => τ'.app p.1.left) p
    have hdescD := StrictOrdinaryWeightedBar.wbarDesc_ι
      (CategoryBar.replUnit J) D₀ n (fun p => τ.app p.1.left) p
    calc
      _ = (StrictOrdinaryWeightedBar.wbarIncl
            (CategoryBar.replUnit J) D₀ n p ≫
            StrictOrdinaryWeightedBar.wbarMapF n α) ≫
          StrictOrdinaryWeightedBar.wbarDesc
            (CategoryBar.replUnit J) E₀ n (fun p => τ'.app p.1.left) :=
        (Category.assoc _ _ _).symm
      _ = ((α.app p.1.left ≫
            StrictOrdinaryWeightedBar.wbarIncl
              (CategoryBar.replUnit J) E₀ n p) ≫
          StrictOrdinaryWeightedBar.wbarDesc
            (CategoryBar.replUnit J) E₀ n (fun p => τ'.app p.1.left)) := by
        exact congrArg (fun z => z ≫
          StrictOrdinaryWeightedBar.wbarDesc
            (CategoryBar.replUnit J) E₀ n
              (fun p => τ'.app p.1.left)) hmap
      _ = α.app p.1.left ≫
          (StrictOrdinaryWeightedBar.wbarIncl
            (CategoryBar.replUnit J) E₀ n p ≫
            StrictOrdinaryWeightedBar.wbarDesc
              (CategoryBar.replUnit J) E₀ n
                (fun p => τ'.app p.1.left)) := Category.assoc _ _ _
      _ = α.app p.1.left ≫ τ'.app p.1.left := by
        exact congrArg (fun z => α.app p.1.left ≫ z) hdescE
      _ = τ.app p.1.left ≫ u := h p.1.left
      _ = (StrictOrdinaryWeightedBar.wbarIncl
            (CategoryBar.replUnit J) D₀ n p ≫
            StrictOrdinaryWeightedBar.wbarDesc
              (CategoryBar.replUnit J) D₀ n
                (fun p => τ.app p.1.left)) ≫ u := by
        exact congrArg (fun z => z ≫ u) hdescD.symm
      _ = StrictOrdinaryWeightedBar.wbarIncl
            (CategoryBar.replUnit J) D₀ n p ≫
          (StrictOrdinaryWeightedBar.wbarDesc
            (CategoryBar.replUnit J) D₀ n
              (fun p => τ.app p.1.left) ≫ u) := Category.assoc _ _ _
  rw [NatTrans.comp_app, NatTrans.comp_app,
    bkHocolimMapOf_app_mk, bkAugmentationOf_app_mk,
    bkAugmentationOf_app_mk]
  change
    (StrictOrdinaryWeightedBar.wbarMapF
        (W := CategoryBar.replUnit J) n α).app (op ⦋n⦌) ≫
      (StrictOrdinaryWeightedBar.wbarDesc
        (CategoryBar.replUnit J) E₀ n
          (fun p => τ'.app p.1.left)).app (op ⦋n⦌) =
    (StrictOrdinaryWeightedBar.wbarDesc
        (CategoryBar.replUnit J) D₀ n
          (fun p => τ.app p.1.left)).app (op ⦋n⦌) ≫
      u.app (op ⦋n⦌)
  exact congrArg (fun q => q.app (op ⦋n⦌)) hn

end AugmentationOf


end SSet

end
