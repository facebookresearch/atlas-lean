/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import MathlibExt.CategoryTheory.Enriched.WeightedBarSimplicial
public import MathlibExt.AlgebraicTopology.SimplicialObject.FromData
public import MathlibExt.AlgebraicTopology.SimplicialObject.DataIso
public import MathlibExt.AlgebraicTopology.SimplicialObject.ToSimplicial

/-!
# Target postcomposition for the strict ordinary weighted bar

For a functor `G : C ⥤ D` preserving the relevant coproducts,
postcomposition commutes with the strict ordinary weighted bar: a degreewise
isomorphism `wbarObjMapIso` (via `PreservesCoproduct.iso`), coefficient laws,
face/degeneracy commutations in inverse form, and the bundled data and
simplicial isomorphisms `wbarDataMapPostcompIso` /
`wbarSimplicialMapPostcompIso` with their degree computations.

This API is independent of simplicial sets, `ULift`, and Quillen B; the
Bousfield–Kan compatibility built on it lives in
`MathlibExt.AlgebraicTopology.SimplicialSet.ChangeOfUniverseBousfieldKan`.
Diagram/weight variance is in `WeightedBarMapF` / `WeightedBarMapW` /
`WeightedBarMapFW`; categorical packaging is in `WeightedBarFunctor`.

Nonclaims: no `SSet` or `ULift` content, no Bousfield–Kan carrier,
augmentation, or homotopy-colimit statement, and no comparison,
weak-equivalence, realization, or model-category conclusion.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace CategoryTheory
namespace StrictOrdinaryWeightedBar

universe uJ vJ uW uC vC uD vD

variable {J : Type uJ} [Category.{vJ} J]
variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {W : Jᵒᵖ ⥤ Type uW} {F : J ⥤ C} (G : C ⥤ D)

section WbarPostcomp

/-- Postcomposition comparison at one weighted-bar degree: mapping the
coproduct out is the coproduct of the mapped diagram. -/
noncomputable def wbarObjMapIso (n : ℕ)
    [Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W n => (F ⋙ G).obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W n => G.obj (F.obj p.1.left))]
    [Limits.PreservesColimit
      (Discrete.functor (fun p : WIdx J W n => F.obj p.1.left)) G] :
    G.obj (wbarObj W F n) ≅ wbarObj W (F ⋙ G) n :=
  Limits.PreservesCoproduct.iso G (fun p : WIdx J W n => F.obj p.1.left)

/-- The inverse direction is the coproduct comparison map. -/
@[nolint unusedArguments]
theorem wbarObjMapIso_inv_eq (n : ℕ)
    [Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W n => (F ⋙ G).obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W n => G.obj (F.obj p.1.left))]
    [Limits.PreservesColimit
      (Discrete.functor (fun p : WIdx J W n => F.obj p.1.left)) G] :
    (wbarObjMapIso (G := G) n).inv =
      Limits.sigmaComparison G (fun p : WIdx J W n => F.obj p.1.left) :=
  rfl

/-- Coproduct-inclusion law for the inverse direction. -/
theorem wbarObjMapIso_inv_ι (n : ℕ)
    [Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W n => (F ⋙ G).obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W n => G.obj (F.obj p.1.left))]
    [Limits.PreservesColimit
      (Discrete.functor (fun p : WIdx J W n => F.obj p.1.left)) G]
    (p : WIdx J W n) :
    wbarIncl W (F ⋙ G) n p ≫ (wbarObjMapIso (G := G) n).inv =
      G.map (wbarIncl W F n p) := by
  rw [wbarObjMapIso_inv_eq]
  exact Limits.ι_comp_sigmaComparison G _ p

/-- The outermost-face coefficient commutes with postcomposition. -/
theorem srepFaceZeroComponent_postcomp {n : ℕ}
    (s : SrepBridge.SrepIdx J (n + 1)) :
    SrepBridge.srepFaceZeroComponent (F ⋙ G) s =
      G.map (SrepBridge.srepFaceZeroComponent F s) := by
  simp only [SrepBridge.srepFaceZeroComponent, Functor.map_comp,
    Functor.comp_map]
  rw [eqToHom_map, eqToHom_map]

/-- The last-face coefficient commutes with postcomposition. -/
theorem srepFaceLastComponent_postcomp {n : ℕ}
    (s : SrepBridge.SrepIdx J (n + 1)) :
    SrepBridge.srepFaceLastComponent (F ⋙ G) s =
      G.map (SrepBridge.srepFaceLastComponent F s) := by
  simp only [SrepBridge.srepFaceLastComponent]
  rw [eqToHom_map]

/-- The interior-face coefficient commutes with postcomposition. -/
theorem wFaceInnerComponent_postcomp {n : ℕ} (i : Fin (n + 2))
    (hi0 : i ≠ 0) [NeZero (n + 1)]
    (s : SrepBridge.SrepIdx J (n + 1)) :
    wFaceInnerComponent (F ⋙ G) i hi0 s =
      G.map (wFaceInnerComponent F i hi0 s) := by
  simp only [wFaceInnerComponent]
  rw [eqToHom_map]

/-- The interior-degeneracy coefficient commutes with postcomposition. -/
theorem wDegInnerComponent_postcomp {n : ℕ} (i : Fin (n + 1))
    [NeZero (n + 1)] (s : SrepBridge.SrepIdx J n) :
    wDegInnerComponent (F ⋙ G) i s =
      G.map (wDegInnerComponent F i s) := by
  simp only [wDegInnerComponent]
  rw [eqToHom_map]

/-- Outermost face commutes with postcomposition, inverse form. -/
theorem wbarFaceZero_mapIso_inv (n : ℕ)
    [Limits.HasCoproduct (fun p : WIdx J W (n + 1) => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W (n + 1) => (F ⋙ G).obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W n => (F ⋙ G).obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W (n + 1) => G.obj (F.obj p.1.left))]
    [Limits.HasCoproduct (fun p : WIdx J W n => G.obj (F.obj p.1.left))]
    [Limits.PreservesColimit
      (Discrete.functor (fun p : WIdx J W (n + 1) => F.obj p.1.left)) G]
    [Limits.PreservesColimit
      (Discrete.functor (fun p : WIdx J W n => F.obj p.1.left)) G] :
    (wbarObjMapIso (G := G) (n + 1)).inv ≫ G.map (wbarFaceZero W F n) =
      wbarFaceZero W (F ⋙ G) n ≫ (wbarObjMapIso (G := G) n).inv := by
  refine Limits.Sigma.hom_ext _ _ (fun p : WIdx J W (n + 1) => ?_)
  change wbarIncl W (F ⋙ G) (n + 1) p ≫
      ((wbarObjMapIso (G := G) (n + 1)).inv ≫ G.map (wbarFaceZero W F n)) =
    wbarIncl W (F ⋙ G) (n + 1) p ≫
      (wbarFaceZero W (F ⋙ G) n ≫ (wbarObjMapIso (G := G) n).inv)
  have hL : wbarIncl W (F ⋙ G) (n + 1) p ≫
      ((wbarObjMapIso (G := G) (n + 1)).inv ≫ G.map (wbarFaceZero W F n)) =
      G.map (SrepBridge.srepFaceZeroComponent F p.1) ≫
        G.map (wbarIncl W F n (wFaceZeroIdx W n p)) := by
    calc wbarIncl W (F ⋙ G) (n + 1) p ≫
            ((wbarObjMapIso (G := G) (n + 1)).inv ≫
              G.map (wbarFaceZero W F n))
        = (wbarIncl W (F ⋙ G) (n + 1) p ≫
            (wbarObjMapIso (G := G) (n + 1)).inv) ≫
            G.map (wbarFaceZero W F n) := by
          exact (Category.assoc _ _ _).symm
      _ = G.map (wbarIncl W F (n + 1) p) ≫ G.map (wbarFaceZero W F n) := by
          exact congrArg (· ≫ G.map (wbarFaceZero W F n))
            (wbarObjMapIso_inv_ι (G := G) (n + 1) p)
      _ = G.map (wbarIncl W F (n + 1) p ≫ wbarFaceZero W F n) := by
          exact (G.map_comp _ _).symm
      _ = G.map (SrepBridge.srepFaceZeroComponent F p.1 ≫
            wbarIncl W F n (wFaceZeroIdx W n p)) := by
          exact congrArg (G.map) (wbarFaceZero_ι W F n p)
      _ = G.map (SrepBridge.srepFaceZeroComponent F p.1) ≫
            G.map (wbarIncl W F n (wFaceZeroIdx W n p)) := by
          exact G.map_comp _ _
  have hR : wbarIncl W (F ⋙ G) (n + 1) p ≫
      (wbarFaceZero W (F ⋙ G) n ≫ (wbarObjMapIso (G := G) n).inv) =
      SrepBridge.srepFaceZeroComponent (F ⋙ G) p.1 ≫
        G.map (wbarIncl W F n (wFaceZeroIdx W n p)) := by
    calc wbarIncl W (F ⋙ G) (n + 1) p ≫
            (wbarFaceZero W (F ⋙ G) n ≫ (wbarObjMapIso (G := G) n).inv)
        = (wbarIncl W (F ⋙ G) (n + 1) p ≫ wbarFaceZero W (F ⋙ G) n) ≫
            (wbarObjMapIso (G := G) n).inv := by
          exact (Category.assoc _ _ _).symm
      _ = (SrepBridge.srepFaceZeroComponent (F ⋙ G) p.1 ≫
            wbarIncl W (F ⋙ G) n (wFaceZeroIdx W n p)) ≫
            (wbarObjMapIso (G := G) n).inv := by
          exact congrArg (· ≫ (wbarObjMapIso (G := G) n).inv)
            (wbarFaceZero_ι W (F ⋙ G) n p)
      _ = SrepBridge.srepFaceZeroComponent (F ⋙ G) p.1 ≫
            (wbarIncl W (F ⋙ G) n (wFaceZeroIdx W n p) ≫
              (wbarObjMapIso (G := G) n).inv) := by
          exact Category.assoc _ _ _
      _ = SrepBridge.srepFaceZeroComponent (F ⋙ G) p.1 ≫
            G.map (wbarIncl W F n (wFaceZeroIdx W n p)) := by
          exact congrArg (SrepBridge.srepFaceZeroComponent (F ⋙ G) p.1 ≫ ·)
            (wbarObjMapIso_inv_ι (G := G) n (wFaceZeroIdx W n p))
  have hcoeff : G.map (SrepBridge.srepFaceZeroComponent F p.1) =
      SrepBridge.srepFaceZeroComponent (F ⋙ G) p.1 :=
    (srepFaceZeroComponent_postcomp (G := G) p.1).symm
  calc wbarIncl W (F ⋙ G) (n + 1) p ≫
          ((wbarObjMapIso (G := G) (n + 1)).inv ≫
            G.map (wbarFaceZero W F n))
      = G.map (SrepBridge.srepFaceZeroComponent F p.1) ≫
          G.map (wbarIncl W F n (wFaceZeroIdx W n p)) := hL
    _ = SrepBridge.srepFaceZeroComponent (F ⋙ G) p.1 ≫
          G.map (wbarIncl W F n (wFaceZeroIdx W n p)) := by
        exact congrArg (· ≫ G.map (wbarIncl W F n (wFaceZeroIdx W n p))) hcoeff
    _ = wbarIncl W (F ⋙ G) (n + 1) p ≫
          (wbarFaceZero W (F ⋙ G) n ≫ (wbarObjMapIso (G := G) n).inv) :=
        hR.symm

/-- Last face commutes with postcomposition, inverse form. -/
theorem wbarFaceLast_mapIso_inv (n : ℕ)
    [Limits.HasCoproduct (fun p : WIdx J W (n + 1) => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W (n + 1) => (F ⋙ G).obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W n => (F ⋙ G).obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W (n + 1) => G.obj (F.obj p.1.left))]
    [Limits.HasCoproduct (fun p : WIdx J W n => G.obj (F.obj p.1.left))]
    [Limits.PreservesColimit
      (Discrete.functor (fun p : WIdx J W (n + 1) => F.obj p.1.left)) G]
    [Limits.PreservesColimit
      (Discrete.functor (fun p : WIdx J W n => F.obj p.1.left)) G] :
    (wbarObjMapIso (G := G) (n + 1)).inv ≫ G.map (wbarFaceLast W F n) =
      wbarFaceLast W (F ⋙ G) n ≫ (wbarObjMapIso (G := G) n).inv := by
  refine Limits.Sigma.hom_ext _ _ (fun p : WIdx J W (n + 1) => ?_)
  change wbarIncl W (F ⋙ G) (n + 1) p ≫
      ((wbarObjMapIso (G := G) (n + 1)).inv ≫ G.map (wbarFaceLast W F n)) =
    wbarIncl W (F ⋙ G) (n + 1) p ≫
      (wbarFaceLast W (F ⋙ G) n ≫ (wbarObjMapIso (G := G) n).inv)
  have hL : wbarIncl W (F ⋙ G) (n + 1) p ≫
      ((wbarObjMapIso (G := G) (n + 1)).inv ≫ G.map (wbarFaceLast W F n)) =
      G.map (SrepBridge.srepFaceLastComponent F p.1) ≫
        G.map (wbarIncl W F n (wFaceLastIdx W n p)) := by
    calc wbarIncl W (F ⋙ G) (n + 1) p ≫
            ((wbarObjMapIso (G := G) (n + 1)).inv ≫
              G.map (wbarFaceLast W F n))
        = (wbarIncl W (F ⋙ G) (n + 1) p ≫
            (wbarObjMapIso (G := G) (n + 1)).inv) ≫
            G.map (wbarFaceLast W F n) := by
          exact (Category.assoc _ _ _).symm
      _ = G.map (wbarIncl W F (n + 1) p) ≫ G.map (wbarFaceLast W F n) := by
          exact congrArg (· ≫ G.map (wbarFaceLast W F n))
            (wbarObjMapIso_inv_ι (G := G) (n + 1) p)
      _ = G.map (wbarIncl W F (n + 1) p ≫ wbarFaceLast W F n) := by
          exact (G.map_comp _ _).symm
      _ = G.map (SrepBridge.srepFaceLastComponent F p.1 ≫
            wbarIncl W F n (wFaceLastIdx W n p)) := by
          exact congrArg (G.map) (wbarFaceLast_ι W F n p)
      _ = G.map (SrepBridge.srepFaceLastComponent F p.1) ≫
            G.map (wbarIncl W F n (wFaceLastIdx W n p)) := by
          exact G.map_comp _ _
  have hR : wbarIncl W (F ⋙ G) (n + 1) p ≫
      (wbarFaceLast W (F ⋙ G) n ≫ (wbarObjMapIso (G := G) n).inv) =
      SrepBridge.srepFaceLastComponent (F ⋙ G) p.1 ≫
        G.map (wbarIncl W F n (wFaceLastIdx W n p)) := by
    calc wbarIncl W (F ⋙ G) (n + 1) p ≫
            (wbarFaceLast W (F ⋙ G) n ≫ (wbarObjMapIso (G := G) n).inv)
        = (wbarIncl W (F ⋙ G) (n + 1) p ≫ wbarFaceLast W (F ⋙ G) n) ≫
            (wbarObjMapIso (G := G) n).inv := by
          exact (Category.assoc _ _ _).symm
      _ = (SrepBridge.srepFaceLastComponent (F ⋙ G) p.1 ≫
            wbarIncl W (F ⋙ G) n (wFaceLastIdx W n p)) ≫
            (wbarObjMapIso (G := G) n).inv := by
          exact congrArg (· ≫ (wbarObjMapIso (G := G) n).inv)
            (wbarFaceLast_ι W (F ⋙ G) n p)
      _ = SrepBridge.srepFaceLastComponent (F ⋙ G) p.1 ≫
            (wbarIncl W (F ⋙ G) n (wFaceLastIdx W n p) ≫
              (wbarObjMapIso (G := G) n).inv) := by
          exact Category.assoc _ _ _
      _ = SrepBridge.srepFaceLastComponent (F ⋙ G) p.1 ≫
            G.map (wbarIncl W F n (wFaceLastIdx W n p)) := by
          exact congrArg (SrepBridge.srepFaceLastComponent (F ⋙ G) p.1 ≫ ·)
            (wbarObjMapIso_inv_ι (G := G) n (wFaceLastIdx W n p))
  have hcoeff : G.map (SrepBridge.srepFaceLastComponent F p.1) =
      SrepBridge.srepFaceLastComponent (F ⋙ G) p.1 :=
    (srepFaceLastComponent_postcomp (G := G) p.1).symm
  calc wbarIncl W (F ⋙ G) (n + 1) p ≫
          ((wbarObjMapIso (G := G) (n + 1)).inv ≫
            G.map (wbarFaceLast W F n))
      = G.map (SrepBridge.srepFaceLastComponent F p.1) ≫
          G.map (wbarIncl W F n (wFaceLastIdx W n p)) := hL
    _ = SrepBridge.srepFaceLastComponent (F ⋙ G) p.1 ≫
          G.map (wbarIncl W F n (wFaceLastIdx W n p)) := by
        exact congrArg (· ≫ G.map (wbarIncl W F n (wFaceLastIdx W n p))) hcoeff
    _ = wbarIncl W (F ⋙ G) (n + 1) p ≫
          (wbarFaceLast W (F ⋙ G) n ≫ (wbarObjMapIso (G := G) n).inv) :=
        hR.symm

/-- Interior face commutes with postcomposition, inverse form. -/
theorem wbarFaceInner_mapIso_inv (n : ℕ) (i : Fin (n + 2))
    (hi0 : i ≠ 0) (hiLast : i ≠ Fin.last (n + 1)) [NeZero (n + 1)]
    [Limits.HasCoproduct (fun p : WIdx J W (n + 1) => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W (n + 1) => (F ⋙ G).obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W n => (F ⋙ G).obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W (n + 1) => G.obj (F.obj p.1.left))]
    [Limits.HasCoproduct (fun p : WIdx J W n => G.obj (F.obj p.1.left))]
    [Limits.PreservesColimit
      (Discrete.functor (fun p : WIdx J W (n + 1) => F.obj p.1.left)) G]
    [Limits.PreservesColimit
      (Discrete.functor (fun p : WIdx J W n => F.obj p.1.left)) G] :
    (wbarObjMapIso (G := G) (n + 1)).inv ≫
        G.map (wbarFaceInner W F n i hi0 hiLast) =
      wbarFaceInner W (F ⋙ G) n i hi0 hiLast ≫
        (wbarObjMapIso (G := G) n).inv := by
  refine Limits.Sigma.hom_ext _ _ (fun p : WIdx J W (n + 1) => ?_)
  change wbarIncl W (F ⋙ G) (n + 1) p ≫
      ((wbarObjMapIso (G := G) (n + 1)).inv ≫
        G.map (wbarFaceInner W F n i hi0 hiLast)) =
    wbarIncl W (F ⋙ G) (n + 1) p ≫
      (wbarFaceInner W (F ⋙ G) n i hi0 hiLast ≫
        (wbarObjMapIso (G := G) n).inv)
  have hL : wbarIncl W (F ⋙ G) (n + 1) p ≫
      ((wbarObjMapIso (G := G) (n + 1)).inv ≫
        G.map (wbarFaceInner W F n i hi0 hiLast)) =
      G.map (wFaceInnerComponent F i hi0 p.1) ≫
        G.map (wbarIncl W F n (wFaceInnerIdx W n i hiLast p)) := by
    calc wbarIncl W (F ⋙ G) (n + 1) p ≫
            ((wbarObjMapIso (G := G) (n + 1)).inv ≫
              G.map (wbarFaceInner W F n i hi0 hiLast))
        = (wbarIncl W (F ⋙ G) (n + 1) p ≫
            (wbarObjMapIso (G := G) (n + 1)).inv) ≫
            G.map (wbarFaceInner W F n i hi0 hiLast) := by
          exact (Category.assoc _ _ _).symm
      _ = G.map (wbarIncl W F (n + 1) p) ≫
            G.map (wbarFaceInner W F n i hi0 hiLast) := by
          exact congrArg (· ≫ G.map (wbarFaceInner W F n i hi0 hiLast))
            (wbarObjMapIso_inv_ι (G := G) (n + 1) p)
      _ = G.map (wbarIncl W F (n + 1) p ≫
            wbarFaceInner W F n i hi0 hiLast) := by
          exact (G.map_comp _ _).symm
      _ = G.map (wFaceInnerComponent F i hi0 p.1 ≫
            wbarIncl W F n (wFaceInnerIdx W n i hiLast p)) := by
          exact congrArg (G.map) (wbarFaceInner_ι W F n i hi0 hiLast p)
      _ = G.map (wFaceInnerComponent F i hi0 p.1) ≫
            G.map (wbarIncl W F n (wFaceInnerIdx W n i hiLast p)) := by
          exact G.map_comp _ _
  have hR : wbarIncl W (F ⋙ G) (n + 1) p ≫
      (wbarFaceInner W (F ⋙ G) n i hi0 hiLast ≫
        (wbarObjMapIso (G := G) n).inv) =
      wFaceInnerComponent (F ⋙ G) i hi0 p.1 ≫
        G.map (wbarIncl W F n (wFaceInnerIdx W n i hiLast p)) := by
    calc wbarIncl W (F ⋙ G) (n + 1) p ≫
            (wbarFaceInner W (F ⋙ G) n i hi0 hiLast ≫
              (wbarObjMapIso (G := G) n).inv)
        = (wbarIncl W (F ⋙ G) (n + 1) p ≫
            wbarFaceInner W (F ⋙ G) n i hi0 hiLast) ≫
            (wbarObjMapIso (G := G) n).inv := by
          exact (Category.assoc _ _ _).symm
      _ = (wFaceInnerComponent (F ⋙ G) i hi0 p.1 ≫
            wbarIncl W (F ⋙ G) n (wFaceInnerIdx W n i hiLast p)) ≫
            (wbarObjMapIso (G := G) n).inv := by
          exact congrArg (· ≫ (wbarObjMapIso (G := G) n).inv)
            (wbarFaceInner_ι W (F ⋙ G) n i hi0 hiLast p)
      _ = wFaceInnerComponent (F ⋙ G) i hi0 p.1 ≫
            (wbarIncl W (F ⋙ G) n (wFaceInnerIdx W n i hiLast p) ≫
              (wbarObjMapIso (G := G) n).inv) := by
          exact Category.assoc _ _ _
      _ = wFaceInnerComponent (F ⋙ G) i hi0 p.1 ≫
            G.map (wbarIncl W F n (wFaceInnerIdx W n i hiLast p)) := by
          exact congrArg (wFaceInnerComponent (F ⋙ G) i hi0 p.1 ≫ ·)
            (wbarObjMapIso_inv_ι (G := G) n (wFaceInnerIdx W n i hiLast p))
  have hcoeff : G.map (wFaceInnerComponent F i hi0 p.1) =
      wFaceInnerComponent (F ⋙ G) i hi0 p.1 :=
    (wFaceInnerComponent_postcomp (G := G) i hi0 p.1).symm
  calc wbarIncl W (F ⋙ G) (n + 1) p ≫
          ((wbarObjMapIso (G := G) (n + 1)).inv ≫
            G.map (wbarFaceInner W F n i hi0 hiLast))
      = G.map (wFaceInnerComponent F i hi0 p.1) ≫
          G.map (wbarIncl W F n (wFaceInnerIdx W n i hiLast p)) := hL
    _ = wFaceInnerComponent (F ⋙ G) i hi0 p.1 ≫
          G.map (wbarIncl W F n (wFaceInnerIdx W n i hiLast p)) := by
        exact congrArg
          (· ≫ G.map (wbarIncl W F n (wFaceInnerIdx W n i hiLast p))) hcoeff
    _ = wbarIncl W (F ⋙ G) (n + 1) p ≫
          (wbarFaceInner W (F ⋙ G) n i hi0 hiLast ≫
            (wbarObjMapIso (G := G) n).inv) := hR.symm

/-- Interior degeneracy commutes with postcomposition, inverse form. -/
theorem wbarDegInner_mapIso_inv (n : ℕ) (i : Fin (n + 1)) [NeZero (n + 1)]
    [Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W (n + 1) => F.obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W n => (F ⋙ G).obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W (n + 1) => (F ⋙ G).obj p.1.left)]
    [Limits.HasCoproduct (fun p : WIdx J W n => G.obj (F.obj p.1.left))]
    [Limits.HasCoproduct (fun p : WIdx J W (n + 1) => G.obj (F.obj p.1.left))]
    [Limits.PreservesColimit
      (Discrete.functor (fun p : WIdx J W n => F.obj p.1.left)) G]
    [Limits.PreservesColimit
      (Discrete.functor (fun p : WIdx J W (n + 1) => F.obj p.1.left)) G] :
    (wbarObjMapIso (G := G) n).inv ≫ G.map (wbarDegInner W F n i) =
      wbarDegInner W (F ⋙ G) n i ≫ (wbarObjMapIso (G := G) (n + 1)).inv := by
  refine Limits.Sigma.hom_ext _ _ (fun p : WIdx J W n => ?_)
  change wbarIncl W (F ⋙ G) n p ≫
      ((wbarObjMapIso (G := G) n).inv ≫ G.map (wbarDegInner W F n i)) =
    wbarIncl W (F ⋙ G) n p ≫
      (wbarDegInner W (F ⋙ G) n i ≫ (wbarObjMapIso (G := G) (n + 1)).inv)
  have hL : wbarIncl W (F ⋙ G) n p ≫
      ((wbarObjMapIso (G := G) n).inv ≫ G.map (wbarDegInner W F n i)) =
      G.map (wDegInnerComponent F i p.1) ≫
        G.map (wbarIncl W F (n + 1) (wDegInnerIdx W n i p)) := by
    calc wbarIncl W (F ⋙ G) n p ≫
            ((wbarObjMapIso (G := G) n).inv ≫ G.map (wbarDegInner W F n i))
        = (wbarIncl W (F ⋙ G) n p ≫ (wbarObjMapIso (G := G) n).inv) ≫
            G.map (wbarDegInner W F n i) := by
          exact (Category.assoc _ _ _).symm
      _ = G.map (wbarIncl W F n p) ≫ G.map (wbarDegInner W F n i) := by
          exact congrArg (· ≫ G.map (wbarDegInner W F n i))
            (wbarObjMapIso_inv_ι (G := G) n p)
      _ = G.map (wbarIncl W F n p ≫ wbarDegInner W F n i) := by
          exact (G.map_comp _ _).symm
      _ = G.map (wDegInnerComponent F i p.1 ≫
            wbarIncl W F (n + 1) (wDegInnerIdx W n i p)) := by
          exact congrArg (G.map) (wbarDegInner_ι W F n i p)
      _ = G.map (wDegInnerComponent F i p.1) ≫
            G.map (wbarIncl W F (n + 1) (wDegInnerIdx W n i p)) := by
          exact G.map_comp _ _
  have hR : wbarIncl W (F ⋙ G) n p ≫
      (wbarDegInner W (F ⋙ G) n i ≫ (wbarObjMapIso (G := G) (n + 1)).inv) =
      wDegInnerComponent (F ⋙ G) i p.1 ≫
        G.map (wbarIncl W F (n + 1) (wDegInnerIdx W n i p)) := by
    calc wbarIncl W (F ⋙ G) n p ≫
            (wbarDegInner W (F ⋙ G) n i ≫
              (wbarObjMapIso (G := G) (n + 1)).inv)
        = (wbarIncl W (F ⋙ G) n p ≫ wbarDegInner W (F ⋙ G) n i) ≫
            (wbarObjMapIso (G := G) (n + 1)).inv := by
          exact (Category.assoc _ _ _).symm
      _ = (wDegInnerComponent (F ⋙ G) i p.1 ≫
            wbarIncl W (F ⋙ G) (n + 1) (wDegInnerIdx W n i p)) ≫
            (wbarObjMapIso (G := G) (n + 1)).inv := by
          exact congrArg (· ≫ (wbarObjMapIso (G := G) (n + 1)).inv)
            (wbarDegInner_ι W (F ⋙ G) n i p)
      _ = wDegInnerComponent (F ⋙ G) i p.1 ≫
            (wbarIncl W (F ⋙ G) (n + 1) (wDegInnerIdx W n i p) ≫
              (wbarObjMapIso (G := G) (n + 1)).inv) := by
          exact Category.assoc _ _ _
      _ = wDegInnerComponent (F ⋙ G) i p.1 ≫
            G.map (wbarIncl W F (n + 1) (wDegInnerIdx W n i p)) := by
          exact congrArg (wDegInnerComponent (F ⋙ G) i p.1 ≫ ·)
            (wbarObjMapIso_inv_ι (G := G) (n + 1) (wDegInnerIdx W n i p))
  have hcoeff : G.map (wDegInnerComponent F i p.1) =
      wDegInnerComponent (F ⋙ G) i p.1 :=
    (wDegInnerComponent_postcomp (G := G) i p.1).symm
  calc wbarIncl W (F ⋙ G) n p ≫
          ((wbarObjMapIso (G := G) n).inv ≫ G.map (wbarDegInner W F n i))
      = G.map (wDegInnerComponent F i p.1) ≫
          G.map (wbarIncl W F (n + 1) (wDegInnerIdx W n i p)) := hL
    _ = wDegInnerComponent (F ⋙ G) i p.1 ≫
          G.map (wbarIncl W F (n + 1) (wDegInnerIdx W n i p)) := by
        exact congrArg
          (· ≫ G.map (wbarIncl W F (n + 1) (wDegInnerIdx W n i p))) hcoeff
    _ = wbarIncl W (F ⋙ G) n p ≫
          (wbarDegInner W (F ⋙ G) n i ≫
            (wbarObjMapIso (G := G) (n + 1)).inv) := hR.symm

/-- Total face commutes with postcomposition, inverse form, by
zero/last/interior dispatch. -/
theorem wbarδ_mapIso_inv (n : ℕ) (i : Fin (n + 2))
    [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => (F ⋙ G).obj p.1.left)]
    [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => G.obj (F.obj p.1.left))]
    [∀ n, Limits.PreservesColimit
      (Discrete.functor (fun p : WIdx J W n => F.obj p.1.left)) G] :
    (wbarObjMapIso (G := G) (n + 1)).inv ≫ G.map (wbarδ W F n i) =
      wbarδ W (F ⋙ G) n i ≫ (wbarObjMapIso (G := G) n).inv := by
  by_cases h0 : i = 0
  · subst h0
    rw [wbarδ_zero, wbarδ_zero]
    exact wbarFaceZero_mapIso_inv (G := G) n
  · by_cases hlast : i = Fin.last (n + 1)
    · subst hlast
      rw [wbarδ_last, wbarδ_last]
      exact wbarFaceLast_mapIso_inv (G := G) n
    · have : NeZero (n + 1) := ⟨by omega⟩
      rw [wbarδ_inner _ _ _ i h0 hlast, wbarδ_inner _ _ _ i h0 hlast]
      exact wbarFaceInner_mapIso_inv (G := G) n i h0 hlast

/-- Total degeneracy commutes with postcomposition, inverse form. -/
theorem wbarσ_mapIso_inv (n : ℕ) (i : Fin (n + 1))
    [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => (F ⋙ G).obj p.1.left)]
    [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => G.obj (F.obj p.1.left))]
    [∀ n, Limits.PreservesColimit
      (Discrete.functor (fun p : WIdx J W n => F.obj p.1.left)) G] :
    (wbarObjMapIso (G := G) n).inv ≫ G.map (wbarσ W F n i) =
      wbarσ W (F ⋙ G) n i ≫ (wbarObjMapIso (G := G) (n + 1)).inv := by
  have : NeZero (n + 1) := ⟨by omega⟩
  unfold wbarσ
  exact wbarDegInner_mapIso_inv (G := G) n i

/-- An inverse-form square is a forward-form square. -/
theorem inv_comp_to_hom_comp {X₁ X₂ Y₁ Y₂ : D} (e₁ : X₁ ≅ Y₁) (e₂ : X₂ ≅ Y₂)
    {a : X₁ ⟶ X₂} {b : Y₁ ⟶ Y₂} (h : e₁.inv ≫ a = b ≫ e₂.inv) :
    a ≫ e₂.hom = e₁.hom ≫ b := by
  have h2 : e₁.inv ≫ (a ≫ e₂.hom) = e₁.inv ≫ (e₁.hom ≫ b) := by
    rw [← Category.assoc, h, Category.assoc, Iso.inv_hom_id,
      Category.comp_id, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  calc a ≫ e₂.hom = 𝟙 _ ≫ (a ≫ e₂.hom) := by simp
    _ = (e₁.hom ≫ e₁.inv) ≫ (a ≫ e₂.hom) := by rw [Iso.hom_inv_id]
    _ = e₁.hom ≫ (e₁.inv ≫ (a ≫ e₂.hom)) := by simp
    _ = e₁.hom ≫ (e₁.inv ≫ (e₁.hom ≫ b)) := by rw [h2]
    _ = e₁.hom ≫ b := by simp

/-- Bundled data isomorphism for postcomposition, stated with `mapObj` so it
meets the postcomposition comparison syntactically. -/
noncomputable def wbarDataMapPostcompIso
    [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => (F ⋙ G).obj p.1.left)]
    [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => G.obj (F.obj p.1.left))]
    [∀ n, Limits.PreservesColimit
      (Discrete.functor (fun p : WIdx J W n => F.obj p.1.left)) G] :
    (SimplicialObject.Data.mapObj G (wbarData W F)) ≅
      wbarData W (F ⋙ G) :=
  SimplicialObject.Data.isoOfIso (fun n => wbarObjMapIso (G := G) n)
    (fun {n} i => by
      rw [SimplicialObject.Data.mapObj_δ, wbarData_δ, wbarData_δ]
      exact (inv_comp_to_hom_comp _ _
        (wbarδ_mapIso_inv (W := W) (F := F) (G := G) n i)).symm)
    (fun {n} i => by
      rw [SimplicialObject.Data.mapObj_σ, wbarData_σ, wbarData_σ]
      exact (inv_comp_to_hom_comp _ _
        (wbarσ_mapIso_inv (W := W) (F := F) (G := G) n i)).symm)

/-- Simplicial isomorphism for postcomposition, via the data transport. -/
noncomputable def wbarSimplicialDataIso
    [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => (F ⋙ G).obj p.1.left)]
    [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => G.obj (F.obj p.1.left))]
    [∀ n, Limits.PreservesColimit
      (Discrete.functor (fun p : WIdx J W n => F.obj p.1.left)) G] :
    (SimplicialObject.Data.mapObj G (wbarData W F)).toSimplicialObject ≅
      (wbarData W (F ⋙ G)).toSimplicialObject where
  hom := SimplicialObject.Data.toSimplicialNatTrans
    (wbarDataMapPostcompIso (W := W) (F := F) (G := G)).hom
  inv := SimplicialObject.Data.toSimplicialNatTrans
    (wbarDataMapPostcompIso (W := W) (F := F) (G := G)).inv
  hom_inv_id := by
    change (SimplicialObject.Data.toSimplicialFunctor (C := D)).map _ ≫
      (SimplicialObject.Data.toSimplicialFunctor (C := D)).map _ = 𝟙 _
    rw [← Functor.map_comp, Iso.hom_inv_id, Functor.map_id]
  inv_hom_id := by
    change (SimplicialObject.Data.toSimplicialFunctor (C := D)).map _ ≫
      (SimplicialObject.Data.toSimplicialFunctor (C := D)).map _ = 𝟙 _
    rw [← Functor.map_comp, Iso.inv_hom_id, Functor.map_id]

/-- Bundled simplicial isomorphism for postcomposition. -/
noncomputable def wbarSimplicialMapPostcompIso
    [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => (F ⋙ G).obj p.1.left)]
    [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => G.obj (F.obj p.1.left))]
    [∀ n, Limits.PreservesColimit
      (Discrete.functor (fun p : WIdx J W n => F.obj p.1.left)) G] :
    (wbarSimplicial W F ⋙ G) ≅ wbarSimplicial W (F ⋙ G) :=
  (SimplicialObject.Data.toSimplicialObject_mapObjIso G (wbarData W F)).trans
    (wbarSimplicialDataIso (W := W) (F := F) (G := G))

/-- Degree computation for the bundled simplicial isomorphism. -/
@[simp]
theorem wbarSimplicialMapPostcompIso_hom_app_mk
    [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => (F ⋙ G).obj p.1.left)]
    [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => G.obj (F.obj p.1.left))]
    [∀ n, Limits.PreservesColimit
      (Discrete.functor (fun p : WIdx J W n => F.obj p.1.left)) G]
    (n : ℕ) :
    (wbarSimplicialMapPostcompIso (W := W) (F := F) (G := G)).hom.app
        (Opposite.op (SimplexCategory.mk n)) =
      (wbarObjMapIso (G := G) n).hom := by
  have h1 : (wbarSimplicialMapPostcompIso (W := W) (F := F) (G := G)).hom.app
          (Opposite.op (SimplexCategory.mk n)) =
        ((SimplicialObject.Data.toSimplicialObject_mapObjIso G
            (wbarData W F)).trans
            (wbarSimplicialDataIso (W := W) (F := F) (G := G))).hom.app
          (Opposite.op (SimplexCategory.mk n)) := rfl
  have h2 : ((SimplicialObject.Data.toSimplicialObject_mapObjIso G
          (wbarData W F)).trans
          (wbarSimplicialDataIso (W := W) (F := F) (G := G))).hom.app
        (Opposite.op (SimplexCategory.mk n)) =
        (SimplicialObject.Data.toSimplicialObject_mapObjIso G
            (wbarData W F)).hom.app
          (Opposite.op (SimplexCategory.mk n)) ≫
          (wbarSimplicialDataIso (W := W) (F := F) (G := G)).hom.app
            (Opposite.op (SimplexCategory.mk n)) := rfl
  have h3 : (SimplicialObject.Data.toSimplicialObject_mapObjIso G
          (wbarData W F)).hom.app (Opposite.op (SimplexCategory.mk n)) ≫
        (wbarSimplicialDataIso (W := W) (F := F) (G := G)).hom.app
          (Opposite.op (SimplexCategory.mk n)) =
        𝟙 _ ≫ (wbarSimplicialDataIso (W := W) (F := F) (G := G)).hom.app
          (Opposite.op (SimplexCategory.mk n)) :=
    congrArg (· ≫ _)
      (SimplicialObject.Data.toSimplicialObject_mapObjIso_hom_app_mk _ _ _)
  have h4 : 𝟙 _ ≫ (wbarSimplicialDataIso (W := W) (F := F) (G := G)).hom.app
        (Opposite.op (SimplexCategory.mk n)) =
      (wbarSimplicialDataIso (W := W) (F := F) (G := G)).hom.app
        (Opposite.op (SimplexCategory.mk n)) := Category.id_comp _
  have h5 : (wbarSimplicialDataIso (W := W) (F := F) (G := G)).hom.app
        (Opposite.op (SimplexCategory.mk n)) =
      (SimplicialObject.Data.toSimplicialNatTrans
          (wbarDataMapPostcompIso (W := W) (F := F) (G := G)).hom).app
        (Opposite.op (SimplexCategory.mk n)) := rfl
  have h6 : (SimplicialObject.Data.toSimplicialNatTrans
        (wbarDataMapPostcompIso (W := W) (F := F) (G := G)).hom).app
      (Opposite.op (SimplexCategory.mk n)) =
      (wbarDataMapPostcompIso (W := W) (F := F) (G := G)).hom.app n :=
    SimplicialObject.Data.toSimplicialNatTrans_app_mk _ _
  have h7 : (wbarDataMapPostcompIso (W := W) (F := F) (G := G)).hom.app n =
      (wbarObjMapIso (G := G) n).hom :=
    SimplicialObject.Data.isoOfIso_hom_app _ _ _ _
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans h7)))))

/-- Degree computation for the inverse direction. -/
@[simp]
theorem wbarSimplicialMapPostcompIso_inv_app_mk
    [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => (F ⋙ G).obj p.1.left)]
    [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => G.obj (F.obj p.1.left))]
    [∀ n, Limits.PreservesColimit
      (Discrete.functor (fun p : WIdx J W n => F.obj p.1.left)) G]
    (n : ℕ) :
    (wbarSimplicialMapPostcompIso (W := W) (F := F) (G := G)).inv.app
        (Opposite.op (SimplexCategory.mk n)) =
      (wbarObjMapIso (G := G) n).inv := by
  have h1 : (wbarSimplicialMapPostcompIso (W := W) (F := F) (G := G)).inv.app
          (Opposite.op (SimplexCategory.mk n)) =
        ((SimplicialObject.Data.toSimplicialObject_mapObjIso G
            (wbarData W F)).trans
            (wbarSimplicialDataIso (W := W) (F := F) (G := G))).inv.app
          (Opposite.op (SimplexCategory.mk n)) := rfl
  have h2 : ((SimplicialObject.Data.toSimplicialObject_mapObjIso G
          (wbarData W F)).trans
          (wbarSimplicialDataIso (W := W) (F := F) (G := G))).inv.app
        (Opposite.op (SimplexCategory.mk n)) =
        (wbarSimplicialDataIso (W := W) (F := F) (G := G)).inv.app
          (Opposite.op (SimplexCategory.mk n)) ≫
          (SimplicialObject.Data.toSimplicialObject_mapObjIso G
            (wbarData W F)).inv.app
            (Opposite.op (SimplexCategory.mk n)) := rfl
  have h3 : (wbarSimplicialDataIso (W := W) (F := F) (G := G)).inv.app
        (Opposite.op (SimplexCategory.mk n)) ≫
        (SimplicialObject.Data.toSimplicialObject_mapObjIso G
          (wbarData W F)).inv.app
          (Opposite.op (SimplexCategory.mk n)) =
        (wbarSimplicialDataIso (W := W) (F := F) (G := G)).inv.app
          (Opposite.op (SimplexCategory.mk n)) ≫ 𝟙 _ :=
    congrArg _
      (SimplicialObject.Data.toSimplicialObject_mapObjIso_inv_app_mk _ _ _)
  have h4 : (wbarSimplicialDataIso (W := W) (F := F) (G := G)).inv.app
        (Opposite.op (SimplexCategory.mk n)) ≫ 𝟙 _ =
      (wbarSimplicialDataIso (W := W) (F := F) (G := G)).inv.app
        (Opposite.op (SimplexCategory.mk n)) := Category.comp_id _
  have h5 : (wbarSimplicialDataIso (W := W) (F := F) (G := G)).inv.app
        (Opposite.op (SimplexCategory.mk n)) =
      (SimplicialObject.Data.toSimplicialNatTrans
          (wbarDataMapPostcompIso (W := W) (F := F) (G := G)).inv).app
        (Opposite.op (SimplexCategory.mk n)) := rfl
  have h6 : (SimplicialObject.Data.toSimplicialNatTrans
        (wbarDataMapPostcompIso (W := W) (F := F) (G := G)).inv).app
      (Opposite.op (SimplexCategory.mk n)) =
      (wbarDataMapPostcompIso (W := W) (F := F) (G := G)).inv.app n :=
    SimplicialObject.Data.toSimplicialNatTrans_app_mk _ _
  have h7 : (wbarDataMapPostcompIso (W := W) (F := F) (G := G)).inv.app n =
      (wbarObjMapIso (G := G) n).inv :=
    SimplicialObject.Data.isoOfIso_inv_app _ _ _ _
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans h7)))))

end WbarPostcomp

end StrictOrdinaryWeightedBar
end CategoryTheory

end
