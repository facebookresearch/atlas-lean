/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Fiber
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.PathSpace

/-!
# Explicit simplicial path homotopy fibers

This file defines the path-object model of a homotopy pullback, its
functoriality under compatible cospan maps, the based path homotopy fiber,
and the canonical map from the strict simplicial fiber.

It is purely categorical: no model structure, fibrancy, properness,
realization, weak-equivalence, or bar-construction result is used.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalClosed
  Simplicial
open scoped Simplicial

universe u

namespace SSet

/-- The two endpoint evaluations as a categorical-product map. -/
private noncomputable def pathEndpointPair (B : SSet.{u}) :
    SSet.pathSpace B ⟶ B ⨯ B :=
  SSet.evalPair ≫
    (CartesianMonoidalCategory.tensorLeftIsoProd B).hom.app B

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
private theorem pathEndpointPair_fst (B : SSet.{u}) :
    pathEndpointPair B ≫ Limits.prod.fst = SSet.eval₀ := by
  rw [pathEndpointPair, Category.assoc, tensorLeftIsoProd_hom_fst]
  exact SSet.evalPair_fst

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
private theorem pathEndpointPair_snd (B : SSet.{u}) :
    pathEndpointPair B ≫ Limits.prod.snd = SSet.eval₁ := by
  rw [pathEndpointPair, Category.assoc, tensorLeftIsoProd_hom_snd]
  exact SSet.evalPair_snd

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem pathEndpointPair_naturality
    {B B' : SSet.{u}} (h : B ⟶ B') :
    (ihom (Δ[1] : SSet.{u})).map h ≫ pathEndpointPair B' =
      pathEndpointPair B ≫ Limits.prod.map h h := by
  apply Limits.prod.hom_ext
  · simp only [Category.assoc, pathEndpointPair_fst,
      Limits.prod.map_fst]
    rw [← Category.assoc, pathEndpointPair_fst]
    exact SSet.pathSpace_map_eval₀ h
  · simp only [Category.assoc, pathEndpointPair_snd,
      Limits.prod.map_snd]
    rw [← Category.assoc, pathEndpointPair_snd]
    exact SSet.pathSpace_map_eval₁ h

/-- Explicit path model for a homotopy pullback. -/
noncomputable abbrev pathHomotopyPullback
    {X Y B : SSet.{u}} (f : X ⟶ B) (g : Y ⟶ B) : SSet.{u} :=
  pullback (Limits.prod.map f g) (pathEndpointPair B)

noncomputable abbrev pathHomotopyPullbackLeft
    {X Y B : SSet.{u}} (f : X ⟶ B) (g : Y ⟶ B) :
    pathHomotopyPullback f g ⟶ X :=
  pullback.fst (Limits.prod.map f g) (pathEndpointPair B) ≫ Limits.prod.fst

noncomputable abbrev pathHomotopyPullbackRight
    {X Y B : SSet.{u}} (f : X ⟶ B) (g : Y ⟶ B) :
    pathHomotopyPullback f g ⟶ Y :=
  pullback.fst (Limits.prod.map f g) (pathEndpointPair B) ≫ Limits.prod.snd

noncomputable abbrev pathHomotopyPullbackPath
    {X Y B : SSet.{u}} (f : X ⟶ B) (g : Y ⟶ B) :
    pathHomotopyPullback f g ⟶ SSet.pathSpace B :=
  pullback.snd (Limits.prod.map f g) (pathEndpointPair B)

@[reassoc]
theorem pathHomotopyPullbackPath_evalZero
    {X Y B : SSet.{u}} (f : X ⟶ B) (g : Y ⟶ B) :
    pathHomotopyPullbackPath f g ≫ SSet.eval₀ =
      pathHomotopyPullbackLeft f g ≫ f := by
  have h := congrArg (fun k => k ≫ Limits.prod.fst)
    (pullback.condition
      (f := Limits.prod.map f g) (g := pathEndpointPair B))
  simpa only [Category.assoc, Limits.prod.map_fst,
    pathEndpointPair_fst] using h.symm

@[reassoc]
theorem pathHomotopyPullbackPath_evalOne
    {X Y B : SSet.{u}} (f : X ⟶ B) (g : Y ⟶ B) :
    pathHomotopyPullbackPath f g ≫ SSet.eval₁ =
      pathHomotopyPullbackRight f g ≫ g := by
  have h := congrArg (fun k => k ≫ Limits.prod.snd)
    (pullback.condition
      (f := Limits.prod.map f g) (g := pathEndpointPair B))
  simpa only [Category.assoc, Limits.prod.map_snd,
    pathEndpointPair_snd] using h.symm

theorem pathHomotopyPullback_hom_ext
    {X Y B Z : SSet.{u}} {f : X ⟶ B} {g : Y ⟶ B}
    {a b : Z ⟶ pathHomotopyPullback f g}
    (hleft : a ≫ pathHomotopyPullbackLeft f g =
      b ≫ pathHomotopyPullbackLeft f g)
    (hright : a ≫ pathHomotopyPullbackRight f g =
      b ≫ pathHomotopyPullbackRight f g)
    (hpath : a ≫ pathHomotopyPullbackPath f g =
      b ≫ pathHomotopyPullbackPath f g) : a = b := by
  apply pullback.hom_ext
  · apply Limits.prod.hom_ext
    · simpa only [Category.assoc] using hleft
    · simpa only [Category.assoc] using hright
  · exact hpath

/-- Map induced by a compatible map between two cospans. -/
noncomputable def pathHomotopyPullbackMap
    {X Y B X' Y' B' : SSet.{u}}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : X' ⟶ B'} {g' : Y' ⟶ B'}
    (l : X ⟶ X') (r : Y ⟶ Y') (h : B ⟶ B')
    (hf : f ≫ h = l ≫ f') (hg : g ≫ h = r ≫ g') :
    pathHomotopyPullback f g ⟶ pathHomotopyPullback f' g' :=
  pullback.lift
    (pullback.fst (Limits.prod.map f g) (pathEndpointPair B) ≫
      Limits.prod.map l r)
    (pullback.snd (Limits.prod.map f g) (pathEndpointPair B) ≫
      (ihom (Δ[1] : SSet.{u})).map h)
    (by
      calc
        (pullback.fst (Limits.prod.map f g) (pathEndpointPair B) ≫
              Limits.prod.map l r) ≫ Limits.prod.map f' g' =
            pullback.fst (Limits.prod.map f g) (pathEndpointPair B) ≫
              (Limits.prod.map l r ≫ Limits.prod.map f' g') :=
          Category.assoc _ _ _
        _ = pullback.fst (Limits.prod.map f g) (pathEndpointPair B) ≫
              Limits.prod.map (l ≫ f') (r ≫ g') := by
          rw [Limits.prod.map_map]
        _ = pullback.fst (Limits.prod.map f g) (pathEndpointPair B) ≫
              Limits.prod.map (f ≫ h) (g ≫ h) := by
          rw [hf, hg]
        _ = pullback.fst (Limits.prod.map f g) (pathEndpointPair B) ≫
              (Limits.prod.map f g ≫ Limits.prod.map h h) := by
          rw [Limits.prod.map_map]
        _ = (pullback.fst (Limits.prod.map f g) (pathEndpointPair B) ≫
              Limits.prod.map f g) ≫ Limits.prod.map h h :=
          (Category.assoc _ _ _).symm
        _ = (pullback.snd (Limits.prod.map f g) (pathEndpointPair B) ≫
              pathEndpointPair B) ≫ Limits.prod.map h h := by
          rw [pullback.condition]
        _ = pullback.snd (Limits.prod.map f g) (pathEndpointPair B) ≫
              (pathEndpointPair B ≫ Limits.prod.map h h) :=
          Category.assoc _ _ _
        _ = pullback.snd (Limits.prod.map f g) (pathEndpointPair B) ≫
              ((ihom (Δ[1] : SSet.{u})).map h ≫ pathEndpointPair B') := by
          rw [pathEndpointPair_naturality]
        _ = (pullback.snd (Limits.prod.map f g) (pathEndpointPair B) ≫
              (ihom (Δ[1] : SSet.{u})).map h) ≫ pathEndpointPair B' :=
          (Category.assoc _ _ _).symm)

@[reassoc (attr := simp)]
theorem pathHomotopyPullbackMap_left
    {X Y B X' Y' B' : SSet.{u}}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : X' ⟶ B'} {g' : Y' ⟶ B'}
    (l : X ⟶ X') (r : Y ⟶ Y') (h : B ⟶ B')
    (hf : f ≫ h = l ≫ f') (hg : g ≫ h = r ≫ g') :
    pathHomotopyPullbackMap l r h hf hg ≫
        pathHomotopyPullbackLeft f' g' =
      pathHomotopyPullbackLeft f g ≫ l := by
  rw [pathHomotopyPullbackMap, pathHomotopyPullbackLeft,
    ← Category.assoc, pullback.lift_fst]
  simp

@[reassoc (attr := simp)]
theorem pathHomotopyPullbackMap_right
    {X Y B X' Y' B' : SSet.{u}}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : X' ⟶ B'} {g' : Y' ⟶ B'}
    (l : X ⟶ X') (r : Y ⟶ Y') (h : B ⟶ B')
    (hf : f ≫ h = l ≫ f') (hg : g ≫ h = r ≫ g') :
    pathHomotopyPullbackMap l r h hf hg ≫
        pathHomotopyPullbackRight f' g' =
      pathHomotopyPullbackRight f g ≫ r := by
  rw [pathHomotopyPullbackMap, pathHomotopyPullbackRight,
    ← Category.assoc, pullback.lift_fst]
  simp

@[reassoc (attr := simp)]
theorem pathHomotopyPullbackMap_path
    {X Y B X' Y' B' : SSet.{u}}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : X' ⟶ B'} {g' : Y' ⟶ B'}
    (l : X ⟶ X') (r : Y ⟶ Y') (h : B ⟶ B')
    (hf : f ≫ h = l ≫ f') (hg : g ≫ h = r ≫ g') :
    pathHomotopyPullbackMap l r h hf hg ≫
        pathHomotopyPullbackPath f' g' =
      pathHomotopyPullbackPath f g ≫
        (ihom (Δ[1] : SSet.{u})).map h := by
  rw [pathHomotopyPullbackMap, pathHomotopyPullbackPath,
    pullback.lift_snd]

theorem pathHomotopyPullbackMap_id
    {X Y B : SSet.{u}} (f : X ⟶ B) (g : Y ⟶ B) :
    pathHomotopyPullbackMap (𝟙 X) (𝟙 Y) (𝟙 B)
        (by simp) (by simp) =
      𝟙 (pathHomotopyPullback f g) := by
  apply pathHomotopyPullback_hom_ext
  · simp
  · simp
  · rw [pathHomotopyPullbackMap_path]
    simp

theorem pathHomotopyPullbackMap_comp
    {X Y B X' Y' B' X'' Y'' B'' : SSet.{u}}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : X' ⟶ B'} {g' : Y' ⟶ B'}
    {f'' : X'' ⟶ B''} {g'' : Y'' ⟶ B''}
    (l : X ⟶ X') (r : Y ⟶ Y') (h : B ⟶ B')
    (l' : X' ⟶ X'') (r' : Y' ⟶ Y'') (h' : B' ⟶ B'')
    (hf : f ≫ h = l ≫ f') (hg : g ≫ h = r ≫ g')
    (hf' : f' ≫ h' = l' ≫ f'') (hg' : g' ≫ h' = r' ≫ g'') :
    pathHomotopyPullbackMap l r h hf hg ≫
        pathHomotopyPullbackMap l' r' h' hf' hg' =
      pathHomotopyPullbackMap (l ≫ l') (r ≫ r') (h ≫ h')
        (by
          calc
            f ≫ (h ≫ h') = (f ≫ h) ≫ h' := (Category.assoc _ _ _).symm
            _ = (l ≫ f') ≫ h' := by rw [hf]
            _ = l ≫ (f' ≫ h') := Category.assoc _ _ _
            _ = l ≫ (l' ≫ f'') := by rw [hf']
            _ = (l ≫ l') ≫ f'' := (Category.assoc _ _ _).symm)
        (by
          calc
            g ≫ (h ≫ h') = (g ≫ h) ≫ h' := (Category.assoc _ _ _).symm
            _ = (r ≫ g') ≫ h' := by rw [hg]
            _ = r ≫ (g' ≫ h') := Category.assoc _ _ _
            _ = r ≫ (r' ≫ g'') := by rw [hg']
            _ = (r ≫ r') ≫ g'' := (Category.assoc _ _ _).symm) := by
  apply pathHomotopyPullback_hom_ext
  · simp
  · simp
  · rw [Category.assoc, pathHomotopyPullbackMap_path,
      pathHomotopyPullbackMap_path_assoc,
      pathHomotopyPullbackMap_path]
    rw [← Functor.map_comp]

/-- Based path-homotopy fiber over a selected vertex. -/
noncomputable abbrev pathHomotopyFiber
    {X B : SSet.{u}} (f : X ⟶ B) (b : B _⦋0⦌) : SSet.{u} :=
  pathHomotopyPullback f (SSet.const (X := (Δ[0] : SSet.{u})) b)

noncomputable abbrev pathHomotopyFiberToTotal
    {X B : SSet.{u}} (f : X ⟶ B) (b : B _⦋0⦌) :
    pathHomotopyFiber f b ⟶ X :=
  pathHomotopyPullbackLeft f (SSet.const b)

noncomputable abbrev pathHomotopyFiberPath
    {X B : SSet.{u}} (f : X ⟶ B) (b : B _⦋0⦌) :
    pathHomotopyFiber f b ⟶ SSet.pathSpace B :=
  pathHomotopyPullbackPath f (SSet.const b)

@[reassoc]
theorem pathHomotopyFiberPath_evalZero
    {X B : SSet.{u}} (f : X ⟶ B) (b : B _⦋0⦌) :
    pathHomotopyFiberPath f b ≫ SSet.eval₀ =
      pathHomotopyFiberToTotal f b ≫ f :=
  pathHomotopyPullbackPath_evalZero f (SSet.const b)

@[reassoc]
theorem pathHomotopyFiberPath_evalOne
    {X B : SSet.{u}} (f : X ⟶ B) (b : B _⦋0⦌) :
    pathHomotopyFiberPath f b ≫ SSet.eval₁ =
      SSet.const (X := pathHomotopyFiber f b) b := by
  simpa using pathHomotopyPullbackPath_evalOne f
    (SSet.const (X := (Δ[0] : SSet.{u})) b)

/-- Maps to a based path fiber are determined by total and path projection. -/
theorem pathHomotopyFiber_hom_ext
    {X B Z : SSet.{u}} {f : X ⟶ B} {b : B _⦋0⦌}
    {a c : Z ⟶ pathHomotopyFiber f b}
    (htotal : a ≫ pathHomotopyFiberToTotal f b =
      c ≫ pathHomotopyFiberToTotal f b)
    (hpath : a ≫ pathHomotopyFiberPath f b =
      c ≫ pathHomotopyFiberPath f b) : a = c := by
  apply pathHomotopyPullback_hom_ext htotal
  · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  · exact hpath

/-- Fiber map induced by a compatible square and selected-vertex equation. -/
noncomputable def pathHomotopyFiberMap
    {X B X' B' : SSet.{u}} {f : X ⟶ B} {f' : X' ⟶ B'}
    (l : X ⟶ X') (h : B ⟶ B') (hf : f ≫ h = l ≫ f')
    {b : B _⦋0⦌} {b' : B' _⦋0⦌} (hb : h.app _ b = b') :
    pathHomotopyFiber f b ⟶ pathHomotopyFiber f' b' :=
  pathHomotopyPullbackMap l (𝟙 (Δ[0] : SSet.{u})) h hf
    (by simp [SSet.const_comp, hb])

@[reassoc (attr := simp)]
theorem pathHomotopyFiberMap_toTotal
    {X B X' B' : SSet.{u}} {f : X ⟶ B} {f' : X' ⟶ B'}
    (l : X ⟶ X') (h : B ⟶ B') (hf : f ≫ h = l ≫ f')
    {b : B _⦋0⦌} {b' : B' _⦋0⦌} (hb : h.app _ b = b') :
    pathHomotopyFiberMap l h hf hb ≫ pathHomotopyFiberToTotal f' b' =
      pathHomotopyFiberToTotal f b ≫ l := by
  apply pathHomotopyPullbackMap_left

@[reassoc (attr := simp)]
theorem pathHomotopyFiberMap_path
    {X B X' B' : SSet.{u}} {f : X ⟶ B} {f' : X' ⟶ B'}
    (l : X ⟶ X') (h : B ⟶ B') (hf : f ≫ h = l ≫ f')
    {b : B _⦋0⦌} {b' : B' _⦋0⦌} (hb : h.app _ b = b') :
    pathHomotopyFiberMap l h hf hb ≫ pathHomotopyFiberPath f' b' =
      pathHomotopyFiberPath f b ≫
        (ihom (Δ[1] : SSet.{u})).map h := by
  apply pathHomotopyPullbackMap_path

theorem pathHomotopyFiberMap_id
    {X B : SSet.{u}} (f : X ⟶ B) (b : B _⦋0⦌) :
    pathHomotopyFiberMap (𝟙 X) (𝟙 B) (by simp) (by simp) =
      𝟙 (pathHomotopyFiber f b) := by
  apply pathHomotopyPullback_hom_ext
  · simp
  · simp [pathHomotopyFiberMap]
  · simp

theorem pathHomotopyFiberMap_comp
    {X B X' B' X'' B'' : SSet.{u}}
    {f : X ⟶ B} {f' : X' ⟶ B'} {f'' : X'' ⟶ B''}
    (l : X ⟶ X') (h : B ⟶ B') (l' : X' ⟶ X'') (h' : B' ⟶ B'')
    (hf : f ≫ h = l ≫ f') (hf' : f' ≫ h' = l' ≫ f'')
    {b : B _⦋0⦌} {b' : B' _⦋0⦌} {b'' : B'' _⦋0⦌}
    (hb : h.app _ b = b') (hb' : h'.app _ b' = b'') :
    pathHomotopyFiberMap l h hf hb ≫
        pathHomotopyFiberMap l' h' hf' hb' =
      pathHomotopyFiberMap (l ≫ l') (h ≫ h')
        (by
          calc
            f ≫ (h ≫ h') = (f ≫ h) ≫ h' := (Category.assoc _ _ _).symm
            _ = (l ≫ f') ≫ h' := by rw [hf]
            _ = l ≫ (f' ≫ h') := Category.assoc _ _ _
            _ = l ≫ (l' ≫ f'') := by rw [hf']
            _ = (l ≫ l') ≫ f'' := (Category.assoc _ _ _).symm)
        (by
          change h'.app _ (h.app _ b) = b''
          rw [hb, hb']) := by
  apply pathHomotopyPullback_hom_ext
  · simp
  · simp [pathHomotopyFiberMap]
  · simp [← Functor.map_comp]

/-- Canonical map from the strict fiber to the path homotopy fiber. -/
noncomputable def strictFiberToPathHomotopyFiber
    {X B : SSet.{u}} (f : X ⟶ B) (b : B _⦋0⦌) :
    (SSet.Subcomplex.fiber f b : SSet.{u}) ⟶ pathHomotopyFiber f b :=
  pullback.lift
    (Limits.prod.lift (SSet.Subcomplex.fiber f b).ι
      (SSet.stdSimplex.isTerminalObj₀.from _))
    (SSet.const b ≫ SSet.constPath B)
    (by
      apply Limits.prod.hom_ext
      · simp only [Category.assoc, Limits.prod.map_fst,
          pathEndpointPair_fst]
        rw [← Category.assoc, Limits.prod.lift_fst,
          SSet.eval₀_constPath]
        simp
      · simp only [Category.assoc, Limits.prod.map_snd,
          pathEndpointPair_snd]
        rw [← Category.assoc, Limits.prod.lift_snd,
          SSet.eval₁_constPath]
        simp)

@[reassoc (attr := simp)]
theorem strictFiberToPathHomotopyFiber_toTotal
    {X B : SSet.{u}} (f : X ⟶ B) (b : B _⦋0⦌) :
    strictFiberToPathHomotopyFiber f b ≫ pathHomotopyFiberToTotal f b =
      (SSet.Subcomplex.fiber f b).ι := by
  rw [strictFiberToPathHomotopyFiber, pathHomotopyFiberToTotal,
    pathHomotopyPullbackLeft, ← Category.assoc, pullback.lift_fst]
  simp

@[reassoc (attr := simp)]
theorem strictFiberToPathHomotopyFiber_path
    {X B : SSet.{u}} (f : X ⟶ B) (b : B _⦋0⦌) :
    strictFiberToPathHomotopyFiber f b ≫ pathHomotopyFiberPath f b =
      SSet.const b ≫ SSet.constPath B := by
  rw [strictFiberToPathHomotopyFiber, pathHomotopyFiberPath,
    pathHomotopyPullbackPath, pullback.lift_snd]

end SSet

end
