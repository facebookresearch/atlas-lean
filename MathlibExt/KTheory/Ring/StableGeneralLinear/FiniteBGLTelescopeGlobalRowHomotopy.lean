/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteBGLTelescopeEndpointBoundary
public import MathlibExt.Topology.Category.TopCat.ColimitIntervalFamily

/-!
# The whole original telescope-to-stable-row homotopy

The actual endpoint-fixed corrections are compatible on every original bounded
inclusion. Their whole interval families therefore descend through the actual
ordinary bounded cofan. Both endpoint maps and the entire original rank-zero
root trace are retained.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology
open scoped ContinuousMap Simplicial

universe u

namespace AlgebraicKTheory.StableGL

variable (R : Type u) [Ring R]

/-- The internally constructed corrected families agree on every original
bounded inclusion and every original interval time. -/
public theorem finiteBGLTelescopeBoundedOriginalStableRowCorrection_le_compatible
    {n m : ℕ} (h : n ≤ m) (t : unitInterval)
    (x : SSet.toTop.obj (nerve (FiniteBGLTelescopeBoundedCategory R n))) :
    (finiteBGLTelescopeBoundedOriginalStableRowCorrection R m).corrected.toContinuousMap
        (t, SSet.toTop.map ((finiteBGLTelescopeBoundedNerveDiagram R).map (homOfLE h)) x) =
      (finiteBGLTelescopeBoundedOriginalStableRowCorrection R n).corrected.toContinuousMap
        (t, x) := by
  let D : ℕ ⥤ TopCat.{u} := finiteBGLTelescopeBoundedNerveDiagram R ⋙ SSet.toTop
  induction m, h using Nat.le_induction with
  | base =>
    have hq : (homOfLE (Nat.le_refl n) : n ⟶ n) = 𝟙 n := homOfLE_refl _
    have hNerve : (finiteBGLTelescopeBoundedNerveDiagram R).map
        (homOfLE (Nat.le_refl n)) =
      𝟙 ((finiteBGLTelescopeBoundedNerveDiagram R).obj n) :=
      ((finiteBGLTelescopeBoundedNerveDiagram R).congr_map hq).trans
        ((finiteBGLTelescopeBoundedNerveDiagram R).map_id n)
    have hTop : SSet.toTop.map ((finiteBGLTelescopeBoundedNerveDiagram R).map
        (homOfLE (Nat.le_refl n))) =
      𝟙 (SSet.toTop.obj ((finiteBGLTelescopeBoundedNerveDiagram R).obj n)) :=
      (SSet.toTop.congr_map hNerve).trans
        (SSet.toTop.map_id ((finiteBGLTelescopeBoundedNerveDiagram R).obj n))
    have hId : SSet.toTop.map ((finiteBGLTelescopeBoundedNerveDiagram R).map
        (homOfLE (Nat.le_refl n))) x = x :=
      (ConcreteCategory.congr_hom hTop x).trans
        (TopCat.id_app (SSet.toTop.obj ((finiteBGLTelescopeBoundedNerveDiagram R).obj n)) x)
    exact congrArg
      (fun z : SSet.toTop.obj (nerve (FiniteBGLTelescopeBoundedCategory R n)) =>
        (finiteBGLTelescopeBoundedOriginalStableRowCorrection R n).corrected.toContinuousMap
          (t, z)) hId
  | succ m hnm ih =>
    have hComp : D.map (homOfLE (hnm.trans (Nat.le_succ m))) =
        D.map (homOfLE hnm) ≫ D.map (homOfLE (Nat.le_succ m)) := by
      simpa only [homOfLE_comp] using
        D.map_comp (homOfLE hnm) (homOfLE (Nat.le_succ m))
    have hPoint : D.map (homOfLE (hnm.trans (Nat.le_succ m))) x =
        D.map (homOfLE (Nat.le_succ m)) (D.map (homOfLE hnm) x) := by
      exact (ConcreteCategory.congr_hom hComp x).trans
        (TopCat.comp_app (D.map (homOfLE hnm))
          (D.map (homOfLE (Nat.le_succ m))) x)
    change
      (finiteBGLTelescopeBoundedOriginalStableRowCorrection R (m + 1)).corrected.toContinuousMap
          (t, D.map (homOfLE (hnm.trans (Nat.le_succ m))) x) = _
    rw [hPoint]
    exact
      (finiteBGLTelescopeBoundedOriginalStableRowCorrection_succ_compatible R m t
        (D.map (homOfLE hnm) x)).trans ih

/-- The same whole corrected families agree along every actual morphism of
the original natural-number diagram. -/
public theorem finiteBGLTelescopeBoundedOriginalStableRowCorrection_map_compatible
    {n m : ℕ} (q : n ⟶ m) (t : unitInterval)
    (x : SSet.toTop.obj (nerve (FiniteBGLTelescopeBoundedCategory R n))) :
    (finiteBGLTelescopeBoundedOriginalStableRowCorrection R m).corrected.toContinuousMap
        (t, SSet.toTop.map ((finiteBGLTelescopeBoundedNerveDiagram R).map q) x) =
      (finiteBGLTelescopeBoundedOriginalStableRowCorrection R n).corrected.toContinuousMap
        (t, x) := by
  have hq : (homOfLE (leOfHom q) : n ⟶ m) = q := Subsingleton.elim _ _
  have hTop : SSet.toTop.map ((finiteBGLTelescopeBoundedNerveDiagram R).map
      (homOfLE (leOfHom q))) =
    SSet.toTop.map ((finiteBGLTelescopeBoundedNerveDiagram R).map q) :=
    SSet.toTop.congr_map ((finiteBGLTelescopeBoundedNerveDiagram R).congr_map hq)
  have hArg := congrArg
    (fun z : SSet.toTop.obj (nerve (FiniteBGLTelescopeBoundedCategory R m)) =>
      (finiteBGLTelescopeBoundedOriginalStableRowCorrection R m).corrected.toContinuousMap
        (t, z)) (ConcreteCategory.congr_hom hTop x).symm
  exact hArg.trans
    (finiteBGLTelescopeBoundedOriginalStableRowCorrection_le_compatible R (leOfHom q) t x)

/-- The SAME internally chosen corrected families, with one shared typed input
for the original cofan descent and its factorization proof. -/
private def originalGlobalCorrectedFamilies :
    (n : ℕ) → C(unitInterval ×
      (finiteBGLTelescopeBoundedNerveDiagram R ⋙ SSet.toTop).obj n,
      SSet.toTop.obj
        (nerve (SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R)))) :=
  fun n => (finiteBGLTelescopeBoundedOriginalStableRowCorrection R n).corrected.toContinuousMap

/-- A whole computed value of the SAME local family is available without
expanding the opaque dependent correction during higher-order unification. -/
private theorem originalGlobalCorrectedFamilies_eq (n : ℕ) :
    originalGlobalCorrectedFamilies R n =
      (finiteBGLTelescopeBoundedOriginalStableRowCorrection R n).corrected.toContinuousMap := by
  rfl

/-- The actual internal all-arrow equation supplies the shared descent proof. -/
private theorem originalGlobalCorrectedFamiliesCompatible
    {n m : ℕ} (q : n ⟶ m) (t : unitInterval)
    (x : (finiteBGLTelescopeBoundedNerveDiagram R ⋙ SSet.toTop).obj n) :
    originalGlobalCorrectedFamilies R m
        (t, (finiteBGLTelescopeBoundedNerveDiagram R ⋙ SSet.toTop).map q x) =
      originalGlobalCorrectedFamilies R n (t, x) := by
  have hMap : (finiteBGLTelescopeBoundedNerveDiagram R ⋙ SSet.toTop).map q =
      SSet.toTop.map ((finiteBGLTelescopeBoundedNerveDiagram R).map q) := by
    rfl
  have hArg := congrArg
    (fun z : (finiteBGLTelescopeBoundedNerveDiagram R ⋙ SSet.toTop).obj m =>
      originalGlobalCorrectedFamilies R m (t, z))
    (ConcreteCategory.congr_hom hMap x)
  have hLeft := congrArg
    (fun k : C(unitInterval ×
      (finiteBGLTelescopeBoundedNerveDiagram R ⋙ SSet.toTop).obj m,
      SSet.toTop.obj
        (nerve (SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R)))) =>
        k (t, SSet.toTop.map ((finiteBGLTelescopeBoundedNerveDiagram R).map q) x))
    (originalGlobalCorrectedFamilies_eq R m)
  have hRight := congrArg
    (fun k : C(unitInterval ×
      (finiteBGLTelescopeBoundedNerveDiagram R ⋙ SSet.toTop).obj n,
      SSet.toTop.obj
        (nerve (SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R)))) =>
        k (t, x))
    (originalGlobalCorrectedFamilies_eq R n)
  exact hArg.trans (hLeft.trans
    ((finiteBGLTelescopeBoundedOriginalStableRowCorrection_map_compatible R q t x).trans
      hRight.symm))

/-- The actual full descent is typed on its EXACT diagram and cofan carrier. -/
private def originalGlobalCorrectedDesc :
    C(unitInterval × (SSet.toTop.mapCocone
      (finiteBGLTelescopeBoundedNerveCocone R)).pt,
      SSet.toTop.obj
        (nerve (SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R)))) :=
  TopCat.descIntervalFamily (J := ℕ)
    (F := finiteBGLTelescopeBoundedNerveDiagram R ⋙ SSet.toTop)
    (c := SSet.toTop.mapCocone (finiteBGLTelescopeBoundedNerveCocone R))
    (finiteBGLTelescopeBoundedTopCoconeIsColimit R)
    (SSet.toTop.obj
      (nerve (SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R))))
    (originalGlobalCorrectedFamilies R)
    (fun {n m} q t x =>
      originalGlobalCorrectedFamiliesCompatible R (n := n) (m := m) q t x)

/-- Descend the entire original corrected interval families through the actual
ordinary bounded cofan. Every datum is constructed from the original Ring. -/
public def finiteBGLTelescopeGlobalOriginalStableRowFamily :
    C(unitInterval × ordinaryFiniteBGLTelescope R,
      SSet.toTop.obj
        (nerve (SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R)))) :=
  originalGlobalCorrectedDesc R

/-- The global family retains the whole corrected family on every original
cofan point, bound and interval time. -/
public theorem finiteBGLTelescopeGlobalOriginalStableRowFamily_fac
    (n : ℕ) (t : unitInterval)
    (x : SSet.toTop.obj (nerve (FiniteBGLTelescopeBoundedCategory R n))) :
    finiteBGLTelescopeGlobalOriginalStableRowFamily R
        (t, SSet.toTop.map (nerveMap (finiteBGLTelescopeBoundedInclusion R n)) x) =
      (finiteBGLTelescopeBoundedOriginalStableRowCorrection R n).corrected.toContinuousMap
        (t, x) := by
  have h : finiteBGLTelescopeGlobalOriginalStableRowFamily R
      (t, (SSet.toTop.mapCocone (finiteBGLTelescopeBoundedNerveCocone R)).ι.app n x) =
    originalGlobalCorrectedFamilies R n (t, x) := by
    unfold finiteBGLTelescopeGlobalOriginalStableRowFamily originalGlobalCorrectedDesc
    exact TopCat.descIntervalFamily_fac (J := ℕ)
      (F := finiteBGLTelescopeBoundedNerveDiagram R ⋙ SSet.toTop)
      (c := SSet.toTop.mapCocone (finiteBGLTelescopeBoundedNerveCocone R))
      (finiteBGLTelescopeBoundedTopCoconeIsColimit R)
      (SSet.toTop.obj
        (nerve (SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R))))
      (originalGlobalCorrectedFamilies R)
      (fun {i j} q s y =>
        originalGlobalCorrectedFamiliesCompatible R (n := i) (m := j) q s y) n t x
  have hInjection : (SSet.toTop.mapCocone
      (finiteBGLTelescopeBoundedNerveCocone R)).ι.app n =
    SSet.toTop.map (nerveMap (finiteBGLTelescopeBoundedInclusion R n)) := by
    exact (Functor.mapCocone_ι_app SSet.toTop
      (finiteBGLTelescopeBoundedNerveCocone R) n).trans
      (SSet.toTop.congr_map (finiteBGLTelescopeBoundedNerveCocone_ι R n))
  have hArg := congrArg
    (fun z : ordinaryFiniteBGLTelescope R =>
      finiteBGLTelescopeGlobalOriginalStableRowFamily R (t, z))
    (ConcreteCategory.congr_hom hInjection x).symm
  have hFamily : originalGlobalCorrectedFamilies R n =
      (finiteBGLTelescopeBoundedOriginalStableRowCorrection R n).corrected.toContinuousMap :=
    originalGlobalCorrectedFamilies_eq R n
  have hValue := congrArg
    (fun f : C(unitInterval × SSet.toTop.obj
      (nerve (FiniteBGLTelescopeBoundedCategory R n)),
      SSet.toTop.obj
        (nerve (SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R)))) => f (t, x))
    hFamily
  exact hArg.trans (h.trans hValue)

/-- The entire zero-time endpoint is the original telescope-to-row map,
proved by the actual ordinary cofan universal property. -/
public theorem finiteBGLTelescopeGlobalOriginalStableRowFamily_zero :
    (finiteBGLTelescopeGlobalOriginalStableRowFamily R).comp
        ((ContinuousMap.const (ordinaryFiniteBGLTelescope R) (0 : unitInterval)).prodMk
          (ContinuousMap.id (ordinaryFiniteBGLTelescope R))) =
      (finiteBGLTelescopeToRowZeroComponentTop R).hom := by
  let g : ordinaryFiniteBGLTelescope R ⟶
      SSet.toTop.obj
        (nerve (SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R))) :=
    TopCat.ofHom ((finiteBGLTelescopeGlobalOriginalStableRowFamily R).comp
      ((ContinuousMap.const (ordinaryFiniteBGLTelescope R) (0 : unitInterval)).prodMk
        (ContinuousMap.id (ordinaryFiniteBGLTelescope R))))
  have hg : g = finiteBGLTelescopeToRowZeroComponentTop R := by
    apply (finiteBGLTelescopeBoundedTopCoconeIsColimit R).hom_ext
    intro n
    apply TopCat.ext
    intro x
    simp only [Functor.mapCocone_ι_app, TopCat.comp_app]
    change finiteBGLTelescopeGlobalOriginalStableRowFamily R
        (0, SSet.toTop.map (nerveMap (finiteBGLTelescopeBoundedInclusion R n)) x) =
      finiteBGLTelescopeToRowZeroComponentTop R
        (SSet.toTop.map (nerveMap (finiteBGLTelescopeBoundedInclusion R n)) x)
    have hEnd :=
      ((finiteBGLTelescopeBoundedOriginalStableRowCorrection R n).corrected.apply_zero x).trans
        (TopCat.comp_app
          (SSet.toTop.map (nerveMap (finiteBGLTelescopeBoundedInclusion R n)))
          (finiteBGLTelescopeToRowZeroComponentTop R) x)
    exact (finiteBGLTelescopeGlobalOriginalStableRowFamily_fac R n 0 x).trans hEnd
  apply ContinuousMap.ext
  intro x
  change finiteBGLTelescopeGlobalOriginalStableRowFamily R (0, x) =
    finiteBGLTelescopeToRowZeroComponentTop R x
  exact ConcreteCategory.congr_hom hg x

/-- The entire one-time endpoint is the original telescope projection
followed by the same original stable-row comparison. -/
public theorem finiteBGLTelescopeGlobalOriginalStableRowFamily_one :
    (finiteBGLTelescopeGlobalOriginalStableRowFamily R).comp
        ((ContinuousMap.const (ordinaryFiniteBGLTelescope R) (1 : unitInterval)).prodMk
          (ContinuousMap.id (ordinaryFiniteBGLTelescope R))) =
      (ordinaryFiniteBGLTelescopeToBGL R ≫ finiteFreeRowStableZeroComparison R).hom := by
  let g : ordinaryFiniteBGLTelescope R ⟶
      SSet.toTop.obj
        (nerve (SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R))) :=
    TopCat.ofHom ((finiteBGLTelescopeGlobalOriginalStableRowFamily R).comp
      ((ContinuousMap.const (ordinaryFiniteBGLTelescope R) (1 : unitInterval)).prodMk
        (ContinuousMap.id (ordinaryFiniteBGLTelescope R))))
  have hg : g = ordinaryFiniteBGLTelescopeToBGL R ≫ finiteFreeRowStableZeroComparison R := by
    apply (finiteBGLTelescopeBoundedTopCoconeIsColimit R).hom_ext
    intro n
    apply TopCat.ext
    intro x
    simp only [Functor.mapCocone_ι_app, TopCat.comp_app]
    change finiteBGLTelescopeGlobalOriginalStableRowFamily R
        (1, SSet.toTop.map (nerveMap (finiteBGLTelescopeBoundedInclusion R n)) x) =
      finiteFreeRowStableZeroComparison R
        (ordinaryFiniteBGLTelescopeToBGL R
          (SSet.toTop.map (nerveMap (finiteBGLTelescopeBoundedInclusion R n)) x))
    have hEnd :=
      ((finiteBGLTelescopeBoundedOriginalStableRowCorrection R n).corrected.apply_one x).trans
        ((TopCat.comp_app
          (SSet.toTop.map (nerveMap (finiteBGLTelescopeBoundedInclusion R n)))
          (ordinaryFiniteBGLTelescopeToBGL R ≫ finiteFreeRowStableZeroComparison R) x).trans
            (TopCat.comp_app (ordinaryFiniteBGLTelescopeToBGL R)
              (finiteFreeRowStableZeroComparison R)
              (SSet.toTop.map (nerveMap (finiteBGLTelescopeBoundedInclusion R n)) x)))
    exact (finiteBGLTelescopeGlobalOriginalStableRowFamily_fac R n 1 x).trans hEnd
  apply ContinuousMap.ext
  intro x
  change finiteBGLTelescopeGlobalOriginalStableRowFamily R (1, x) =
    finiteFreeRowStableZeroComparison R (ordinaryFiniteBGLTelescopeToBGL R x)
  exact ConcreteCategory.congr_hom hg x

/-- The actual whole homotopy on the original ordinary telescope has BOTH
original endpoint maps and the same descended corrected family. -/
public def finiteBGLTelescopeGlobalOriginalStableRowHomotopy :
    TopCat.Homotopy (finiteBGLTelescopeToRowZeroComponentTop R)
      (ordinaryFiniteBGLTelescopeToBGL R ≫ finiteFreeRowStableZeroComparison R) :=
  { toFun := (finiteBGLTelescopeGlobalOriginalStableRowFamily R).toFun
    continuous_toFun := (finiteBGLTelescopeGlobalOriginalStableRowFamily R).continuous
    map_zero_left := fun x => by
      have h := congrArg
        (fun f : C(ordinaryFiniteBGLTelescope R,
          SSet.toTop.obj
            (nerve (SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R)))) => f x)
        (finiteBGLTelescopeGlobalOriginalStableRowFamily_zero R)
      exact h
    map_one_left := fun x => by
      have h := congrArg
        (fun f : C(ordinaryFiniteBGLTelescope R,
          SSet.toTop.obj
            (nerve (SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R)))) => f x)
        (finiteBGLTelescopeGlobalOriginalStableRowFamily_one R)
      exact h }

/-- The entire homotopy family is the same original cofan descent. -/
public theorem finiteBGLTelescopeGlobalOriginalStableRowHomotopy_toContinuousMap :
    (finiteBGLTelescopeGlobalOriginalStableRowHomotopy R).toContinuousMap =
      finiteBGLTelescopeGlobalOriginalStableRowFamily R := by
  rfl

/-- Restriction to each original bounded piece keeps the whole corrected
homotopy with the actual source and target endpoint transports. -/
public theorem finiteBGLTelescopeGlobalOriginalStableRowHomotopy_restrict (n : ℕ) :
    let i := SSet.toTop.map (nerveMap (finiteBGLTelescopeBoundedInclusion R n))
    ((finiteBGLTelescopeGlobalOriginalStableRowHomotopy R).compContinuousMap i.hom).cast
        (show (finiteBGLTelescopeToRowZeroComponentTop R).hom.comp i.hom =
          (i ≫ finiteBGLTelescopeToRowZeroComponentTop R).hom from by
            apply ContinuousMap.ext
            intro x
            rfl)
        (show (ordinaryFiniteBGLTelescopeToBGL R ≫
            finiteFreeRowStableZeroComparison R).hom.comp i.hom =
          (i ≫ ordinaryFiniteBGLTelescopeToBGL R ≫ finiteFreeRowStableZeroComparison R).hom from by
            apply ContinuousMap.ext
            intro x
            rfl) =
      (finiteBGLTelescopeBoundedOriginalStableRowCorrection R n).corrected := by
  apply ContinuousMap.Homotopy.ext
  intro p
  rcases p with ⟨t, x⟩
  change finiteBGLTelescopeGlobalOriginalStableRowFamily R
      (t, SSet.toTop.map (nerveMap (finiteBGLTelescopeBoundedInclusion R n)) x) =
    (finiteBGLTelescopeBoundedOriginalStableRowCorrection R n).corrected.toContinuousMap
      (t, x)
  exact finiteBGLTelescopeGlobalOriginalStableRowFamily_fac R n t x

/-- The actual original cofan identifies its rank-zero vertex with the
same original telescope basepoint. -/
private theorem originalGlobalRowZeroStageBasepoint :
    SSet.toTop.map (nerveMap (finiteBGLTelescopeBoundedInclusion R 0))
        (SSet.realizedVertex (ComposableArrows.mk₀
          (⟨finiteBGLTelescopeBaseObject R, Nat.zero_le 0⟩ :
            FiniteBGLTelescopeBoundedCategory R 0))) =
      ordinaryFiniteBGLTelescopeBasepoint R := by
  let c : FiniteBGLTelescopeBoundedCategory R 0 :=
    ⟨finiteBGLTelescopeBaseObject R, Nat.zero_le 0⟩
  let v : (nerve (FiniteBGLTelescopeBoundedCategory R 0)) _⦋0⦌ :=
    ComposableArrows.mk₀ c
  have hObj : (finiteBGLTelescopeBoundedInclusion R 0).obj c =
      finiteBGLTelescopeBaseObject R := by
    rfl
  have hNerve : (nerveMap (finiteBGLTelescopeBoundedInclusion R 0)).app
      (Opposite.op (SimplexCategory.mk 0)) v =
        ComposableArrows.mk₀ (finiteBGLTelescopeBaseObject R) :=
    (nerveMap_app_mk₀ (finiteBGLTelescopeBoundedInclusion R 0) c).trans
      (congrArg ComposableArrows.mk₀ hObj)
  have hVertex :=
    (SSet.realizedVertex_naturality
      (nerveMap (finiteBGLTelescopeBoundedInclusion R 0)) v).symm.trans
      (congrArg (SSet.realizedVertex (X := nerve (FiniteBGLTelescopeCategory R))) hNerve)
  exact hVertex

/-- EVERY original interval time retains the same original rank-zero row
image vertex; the initial family is the unchanged original H0. -/
public theorem finiteBGLTelescopeGlobalOriginalStableRowHomotopy_zero_root
    (t : unitInterval) :
    (finiteBGLTelescopeGlobalOriginalStableRowHomotopy R).toContinuousMap
        (t, ordinaryFiniteBGLTelescopeBasepoint R) =
      SSet.realizedVertex
        (X := nerve (SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R)))
        (ComposableArrows.mk₀ ((finiteFreeRowZeroComponentFunctor R 0).obj
          (SingleObj.star (Matrix.GeneralLinearGroup (Fin 0) R)ᵐᵒᵖ))) := by
  let c : FiniteBGLTelescopeBoundedCategory R 0 :=
    ⟨finiteBGLTelescopeBaseObject R, Nat.zero_le 0⟩
  let x : SSet.toTop.obj (nerve (FiniteBGLTelescopeBoundedCategory R 0)) :=
    SSet.realizedVertex (X := (nerve (FiniteBGLTelescopeBoundedCategory R 0) : SSet.{u}))
      (ComposableArrows.mk₀ c)
  calc
    (finiteBGLTelescopeGlobalOriginalStableRowHomotopy R).toContinuousMap
        (t, ordinaryFiniteBGLTelescopeBasepoint R) =
      finiteBGLTelescopeGlobalOriginalStableRowFamily R
        (t, SSet.toTop.map (nerveMap (finiteBGLTelescopeBoundedInclusion R 0)) x) := by
          rw [finiteBGLTelescopeGlobalOriginalStableRowHomotopy_toContinuousMap,
            originalGlobalRowZeroStageBasepoint]
    _ = (finiteBGLTelescopeBoundedOriginalStableRowCorrection R 0).corrected.toContinuousMap
        (t, x) := finiteBGLTelescopeGlobalOriginalStableRowFamily_fac R 0 t x
    _ = (finiteBGLTelescopeBoundedOriginalStableRowHomotopy R 0).toContinuousMap (t, x) := by
      rw [finiteBGLTelescopeBoundedOriginalStableRowCorrection_zero_corrected]
    _ = _ := finiteBGLTelescopeBoundedOriginalStableRowHomotopy_zero_root R t

/-- The same entire original global family is point-relative at the
original telescope basepoint, using its actual stationary root trace. -/
public def finiteBGLTelescopeGlobalOriginalStableRowPointRelative :
    ContinuousMap.HomotopyRel (finiteBGLTelescopeToRowZeroComponentTop R).hom
      (ordinaryFiniteBGLTelescopeToBGL R ≫ finiteFreeRowStableZeroComparison R).hom
      {ordinaryFiniteBGLTelescopeBasepoint R} :=
  { toContinuousMap := (finiteBGLTelescopeGlobalOriginalStableRowHomotopy R).toContinuousMap
    map_zero_left := (finiteBGLTelescopeGlobalOriginalStableRowHomotopy R).map_zero_left
    map_one_left := (finiteBGLTelescopeGlobalOriginalStableRowHomotopy R).map_one_left
    prop' := by
      intro t x hx
      have hPoint : x = ordinaryFiniteBGLTelescopeBasepoint R := Set.mem_singleton_iff.mp hx
      subst x
      exact (finiteBGLTelescopeGlobalOriginalStableRowHomotopy_zero_root R t).trans
        ((finiteBGLTelescopeGlobalOriginalStableRowHomotopy_zero_root R 0).symm.trans
          ((finiteBGLTelescopeGlobalOriginalStableRowHomotopy R).apply_zero
            (ordinaryFiniteBGLTelescopeBasepoint R))) }

/-- The point-relative family keeps the same entire original cofan descent. -/
public theorem finiteBGLTelescopeGlobalOriginalStableRowPointRelative_toContinuousMap :
    (finiteBGLTelescopeGlobalOriginalStableRowPointRelative R).toContinuousMap =
      finiteBGLTelescopeGlobalOriginalStableRowFamily R := by
  rfl

end AlgebraicKTheory.StableGL
