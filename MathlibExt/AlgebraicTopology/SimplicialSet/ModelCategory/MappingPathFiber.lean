/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.PathHomotopyFiber
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanHomotopyPullback

/-!
# The actual ending-path fiber and strict mapping-path fiber

The generic universal-property construction is moved unchanged from the
homotopy-fiber criterion owner. Both maps retain the original source and
entire path. No fibrancy, comparison, weak-equivalence or model witness is
an input. The public component equations make the computed carrier usable
without unfolding an opaque isomorphism.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped Simplicial

universe u

public section

namespace SSet

/-- A structural pullback lift into the existing full ending-path carrier.
This is private universal-property glue; final callers compute both maps. -/
private noncomputable def actualPathFiberLift {Z X B : SSet.{u}}
    (f : X ⟶ B) (b : B _⦋0⦌) (x : Z ⟶ X) (γ : Z ⟶ SSet.pathSpace B)
    (hzero : γ ≫ SSet.eval₀ = x ≫ f)
    (hone : γ ≫ SSet.eval₁ = SSet.const (X := Z) b) :
    Z ⟶ SSet.pathHomotopyFiber f b :=
  pullback.lift (Limits.prod.lift x (SSet.stdSimplex.isTerminalObj₀.from Z)) γ (by
    change Limits.prod.lift x (SSet.stdSimplex.isTerminalObj₀.from Z) ≫
        Limits.prod.map f (SSet.const (X := (Δ[0] : SSet.{u})) b) =
      γ ≫ SSet.evalPair ≫ (CartesianMonoidalCategory.tensorLeftIsoProd B).hom.app B
    apply Limits.prod.hom_ext
    · simpa only [Category.assoc, Limits.prod.map_fst, Limits.prod.lift_fst_assoc,
        SSet.tensorLeftIsoProd_hom_fst, SSet.evalPair_fst] using hzero.symm
    · simpa only [Category.assoc, Limits.prod.map_snd, Limits.prod.lift_snd_assoc,
        SSet.tensorLeftIsoProd_hom_snd, SSet.evalPair_snd, SSet.comp_const] using hone.symm)

private theorem actualPathFiberLift_toTotal {Z X B : SSet.{u}}
    (f : X ⟶ B) (b : B _⦋0⦌) (x : Z ⟶ X) (γ : Z ⟶ SSet.pathSpace B)
    (hzero : γ ≫ SSet.eval₀ = x ≫ f)
    (hone : γ ≫ SSet.eval₁ = SSet.const (X := Z) b) :
    actualPathFiberLift f b x γ hzero hone ≫ SSet.pathHomotopyFiberToTotal f b = x := by
  dsimp only [actualPathFiberLift, SSet.pathHomotopyFiberToTotal, SSet.pathHomotopyPullbackLeft]
  rw [← Category.assoc, pullback.lift_fst, Limits.prod.lift_fst]

private theorem actualPathFiberLift_path {Z X B : SSet.{u}}
    (f : X ⟶ B) (b : B _⦋0⦌) (x : Z ⟶ X) (γ : Z ⟶ SSet.pathSpace B)
    (hzero : γ ≫ SSet.eval₀ = x ≫ f)
    (hone : γ ≫ SSet.eval₁ = SSet.const (X := Z) b) :
    actualPathFiberLift f b x γ hzero hone ≫ SSet.pathHomotopyFiberPath f b = γ := by
  dsimp only [actualPathFiberLift, SSet.pathHomotopyFiberPath, SSet.pathHomotopyPullbackPath]
  exact pullback.lift_snd _ _ _

/-- The ending-path fiber's two original coordinates define its map to the
fixed mapping path total space. -/
private noncomputable def pathFiberToMappingPath {X B : SSet.{u}}
    (f : X ⟶ B) (b : B _⦋0⦌) :
    SSet.pathHomotopyFiber f b ⟶ SSet.mappingPathSpace f :=
  pullback.lift (SSet.pathHomotopyFiberToTotal f b)
    (SSet.pathHomotopyFiberPath f b) (SSet.pathHomotopyFiberPath_evalZero f b).symm

private theorem pathFiberToMappingPath_retract {X B : SSet.{u}}
    (f : X ⟶ B) (b : B _⦋0⦌) :
    pathFiberToMappingPath f b ≫ SSet.mappingPathRetract f =
      SSet.pathHomotopyFiberToTotal f b := by
  dsimp only [pathFiberToMappingPath, SSet.mappingPathRetract]
  exact pullback.lift_fst _ _ _

private theorem pathFiberToMappingPath_eval {X B : SSet.{u}}
    (f : X ⟶ B) (b : B _⦋0⦌) :
    pathFiberToMappingPath f b ≫ SSet.mappingPathEval f =
      SSet.pathHomotopyFiberPath f b := by
  dsimp only [pathFiberToMappingPath, SSet.mappingPathEval]
  exact pullback.lift_snd _ _ _

private theorem pathFiberToMappingPath_target {X B : SSet.{u}}
    (f : X ⟶ B) (b : B _⦋0⦌) :
    pathFiberToMappingPath f b ≫ SSet.mappingPathTarget f =
      SSet.const (X := SSet.pathHomotopyFiber f b) b := by
  dsimp only [SSet.mappingPathTarget]
  rw [← Category.assoc, pathFiberToMappingPath_eval]
  exact SSet.pathHomotopyFiberPath_evalOne f b

/-- The map lands in the literal strict fiber of the derived fibration. -/
private noncomputable def pathFiberToStrictMappingPath {X B : SSet.{u}}
    (f : X ⟶ B) (b : B _⦋0⦌) :
    SSet.pathHomotopyFiber f b ⟶
      (SSet.Subcomplex.fiber (SSet.mappingPathTarget f) b : SSet.{u}) :=
  SSet.Subcomplex.lift (pathFiberToMappingPath f b)
    ((SSet.Subcomplex.range_le_fiber_iff (SSet.mappingPathTarget f) b _).mpr
      (pathFiberToMappingPath_target f b))

private theorem pathFiberToStrictMappingPath_ι {X B : SSet.{u}}
    (f : X ⟶ B) (b : B _⦋0⦌) :
    pathFiberToStrictMappingPath f b ≫ (SSet.Subcomplex.fiber (SSet.mappingPathTarget f) b).ι =
      pathFiberToMappingPath f b :=
  SSet.Subcomplex.lift_ι _ _

/-- Restricting both actual mapping-path coordinates constructs the reverse
map to the original ending-path carrier. -/
private noncomputable def strictMappingPathToPathFiber {X B : SSet.{u}}
    (f : X ⟶ B) (b : B _⦋0⦌) :
    (SSet.Subcomplex.fiber (SSet.mappingPathTarget f) b : SSet.{u}) ⟶
      SSet.pathHomotopyFiber f b := by
  let F := SSet.Subcomplex.fiber (SSet.mappingPathTarget f) b
  let x := F.ι ≫ SSet.mappingPathRetract f
  let γ := F.ι ≫ SSet.mappingPathEval f
  have hzero : γ ≫ SSet.eval₀ = x ≫ f := by
    have h : SSet.mappingPathEval f ≫ SSet.eval₀ = SSet.mappingPathRetract f ≫ f :=
      pullback.condition.symm
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => F.ι ≫ k) h).trans (Category.assoc _ _ _).symm)
  have hone : γ ≫ SSet.eval₁ = SSet.const (X := (F : SSet.{u})) b :=
    (Category.assoc _ _ _).trans (SSet.Subcomplex.fiber_ι_comp (SSet.mappingPathTarget f) b)
  exact actualPathFiberLift f b x γ hzero hone

private theorem strictMappingPathToPathFiber_total {X B : SSet.{u}}
    (f : X ⟶ B) (b : B _⦋0⦌) :
    strictMappingPathToPathFiber f b ≫ SSet.pathHomotopyFiberToTotal f b =
      (SSet.Subcomplex.fiber (SSet.mappingPathTarget f) b).ι ≫ SSet.mappingPathRetract f := by
  unfold strictMappingPathToPathFiber
  exact actualPathFiberLift_toTotal _ _ _ _ _ _

private theorem strictMappingPathToPathFiber_path {X B : SSet.{u}}
    (f : X ⟶ B) (b : B _⦋0⦌) :
    strictMappingPathToPathFiber f b ≫ SSet.pathHomotopyFiberPath f b =
      (SSet.Subcomplex.fiber (SSet.mappingPathTarget f) b).ι ≫ SSet.mappingPathEval f := by
  unfold strictMappingPathToPathFiber
  exact actualPathFiberLift_path _ _ _ _ _ _

/-- Both pointwise-coordinate computations certify the original carrier roundtrip. -/
private theorem pathFiber_mappingPath_roundtrip {X B : SSet.{u}}
    (f : X ⟶ B) (b : B _⦋0⦌) :
    pathFiberToStrictMappingPath f b ≫ strictMappingPathToPathFiber f b =
      𝟙 (SSet.pathHomotopyFiber f b) := by
  apply SSet.pathHomotopyFiber_hom_ext
  · calc
      (pathFiberToStrictMappingPath f b ≫ strictMappingPathToPathFiber f b) ≫
          SSet.pathHomotopyFiberToTotal f b =
        pathFiberToStrictMappingPath f b ≫
          ((SSet.Subcomplex.fiber (SSet.mappingPathTarget f) b).ι ≫ SSet.mappingPathRetract f) := by
            rw [Category.assoc, strictMappingPathToPathFiber_total]
      _ = (pathFiberToStrictMappingPath f b ≫
          (SSet.Subcomplex.fiber (SSet.mappingPathTarget f) b).ι) ≫ SSet.mappingPathRetract f :=
            (Category.assoc _ _ _).symm
      _ = SSet.pathHomotopyFiberToTotal f b := by
            rw [pathFiberToStrictMappingPath_ι, pathFiberToMappingPath_retract]
      _ = 𝟙 _ ≫ SSet.pathHomotopyFiberToTotal f b := (Category.id_comp _).symm
  · calc
      (pathFiberToStrictMappingPath f b ≫ strictMappingPathToPathFiber f b) ≫
          SSet.pathHomotopyFiberPath f b =
        pathFiberToStrictMappingPath f b ≫
          ((SSet.Subcomplex.fiber (SSet.mappingPathTarget f) b).ι ≫ SSet.mappingPathEval f) := by
            rw [Category.assoc, strictMappingPathToPathFiber_path]
      _ = (pathFiberToStrictMappingPath f b ≫
          (SSet.Subcomplex.fiber (SSet.mappingPathTarget f) b).ι) ≫ SSet.mappingPathEval f :=
            (Category.assoc _ _ _).symm
      _ = SSet.pathHomotopyFiberPath f b := by
            rw [pathFiberToStrictMappingPath_ι, pathFiberToMappingPath_eval]
      _ = 𝟙 _ ≫ SSet.pathHomotopyFiberPath f b := (Category.id_comp _).symm

private theorem strictMappingPath_roundtrip {X B : SSet.{u}}
    (f : X ⟶ B) (b : B _⦋0⦌) :
    strictMappingPathToPathFiber f b ≫ pathFiberToStrictMappingPath f b =
      𝟙 (SSet.Subcomplex.fiber (SSet.mappingPathTarget f) b : SSet.{u}) := by
  let F := SSet.Subcomplex.fiber (SSet.mappingPathTarget f) b
  apply (cancel_mono F.ι).mp
  have h : strictMappingPathToPathFiber f b ≫ pathFiberToMappingPath f b = F.ι := by
    apply pullback.hom_ext
    · change (strictMappingPathToPathFiber f b ≫ pathFiberToMappingPath f b) ≫
        SSet.mappingPathRetract f = F.ι ≫ SSet.mappingPathRetract f
      rw [Category.assoc, pathFiberToMappingPath_retract, strictMappingPathToPathFiber_total]
    · change (strictMappingPathToPathFiber f b ≫ pathFiberToMappingPath f b) ≫
        SSet.mappingPathEval f = F.ι ≫ SSet.mappingPathEval f
      rw [Category.assoc, pathFiberToMappingPath_eval, strictMappingPathToPathFiber_path]
  calc
    (strictMappingPathToPathFiber f b ≫ pathFiberToStrictMappingPath f b) ≫ F.ι =
        strictMappingPathToPathFiber f b ≫ pathFiberToMappingPath f b := by
          rw [Category.assoc, pathFiberToStrictMappingPath_ι]
    _ = F.ι := h
    _ = 𝟙 (F : SSet.{u}) ≫ F.ι := (Category.id_comp _).symm

/-- A computed isomorphism ties the original full ending-path fiber to the
literal strict fiber of the fixed derived fibration, with both actual coordinates. -/
noncomputable def pathHomotopyFiberStrictMappingPathIso {X B : SSet.{u}}
    (f : X ⟶ B) (b : B _⦋0⦌) :
    SSet.pathHomotopyFiber f b ≅
      (SSet.Subcomplex.fiber (SSet.mappingPathTarget f) b : SSet.{u}) where
  hom := pathFiberToStrictMappingPath f b
  inv := strictMappingPathToPathFiber f b
  hom_inv_id := pathFiber_mappingPath_roundtrip f b
  inv_hom_id := strictMappingPath_roundtrip f b


private theorem pathHomotopyFiberStrictMappingPathIso_hom_total_computation
    {X B : SSet.{u}} (f : X ⟶ B) (b : B _⦋0⦌) :
    (pathHomotopyFiberStrictMappingPathIso f b).hom ≫
      ((Subcomplex.fiber (mappingPathTarget f) b).ι ≫ mappingPathRetract f) =
        pathHomotopyFiberToTotal f b := by
  change pathFiberToStrictMappingPath f b ≫
    ((Subcomplex.fiber (mappingPathTarget f) b).ι ≫ mappingPathRetract f) = _
  rw [← Category.assoc, pathFiberToStrictMappingPath_ι, pathFiberToMappingPath_retract]

/-- The forward computed isomorphism retains the entire original source projection. -/
theorem pathHomotopyFiberStrictMappingPathIso_hom_total
    {X B : SSet.{u}} (f : X ⟶ B) (b : B _⦋0⦌) :
    (pathHomotopyFiberStrictMappingPathIso f b).hom ≫
      ((Subcomplex.fiber (mappingPathTarget f) b).ι ≫ mappingPathRetract f) =
        pathHomotopyFiberToTotal f b :=
  pathHomotopyFiberStrictMappingPathIso_hom_total_computation f b

private theorem pathHomotopyFiberStrictMappingPathIso_hom_path_computation
    {X B : SSet.{u}} (f : X ⟶ B) (b : B _⦋0⦌) :
    (pathHomotopyFiberStrictMappingPathIso f b).hom ≫
      ((Subcomplex.fiber (mappingPathTarget f) b).ι ≫ mappingPathEval f) =
        pathHomotopyFiberPath f b := by
  change pathFiberToStrictMappingPath f b ≫
    ((Subcomplex.fiber (mappingPathTarget f) b).ι ≫ mappingPathEval f) = _
  rw [← Category.assoc, pathFiberToStrictMappingPath_ι, pathFiberToMappingPath_eval]

/-- The forward computed isomorphism retains the original complete ending path. -/
theorem pathHomotopyFiberStrictMappingPathIso_hom_path
    {X B : SSet.{u}} (f : X ⟶ B) (b : B _⦋0⦌) :
    (pathHomotopyFiberStrictMappingPathIso f b).hom ≫
      ((Subcomplex.fiber (mappingPathTarget f) b).ι ≫ mappingPathEval f) =
        pathHomotopyFiberPath f b :=
  pathHomotopyFiberStrictMappingPathIso_hom_path_computation f b

private theorem pathHomotopyFiberStrictMappingPathIso_inv_total_computation
    {X B : SSet.{u}} (f : X ⟶ B) (b : B _⦋0⦌) :
    (pathHomotopyFiberStrictMappingPathIso f b).inv ≫ pathHomotopyFiberToTotal f b =
      (Subcomplex.fiber (mappingPathTarget f) b).ι ≫ mappingPathRetract f :=
  strictMappingPathToPathFiber_total f b

/-- The inverse returns the literal strict mapping-path source coordinate. -/
theorem pathHomotopyFiberStrictMappingPathIso_inv_total
    {X B : SSet.{u}} (f : X ⟶ B) (b : B _⦋0⦌) :
    (pathHomotopyFiberStrictMappingPathIso f b).inv ≫ pathHomotopyFiberToTotal f b =
      (Subcomplex.fiber (mappingPathTarget f) b).ι ≫ mappingPathRetract f :=
  pathHomotopyFiberStrictMappingPathIso_inv_total_computation f b

private theorem pathHomotopyFiberStrictMappingPathIso_inv_path_computation
    {X B : SSet.{u}} (f : X ⟶ B) (b : B _⦋0⦌) :
    (pathHomotopyFiberStrictMappingPathIso f b).inv ≫ pathHomotopyFiberPath f b =
      (Subcomplex.fiber (mappingPathTarget f) b).ι ≫ mappingPathEval f :=
  strictMappingPathToPathFiber_path f b

/-- The inverse returns the same literal strict mapping-path path coordinate. -/
theorem pathHomotopyFiberStrictMappingPathIso_inv_path
    {X B : SSet.{u}} (f : X ⟶ B) (b : B _⦋0⦌) :
    (pathHomotopyFiberStrictMappingPathIso f b).inv ≫ pathHomotopyFiberPath f b =
      (Subcomplex.fiber (mappingPathTarget f) b).ι ≫ mappingPathEval f :=
  pathHomotopyFiberStrictMappingPathIso_inv_path_computation f b

end SSet
