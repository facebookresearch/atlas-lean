/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.HomotopyPullback
public import MathlibExt.AlgebraicTopology.SingularHomology.UniverseLiftIntegral
public import Mathlib.Topology.Category.TopCat.ULift
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# The actual ending-path homotopy fiber under a carrier lift

The interval, path object, product and pullback comparisons retain the
original source and path coordinates. Integral acyclicity is transported
with the genuine integer-coefficient universe comparison.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology
open scoped ContinuousMap

universe u v w

namespace TopCat.UniverseLift

private def intervalHomeomorph : TopCat.I.{u} ≃ₜ TopCat.I.{max u v} :=
  TopCat.I.homeomorph.{u}.trans TopCat.I.homeomorph.{max u v}.symm

private theorem intervalHomeomorph_zero :
    intervalHomeomorph.{u, v} (0 : TopCat.I.{u}) = (0 : TopCat.I.{max u v}) := by
  apply TopCat.I.homeomorph.{max u v}.injective
  simp only [intervalHomeomorph, Homeomorph.trans_apply, Homeomorph.apply_symm_apply,
    TopCat.I.homeomorph_zero]

private theorem intervalHomeomorph_one :
    intervalHomeomorph.{u, v} (1 : TopCat.I.{u}) = (1 : TopCat.I.{max u v}) := by
  apply TopCat.I.homeomorph.{max u v}.injective
  simp only [intervalHomeomorph, Homeomorph.trans_apply, Homeomorph.apply_symm_apply,
    TopCat.I.homeomorph_one]

private theorem intervalHomeomorph_symm_zero :
    intervalHomeomorph.{u, v}.symm (0 : TopCat.I.{max u v}) = (0 : TopCat.I.{u}) := by
  exact (congrArg intervalHomeomorph.{u, v}.symm
    intervalHomeomorph_zero.{u, v}).symm.trans
      (intervalHomeomorph.{u, v}.symm_apply_apply 0)

private theorem intervalHomeomorph_symm_one :
    intervalHomeomorph.{u, v}.symm (1 : TopCat.I.{max u v}) = (1 : TopCat.I.{u}) := by
  exact (congrArg intervalHomeomorph.{u, v}.symm
    intervalHomeomorph_one.{u, v}).symm.trans
      (intervalHomeomorph.{u, v}.symm_apply_apply 1)

/-- The canonical compact-open path-object comparison, with the original
interval reparametrization and original carrier up/down maps. -/
public def pathObjectIso (B : TopCat.{u}) :
    TopCat.uliftFunctor.{v, u}.obj (TopCat.pathObject B) ≅
      TopCat.pathObject (TopCat.uliftFunctor.{v, u}.obj B) :=
  TopCat.isoOfHomeo
    ((Homeomorph.ulift : ULift.{v} (TopCat.pathObject B) ≃ₜ TopCat.pathObject B).trans
      (intervalHomeomorph.{u, v}.arrowCongr (TopCat.uliftFunctorObjHomeo.{v, u} B)))

/-- The path comparison keeps the whole original path, with the canonical
change of interval coordinates. -/
public theorem pathObjectIso_hom_apply (B : TopCat.{u})
    (γ : TopCat.uliftFunctor.{v, u}.obj (TopCat.pathObject B))
    (t : TopCat.I.{max u v}) :
    (pathObjectIso.{u, v} B).hom γ t =
      ULift.up (γ.down
        (TopCat.I.homeomorph.{u}.symm (TopCat.I.homeomorph.{max u v} t))) := by
  rfl

@[reassoc]
public theorem pathObjectIso_hom_evalZero (B : TopCat.{u}) :
    (pathObjectIso.{u, v} B).hom ≫
        TopCat.pathEvalZero (TopCat.uliftFunctor.{v, u}.obj B) =
      TopCat.uliftFunctor.{v, u}.map (TopCat.pathEvalZero B) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro γ
  change (pathObjectIso.{u, v} B).hom γ 0 = _
  rw [pathObjectIso_hom_apply, TopCat.I.homeomorph_zero]
  rfl

@[reassoc]
public theorem pathObjectIso_hom_evalOne (B : TopCat.{u}) :
    (pathObjectIso.{u, v} B).hom ≫
        TopCat.pathEvalOne (TopCat.uliftFunctor.{v, u}.obj B) =
      TopCat.uliftFunctor.{v, u}.map (TopCat.pathEvalOne B) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro γ
  change (pathObjectIso.{u, v} B).hom γ 1 = _
  rw [pathObjectIso_hom_apply, TopCat.I.homeomorph_one]
  rfl

private theorem pathObjectIso_endpoints (B : TopCat.{u}) :
    TopCat.uliftFunctor.{v, u}.map (TopCat.pathEndpoints B) ≫
        prodComparison TopCat.uliftFunctor.{v, u} B B =
      (pathObjectIso.{u, v} B).hom ≫
        TopCat.pathEndpoints (TopCat.uliftFunctor.{v, u}.obj B) := by
  apply Limits.prod.hom_ext
  · simp only [Category.assoc, prodComparison_fst, ← Functor.map_comp,
      TopCat.pathEndpoints, Limits.prod.lift_fst, Limits.prod.lift_fst_assoc,
      pathObjectIso_hom_evalZero]
  · simp only [Category.assoc, prodComparison_snd, ← Functor.map_comp,
      TopCat.pathEndpoints, Limits.prod.lift_snd, Limits.prod.lift_snd_assoc,
      pathObjectIso_hom_evalOne]

/-- The actual map from the lifted original compact-open homotopy
pullback to the compact-open homotopy pullback of the lifted maps. -/
public def homotopyPullbackMap {X Y B : TopCat.{u}} (f : X ⟶ B) (g : Y ⟶ B) :
    TopCat.uliftFunctor.{v, u}.obj (TopCat.homotopyPullback f g) ⟶
      TopCat.homotopyPullback
        (TopCat.uliftFunctor.{v, u}.map f) (TopCat.uliftFunctor.{v, u}.map g) :=
  pullbackComparison TopCat.uliftFunctor.{v, u}
      (Limits.prod.map f g) (TopCat.pathEndpoints B) ≫
    pullback.map
      (TopCat.uliftFunctor.{v, u}.map (Limits.prod.map f g))
      (TopCat.uliftFunctor.{v, u}.map (TopCat.pathEndpoints B))
      (Limits.prod.map (TopCat.uliftFunctor.{v, u}.map f)
        (TopCat.uliftFunctor.{v, u}.map g))
      (TopCat.pathEndpoints (TopCat.uliftFunctor.{v, u}.obj B))
      (prodComparison TopCat.uliftFunctor.{v, u} X Y)
      (pathObjectIso.{u, v} B).hom
      (prodComparison TopCat.uliftFunctor.{v, u} B B)
      (prodComparison_natural TopCat.uliftFunctor.{v, u} f g)
      (pathObjectIso_endpoints.{u, v} B)

private instance homotopyPullbackMapIsIso {X Y B : TopCat.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) : IsIso (homotopyPullbackMap.{u, v} f g) := by
  dsimp only [homotopyPullbackMap]
  infer_instance

/-- The actual carrier-lift homotopy-pullback comparison is a canonical Iso. -/
public def homotopyPullbackIso {X Y B : TopCat.{u}} (f : X ⟶ B) (g : Y ⟶ B) :
    TopCat.uliftFunctor.{v, u}.obj (TopCat.homotopyPullback f g) ≅
      TopCat.homotopyPullback
        (TopCat.uliftFunctor.{v, u}.map f) (TopCat.uliftFunctor.{v, u}.map g) :=
  asIso (homotopyPullbackMap.{u, v} f g)

@[reassoc]
public theorem homotopyPullbackIso_hom_left {X Y B : TopCat.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) :
    (homotopyPullbackIso.{u, v} f g).hom ≫
        TopCat.homotopyPullbackLeft
          (TopCat.uliftFunctor.{v, u}.map f) (TopCat.uliftFunctor.{v, u}.map g) =
      TopCat.uliftFunctor.{v, u}.map (TopCat.homotopyPullbackLeft f g) := by
  simp only [homotopyPullbackIso, asIso_hom, homotopyPullbackMap,
    TopCat.homotopyPullbackLeft, Category.assoc, pullback.map,
    pullback.lift_fst_assoc, prodComparison_fst,
    pullbackComparison_comp_fst_assoc, Functor.map_comp]

@[reassoc]
public theorem homotopyPullbackIso_hom_path {X Y B : TopCat.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) :
    (homotopyPullbackIso.{u, v} f g).hom ≫
        TopCat.homotopyPullbackPath
          (TopCat.uliftFunctor.{v, u}.map f) (TopCat.uliftFunctor.{v, u}.map g) =
      TopCat.uliftFunctor.{v, u}.map (TopCat.homotopyPullbackPath f g) ≫
        (pathObjectIso.{u, v} B).hom := by
  simp only [homotopyPullbackIso, asIso_hom, homotopyPullbackMap,
    TopCat.homotopyPullbackPath, Category.assoc, pullback.map, pullback.lift_snd,
    pullbackComparison_comp_snd_assoc]

private instance pathObjectMapIsIso {B B' : TopCat.{w}}
    (h : B ⟶ B') [IsIso h] : IsIso (TopCat.pathObjectMap h) := by
  refine ⟨⟨TopCat.pathObjectMap (inv h), ?_, ?_⟩⟩
  · rw [← TopCat.pathObjectMap_comp, IsIso.hom_inv_id, TopCat.pathObjectMap_id]
  · rw [← TopCat.pathObjectMap_comp, IsIso.inv_hom_id, TopCat.pathObjectMap_id]

private theorem originalHomotopyPullbackMapIsIso
    {X Y B X' Y' B' : TopCat.{w}}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : X' ⟶ B'} {g' : Y' ⟶ B'}
    (l : X ⟶ X') (r : Y ⟶ Y') (h : B ⟶ B')
    (hf : f ≫ h = l ≫ f') (hg : g ≫ h = r ≫ g')
    [IsIso l] [IsIso r] [IsIso h] :
    IsIso (TopCat.homotopyPullbackMap l r h hf hg) := by
  have hp : Limits.prod.map f g ≫ Limits.prod.map h h =
      Limits.prod.map l r ≫ Limits.prod.map f' g' := by
    simp only [Limits.prod.map_map]
    rw [hf, hg]
  have hm : TopCat.homotopyPullbackMap l r h hf hg =
      pullback.map (Limits.prod.map f g) (TopCat.pathEndpoints B)
        (Limits.prod.map f' g') (TopCat.pathEndpoints B')
        (Limits.prod.map l r) (TopCat.pathObjectMap h) (Limits.prod.map h h)
        hp (TopCat.pathObjectMap_endpoints h).symm := by
    apply pullback.hom_ext
    · simp only [TopCat.homotopyPullbackMap, pullback.map, pullback.lift_fst]
    · simp only [TopCat.homotopyPullbackMap, pullback.map, pullback.lift_snd]
  rw [hm]
  infer_instance

private def pointIso :
    TopCat.uliftFunctor.{v, u}.obj (TopCat.of PUnit.{u + 1}) ≅
      TopCat.of PUnit.{max u v + 1} :=
  TopCat.isoOfHomeo
    { toFun := fun _ => PUnit.unit
      invFun := fun _ => ULift.up PUnit.unit
      left_inv := fun x => Subsingleton.elim (ULift.up PUnit.unit) x
      right_inv := fun x => Subsingleton.elim PUnit.unit x
      continuous_toFun := continuous_const
      continuous_invFun := continuous_const }

/-- The actual lifted ending-path fiber is homeomorphic to the lift of
the actual old ending-path fiber, including the canonical one-point input. -/
public def homotopyFiberIso {X B : TopCat.{u}} (f : X ⟶ B) (b : B) :
    TopCat.uliftFunctor.{v, u}.obj (TopCat.homotopyFiber f b) ≅
      TopCat.homotopyFiber (TopCat.uliftFunctor.{v, u}.map f) (ULift.up b) := by
  let U := TopCat.uliftFunctor.{v, u}
  let P := TopCat.of PUnit.{u + 1}
  let P' := TopCat.of PUnit.{max u v + 1}
  let e := pointIso.{u, v}
  let c : P ⟶ B := TopCat.const b
  let c' : P' ⟶ U.obj B := TopCat.const (ULift.up b)
  have hc : U.map c = e.hom ≫ c' := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro q
    rfl
  let m : TopCat.homotopyPullback (U.map f) (U.map c) ⟶
      TopCat.homotopyFiber (U.map f) (ULift.up b) :=
    TopCat.homotopyPullbackMap (𝟙 (U.obj X)) e.hom (𝟙 (U.obj B))
      (by simp) (by simpa only [Category.comp_id] using hc)
  let : IsIso m := originalHomotopyPullbackMapIsIso _ _ _ _ _
  exact homotopyPullbackIso.{u, v} f c ≪≫ asIso m

@[reassoc]
public theorem homotopyFiberIso_hom_toTotal {X B : TopCat.{u}} (f : X ⟶ B) (b : B) :
    (homotopyFiberIso.{u, v} f b).hom ≫
        TopCat.homotopyFiberToTotal (TopCat.uliftFunctor.{v, u}.map f) (ULift.up b) =
      TopCat.uliftFunctor.{v, u}.map (TopCat.homotopyFiberToTotal f b) := by
  simp only [homotopyFiberIso, Iso.trans_hom, asIso_hom,
    TopCat.homotopyFiberToTotal, Category.assoc,
    TopCat.homotopyPullbackMap_left, Category.comp_id,
    homotopyPullbackIso_hom_left]

@[reassoc]
public theorem homotopyFiberIso_hom_path {X B : TopCat.{u}} (f : X ⟶ B) (b : B) :
    (homotopyFiberIso.{u, v} f b).hom ≫
        TopCat.homotopyFiberPath (TopCat.uliftFunctor.{v, u}.map f) (ULift.up b) =
      TopCat.uliftFunctor.{v, u}.map (TopCat.homotopyFiberPath f b) ≫
        (pathObjectIso.{u, v} B).hom := by
  simp only [homotopyFiberIso, Iso.trans_hom, asIso_hom,
    TopCat.homotopyFiberPath, Category.assoc,
    TopCat.homotopyPullbackMap_path, TopCat.pathObjectMap_id,
    Category.comp_id, homotopyPullbackIso_hom_path]

/-- An original source point gives an actual point of its ending-path
fiber over its image, using the constant original path. -/
public theorem homotopyFiber_at_image_nonempty {X B : TopCat.{u}}
    (f : X ⟶ B) (x : X) : Nonempty (TopCat.homotopyFiber f (f x)) := by
  let P := TopCat.of PUnit.{u + 1}
  let γ : TopCat.pathObject B := ContinuousMap.const TopCat.I.{u} (f x)
  let a : P ⟶ X := TopCat.const x
  let c : P ⟶ B := TopCat.const (f x)
  let k : P ⟶ TopCat.pathObject B := TopCat.const γ
  let l : P ⟶ X ⨯ P := Limits.prod.lift a (𝟙 P)
  have hw : l ≫ Limits.prod.map f c = k ≫ TopCat.pathEndpoints B := by
    apply Limits.prod.hom_ext
    · simp only [l, TopCat.pathEndpoints, Category.assoc, Limits.prod.map_fst,
        Limits.prod.lift_fst, Limits.prod.lift_fst_assoc]
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro q
      rfl
    · simp only [l, TopCat.pathEndpoints, Category.assoc, Limits.prod.map_snd,
        Limits.prod.lift_snd, Limits.prod.lift_snd_assoc, Category.id_comp]
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro q
      rfl
  let z : P ⟶ TopCat.homotopyFiber f (f x) := pullback.lift l k hw
  exact ⟨z PUnit.unit⟩

/-- Integral acyclicity of the actual old fiber over an image point
transports to the actual lifted fiber, without a supplied comparison. -/
public theorem isAcyclicMapAt_ulift_at_image {X B : TopCat.{u}}
    (f : X ⟶ B) (x : X) (hf : TopCat.IsAcyclicMapAt f (f x)) :
    TopCat.IsAcyclicMapAt (TopCat.uliftFunctor.{v, u}.map f) (ULift.up (f x)) := by
  let : Nonempty (TopCat.homotopyFiber f (f x)) := homotopyFiber_at_image_nonempty f x
  have hLift := AlgebraicTopology.IntegralUniverseLift.isAcyclicSpace_ulift.{u, v}
    (TopCat.homotopyFiber f (f x)) hf
  intro n
  let H := AlgebraicTopology.reducedSingularHomologyFunctor AddCommGrpCat.{max u v}
    AlgebraicTopology.singularIntegralCoefficients.{max u v} n
  exact IsZero.of_iso (hLift n) (H.mapIso (homotopyFiberIso.{u, v} f (f x))).symm

end TopCat.UniverseLift
