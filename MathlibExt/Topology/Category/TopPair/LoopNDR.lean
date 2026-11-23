/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.PointedTopCat
public import MathlibExt.Topology.Category.TopPair.NDR
public import Mathlib.Topology.Homotopy.HomotopyGroup
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Standard NDR data for the actual constant loop

The raw pointed loop space has the compact-open path topology and the literal
reflexive loop as its point. Standard NDR data at the original point gives
standard NDR data at this loop: take the norm of the point control along a loop
and apply the original relative deformation pointwise.
-/

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Topology
open scoped unitInterval

universe u

namespace PointedTopCat

/-- The raw compact-open loop space, pointed at the literal constant loop. -/
abbrev loopSpace (X : PointedTopCat.{u}) : PointedTopCat.{u} :=
  { left := Discrete.mk PUnit.unit
    right := TopCat.of (LoopSpace X.right (X.hom PUnit.unit))
    hom := TopCat.const (X := TopCat.of PUnit)
      (Path.refl (X.hom PUnit.unit)) }

/-- The pointed loop object's carrier is the actual compact-open path loop space. -/
@[simp]
theorem loopSpace_right (X : PointedTopCat.{u}) :
    (loopSpace X).right = TopCat.of (LoopSpace X.right (X.hom PUnit.unit)) := rfl

/-- Its distinguished point is precisely the reflexive loop at the original point. -/
@[simp]
theorem loopSpace_basepoint (X : PointedTopCat.{u}) :
    (loopSpace X).hom PUnit.unit = Path.refl (X.hom PUnit.unit) := rfl

/-- The actual constant-loop point pair, with its raw path carrier exposed. -/
abbrev loopPair (X : PointedTopCat.{u}) : TopPair.{u} :=
  TopPair.of (A := TopCat.of PUnit)
    (X := TopCat.of (LoopSpace X.right (X.hom PUnit.unit)))
    (TopCat.const (Path.refl (X.hom PUnit.unit)))
    (Topology.IsEmbedding.of_subsingleton _)

/-- The raw loop point pair is the canonical pointed pair of the loop object. -/
theorem loopPair_eq_pointedPair (X : PointedTopCat.{u}) :
    loopPair X = pointedPair.obj (loopSpace X) := rfl

end PointedTopCat

namespace TopPair.StandardNDRData

variable {X : PointedTopCat.{u}} (d : StandardNDRData (PointedTopCat.pointedPair.obj X))

private abbrev LoopCarrier := LoopSpace X.right (X.hom PUnit.unit)

private theorem point_control : d.control (X.hom PUnit.unit) = 0 :=
  (d.control_eq_zero_iff _).mpr ⟨PUnit.unit, rfl⟩

private theorem point_endpoint : d.endpoint (X.hom PUnit.unit) = X.hom PUnit.unit :=
  (d.deformation.fst_eq_snd ⟨PUnit.unit, rfl⟩).symm

private def controlMap : C(X.right, ℝ) where
  toFun x := (d.control x : ℝ)
  continuous_toFun := continuous_subtype_val.comp d.control.continuous

private def controlNorm (gamma : LoopCarrier (X := X)) : ℝ :=
  ‖(controlMap d).comp gamma.toContinuousMap‖

private theorem continuous_controlNorm : Continuous (controlNorm d) := by
  exact continuous_norm.comp
    ((ContinuousMap.continuous_postcomp (controlMap d)).comp continuous_induced_dom)

private theorem controlNorm_le_one (gamma : LoopCarrier (X := X)) :
    controlNorm d gamma ≤ 1 := by
  apply (ContinuousMap.norm_le _ zero_le_one).mpr
  intro t
  change ‖(d.control (gamma t) : ℝ)‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg (d.control (gamma t)).property.1]
  exact (d.control (gamma t)).property.2

private def loopControl : C(LoopCarrier (X := X), unitInterval) where
  toFun gamma := ⟨controlNorm d gamma, norm_nonneg _, controlNorm_le_one d gamma⟩
  continuous_toFun := (continuous_controlNorm d).subtype_mk _

private def loopEndpointPath (gamma : LoopCarrier (X := X)) : LoopCarrier (X := X) where
  toContinuousMap := d.endpoint.comp gamma.toContinuousMap
  source' := by
    change d.endpoint (gamma 0) = X.hom PUnit.unit
    rw [gamma.source, point_endpoint]
  target' := by
    change d.endpoint (gamma 1) = X.hom PUnit.unit
    rw [gamma.target, point_endpoint]

private def loopEndpointMap : C(LoopCarrier (X := X), LoopCarrier (X := X)) where
  toFun := loopEndpointPath d
  continuous_toFun := Path.continuous_uncurry_iff.mp
    (d.endpoint.continuous.comp (continuous_fst.eval continuous_snd))

private def loopDeformationPath (s : unitInterval) (gamma : LoopCarrier (X := X)) :
    LoopCarrier (X := X) where
  toContinuousMap :=
    { toFun t := d.deformation (s, gamma t)
      continuous_toFun := d.deformation.continuous.comp
        (continuous_const.prodMk gamma.continuous) }
  source' := by
    change d.deformation (s, gamma 0) = X.hom PUnit.unit
    rw [gamma.source]
    exact d.deformation.eq_fst s ⟨PUnit.unit, rfl⟩
  target' := by
    change d.deformation (s, gamma 1) = X.hom PUnit.unit
    rw [gamma.target]
    exact d.deformation.eq_fst s ⟨PUnit.unit, rfl⟩

private def loopDeformationData :
    ContinuousMap.HomotopyRel (ContinuousMap.id (LoopCarrier (X := X)))
      (loopEndpointMap d)
      (Set.range (PointedTopCat.pointedPair.obj (PointedTopCat.loopSpace X)).map) where
  toFun z := loopDeformationPath d z.1 z.2
  continuous_toFun := Path.continuous_uncurry_iff.mp
    (d.deformation.continuous.comp
      ((continuous_fst.comp continuous_fst).prodMk
        ((continuous_snd.comp continuous_fst).eval continuous_snd)))
  map_zero_left gamma := by
    apply Path.ext
    funext t
    exact d.deformation.apply_zero (gamma t)
  map_one_left gamma := by
    apply Path.ext
    funext t
    exact d.deformation.apply_one (gamma t)
  prop' s gamma hgamma := by
    obtain ⟨p, rfl⟩ := hgamma
    apply Path.ext
    funext t
    exact d.deformation.eq_fst s ⟨PUnit.unit, rfl⟩

private theorem loopControl_eq_zero_iff (gamma : LoopCarrier (X := X)) :
    loopControl d gamma = 0 ↔
      gamma ∈ Set.range (PointedTopCat.pointedPair.obj (PointedTopCat.loopSpace X)).map := by
  constructor
  · intro h
    have hnorm : controlNorm d gamma = 0 := congrArg Subtype.val h
    have hmap : (controlMap d).comp gamma.toContinuousMap = 0 := norm_eq_zero.mp hnorm
    refine ⟨PUnit.unit, ?_⟩
    apply Path.ext
    funext t
    have hu : d.control (gamma t) = 0 := by
      apply Subtype.ext
      exact congrArg (fun f : C(unitInterval, ℝ) => f t) hmap
    obtain ⟨p, hp⟩ := (d.control_eq_zero_iff (gamma t)).mp hu
    change X.hom p = gamma t at hp
    cases p
    exact hp
  · rintro ⟨p, rfl⟩
    apply Subtype.ext
    apply norm_eq_zero.mpr
    ext t
    change (d.control (X.hom PUnit.unit) : ℝ) = 0
    rw [point_control]
    rfl

private theorem loopEndpoint_mem_range (gamma : LoopCarrier (X := X))
    (hgamma : loopControl d gamma < 1) :
    loopEndpointMap d gamma ∈
      Set.range (PointedTopCat.pointedPair.obj (PointedTopCat.loopSpace X)).map := by
  refine ⟨PUnit.unit, ?_⟩
  apply Path.ext
  funext t
  have hu : d.control (gamma t) < 1 := by
    change (d.control (gamma t) : ℝ) < 1
    have hbound := ((controlMap d).comp gamma.toContinuousMap).norm_coe_le_norm t
    change ‖(d.control (gamma t) : ℝ)‖ ≤ controlNorm d gamma at hbound
    rw [Real.norm_eq_abs, abs_of_nonneg (d.control (gamma t)).property.1] at hbound
    exact hbound.trans_lt hgamma
  obtain ⟨p, hp⟩ := d.endpoint_mem_range (gamma t) hu
  change X.hom p = d.endpoint (gamma t) at hp
  cases p
  exact hp

/-- Standard NDR data at the actual constant loop, derived from the original point data. -/
def loop : StandardNDRData (PointedTopCat.loopPair X) where
  control := loopControl d
  endpoint := loopEndpointMap d
  deformation := loopDeformationData d
  control_eq_zero_iff := loopControl_eq_zero_iff d
  endpoint_mem_range := loopEndpoint_mem_range d

/-- The constructed endpoint as a map between the actual raw loop carriers. -/
@[expose]
def loopEndpoint : C(LoopSpace X.right (X.hom PUnit.unit),
    LoopSpace X.right (X.hom PUnit.unit)) :=
  (d.loop (X := X)).endpoint

/-- The constructed relative deformation with its raw loop value type retained. -/
@[expose]
def loopDeformation :
    ContinuousMap.HomotopyRel
      (ContinuousMap.id (LoopSpace X.right (X.hom PUnit.unit))) (loopEndpoint d)
      (Set.range (PointedTopCat.loopPair X).map) :=
  (d.loop (X := X)).deformation

private theorem loop_control_norm_private (gamma : LoopSpace X.right (X.hom PUnit.unit)) :
    ((d.loop (X := X)).control gamma : ℝ) =
      ‖(⟨fun x : X.right => (d.control x : ℝ),
        continuous_subtype_val.comp d.control.continuous⟩ : C(X.right, ℝ)).comp
          gamma.toContinuousMap‖ := by rfl

/-- The actual loop control is the compact-domain norm of the original point control. -/
theorem loop_control_norm (gamma : LoopSpace X.right (X.hom PUnit.unit)) :
    ((d.loop (X := X)).control gamma : ℝ) =
      ‖(⟨fun x : X.right => (d.control x : ℝ),
        continuous_subtype_val.comp d.control.continuous⟩ : C(X.right, ℝ)).comp
          gamma.toContinuousMap‖ := loop_control_norm_private d gamma

private theorem loop_endpoint_apply_private (gamma : LoopSpace X.right (X.hom PUnit.unit))
    (t : unitInterval) :
    d.loopEndpoint gamma t = d.endpoint (gamma t) := by rfl

/-- The loop endpoint is the original endpoint applied at each interval parameter. -/
@[simp]
theorem loop_endpoint_apply (gamma : LoopSpace X.right (X.hom PUnit.unit)) (t : unitInterval) :
    d.loopEndpoint gamma t = d.endpoint (gamma t) :=
  loop_endpoint_apply_private d gamma t

private theorem loop_deformation_apply_private (s : unitInterval)
    (gamma : LoopSpace X.right (X.hom PUnit.unit)) (t : unitInterval) :
    d.loopDeformation (s, gamma) t = d.deformation (s, gamma t) := by rfl

/-- The actual loop deformation applies the original relative deformation pointwise. -/
@[simp]
theorem loop_deformation_apply (s : unitInterval) (gamma : LoopSpace X.right (X.hom PUnit.unit))
    (t : unitInterval) :
    d.loopDeformation (s, gamma) t = d.deformation (s, gamma t) :=
  loop_deformation_apply_private d s gamma t

end TopPair.StandardNDRData

end
