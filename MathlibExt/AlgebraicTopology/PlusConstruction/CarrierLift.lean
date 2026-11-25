/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.FundamentalGroupoid.FundamentalGroupIso
public import MathlibExt.AlgebraicTopology.FundamentalGroupoid.PiOneMapComposition
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.GroupTheory.IsPerfect

/-!
# The original perfect subgroup under an independent carrier lift

The carrier homeomorphism supplies both actual based fundamental-group
maps. Their two composite identities compute the transported subgroup.
Normality and perfectness follow from this dictionary; the scalar ring
and the original subgroup remain unchanged.
-/

set_option autoImplicit false

noncomputable section

open scoped ContinuousMap

universe u v

namespace FundamentalGroup.UniverseLift

/-- The actual based map of the carrier projection, including its original
image-point equality. -/
public abbrev downMap (X : Type u) [TopologicalSpace X] (x : X) :
    FundamentalGroup (ULift.{v} X) (ULift.up x) →* FundamentalGroup X x :=
  FundamentalGroup.mapOfEq
    (Homeomorph.ulift : ULift.{v} X ≃ₜ X).toHomotopyEquiv.toFun rfl

/-- The actual based map of the inverse carrier homeomorphism. -/
public abbrev upMap (X : Type u) [TopologicalSpace X] (x : X) :
    FundamentalGroup X x →* FundamentalGroup (ULift.{v} X) (ULift.up x) :=
  FundamentalGroup.mapOfEq
    (Homeomorph.ulift.symm : X ≃ₜ ULift.{v} X).toHomotopyEquiv.toFun rfl

/-- The carrier projection gives a multiplicative equivalence of the
original based fundamental groups. -/
public def downMulEquiv (X : Type u) [TopologicalSpace X] (x : X) :
    FundamentalGroup (ULift.{v} X) (ULift.up x) ≃* FundamentalGroup X x :=
  FundamentalGroup.mulEquivOfHomeomorphAt
    (Homeomorph.ulift : ULift.{v} X ≃ₜ X) (ULift.up x) x rfl

/-- The forward map of this equivalence is the literal carrier projection
map on every original fundamental-group element. -/
public theorem downMulEquiv_toMonoidHom
    (X : Type u) [TopologicalSpace X] (x : X) :
    (downMulEquiv.{u, v} X x).toMonoidHom = downMap.{u, v} X x := by
  unfold downMulEquiv
  apply MonoidHom.ext
  intro q
  exact FundamentalGroup.mulEquivOfHomeomorphAt_apply
    (Homeomorph.ulift : ULift.{v} X ≃ₜ X) (ULift.up x) x rfl q

/-- The actual upward map followed by the actual projection is the
original identity, including its original image-point equality. -/
public theorem downMap_comp_upMap
    (X : Type u) [TopologicalSpace X] (x : X) :
    (downMap.{u, v} X x).comp (upMap.{u, v} X x) =
      MonoidHom.id (FundamentalGroup X x) := by
  let f := (Homeomorph.ulift.symm : X ≃ₜ ULift.{v} X).toHomotopyEquiv.toFun
  let g := (Homeomorph.ulift : ULift.{v} X ≃ₜ X).toHomotopyEquiv.toFun
  have hc : (g.comp f) x = x := rfl
  have hcomp := FundamentalGroup.mapOfEq_comp f g rfl rfl hc
  have hfg : (⟨g.comp f, hc⟩ : {k : C(X, X) // k x = x}) =
      ⟨ContinuousMap.id X, rfl⟩ := Subtype.ext (by ext z; rfl)
  have hmap := congrArg
    (fun k : {k : C(X, X) // k x = x} =>
      FundamentalGroup.mapOfEq k.val k.property) hfg
  exact hcomp.symm.trans (hmap.trans (FundamentalGroup.mapOfEq_id x rfl))

/-- The actual projection followed by the actual upward map is the
identity on the independently lifted original carrier. -/
public theorem upMap_comp_downMap
    (X : Type u) [TopologicalSpace X] (x : X) :
    (upMap.{u, v} X x).comp (downMap.{u, v} X x) =
      MonoidHom.id (FundamentalGroup (ULift.{v} X) (ULift.up x)) := by
  let f := (Homeomorph.ulift : ULift.{v} X ≃ₜ X).toHomotopyEquiv.toFun
  let g := (Homeomorph.ulift.symm : X ≃ₜ ULift.{v} X).toHomotopyEquiv.toFun
  have hc : (g.comp f) (ULift.up x) = ULift.up x := rfl
  have hcomp := FundamentalGroup.mapOfEq_comp f g rfl rfl hc
  have hfg :
      (⟨g.comp f, hc⟩ :
        {k : C(ULift.{v} X, ULift.{v} X) // k (ULift.up x) = ULift.up x}) =
          ⟨ContinuousMap.id (ULift.{v} X), rfl⟩ :=
    Subtype.ext (by
      apply ContinuousMap.ext
      intro z
      exact (Homeomorph.ulift : ULift.{v} X ≃ₜ X).symm_apply_apply z)
  have hmap := congrArg
    (fun k : {k : C(ULift.{v} X, ULift.{v} X) // k (ULift.up x) = ULift.up x} =>
      FundamentalGroup.mapOfEq k.val k.property) hfg
  exact hcomp.symm.trans
    (hmap.trans (FundamentalGroup.mapOfEq_id (ULift.up x) rfl))

/-- The lifted subgroup is the literal comap through the actual carrier
projection, rather than an independently selected perfect subgroup. -/
public abbrev comapSubgroup (X : Type u) [TopologicalSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    Subgroup (FundamentalGroup (ULift.{v} X) (ULift.up x)) :=
  P.comap (downMap.{u, v} X x)

/-- Membership in the transported subgroup is membership of the actual
downward image in the original subgroup. -/
public theorem mem_comapSubgroup_iff
    (X : Type u) [TopologicalSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x))
    (q : FundamentalGroup (ULift.{v} X) (ULift.up x)) :
    q ∈ comapSubgroup.{u, v} X x P ↔ downMap.{u, v} X x q ∈ P :=
  Iff.rfl

/-- The same transported subgroup is the image under the actual upward
map; both based inverse equations compute this equality. -/
public theorem map_up_eq_comap_down
    (X : Type u) [TopologicalSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    P.map (upMap.{u, v} X x) = comapSubgroup.{u, v} X x P := by
  apply Subgroup.ext
  intro q
  constructor
  · intro hq
    obtain ⟨p, hp, hpq⟩ := Subgroup.mem_map.mp hq
    change downMap.{u, v} X x q ∈ P
    have hdp : downMap.{u, v} X x (upMap.{u, v} X x p) = p :=
      congrArg (fun k : FundamentalGroup X x →* FundamentalGroup X x => k p)
        (downMap_comp_upMap.{u, v} X x)
    rw [← hpq, hdp]
    exact hp
  · intro hq
    change downMap.{u, v} X x q ∈ P at hq
    have hup : upMap.{u, v} X x (downMap.{u, v} X x q) = q :=
      congrArg
        (fun k : FundamentalGroup (ULift.{v} X) (ULift.up x) →*
            FundamentalGroup (ULift.{v} X) (ULift.up x) => k q)
        (upMap_comp_downMap.{u, v} X x)
    exact Subgroup.mem_map.mpr ⟨downMap.{u, v} X x q, hq, hup⟩

/-- Original normality is retained by the computed comap. -/
public theorem comapSubgroup_normal
    (X : Type u) [TopologicalSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] :
    (comapSubgroup.{u, v} X x P).Normal := by
  change (P.comap (downMap.{u, v} X x)).Normal
  infer_instance

/-- Original perfectness is retained by the computed image/comap
dictionary; no new perfect subgroup witness is supplied. -/
public theorem comapSubgroup_isPerfect
    (X : Type u) [TopologicalSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [Group.IsPerfect P] :
    Group.IsPerfect (comapSubgroup.{u, v} X x P) := by
  rw [← map_up_eq_comap_down.{u, v} X x P]
  exact Group.IsPerfect.map (upMap.{u, v} X x)

end FundamentalGroup.UniverseLift

end
