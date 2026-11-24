/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.Topology.Homotopy.HSpaces
public import Mathlib.Topology.Homotopy.Equiv

/-!
# H-space transport through the actual based homotopy equivalence

The operation is conjugated by the given continuous forward and inverse
maps. Both point-relative inverse families are used. The transferred unit
is the literal chosen point, including both whole relative unit families.
-/

noncomputable section

open ContinuousMap
open scoped ContinuousMap

universe u v

namespace ContinuousMap.HomotopyEquiv

/-- A based homotopy equivalence with BOTH actual point-relative inverse
families transfers an H-space to the original target carrier and point. -/
public def pointRelativeHSpaceTransfer
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (H : HSpace X) (y : Y)
    (he : e.toFun H.e = y)
    (LX : HomotopyRel (e.invFun.comp e.toFun) (ContinuousMap.id X) {H.e})
    (RY : HomotopyRel (e.toFun.comp e.invFun) (ContinuousMap.id Y) {y}) :
    { D : HSpace Y // D.e = y ∧
        D.hmul = e.toFun.comp (H.hmul.comp (e.invFun.prodMap e.invFun)) } := by
  letI : HSpace X := H
  have hg : e.invFun y = H.e :=
    (congrArg e.invFun he).symm.trans
      (LX.fst_eq_snd (Set.mem_singleton H.e))
  let μ : C(Y × Y, Y) :=
    e.toFun.comp (H.hmul.comp (e.invFun.prodMap e.invFun))
  have hμ : μ (y, y) = y := by
    change e.toFun (H.hmul (e.invFun y, e.invFun y)) = y
    rw [hg, H.hmul_e_e, he]
  let KL : HomotopyRel
      (μ.comp ((ContinuousMap.const Y y).prodMk (ContinuousMap.id Y)))
      (e.toFun.comp e.invFun) {y} :=
    { toFun := fun z => e.toFun (H.eHmul (z.1, e.invFun z.2))
      continuous_toFun := e.toFun.continuous.comp
        (H.eHmul.continuous_toFun.comp
          (continuous_fst.prodMk (e.invFun.continuous.comp continuous_snd)))
      map_zero_left := fun z => by
        change e.toFun (H.eHmul.toFun (0, e.invFun z)) =
          e.toFun (H.hmul (e.invFun y, e.invFun z))
        have h0 : H.eHmul.toFun (0, e.invFun z) =
            H.hmul (H.e, e.invFun z) :=
          H.eHmul.map_zero_left (e.invFun z)
        exact (congrArg e.toFun h0).trans
          (congrArg (fun x => e.toFun (H.hmul (x, e.invFun z))) hg.symm)
      map_one_left := fun z => congrArg e.toFun (H.eHmul.map_one_left _)
      prop' := fun t z hz => by
        have hz' : z = y := Set.mem_singleton_iff.mp hz
        subst z
        change e.toFun (H.eHmul (t, e.invFun y)) =
          e.toFun (H.hmul (e.invFun y, e.invFun y))
        rw [hg]
        exact congrArg e.toFun (H.eHmul.eq_fst t (Set.mem_singleton H.e)) }
  let KR : HomotopyRel
      (μ.comp ((ContinuousMap.id Y).prodMk (ContinuousMap.const Y y)))
      (e.toFun.comp e.invFun) {y} :=
    { toFun := fun z => e.toFun (H.hmulE (z.1, e.invFun z.2))
      continuous_toFun := e.toFun.continuous.comp
        (H.hmulE.continuous_toFun.comp
          (continuous_fst.prodMk (e.invFun.continuous.comp continuous_snd)))
      map_zero_left := fun z => by
        change e.toFun (H.hmulE.toFun (0, e.invFun z)) =
          e.toFun (H.hmul (e.invFun z, e.invFun y))
        have h0 : H.hmulE.toFun (0, e.invFun z) =
            H.hmul (e.invFun z, H.e) :=
          H.hmulE.map_zero_left (e.invFun z)
        exact (congrArg e.toFun h0).trans
          (congrArg (fun x => e.toFun (H.hmul (e.invFun z, x))) hg.symm)
      map_one_left := fun z => congrArg e.toFun (H.hmulE.map_one_left _)
      prop' := fun t z hz => by
        have hz' : z = y := Set.mem_singleton_iff.mp hz
        subst z
        change e.toFun (H.hmulE (t, e.invFun y)) =
          e.toFun (H.hmul (e.invFun y, e.invFun y))
        rw [hg]
        exact congrArg e.toFun (H.hmulE.eq_fst t (Set.mem_singleton H.e)) }
  exact ⟨
    { hmul := μ
      e := y
      hmul_e_e := hμ
      eHmul := KL.trans RY
      hmulE := KR.trans RY },
    rfl, rfl⟩

end ContinuousMap.HomotopyEquiv

end
