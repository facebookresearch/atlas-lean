/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.CofibrantPointTraceRetuning
public import MathlibExt.Topology.Category.TopCat.TrivialCofibrationExtension
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

/-!
# Strict and point-relative units from one actual common root trace

Multiplication is first retuned at its original source point by genuine
homotopy extension. Each whole unit family is then a reverse root trace
followed by the same forward root trace. The standard path cancellation
homotopy and endpoint-fixed fiber extension make BOTH families relative
to the original unit point.
-/

noncomputable section

open CategoryTheory Limits HomotopicalAlgebra
open scoped ContinuousMap TopCat.modelCategory

universe u

namespace TopCat.CoherentWeakUnitRetuning

private theorem unitTrace
    {X U : TopCat.{u}} (μ ν : U ⟶ X) (a : X ⟶ U) (e : X) (p : U)
    (ha : a e = p) (hν : ν p = e)
    (r : _root_.Path (μ p) e) (H : TopCat.Homotopy μ ν)
    (hH : ∀ t : unitInterval, H (t, p) = r t)
    (K : TopCat.Homotopy (a ≫ μ) (𝟙 X)) :
    (((TopCat.Homotopy.comp H.symm (TopCat.Homotopy.refl a)).trans K).evalAt e).cast
        ((congrArg ν ha).trans hν).symm rfl =
      r.symm.trans ((K.evalAt e).cast (congrArg μ ha).symm rfl) := by
  have hA (t : unitInterval) : H (t, a e) = r t :=
    (congrArg (fun z => H (t, z)) ha).trans (hH t)
  have hcomp (s : unitInterval) :
      (TopCat.Homotopy.comp H.symm (TopCat.Homotopy.refl a)) (s, e) = r.symm s := by
    have hRefl : (TopCat.Homotopy.refl a) (s, e) = a e :=
      ContinuousMap.Homotopy.refl_apply a.hom (s, e)
    calc
      (TopCat.Homotopy.comp H.symm (TopCat.Homotopy.refl a)) (s, e) =
          H.symm (s, (TopCat.Homotopy.refl a) (s, e)) :=
        TopCat.Homotopy.comp_apply H.symm (TopCat.Homotopy.refl a) (s, e)
      _ = H.symm (s, a e) := congrArg (fun z : U => H.symm (s, z)) hRefl
      _ = H (unitInterval.symm s, a e) :=
        ContinuousMap.Homotopy.symm_apply H (s, a e)
      _ = r (unitInterval.symm s) := hA (unitInterval.symm s)
      _ = r.symm s := (_root_.Path.symm_apply r s).symm
  apply _root_.Path.ext
  funext t
  change ((TopCat.Homotopy.comp H.symm (TopCat.Homotopy.refl a)).trans K) (t, e) =
    (r.symm.trans ((K.evalAt e).cast (congrArg μ ha).symm rfl)) t
  rw [ContinuousMap.Homotopy.trans_apply, _root_.Path.trans_apply]
  split_ifs with ht
  · let s : unitInterval :=
      ⟨2 * (t : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).mpr ⟨t.property.1, ht⟩⟩
    change (TopCat.Homotopy.comp H.symm (TopCat.Homotopy.refl a)) (s, e) = r.symm s
    exact hcomp s
  · rfl

/-- Actual coherent weak-unit families give a derived operation with a
strict original point equation and BOTH whole point-relative unit
homotopies. The original multiplication is retained through a calibrated
homotopy, whose entire point trace is the original root path. -/
public theorem _root_.TopCat.exists_strict_pointRelative_units_of_common_trace
    {X U : TopCat.{u}} (μ : U ⟶ X) (left right : X ⟶ U)
    (e : X) (p : U)
    [Cofibration (TopCat.const e : TopCat.of PUnit.{u + 1} ⟶ X)]
    [Cofibration (TopCat.const p : TopCat.of PUnit.{u + 1} ⟶ U)]
    (hleft : left e = p) (hright : right e = p)
    (r : _root_.Path (μ p) e)
    (L : TopCat.Homotopy (left ≫ μ) (𝟙 X))
    (R : TopCat.Homotopy (right ≫ μ) (𝟙 X))
    (hL : ((L.evalAt e).cast (congrArg μ hleft).symm rfl).Homotopic r)
    (hR : ((R.evalAt e).cast (congrArg μ hright).symm rfl).Homotopic r) :
    ∃ ν : U ⟶ X, ν p = e ∧
      Nonempty (ContinuousMap.HomotopyRel (left ≫ ν).hom (𝟙 X : X ⟶ X).hom {e}) ∧
      Nonempty (ContinuousMap.HomotopyRel (right ≫ ν).hom (𝟙 X : X ⟶ X).hom {e}) ∧
      ∃ H : TopCat.Homotopy μ ν,
        ∀ t : unitInterval, H (t, p) = r t := by
  let A : TopCat.{u} := TopCat.of PUnit.{u + 1}
  let i : A ⟶ U := TopCat.const p
  let k : A ⟶ X := TopCat.const e
  let K : TopCat.Homotopy (i ≫ μ) k :=
    { toFun := fun z => r z.1
      continuous_toFun := r.continuous.comp continuous_fst
      map_zero_left := fun _ => r.source
      map_one_left := fun _ => r.target }
  obtain ⟨ν, H, hi, htrace⟩ :=
    TopCat.exists_homotopyExtension_of_cofibration i μ k K
  have hν : ν p = e := ConcreteCategory.congr_hom hi PUnit.unit
  have hH (t : unitInterval) : H (t, p) = r t := htrace t PUnit.unit
  let LL : TopCat.Homotopy (left ≫ ν) (𝟙 X) :=
    (TopCat.Homotopy.comp H.symm (TopCat.Homotopy.refl left)).trans L
  let RR : TopCat.Homotopy (right ≫ ν) (𝟙 X) :=
    (TopCat.Homotopy.comp H.symm (TopCat.Homotopy.refl right)).trans R
  have hLe : (left ≫ ν) e = e := (congrArg ν hleft).trans hν
  have hRe : (right ≫ ν) e = e := (congrArg ν hright).trans hν
  have hLT : (LL.evalAt e).cast hLe.symm rfl =
      r.symm.trans ((L.evalAt e).cast (congrArg μ hleft).symm rfl) :=
    unitTrace μ ν left e p hleft hν r H hH L
  have hRT : (RR.evalAt e).cast hRe.symm rfl =
      r.symm.trans ((R.evalAt e).cast (congrArg μ hright).symm rfl) :=
    unitTrace μ ν right e p hright hν r H hH R
  have hln : ((LL.evalAt e).cast hLe.symm rfl).Homotopic (_root_.Path.refl e) := by
    rw [hLT]
    exact ((_root_.Path.Homotopic.refl r.symm).hcomp hL).trans
      ⟨(_root_.Path.Homotopy.reflSymmTrans r).symm⟩
  have hrn : ((RR.evalAt e).cast hRe.symm rfl).Homotopic (_root_.Path.refl e) := by
    rw [hRT]
    exact ((_root_.Path.Homotopic.refl r.symm).hcomp hR).trans
      ⟨(_root_.Path.Homotopy.reflSymmTrans r).symm⟩
  obtain ⟨QL⟩ := hln
  obtain ⟨QR⟩ := hrn
  obtain ⟨LP⟩ := TopCat.exists_pointRelativeHomotopy_of_null_trace
    (left ≫ ν) (𝟙 X) e e hLe rfl LL QL
  obtain ⟨RP⟩ := TopCat.exists_pointRelativeHomotopy_of_null_trace
    (right ≫ ν) (𝟙 X) e e hRe rfl RR QR
  exact ⟨ν, hν, ⟨LP⟩, ⟨RP⟩, H, hH⟩

end TopCat.CoherentWeakUnitRetuning

end
