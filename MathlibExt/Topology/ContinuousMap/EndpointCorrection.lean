/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Category.TopCat.Monoidal
public import Mathlib.Topology.Algebra.Module.Basic

import Mathlib.Tactic.Abel

/-!
# Continuous affine correction of two endpoints

Let E be a real module with a topological additive group and continuous
scalar multiplication. Let I be the lifted closed unit interval and γ : C(I,E).
For desired endpoints a,b : E, define
Γ(s) = γ(s) + (1-t) • (a-γ(0)) + t • (b-γ(1)),
where t ∈ [0,1] is the real coordinate of s.
Then Γ(0)=a and Γ(1)=b. Correcting to the original endpoints fixes γ,
and Γ depends jointly continuously on γ,a,b for the compact-open topology.
-/

public section

noncomputable section

universe u

namespace ContinuousMap

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- Let E be a real module with a topological additive group and continuous
real scalar multiplication, and I the lifted closed unit interval.
For γ : C(I,E) and a,b : E, the corrected curve is
γ(s)+(1-t) • (a-γ(0))+t • (b-γ(1)), where t is the real coordinate of s. -/
def endpointCorrection (γ : C(TopCat.I.{u}, E)) (a b : E) : C(TopCat.I.{u}, E) where
  toFun s := γ s +
    (1 - (TopCat.I.homeomorph s : ℝ)) • (a - γ 0) +
    (TopCat.I.homeomorph s : ℝ) • (b - γ 1)
  continuous_toFun := by
    have ht : Continuous (fun s : TopCat.I.{u} => (TopCat.I.homeomorph s : ℝ)) :=
      TopCat.I.homeomorph.continuous.subtype_val
    exact (γ.continuous.add ((continuous_const.sub ht).smul continuous_const)).add
      (ht.smul continuous_const)

/-- Let E be a real module with a topological additive group and continuous
real scalar multiplication, and I the lifted closed unit interval.
For γ : C(I,E), a,b : E and s : I with real coordinate t,
the corrected value is γ(s)+(1-t) • (a-γ(0))+t • (b-γ(1)). -/
private theorem endpointCorrectionApplyComputed (γ : C(TopCat.I.{u}, E)) (a b : E)
    (s : TopCat.I.{u}) :
    endpointCorrection γ a b s = γ s +
      (1 - (TopCat.I.homeomorph s : ℝ)) • (a - γ 0) +
      (TopCat.I.homeomorph s : ℝ) • (b - γ 1) := rfl

/-- Let E be a real module with a topological additive group and continuous
real scalar multiplication, and I the lifted closed unit interval.
For γ : C(I,E), a,b : E and s : I with real coordinate t,
endpointCorrection γ a b s = γ(s)+(1-t) • (a-γ(0))+t • (b-γ(1)). -/
theorem endpointCorrection_apply (γ : C(TopCat.I.{u}, E)) (a b : E)
    (s : TopCat.I.{u}) :
    endpointCorrection γ a b s = γ s +
      (1 - (TopCat.I.homeomorph s : ℝ)) • (a - γ 0) +
      (TopCat.I.homeomorph s : ℝ) • (b - γ 1) :=
  endpointCorrectionApplyComputed γ a b s

/-- Let E be a real module with a topological additive group and continuous
real scalar multiplication, and I the lifted closed unit interval.
For γ : C(I,E) and a,b : E, the corrected curve has value a at 0. -/
private theorem endpointCorrectionZeroComputed (γ : C(TopCat.I.{u}, E)) (a b : E) :
    endpointCorrection γ a b 0 = a := by
  rw [endpointCorrection_apply, TopCat.I.homeomorph_zero]
  change γ 0 + (1 - (0 : ℝ)) • (a - γ 0) + (0 : ℝ) • (b - γ 1) = a
  simp only [sub_zero, one_smul, zero_smul, add_zero]
  abel

/-- Let E be a real module with a topological additive group and continuous
real scalar multiplication, and I the lifted closed unit interval.
For γ : C(I,E) and a,b : E, endpointCorrection γ a b 0 = a. -/
theorem endpointCorrection_zero (γ : C(TopCat.I.{u}, E)) (a b : E) :
    endpointCorrection γ a b 0 = a := endpointCorrectionZeroComputed γ a b

/-- Let E be a real module with a topological additive group and continuous
real scalar multiplication, and I the lifted closed unit interval.
For γ : C(I,E) and a,b : E, the corrected curve has value b at 1. -/
private theorem endpointCorrectionOneComputed (γ : C(TopCat.I.{u}, E)) (a b : E) :
    endpointCorrection γ a b 1 = b := by
  rw [endpointCorrection_apply, TopCat.I.homeomorph_one]
  change γ 1 + (1 - (1 : ℝ)) • (a - γ 0) + (1 : ℝ) • (b - γ 1) = b
  simp only [sub_self, zero_smul, one_smul, add_zero]
  abel

/-- Let E be a real module with a topological additive group and continuous
real scalar multiplication, and I the lifted closed unit interval.
For γ : C(I,E) and a,b : E, endpointCorrection γ a b 1 = b. -/
theorem endpointCorrection_one (γ : C(TopCat.I.{u}, E)) (a b : E) :
    endpointCorrection γ a b 1 = b := endpointCorrectionOneComputed γ a b

/-- Let E be a real module with a topological additive group and continuous
real scalar multiplication, and I the lifted closed unit interval.
Correcting any γ : C(I,E) to its own endpoint values γ(0),γ(1) returns γ. -/
private theorem endpointCorrectionSelfComputed (γ : C(TopCat.I.{u}, E)) :
    endpointCorrection γ (γ 0) (γ 1) = γ := by
  apply ContinuousMap.ext
  intro s
  rw [endpointCorrection_apply]
  simp only [sub_self, smul_zero, add_zero]

/-- Let E be a real module with a topological additive group and continuous
real scalar multiplication, and I the lifted closed unit interval.
For γ : C(I,E), endpointCorrection γ (γ 0) (γ 1) = γ. -/
theorem endpointCorrection_self (γ : C(TopCat.I.{u}, E)) :
    endpointCorrection γ (γ 0) (γ 1) = γ := endpointCorrectionSelfComputed γ

/-- Let E be a real module with a topological additive group and continuous
real scalar multiplication, and I the lifted closed unit interval.
For γ : C(I,E), a,b : E with γ(0)=a and γ(1)=b,
endpointCorrection γ a b = γ. -/
theorem endpointCorrection_eq_self (γ : C(TopCat.I.{u}, E)) (a b : E)
    (h₀ : γ 0 = a) (h₁ : γ 1 = b) : endpointCorrection γ a b = γ := by
  rw [← h₀, ← h₁]
  exact endpointCorrection_self γ

/-- Let E be a real module with a topological additive group and continuous
real scalar multiplication, and I the lifted closed unit interval.
The map (γ,a,b) ↦ endpointCorrection γ a b from C(I,E) × E × E to C(I,E)
is continuous when the continuous-map spaces have the compact-open topology. -/
private theorem endpointCorrectionContinuous :
    Continuous (fun p : C(TopCat.I.{u}, E) × E × E =>
      endpointCorrection p.1 p.2.1 p.2.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun z : (C(TopCat.I.{u}, E) × E × E) × TopCat.I.{u} =>
    z.1.1 z.2 +
      (1 - (TopCat.I.homeomorph z.2 : ℝ)) • (z.1.2.1 - z.1.1 0) +
      (TopCat.I.homeomorph z.2 : ℝ) • (z.1.2.2 - z.1.1 1))
  have ht : Continuous (fun z : (C(TopCat.I.{u}, E) × E × E) × TopCat.I.{u} =>
      (TopCat.I.homeomorph z.2 : ℝ)) :=
    (TopCat.I.homeomorph.continuous.comp continuous_snd).subtype_val
  have hγ : Continuous (fun z : (C(TopCat.I.{u}, E) × E × E) × TopCat.I.{u} =>
      z.1.1 z.2) := continuous_fst.fst.eval continuous_snd
  have h₀ : Continuous (fun z : (C(TopCat.I.{u}, E) × E × E) × TopCat.I.{u} =>
      z.1.1 (0 : TopCat.I.{u})) := (continuous_eval_const _).comp continuous_fst.fst
  have h₁ : Continuous (fun z : (C(TopCat.I.{u}, E) × E × E) × TopCat.I.{u} =>
      z.1.1 (1 : TopCat.I.{u})) := (continuous_eval_const _).comp continuous_fst.fst
  have ha : Continuous (fun z : (C(TopCat.I.{u}, E) × E × E) × TopCat.I.{u} =>
      z.1.2.1) := continuous_fst.snd.fst
  have hb : Continuous (fun z : (C(TopCat.I.{u}, E) × E × E) × TopCat.I.{u} =>
      z.1.2.2) := continuous_fst.snd.snd
  exact (hγ.add ((continuous_const.sub ht).smul (ha.sub h₀))).add (ht.smul (hb.sub h₁))

/-- Let E be a real module with a topological additive group and continuous
real scalar multiplication, and I the lifted closed unit interval.
The map (γ,a,b) ↦ endpointCorrection γ a b from C(I,E) × E × E to C(I,E)
is jointly continuous for the compact-open topology. -/
theorem continuous_endpointCorrection :
    Continuous (fun p : C(TopCat.I.{u}, E) × E × E =>
      endpointCorrection p.1 p.2.1 p.2.2) := endpointCorrectionContinuous

end ContinuousMap
