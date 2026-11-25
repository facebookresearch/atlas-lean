/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.ProjIcc

/-!
# Box projection for rate dynamics

The coordinatewise projection onto a product box applies Mathlib's canonical interval projection `Set.projIcc` in each coordinate. The projected state lies in the box by construction, and the projection is idempotent.
-/

@[expose] public section

namespace MathlibExt.Biology.Biophysics.NeuralPopulation.BoxFlow

/-- The coordinatewise projection onto the product box
`[0, U] x [0, U]`, applying the canonical interval projection in
each coordinate. -/
noncomputable def boxProj (U : ℝ) (hU : 0 ≤ U) (x : Fin 2 → ℝ) :
    Set.Icc (0 : Fin 2 → ℝ) (fun _ => U) :=
  ⟨fun i => ((Set.projIcc 0 U hU (x i) : Set.Icc (0:ℝ) U) : ℝ),
    Set.mem_Icc.mpr ⟨fun i => (Set.projIcc 0 U hU (x i)).2.1,
      fun i => (Set.projIcc 0 U hU (x i)).2.2⟩⟩

/-- Each projected coordinate is the canonical interval
projection of the original coordinate. -/
lemma boxProj_apply (U : ℝ) (hU : 0 ≤ U) (x : Fin 2 → ℝ) (i : Fin 2) :
    ((boxProj U hU x : Set.Icc (0 : Fin 2 → ℝ) (fun _ => U)) : Fin 2 → ℝ) i =
      max 0 (min U (x i)) := by
  show ((Set.projIcc 0 U hU (x i) : Set.Icc (0:ℝ) U) : ℝ) = max 0 (min U (x i))
  exact Set.coe_projIcc 0 U hU (x i)

/-- **The box projection is idempotent.** Projecting a projected
state changes nothing. -/
lemma boxProj_idempotent (U : ℝ) (hU : 0 ≤ U) (x : Fin 2 → ℝ) :
    boxProj U hU ((boxProj U hU x : Set.Icc (0 : Fin 2 → ℝ) (fun _ => U)) : Fin 2 → ℝ) =
      boxProj U hU x := by
  apply Subtype.ext
  funext i
  show ((Set.projIcc 0 U hU (((boxProj U hU x : Set.Icc (0 : Fin 2 → ℝ) (fun _ => U)) : Fin 2 → ℝ) i) : Set.Icc (0:ℝ) U) : ℝ) =
    ((Set.projIcc 0 U hU (x i) : Set.Icc (0:ℝ) U) : ℝ)
  have hmem : ((boxProj U hU x : Set.Icc (0 : Fin 2 → ℝ) (fun _ => U)) : Fin 2 → ℝ) i ∈
      Set.Icc (0:ℝ) U :=
    Set.mem_Icc.mpr ⟨(Set.mem_Icc.mp (boxProj U hU x).2).1 i,
      (Set.mem_Icc.mp (boxProj U hU x).2).2 i⟩
  have h := Set.projIcc_of_mem hU hmem
  have h2 : ((Set.projIcc 0 U hU
      (((boxProj U hU x : Set.Icc (0 : Fin 2 → ℝ) (fun _ => U)) : Fin 2 → ℝ) i) :
        Set.Icc (0:ℝ) U) : ℝ) =
      ((boxProj U hU x : Set.Icc (0 : Fin 2 → ℝ) (fun _ => U)) : Fin 2 → ℝ) i :=
    congrArg Subtype.val h
  rw [h2, boxProj_apply]
  exact (Set.coe_projIcc 0 U hU (x i)).symm

/-- **The box projection is the identity on the box.** For a
state already in the box, projecting changes nothing. -/
lemma boxProj_of_mem (U : ℝ) (hU : 0 ≤ U) {x : Fin 2 → ℝ}
    (hx : x ∈ Set.Icc (0 : Fin 2 → ℝ) (fun _ => U)) :
    ((boxProj U hU x : Set.Icc (0 : Fin 2 → ℝ) (fun _ => U)) : Fin 2 → ℝ) = x := by
  funext i
  show ((Set.projIcc 0 U hU (x i) : Set.Icc (0:ℝ) U) : ℝ) = x i
  have hmem : x i ∈ Set.Icc (0:ℝ) U :=
    Set.mem_Icc.mpr ⟨(Set.mem_Icc.mp hx).1 i, (Set.mem_Icc.mp hx).2 i⟩
  exact congrArg Subtype.val (Set.projIcc_of_mem hU hmem)


end MathlibExt.Biology.Biophysics.NeuralPopulation.BoxFlow
