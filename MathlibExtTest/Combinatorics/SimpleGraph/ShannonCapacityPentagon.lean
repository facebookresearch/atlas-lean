/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.ShannonCapacityPentagon

open MathlibExt.Combinatorics.ShannonCapacityPentagonWanted.Combinatorics.ShannonCapacityPentagon
open Filter

-- All empty words coincide, so the zeroth power has no edges.
example {V : Type*} (G : SimpleGraph V) : strongPower G 0 = ⊥ := by
  ext x y
  have h : x = y := funext fun i => i.elim0
  simp [strongPower, h]

-- Equal coordinates are allowed, and the pentagon wraps from vertex 0 to vertex 4.
example : (strongPower (SimpleGraph.cycleGraph 5) 2).Adj
    (fun _ => 0) (fun i => if i = 0 then 0 else 4) := by
  refine ⟨?_, fun i => ?_⟩
  · intro h
    exact (by decide : (0 : Fin 5) ≠ 4) (congrFun h 1)
  · fin_cases i <;> decide

-- One distinct nonadjacent coordinate prevents a strong-power edge.
example : ¬ (strongPower (SimpleGraph.cycleGraph 5) 2).Adj
    (fun _ => 0) (fun i => if i = 0 then 0 else 2) := by
  intro h
  exact (by decide : ¬ ((0 : Fin 5) = 2 ∨ (SimpleGraph.cycleGraph 5).Adj 0 2)) (h.2 1)

-- A one-vertex alphabet has exactly one word at every positive length.
example : HasShannonCapacity (⊥ : SimpleGraph (Fin 1)) 1 := by
  have h (k : ℕ) : (strongPower (⊥ : SimpleGraph (Fin 1)) k).indepNum = 1 := by
    have hbot : strongPower (⊥ : SimpleGraph (Fin 1)) k = ⊥ := by
      ext x y
      have hxy : x = y := Subsingleton.elim _ _
      simp [strongPower, hxy]
    rw [hbot, ← SimpleGraph.cliqueNum_compl, compl_bot, SimpleGraph.cliqueNum_top]
    simp
  change Tendsto (fun k : ℕ =>
    ((strongPower (⊥ : SimpleGraph (Fin 1)) (k + 1)).indepNum : ℝ) ^
      (((k : ℝ) + 1)⁻¹)) atTop (nhds 1)
  simp only [h, Nat.cast_one, Real.one_rpow]
  exact tendsto_const_nhds
