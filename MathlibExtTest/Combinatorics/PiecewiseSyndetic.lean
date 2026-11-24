/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.PiecewiseSyndetic

open MetaMathlibExt

-- With two colors and sides 1, 2, 3, density for the first color means a monochromatic pair
-- in dimension one. The second color only has to meet each pair inside its interval.
example (a : Fin 1 → ℕ) (red : Set (Fin 1 → ℕ)) :
    (∃ b, latticeCube b 2 ⊆ latticeCube a 3 ∧ latticeCube b 2 ⊆ red) ∨
    ∃ b, latticeCube b 3 ⊆ latticeCube a 3 ∧ IsDenseInCubes 2 redᶜ (latticeCube b 3) := by
  classical
  let c (x : Fin 1 → ℕ) : ℕ := if x ∈ red then 1 else 2
  have hc (x) (_ : x ∈ latticeCube a 3) : c x ∈ Set.Icc 1 2 := by
    by_cases hx : x ∈ red <;> simp [c, hx]
  obtain ⟨i, ⟨hlo, hhi⟩, b, hsub, hd⟩ :=
    exists_subcube_isDenseInCubes_colorClass 1 Nat.succ rfl (fun _ _ => Nat.succ_lt_succ) 2 a c hc
  have hi : i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl
  · refine Or.inl ⟨b, hsub, ?_⟩
    simpa [c] using (isDenseInCubes_one_iff.mp hd)
  · refine Or.inr ⟨b, hsub, ?_⟩
    simpa [c, Set.compl_def] using hd

-- The empty product contains its unique point for every side length, including zero.
example (a : Fin 0 → ℕ) (d m : ℕ) : IsDenseInCubes d {a} (latticeCube a m) := by
  intro b _
  exact ⟨a, mem_latticeCube.mpr (fun i => i.elim0), rfl⟩

-- In dimension zero a singleton is the whole space and hence piecewise syndetic.
example (a : Fin 0 → ℕ) : IsPiecewiseSyndetic {a} := by
  have ha : ({a} : Set (Fin 0 → ℕ)) = Set.univ := Set.eq_univ_of_forall fun x =>
    Subsingleton.elim x a
  rw [ha]
  exact isPiecewiseSyndetic_univ

-- In that dimension even a side-zero cube is nonempty. No gap size witnesses the empty set.
example : cubeGapSize (∅ : Set (Fin 0 → ℕ)) = 0 := by
  unfold cubeGapSize
  refine (congrArg sInf ?_).trans Nat.sInf_empty
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro d ⟨_, a, m, _, hd⟩
  have hsub : latticeCube a d ⊆ latticeCube a m := fun _ _ =>
    mem_latticeCube.mpr fun i => i.elim0
  obtain ⟨x, _, hx⟩ := hd a hsub
  exact hx
