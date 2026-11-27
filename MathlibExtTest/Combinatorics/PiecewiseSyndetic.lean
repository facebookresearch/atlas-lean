/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fin.VecNotation
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

-- One bound `A` serves every red/blue coloring of `ℕ^t`: the red set or its complement is
-- `d`-dense in a subcube of `[1, A]^t` whose side exceeds `f d`.
example (t : ℕ) (f : ℕ → ℕ) : ∃ A : ℕ, ∀ red : Set (Fin t → ℕ), ∃ d m : ℕ, 1 ≤ d ∧ f d < m ∧
    ∃ a : Fin t → ℕ, latticeCube a m ⊆ latticeCube (fun _ => 1) A ∧
      (IsDenseInCubes d red (latticeCube a m) ∨ IsDenseInCubes d redᶜ (latticeCube a m)) := by
  classical
  obtain ⟨A, hA⟩ := exists_cube_bound_isDenseInCubes 2 t f
  refine ⟨A, fun red => ?_⟩
  obtain ⟨d, m, hd, hm, j, a, hsub, hdense⟩ := hA fun x => if x ∈ red then 0 else 1
  refine ⟨d, m, hd, hm, a, hsub, ?_⟩
  rcases j with ⟨_ | _ | j, hj⟩
  · exact Or.inl (by simpa using hdense)
  · exact Or.inr (by simpa [Set.compl_def] using hdense)
  · omega

-- In positive dimension, with at least one color, the subcube really lies in `[1, A]^t`: its
-- side is at most `A`, so a bound for the constant function `k` exceeds `k`.
example (r t k : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) :
    ∃ A : ℕ, k < A ∧ ∀ c : (Fin t → ℕ) → Fin r, ∃ d m : ℕ, 1 ≤ d ∧ k < m ∧ ∃ j : Fin r,
      ∃ a : Fin t → ℕ, latticeCube a m ⊆ latticeCube (fun _ => 1) A ∧
        IsDenseInCubes d {x | c x = j} (latticeCube a m) := by
  obtain ⟨A, hA⟩ := exists_cube_bound_isDenseInCubes r t fun _ => k
  refine ⟨A, ?_, hA⟩
  obtain ⟨d, m, -, hkm, -, a, hsub, -⟩ := hA fun _ => ⟨0, hr⟩
  have hnear := mem_latticeCube.mp (hsub (mem_latticeCube.mpr fun i => ⟨le_rfl, by omega⟩))
    ⟨0, ht⟩
  have hfar := mem_latticeCube.mp (hsub ((mem_latticeCube (x := fun i => a i + (m - 1))).mpr
    fun i => ⟨by omega, by omega⟩)) ⟨0, ht⟩
  omega

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

-- Partition regularity in Ramsey form: when the points of a piecewise syndetic set get `r`
-- colors, some color class is piecewise syndetic.
example (t r : ℕ) (A : Set (Fin t → ℕ)) (hA : IsPiecewiseSyndetic A)
    (c : (Fin t → ℕ) → Fin r) : ∃ j, IsPiecewiseSyndetic {x ∈ A | c x = j} :=
  hA.exists_of_eq_iUnion (fun j => {x ∈ A | c x = j}) (by ext x; simp)

-- For a red/blue coloring of `ℕ^t`, the red set or its complement is piecewise syndetic.
example (t : ℕ) (red : Set (Fin t → ℕ)) :
    IsPiecewiseSyndetic red ∨ IsPiecewiseSyndetic redᶜ := by
  simpa using isPiecewiseSyndetic_univ.exists_of_eq_iUnion ![red, redᶜ]
    (by ext x; by_cases hx : x ∈ red <;> simp [hx])

-- The sets that are not piecewise syndetic are closed under binary unions.
example (t : ℕ) (B C : Set (Fin t → ℕ)) (hB : ¬ IsPiecewiseSyndetic B)
    (hC : ¬ IsPiecewiseSyndetic C) : ¬ IsPiecewiseSyndetic (B ∪ C) := fun h => by
  simpa [hB, hC] using h.exists_of_eq_iUnion ![B, C] (by ext x; simp)

-- With no pieces the union is empty, so it is never a piecewise syndetic set.
example (t : ℕ) (A : Set (Fin t → ℕ)) (hA : IsPiecewiseSyndetic A)
    (B : Fin 0 → Set (Fin t → ℕ)) : A ≠ ⋃ i, B i := fun hAB =>
  (hA.exists_of_eq_iUnion B hAB).elim fun i _ => i.elim0
