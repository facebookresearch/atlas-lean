/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Young.SemistandardTableau

/-!
# Near-hook tableaux and first-quadrant lattice paths

Statements from Liam Ayres, Evan Bialo, Alwin Chen, Aidan Cook, Matteus Froese, Erica Liu, Maryam
Mohammadi Yekta, Oliver Pechenik and Benjamin Wong, *An Exceptional Equinumerosity of Lattice Paths
and Young Tableaux*, Journal of Integer Sequences 28 (2025), Article 25.5.2 (arXiv `2506.03116`,
TeX source read).

`nearHookTheta n` is the Young diagram of `θ^(n) = (n + 2, 2, 1^n)`. A standard Young tableau of
shape `θ^(n)` is a Mathlib `SemistandardYoungTableau` whose entries map the `2n + 4` cells
bijectively onto `{1, …, 2n + 4}`. The arm is row `0`, the leg is column `0` and the heart is the
cell `(1, 1)`. A lattice path is its word of unit steps `N = (0, 1)`, `S = (0, -1)`,
`E = (1, 0)`, `W = (-1, 0)` in `ℤ × ℤ`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- The Young diagram of the near-hook partition `θ^(n) = (n + 2, 2, 1^n)` of `2n + 4`.

Source: L. Ayres et al., *An Exceptional Equinumerosity of Lattice Paths and Young Tableaux*,
Journal of Integer Sequences 28 (2025), Article 25.5.2, Section 2. -/
def nearHookTheta (n : ℕ) : YoungDiagram :=
  YoungDiagram.ofRowLens ([n + 2, 2] ++ List.replicate n 1) <| by
    rw [List.sortedGE_iff_pairwise]
    simp only [List.cons_append, List.pairwise_cons, List.nil_append, List.mem_cons,
      List.mem_replicate, List.pairwise_replicate]
    refine ⟨?_, ?_, ?_⟩
    · rintro a (rfl | ⟨-, rfl⟩) <;> omega
    · rintro a ⟨-, rfl⟩; omega
    · simp

/-- The row lengths of `θ^(n)` are `n + 2, 2, 1, …, 1` (`n` ones).

Source: L. Ayres et al., *An Exceptional Equinumerosity of Lattice Paths and Young Tableaux*,
Journal of Integer Sequences 28 (2025), Article 25.5.2, Section 2. -/
theorem nearHookTheta_rowLens (n : ℕ) :
    (nearHookTheta n).rowLens = [n + 2, 2] ++ List.replicate n 1 := by
  refine YoungDiagram.rowLens_ofRowLens_eq_self ?_
  simp only [List.cons_append, List.mem_cons, List.nil_append, List.mem_replicate]
  rintro x (rfl | rfl | ⟨-, rfl⟩) <;> omega

/-- The set `𝒫_n` of Guy, Krattenthaler and Sagan: words of `2n + 2` steps from
`{N, S, E, W}` whose partial sums stay in the closed first quadrant and whose total is `(n, n)`.

Source: L. Ayres et al., *An Exceptional Equinumerosity of Lattice Paths and Young Tableaux*,
Journal of Integer Sequences 28 (2025), Article 25.5.2, Section 1. -/
def firstQuadrantPaths (n : ℕ) : Set (List (ℤ × ℤ)) :=
  {w | w.length = 2 * n + 2 ∧ (∀ s ∈ w, s = (0, 1) ∨ s = (0, -1) ∨ s = (1, 0) ∨ s = (-1, 0)) ∧
    (∀ k, 0 ≤ (w.take k).sum.1 ∧ 0 ≤ (w.take k).sum.2) ∧ w.sum = ((n : ℤ), (n : ℤ))}

/-- `NS ∈ 𝒫_0`.

Source: L. Ayres et al., *An Exceptional Equinumerosity of Lattice Paths and Young Tableaux*,
Journal of Integer Sequences 28 (2025), Article 25.5.2, Section 1. -/
theorem north_south_mem_firstQuadrantPaths_zero :
    [((0 : ℤ), (1 : ℤ)), (0, -1)] ∈ firstQuadrantPaths 0 := by
  refine ⟨rfl, by simp, fun k => ?_, by simp⟩
  rcases k with _ | _ | k <;> simp

/-- The bijection `ψ` of equation (eq:psi): for `1 ≤ i ≤ 2n + 2` the `i`-th step is `E` if `i + 2`
lies in the arm, `N` if it lies in the leg, and otherwise (`i + 2` in the heart) `S` if `2` lies in
the arm and `W` if it lies in the leg. List index `k` is `i - 1`.

Source: L. Ayres et al., *An Exceptional Equinumerosity of Lattice Paths and Young Tableaux*,
Journal of Integer Sequences 28 (2025), Article 25.5.2, Section 3, equation (eq:psi). -/
def nearHookTableauToPathPsi (n : ℕ) (T : SemistandardYoungTableau (nearHookTheta n)) :
    List (ℤ × ℤ) :=
  (List.range (2 * n + 2)).map fun k =>
    if ∃ j < n + 2, T 0 j = k + 3 then (1, 0)
    else if ∃ i < n + 2, T i 0 = k + 3 then (0, 1)
    else if ∃ j < n + 2, T 0 j = 2 then (0, -1) else (-1, 0)

/-- `ψ(T)` has `2n + 2` steps.

Source: L. Ayres et al., *An Exceptional Equinumerosity of Lattice Paths and Young Tableaux*,
Journal of Integer Sequences 28 (2025), Article 25.5.2, Section 3, equation (eq:psi). -/
theorem length_nearHookTableauToPathPsi (n : ℕ) (T : SemistandardYoungTableau (nearHookTheta n)) :
    (nearHookTableauToPathPsi n T).length = 2 * n + 2 := by
  simp [nearHookTableauToPathPsi]

/-- The map `ξ` of equation (eq:xi), with `H` the heart entry: for `1 ≤ i ≤ 2n + 2`, if
`i + 2 < H` the step is `E` or `N` as `i + 1` lies in the arm or the leg; if `i + 2 = H` it is `S`
or `W` as `i + 1` lies in the arm or the leg; if `i + 2 > H` it is `E` or `N` as `i + 2` lies in the
arm or the leg. For a standard tableau the inspected value is never the heart, so "not in the arm"
is "in the leg". List index `k` is `i - 1`.

Source: L. Ayres et al., *An Exceptional Equinumerosity of Lattice Paths and Young Tableaux*,
Journal of Integer Sequences 28 (2025), Article 25.5.2, Section 4.1, equation (eq:xi). -/
def nearHookTableauToPathXi (n : ℕ) (T : SemistandardYoungTableau (nearHookTheta n)) :
    List (ℤ × ℤ) :=
  (List.range (2 * n + 2)).map fun k =>
    if k + 3 < T 1 1 then (if ∃ j < n + 2, T 0 j = k + 2 then (1, 0) else (0, 1))
    else if k + 3 = T 1 1 then (if ∃ j < n + 2, T 0 j = k + 2 then (0, -1) else (-1, 0))
    else if ∃ j < n + 2, T 0 j = k + 3 then (1, 0) else (0, 1)

/-- `ξ(T)` has `2n + 2` steps.

Source: L. Ayres et al., *An Exceptional Equinumerosity of Lattice Paths and Young Tableaux*,
Journal of Integer Sequences 28 (2025), Article 25.5.2, Section 4.1, equation (eq:xi). -/
theorem length_nearHookTableauToPathXi (n : ℕ) (T : SemistandardYoungTableau (nearHookTheta n)) :
    (nearHookTableauToPathXi n T).length = 2 * n + 2 := by
  simp [nearHookTableauToPathXi]

/-- `ψ` is a bijection from the standard Young tableaux of shape `θ^(n)` onto `𝒫_n`.

Source: Liam Ayres, Evan Bialo, Alwin Chen, Aidan Cook, Matteus Froese, Erica Liu, Maryam Mohammadi
Yekta, Oliver Pechenik and Benjamin Wong, *An Exceptional Equinumerosity of Lattice Paths and Young
Tableaux*, Journal of Integer Sequences 28 (2025), Article 25.5.2, Theorem 2
(`jis-2025-25.5.2-thm-2`). -/
public theorem_wanted bijOn_nearHookTableauToPathPsi (n : ℕ) :
    Set.BijOn (nearHookTableauToPathPsi n)
      {T | Set.BijOn (fun c : ℕ × ℕ => T c.1 c.2) (nearHookTheta n).cells
        (Set.Icc 1 (2 * n + 4))}
      (firstQuadrantPaths n)

/-- `ξ` is a bijection from the standard Young tableaux of shape `θ^(n)` onto `𝒫_n`.

Source: Liam Ayres, Evan Bialo, Alwin Chen, Aidan Cook, Matteus Froese, Erica Liu, Maryam Mohammadi
Yekta, Oliver Pechenik and Benjamin Wong, *An Exceptional Equinumerosity of Lattice Paths and Young
Tableaux*, Journal of Integer Sequences 28 (2025), Article 25.5.2, Proposition 3
(`jis-2025-25.5.2-prop-3`). -/
public theorem_wanted bijOn_nearHookTableauToPathXi (n : ℕ) :
    Set.BijOn (nearHookTableauToPathXi n)
      {T | Set.BijOn (fun c : ℕ × ℕ => T c.1 c.2) (nearHookTheta n).cells
        (Set.Icc 1 (2 * n + 4))}
      (firstQuadrantPaths n)

end

end MetaMathlibExt
