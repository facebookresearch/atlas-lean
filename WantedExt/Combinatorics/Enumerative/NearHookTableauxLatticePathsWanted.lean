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

/-- **The near-hook diagram $\theta^{(n)}$.** For $n \in \mathbb{N}$, $\theta^{(n)}$ is the Young
diagram of the near-hook partition $(n + 2, 2, 1^n)$ of $2n + 4$: its rows have lengths $n + 2$
and $2$, followed by $n$ rows of length $1$.

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

/-- **Row lengths of $\theta^{(n)}$.** For every $n \in \mathbb{N}$, the row lengths of the Young
diagram $\theta^{(n)}$, from the top row down, are $n + 2$, $2$, and then $1$ repeated $n$ times.

Source: L. Ayres et al., *An Exceptional Equinumerosity of Lattice Paths and Young Tableaux*,
Journal of Integer Sequences 28 (2025), Article 25.5.2, Section 2. -/
theorem nearHookTheta_rowLens (n : ℕ) :
    (nearHookTheta n).rowLens = [n + 2, 2] ++ List.replicate n 1 := by
  refine YoungDiagram.rowLens_ofRowLens_eq_self ?_
  simp only [List.cons_append, List.mem_cons, List.nil_append, List.mem_replicate]
  rintro x (rfl | rfl | ⟨-, rfl⟩) <;> omega

/-- **First-quadrant paths $\mathcal{P}_n$.** For $n \in \mathbb{N}$, $\mathcal{P}_n$ is the set of
words $(s_1, \dots, s_{2n+2})$ of $2n + 2$ steps, each one of $N = (0, 1)$, $S = (0, -1)$,
$E = (1, 0)$ and $W = (-1, 0)$ in $\mathbb{Z}^2$, such that every partial sum $s_1 + \dots + s_k$
with $0 \le k \le 2n + 2$ has both coordinates nonnegative and the total $s_1 + \dots + s_{2n+2}$
equals $(n, n)$.

These are the walks of Guy, Krattenthaler and Sagan.

Source: L. Ayres et al., *An Exceptional Equinumerosity of Lattice Paths and Young Tableaux*,
Journal of Integer Sequences 28 (2025), Article 25.5.2, Section 1. -/
def firstQuadrantPaths (n : ℕ) : Set (List (ℤ × ℤ)) :=
  {w | w.length = 2 * n + 2 ∧ (∀ s ∈ w, s = (0, 1) ∨ s = (0, -1) ∨ s = (1, 0) ∨ s = (-1, 0)) ∧
    (∀ k, 0 ≤ (w.take k).sum.1 ∧ 0 ≤ (w.take k).sum.2) ∧ w.sum = ((n : ℤ), (n : ℤ))}

/-- **The path $NS$ lies in $\mathcal{P}_0$.** The two-step word consisting of a north step
$(0, 1)$ followed by a south step $(0, -1)$ belongs to the set $\mathcal{P}_0$ of first-quadrant
paths.

Source: L. Ayres et al., *An Exceptional Equinumerosity of Lattice Paths and Young Tableaux*,
Journal of Integer Sequences 28 (2025), Article 25.5.2, Section 1. -/
theorem north_south_mem_firstQuadrantPaths_zero :
    [((0 : ℤ), (1 : ℤ)), (0, -1)] ∈ firstQuadrantPaths 0 := by
  refine ⟨rfl, by simp, fun k => ?_, by simp⟩
  rcases k with _ | _ | k <;> simp

/-- **The map $\psi$ from near-hook tableaux to lattice paths.** Let $n \in \mathbb{N}$ and let
$T$ be a semistandard Young tableau of shape $\theta^{(n)}$, with rows and columns numbered from
$0$; call row $0$ of $\theta^{(n)}$ the arm and column $0$ the leg. Then $\psi(T)$ is the word
$(s_1, \dots, s_{2n+2})$ of steps in $\mathbb{Z}^2$ in which $s_i$ is $E = (1, 0)$ if $i + 2$ is an
entry of $T$ in the arm; otherwise $s_i$ is $N = (0, 1)$ if $i + 2$ is an entry of $T$ in the leg;
otherwise $s_i$ is $S = (0, -1)$ if $2$ is an entry of $T$ in the arm, and $W = (-1, 0)$ if not.

For a standard Young tableau, the last two cases are those where $i + 2$ is the entry of the
heart, the cell in row $1$ and column $1$, and $2$ is then an entry of the arm or of the leg.

Source: L. Ayres et al., *An Exceptional Equinumerosity of Lattice Paths and Young Tableaux*,
Journal of Integer Sequences 28 (2025), Article 25.5.2, Section 3, equation (eq:psi). -/
def nearHookTableauToPathPsi (n : ℕ) (T : SemistandardYoungTableau (nearHookTheta n)) :
    List (ℤ × ℤ) :=
  (List.range (2 * n + 2)).map fun k =>
    if ∃ j < n + 2, T 0 j = k + 3 then (1, 0)
    else if ∃ i < n + 2, T i 0 = k + 3 then (0, 1)
    else if ∃ j < n + 2, T 0 j = 2 then (0, -1) else (-1, 0)

/-- **The path $\psi(T)$ has $2n + 2$ steps.** For every $n \in \mathbb{N}$ and every
semistandard Young tableau $T$ of shape $\theta^{(n)}$, the word $\psi(T)$ has length $2n + 2$.

Source: L. Ayres et al., *An Exceptional Equinumerosity of Lattice Paths and Young Tableaux*,
Journal of Integer Sequences 28 (2025), Article 25.5.2, Section 3, equation (eq:psi). -/
theorem length_nearHookTableauToPathPsi (n : ℕ) (T : SemistandardYoungTableau (nearHookTheta n)) :
    (nearHookTableauToPathPsi n T).length = 2 * n + 2 := by
  simp [nearHookTableauToPathPsi]

/-- **The map $\xi$ from near-hook tableaux to lattice paths.** Let $n \in \mathbb{N}$ and let
$T$ be a semistandard Young tableau of shape $\theta^{(n)}$, with rows and columns numbered from
$0$; call row $0$ of $\theta^{(n)}$ the arm and the cell in row $1$ and column $1$ the heart, and
let $H$ be the entry of $T$ in the heart. Then $\xi(T)$ is the word $(s_1, \dots, s_{2n+2})$ of
steps in $\mathbb{Z}^2$ given as follows, where $E = (1, 0)$, $N = (0, 1)$, $S = (0, -1)$ and
$W = (-1, 0)$. If $i + 2 < H$, then $s_i$ is $E$ if $i + 1$ is an entry of $T$ in the arm and
$N$ otherwise. If $i + 2 = H$, then $s_i$ is $S$ if $i + 1$ is an entry of $T$ in the arm and
$W$ otherwise. If $i + 2 > H$, then $s_i$ is $E$ if $i + 2$ is an entry of $T$ in the arm and
$N$ otherwise.

For a standard Young tableau the inspected value is never $1$ or $H$, so it lies in exactly one
of the arm and the leg, column $0$; "otherwise" then means that it lies in the leg.

Source: L. Ayres et al., *An Exceptional Equinumerosity of Lattice Paths and Young Tableaux*,
Journal of Integer Sequences 28 (2025), Article 25.5.2, Section 4.1, equation (eq:xi). -/
def nearHookTableauToPathXi (n : ℕ) (T : SemistandardYoungTableau (nearHookTheta n)) :
    List (ℤ × ℤ) :=
  (List.range (2 * n + 2)).map fun k =>
    if k + 3 < T 1 1 then (if ∃ j < n + 2, T 0 j = k + 2 then (1, 0) else (0, 1))
    else if k + 3 = T 1 1 then (if ∃ j < n + 2, T 0 j = k + 2 then (0, -1) else (-1, 0))
    else if ∃ j < n + 2, T 0 j = k + 3 then (1, 0) else (0, 1)

/-- **The path $\xi(T)$ has $2n + 2$ steps.** For every $n \in \mathbb{N}$ and every
semistandard Young tableau $T$ of shape $\theta^{(n)}$, the word $\xi(T)$ has length $2n + 2$.

Source: L. Ayres et al., *An Exceptional Equinumerosity of Lattice Paths and Young Tableaux*,
Journal of Integer Sequences 28 (2025), Article 25.5.2, Section 4.1, equation (eq:xi). -/
theorem length_nearHookTableauToPathXi (n : ℕ) (T : SemistandardYoungTableau (nearHookTheta n)) :
    (nearHookTableauToPathXi n T).length = 2 * n + 2 := by
  simp [nearHookTableauToPathXi]

/-- **The map $\psi$ is a bijection from near-hook tableaux to first-quadrant paths.** For every
$n \in \mathbb{N}$, the map $\psi$ restricts to a bijection from the standard Young tableaux of
shape $\theta^{(n)}$ onto the set $\mathcal{P}_n$ of first-quadrant paths. Here a standard Young
tableau of shape $\theta^{(n)}$ is a semistandard Young tableau of that shape whose entries map
the $2n + 4$ cells of $\theta^{(n)}$ bijectively onto $\{1, \dots, 2n + 4\}$.

Source: Liam Ayres, Evan Bialo, Alwin Chen, Aidan Cook, Matteus Froese, Erica Liu, Maryam Mohammadi
Yekta, Oliver Pechenik and Benjamin Wong, *An Exceptional Equinumerosity of Lattice Paths and Young
Tableaux*, Journal of Integer Sequences 28 (2025), Article 25.5.2, Theorem 2
(`jis-2025-25.5.2-thm-2`). -/
public theorem_wanted bijOn_nearHookTableauToPathPsi (n : ℕ) :
    Set.BijOn (nearHookTableauToPathPsi n)
      {T | Set.BijOn (fun c : ℕ × ℕ => T c.1 c.2) (nearHookTheta n).cells
        (Set.Icc 1 (2 * n + 4))}
      (firstQuadrantPaths n)

/-- **The map $\xi$ is a bijection from near-hook tableaux to first-quadrant paths.** For every
$n \in \mathbb{N}$, the map $\xi$ restricts to a bijection from the standard Young tableaux of
shape $\theta^{(n)}$ onto the set $\mathcal{P}_n$ of first-quadrant paths. Here a standard Young
tableau of shape $\theta^{(n)}$ is a semistandard Young tableau of that shape whose entries map
the $2n + 4$ cells of $\theta^{(n)}$ bijectively onto $\{1, \dots, 2n + 4\}$.

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
