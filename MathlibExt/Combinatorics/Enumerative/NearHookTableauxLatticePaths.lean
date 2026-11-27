/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Combinatorics.Young.SemistandardTableau

/-!
# Near-hook tableaux and first-quadrant lattice paths

We prove that the map $\xi$ is a bijection between standard near-hook tableaux and
first-quadrant paths, following Liam Ayres, Evan Bialo, Alwin Chen, Aidan Cook, Matteus Froese,
Erica Liu, Maryam Mohammadi Yekta, Oliver Pechenik and Benjamin Wong, *An Exceptional
Equinumerosity of Lattice Paths and Young Tableaux*, Journal of Integer Sequences 28 (2025),
Article 25.5.2 (arXiv `2506.03116`).

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

namespace bijOn_nearHookTableauToPathXi

private abbrev Steps := List (ℤ × ℤ)

-- A position in the word belongs to the arm if its step is east or south.
-- At a backward step both coordinates lose one relative to an east or north step.
private def word (m : ℕ) (A D : Finset ℕ) : Steps :=
  (List.range m).map fun k =>
    ((if k ∈ A then 1 else 0) - (if k ∈ D then 1 else 0),
     (if k ∈ A then 0 else 1) - (if k ∈ D then 1 else 0))

private def countBefore (A : Finset ℕ) (k : ℕ) := (Finset.range k ∩ A).card

private lemma countBefore_succ (A : Finset ℕ) (k : ℕ) :
    countBefore A (k + 1) = countBefore A k + if k ∈ A then 1 else 0 := by
  by_cases hk : k ∈ A <;> simp [countBefore, Finset.range_add_one, Finset.insert_inter_of_mem,
    Finset.insert_inter_of_notMem, hk, Finset.card_insert_of_notMem]

private lemma word_sum (m : ℕ) (A D : Finset ℕ) :
    (word m A D).sum =
      ((countBefore A m : ℤ) - countBefore D m, m - (countBefore A m : ℤ) - countBefore D m) := by
  induction m with
  | zero => simp [word, countBefore, Prod.ext_iff]
  | succ m ih =>
    simp only [word, List.range_succ, List.map_append, List.map_singleton, List.sum_append,
      List.sum_singleton] at ih ⊢
    rw [ih]
    by_cases ha : m ∈ A <;> by_cases hd : m ∈ D <;>
      simp [countBefore_succ, ha, hd, Prod.ext_iff] <;> omega

private lemma take_word (m k : ℕ) (A D : Finset ℕ) :
    (word m A D).take k = word (min k m) A D := by
  simp only [word, ← List.map_take, List.take_range]

private structure Code where
  heart : ℕ  -- zero-based position of the backward step
  arm : Finset ℕ

private def Code.leg (c : Code) (n : ℕ) := Finset.range (2 * n + 2) \ c.arm

private structure Good (n : ℕ) (c : Code) : Prop where
  heart_lt : c.heart < 2 * n + 2
  arm_sub : c.arm ⊆ Finset.range (2 * n + 2)
  arm_card : c.arm.card = n + 1
  leg_card : (c.leg n).card = n + 1
  arm_before : ∃ k ∈ c.arm, k ≤ c.heart
  leg_before : ∃ k ∈ c.leg n, k ≤ c.heart

private def Code.path (c : Code) (n : ℕ) := word (2 * n + 2) c.arm {c.heart}

private lemma countBefore_full {m : ℕ} {A : Finset ℕ} (ha : A ⊆ Finset.range m) :
    countBefore A m = A.card := by
  rw [countBefore, Finset.inter_eq_right.mpr ha]

private lemma countBefore_single (h k : ℕ) :
    countBefore {h} k = if h < k then 1 else 0 := by
  by_cases hk : h < k <;> simp [countBefore, hk]

private lemma countBefore_le (A : Finset ℕ) (k : ℕ) : countBefore A k ≤ k := by
  simpa [countBefore] using
    Finset.card_le_card (Finset.inter_subset_left : Finset.range k ∩ A ⊆ Finset.range k)

private lemma path_mem {n : ℕ} {c : Code} (g : Good n c) : c.path n ∈ firstQuadrantPaths n := by
  refine ⟨by simp [Code.path, word], ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp hs
    by_cases ha : k ∈ c.arm <;> by_cases hd : k ∈ ({c.heart} : Finset ℕ) <;> simp [ha, hd]
  · intro k
    rw [Code.path, take_word, word_sum, countBefore_single]
    generalize min k (2 * n + 2) = t
    have hle := countBefore_le c.arm t
    split_ifs with ht
    · obtain ⟨a, ha, ah⟩ := g.arm_before
      obtain ⟨b, hb, bh⟩ := g.leg_before
      have hb' := (Finset.mem_sdiff.mp hb).2
      have hpos : 0 < countBefore c.arm t := Finset.card_pos.mpr
        ⟨a, Finset.mem_inter.mpr ⟨Finset.mem_range.mpr (by omega), ha⟩⟩
      have hlt : countBefore c.arm t < t := by
        change (Finset.range t ∩ c.arm).card < t
        conv_rhs => rw [← Finset.card_range t]
        apply Finset.card_lt_card
        exact Finset.ssubset_iff_of_subset Finset.inter_subset_left |>.mpr
          ⟨b, Finset.mem_range.mpr (by omega), by simp [hb']⟩
      constructor <;> dsimp <;> omega
    · constructor <;> dsimp <;> omega
  · simp [Code.path, word_sum, countBefore_single, g.heart_lt, countBefore_full g.arm_sub,
      g.arm_card, Prod.ext_iff]
    omega

private def armPositions (m : ℕ) (w : Steps) :=
  (Finset.range m).filter fun k => w[k]! = (1, 0) ∨ w[k]! = (0, -1)

private def backPositions (m : ℕ) (w : Steps) :=
  (Finset.range m).filter fun k => w[k]! = (-1, 0) ∨ w[k]! = (0, -1)

private lemma word_get {m k : ℕ} (hk : k < m) (A D : Finset ℕ) :
    (word m A D)[k]! =
      ((if k ∈ A then 1 else 0) - (if k ∈ D then 1 else 0),
       (if k ∈ A then 0 else 1) - (if k ∈ D then 1 else 0)) := by
  simp [word, getElem!_pos, hk]

private lemma recover_positions {m : ℕ} {A D : Finset ℕ} (ha : A ⊆ Finset.range m)
    (hd : D ⊆ Finset.range m) :
    armPositions m (word m A D) = A ∧ backPositions m (word m A D) = D := by
  constructor <;> ext k <;> by_cases hk : k < m
  all_goals simp only [armPositions, backPositions, Finset.mem_filter, Finset.mem_range]
  all_goals try rw [word_get hk]
  all_goals by_cases hA : k ∈ A <;> by_cases hD : k ∈ D <;> simp_all [Finset.subset_iff]

private lemma path_inj {n : ℕ} {c d : Code} (g : Good n c) (g' : Good n d)
    (eq : c.path n = d.path n) : c = d := by
  have hc := recover_positions g.arm_sub (Finset.singleton_subset_iff.mpr
    (Finset.mem_range.mpr g.heart_lt))
  have hd := recover_positions g'.arm_sub (Finset.singleton_subset_iff.mpr
    (Finset.mem_range.mpr g'.heart_lt))
  unfold Code.path at eq
  rw [eq] at hc
  cases c
  cases d
  simp_all

private lemma path_code {n : ℕ} {w : Steps} (hw : w ∈ firstQuadrantPaths n) :
    ∃ c : Code, Good n c ∧ c.path n = w := by
  obtain ⟨hlen, hsteps, hprefix, hend⟩ := hw
  let m := 2 * n + 2
  let A := armPositions m w
  let D := backPositions m w
  have ha : A ⊆ Finset.range m := Finset.filter_subset _ _
  have hd : D ⊆ Finset.range m := Finset.filter_subset _ _
  have heq : word m A D = w := by
    apply List.ext_getElem
    · simp [word, m, hlen]
    · intro k hk hk'
      have hkm : k < m := by simpa [word] using hk
      have hs := hsteps w[k] (List.getElem_mem hk')
      simp only [word, List.getElem_map, List.getElem_range]
      rcases hs with hs | hs | hs | hs <;>
        simp [A, D, armPositions, backPositions, hkm, hk', hs]
  rw [← heq, word_sum, countBefore_full ha, countBefore_full hd, Prod.mk.injEq] at hend
  dsimp [m] at hend
  obtain ⟨h, hD⟩ := Finset.card_eq_one.mp (show D.card = 1 by omega)
  have hh : h < m := Finset.mem_range.mp (hd (by simp [hD]))
  refine ⟨⟨h, A⟩, ?_, by simpa [Code.path, hD] using heq⟩
  specialize hprefix (h + 1)
  rw [← heq, take_word, Nat.min_eq_left (by omega), word_sum, hD, countBefore_single,
    ite_eq_left (by omega)] at hprefix
  dsimp only at hprefix
  rw [hD, Finset.card_singleton] at hend
  have hA : A.card = n + 1 := by omega
  refine ⟨hh, ha, hA, ?_, ?_, ?_⟩
  · simp [Code.leg, Finset.card_sdiff_of_subset ha, hA, m]
    omega
  · obtain ⟨k, hk⟩ := Finset.card_pos.mp (show 0 < countBefore A (h + 1) by omega)
    exact ⟨k, (Finset.mem_inter.mp hk).2, Nat.le_of_lt_succ
      (Finset.mem_range.mp (Finset.mem_inter.mp hk).1)⟩
  · have hlt : (Finset.range (h + 1) ∩ A).card < (Finset.range (h + 1)).card := by
      rw [Finset.card_range]
      change countBefore A (h + 1) < h + 1
      omega
    have hss := Finset.ssubset_iff_of_subset
      (Finset.inter_subset_left : Finset.range (h + 1) ∩ A ⊆ Finset.range (h + 1))
    obtain ⟨k, hk, hk'⟩ := hss.mp (lt_of_le_of_ne Finset.inter_subset_left
      (fun eq => (ne_of_lt hlt) (congrArg Finset.card eq)))
    have hkh := Finset.mem_range.mp hk
    exact ⟨k, Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr (by dsimp [m] at hh; omega),
      fun hA => hk' (Finset.mem_inter.mpr ⟨hk, hA⟩)⟩, Nat.le_of_lt_succ hkh⟩

-- The labels on the two sides omit 1 and the heart entry.
private def label (h k : ℕ) := if k ≤ h then k + 2 else k + 3

private lemma label_strict (h : ℕ) : StrictMono (label h) := by
  intro i j hij
  simp only [label]
  split_ifs <;> omega

private lemma label_bounds {n h k : ℕ} (hk : k < 2 * n + 2) :
    2 ≤ label h k ∧ label h k ≤ 2 * n + 4 ∧ label h k ≠ h + 3 := by
  unfold label
  split <;> omega

private lemma exists_label {n h v : ℕ} (hh : h < 2 * n + 2)
    (hv : 2 ≤ v) (hv' : v ≤ 2 * n + 4)
    (hne : v ≠ h + 3) : ∃ k < 2 * n + 2, label h k = v := by
  by_cases hlt : v < h + 3
  · exact ⟨v - 2, by omega, by simp [label, show v - 2 ≤ h by omega]; omega⟩
  · exact ⟨v - 3, by omega, by simp [label, show ¬ v - 3 ≤ h by omega]; omega⟩

private def axis (arm : Bool) (i : ℕ) : ℕ × ℕ := if arm then (0, i + 1) else (i + 1, 0)

private abbrev Tableau (n : ℕ) := SemistandardYoungTableau (nearHookTheta n)

private abbrev value {n : ℕ} (T : Tableau n) (p : ℕ × ℕ) := T p.1 p.2

private abbrev Standard {n : ℕ} (T : Tableau n) :=
  Set.BijOn (value T) (nearHookTheta n).cells (Set.Icc 1 (2 * n + 4))

private lemma shape {n i j : ℕ} :
    (i, j) ∈ nearHookTheta n ↔
      (i = 0 ∧ j < n + 2) ∨ (j = 0 ∧ i < n + 2) ∨ (i = 1 ∧ j = 1) := by
  rw [nearHookTheta, YoungDiagram.mem_ofRowLens]
  rcases i with _ | _ | i <;> simp <;> omega

private lemma axis_mem {n : ℕ} (b : Bool) (i : Fin (n + 1)) :
    axis b i ∈ (nearHookTheta n).cells := by
  have := i.isLt
  cases b <;> simp [axis, YoungDiagram.mem_cells, shape]

private lemma cells_cases {n : ℕ} {p : ℕ × ℕ} (hp : p ∈ (nearHookTheta n).cells) :
    p = (0, 0) ∨ p = (1, 1) ∨ ∃ (b : Bool) (i : Fin (n + 1)), p = axis b i := by
  obtain ⟨i, j⟩ := p
  change (i, j) ∈ nearHookTheta n at hp
  rw [shape] at hp
  rcases hp with ⟨rfl, hj⟩ | ⟨rfl, hi⟩ | ⟨rfl, rfl⟩
  · cases j with
    | zero => exact Or.inl rfl
    | succ j => exact Or.inr (.inr ⟨true, ⟨j, by omega⟩, rfl⟩)
  · cases i with
    | zero => exact Or.inl rfl
    | succ i => exact Or.inr (.inr ⟨false, ⟨i, by omega⟩, rfl⟩)
  · exact Or.inr (.inl rfl)

private def Code.side (c : Code) (n : ℕ) (b : Bool) := if b then c.arm else c.leg n

private lemma side_card {n : ℕ} {c : Code} (g : Good n c) (b : Bool) :
    (c.side n b).card = n + 1 := by
  cases b
  exacts [g.leg_card, g.arm_card]

private def indexAt {n : ℕ} {c : Code} (g : Good n c) (b : Bool) :=
  (c.side n b).orderEmbOfFin (side_card g b)

private lemma index_mem {n : ℕ} {c : Code} (g : Good n c) (b : Bool) (i : Fin (n + 1)) :
    indexAt g b i ∈ c.side n b := Finset.orderEmbOfFin_mem _ _ _

private lemma index_lt {n : ℕ} {c : Code} (g : Good n c) (b : Bool) (i : Fin (n + 1)) :
    indexAt g b i < 2 * n + 2 := by
  have hi := index_mem g b i
  cases b
  · exact Finset.mem_range.mp (Finset.mem_sdiff.mp hi).1
  · exact Finset.mem_range.mp (g.arm_sub hi)

private lemma exists_index {n : ℕ} {c : Code} (g : Good n c) (b : Bool) {k : ℕ}
    (hk : k ∈ c.side n b) : ∃ i, indexAt g b i = k := by
  exact (Finset.range_orderEmbOfFin _ (side_card g b) ▸ hk : k ∈ Set.range (indexAt g b))

private def entryAt {n : ℕ} {c : Code} (g : Good n c) (b : Bool) (i : Fin (n + 1)) :=
  label c.heart (indexAt g b i)

private lemma entry_mono {n : ℕ} {c : Code} (g : Good n c) (b : Bool) :
    StrictMono (entryAt g b) := (label_strict _).comp (indexAt g b).strictMono

private lemma first_lt_heart {n : ℕ} {c : Code} (g : Good n c) (b : Bool) :
    entryAt g b 0 < c.heart + 3 := by
  have hb : ∃ k ∈ c.side n b, k ≤ c.heart := by
    cases b
    exacts [g.leg_before, g.arm_before]
  obtain ⟨k, hk, hle⟩ := hb
  obtain ⟨i, rfl⟩ := exists_index g b hk
  have hi := (indexAt g b).monotone (Fin.zero_le i)
  simp [entryAt, label, hi.trans hle]
  omega

private structure Matches {n : ℕ} (T : Tableau n) {c : Code} (g : Good n c) : Prop where
  corner : T 0 0 = 1
  heart : T 1 1 = c.heart + 3
  sides (b : Bool) (i : Fin (n + 1)) : value T (axis b i) = entryAt g b i

private lemma matches_unique {n : ℕ} {T U : Tableau n} {c : Code} {g : Good n c}
    (hT : Matches T g) (hU : Matches U g) : T = U := by
  ext i j
  by_cases h : (i, j) ∈ nearHookTheta n
  · change value T (i, j) = value U (i, j)
    rcases cells_cases h with hc | hc | ⟨b, t, hc⟩ <;> rw [hc]
    · exact hT.corner.trans hU.corner.symm
    · exact hT.heart.trans hU.heart.symm
    · rw [hT.sides, hU.sides]
  · rw [T.zeros h, U.zeros h]

private lemma test_arm {n : ℕ} {T : Tableau n} {c : Code} {g : Good n c}
    (hT : Matches T g) (k : ℕ) :
    (∃ j < n + 2, T 0 j = label c.heart k) ↔ k ∈ c.arm := by
  constructor
  · rintro ⟨_ | j, hj, he⟩
    · rw [hT.corner] at he
      unfold label at he
      split at he <;> omega
    · let i : Fin (n + 1) := ⟨j, by omega⟩
      have he' : label c.heart (indexAt g true i) = label c.heart k :=
        (hT.sides true i).symm.trans he
      exact (label_strict _).injective he' ▸ index_mem g true i
  · intro hk
    obtain ⟨i, rfl⟩ := exists_index g true hk
    exact ⟨i + 1, by have := i.isLt; omega, hT.sides true i⟩

private lemma matches_path {n : ℕ} {T : Tableau n} {c : Code} {g : Good n c}
    (hT : Matches T g) : nearHookTableauToPathXi n T = c.path n := by
  unfold nearHookTableauToPathXi Code.path word
  apply List.map_congr_left
  intro k _
  have ha := test_arm hT k
  rw [hT.heart]
  rcases lt_trichotomy k c.heart with hk | rfl | hk
  · simp [label, hk.le] at ha
    by_cases h : k ∈ c.arm <;> simp [show k + 3 < c.heart + 3 by omega, ha, h, hk.ne]
  · simp [label] at ha
    by_cases h : c.heart ∈ c.arm <;> simp [ha, h]
  · simp [label, hk.not_ge] at ha
    by_cases h : k ∈ c.arm <;> simp [ha, h, hk.ne', hk.not_gt]

private def filling {n : ℕ} {c : Code} (g : Good n c) : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, j + 1 => if hj : j < n + 1 then entryAt g true ⟨j, hj⟩ else 0
  | i + 1, 0 => if hi : i < n + 1 then entryAt g false ⟨i, hi⟩ else 0
  | 1, 1 => c.heart + 3
  | _, _ => 0

private lemma entry_bounds {n : ℕ} {c : Code} (g : Good n c) (b : Bool) (i : Fin (n + 1)) :
    2 ≤ entryAt g b i ∧ entryAt g b i ≤ 2 * n + 4 :=
  ⟨(label_bounds (h := c.heart) (index_lt g b i)).1,
    (label_bounds (h := c.heart) (index_lt g b i)).2.1⟩

private def tableau {n : ℕ} {c : Code} (g : Good n c) : Tableau n where
  entry := filling g
  row_weak' := by
    intro i j k hj hc
    rcases shape.mp hc with ⟨rfl, hk⟩ | ⟨rfl, -⟩ | ⟨rfl, rfl⟩
    · cases k with
      | zero => omega
      | succ k =>
        have hk' : k < n + 1 := by omega
        cases j with
        | zero => simpa [filling, hk'] using (entry_bounds g true ⟨k, hk'⟩).1.trans'
                    (by decide : 1 ≤ 2)
        | succ j =>
          have hj' : j < n + 1 := by omega
          simpa [filling, hj', hk'] using
            (entry_mono g true).monotone (show (⟨j, hj'⟩ : Fin _) ≤ ⟨k, hk'⟩ from
              Nat.le_of_succ_le_succ hj.le)
    · omega
    · obtain rfl : j = 0 := by omega
      simpa [filling] using (first_lt_heart g false).le
  col_strict' := by
    intro i k j hi hc
    rcases shape.mp hc with ⟨rfl, -⟩ | ⟨rfl, hk⟩ | ⟨rfl, rfl⟩
    · omega
    · cases k with
      | zero => omega
      | succ k =>
        have hk' : k < n + 1 := by omega
        cases i with
        | zero => simpa [filling, hk'] using (show 1 < entryAt g false ⟨k, hk'⟩ from
                    Nat.lt_of_succ_le (entry_bounds g false ⟨k, hk'⟩).1)
        | succ i =>
          have hi' : i < n + 1 := by omega
          simpa [filling, hi', hk'] using
            entry_mono g false (show (⟨i, hi'⟩ : Fin _) < ⟨k, hk'⟩ from Nat.lt_of_succ_lt_succ hi)
    · obtain rfl : i = 0 := by omega
      simpa [filling] using first_lt_heart g true
  zeros' := by
    intro i j hc
    rw [shape] at hc
    rcases i with _ | _ | i <;> rcases j with _ | _ | j <;> simp_all [filling]

private lemma tableau_matches {n : ℕ} {c : Code} (g : Good n c) : Matches (tableau g) g where
  corner := rfl
  heart := rfl
  sides b i := by
    change filling g (axis b i).1 (axis b i).2 = _
    cases b <;> simp [axis, filling, i.isLt]

private lemma tableau_standard {n : ℕ} {c : Code} (g : Good n c) : Standard (tableau g) := by
  let T := tableau g
  have ht : Matches T g := tableau_matches g
  have hh := g.heart_lt
  have hmap : Set.MapsTo (value T) (nearHookTheta n).cells (Finset.Icc 1 (2 * n + 4)) := by
    intro p hp
    rw [Finset.mem_coe, Finset.mem_Icc]
    rcases cells_cases hp with rfl | rfl | ⟨b, i, rfl⟩
    · change 1 ≤ T 0 0 ∧ T 0 0 ≤ _
      rw [ht.corner]
      omega
    · change 1 ≤ T 1 1 ∧ T 1 1 ≤ _
      rw [ht.heart]
      omega
    · rw [ht.sides]
      have := entry_bounds g b i
      omega
  have hsurj : Set.SurjOn (value T) (nearHookTheta n).cells (Finset.Icc 1 (2 * n + 4)) := by
    intro v hv
    obtain ⟨hv, hv'⟩ := Finset.mem_Icc.mp hv
    by_cases h1 : v = 1
    · exact ⟨(0, 0), shape.mpr (by simp), ht.corner.trans h1.symm⟩
    by_cases hH : v = c.heart + 3
    · exact ⟨(1, 1), shape.mpr (by simp), ht.heart.trans hH.symm⟩
    obtain ⟨k, hk, rfl⟩ := exists_label hh (by omega) hv' hH
    have aux (b : Bool) (hb : k ∈ c.side n b) :
        label c.heart k ∈ value T '' ↑(nearHookTheta n).cells := by
      obtain ⟨i, rfl⟩ := exists_index g b hb
      exact ⟨_, axis_mem b i, ht.sides b i⟩
    by_cases ha : k ∈ c.arm
    · exact aux true ha
    · exact aux false (Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr hk, ha⟩)
  have hc : (nearHookTheta n).cells.card ≤ (Finset.Icc 1 (2 * n + 4)).card := by
    change (nearHookTheta n).card ≤ _
    rw [← YoungDiagram.sum_rowLens_eq_card, nearHookTheta_rowLens]
    simp
    omega
  unfold Standard
  rw [← Finset.coe_Icc]
  exact ⟨hmap, Finset.injOn_of_surjOn_of_card_le _ hmap hsurj hc, hsurj⟩

private lemma row_strict {n : ℕ} {T : Tableau n} (hs : Standard T) {i j k : ℕ} (hjk : j < k)
    (hc : (i, k) ∈ nearHookTheta n) : T i j < T i k := by
  apply lt_of_le_of_ne (T.row_weak hjk hc)
  intro heq
  have eq := hs.injOn (x₁ := (i, j)) (x₂ := (i, k))
    ((nearHookTheta n).up_left_mem le_rfl hjk.le hc) hc heq
  exact hjk.ne (congrArg Prod.snd eq)

private lemma standard_corner {n : ℕ} {T : Tableau n} (hs : Standard T) : T 0 0 = 1 := by
  have h00 : (0, 0) ∈ nearHookTheta n := shape.mpr (by simp)
  have hlo : 1 ≤ T 0 0 := (hs.mapsTo h00).1
  obtain ⟨⟨i, j⟩, hij, heq⟩ := hs.surjOn (show 1 ∈ Set.Icc 1 (2 * n + 4) by simp)
  have hi := T.col_weak (Nat.zero_le i) ((nearHookTheta n).up_left_mem le_rfl (Nat.zero_le j) hij)
  have hj := T.row_weak_of_le (Nat.zero_le j) hij
  change T i j = 1 at heq
  omega

private lemma axis_mono {n : ℕ} {T : Tableau n} (hs : Standard T) (b : Bool) :
    StrictMono (fun i : Fin (n + 1) => value T (axis b i)) := by
  intro i j hij
  cases b
  · exact T.col_strict (Nat.succ_lt_succ hij) (axis_mem false j)
  · exact row_strict hs (Nat.succ_lt_succ hij) (axis_mem true j)

private lemma axis_first_lt {n : ℕ} {T : Tableau n} (hs : Standard T) (b : Bool) :
    value T (axis b 0) < T 1 1 := by
  have hc : (1, 1) ∈ nearHookTheta n := shape.mpr (by simp)
  cases b
  · exact row_strict hs (by decide : 0 < 1) hc
  · exact T.col_strict (by decide : 0 < 1) hc

private lemma axis_gt_one {n : ℕ} {T : Tableau n} (hs : Standard T) (b : Bool) (i : Fin (n + 1)) :
    1 < value T (axis b i) := by
  conv_lhs => rw [← standard_corner hs]
  cases b
  · exact T.col_strict (Nat.zero_lt_succ _) (axis_mem false i)
  · exact row_strict hs (Nat.zero_lt_succ _) (axis_mem true i)

private lemma axis_ne_heart {n : ℕ} {T : Tableau n} (hs : Standard T) (b : Bool)
    (i : Fin (n + 1)) : value T (axis b i) ≠ T 1 1 := by
  have hc : (1, 1) ∈ nearHookTheta n := shape.mpr (by simp)
  intro he
  have eq := hs.injOn (axis_mem b i) hc he
  cases b <;> simp [axis] at eq

private lemma tableau_code {n : ℕ} {T : Tableau n} (hs : Standard T) :
    ∃ (c : Code) (g : Good n c), Matches T g := by
  let h := T 1 1 - 3
  have hlow := axis_gt_one hs true 0
  have hhigh := axis_first_lt hs true
  change 1 < T 0 1 at hlow
  change T 0 1 < T 1 1 at hhigh
  have hH : T 1 1 = h + 3 := by dsimp [h]; omega
  have hval := hs.mapsTo (x := (1, 1)) (shape.mpr (by simp))
  have hh : h < 2 * n + 2 := by change _ ∧ T 1 1 ≤ _ at hval; omega
  -- Index each non-corner side cell by its label with the heart skipped.
  have hinv (b : Bool) (i : Fin (n + 1)) :
      ∃ k < 2 * n + 2, label h k = value T (axis b i) := by
    apply exists_label hh (axis_gt_one hs b i) (hs.mapsTo (axis_mem b i)).2
    rw [← hH]
    exact axis_ne_heart hs b i
  choose idx idx_lt idx_label using hinv
  have hmono (b : Bool) : StrictMono (idx b) := by
    intro i j hij
    apply (label_strict h).lt_iff_lt.mp
    simpa only [idx_label] using (axis_mono hs b hij)
  let indices (b : Bool) := Finset.univ.image (idx b)
  have hmem (b : Bool) (i : Fin (n + 1)) : idx b i ∈ indices b :=
    Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have hcard (b : Bool) : (indices b).card = n + 1 := by
    simp [indices, Finset.card_image_of_injective _ (hmono b).injective]
  have hsub (b : Bool) : indices b ⊆ Finset.range (2 * n + 2) := by
    intro k hk
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_range.mpr (idx_lt b i)
  let c : Code := ⟨h, indices true⟩
  have hleg : c.leg n = indices false := by
    ext k
    change k ∈ Finset.range (2 * n + 2) \ indices true ↔ k ∈ indices false
    rw [Finset.mem_sdiff]
    constructor
    · rintro ⟨hk, hA⟩
      have hb := label_bounds (h := h) (Finset.mem_range.mp hk)
      obtain ⟨p, hp, hep⟩ := hs.surjOn (show label h k ∈ Set.Icc 1 (2 * n + 4) from
        ⟨by omega, hb.2.1⟩)
      rcases cells_cases hp with rfl | rfl | ⟨b, i, rfl⟩
      · change T 0 0 = _ at hep
        rw [standard_corner hs] at hep
        omega
      · change T 1 1 = _ at hep
        omega
      · have he := (label_strict h).injective ((idx_label b i).trans hep)
        cases b
        · exact he ▸ hmem false i
        · exact (hA (he ▸ hmem true i)).elim
    · intro hk
      refine ⟨hsub false hk, ?_⟩
      rintro hk'
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hk
      obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hk'
      have he : value T (axis false i) = value T (axis true j) := by
        rw [← idx_label, ← idx_label, hi, hj]
      have eq := hs.injOn (axis_mem false i) (axis_mem true j) he
      simp [axis] at eq
  have hside (b : Bool) : c.side n b = indices b := by
    cases b
    · exact hleg
    · rfl
  have hbefore (b : Bool) : idx b 0 ≤ h := by
    have hlt := axis_first_lt hs b
    have he := idx_label b 0
    change label h (idx b 0) = value T (axis b 0) at he
    unfold label at he
    split at he <;> omega
  have g : Good n c := ⟨hh, hsub true, hcard true, hleg ▸ hcard false,
    ⟨_, hmem true 0, hbefore true⟩, ⟨_, hleg ▸ hmem false 0, hbefore false⟩⟩
  refine ⟨c, g, standard_corner hs, hH, ?_⟩
  intro b i
  have he : idx b = indexAt g b := Finset.orderEmbOfFin_unique (side_card g b)
    (fun j => hside b ▸ hmem b j) (hmono b)
  exact (idx_label b i).symm.trans (congrArg (label h) (congrFun he i))

-- The two maps encode the side entries with the same heart position. Up to that position,
-- ξ reads the labels 2, …, H - 1 in order, while ψ moves the label 2 to the backward step.
private def cyclePrefix (h : ℕ) : ℕ ≃ ℕ where
  toFun k := if k < h then k + 1 else if k = h then 0 else k
  invFun k := if k = 0 then h else if k ≤ h then k - 1 else k
  left_inv k := by
    dsimp only
    rcases lt_trichotomy k h with hlt | rfl | hgt
    · simp [hlt, show k + 1 ≤ h by omega]
    · simp
    · simp [hgt.not_gt, hgt.ne', show k ≠ 0 by omega, hgt.not_ge]
  right_inv k := by dsimp only; split_ifs <;> omega

private lemma cyclePrefix_lt (h m k : ℕ) (hm : h < m) :
    cyclePrefix h k < m ↔ k < m := by
  change (if k < h then k + 1 else if k = h then 0 else k) < m ↔ k < m
  split_ifs <;> omega

private def Code.reindex (c : Code) (e : ℕ ≃ ℕ) : Code :=
  ⟨c.heart, c.arm.map e.symm.toEmbedding⟩

private lemma mem_reindex_arm (c : Code) (e : ℕ ≃ ℕ) (k : ℕ) :
    k ∈ (c.reindex e).arm ↔ e k ∈ c.arm := by
  simp [Code.reindex, Finset.mem_map_equiv]

private lemma reindex_symm (c : Code) (e : ℕ ≃ ℕ) : (c.reindex e).reindex e.symm = c := by
  cases c with
  | mk h A =>
    have ha : ((Code.mk h A).reindex e |>.reindex e.symm).arm = A := by
      ext k
      simp [mem_reindex_arm]
    exact congrArg (Code.mk h) ha

private lemma Good.reindex {n : ℕ} {c : Code} (g : Good n c) (e : ℕ ≃ ℕ)
    (hrange : ∀ k, e k < 2 * n + 2 ↔ k < 2 * n + 2)
    (hprefix : ∀ k, e k < c.heart + 1 ↔ k < c.heart + 1) : Good n (c.reindex e) := by
  have hleg : (c.reindex e).leg n = (c.leg n).map e.symm.toEmbedding := by
    ext k
    simp only [Code.leg, Finset.mem_sdiff, Finset.mem_range, mem_reindex_arm,
      Finset.mem_map_equiv, Equiv.symm_symm, hrange]
  have hbefore (k : ℕ) (hk : k ≤ c.heart) : e.symm k ≤ c.heart := by
    apply Nat.lt_succ_iff.mp ((hprefix (e.symm k)).mp _)
    simpa only [Equiv.apply_symm_apply] using Nat.lt_succ_of_le hk
  refine ⟨g.heart_lt, ?_, by simp [Code.reindex, g.arm_card], by simp [hleg, g.leg_card], ?_, ?_⟩
  · intro k hk
    exact Finset.mem_range.mpr ((hrange k).mp (Finset.mem_range.mp
      (g.arm_sub ((mem_reindex_arm c e k).mp hk))))
  · obtain ⟨k, hk, hkh⟩ := g.arm_before
    exact ⟨e.symm k, by simp [mem_reindex_arm, hk], hbefore k hkh⟩
  · obtain ⟨k, hk, hkh⟩ := g.leg_before
    exact ⟨e.symm k, by simp [hleg, hk], hbefore k hkh⟩

private def Code.rotate (c : Code) : Code := c.reindex (cyclePrefix c.heart)

private def Code.unrotate (c : Code) : Code := c.reindex (cyclePrefix c.heart).symm

private lemma Good.rotate {n : ℕ} {c : Code} (g : Good n c) : Good n c.rotate :=
  g.reindex _ (fun k => cyclePrefix_lt _ _ k g.heart_lt)
    (fun k => cyclePrefix_lt _ _ k (Nat.lt_succ_self _))

private lemma Good.unrotate {n : ℕ} {c : Code} (g : Good n c) : Good n c.unrotate := by
  have aux (m k : ℕ) (hm : c.heart < m) : (cyclePrefix c.heart).symm k < m ↔ k < m := by
    rw [← cyclePrefix_lt c.heart m ((cyclePrefix c.heart).symm k) hm, Equiv.apply_symm_apply]
  exact g.reindex _ (fun k => aux _ k g.heart_lt) (fun k => aux _ k (Nat.lt_succ_self _))

private lemma unrotate_rotate (c : Code) : c.rotate.unrotate = c :=
  reindex_symm c (cyclePrefix c.heart)

private lemma rotate_unrotate (c : Code) : c.unrotate.rotate = c :=
  reindex_symm c (cyclePrefix c.heart).symm

private lemma side_has_label {n : ℕ} {T : Tableau n} {c : Code} {g : Good n c}
    (hT : Matches T g) (b : Bool) {v : ℕ} (hv : v ≠ 1) :
    (∃ j < n + 2, (if b then T 0 j else T j 0) = v) ↔
      ∃ k ∈ c.side n b, label c.heart k = v := by
  constructor
  · rintro ⟨_ | j, hj, he⟩
    · exact (hv (by simpa [hT.corner] using he.symm)).elim
    · let i : Fin (n + 1) := ⟨j, by omega⟩
      refine ⟨indexAt g b i, index_mem g b i, (hT.sides b i).symm.trans ?_⟩
      cases b <;> exact he
  · rintro ⟨k, hk, hvk⟩
    obtain ⟨i, rfl⟩ := exists_index g b hk
    refine ⟨i + 1, by have := i.isLt; omega, ?_⟩
    cases b <;> exact (hT.sides _ i).trans hvk

private lemma matches_path_psi {n : ℕ} {T : Tableau n} {c : Code} {g : Good n c}
    (hT : Matches T g) : nearHookTableauToPathPsi n T = c.rotate.path n := by
  unfold nearHookTableauToPathPsi Code.path word
  apply List.map_congr_left
  intro k hk
  rw [List.mem_range] at hk
  have hmem := mem_reindex_arm c (cyclePrefix c.heart) k
  change k ∈ c.rotate.arm ↔ _ at hmem
  have hside (b : Bool) (j : ℕ) :
      (∃ i < n + 2, (if b then T 0 i else T i 0) = label c.heart j) ↔ j ∈ c.side n b := by
    have hne : label c.heart j ≠ 1 := by unfold label; split <;> omega
    rw [side_has_label hT b hne]
    simp [(label_strict c.heart).injective.eq_iff]
  have heart_eq : c.rotate.heart = c.heart := rfl
  by_cases hh : k = c.heart
  · subst k
    have hnone (b : Bool) : ¬ ∃ i < n + 2, (if b then T 0 i else T i 0) = c.heart + 3 := by
      rw [side_has_label hT b (by omega)]
      rintro ⟨j, -, hj⟩
      unfold label at hj
      split at hj <;> omega
    have ha : ¬ ∃ i < n + 2, T 0 i = c.heart + 3 := hnone true
    have hl : ¬ ∃ i < n + 2, T i 0 = c.heart + 3 := hnone false
    have htwo : (∃ i < n + 2, T 0 i = 2) ↔ 0 ∈ c.arm := by
      simpa [Code.side, label] using hside true 0
    have hmem₀ : c.heart ∈ c.rotate.arm ↔ 0 ∈ c.arm := by simpa [cyclePrefix] using hmem
    by_cases h : 0 ∈ c.arm <;> simp [hmem₀, heart_eq, ha, hl, htwo, h]
  · let j := cyclePrefix c.heart k
    have hj : j < 2 * n + 2 := (cyclePrefix_lt _ _ _ g.heart_lt).mpr hk
    have hlabel : label c.heart j = k + 3 := by
      dsimp [j]
      by_cases hlt : k < c.heart
      · simp [cyclePrefix, hlt, label, show k + 1 ≤ c.heart by omega]
      · simp [cyclePrefix, hlt, hh, label, show ¬ k ≤ c.heart by omega]
    have ha : (∃ i < n + 2, T 0 i = k + 3) ↔ j ∈ c.arm := by
      simpa [Code.side, hlabel] using hside true j
    have hl : (∃ i < n + 2, T i 0 = k + 3) ↔ j ∉ c.arm := by
      simpa [Code.side, Code.leg, Finset.mem_range, hj, hlabel] using hside false j
    change k ∈ c.rotate.arm ↔ j ∈ c.arm at hmem
    by_cases h : j ∈ c.arm <;> simp [hmem, heart_eq, hh, ha, hl, h]

end bijOn_nearHookTableauToPathXi

open bijOn_nearHookTableauToPathXi

/-- **The map $\xi$ is a bijection from near-hook tableaux to first-quadrant paths.** For every
$n \in \mathbb{N}$, the map $\xi$ restricts to a bijection from the standard Young tableaux of
shape $\theta^{(n)}$ onto the set $\mathcal{P}_n$ of first-quadrant paths. Here a standard Young
tableau of shape $\theta^{(n)}$ is a semistandard Young tableau of that shape whose entries map
the $2n + 4$ cells of $\theta^{(n)}$ bijectively onto $\{1, \dots, 2n + 4\}$.

Source: Liam Ayres, Evan Bialo, Alwin Chen, Aidan Cook, Matteus Froese, Erica Liu, Maryam Mohammadi
Yekta, Oliver Pechenik and Benjamin Wong, *An Exceptional Equinumerosity of Lattice Paths and Young
Tableaux*, Journal of Integer Sequences 28 (2025), Article 25.5.2, Proposition 3
(`jis-2025-25.5.2-prop-3`). -/
public theorem bijOn_nearHookTableauToPathXi (n : ℕ) :
    Set.BijOn (nearHookTableauToPathXi n)
      {T | Set.BijOn (fun c : ℕ × ℕ => T c.1 c.2) (nearHookTheta n).cells
        (Set.Icc 1 (2 * n + 4))}
      (firstQuadrantPaths n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro T hT
    obtain ⟨c, g, hm⟩ := tableau_code hT
    rw [matches_path hm]
    exact path_mem g
  · intro T hT U hU heq
    obtain ⟨c, g, ht⟩ := tableau_code hT
    obtain ⟨d, g', hu⟩ := tableau_code hU
    rw [matches_path ht, matches_path hu] at heq
    obtain rfl := path_inj g g' heq
    exact matches_unique ht hu
  · intro w hw
    obtain ⟨c, g, rfl⟩ := path_code hw
    exact ⟨tableau g, tableau_standard g, matches_path (tableau_matches g)⟩

/-- **The map $\psi$ is a bijection from near-hook tableaux to first-quadrant paths.** For every
$n \in \mathbb{N}$, the map $\psi$ restricts to a bijection from the standard Young tableaux of
shape $\theta^{(n)}$ onto the set $\mathcal{P}_n$ of first-quadrant paths. Here a standard Young
tableau of shape $\theta^{(n)}$ is a semistandard Young tableau of that shape whose entries map
the $2n + 4$ cells of $\theta^{(n)}$ bijectively onto $\{1, \dots, 2n + 4\}$.

Source: Liam Ayres, Evan Bialo, Alwin Chen, Aidan Cook, Matteus Froese, Erica Liu, Maryam Mohammadi
Yekta, Oliver Pechenik and Benjamin Wong, *An Exceptional Equinumerosity of Lattice Paths and Young
Tableaux*, Journal of Integer Sequences 28 (2025), Article 25.5.2, Theorem 2
(`jis-2025-25.5.2-thm-2`). -/
public theorem bijOn_nearHookTableauToPathPsi (n : ℕ) :
    Set.BijOn (nearHookTableauToPathPsi n)
      {T | Set.BijOn (fun c : ℕ × ℕ => T c.1 c.2) (nearHookTheta n).cells
        (Set.Icc 1 (2 * n + 4))}
      (firstQuadrantPaths n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro T hT
    obtain ⟨c, g, hm⟩ := tableau_code hT
    rw [matches_path_psi hm]
    exact path_mem g.rotate
  · intro T hT U hU heq
    obtain ⟨c, g, ht⟩ := tableau_code hT
    obtain ⟨d, g', hu⟩ := tableau_code hU
    rw [matches_path_psi ht, matches_path_psi hu] at heq
    have h := congrArg Code.unrotate (path_inj g.rotate g'.rotate heq)
    rw [unrotate_rotate, unrotate_rotate] at h
    subst d
    exact matches_unique ht hu
  · intro w hw
    obtain ⟨c, g, rfl⟩ := path_code hw
    refine ⟨tableau g.unrotate, tableau_standard g.unrotate, ?_⟩
    rw [matches_path_psi (tableau_matches g.unrotate), rotate_unrotate]

end

end MetaMathlibExt
