/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Int.Basic
public import Mathlib.SetTheory.Cardinal.Finite

import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

/-! # Fault-free 3 × n tilings recursion

This file proves the recurrence for vertical-fault-free tilings of a `3 × n` rectangle by
squares and dominoes.
-/

/-- **Cells of the $3 \times n$ rectangle.** A cell of the $3 \times n$ rectangle is a pair
$(r, c)$ of a row $r \in \{0, 1, 2\}$ and a column $c \in \{0, \dots, n-1\}$. -/
abbrev TilingCell (n : ℕ) := Fin 3 × Fin n

/-- **Adjacent cells.** Two cells $x$ and $y$ of the $3 \times n$ rectangle are adjacent when they
share an edge: they lie in the same row and their columns differ by $1$, or they lie in the same
column and their rows differ by $1$. -/
def TilingCell.Adjacent {n : ℕ} (x y : TilingCell n) : Prop :=
  (x.1 = y.1 ∧ (x.2.val + 1 = y.2.val ∨ y.2.val + 1 = x.2.val)) ∨
    (x.2 = y.2 ∧ (x.1.val + 1 = y.1.val ∨ y.1.val + 1 = x.1.val))

/-- **Square and domino tiles.** A set $d$ of cells of the $3 \times n$ rectangle is a
square-or-domino tile when it consists of exactly one cell, or of exactly two cells that are
adjacent. -/
def IsSquareOrDomino {n : ℕ} (d : Finset (TilingCell n)) : Prop :=
  d.card = 1 ∨
    (d.card = 2 ∧ ∀ x ∈ d, ∀ y ∈ d, x ≠ y → TilingCell.Adjacent x y)

private theorem ff3_adjacent_comm {n : ℕ} {x y : TilingCell n} :
    TilingCell.Adjacent x y ↔ TilingCell.Adjacent y x := by
  simp only [TilingCell.Adjacent, eq_comm]
  tauto

/-- **Characterization of square and domino tiles.** A set $d$ of cells of the $3 \times n$
rectangle is a square-or-domino tile if and only if either $d = \{x\}$ for some cell $x$, or
$d = \{x, y\}$ for some distinct adjacent cells $x$ and $y$. -/
public theorem isSquareOrDomino_iff {n : ℕ} (d : Finset (TilingCell n)) :
    IsSquareOrDomino d ↔
      (∃ x, d = {x}) ∨
        ∃ x y, x ≠ y ∧ TilingCell.Adjacent x y ∧ d = {x, y} := by
  constructor
  · rintro (h | ⟨hcard, hadj⟩)
    · exact Or.inl (Finset.card_eq_one.mp h)
    · obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hcard
      refine Or.inr ⟨x, y, hxy, ?_, rfl⟩
      exact hadj x (by simp) y (by simp) hxy
  · rintro (⟨x, rfl⟩ | ⟨x, y, hxy, hadj, rfl⟩)
    · exact Or.inl (by simp)
    · refine Or.inr ⟨by simp [hxy], ?_⟩
      intro a ha b hb hab
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact (hab rfl).elim
      · exact hadj
      · exact ff3_adjacent_comm.mp hadj
      · exact (hab rfl).elim

/-- **Square-and-domino tilings.** A square-and-domino tiling of the $3 \times n$ rectangle is a
finite family $T$ of sets of cells such that every member of $T$ is a square-or-domino tile (a
single cell or two adjacent cells), any two distinct members of $T$ are disjoint, and every cell
of the rectangle lies in some member of $T$. -/
def IsSquareDominoTiling {n : ℕ} (T : Finset (Finset (TilingCell n))) : Prop :=
  (∀ d ∈ T, IsSquareOrDomino d) ∧
    (∀ d₁ ∈ T, ∀ d₂ ∈ T, d₁ ≠ d₂ → Disjoint d₁ d₂) ∧
      ∀ x : TilingCell n, ∃ d ∈ T, x ∈ d

/-- **Vertical-fault-free families.** A family $T$ of sets of cells of the $3 \times n$ rectangle,
with columns numbered $0, \dots, n-1$, is vertical-fault-free when for every natural number $k$
with $k + 1 < n$ some member of $T$ contains two cells of the same row lying in columns $k$ and
$k + 1$. For a square-and-domino tiling this says that every internal vertical boundary is
crossed by a horizontal domino. -/
def IsVerticalFaultFree {n : ℕ} (T : Finset (Finset (TilingCell n))) : Prop :=
  ∀ k : ℕ, k + 1 < n →
    ∃ d ∈ T, ∃ x ∈ d, ∃ y ∈ d,
      x.1 = y.1 ∧ x.2.val = k ∧ y.2.val = k + 1

private def ff3IsDomino {n : ℕ} (d : Finset (TilingCell n)) : Prop :=
  d.card = 2 ∧
    ∀ x ∈ d, ∀ y ∈ d, x ≠ y → TilingCell.Adjacent x y

private def ff3IsMatching {n : ℕ} (D : Finset (Finset (TilingCell n))) : Prop :=
  (∀ d ∈ D, ff3IsDomino d) ∧
    ∀ d₁ ∈ D, ∀ d₂ ∈ D, d₁ ≠ d₂ → Disjoint d₁ d₂

private abbrev ff3FaultFreeTilings (n : ℕ) :=
  {T : Finset (Finset (TilingCell n)) //
    IsSquareDominoTiling T ∧ IsVerticalFaultFree T}

private abbrev ff3FaultFreeMatchings (n : ℕ) :=
  {D : Finset (Finset (TilingCell n)) //
    ff3IsMatching D ∧ IsVerticalFaultFree D}

private def ff3Dominoes {n : ℕ} (T : Finset (Finset (TilingCell n))) :=
  T.filter fun d ↦ d.card = 2

private def ff3Uncovered {n : ℕ} (D : Finset (Finset (TilingCell n))) :=
  Finset.univ.filter fun x ↦ ∀ d ∈ D, x ∉ d

private def ff3Complete {n : ℕ} (D : Finset (Finset (TilingCell n))) :=
  D ∪ (ff3Uncovered D).image fun x ↦ {x}

private theorem ff3_dominoes_matching {n : ℕ} {T : Finset (Finset (TilingCell n))}
    (hT : IsSquareDominoTiling T) : ff3IsMatching (ff3Dominoes T) := by
  refine ⟨?_, ?_⟩
  · intro d hd
    simp only [ff3Dominoes, Finset.mem_filter] at hd
    obtain ⟨hdT, hcard⟩ := hd
    obtain hsingle | hdomino := hT.1 d hdT
    · omega
    · exact hdomino
  · intro d₁ hd₁ d₂ hd₂ hne
    simp only [ff3Dominoes, Finset.mem_filter] at hd₁ hd₂
    exact hT.2.1 d₁ hd₁.1 d₂ hd₂.1 hne

private theorem ff3_dominoes_faultFree {n : ℕ} {T : Finset (Finset (TilingCell n))}
    (hvalid : ∀ d ∈ T, IsSquareOrDomino d) (hT : IsVerticalFaultFree T) :
    IsVerticalFaultFree (ff3Dominoes T) := by
  intro k hk
  obtain ⟨d, hd, x, hxd, y, hyd, hrow, hx, hy⟩ := hT k hk
  refine ⟨d, ?_, x, hxd, y, hyd, hrow, hx, hy⟩
  simp only [ff3Dominoes, Finset.mem_filter]
  refine ⟨hd, ?_⟩
  have hxy : x ≠ y := by
    intro h
    subst y
    omega
  have htwo : ({x, y} : Finset (TilingCell n)) ⊆ d := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hxd
    · exact hyd
  have hcardTwo : ({x, y} : Finset (TilingCell n)).card = 2 := by simp [hxy]
  have hcardLower : 2 ≤ d.card := by
    rw [← hcardTwo]
    exact Finset.card_le_card htwo
  obtain hsingle | hdomino := hvalid d hd
  · omega
  · exact hdomino.1

private theorem ff3_complete_tiling {n : ℕ} {D : Finset (Finset (TilingCell n))}
    (hD : ff3IsMatching D) : IsSquareDominoTiling (ff3Complete D) := by
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    simp only [ff3Complete, Finset.mem_union] at hd
    rcases hd with hd | hd
    · exact Or.inr (hD.1 d hd)
    · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hd
      exact Or.inl (by simp)
  · intro d₁ hd₁ d₂ hd₂ hne
    simp only [ff3Complete, Finset.mem_union] at hd₁ hd₂
    rcases hd₁ with hd₁ | hd₁ <;> rcases hd₂ with hd₂ | hd₂
    · exact hD.2 d₁ hd₁ d₂ hd₂ hne
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hd₂
      simp only [ff3Uncovered, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rw [Finset.disjoint_left]
      intro z hz hzx
      simp only [Finset.mem_singleton] at hzx
      subst z
      exact hx d₁ hd₁ hz
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hd₁
      simp only [ff3Uncovered, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rw [Finset.disjoint_left]
      intro z hzx hz
      simp only [Finset.mem_singleton] at hzx
      subst z
      exact hx d₂ hd₂ hz
    · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hd₁
      obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hd₂
      rw [Finset.disjoint_left]
      intro z hzx hzy
      simp only [Finset.mem_singleton] at hzx hzy
      subst z
      subst y
      exact hne rfl
  · intro x
    by_cases hx : ∃ d ∈ D, x ∈ d
    · obtain ⟨d, hd, hxd⟩ := hx
      exact ⟨d, Finset.mem_union_left _ hd, hxd⟩
    · refine ⟨{x}, Finset.mem_union_right _ ?_, by simp⟩
      apply Finset.mem_image.mpr
      refine ⟨x, ?_, rfl⟩
      simp only [ff3Uncovered, Finset.mem_filter, Finset.mem_univ, true_and]
      intro d hd hxd
      exact hx ⟨d, hd, hxd⟩

private theorem ff3_complete_faultFree {n : ℕ} {D : Finset (Finset (TilingCell n))}
    (hD : IsVerticalFaultFree D) : IsVerticalFaultFree (ff3Complete D) := by
  intro k hk
  obtain ⟨d, hd, rest⟩ := hD k hk
  exact ⟨d, Finset.mem_union_left _ hd, rest⟩

private theorem ff3_dominoes_complete {n : ℕ} {D : Finset (Finset (TilingCell n))}
    (hD : ff3IsMatching D) : ff3Dominoes (ff3Complete D) = D := by
  ext d
  constructor
  · intro hd
    simp only [ff3Dominoes, Finset.mem_filter, ff3Complete, Finset.mem_union] at hd
    obtain ⟨hd | hd, hcard⟩ := hd
    · exact hd
    · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hd
      simp at hcard
  · intro hd
    simp only [ff3Dominoes, Finset.mem_filter, ff3Complete, Finset.mem_union]
    exact ⟨Or.inl hd, (hD.1 d hd).1⟩

private theorem ff3_complete_dominoes {n : ℕ} {T : Finset (Finset (TilingCell n))}
    (hT : IsSquareDominoTiling T) : ff3Complete (ff3Dominoes T) = T := by
  ext d
  constructor
  · intro hd
    simp only [ff3Complete, Finset.mem_union] at hd
    rcases hd with hd | hd
    · exact (Finset.mem_filter.mp hd).1
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hd
      simp only [ff3Uncovered, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      obtain ⟨e, heT, hxe⟩ := hT.2.2 x
      rcases (isSquareOrDomino_iff e).mp (hT.1 e heT) with hsingle | hpair
      · obtain ⟨y, rfl⟩ := hsingle
        simp only [Finset.mem_singleton] at hxe
        subst y
        exact heT
      · obtain ⟨y, z, hyz, _, rfl⟩ := hpair
        have heDomino : {y, z} ∈ ff3Dominoes T := by
          simp [ff3Dominoes, heT, hyz]
        exact (hx {y, z} heDomino hxe).elim
  · intro hd
    rcases (isSquareOrDomino_iff d).mp (hT.1 d hd) with hsingle | hpair
    · obtain ⟨x, rfl⟩ := hsingle
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨x, ?_, rfl⟩
      simp only [ff3Uncovered, Finset.mem_filter, Finset.mem_univ, true_and]
      intro e he hxe
      obtain ⟨heT, hecard⟩ := Finset.mem_filter.mp he
      have hne : ({x} : Finset (TilingCell n)) ≠ e := by
        intro h
        subst e
        simp at hecard
      exact Finset.disjoint_left.mp (hT.2.1 {x} hd e heT hne) (by simp) hxe
    · obtain ⟨x, y, hxy, _, rfl⟩ := hpair
      apply Finset.mem_union_left
      simp [ff3Dominoes, hd, hxy]

private def ff3_tilingMatchingEquiv (n : ℕ) :
    ff3FaultFreeTilings n ≃ ff3FaultFreeMatchings n where
  toFun T := ⟨ff3Dominoes T, ff3_dominoes_matching T.property.1,
    ff3_dominoes_faultFree T.property.1.1 T.property.2⟩
  invFun D := ⟨ff3Complete D, ff3_complete_tiling D.property.1,
    ff3_complete_faultFree D.property.2⟩
  left_inv T := Subtype.ext (ff3_complete_dominoes T.property.1)
  right_inv D := Subtype.ext (ff3_dominoes_complete D.property.1)

private def ff3HorizontalDomino {n : ℕ} (r : Fin 3) (k : Fin n) :
    Finset (TilingCell (n + 1)) :=
  {(r, k.castSucc), (r, k.succ)}

private def ff3VerticalDomino {n : ℕ} (r : Fin 2) (k : Fin (n + 1)) :
    Finset (TilingCell (n + 1)) :=
  {(r.castSucc, k), (r.succ, k)}

private theorem ff3_horizontal_isDomino {n : ℕ} (r : Fin 3) (k : Fin n) :
    ff3IsDomino (ff3HorizontalDomino r k) := by
  refine ⟨?_, ?_⟩
  · simp [ff3HorizontalDomino, Fin.ext_iff]
  · intro x hx y hy hxy
    simp only [ff3HorizontalDomino, Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact (hxy rfl).elim
    · left
      simp
    · left
      simp
    · exact (hxy rfl).elim

private theorem ff3_vertical_isDomino {n : ℕ} (r : Fin 2) (k : Fin (n + 1)) :
    ff3IsDomino (ff3VerticalDomino r k) := by
  refine ⟨?_, ?_⟩
  · simp [ff3VerticalDomino, Fin.ext_iff]
  · intro x hx y hy hxy
    simp only [ff3VerticalDomino, Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact (hxy rfl).elim
    · right
      simp
    · right
      simp
    · exact (hxy rfl).elim

private theorem ff3_isDomino_iff {n : ℕ} (d : Finset (TilingCell (n + 1))) :
    ff3IsDomino d ↔
      (∃ r : Fin 3, ∃ k : Fin n, d = ff3HorizontalDomino r k) ∨
        ∃ r : Fin 2, ∃ k : Fin (n + 1), d = ff3VerticalDomino r k := by
  constructor
  · rintro ⟨hcard, hadj⟩
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hcard
    have hAdj := hadj x (by simp) y (by simp) hxy
    rcases hAdj with ⟨hrow, hcol⟩ | ⟨hcol, hrow⟩
    · rcases hcol with hxycol | hyxcol
      · left
        let k : Fin n := ⟨x.2.val, by omega⟩
        refine ⟨x.1, k, ?_⟩
        have hx0 : x = (x.1, k.castSucc) := by
          apply Prod.ext
          · rfl
          · rfl
        have hy1 : y = (x.1, k.succ) := by
          apply Prod.ext
          · exact hrow.symm
          · exact Fin.ext hxycol.symm
        rw [hx0, hy1]
        rfl
      · left
        let k : Fin n := ⟨y.2.val, by omega⟩
        refine ⟨y.1, k, ?_⟩
        have hy0 : y = (y.1, k.castSucc) := by
          apply Prod.ext
          · rfl
          · rfl
        have hx1 : x = (y.1, k.succ) := by
          apply Prod.ext
          · exact hrow
          · exact Fin.ext hyxcol.symm
        rw [hx1, hy0, Finset.pair_comm]
        rfl
    · rcases hrow with hxyrow | hyxrow
      · right
        let r : Fin 2 := ⟨x.1.val, by omega⟩
        refine ⟨r, x.2, ?_⟩
        have hx0 : x = (r.castSucc, x.2) := by
          apply Prod.ext
          · rfl
          · rfl
        have hy1 : y = (r.succ, x.2) := by
          apply Prod.ext
          · exact Fin.ext hxyrow.symm
          · exact hcol.symm
        rw [hx0, hy1]
        rfl
      · right
        let r : Fin 2 := ⟨y.1.val, by omega⟩
        refine ⟨r, y.2, ?_⟩
        have hy0 : y = (r.castSucc, y.2) := by
          apply Prod.ext
          · rfl
          · rfl
        have hx1 : x = (r.succ, y.2) := by
          apply Prod.ext
          · exact Fin.ext hyxrow.symm
          · exact hcol
        rw [hx1, hy0, Finset.pair_comm]
        rfl
  · rintro (⟨r, k, rfl⟩ | ⟨r, k, rfl⟩)
    · exact ff3_horizontal_isDomino r k
    · exact ff3_vertical_isDomino r k

private theorem ff3_horizontal_injective {n : ℕ} :
    Function.Injective (fun e : Fin 3 × Fin n ↦ ff3HorizontalDomino e.1 e.2) := by
  rintro ⟨r, k⟩ ⟨s, l⟩ h
  change ff3HorizontalDomino r k = ff3HorizontalDomino s l at h
  have h0 : (r, k.castSucc) ∈ ff3HorizontalDomino s l := by
    rw [← h]
    simp [ff3HorizontalDomino]
  have h1 : (r, k.succ) ∈ ff3HorizontalDomino s l := by
    rw [← h]
    simp [ff3HorizontalDomino]
  simp only [ff3HorizontalDomino, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at h0 h1
  rcases h0 with ⟨hrs, hkl⟩ | ⟨hrs, hkl⟩ <;>
    rcases h1 with ⟨_, hkl'⟩ | ⟨_, hkl'⟩
  · omega
  · apply Prod.ext
    · exact Fin.ext hrs
    · exact Fin.ext hkl
  · omega
  · omega

private theorem ff3_vertical_injective {n : ℕ} :
    Function.Injective (fun e : Fin 2 × Fin (n + 1) ↦ ff3VerticalDomino e.1 e.2) := by
  rintro ⟨r, k⟩ ⟨s, l⟩ h
  change ff3VerticalDomino r k = ff3VerticalDomino s l at h
  have h0 : (r.castSucc, k) ∈ ff3VerticalDomino s l := by
    rw [← h]
    simp [ff3VerticalDomino]
  have h1 : (r.succ, k) ∈ ff3VerticalDomino s l := by
    rw [← h]
    simp [ff3VerticalDomino]
  simp only [ff3VerticalDomino, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at h0 h1
  rcases h0 with ⟨hrs, hkl⟩ | ⟨hrs, hkl⟩ <;>
    rcases h1 with ⟨hrs', _⟩ | ⟨hrs', _⟩
  · omega
  · apply Prod.ext
    · exact Fin.ext hrs
    · exact Fin.ext hkl
  · omega
  · omega

private theorem ff3_horizontal_ne_vertical {n : ℕ} (r : Fin 3) (k : Fin n)
    (s : Fin 2) (j : Fin (n + 1)) :
    ff3HorizontalDomino r k ≠ ff3VerticalDomino s j := by
  intro h
  have h0 : (s.castSucc, j) ∈ ff3HorizontalDomino r k := by
    rw [h]
    simp [ff3VerticalDomino]
  have h1 : (s.succ, j) ∈ ff3HorizontalDomino r k := by
    rw [h]
    simp [ff3VerticalDomino]
  simp only [ff3HorizontalDomino, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at h0 h1
  rcases h0 with ⟨hsr, _⟩ | ⟨hsr, _⟩ <;>
    rcases h1 with ⟨hsr', _⟩ | ⟨hsr', _⟩ <;> omega

private abbrev ff3Edge (n : ℕ) :=
  (Fin 3 × Fin n) ⊕ (Fin 2 × Fin (n + 1))

private def ff3EdgeDomino {n : ℕ} : ff3Edge n → Finset (TilingCell (n + 1))
  | Sum.inl e => ff3HorizontalDomino e.1 e.2
  | Sum.inr e => ff3VerticalDomino e.1 e.2

private theorem ff3_edgeDomino_isDomino {n : ℕ} (e : ff3Edge n) :
    ff3IsDomino (ff3EdgeDomino e) := by
  rcases e with e | e
  · exact ff3_horizontal_isDomino e.1 e.2
  · exact ff3_vertical_isDomino e.1 e.2

private theorem ff3_edgeDomino_injective {n : ℕ} :
    Function.Injective (@ff3EdgeDomino n) := by
  intro e f h
  rcases e with e | e <;> rcases f with f | f
  · exact congrArg Sum.inl (ff3_horizontal_injective h)
  · exact (ff3_horizontal_ne_vertical e.1 e.2 f.1 f.2 h).elim
  · exact (ff3_horizontal_ne_vertical f.1 f.2 e.1 e.2 h.symm).elim
  · exact congrArg Sum.inr (ff3_vertical_injective h)

private def ff3EdgeDominoes {n : ℕ} (E : Finset (ff3Edge n)) :=
  E.image ff3EdgeDomino

private def ff3EdgesOf {n : ℕ} (D : Finset (Finset (TilingCell (n + 1)))) :=
  Finset.univ.filter fun e ↦ ff3EdgeDomino e ∈ D

private theorem ff3_edgeDominoes_edgesOf {n : ℕ}
    {D : Finset (Finset (TilingCell (n + 1)))} (hD : ∀ d ∈ D, ff3IsDomino d) :
    ff3EdgeDominoes (ff3EdgesOf D) = D := by
  ext d
  constructor
  · intro hd
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hd
    exact (Finset.mem_filter.mp he).2
  · intro hd
    rcases (ff3_isDomino_iff d).mp (hD d hd) with h | h
    · obtain ⟨r, k, rfl⟩ := h
      apply Finset.mem_image.mpr
      refine ⟨Sum.inl (r, k), ?_, rfl⟩
      simp only [ff3EdgesOf, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hd
    · obtain ⟨r, k, rfl⟩ := h
      apply Finset.mem_image.mpr
      refine ⟨Sum.inr (r, k), ?_, rfl⟩
      simp only [ff3EdgesOf, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hd

private theorem ff3_edgesOf_edgeDominoes {n : ℕ} (E : Finset (ff3Edge n)) :
    ff3EdgesOf (ff3EdgeDominoes E) = E := by
  ext e
  simp only [ff3EdgesOf, Finset.mem_filter, Finset.mem_univ, true_and,
    ff3EdgeDominoes, Finset.mem_image]
  constructor
  · rintro ⟨f, hf, hfe⟩
    exact (ff3_edgeDomino_injective hfe).symm ▸ hf
  · intro he
    exact ⟨e, he, rfl⟩

private def ff3IsEdgeMatching {n : ℕ} (E : Finset (ff3Edge n)) : Prop :=
  ∀ e ∈ E, ∀ f ∈ E, e ≠ f → Disjoint (ff3EdgeDomino e) (ff3EdgeDomino f)

private def ff3CrossesEveryCut {n : ℕ} (E : Finset (ff3Edge n)) : Prop :=
  ∀ k : Fin n, ∃ r : Fin 3, Sum.inl (r, k) ∈ E

private theorem ff3_edgeDominoes_matching_iff {n : ℕ} (E : Finset (ff3Edge n)) :
    ff3IsMatching (ff3EdgeDominoes E) ↔ ff3IsEdgeMatching E := by
  constructor
  · intro hD e he f hf hne
    apply hD.2 (ff3EdgeDomino e) (Finset.mem_image.mpr ⟨e, he, rfl⟩)
      (ff3EdgeDomino f) (Finset.mem_image.mpr ⟨f, hf, rfl⟩)
    exact fun h ↦ hne (ff3_edgeDomino_injective h)
  · intro hE
    refine ⟨?_, ?_⟩
    · intro d hd
      obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hd
      exact ff3_edgeDomino_isDomino e
    · intro d hd e he hde
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hd
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp he
      exact hE a ha b hb fun hab ↦ hde (congrArg ff3EdgeDomino hab)

private theorem ff3_fault_domino_eq_horizontal {n : ℕ}
    {d : Finset (TilingCell (n + 1))} (hd : ff3IsDomino d) {x y : TilingCell (n + 1)}
    (hx : x ∈ d) (hy : y ∈ d) (k : Fin n) (hrow : x.1 = y.1)
    (hxcol : x.2.val = k.val) (hycol : y.2.val = k.val + 1) :
    d = ff3HorizontalDomino x.1 k := by
  have hxy : x ≠ y := by
    intro h
    subst y
    omega
  have hsub : ({x, y} : Finset (TilingCell (n + 1))) ⊆ d := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  have hpair : ({x, y} : Finset (TilingCell (n + 1))) = d := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [hd.1]
    simp [hxy]
  have hx' : x = (x.1, k.castSucc) := by
    apply Prod.ext
    · rfl
    · exact Fin.ext hxcol
  have hy' : y = (x.1, k.succ) := by
    apply Prod.ext
    · exact hrow.symm
    · exact Fin.ext hycol
  rw [← hpair, hx', hy']
  rfl

private theorem ff3_edgeDominoes_faultFree_iff {n : ℕ} (E : Finset (ff3Edge n)) :
    IsVerticalFaultFree (ff3EdgeDominoes E) ↔ ff3CrossesEveryCut E := by
  constructor
  · intro h k
    obtain ⟨d, hd, x, hx, y, hy, hrow, hxcol, hycol⟩ := h k.val (by omega)
    obtain ⟨e, he, hdomino⟩ := Finset.mem_image.mp hd
    let k' : Fin n := ⟨k.val, k.isLt⟩
    have hdEq : d = ff3HorizontalDomino x.1 k' :=
      ff3_fault_domino_eq_horizontal (hdomino ▸ ff3_edgeDomino_isDomino e)
        hx hy k' hrow hxcol hycol
    have heEq : e = Sum.inl (x.1, k') := by
      apply ff3_edgeDomino_injective
      change ff3EdgeDomino e = ff3HorizontalDomino x.1 k'
      rw [hdomino, hdEq]
    refine ⟨x.1, ?_⟩
    simpa [k'] using heEq ▸ he
  · intro h k hk
    let k' : Fin n := ⟨k, by omega⟩
    obtain ⟨r, hr⟩ := h k'
    refine ⟨ff3HorizontalDomino r k', Finset.mem_image.mpr ⟨Sum.inl (r, k'), hr, rfl⟩,
      (r, k'.castSucc), by simp [ff3HorizontalDomino],
      (r, k'.succ), by simp [ff3HorizontalDomino], ?_⟩
    simp [k']

private abbrev ff3FaultFreeEdgeMatchings (n : ℕ) :=
  {E : Finset (ff3Edge n) // ff3IsEdgeMatching E ∧ ff3CrossesEveryCut E}

private def ff3_matchingEdgeEquiv (n : ℕ) :
    ff3FaultFreeEdgeMatchings n ≃ ff3FaultFreeMatchings (n + 1) where
  toFun E := ⟨ff3EdgeDominoes E,
    (ff3_edgeDominoes_matching_iff (n := n) E.1).mpr E.property.1,
    (ff3_edgeDominoes_faultFree_iff (n := n) E.1).mpr E.property.2⟩
  invFun D := by
    let E := ff3EdgesOf D.1
    have hEq : ff3EdgeDominoes E = D.1 :=
      ff3_edgeDominoes_edgesOf D.property.1.1
    refine ⟨E, ?_, ?_⟩
    · apply (ff3_edgeDominoes_matching_iff (n := n) E).mp
      rw [hEq]
      exact D.property.1
    · apply (ff3_edgeDominoes_faultFree_iff (n := n) E).mp
      rw [hEq]
      exact D.property.2
  left_inv E := by
    apply Subtype.ext
    change ff3EdgesOf (ff3EdgeDominoes E.1) = E.1
    exact ff3_edgesOf_edgeDominoes E.1
  right_inv D := by
    apply Subtype.ext
    change ff3EdgeDominoes (ff3EdgesOf D.1) = D.1
    exact ff3_edgeDominoes_edgesOf D.property.1.1

private abbrev ff3Profile := Fin 7

private def ff3ProfileRows : ff3Profile → Finset (Fin 3) := ![
  {0}, {1}, {0, 1}, {2}, {0, 2}, {1, 2}, {0, 1, 2}]

private theorem ff3_profileRows_nonempty (p : ff3Profile) :
    (ff3ProfileRows p).Nonempty := by
  fin_cases p <;> decide

private def ff3ProfileRows' (p : ff3Profile) :
    {s : Finset (Fin 3) // s.Nonempty} :=
  ⟨ff3ProfileRows p, ff3_profileRows_nonempty p⟩

private theorem ff3_profileRows_bijective : Function.Bijective ff3ProfileRows' := by
  decide

private noncomputable def ff3ProfileEquiv :
    ff3Profile ≃ {s : Finset (Fin 3) // s.Nonempty} :=
  Equiv.ofBijective ff3ProfileRows' ff3_profileRows_bijective

private def ff3VerticalRows : Option (Fin 2) → Finset (Fin 3)
  | none => ∅
  | some r => {r.castSucc, r.succ}

private abbrev ff3ColumnFilling (a b : Finset (Fin 3)) :=
  {v : Option (Fin 2) //
    Disjoint a b ∧
      Disjoint a (ff3VerticalRows v) ∧ Disjoint b (ff3VerticalRows v)}

private def ff3ColumnCount (a b : Finset (Fin 3)) :=
  Fintype.card (ff3ColumnFilling a b)

private def ff3Matrix (R : Type) [Semiring R] : Matrix ff3Profile ff3Profile R := !![
  0, 1, 0, 1, 0, 1, 0;
  1, 0, 0, 1, 1, 0, 0;
  0, 0, 0, 1, 0, 0, 0;
  1, 1, 1, 0, 0, 0, 0;
  0, 1, 0, 0, 0, 0, 0;
  1, 0, 0, 0, 0, 0, 0;
  0, 0, 0, 0, 0, 0, 0]

private def ff3Boundary (R : Type) [Semiring R] : ff3Profile → R :=
  ![2, 1, 1, 2, 1, 1, 1]

private theorem ff3_columnCount_profiles (p q : ff3Profile) :
    ff3ColumnCount (ff3ProfileRows p) (ff3ProfileRows q) = ff3Matrix ℕ p q := by
  fin_cases p <;> fin_cases q <;> decide

private theorem ff3_columnCount_left (p : ff3Profile) :
    ff3ColumnCount ∅ (ff3ProfileRows p) = ff3Boundary ℕ p := by
  fin_cases p <;> decide

private theorem ff3_columnCount_right (p : ff3Profile) :
    ff3ColumnCount (ff3ProfileRows p) ∅ = ff3Boundary ℕ p := by
  fin_cases p <;> decide

private theorem ff3_columnCount_empty : ff3ColumnCount ∅ ∅ = 3 := by
  decide

private def ff3Path (a : Finset (Fin 3)) : ℕ → Type
  | 0 => ff3ColumnFilling a ∅
  | n + 1 => Σ p : ff3Profile,
      ff3ColumnFilling a (ff3ProfileRows p) × ff3Path (ff3ProfileRows p) n

@[instance_reducible] private noncomputable def ff3PathFintypeDef :
    (a : Finset (Fin 3)) → (n : ℕ) → Fintype (ff3Path a n)
  | a, 0 => by
      change Fintype (ff3ColumnFilling a ∅)
      infer_instance
  | a, n + 1 => by
      change Fintype (Σ p : ff3Profile,
        ff3ColumnFilling a (ff3ProfileRows p) × ff3Path (ff3ProfileRows p) n)
      letI : ∀ p : ff3Profile, Fintype (ff3Path (ff3ProfileRows p) n) :=
        fun p ↦ ff3PathFintypeDef (ff3ProfileRows p) n
      infer_instance

private noncomputable instance ff3PathFintype (a : Finset (Fin 3)) (n : ℕ) :
    Fintype (ff3Path a n) := ff3PathFintypeDef a n

private def ff3TailCount (R : Type) [Semiring R] (n : ℕ) (p : ff3Profile) : R :=
  ∑ q, (ff3Matrix R ^ n) p q * ff3Boundary R q

private def ff3TransferCount (R : Type) [Semiring R] (n : ℕ) : R :=
  ∑ p, ff3Boundary R p * ff3TailCount R n p

private theorem ff3_card_path_rows (p : ff3Profile) : ∀ n,
    Nat.card (ff3Path (ff3ProfileRows p) n) = ff3TailCount ℕ n p := by
  intro n
  induction n generalizing p with
  | zero =>
      change Nat.card (ff3ColumnFilling (ff3ProfileRows p) ∅) = _
      rw [Nat.card_eq_fintype_card, show Fintype.card
        (ff3ColumnFilling (ff3ProfileRows p) ∅) =
          ff3ColumnCount (ff3ProfileRows p) ∅ from rfl, ff3_columnCount_right]
      classical
      simp [ff3TailCount, Matrix.one_apply]
  | succ n ih =>
      change Nat.card (Σ q : ff3Profile,
        ff3ColumnFilling (ff3ProfileRows p) (ff3ProfileRows q) ×
          ff3Path (ff3ProfileRows q) n) = _
      rw [Nat.card_sigma]
      simp_rw [Nat.card_prod]
      change (∑ q : ff3Profile,
        Nat.card (ff3ColumnFilling (ff3ProfileRows p) (ff3ProfileRows q)) *
          Nat.card (ff3Path (ff3ProfileRows q) n)) = _
      simp_rw [Nat.card_eq_fintype_card]
      change (∑ q : ff3Profile,
        ff3ColumnCount (ff3ProfileRows p) (ff3ProfileRows q) *
          Fintype.card (ff3Path (ff3ProfileRows q) n)) = _
      simp_rw [← Nat.card_eq_fintype_card, ff3_columnCount_profiles, ih]
      simp only [ff3TailCount, pow_succ', Matrix.mul_apply]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r _
      ring

private theorem ff3_card_path_empty_succ (n : ℕ) :
    Nat.card (ff3Path ∅ (n + 1)) = ff3TransferCount ℕ n := by
  change Nat.card (Σ p : ff3Profile,
    ff3ColumnFilling ∅ (ff3ProfileRows p) × ff3Path (ff3ProfileRows p) n) = _
  rw [Nat.card_sigma]
  simp_rw [Nat.card_prod]
  change (∑ p : ff3Profile, Nat.card (ff3ColumnFilling ∅ (ff3ProfileRows p)) *
    Nat.card (ff3Path (ff3ProfileRows p) n)) = _
  simp_rw [Nat.card_eq_fintype_card]
  change (∑ p : ff3Profile, ff3ColumnCount ∅ (ff3ProfileRows p) *
    Fintype.card (ff3Path (ff3ProfileRows p) n)) = _
  simp_rw [← Nat.card_eq_fintype_card, ff3_columnCount_left, ff3_card_path_rows]
  rfl

private theorem ff3_card_path_empty_zero : Nat.card (ff3Path ∅ 0) = 3 := by
  change Nat.card (ff3ColumnFilling ∅ ∅) = 3
  rw [Nat.card_eq_fintype_card]
  exact ff3_columnCount_empty

private theorem ff3_matrix_cast_entry (p q : ff3Profile) :
    ((ff3Matrix ℕ p q : ℕ) : ℤ) = ff3Matrix ℤ p q := by
  fin_cases p <;> fin_cases q <;> rfl

private theorem ff3_boundary_cast (p : ff3Profile) :
    ((ff3Boundary ℕ p : ℕ) : ℤ) = ff3Boundary ℤ p := by
  fin_cases p <;> rfl

private theorem ff3_matrix_pow_cast (n : ℕ) (p q : ff3Profile) :
    (((ff3Matrix ℕ ^ n) p q : ℕ) : ℤ) = (ff3Matrix ℤ ^ n) p q := by
  have hmap := Matrix.map_pow (ff3Matrix ℕ) Int.ofNatHom n
  have hM : (ff3Matrix ℕ).map (⇑Int.ofNatHom) = ff3Matrix ℤ := by
    ext i j
    exact ff3_matrix_cast_entry i j
  have h := congrFun (congrFun hmap p) q
  rw [hM] at h
  change (((ff3Matrix ℕ ^ n) p q : ℕ) : ℤ) = (ff3Matrix ℤ ^ n) p q at h
  exact h

private theorem ff3_transfer_cast (n : ℕ) :
    ((ff3TransferCount ℕ n : ℕ) : ℤ) = ff3TransferCount ℤ n := by
  simp only [ff3TransferCount, ff3TailCount, Nat.cast_sum, Nat.cast_mul]
  simp_rw [ff3_matrix_pow_cast, ff3_boundary_cast]

set_option maxHeartbeats 1000000 in
-- The concrete 7 by 7 calculation exceeds the default heartbeat budget.
private theorem ff3_matrix_annihilates (p q : ff3Profile) :
    (ff3Matrix ℤ ^ 5) p q - (ff3Matrix ℤ ^ 4) p q -
      4 * (ff3Matrix ℤ ^ 3) p q + (ff3Matrix ℤ ^ 2) p q + ff3Matrix ℤ p q = 0 := by
  fin_cases p <;> fin_cases q <;> decide

private theorem ff3_matrix_polynomial :
    ff3Matrix ℤ ^ 5 = ff3Matrix ℤ ^ 4 + (4 : ℤ) • ff3Matrix ℤ ^ 3 -
      ff3Matrix ℤ ^ 2 - ff3Matrix ℤ := by
  ext p q
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply]
  simp only [smul_eq_mul]
  have h := ff3_matrix_annihilates p q
  omega

private theorem ff3_matrix_power_recurrence (n : ℕ) :
    ff3Matrix ℤ ^ (n + 5) = ff3Matrix ℤ ^ (n + 4) +
      (4 : ℤ) • ff3Matrix ℤ ^ (n + 3) - ff3Matrix ℤ ^ (n + 2) -
        ff3Matrix ℤ ^ (n + 1) := by
  rw [pow_add, pow_add, pow_add, pow_add, pow_add, ff3_matrix_polynomial]
  simp only [mul_sub, mul_add, mul_smul_comm]
  simp

private theorem ff3_transfer_recurrence (n : ℕ) :
    ff3TransferCount ℤ (n + 5) = ff3TransferCount ℤ (n + 4) +
      4 * ff3TransferCount ℤ (n + 3) - ff3TransferCount ℤ (n + 2) -
        ff3TransferCount ℤ (n + 1) := by
  have h := ff3_matrix_power_recurrence n
  let L : Matrix ff3Profile ff3Profile ℤ → ℤ := fun A =>
    ∑ p, ff3Boundary ℤ p * ∑ q, A p q * ff3Boundary ℤ q
  have L_add (A B : Matrix ff3Profile ff3Profile ℤ) : L (A + B) = L A + L B := by
    simp [L, Matrix.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
  have L_sub (A B : Matrix ff3Profile ff3Profile ℤ) : L (A - B) = L A - L B := by
    simp [L, Matrix.sub_apply, sub_mul, mul_sub, Finset.sum_sub_distrib]
  have L_smul (A : Matrix ff3Profile ff3Profile ℤ) : L ((4 : ℤ) • A) = 4 * L A := by
    simp only [L, Matrix.smul_apply]
    simp only [smul_eq_mul]
    simp_rw [Finset.mul_sum]
    ring_nf
  change L (ff3Matrix ℤ ^ (n + 5)) = L (ff3Matrix ℤ ^ (n + 4)) +
    4 * L (ff3Matrix ℤ ^ (n + 3)) - L (ff3Matrix ℤ ^ (n + 2)) -
      L (ff3Matrix ℤ ^ (n + 1))
  rw [h]
  rw [L_sub, L_sub, L_add, L_smul]

private theorem ff3_transfer_zero : ff3TransferCount ℕ 0 = 13 := by decide
private theorem ff3_transfer_one : ff3TransferCount ℕ 1 = 26 := by decide
private theorem ff3_transfer_two : ff3TransferCount ℕ 2 = 66 := by decide
private theorem ff3_transfer_three : ff3TransferCount ℕ 3 = 154 := by decide
private theorem ff3_transfer_four : ff3TransferCount ℕ 4 = 380 := by decide

private def ff3Incoming {n : ℕ} (a : Finset (Fin 3)) (p : Fin n → ff3Profile)
    (j : Fin (n + 1)) : Finset (Fin 3) :=
  if h : j.val = 0 then a else ff3ProfileRows (p ⟨j.val - 1, by omega⟩)

private def ff3Outgoing {n : ℕ} (p : Fin n → ff3Profile)
    (j : Fin (n + 1)) : Finset (Fin 3) :=
  if h : j.val < n then ff3ProfileRows (p ⟨j.val, h⟩) else ∅

private theorem ff3_outgoing_castSucc {n : ℕ} (p : Fin n → ff3Profile) (k : Fin n) :
    ff3Outgoing p k.castSucc = ff3ProfileRows (p k) := by
  simp only [ff3Outgoing, Fin.val_castSucc, k.isLt, ↓reduceDIte]

private theorem ff3_incoming_succ {n : ℕ} (a : Finset (Fin 3))
    (p : Fin n → ff3Profile) (k : Fin n) :
    ff3Incoming a p k.succ = ff3ProfileRows (p k) := by
  simp only [ff3Incoming, Fin.val_succ, Nat.add_eq_zero_iff, one_ne_zero, and_false,
    ↓reduceDIte]
  congr

private abbrev ff3Code (a : Finset (Fin 3)) (n : ℕ) :=
  Σ p : Fin n → ff3Profile,
    ∀ j : Fin (n + 1), ff3ColumnFilling (ff3Incoming a p j) (ff3Outgoing p j)

private noncomputable def ff3CodeEdges {n : ℕ} (c : ff3Code ∅ n) :
    Finset (ff3Edge n) := by
  classical
  exact Finset.univ.filter fun e ↦ match e with
      | Sum.inl e => e.1 ∈ ff3ProfileRows (c.1 e.2)
      | Sum.inr e => (c.2 e.2).1 = some e.1

private theorem ff3_mem_codeEdges_horizontal {n : ℕ} (c : ff3Code ∅ n)
    (r : Fin 3) (k : Fin n) :
    Sum.inl (r, k) ∈ ff3CodeEdges c ↔ r ∈ ff3ProfileRows (c.1 k) := by
  classical
  simp [ff3CodeEdges]

private theorem ff3_mem_codeEdges_vertical {n : ℕ} (c : ff3Code ∅ n) (r : Fin 2)
    (j : Fin (n + 1)) :
    Sum.inr (r, j) ∈ ff3CodeEdges c ↔ (c.2 j).1 = some r := by
  classical
  simp [ff3CodeEdges]

private theorem ff3_code_adjacent_disjoint {n : ℕ} (c : ff3Code ∅ n) (l k : Fin n)
    (h : l.succ = k.castSucc) :
    Disjoint (ff3ProfileRows (c.1 l)) (ff3ProfileRows (c.1 k)) := by
  have hd := (c.2 l.succ).property.1
  rw [ff3_incoming_succ] at hd
  rw [h, ff3_outgoing_castSucc] at hd
  exact hd

private theorem ff3_code_out_vertical_disjoint {n : ℕ} (c : ff3Code ∅ n) (k : Fin n) :
    Disjoint (ff3ProfileRows (c.1 k)) (ff3VerticalRows (c.2 k.castSucc).1) := by
  have hd := (c.2 k.castSucc).property.2.2
  simpa only [ff3_outgoing_castSucc] using hd

private theorem ff3_code_in_vertical_disjoint {n : ℕ} (c : ff3Code ∅ n) (k : Fin n) :
    Disjoint (ff3ProfileRows (c.1 k)) (ff3VerticalRows (c.2 k.succ).1) := by
  have hd := (c.2 k.succ).property.2.1
  simpa only [ff3_incoming_succ] using hd

private theorem ff3_code_horizontal_vertical_disjoint {n : ℕ} (c : ff3Code ∅ n)
    (r : Fin 3) (k : Fin n) (s : Fin 2) (j : Fin (n + 1))
    (hr : r ∈ ff3ProfileRows (c.1 k)) (hs : (c.2 j).1 = some s) :
    Disjoint (ff3HorizontalDomino r k) (ff3VerticalDomino s j) := by
  rw [Finset.disjoint_left]
  intro x hx hxs
  simp only [ff3HorizontalDomino, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · simp only [ff3VerticalDomino, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at hxs
    rcases hxs with ⟨hrow, hcol⟩ | ⟨hrow, hcol⟩
    · have hj : j = k.castSucc := Fin.ext hcol.symm
      subst j
      have hrv : r ∈ ff3VerticalRows (c.2 k.castSucc).1 := by
        rw [hs]
        simp [ff3VerticalRows, Fin.ext_iff, hrow]
      exact Finset.disjoint_left.mp (ff3_code_out_vertical_disjoint c k) hr hrv
    · have hj : j = k.castSucc := Fin.ext hcol.symm
      subst j
      have hrv : r ∈ ff3VerticalRows (c.2 k.castSucc).1 := by
        rw [hs]
        simp [ff3VerticalRows, Fin.ext_iff, hrow]
      exact Finset.disjoint_left.mp (ff3_code_out_vertical_disjoint c k) hr hrv
  · simp only [ff3VerticalDomino, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at hxs
    rcases hxs with ⟨hrow, hcol⟩ | ⟨hrow, hcol⟩
    · have hj : j = k.succ := Fin.ext hcol.symm
      subst j
      have hrv : r ∈ ff3VerticalRows (c.2 k.succ).1 := by
        rw [hs]
        simp [ff3VerticalRows, Fin.ext_iff, hrow]
      exact Finset.disjoint_left.mp (ff3_code_in_vertical_disjoint c k) hr hrv
    · have hj : j = k.succ := Fin.ext hcol.symm
      subst j
      have hrv : r ∈ ff3VerticalRows (c.2 k.succ).1 := by
        rw [hs]
        simp [ff3VerticalRows, Fin.ext_iff, hrow]
      exact Finset.disjoint_left.mp (ff3_code_in_vertical_disjoint c k) hr hrv

private theorem ff3_code_horizontal_disjoint {n : ℕ} (c : ff3Code ∅ n)
    (r s : Fin 3) (k l : Fin n) (hr : r ∈ ff3ProfileRows (c.1 k))
    (hs : s ∈ ff3ProfileRows (c.1 l)) (hne : (r, k) ≠ (s, l)) :
    Disjoint (ff3HorizontalDomino r k) (ff3HorizontalDomino s l) := by
  rw [Finset.disjoint_left]
  intro x hx hxs
  simp only [ff3HorizontalDomino, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · simp only [ff3HorizontalDomino, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at hxs
    rcases hxs with ⟨hrow, hcol⟩ | ⟨hrow, hcol⟩
    · apply hne
      exact Prod.ext (Fin.ext hrow) (Fin.ext hcol)
    · have hkl : l.succ = k.castSucc := Fin.ext hcol.symm
      have hd := ff3_code_adjacent_disjoint c l k hkl
      have hrs : r = s := Fin.ext hrow
      subst s
      exact Finset.disjoint_left.mp hd hs hr
  · simp only [ff3HorizontalDomino, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at hxs
    rcases hxs with ⟨hrow, hcol⟩ | ⟨hrow, hcol⟩
    · have hkl : k.succ = l.castSucc := Fin.ext hcol
      have hd := ff3_code_adjacent_disjoint c k l hkl
      have hrs : r = s := Fin.ext hrow
      subst s
      exact Finset.disjoint_left.mp hd hr hs
    · apply hne
      exact Prod.ext (Fin.ext hrow) (Fin.ext (Nat.add_right_cancel hcol))

private theorem ff3_code_vertical_disjoint {n : ℕ} (c : ff3Code ∅ n)
    (r s : Fin 2) (j l : Fin (n + 1)) (hr : (c.2 j).1 = some r)
    (hs : (c.2 l).1 = some s) (hne : (r, j) ≠ (s, l)) :
    Disjoint (ff3VerticalDomino r j) (ff3VerticalDomino s l) := by
  rw [Finset.disjoint_left]
  intro x hx hxs
  simp only [ff3VerticalDomino, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · simp only [ff3VerticalDomino, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq] at hxs
    rcases hxs with ⟨_, hcol⟩ | ⟨_, hcol⟩ <;>
      subst l <;> exact hne (congrArg (fun t ↦ (t, j)) (Option.some.inj (hr.symm.trans hs)))
  · simp only [ff3VerticalDomino, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq] at hxs
    rcases hxs with ⟨_, hcol⟩ | ⟨_, hcol⟩ <;>
      subst l <;> exact hne (congrArg (fun t ↦ (t, j)) (Option.some.inj (hr.symm.trans hs)))

private theorem ff3_codeEdges_isMatching {n : ℕ} (c : ff3Code ∅ n) :
    ff3IsEdgeMatching (ff3CodeEdges c) := by
  intro e he f hf hne
  rcases e with e | e <;> rcases f with f | f
  · exact ff3_code_horizontal_disjoint c e.1 f.1 e.2 f.2
      ((ff3_mem_codeEdges_horizontal c e.1 e.2).mp he)
      ((ff3_mem_codeEdges_horizontal c f.1 f.2).mp hf)
      (fun h ↦ hne (congrArg Sum.inl h))
  · exact ff3_code_horizontal_vertical_disjoint c e.1 e.2 f.1 f.2
      ((ff3_mem_codeEdges_horizontal c e.1 e.2).mp he)
      ((ff3_mem_codeEdges_vertical c f.1 f.2).mp hf)
  · exact Disjoint.symm <| ff3_code_horizontal_vertical_disjoint c f.1 f.2 e.1 e.2
      ((ff3_mem_codeEdges_horizontal c f.1 f.2).mp hf)
      ((ff3_mem_codeEdges_vertical c e.1 e.2).mp he)
  · exact ff3_code_vertical_disjoint c e.1 f.1 e.2 f.2
      ((ff3_mem_codeEdges_vertical c e.1 e.2).mp he)
      ((ff3_mem_codeEdges_vertical c f.1 f.2).mp hf)
      (fun h ↦ hne (congrArg Sum.inr h))

private theorem ff3_codeEdges_crosses {n : ℕ} (c : ff3Code ∅ n) :
    ff3CrossesEveryCut (ff3CodeEdges c) := by
  intro k
  obtain ⟨r, hr⟩ := ff3_profileRows_nonempty (c.1 k)
  exact ⟨r, (ff3_mem_codeEdges_horizontal c r k).mpr hr⟩

private def ff3EdgeProfileRows {n : ℕ} (E : ff3FaultFreeEdgeMatchings n) (k : Fin n) :
    Finset (Fin 3) :=
  Finset.univ.filter fun r ↦ Sum.inl (r, k) ∈ E.1

private theorem ff3_edgeProfileRows_nonempty {n : ℕ} (E : ff3FaultFreeEdgeMatchings n)
    (k : Fin n) : (ff3EdgeProfileRows E k).Nonempty := by
  obtain ⟨r, hr⟩ := E.property.2 k
  exact ⟨r, by simp [ff3EdgeProfileRows, hr]⟩

private noncomputable def ff3EdgeProfile {n : ℕ} (E : ff3FaultFreeEdgeMatchings n)
    (k : Fin n) : ff3Profile :=
  ff3ProfileEquiv.symm ⟨ff3EdgeProfileRows E k, ff3_edgeProfileRows_nonempty E k⟩

private theorem ff3_mem_edgeProfile {n : ℕ} (E : ff3FaultFreeEdgeMatchings n)
    (r : Fin 3) (k : Fin n) :
    r ∈ ff3ProfileRows (ff3EdgeProfile E k) ↔ Sum.inl (r, k) ∈ E.1 := by
  have h := congrArg Subtype.val
    (ff3ProfileEquiv.apply_symm_apply
      ⟨ff3EdgeProfileRows E k, ff3_edgeProfileRows_nonempty E k⟩)
  rw [show ff3ProfileRows (ff3EdgeProfile E k) = ff3EdgeProfileRows E k from h]
  simp [ff3EdgeProfileRows]

private theorem ff3_edge_no_both_vertical {n : ℕ} (E : ff3FaultFreeEdgeMatchings n)
    (j : Fin (n + 1)) :
    ¬(Sum.inr ((0 : Fin 2), j) ∈ E.1 ∧ Sum.inr ((1 : Fin 2), j) ∈ E.1) := by
  rintro ⟨h0, h1⟩
  have hne : (Sum.inr ((0 : Fin 2), j) : ff3Edge n) ≠ Sum.inr ((1 : Fin 2), j) := by
    simp
  have hd := E.property.1 _ h0 _ h1 hne
  have hm0 : ((1 : Fin 3), j) ∈ ff3EdgeDomino (Sum.inr ((0 : Fin 2), j)) := by
    simp [ff3EdgeDomino, ff3VerticalDomino]
  have hm1 : ((1 : Fin 3), j) ∈ ff3EdgeDomino (Sum.inr ((1 : Fin 2), j)) := by
    simp [ff3EdgeDomino, ff3VerticalDomino]
  exact Finset.disjoint_left.mp hd hm0 hm1

private noncomputable def ff3EdgeVertical {n : ℕ} (E : ff3FaultFreeEdgeMatchings n)
    (j : Fin (n + 1)) : Option (Fin 2) :=
  if Sum.inr ((0 : Fin 2), j) ∈ E.1 then some 0
  else if Sum.inr ((1 : Fin 2), j) ∈ E.1 then some 1 else none

private theorem ff3_edgeVertical_eq_some_iff {n : ℕ} (E : ff3FaultFreeEdgeMatchings n)
    (r : Fin 2) (j : Fin (n + 1)) :
    ff3EdgeVertical E j = some r ↔ Sum.inr (r, j) ∈ E.1 := by
  fin_cases r
  · simp [ff3EdgeVertical]
  · by_cases h0 : Sum.inr ((0 : Fin 2), j) ∈ E.1
    · have h1 : Sum.inr ((1 : Fin 2), j) ∉ E.1 := by
        intro h
        exact ff3_edge_no_both_vertical E j ⟨h0, h⟩
      simp [ff3EdgeVertical, h0, h1]
    · simp [ff3EdgeVertical, h0]

private noncomputable def ff3EdgeFilling {n : ℕ} (E : ff3FaultFreeEdgeMatchings n)
    (j : Fin (n + 1)) :
    ff3ColumnFilling (ff3Incoming ∅ (ff3EdgeProfile E) j)
      (ff3Outgoing (ff3EdgeProfile E) j) := by
  refine ⟨ff3EdgeVertical E j, ?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro r hin hout
    simp only [ff3Incoming] at hin
    split at hin
    · simp at hin
    · rename_i hj0
      simp only [ff3Outgoing] at hout
      split at hout
      · rename_i hjn
        let l : Fin n := ⟨j.val - 1, by omega⟩
        let k : Fin n := ⟨j.val, hjn⟩
        have hil : Sum.inl (r, l) ∈ E.1 := by
          apply (ff3_mem_edgeProfile E r l).mp
          simpa [l] using hin
        have hik : Sum.inl (r, k) ∈ E.1 := by
          apply (ff3_mem_edgeProfile E r k).mp
          simpa [k] using hout
        have hne : (Sum.inl (r, l) : ff3Edge n) ≠ Sum.inl (r, k) := by
          intro h
          injection h with h
          have := congrArg (fun e ↦ e.2.val) h
          simp [l, k] at this
          omega
        have hd := E.property.1 _ hil _ hik hne
        have hjl : l.succ = j := Fin.ext (by simp [l]; omega)
        have hjk : k.castSucc = j := Fin.ext (by simp [k])
        have hmil : (r, j) ∈ ff3EdgeDomino (Sum.inl (r, l)) := by
          simp [ff3EdgeDomino, ff3HorizontalDomino, ← hjl]
        have hmik : (r, j) ∈ ff3EdgeDomino (Sum.inl (r, k)) := by
          simp [ff3EdgeDomino, ff3HorizontalDomino, ← hjk]
        exact Finset.disjoint_left.mp hd hmil hmik
      · simp at hout
  · rw [Finset.disjoint_left]
    intro r hin hrv
    simp only [ff3Incoming] at hin
    split at hin
    · simp at hin
    · rename_i hj0
      let l : Fin n := ⟨j.val - 1, by omega⟩
      have hil : Sum.inl (r, l) ∈ E.1 := by
        apply (ff3_mem_edgeProfile E r l).mp
        simpa [l] using hin
      cases hv : ff3EdgeVertical E j with
      | none => simp [hv, ff3VerticalRows] at hrv
      | some s =>
          have his : Sum.inr (s, j) ∈ E.1 :=
            (ff3_edgeVertical_eq_some_iff E s j).mp hv
          have hd := E.property.1 _ hil _ his (by simp)
          have hjl : l.succ = j := Fin.ext (by simp [l]; omega)
          have hmil : (r, j) ∈ ff3EdgeDomino (Sum.inl (r, l)) := by
            simp [ff3EdgeDomino, ff3HorizontalDomino, ← hjl]
          have hmis : (r, j) ∈ ff3EdgeDomino (Sum.inr (s, j)) := by
            change (r, j) ∈ ff3VerticalDomino s j
            simpa [ff3VerticalDomino, ff3VerticalRows, hv] using hrv
          exact Finset.disjoint_left.mp hd hmil hmis
  · rw [Finset.disjoint_left]
    intro r hout hrv
    simp only [ff3Outgoing] at hout
    split at hout
    · rename_i hjn
      let k : Fin n := ⟨j.val, hjn⟩
      have hik : Sum.inl (r, k) ∈ E.1 := by
        apply (ff3_mem_edgeProfile E r k).mp
        simpa [k] using hout
      cases hv : ff3EdgeVertical E j with
      | none => simp [hv, ff3VerticalRows] at hrv
      | some s =>
          have his : Sum.inr (s, j) ∈ E.1 :=
            (ff3_edgeVertical_eq_some_iff E s j).mp hv
          have hd := E.property.1 _ hik _ his (by simp)
          have hjk : k.castSucc = j := Fin.ext (by simp [k])
          have hmik : (r, j) ∈ ff3EdgeDomino (Sum.inl (r, k)) := by
            simp [ff3EdgeDomino, ff3HorizontalDomino, ← hjk]
          have hmis : (r, j) ∈ ff3EdgeDomino (Sum.inr (s, j)) := by
            change (r, j) ∈ ff3VerticalDomino s j
            simpa [ff3VerticalDomino, ff3VerticalRows, hv] using hrv
          exact Finset.disjoint_left.mp hd hmik hmis
    · simp at hout

private noncomputable def ff3EdgeCode {n : ℕ} (E : ff3FaultFreeEdgeMatchings n) :
    ff3Code ∅ n :=
  ⟨ff3EdgeProfile E, ff3EdgeFilling E⟩

private theorem ff3_profileRows_injective : Function.Injective ff3ProfileRows := by
  intro p q h
  exact ff3_profileRows_bijective.1 (Subtype.ext h)

private theorem ff3_code_ext {a : Finset (Fin 3)} {n : ℕ} {c d : ff3Code a n}
    (hp : c.1 = d.1) (hv : ∀ j, (c.2 j).1 = (d.2 j).1) : c = d := by
  obtain ⟨p, f⟩ := c
  obtain ⟨q, g⟩ := d
  dsimp at hp hv
  subst q
  have hfg : f = g := by
    funext j
    exact Subtype.ext (hv j)
  subst g
  rfl

private theorem ff3_codeEdges_edgeCode {n : ℕ} (E : ff3FaultFreeEdgeMatchings n) :
    ff3CodeEdges (ff3EdgeCode E) = E.1 := by
  ext e
  rcases e with e | e
  · rw [ff3_mem_codeEdges_horizontal]
    change e.1 ∈ ff3ProfileRows (ff3EdgeProfile E e.2) ↔ Sum.inl e ∈ E.1
    exact ff3_mem_edgeProfile E e.1 e.2
  · rw [ff3_mem_codeEdges_vertical]
    change ff3EdgeVertical E e.2 = some e.1 ↔ _
    exact ff3_edgeVertical_eq_some_iff E e.1 e.2

private theorem ff3_edgeCode_codeEdges {n : ℕ} (c : ff3Code ∅ n) :
    ff3EdgeCode ⟨ff3CodeEdges c, ff3_codeEdges_isMatching c, ff3_codeEdges_crosses c⟩ = c := by
  let E : ff3FaultFreeEdgeMatchings n :=
    ⟨ff3CodeEdges c, ff3_codeEdges_isMatching c, ff3_codeEdges_crosses c⟩
  apply ff3_code_ext
  · funext k
    apply ff3_profileRows_injective
    ext r
    change r ∈ ff3ProfileRows (ff3EdgeProfile E k) ↔ r ∈ ff3ProfileRows (c.1 k)
    rw [ff3_mem_edgeProfile]
    exact ff3_mem_codeEdges_horizontal c r k
  · intro j
    change ff3EdgeVertical E j = (c.2 j).1
    cases hv : (c.2 j).1 with
    | none =>
        cases he : ff3EdgeVertical E j with
        | none => rfl
        | some r =>
            have hrE : Sum.inr (r, j) ∈ E.1 :=
              (ff3_edgeVertical_eq_some_iff E r j).mp he
            have hrc : (c.2 j).1 = some r :=
              (ff3_mem_codeEdges_vertical c r j).mp hrE
            rw [hv] at hrc
            contradiction
    | some r =>
        apply (ff3_edgeVertical_eq_some_iff E r j).mpr
        exact (ff3_mem_codeEdges_vertical c r j).mpr hv

private noncomputable def ff3CodeEdgeEquiv (n : ℕ) :
    ff3Code ∅ n ≃ ff3FaultFreeEdgeMatchings n where
  toFun c := ⟨ff3CodeEdges c, ff3_codeEdges_isMatching c, ff3_codeEdges_crosses c⟩
  invFun E := ff3EdgeCode E
  left_inv := ff3_edgeCode_codeEdges
  right_inv E := Subtype.ext (ff3_codeEdges_edgeCode E)

private theorem ff3_incoming_tail {a : Finset (Fin 3)} {n : ℕ}
    (p : Fin (n + 1) → ff3Profile) (j : Fin (n + 1)) :
    ff3Incoming (ff3ProfileRows (p 0)) (Fin.tail p) j = ff3Incoming a p j.succ := by
  refine Fin.cases ?_ (fun k ↦ ?_) j
  · simp [ff3Incoming]
  · simp [ff3Incoming]
    congr

private theorem ff3_outgoing_tail {n : ℕ} (p : Fin (n + 1) → ff3Profile)
    (j : Fin (n + 1)) : ff3Outgoing (Fin.tail p) j = ff3Outgoing p j.succ := by
  simp [ff3Outgoing, Fin.tail]

private theorem ff3_incoming_cons_succ {a : Finset (Fin 3)} {n : ℕ} (p : ff3Profile)
    (q : Fin n → ff3Profile) (j : Fin (n + 1)) :
    ff3Incoming a (Fin.cons p q) j.succ = ff3Incoming (ff3ProfileRows p) q j := by
  refine Fin.cases ?_ (fun k ↦ ?_) j
  · simp [ff3Incoming, Fin.cons]
  · simp [ff3Incoming, Fin.cons]

private theorem ff3_outgoing_cons_succ {n : ℕ} (p : ff3Profile) (q : Fin n → ff3Profile)
    (j : Fin (n + 1)) : ff3Outgoing (Fin.cons p q) j.succ = ff3Outgoing q j := by
  simp [ff3Outgoing, Fin.cons]

private def ff3CodeHeadFilling {a : Finset (Fin 3)} {n : ℕ} (c : ff3Code a (n + 1)) :
    ff3ColumnFilling a (ff3ProfileRows (c.1 0)) := by
  simpa [ff3Incoming, ff3Outgoing] using c.2 0

private def ff3CodeTail {a : Finset (Fin 3)} {n : ℕ} (c : ff3Code a (n + 1)) :
    ff3Code (ff3ProfileRows (c.1 0)) n := by
  refine ⟨Fin.tail c.1, fun j ↦ ?_⟩
  refine ⟨(c.2 j.succ).1, ?_⟩
  rw [ff3_incoming_tail (a := a) c.1 j, ff3_outgoing_tail c.1 j]
  exact (c.2 j.succ).property

private def ff3CodeCons {a : Finset (Fin 3)} {n : ℕ} (p : ff3Profile)
    (f : ff3ColumnFilling a (ff3ProfileRows p))
    (c : ff3Code (ff3ProfileRows p) n) : ff3Code a (n + 1) := by
  refine ⟨Fin.cons p c.1, fun j ↦ Fin.cases ?_ (fun k ↦ ?_) j⟩
  · refine ⟨f.1, ?_⟩
    simpa [ff3Incoming, ff3Outgoing] using f.property
  · refine ⟨(c.2 k).1, ?_⟩
    simpa only [ff3_incoming_cons_succ, ff3_outgoing_cons_succ] using (c.2 k).property

private theorem ff3_codeCons_head_tail {a : Finset (Fin 3)} {n : ℕ}
    (c : ff3Code a (n + 1)) :
    ff3CodeCons (c.1 0) (ff3CodeHeadFilling c) (ff3CodeTail c) = c := by
  apply ff3_code_ext
  · exact Fin.cons_self_tail c.1
  · intro j
    refine Fin.cases ?_ (fun k ↦ ?_) j
    · rfl
    · rfl

private theorem ff3_codeHeadFilling_cons {a : Finset (Fin 3)} {n : ℕ} (p : ff3Profile)
    (f : ff3ColumnFilling a (ff3ProfileRows p))
    (c : ff3Code (ff3ProfileRows p) n) :
    ff3CodeHeadFilling (ff3CodeCons p f c) = f := by
  apply Subtype.ext
  rfl

private theorem ff3_codeTail_cons {a : Finset (Fin 3)} {n : ℕ} (p : ff3Profile)
    (f : ff3ColumnFilling a (ff3ProfileRows p))
    (c : ff3Code (ff3ProfileRows p) n) : ff3CodeTail (ff3CodeCons p f c) = c := by
  apply ff3_code_ext
  · funext j
    rfl
  · intro j
    rfl

private def ff3CodeZeroFilling {a : Finset (Fin 3)} (c : ff3Code a 0) :
    ff3ColumnFilling a ∅ := by
  refine ⟨(c.2 0).1, ?_⟩
  simpa [ff3Incoming, ff3Outgoing] using (c.2 0).property

private def ff3FillingCodeZero {a : Finset (Fin 3)} (f : ff3ColumnFilling a ∅) :
    ff3Code a 0 := by
  refine ⟨Fin.elim0, fun j ↦ ?_⟩
  refine ⟨f.1, ?_⟩
  have hj : j = 0 := Fin.eq_zero j
  subst j
  simpa [ff3Incoming, ff3Outgoing] using f.property

private def ff3CodeZeroEquiv (a : Finset (Fin 3)) : ff3Code a 0 ≃ ff3Path a 0 where
  toFun := ff3CodeZeroFilling
  invFun := ff3FillingCodeZero
  left_inv c := by
    apply ff3_code_ext
    · funext j
      exact Fin.elim0 j
    · intro j
      have hj : j = 0 := Fin.eq_zero j
      subst j
      rfl
  right_inv f := Subtype.ext rfl

private noncomputable def ff3CodePathEquiv :
    (a : Finset (Fin 3)) → (n : ℕ) → ff3Code a n ≃ ff3Path a n
  | a, 0 => ff3CodeZeroEquiv a
  | a, n + 1 =>
      { toFun := fun c ↦
          ⟨c.1 0, ff3CodeHeadFilling c,
            ff3CodePathEquiv (ff3ProfileRows (c.1 0)) n (ff3CodeTail c)⟩
        invFun := fun x ↦
          ff3CodeCons x.1 x.2.1
            ((ff3CodePathEquiv (ff3ProfileRows x.1) n).symm x.2.2)
        left_inv := fun c ↦ by
          change ff3CodeCons (c.1 0) (ff3CodeHeadFilling c)
            ((ff3CodePathEquiv (ff3ProfileRows (c.1 0)) n).symm
              (ff3CodePathEquiv (ff3ProfileRows (c.1 0)) n (ff3CodeTail c))) = c
          rw [Equiv.symm_apply_apply]
          exact ff3_codeCons_head_tail c
        right_inv := fun x ↦ by
          obtain ⟨p, f, t⟩ := x
          change (⟨p,
            (ff3CodeHeadFilling
                (ff3CodeCons p f ((ff3CodePathEquiv (ff3ProfileRows p) n).symm t)),
              ff3CodePathEquiv (ff3ProfileRows p) n
                (ff3CodeTail
                  (ff3CodeCons p f ((ff3CodePathEquiv (ff3ProfileRows p) n).symm t))))⟩ :
                  ff3Path a (n + 1)) = ⟨p, (f, t)⟩
          rw [ff3_codeHeadFilling_cons, ff3_codeTail_cons, Equiv.apply_symm_apply] }

/-- **Number of vertical-fault-free tilings of the $3 \times n$ rectangle.** For every natural
number $n$, this is the number of square-and-domino tilings of the $3 \times n$ rectangle that
are vertical-fault-free. -/
noncomputable def verticalFaultFreeTilingCount (n : ℕ) : ℕ :=
  Nat.card {T : Finset (Finset (TilingCell n)) //
    IsSquareDominoTiling T ∧ IsVerticalFaultFree T}

/-- **Recurrence sequence for vertical-fault-free $3 \times n$ tilings.** The integer sequence
$(V_n)_{n \ge 0}$ is defined by $V_0 = 0$, $V_1 = 3$, $V_2 = 13$, $V_3 = 26$, $V_4 = 66$,
$V_5 = 154$, $V_6 = 380$ and $V_n = V_{n-1} + 4 V_{n-2} - V_{n-3} - V_{n-4}$ for $n \ge 7$.

The value $V_0 = 0$ is a placeholder; the source considers only $n \ge 1$. -/
def tilingCount : ℕ → ℤ
  | 0 => 0
  | 1 => 3
  | 2 => 13
  | 3 => 26
  | 4 => 66
  | 5 => 154
  | 6 => 380
  | (n + 7) => tilingCount (n + 6) + 4 * tilingCount (n + 5)
      - tilingCount (n + 4) - tilingCount (n + 3)

private def ff3ModelCount : ℕ → ℕ
  | 0 => 0
  | 1 => 3
  | n + 2 => ff3TransferCount ℕ n

private theorem ff3_model_recurrence (n : ℕ) :
    (ff3ModelCount (n + 7) : ℤ) = (ff3ModelCount (n + 6) : ℤ) +
      4 * (ff3ModelCount (n + 5) : ℤ) - (ff3ModelCount (n + 4) : ℤ) -
        (ff3ModelCount (n + 3) : ℤ) := by
  change ((ff3TransferCount ℕ (n + 5) : ℕ) : ℤ) =
    (ff3TransferCount ℕ (n + 4) : ℤ) + 4 * (ff3TransferCount ℕ (n + 3) : ℤ) -
      (ff3TransferCount ℕ (n + 2) : ℤ) - (ff3TransferCount ℕ (n + 1) : ℤ)
  simp_rw [ff3_transfer_cast]
  exact ff3_transfer_recurrence n

private theorem ff3_model_eq_tilingCount :
    ∀ n : ℕ, 1 ≤ n → (ff3ModelCount n : ℤ) = tilingCount n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn
      by_cases hsmall : n ≤ 6
      · interval_cases n <;>
          simp_all [ff3ModelCount, tilingCount, ff3_transfer_zero, ff3_transfer_one,
            ff3_transfer_two, ff3_transfer_three, ff3_transfer_four]
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
        rw [tilingCount]
        rw [← ih (m + 6) (by omega) (by omega), ← ih (m + 5) (by omega) (by omega),
          ← ih (m + 4) (by omega) (by omega), ← ih (m + 3) (by omega) (by omega)]
        exact ff3_model_recurrence m

private noncomputable def ff3TilingPathEquiv (n : ℕ) :
    ff3FaultFreeTilings (n + 1) ≃ ff3Path ∅ n :=
  (ff3_tilingMatchingEquiv (n + 1)).trans <|
    (ff3_matchingEdgeEquiv n).symm.trans <|
      (ff3CodeEdgeEquiv n).symm.trans (ff3CodePathEquiv ∅ n)

private theorem ff3_vertical_count_succ (n : ℕ) :
    verticalFaultFreeTilingCount (n + 1) = ff3ModelCount (n + 1) := by
  unfold verticalFaultFreeTilingCount
  rw [Nat.card_congr (ff3TilingPathEquiv n)]
  cases n with
  | zero => simpa [ff3ModelCount] using ff3_card_path_empty_zero
  | succ n => simpa [ff3ModelCount] using ff3_card_path_empty_succ n

/--
**Recurrence for vertical-fault-free tilings of the $3 \times n$ rectangle.** For $n \ge 1$, let
$V_n$ be the number of vertical-fault-free tilings of the $3 \times n$ rectangle by unit squares
and dominoes. Then $V_1 = 3$, $V_2 = 13$, $V_3 = 26$, $V_4 = 66$, $V_5 = 154$, $V_6 = 380$, and
$V_n = V_{n-1} + 4 V_{n-2} - V_{n-3} - V_{n-4}$ for every $n \ge 7$.

Here $V_n$ counts the tilings directly; the recurrence is a theorem, not its definition.

Proof: The count is encoded by a transfer matrix over column profiles. An annihilating
polynomial for that matrix gives the recurrence after the six initial values.

Proves `Wanted` entry `fault_free_3xn_tiling_recursion`.

Source: Oluwatobi Jemima Alabi and Greg Dresden, "Fault-Free Tilings of
the 3 × n Rectangle With Squares and Dominos," Journal of Integer
Sequences 24 (2021), Article 21.1.2, theorem on vertical-fault-free `V_n`
(unlabeled), lines 358–364,
<https://cs.uwaterloo.ca/journals/JIS/VOL24/Dresden/dresden7.tex>.
-/
public theorem fault_free_3xn_tiling_recursion :
    ∀ n : ℕ, 1 ≤ n → (verticalFaultFreeTilingCount n : ℤ) = tilingCount n := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [ff3_vertical_count_succ]
  exact ff3_model_eq_tilingCount (m + 1) (by omega)

end MetaMathlibExt
