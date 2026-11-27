/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.CubeNim
import all MathlibExt.Combinatorics.CubeNim
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases

/-!
# Misère vertex Nim on a cube

For a set satisfying the misère outcome recursion (the terminal position is winning), the
losing positions are singletons and positions with equal counts on opposite faces and at least
four tokens in total. A vertex move removes at least one token from the faces incident to one
vertex. The theorem `cubeVertexNim_misere_pPositions` gives the list of cases for a position
`(a, b, c, A, B, C)` with `C` maximal, `a ≤ A`, `b ≤ B` and `a ≤ b`.

## References

* Balaji R. Kadam and A. J. Shaiju, *Variations of the Nim Game Played on a Cube*,
  INTEGERS 25 (2025), Article G2, pp. 1–14, Theorem 6 (pp. 7–8) and Theorem 2 (pp. 4–5).
* `MathlibExt.Combinatorics.CubeNim`: the normal-play balancing and exclusion properties from
  `cubeVertexNim_pPositions`, and its helper `cubeVertexNim_pPositions.eq_opposite`, are reused.
* `MathlibExt.Combinatorics.MisereCubeRotationNim`: the outcome induction follows the structure
  of `cubeRotationNim_misere_pPositions.classification`.
-/

namespace MetaMathlibExt

namespace cubeVertexNim_misere_pPositions

private abbrev Position := Fin 6 → ℕ

private def Balanced (p : Position) : Prop := p 0 = p 3 ∧ p 1 = p 4 ∧ p 2 = p 5

private def Losing (p : Position) : Prop :=
  (∑ i, p i) = 1 ∨ (Balanced p ∧ 4 ≤ ∑ i, p i)

private theorem balanced_axis_eq {p : Position} (hp : Balanced p) {i j : Fin 6}
    (h : i.val % 3 = j.val % 3) : p i = p j := by
  have hfaces : ∀ i j : Fin 6, i.val % 3 = j.val % 3 → i = j ∨ i = j + 3 := by decide
  rcases hfaces i j h with rfl | rfl
  · rfl
  · exact (cubeVertexNim_pPositions.eq_opposite hp j).symm

private theorem move_total_lt {p q : Position} (hm : CubeVertexMove p q) :
    (∑ i, q i) < ∑ i, p i := by
  obtain ⟨_, _, _, _, _, _, hle, hne, _⟩ := hm
  exact Fintype.sum_strictMono (lt_of_le_of_ne hle hne)

private theorem move_keeps_face_of_pair {p q : Position} (hm : CubeVertexMove p q)
    {i j : Fin 6} (hij : i ≠ j) (haxis : i.val % 3 = j.val % 3) : q i = p i ∨ q j = p j := by
  obtain ⟨x, y, z, hx, hy, hz, _, _, hfix⟩ := hm
  have changed {k : Fin 6} (hk : q k ≠ p k) : k = x ∨ k = y ∨ k = z := by
    by_contra! h
    exact hk (hfix k h.1 h.2.1 h.2.2)
  by_contra! h
  rcases changed h.1 with rfl | rfl | rfl <;>
    rcases changed h.2 with h' | h' | h' <;> rw [h'] at hij haxis <;> simp_all

private theorem losing_no_move {p q : Position} (hp : Losing p) (hm : CubeVertexMove p q) :
    ¬ Losing q := by
  rcases hp with hp | ⟨hbp, hlarge⟩
  · have hlt := move_total_lt hm
    rintro (hq | ⟨_, hq⟩) <;> omega
  · rintro (ht | ⟨hbq, _⟩)
    · -- An untouched face from each pair retains at least half the original total.
      have h₁ := move_keeps_face_of_pair hm (i := 0) (j := 3) (by decide) rfl
      have h₂ := move_keeps_face_of_pair hm (i := 1) (j := 4) (by decide) rfl
      have h₃ := move_keeps_face_of_pair hm (i := 2) (j := 5) (by decide) rfl
      obtain ⟨ha, hb, hc⟩ := hbp
      rw [Fin.sum_univ_six] at ht hlarge
      omega
    · exact cubeVertexNim_pPositions.1 p q hbp hm hbq

private theorem exists_move {p : Position} (hp : 0 < ∑ i, p i) : ∃ q, CubeVertexMove p q := by
  have hne : p ≠ 0 := by
    rintro rfl
    simp at hp
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  -- Choose a vertex containing the positive face `i` and empty just that face.
  let face (a : Fin 6) := if i.val % 3 = a.val then i else a
  have haxis (a : Fin 6) (ha : a.val % 3 = a.val) : (face a).val % 3 = a.val := by
    dsimp [face]
    split <;> assumption
  have hsel : i = face 0 ∨ i = face 1 ∨ i = face 2 := by
    rcases (show i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 by omega) with h | h | h
    · exact Or.inl (by simp [face, h])
    · exact Or.inr (Or.inl (by simp [face, h]))
    · exact Or.inr (Or.inr (by simp [face, h]))
  refine ⟨Function.update p i 0, face 0, face 1, face 2, haxis 0 rfl, haxis 1 rfl,
    haxis 2 rfl, update_le_iff.mpr ⟨Nat.zero_le _, fun _ _ => le_rfl⟩,
    Function.update_ne_self_iff.mpr (Ne.symm hi), ?_⟩
  · intro k hkx hky hkz
    rw [Function.update_of_ne]
    rintro rfl
    rcases hsel with h | h | h <;> contradiction

private theorem move_to_losing {p : Position} (hp : 0 < ∑ i, p i) (hn : ¬ Losing p) :
    ∃ q, CubeVertexMove p q ∧ Losing q := by
  -- Start with normal-play balancing, allowing it to do nothing when already balanced.
  obtain ⟨b, hb, hstep⟩ : ∃ b, Balanced b ∧ (b = p ∨ CubeVertexMove p b) := by
    by_cases h : Balanced p
    · exact ⟨p, h, Or.inl rfl⟩
    · obtain ⟨b, hm, hb⟩ := cubeVertexNim_pPositions.2 p h
      exact ⟨b, hb, Or.inr hm⟩
  by_cases hlarge : 4 ≤ ∑ i, b i
  · have hlose : Losing b := Or.inr ⟨hb, hlarge⟩
    exact ⟨b, hstep.resolve_left (fun h => hn (h ▸ hlose)), hlose⟩
  have hsmall : (∑ i, b i) = 0 ∨ (∑ i, b i) = 2 := by
    rw [Fin.sum_univ_six] at hlarge ⊢
    obtain ⟨ha, hb, hc⟩ := hb
    omega
  obtain ⟨x, y, z, hx, hy, hz, hle, hfix⟩ : ∃ x y z : Fin 6,
      x.val % 3 = 0 ∧ y.val % 3 = 1 ∧ z.val % 3 = 2 ∧ b ≤ p ∧
      ∀ k, k ≠ x → k ≠ y → k ≠ z → b k = p k := by
    rcases hstep with rfl | ⟨x, y, z, hx, hy, hz, hle, _, hfix⟩
    · exact ⟨0, 1, 2, rfl, rfl, rfl, le_rfl, fun _ _ _ _ => rfl⟩
    · exact ⟨x, y, z, hx, hy, hz, hle, hfix⟩
  suffices ∃ q : Position, q ≤ p ∧ (∑ i, q i) = 1 ∧
      ∀ k, k ≠ x → k ≠ y → k ≠ z → q k = p k by
    obtain ⟨q, hqp, hq, hkeep⟩ := this
    refine ⟨q, ⟨x, y, z, hx, hy, hz, hqp, ?_, hkeep⟩, Or.inl hq⟩
    rintro rfl
    exact hn (Or.inl hq)
  rcases hsmall with hzero | htwo
  · -- The untouched faces are empty, so keep one token on any positive face of `p`.
    obtain ⟨i, hi⟩ : ∃ i, 0 < p i := by
      by_contra! h
      simp [show ∀ i, p i = 0 from fun i => Nat.eq_zero_of_le_zero (h i)] at hp
    let q : Position := Pi.single i 1
    have hqp : q ≤ p := by
      intro j
      by_cases h : j = i
      · subst j
        simpa [q] using Nat.succ_le_of_lt hi
      · simp [q, Pi.single_eq_of_ne h]
    refine ⟨q, hqp, by simp [q], fun k hkx hky hkz => ?_⟩
    have hbk : b k = 0 := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp
      hzero k (Finset.mem_univ _)
    have hpk : p k = 0 := (hfix k hkx hky hkz).symm.trans hbk
    exact le_antisymm (hqp k) (hpk ▸ Nat.zero_le _)
  · -- The balanced position has two opposite unit heaps. Empty the selected one.
    have hbx : b x = b 0 := balanced_axis_eq hb hx
    have hby : b y = b 1 := balanced_axis_eq hb hy
    have hbz : b z = b 2 := balanced_axis_eq hb hz
    have hsum : b x + b y + b z = 1 := by
      rw [hbx, hby, hbz]
      rw [Fin.sum_univ_six] at htwo
      obtain ⟨ha, hb, hc⟩ := hb
      omega
    obtain ⟨i, hi, hbi⟩ : ∃ i, (i = x ∨ i = y ∨ i = z) ∧ b i = 1 := by
      by_cases hx' : b x = 1
      · exact ⟨x, Or.inl rfl, hx'⟩
      by_cases hy' : b y = 1
      · exact ⟨y, Or.inr (Or.inl rfl), hy'⟩
      · exact ⟨z, Or.inr (Or.inr rfl), by omega⟩
    let q := Function.update b i 0
    have hqb : q ≤ b :=
      update_le_iff.mpr ⟨Nat.zero_le _, fun _ _ => le_rfl⟩
    refine ⟨q, hqb.trans hle, ?_, fun k hkx hky hkz => ?_⟩
    · dsimp only [q]
      rw [Finset.sum_update_of_mem (Finset.mem_univ i), zero_add]
      rw [Finset.sum_eq_sum_sdiff_singleton_add (Finset.mem_univ i) b, hbi] at htwo
      omega
    · have hki : k ≠ i := by
        rintro rfl
        rcases hi with h | h | h <;> contradiction
      dsimp only [q]
      rw [Function.update_of_ne hki, hfix k hkx hky hkz]

private theorem classification (P : Set Position)
    (hP : ∀ p, p ∈ P ↔ (∃ q, CubeVertexMove p q) ∧ ∀ q, CubeVertexMove p q → q ∉ P)
    (p : Position) : p ∈ P ↔ Losing p := by
  have ih (q : Position) (hm : CubeVertexMove p q) : q ∈ P ↔ Losing q :=
    classification P hP q
  rw [hP p]
  constructor
  · rintro ⟨⟨q, hm⟩, hout⟩
    by_contra hn
    obtain ⟨r, hr, hlose⟩ := move_to_losing (Nat.zero_lt_of_lt (move_total_lt hm)) hn
    exact hout r hr ((ih r hr).mpr hlose)
  · intro hp
    have hpos : 0 < ∑ i, p i := by rcases hp with h | ⟨_, h⟩ <;> omega
    exact ⟨exists_move hpos, fun q hm hmem => losing_no_move hp hm ((ih q hm).mp hmem)⟩
termination_by ∑ i, p i
decreasing_by exact move_total_lt hm

end cubeVertexNim_misere_pPositions

open cubeVertexNim_misere_pPositions in
/-- **Misère P-positions of vertex Nim on a cube.** Write a position of the cube game as
$p = (a, b, c, A, B, C)$, the numbers of tokens on the six faces of a cube, where the faces
carrying $A$, $B$, $C$ are opposite those carrying $a$, $b$, $c$; a vertex move removes at
least one token in total from the three faces at one vertex (one face from each opposite pair).
Let $P$ be any set of positions such that $p \in P$ if and only if $p$ has a vertex move and
no vertex move from $p$ leads to a position in $P$ (the misère P-positions). Then for every
position $p$ with $a \le A$, $b \le B$, $a \le b$ and $C$ at least every entry of $p$, we have
$p \in P$ if and only if either $a = A$, $b = B$, $c = C$ and $C \ge 2$ all hold, or $p$ is one
of $(0, 0, 0, 0, 0, 1)$, $(0, 1, 1, 0, 1, 1)$ and $(1, 1, 1, 1, 1, 1)$.

Source: Balaji R. Kadam and A. J. Shaiju, *Variations of the Nim Game Played on a Cube*,
INTEGERS 25 (2025), Article G2, Theorem 6 (`integers-2025-G2-thm-6`). -/
public theorem cubeVertexNim_misere_pPositions (P : Set (Fin 6 → ℕ))
    (hP : ∀ p, p ∈ P ↔ (∃ q, CubeVertexMove p q) ∧ ∀ q, CubeVertexMove p q → q ∉ P)
    (p : Fin 6 → ℕ) (hC : ∀ k, p k ≤ p 5) (ha : p 0 ≤ p 3) (hb : p 1 ≤ p 4) (hab : p 0 ≤ p 1) :
    p ∈ P ↔ (p 0 = p 3 ∧ p 1 = p 4 ∧ p 2 = p 5 ∧ 2 ≤ p 5) ∨ p = ![0, 0, 0, 0, 0, 1] ∨
      p = ![0, 1, 1, 0, 1, 1] ∨ p = ![1, 1, 1, 1, 1, 1] := by
  rw [classification P hP]
  simp only [Losing, Balanced, Fin.sum_univ_six]
  constructor
  · rintro (hsingle | ⟨⟨ha', hb', hc'⟩, htotal⟩)
    · right; left
      have ht : 0 < p 5 := by
        have := hC 2
        have := hC 3
        have := hC 4
        omega
      funext k
      fin_cases k <;> dsimp <;> omega
    · by_cases hlarge : 2 ≤ p 5
      · exact Or.inl ⟨ha', hb', hc', hlarge⟩
      · have h₁ := hC 0
        have h₂ := hC 1
        have h₃ : p 1 = 1 := by omega
        by_cases h₄ : p 0 = 0
        · right; right; left
          funext k
          fin_cases k <;> dsimp <;> omega
        · right; right; right
          funext k
          fin_cases k <;> dsimp <;> omega
  · rintro (⟨ha', hb', hc', hlarge⟩ | rfl | rfl | rfl)
    · exact Or.inr ⟨⟨ha', hb', hc'⟩, by omega⟩
    · decide
    · decide
    · decide

end MetaMathlibExt
