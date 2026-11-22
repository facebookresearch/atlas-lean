/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Projectivization.Constructions
import Mathlib.Combinatorics.Configuration

/-!
# Line arrangements in the projective plane

A line arrangement over a field `K` is a finite set of at least two distinct lines of the
projective plane `ℙ K (Fin 3 → K)`. A line is recorded by its coordinate vector, a point of the
dual plane, which is again `ℙ K (Fin 3 → K)`; the point `p` lies on the line `ℓ` when
`Projectivization.orthogonal p ℓ`, the vanishing of the dot product of representatives. Two
distinct lines meet in exactly one point, `Projectivization.cross ℓ ℓ'`.

## Main definitions

* `LineArrangement K`: a finite set of at least two lines of `ℙ K (Fin 3 → K)`.
* `LineArrangement.multiplicity A p`: the number `m_p` of lines of `A` through `p`.
* `LineArrangement.singularPoints A`: the finite set of points lying on at least two lines of
  `A`, the intersection points of pairs of distinct lines.
* `LineArrangement.hConstant A`: the Harbourne constant `H(A) = (d² - ∑_p m_p²) / s` of an
  arrangement of `d` lines with `s` singular points `p` of multiplicities `m_p`.

## Main statements

* `Projectivization.eq_cross_iff`: the points orthogonal to two distinct points `v ≠ w` are
  exactly `cross v w`; so two distinct lines meet exactly in their cross product, and two distinct
  points lie on exactly one line.
* `LineArrangement.mem_singularPoints_iff_exists`: a point is singular iff it lies on two distinct
  lines of the arrangement.
* `LineArrangement.mem_singularPoints_iff`: the singular points are the points of multiplicity at
  least two.
* `LineArrangement.singularPoints_nonempty`: every arrangement has a singular point, so the
  denominator of `hConstant` is positive (`LineArrangement.card_singularPoints_pos`).

## References

* T. Bauer, S. Di Rocco, B. Harbourne, J. Huizenga, A. Lundman, P. Pokora, T. Szemberg,
  *Bounded negativity and arrangements of lines*, Int. Math. Res. Not. IMRN 2015, no. 19,
  9456–9471 (the H-constant of a line arrangement).
-/

@[expose] public section

open scoped LinearAlgebra.Projectivization

namespace Projectivization

variable {K : Type*} [Field K] [DecidableEq K]

/-- The points orthogonal to two distinct points `v ≠ w` of `ℙ K (Fin 3 → K)` are exactly
`cross v w`: two distinct lines meet exactly in their cross product, and dually two distinct points
lie on exactly one line. -/
theorem eq_cross_iff {p v w : ℙ K (Fin 3 → K)} (h : v ≠ w) :
    p = cross v w ↔ p.orthogonal v ∧ p.orthogonal w := by
  refine ⟨fun hp => hp ▸ ⟨cross_orthogonal_left h, cross_orthogonal_right h⟩, fun hp => ?_⟩
  exact (Configuration.ofField.eq_or_eq_of_orthogonal hp.1 (cross_orthogonal_left h) hp.2
    (cross_orthogonal_right h)).resolve_right h

end Projectivization

/-- A line arrangement in the projective plane over `K`: a finite set of at least two lines, each
line recorded by its coordinate vector, a point of the dual plane `ℙ K (Fin 3 → K)`. -/
@[ext]
structure LineArrangement (K : Type*) [Field K] where
  /-- The lines of the arrangement. -/
  lines : Finset (ℙ K (Fin 3 → K))
  /-- An arrangement has at least two lines. -/
  two_le_card : 2 ≤ lines.card

namespace LineArrangement

variable {K : Type*} [Field K] (A : LineArrangement K)

open Classical in
/-- The multiplicity `m_p` of the point `p` in `A`: the number of lines of `A` through `p`. -/
noncomputable def multiplicity (p : ℙ K (Fin 3 → K)) : ℕ :=
  (A.lines.filter fun ℓ => p.orthogonal ℓ).card

open Classical in
/-- The singular points of `A`: the intersection points of pairs of distinct lines of `A`. -/
noncomputable def singularPoints : Finset (ℙ K (Fin 3 → K)) :=
  A.lines.offDiag.image fun ℓ => Projectivization.cross ℓ.1 ℓ.2

/-- A point is singular iff it lies on two distinct lines of the arrangement. -/
theorem mem_singularPoints_iff_exists {p : ℙ K (Fin 3 → K)} :
    p ∈ A.singularPoints ↔
      ∃ ℓ ∈ A.lines, ∃ ℓ' ∈ A.lines, ℓ ≠ ℓ' ∧ p.orthogonal ℓ ∧ p.orthogonal ℓ' := by
  classical
  simp only [singularPoints, Finset.mem_image, Finset.mem_offDiag, Prod.exists]
  constructor
  · rintro ⟨ℓ, ℓ', ⟨hℓ, hℓ', hne⟩, rfl⟩
    exact ⟨ℓ, hℓ, ℓ', hℓ', hne, (Projectivization.eq_cross_iff hne).1 rfl⟩
  · rintro ⟨ℓ, hℓ, ℓ', hℓ', hne, h⟩
    exact ⟨ℓ, ℓ', ⟨hℓ, hℓ', hne⟩, ((Projectivization.eq_cross_iff hne).2 h).symm⟩

/-- The singular points are the points of multiplicity at least two. -/
theorem mem_singularPoints_iff {p : ℙ K (Fin 3 → K)} :
    p ∈ A.singularPoints ↔ 2 ≤ A.multiplicity p := by
  classical
  rw [mem_singularPoints_iff_exists, multiplicity, Nat.succ_le_iff, Finset.one_lt_card]
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨ℓ, hℓ, ℓ', hℓ', hne, h, h'⟩
    exact ⟨ℓ, ⟨hℓ, h⟩, ℓ', ⟨hℓ', h'⟩, hne⟩
  · rintro ⟨ℓ, ⟨hℓ, h⟩, ℓ', ⟨hℓ', h'⟩, hne⟩
    exact ⟨ℓ, hℓ, ℓ', hℓ', hne, h, h'⟩

/-- The multiplicity of a point is at most the number of lines. -/
theorem multiplicity_le_card (p : ℙ K (Fin 3 → K)) : A.multiplicity p ≤ A.lines.card := by
  classical
  exact Finset.card_filter_le _ _

/-- Every arrangement has a singular point: any two of its lines meet. -/
theorem singularPoints_nonempty : A.singularPoints.Nonempty := by
  classical
  obtain ⟨ℓ, hℓ, ℓ', hℓ', hne⟩ := Finset.one_lt_card.1 A.two_le_card
  exact ⟨_, A.mem_singularPoints_iff_exists.2 ⟨ℓ, hℓ, ℓ', hℓ', hne,
    Projectivization.cross_orthogonal_left hne, Projectivization.cross_orthogonal_right hne⟩⟩

theorem card_singularPoints_pos : 0 < A.singularPoints.card :=
  Finset.card_pos.2 A.singularPoints_nonempty

/-- The Harbourne constant `H(A) = (d² - ∑_p m_p²) / s` of an arrangement of `d` lines with `s`
singular points `p` of multiplicities `m_p`: the self-intersection of the strict transform of the
arrangement on the blow-up of its singular points, divided by `s`. -/
noncomputable def hConstant : ℝ :=
  ((A.lines.card : ℝ) ^ 2 - ∑ p ∈ A.singularPoints, (A.multiplicity p : ℝ) ^ 2) /
    A.singularPoints.card

end LineArrangement
