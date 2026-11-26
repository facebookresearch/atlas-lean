/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: Muse Code powered by Meta Muse Spark
-/
module

public import MathlibExt.Analysis.Complex.Subharmonic.AngularSublevel
public import Mathlib.Analysis.Complex.ReImTopology

/-!
# Finite radial slits in the unit disk

`RadialSlitData n` is a family of `n` closed real intervals with
`0 ≤ inner(i) ≤ outer(i) ≤ 1`. The radius set is their union, the complex
slit is that union on the real axis, and the slit domain is the open unit
disk with the slit removed. Overlapping and degenerate intervals are allowed.
When `n=0` the union is empty and the domain is the full unit disk.

The radius and slit sets are compact and closed, the radius set lies in
`[0,1]`, and the slit lies in the closed unit disk. The remaining domain is
open and nonempty: the negative real point `-1/2` avoids every possible slit.
The distinguished one-interval family gives exactly the entire slit `[0,1]`
on the real axis.
-/

@[expose] public section

namespace Complex

/-- **Finite radial-slit data in the unit disk.** For `n : ℕ`, a `RadialSlitData n` consists
of real endpoint functions `inner,outer : Fin n→ℝ` and bounds `0≤inner(i)≤outer(i)≤1` for
each index. Intervals may overlap or have length zero. For `n=0`, the family and its union
are empty. -/
structure RadialSlitData (n : ℕ) where
  inner : Fin n → ℝ
  outer : Fin n → ℝ
  inner_nonneg : ∀ i, 0 ≤ inner i
  inner_le_outer : ∀ i, inner i ≤ outer i
  outer_le_one : ∀ i, outer i ≤ 1

namespace RadialSlitData

variable {n : ℕ} (E : RadialSlitData n)

/-- **Union of the finite radial intervals.** Let `n : ℕ` and `E : RadialSlitData n` have real
endpoints `a_i=E.inner i`, `b_i=E.outer i` for `i∈Fin n`, with `0≤a_i≤b_i≤1`. Put
`R=⋃_{i∈Fin n}[a_i,b_i]`, `S={z∈ℂ | Re z∈R ∧ Im z=0}` and `D={z∈ℂ | ‖z‖<1}∖S`. Then
`E.radiusSet=R`. Overlapping and zero-length intervals are allowed; for `n=0`, `R=∅`. -/
def radiusSet : Set ℝ :=
  ⋃ i, Set.Icc (E.inner i) (E.outer i)

/-- **Real-axis slit associated with finite radius data.** Let `n : ℕ` and `E : RadialSlitData
n` have real endpoints `a_i=E.inner i`, `b_i=E.outer i` for `i∈Fin n`, with `0≤a_i≤b_i≤1`.
Put `R=⋃_{i∈Fin n}[a_i,b_i]`, `S={z∈ℂ | Re z∈R ∧ Im z=0}` and `D={z∈ℂ | ‖z‖<1}∖S`. Then
`E.slitSet=S=R×ℂ{0}`. For `n=0`, this slit is empty. -/
def slitSet : Set ℂ :=
  E.radiusSet ×ℂ ({0} : Set ℝ)

/-- **Open unit disk with a finite real-axis slit removed.** Let `n : ℕ` and `E :
RadialSlitData n` have real endpoints `a_i=E.inner i`, `b_i=E.outer i` for `i∈Fin n`, with
`0≤a_i≤b_i≤1`. Put `R=⋃_{i∈Fin n}[a_i,b_i]`, `S={z∈ℂ | Re z∈R ∧ Im z=0}` and `D={z∈ℂ |
‖z‖<1}∖S`. Then `E.slitDomain=D`. For `n=0`, the domain is the full open unit disk. -/
noncomputable def slitDomain : Set ℂ :=
  Metric.ball 0 1 \ E.slitSet

/-- **Membership in the finite radius union.** Let `n : ℕ` and `E : RadialSlitData n` have
real endpoints `a_i=E.inner i`, `b_i=E.outer i` for `i∈Fin n`, with `0≤a_i≤b_i≤1`. Put
`R=⋃_{i∈Fin n}[a_i,b_i]`, `S={z∈ℂ | Re z∈R ∧ Im z=0}` and `D={z∈ℂ | ‖z‖<1}∖S`. For `r∈ℝ`,
`r∈E.radiusSet ↔ ∃i∈Fin n, a_i≤r≤b_i`. No disjointness or positive interval length is
assumed. -/
theorem mem_radiusSet {r : ℝ} :
    r ∈ E.radiusSet ↔ ∃ i, r ∈ Set.Icc (E.inner i) (E.outer i) := by
  unfold radiusSet
  exact Set.mem_iUnion

/-- **Complex coordinates of slit membership.** Let `n : ℕ` and `E : RadialSlitData n` have
real endpoints `a_i=E.inner i`, `b_i=E.outer i` for `i∈Fin n`, with `0≤a_i≤b_i≤1`. Put
`R=⋃_{i∈Fin n}[a_i,b_i]`, `S={z∈ℂ | Re z∈R ∧ Im z=0}` and `D={z∈ℂ | ‖z‖<1}∖S`. For `z∈ℂ`,
`z∈E.slitSet ↔ Re z∈R ∧ Im z=0`. -/
theorem mem_slitSet {z : ℂ} :
    z ∈ E.slitSet ↔ z.re ∈ E.radiusSet ∧ z.im = 0 := by
  unfold slitSet
  rw [Complex.mem_reProdIm]
  simp only [Set.mem_singleton_iff]

/-- **Real points on a finite radial slit.** Let `n : ℕ` and `E : RadialSlitData n` have real
endpoints `a_i=E.inner i`, `b_i=E.outer i` for `i∈Fin n`, with `0≤a_i≤b_i≤1`. Put
`R=⋃_{i∈Fin n}[a_i,b_i]`, `S={z∈ℂ | Re z∈R ∧ Im z=0}` and `D={z∈ℂ | ‖z‖<1}∖S`. For `r∈ℝ`,
`(r : ℂ)∈E.slitSet ↔ r∈R`. -/
theorem ofReal_mem_slitSet {r : ℝ} :
    (r : ℂ) ∈ E.slitSet ↔ r ∈ E.radiusSet := by
  rw [mem_slitSet]
  simp

/-- **Norm and exclusion criterion for the slit domain.** Let `n : ℕ` and `E : RadialSlitData
n` have real endpoints `a_i=E.inner i`, `b_i=E.outer i` for `i∈Fin n`, with `0≤a_i≤b_i≤1`.
Put `R=⋃_{i∈Fin n}[a_i,b_i]`, `S={z∈ℂ | Re z∈R ∧ Im z=0}` and `D={z∈ℂ | ‖z‖<1}∖S`. For
`z∈ℂ`, `z∈E.slitDomain ↔ ‖z‖<1 ∧ z∉S`. -/
theorem mem_slitDomain {z : ℂ} :
    z ∈ E.slitDomain ↔ ‖z‖ < 1 ∧ z ∉ E.slitSet := by
  simp only [slitDomain, Set.mem_sdiff, Metric.mem_ball, dist_zero_right]

/-- **Compactness of the finite radius union.** Let `n : ℕ` and `E : RadialSlitData n` have
real endpoints `a_i=E.inner i`, `b_i=E.outer i` for `i∈Fin n`, with `0≤a_i≤b_i≤1`. Put
`R=⋃_{i∈Fin n}[a_i,b_i]`, `S={z∈ℂ | Re z∈R ∧ Im z=0}` and `D={z∈ℂ | ‖z‖<1}∖S`. The finite
union `E.radiusSet=R` is compact in the real topology, including the empty family. -/
theorem isCompact_radiusSet : IsCompact E.radiusSet := by
  unfold radiusSet
  exact isCompact_iUnion fun _ => isCompact_Icc

/-- **Closedness of the finite radius union.** Let `n : ℕ` and `E : RadialSlitData n` have
real endpoints `a_i=E.inner i`, `b_i=E.outer i` for `i∈Fin n`, with `0≤a_i≤b_i≤1`. Put
`R=⋃_{i∈Fin n}[a_i,b_i]`, `S={z∈ℂ | Re z∈R ∧ Im z=0}` and `D={z∈ℂ | ‖z‖<1}∖S`. The radius
union `E.radiusSet=R` is closed in `ℝ`. -/
theorem isClosed_radiusSet : IsClosed E.radiusSet :=
  E.isCompact_radiusSet.isClosed

/-- **Bounds on all selected radii.** Let `n : ℕ` and `E : RadialSlitData n` have real
endpoints `a_i=E.inner i`, `b_i=E.outer i` for `i∈Fin n`, with `0≤a_i≤b_i≤1`. Put
`R=⋃_{i∈Fin n}[a_i,b_i]`, `S={z∈ℂ | Re z∈R ∧ Im z=0}` and `D={z∈ℂ | ‖z‖<1}∖S`. Every
selected radius lies between zero and one: `E.radiusSet⊆[0,1]`. -/
theorem radiusSet_subset_Icc : E.radiusSet ⊆ Set.Icc 0 1 := by
  intro r hr
  rw [E.mem_radiusSet] at hr
  obtain ⟨i, hi⟩ := hr
  rw [Set.mem_Icc] at hi
  exact ⟨le_trans (E.inner_nonneg i) hi.1, le_trans hi.2 (E.outer_le_one i)⟩

/-- **Compactness of a finite real-axis slit.** Let `n : ℕ` and `E : RadialSlitData n` have
real endpoints `a_i=E.inner i`, `b_i=E.outer i` for `i∈Fin n`, with `0≤a_i≤b_i≤1`. Put
`R=⋃_{i∈Fin n}[a_i,b_i]`, `S={z∈ℂ | Re z∈R ∧ Im z=0}` and `D={z∈ℂ | ‖z‖<1}∖S`. The slit
`E.slitSet=S` is compact in the complex-plane topology. -/
theorem isCompact_slitSet : IsCompact E.slitSet :=
  E.isCompact_radiusSet.reProdIm isCompact_singleton

/-- **Closedness of a finite real-axis slit.** Let `n : ℕ` and `E : RadialSlitData n` have
real endpoints `a_i=E.inner i`, `b_i=E.outer i` for `i∈Fin n`, with `0≤a_i≤b_i≤1`. Put
`R=⋃_{i∈Fin n}[a_i,b_i]`, `S={z∈ℂ | Re z∈R ∧ Im z=0}` and `D={z∈ℂ | ‖z‖<1}∖S`. The slit
`E.slitSet=S` is closed in `ℂ`. -/
theorem isClosed_slitSet : IsClosed E.slitSet :=
  E.isCompact_slitSet.isClosed

/-- **Finite slit lies in the closed unit disk.** Let `n : ℕ` and `E : RadialSlitData n` have
real endpoints `a_i=E.inner i`, `b_i=E.outer i` for `i∈Fin n`, with `0≤a_i≤b_i≤1`. Put
`R=⋃_{i∈Fin n}[a_i,b_i]`, `S={z∈ℂ | Re z∈R ∧ Im z=0}` and `D={z∈ℂ | ‖z‖<1}∖S`. The bound
on the endpoints gives `E.slitSet⊆{z∈ℂ | ‖z‖≤1}`. -/
theorem slitSet_subset_closedBall : E.slitSet ⊆ Metric.closedBall 0 1 := by
  intro z hz
  rw [E.mem_slitSet] at hz
  have hmem := E.radiusSet_subset_Icc hz.1
  rw [Set.mem_Icc] at hmem
  have hrw : z = ((z.re : ℝ) : ℂ) := Complex.ext rfl hz.2
  rw [Metric.mem_closedBall, dist_zero_right, hrw, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hmem.1]
  exact hmem.2

/-- **Openness of the disk minus a finite slit.** Let `n : ℕ` and `E : RadialSlitData n` have
real endpoints `a_i=E.inner i`, `b_i=E.outer i` for `i∈Fin n`, with `0≤a_i≤b_i≤1`. Put
`R=⋃_{i∈Fin n}[a_i,b_i]`, `S={z∈ℂ | Re z∈R ∧ Im z=0}` and `D={z∈ℂ | ‖z‖<1}∖S`. Because the
disk is open and `S` is closed, `E.slitDomain=D` is open in `ℂ`. -/
theorem isOpen_slitDomain : IsOpen E.slitDomain :=
  Metric.isOpen_ball.sdiff E.isClosed_slitSet

/-- **Slit domain lies in the open unit disk.** Let `n : ℕ` and `E : RadialSlitData n` have
real endpoints `a_i=E.inner i`, `b_i=E.outer i` for `i∈Fin n`, with `0≤a_i≤b_i≤1`. Put
`R=⋃_{i∈Fin n}[a_i,b_i]`, `S={z∈ℂ | Re z∈R ∧ Im z=0}` and `D={z∈ℂ | ‖z‖<1}∖S`. The domain
satisfies `E.slitDomain⊆{z∈ℂ | ‖z‖<1}`. -/
theorem slitDomain_subset_ball : E.slitDomain ⊆ Metric.ball 0 1 :=
  Set.sdiff_subset

/-- **A negative real point remains outside every radial slit.** Let `n : ℕ` and `E :
RadialSlitData n` have real endpoints `a_i=E.inner i`, `b_i=E.outer i` for `i∈Fin n`, with
`0≤a_i≤b_i≤1`. Put `R=⋃_{i∈Fin n}[a_i,b_i]`, `S={z∈ℂ | Re z∈R ∧ Im z=0}` and `D={z∈ℂ |
‖z‖<1}∖S`. The point `-1/2 : ℂ` has norm less than one and negative real part, so it
belongs to `E.slitDomain`. Thus the domain is nonempty for every finite family. -/
theorem slitDomain_nonempty : E.slitDomain.Nonempty := by
  have heq : (-1/2 : ℂ) = ((-1/2 : ℝ) : ℂ) := by push_cast; ring
  refine ⟨-1/2, ?_⟩
  rw [E.mem_slitDomain]
  refine ⟨?_, ?_⟩
  · rw [heq, Complex.norm_real, Real.norm_eq_abs]
    norm_num
  · intro h
    rw [E.mem_slitSet] at h
    have hsub := E.radiusSet_subset_Icc h.1
    rw [Set.mem_Icc, heq, Complex.ofReal_re] at hsub
    norm_num at hsub

/-- **Single slit interval from zero to one.** The family `unitInterval : RadialSlitData 1`
has `inner(i)=0` and `outer(i)=1` for its unique index. Its radius union is `[0,1]`. -/
def unitInterval : RadialSlitData 1 where
  inner := fun _ => 0
  outer := fun _ => 1
  inner_nonneg := fun _ => le_refl 0
  inner_le_outer := fun _ => zero_le_one
  outer_le_one := fun _ => le_refl 1

/-- **Radius union of the single unit interval.** For `unitInterval : RadialSlitData 1`, with
endpoints zero and one, `unitInterval.radiusSet=[0,1]`. -/
theorem unitInterval_radiusSet :
    unitInterval.radiusSet = Set.Icc 0 1 := by
  ext r
  simp only [mem_radiusSet, Set.mem_Icc]
  constructor
  · rintro ⟨i, hlo, hhi⟩
    have e1 : unitInterval.inner i = 0 := rfl
    have e2 : unitInterval.outer i = 1 := rfl
    rw [e1] at hlo
    rw [e2] at hhi
    exact ⟨hlo, hhi⟩
  · rintro ⟨hlo, hhi⟩
    exact ⟨0, hlo, hhi⟩

/-- **Real-axis segment of the single unit interval.** For `unitInterval : RadialSlitData 1`,
with endpoints zero and one, `unitInterval.slitSet={z∈ℂ | 0≤Re z≤1 ∧ Im z=0}=[0,1]×ℂ{0}`. -/
theorem unitInterval_slitSet :
    unitInterval.slitSet = Set.Icc 0 1 ×ℂ ({0} : Set ℝ) := by
  unfold slitSet
  rw [unitInterval_radiusSet]

end RadialSlitData

end Complex
