/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.Exposed
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Faces of convex polytopes

A convex polytope is the convex hull of a finite set `s` of points of a real normed space `E`.
Following Ziegler, *Lectures on Polytopes* (GTM 152), a face of a polytope `P` is the set of points
of `P` where some linear functional attains its maximum over `P`, together with the empty face. In
Mathlib this is `IsExposed ℝ P F`, which uses continuous linear functionals and also admits `∅` and
`P` itself (the zero functional). In a normed space this loses nothing: a linear functional on the
finite-dimensional span of `s` is continuous and extends to a continuous functional on `E`
(Hahn–Banach), with the same maximisers on `P`. On a space with a coarser topology the continuous
dual can be too small, which is why `E` is a normed space here.

This file proves that every face of `conv s` is the convex hull of the points of `s` it
contains, so that a polytope has only finitely many faces, and defines the face numbers
(the f-vector) and the graph (the 1-skeleton) of a polytope.
-/

@[expose] public section

open Set

namespace MathlibExt.Geometry.Polytope

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Faces of a convex polytope.** The faces of the polytope `P = conv s` spanned by a finite
set `s` in a real normed space are its exposed subsets: the empty set, and the sets of points of
`P` at which some continuous linear functional attains its maximum over `P` (the zero functional
gives `P` itself). In a normed space every linear functional on the span of `s` extends to a
continuous one (Hahn–Banach), so these are exactly the faces of `P` in the standard sense
(G. M. Ziegler, *Lectures on Polytopes*, GTM 152, cited without a theorem number), as used in his
"Face numbers of 4-polytopes and 3-spheres", Proc. ICM 2002, Section 2 (arXiv:math/0208073v2). -/
def faces (s : Finset E) : Set (Set E) :=
  {F | IsExposed ℝ (convexHull ℝ (s : Set E)) F}

/-- **A face of a polytope is the convex hull of the vertices it contains.** If `F` is a face of
`P = conv s` for a finite set `s`, then `F = conv (F ∩ s)`. In particular every face of a
polytope is again a polytope, spanned by some of the given points. -/
theorem eq_convexHull_inter_of_mem_faces {s : Finset E} {F : Set E} (hF : F ∈ faces s) :
    F = convexHull ℝ (F ∩ (s : Set E)) := by
  classical
  rcases F.eq_empty_or_nonempty with rfl | hne
  · simp
  have hFconv : Convex ℝ F := IsExposed.convex hF (convex_convexHull ℝ _)
  refine Subset.antisymm ?_ (convexHull_min inter_subset_left hFconv)
  obtain ⟨l, hl⟩ := hF hne
  intro x hx
  have hx' := hx
  rw [hl] at hx'
  obtain ⟨hxP, hxmax⟩ := hx'
  rw [Finset.convexHull_eq, mem_ofPred_eq] at hxP
  obtain ⟨w, hw0, hw1, hwx⟩ := hxP
  -- every point of `s` lies in `P`, so `l y ≤ l x`
  have hle : ∀ y ∈ s, l y ≤ l x := fun y hy =>
    hxmax y (subset_convexHull ℝ _ (Finset.mem_coe.2 hy))
  -- `l x` is the `w`-average of the values `l y`
  have hsum : ∑ y ∈ s, w y * l y = l x := by
    rw [← hwx, Finset.centerMass_eq_of_sum_1 _ _ hw1, map_sum]
    simp [map_smul, smul_eq_mul]
  have hzero : ∑ y ∈ s, w y * (l x - l y) = 0 := by
    have : ∑ y ∈ s, w y * (l x - l y) = (∑ y ∈ s, w y) * l x - ∑ y ∈ s, w y * l y := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun y _ => by ring
    rw [this, hw1, hsum]; ring
  have hterm : ∀ y ∈ s, w y * (l x - l y) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun y hy =>
      mul_nonneg (hw0 y hy) (sub_nonneg.2 (hle y hy))).1 hzero
  rw [← hwx, ← Finset.centerMass_filter_ne_zero]
  refine Finset.centerMass_mem_convexHull _ (fun y hy => hw0 y (Finset.mem_filter.1 hy).1)
    (by rw [Finset.sum_filter_ne_zero, hw1]; exact one_pos) ?_
  intro y hy
  obtain ⟨hy, hwy⟩ := Finset.mem_filter.1 hy
  refine ⟨?_, Finset.mem_coe.2 hy⟩
  have hly : l y = l x := by
    have h := hterm y hy
    rcases mul_eq_zero.1 h with h | h
    · exact absurd h hwy
    · linarith
  rw [hl]
  refine ⟨subset_convexHull ℝ _ (Finset.mem_coe.2 hy), fun z hz => ?_⟩
  change l z ≤ l y
  rw [hly]
  exact hxmax z hz

/-- **A polytope has finitely many faces.** The faces of `conv s` for a finite set `s` form a
finite set: each face is the convex hull of a subset of `s`. -/
theorem faces_finite (s : Finset E) : (faces s).Finite := by
  classical
  refine ((s.powerset.finite_toSet).image
    (fun t : Finset E => convexHull ℝ (t : Set E))).subset ?_
  intro F hF
  refine ⟨s.filter (· ∈ F), Finset.mem_coe.2 (Finset.mem_powerset.2 (Finset.filter_subset _ _)), ?_⟩
  have hcoe : ((s.filter (· ∈ F) : Finset E) : Set E) = F ∩ s := by
    ext y
    simp [and_comm]
  change convexHull ℝ ((s.filter (· ∈ F) : Finset E) : Set E) = F
  rw [hcoe]
  exact (eq_convexHull_inter_of_mem_faces hF).symm

/-- **Faces cut out by a functional.** Let `s` be finite and `T` a set of points of `s`. If a
functional `l` is at most `V` on `s`, equals `V` on `T`, and equals `V` at no other point of `s`,
then `conv T` is a face of `conv s`. -/
theorem isExposed_convexHull_of_forall_le (s : Finset E) (T : Set E) (l : StrongDual ℝ E)
    (V : ℝ) (hle : ∀ y ∈ s, l y ≤ V) (hT : ∀ y ∈ T, y ∈ s ∧ l y = V)
    (hTs : ∀ y ∈ s, l y = V → y ∈ T) :
    IsExposed ℝ (convexHull ℝ (s : Set E)) (convexHull ℝ T) := by
  rcases T.eq_empty_or_nonempty with rfl | ⟨y0, hy0⟩
  · rw [convexHull_empty]
    exact isExposed_empty
  have hP : ∀ x ∈ convexHull ℝ (s : Set E), l x ≤ V := fun x hx =>
    convexHull_min (t := {w | l w ≤ V}) (fun y hy => hle y hy)
      (convex_halfSpace_le l.toLinearMap.isLinear V) hx
  have hF : l.toExposed (convexHull ℝ (s : Set E)) ∈ faces s :=
    ContinuousLinearMap.toExposed.isExposed
  have hFs : l.toExposed (convexHull ℝ (s : Set E)) ∩ (s : Set E) = T := by
    ext y
    constructor
    · rintro ⟨⟨-, hmax⟩, hys⟩
      refine hTs y hys (le_antisymm (hle y hys) ?_)
      have h := hmax y0 (subset_convexHull ℝ _ (hT y0 hy0).1)
      rwa [(hT y0 hy0).2] at h
    · intro hy
      obtain ⟨hys, hly⟩ := hT y hy
      exact ⟨⟨subset_convexHull ℝ _ hys, fun z hz => hly ▸ hP z hz⟩, hys⟩
  rw [← hFs, ← eq_convexHull_inter_of_mem_faces hF]
  exact hF

/-- **A face of a face of a polytope is a face of the polytope.** If `F` is a face of
`P = conv s` and `G` is a face of `F`, then `G` is a face of `P`. For general convex sets the
analogous statement about exposed subsets fails (see the note in Mathlib's `IsExposed`); for
polytopes it holds because finitely many vertices leave room to tilt the functional exposing
`F` by a small multiple of the one exposing `G`. -/
theorem mem_faces_of_isExposed {s : Finset E} {F G : Set E} (hF : F ∈ faces s)
    (hG : IsExposed ℝ F G) : G ∈ faces s := by
  classical
  rcases G.eq_empty_or_nonempty with rfl | ⟨g0, hg0⟩
  · exact isExposed_empty
  have hGF : G ⊆ F := hG.subset
  have hFne : F.Nonempty := ⟨g0, hGF hg0⟩
  obtain ⟨l₁, hl₁⟩ := hF hFne
  obtain ⟨l₂, hl₂⟩ := hG ⟨g0, hg0⟩
  set P := convexHull ℝ (s : Set E) with hP
  -- the polytope `F` is spanned by the points of `s` it contains
  have hFeq : F = convexHull ℝ ((s.filter (· ∈ F) : Finset E) : Set E) := by
    have h := eq_convexHull_inter_of_mem_faces hF
    have hcoe : ((s.filter (· ∈ F) : Finset E) : Set E) = F ∩ s := by
      ext y
      simp [and_comm]
    rw [hcoe]
    exact h
  have hGface : G ∈ faces (s.filter (· ∈ F)) := by
    change IsExposed ℝ _ G
    rw [← hFeq]
    exact hG
  -- values on the vertices
  have hmem₁ : ∀ x ∈ F, x ∈ P ∧ ∀ y ∈ P, l₁ y ≤ l₁ x := by
    intro x hx
    rw [hl₁] at hx
    exact hx
  set M₁ := l₁ g0
  have hFval : ∀ x ∈ F, l₁ x = M₁ := fun x hx =>
    le_antisymm ((hmem₁ g0 (hGF hg0)).2 x (hmem₁ x hx).1)
      ((hmem₁ x hx).2 g0 (hmem₁ g0 (hGF hg0)).1)
  have hle₁ : ∀ y ∈ P, l₁ y ≤ M₁ := (hmem₁ g0 (hGF hg0)).2
  have hnotF : ∀ y ∈ s, y ∉ F → l₁ y < M₁ := by
    intro y hy hyF
    refine lt_of_le_of_ne (hle₁ y (subset_convexHull ℝ _ hy)) fun h => hyF ?_
    rw [hl₁]
    exact ⟨subset_convexHull ℝ _ hy, fun z hz => h ▸ hle₁ z hz⟩
  have hmem₂ : ∀ x ∈ G, x ∈ F ∧ ∀ y ∈ F, l₂ y ≤ l₂ x := by
    intro x hx
    rw [hl₂] at hx
    exact hx
  set M₂ := l₂ g0
  have hle₂ : ∀ y ∈ F, l₂ y ≤ M₂ := (hmem₂ g0 hg0).2
  have hGval : ∀ x ∈ G, l₂ x = M₂ := fun x hx =>
    le_antisymm (hle₂ x (hmem₂ x hx).1) ((hmem₂ x hx).2 g0 (hGF hg0))
  have hnotG : ∀ y ∈ F, y ∉ G → l₂ y < M₂ := by
    intro y hy hyG
    refine lt_of_le_of_ne (hle₂ y hy) fun h => hyG ?_
    rw [hl₂]
    exact ⟨hy, fun z hz => h ▸ hle₂ z hz⟩
  -- a positive gap `δ` for `l₁` off `F`, and a bound `B` for `|l₂ - M₂|` on `s`
  set out := s.filter (· ∉ F)
  obtain ⟨δ, hδ, hδle⟩ : ∃ δ > 0, ∀ y ∈ out, l₁ y + δ ≤ M₁ := by
    rcases out.eq_empty_or_nonempty with hout | hout
    · exact ⟨1, one_pos, fun y hy => by simp [hout] at hy⟩
    · obtain ⟨y₀, hy₀, hmax⟩ := out.exists_max_image (fun y => l₁ y) hout
      have h₀ := hnotF y₀ (Finset.mem_filter.1 hy₀).1 (Finset.mem_filter.1 hy₀).2
      exact ⟨M₁ - l₁ y₀, sub_pos.2 h₀, fun y hy => by linarith [hmax y hy]⟩
  set B := ∑ y ∈ s, |l₂ y - M₂| with hB
  have hBle : ∀ y ∈ s, |l₂ y - M₂| ≤ B := fun y hy =>
    Finset.single_le_sum (f := fun y => |l₂ y - M₂|) (fun _ _ => abs_nonneg _) hy
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set ε := δ / (B + 1) with hε
  have hεpos : 0 < ε := div_pos hδ (by linarith)
  have hεB : ε * B < δ := by
    rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    nlinarith
  set l := l₁ + ε • l₂
  have hlapp : ∀ y, l y = l₁ y + ε * l₂ y := fun y => by simp [l]
  set V := M₁ + ε * M₂
  have hGfin : G = convexHull ℝ ((s.filter (· ∈ G) : Finset E) : Set E) := by
    have h := eq_convexHull_inter_of_mem_faces hGface
    have hcoe : G ∩ ((s.filter (· ∈ F) : Finset E) : Set E) =
        ((s.filter (· ∈ G) : Finset E) : Set E) := by
      ext y
      simp only [Set.mem_inter_iff, Finset.coe_filter, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨hyG, hys, -⟩
        exact ⟨hys, hyG⟩
      · rintro ⟨hys, hyG⟩
        exact ⟨hyG, hys, hGF hyG⟩
    rw [← hcoe]
    exact h
  rw [hGfin]
  -- the tilted functional `l₁ + ε l₂` is maximal on `s` exactly at the points of `G`
  refine isExposed_convexHull_of_forall_le s _ l V ?_ ?_ ?_
  · intro y hy
    rw [hlapp]
    by_cases hyF : y ∈ F
    · rw [hFval y hyF]
      have := hle₂ y hyF
      nlinarith
    · have h1 := hδle y (Finset.mem_filter.2 ⟨hy, hyF⟩)
      have h2 : ε * (l₂ y - M₂) ≤ ε * B :=
        mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hBle y hy)) hεpos.le
      nlinarith
  · intro y hy
    obtain ⟨hys, hyG⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hy)
    refine ⟨hys, ?_⟩
    rw [hlapp, hFval y (hGF hyG), hGval y hyG]
  · intro y hy hly
    rw [hlapp] at hly
    refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hy, ?_⟩)
    by_cases hyF : y ∈ F
    · by_contra hyG
      rw [hFval y hyF] at hly
      have := hnotG y hyF hyG
      nlinarith
    · exfalso
      have h1 := hδle y (Finset.mem_filter.2 ⟨hy, hyF⟩)
      have h2 : ε * (l₂ y - M₂) ≤ ε * B :=
        mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hBle y hy)) hεpos.le
      nlinarith

/-- **Intersections of faces are faces.** For any family `A` of faces of `P = conv s`, the set
`P ∩ ⋂₀ A` is a face of `P` (for empty `A` it is `P` itself). -/
theorem inter_sInter_mem_faces (s : Finset E) (A : Set (Set E)) (hA : A ⊆ faces s) :
    convexHull ℝ (s : Set E) ∩ ⋂₀ A ∈ faces s := by
  classical
  have hfin : A.Finite := (faces_finite s).subset hA
  have heq : convexHull ℝ (s : Set E) ∩ ⋂₀ A =
      ⋂₀ ((insert (convexHull ℝ (s : Set E)) hfin.toFinset : Finset (Set E)) : Set (Set E)) := by
    rw [Finset.coe_insert, Set.sInter_insert, Set.Finite.coe_toFinset]
  rw [heq]
  refine IsExposed.sInter (Finset.insert_nonempty _ _) fun B hB => ?_
  rcases Finset.mem_insert.1 hB with rfl | hB
  · exact IsExposed.refl _
  · exact hA ((Set.Finite.mem_toFinset hfin).1 hB)

/-- **Face lattice of a polytope.** The faces of `P = conv s`, including `∅` and `P`, ordered by
inclusion. It is a finite complete lattice (`FaceLattice.instCompleteLattice`) whose meet is
intersection, with bottom the empty face and top `P`; its isomorphism class is the
combinatorial type of `P` (Ziegler, "Face numbers of 4-polytopes and 3-spheres", Proc. ICM 2002,
Section 2, arXiv:math/0208073). -/
def FaceLattice (s : Finset E) : Type _ := {F : Set E // F ∈ faces s}

namespace FaceLattice

variable {s : Finset E}

instance : PartialOrder (FaceLattice s) := inferInstanceAs (PartialOrder {F : Set E // F ∈ faces s})

instance : Finite (FaceLattice s) := (faces_finite s).to_subtype

theorem le_iff {F G : FaceLattice s} : F ≤ G ↔ F.1 ⊆ G.1 := Iff.rfl

noncomputable instance : InfSet (FaceLattice s) :=
  ⟨fun A => ⟨convexHull ℝ (s : Set E) ∩ ⋂₀ (Subtype.val '' A),
    inter_sInter_mem_faces s _ (by rintro _ ⟨F, -, rfl⟩; exact F.2)⟩⟩

noncomputable instance instCompleteLattice : CompleteLattice (FaceLattice s) :=
  completeLatticeOfInf _ fun A => by
    refine ⟨fun F hF => ?_, fun G hG => ?_⟩
    · rw [le_iff]
      exact fun x hx => hx.2 _ ⟨F, hF, rfl⟩
    · rw [le_iff]
      intro x hx
      refine ⟨IsExposed.subset G.2 hx, ?_⟩
      rintro _ ⟨F, hF, rfl⟩
      exact (le_iff.1 (hG hF)) hx

/-- **Top of the face lattice.** The top face is the polytope itself. -/
theorem coe_top : (⊤ : FaceLattice s).1 = convexHull ℝ (s : Set E) :=
  Set.Subset.antisymm (IsExposed.subset (⊤ : FaceLattice s).2)
    (le_iff.1 (le_top (a := (show FaceLattice s from
      ⟨convexHull ℝ (s : Set E), IsExposed.refl _⟩))))

/-- **Bottom of the face lattice.** The bottom face is the empty face. -/
theorem coe_bot : (⊥ : FaceLattice s).1 = ∅ :=
  Set.subset_empty_iff.1 (le_iff.1 (bot_le (a := (show FaceLattice s from ⟨∅, isExposed_empty⟩))))

end FaceLattice

/-- **Face numbers of a polytope.** For a finite set `s` and `k : ℕ`, `faceNumber s k` is the
number `f_k` of nonempty faces of the polytope `conv s` whose affine hull has dimension `k`;
`f_0` counts the vertices and `f_1` the edges. The empty face (of dimension `-1`, with
`f_{-1} = 1`) is not counted here. The count is finite by `faces_finite`. -/
noncomputable def faceNumber (s : Finset E) (k : ℕ) : ℕ :=
  {F | F ∈ faces s ∧ F.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F).direction = k}.ncard

/-- **Dimension of a polytope.** The dimension of `conv s` is the dimension of the direction of its
affine hull. -/
noncomputable def dim (s : Finset E) : ℕ :=
  Module.finrank ℝ (affineSpan ℝ (convexHull ℝ (s : Set E))).direction

/-- **The graph of a polytope.** The vertices of the graph of `conv s` are its extreme points,
and two distinct vertices `u, v` are adjacent when the segment `[u, v]` is a face of the polytope
(an edge). -/
def graph (s : Finset E) : SimpleGraph ((convexHull ℝ (s : Set E)).extremePoints ℝ) where
  Adj u v := u ≠ v ∧ IsExposed ℝ (convexHull ℝ (s : Set E)) (segment ℝ (u : E) v)
  symm := ⟨fun u v h => ⟨h.1.symm, by rw [segment_symm]; exact h.2⟩⟩
  loopless := ⟨fun u h => h.1 rfl⟩

/-- **Simplicial polytope.** The polytope `conv s` is simplicial when each of its facets (nonempty
faces of dimension `dim s - 1`) is a simplex, that is, contains exactly `dim s` vertices of the
polytope. Cyclic polytopes, and polytopes spanned by points in general position, are
simplicial. -/
def IsSimplicial (s : Finset E) : Prop :=
  ∀ F ∈ faces s, F.Nonempty →
    Module.finrank ℝ (affineSpan ℝ F).direction + 1 = dim s →
      (F ∩ (convexHull ℝ (s : Set E)).extremePoints ℝ).ncard = dim s

/-- **The vertex set of a polytope is finite.** -/
theorem extremePoints_finite (s : Finset E) :
    ((convexHull ℝ (s : Set E)).extremePoints ℝ).Finite :=
  s.finite_toSet.subset extremePoints_convexHull_subset

end MathlibExt.Geometry.Polytope
