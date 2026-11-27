/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.Subdivision.Affine
import Mathlib.Data.Finset.Sort

/-!
# Threshold coordinates of a standard simplex

For a point `x` of the real standard `n`-simplex, list its distinct positive
coordinate levels as `a₀ > ⋯ > a_d > 0`. The closed superlevel faces
`F_j = {i | a_j ≤ x_i}` form a strictly increasing chain of nonempty faces.
With `a_(d+1) = 0`, the masses `λ_j = |F_j| * (a_j - a_(j+1))` are strictly
positive and sum to one.

The affine barycentric cell of this face chain reconstructs `x` from the masses.
Conversely, each nondegenerate subdivision cell with an interior barycentric point
recovers the same face chain and coordinates under threshold extraction. This gives
a set-level equivalence between points of the standard simplex and such cell-interior
data. The finite vertex sets are lifted into the specified subdivision universe,
with their cardinalities and support conditions preserved.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory Opposite Simplicial
open scoped Simplicial

namespace SSet

/--
The finite set of distinct positive weights of a point in the real standard
`n`-simplex.
-/
noncomputable def thresholdPositiveLevels {n : ℕ}
    (x : Convexity.StdSimplex ℝ (Fin (n + 1))) : Finset ℝ :=
  (Finset.univ.filter (fun i => 0 < x.weights i)).image
    (fun i => x.weights i)

private theorem thresholdPositiveLevels_nonempty {n : ℕ}
    (x : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    (thresholdPositiveLevels x).Nonempty := by
  classical
  obtain ⟨i, hi⟩ := x.support_weights_nonempty
  have hi' : x.weights i ≠ 0 := by simpa using hi
  have hpos : 0 < x.weights i :=
    lt_of_le_of_ne (x.weights_nonneg i) hi'.symm
  exact ⟨x.weights i, Finset.mem_image.mpr
    ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos⟩, rfl⟩⟩

/--
One less than the number of distinct positive coordinate levels, giving the
dimension of the associated subdivision simplex.
-/
noncomputable def thresholdDim {n : ℕ}
    (x : Convexity.StdSimplex ℝ (Fin (n + 1))) : ℕ :=
  (thresholdPositiveLevels x).card - 1

/--
The number of distinct positive coordinate levels is `thresholdDim x + 1`.
-/
theorem thresholdPositiveLevels_card_eq {n : ℕ}
    (x : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    (thresholdPositiveLevels x).card = thresholdDim x + 1 := by
  have h := Finset.card_pos.mpr (thresholdPositiveLevels_nonempty x)
  unfold thresholdDim
  omega

/--
The distinct positive coordinate levels listed in strictly decreasing order.
-/
noncomputable def thresholdLevel {n : ℕ}
    (x : Convexity.StdSimplex ℝ (Fin (n + 1)))
    (j : Fin (thresholdDim x + 1)) : ℝ :=
  (thresholdPositiveLevels x).orderEmbOfFin
    (thresholdPositiveLevels_card_eq x) j.rev

/--
Every entry of the decreasing threshold list is strictly positive.
-/
theorem thresholdLevel_pos {n : ℕ}
    (x : Convexity.StdSimplex ℝ (Fin (n + 1)))
    (j : Fin (thresholdDim x + 1)) : 0 < thresholdLevel x j := by
  classical
  have hmem := Finset.orderEmbOfFin_mem (thresholdPositiveLevels x)
    (thresholdPositiveLevels_card_eq x) j.rev
  obtain ⟨i, hi, hil⟩ := Finset.mem_image.mp hmem
  change 0 < (thresholdPositiveLevels x).orderEmbOfFin
    (thresholdPositiveLevels_card_eq x) j.rev
  rw [← hil]
  exact (Finset.mem_filter.mp hi).2

/--
The threshold-level function is strictly antitone in its finite index.
-/
theorem thresholdLevel_strictAnti {n : ℕ}
    (x : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    StrictAnti (thresholdLevel x) := by
  intro i j hij
  exact ((thresholdPositiveLevels x).orderEmbOfFin
    (thresholdPositiveLevels_card_eq x)).strictMono
      ((Fin.rev_lt_rev (i := j) (j := i)).mpr hij)

/--
The nonempty finite chain of lifted vertices whose weights satisfy
`thresholdLevel x j ≤ x_i`, representing the closed superlevel face at threshold `j`.
-/
noncomputable def thresholdFace {n : ℕ}
    (x : Convexity.StdSimplex ℝ (Fin (n + 1)))
    (j : Fin (thresholdDim x + 1)) :
    PartialOrder.NonemptyFiniteChains (ULift.{u} (Fin (n + 1))) where
  finset := (Finset.univ.filter
    (fun i => thresholdLevel x j ≤ x.weights i)).image ULift.up
  nonempty := by
    classical
    have hmem := Finset.orderEmbOfFin_mem (thresholdPositiveLevels x)
      (thresholdPositiveLevels_card_eq x) j.rev
    obtain ⟨i, hi, hil⟩ := Finset.mem_image.mp hmem
    refine ⟨ULift.up i, Finset.mem_image.mpr ⟨i, ?_, rfl⟩⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hil ▸ le_rfl⟩
  comparable a b := le_total a b

/--
The superlevel faces associated to decreasing positive thresholds form a
monotone chain under inclusion.
-/
theorem thresholdFace_monotone {n : ℕ}
    (x : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    Monotone (thresholdFace.{u} x) := by
  intro i j hij a ha
  classical
  change a ∈ (Finset.univ.filter
    (fun k => thresholdLevel x i ≤ x.weights k)).image ULift.up at ha
  change a ∈ (Finset.univ.filter
    (fun k => thresholdLevel x j ≤ x.weights k)).image ULift.up
  obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp ha
  apply Finset.mem_image.mpr
  refine ⟨b, ?_, hba⟩
  have hb' := (Finset.mem_filter.mp hb).2
  apply Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  exact ((thresholdLevel_strictAnti x).antitone hij).trans hb'

/--
As the positive threshold levels decrease, their superlevel faces form a strictly
increasing chain.
-/
theorem thresholdFace_strictMono {n : ℕ}
    (x : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    StrictMono (thresholdFace.{u} x) := by
  intro i j hij
  have hsub : thresholdFace.{u} x i ≤ thresholdFace.{u} x j :=
    thresholdFace_monotone x hij.le
  apply lt_of_le_of_ne hsub
  intro heq
  classical
  have hmem := Finset.orderEmbOfFin_mem (thresholdPositiveLevels x)
    (thresholdPositiveLevels_card_eq x) j.rev
  obtain ⟨a, ha, hal⟩ := Finset.mem_image.mp hmem
  have haj : ULift.up a ∈ (thresholdFace.{u} x j).finset := by
    apply Finset.mem_image.mpr
    refine ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    exact hal ▸ le_rfl
  have hai : ULift.up a ∈ (thresholdFace.{u} x i).finset := heq ▸ haj
  obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp hai
  have hba' : b = a := ULift.up_injective hba
  subst b
  have hle := (Finset.mem_filter.mp hb).2
  have hlt := thresholdLevel_strictAnti x hij
  rw [hal] at hle
  exact (not_le_of_gt hlt) hle

/--
The subdivision simplex whose vertices are the nested nonempty superlevel faces
of the point's positive coordinate levels.
-/
noncomputable def thresholdSimplex {n : ℕ}
    (x : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    (SimplexCategory.sd.{u}.obj ⦋n⦌) _⦋thresholdDim x⦌ where
  obj := thresholdFace x
  map f := homOfLE
    (thresholdFace_monotone x (leOfHom f))
  map_id := by intro; subsingleton
  map_comp := by intro; subsingleton

/--
The subdivision simplex determined by the strictly increasing superlevel faces
is nondegenerate.
-/
theorem thresholdSimplex_nonDegenerate {n : ℕ}
    (x : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    thresholdSimplex.{u} x ∈
      (SimplexCategory.sd.{u}.obj ⦋n⦌).nonDegenerate
        (thresholdDim x) :=
  (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono
    (thresholdSimplex x)).mpr (thresholdFace_strictMono x)

/--
The next lower positive threshold, with zero used after the last threshold.
-/
noncomputable def thresholdNextLevel {n : ℕ}
    (x : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    Fin (thresholdDim x + 1) → ℝ :=
  Fin.lastCases 0 (fun j => thresholdLevel x j.succ)

@[simp]
private theorem thresholdNextLevel_last {n : ℕ}
    (x : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    thresholdNextLevel x (Fin.last (thresholdDim x)) = 0 := by
  simp [thresholdNextLevel]

@[simp]
private theorem thresholdNextLevel_castSucc {n : ℕ}
    (x : Convexity.StdSimplex ℝ (Fin (n + 1)))
    (j : Fin (thresholdDim x)) :
    thresholdNextLevel x j.castSucc = thresholdLevel x j.succ := by
  simp [thresholdNextLevel]

/--
For superlevel face `F_j` and descending thresholds `a_j`, the mass
`λ_j = |F_j| * (a_j - a_(j+1))`, with the final next threshold defined as zero.
-/
noncomputable def thresholdLambda {n : ℕ}
    (x : Convexity.StdSimplex ℝ (Fin (n + 1)))
    (j : Fin (thresholdDim x + 1)) : ℝ :=
  ((Finset.univ.filter
    (fun i => thresholdLevel x j ≤ x.weights i)).card : ℝ) *
    (thresholdLevel x j - thresholdNextLevel x j)

private theorem thresholdSuperlevel_nonempty {n : ℕ}
    (x : Convexity.StdSimplex ℝ (Fin (n + 1)))
    (j : Fin (thresholdDim x + 1)) :
    (Finset.univ.filter
      (fun i => thresholdLevel x j ≤ x.weights i)).Nonempty := by
  classical
  have hmem := Finset.orderEmbOfFin_mem (thresholdPositiveLevels x)
    (thresholdPositiveLevels_card_eq x) j.rev
  obtain ⟨i, hi, hil⟩ := Finset.mem_image.mp hmem
  exact ⟨i, Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, hil ▸ le_rfl⟩⟩

/--
Every threshold mass `λ_j` is strictly positive.
-/
theorem thresholdLambda_pos {n : ℕ}
    (x : Convexity.StdSimplex ℝ (Fin (n + 1)))
    (j : Fin (thresholdDim x + 1)) :
    0 < thresholdLambda x j := by
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp only [thresholdLambda, thresholdNextLevel_last, sub_zero]
    apply mul_pos
    · exact_mod_cast Finset.card_pos.mpr
        (thresholdSuperlevel_nonempty x _)
    · exact thresholdLevel_pos x _
  · simp only [thresholdLambda, thresholdNextLevel_castSucc]
    apply mul_pos
    · exact_mod_cast Finset.card_pos.mpr
        (thresholdSuperlevel_nonempty x _)
    · exact sub_pos.mpr ((thresholdLevel_strictAnti x) (by simp))

private theorem threshold_telescope {n : ℕ}
    (x : Convexity.StdSimplex ℝ (Fin (n + 1)))
    (r : Fin (thresholdDim x + 1)) :
    (∑ j ∈ Finset.Icc r (Fin.last (thresholdDim x)),
      (thresholdLevel x j - thresholdNextLevel x j)) =
        thresholdLevel x r := by
  induction r using Fin.reverseInduction with
  | last => simp
  | cast r ih =>
      rw [Finset.Icc_eq_cons_Ioc (Fin.le_last r.castSucc),
        Finset.sum_cons]
      have hI : Finset.Ioc r.castSucc (Fin.last (thresholdDim x)) =
          Finset.Icc r.succ (Fin.last (thresholdDim x)) := by
        ext k
        simp only [Finset.mem_Ioc, Finset.mem_Icc]
        exact and_congr Fin.castSucc_lt_iff_succ_le Iff.rfl
      rw [hI, ih, thresholdNextLevel_castSucc]
      ring

private noncomputable def cellFace {n : SimplexCategory} {d : ℕ}
    (σ : (SimplexCategory.sd.{u}.obj n) _⦋d⦌)
    (j : Fin (d + 1)) : Finset (Fin (n.len + 1)) :=
  (σ.obj j).finset.image (fun a => a.down)

private theorem cellFace_nonempty {n : SimplexCategory} {d : ℕ}
    (σ : (SimplexCategory.sd.{u}.obj n) _⦋d⦌)
    (j : Fin (d + 1)) : (cellFace σ j).Nonempty :=
  (σ.obj j).nonempty.image _

private theorem cellFace_monotone {n : SimplexCategory} {d : ℕ}
    (σ : (SimplexCategory.sd.{u}.obj n) _⦋d⦌) :
    Monotone (cellFace σ) := by
  intro i j hij
  apply Finset.image_mono
  exact (σ.map (homOfLE hij)).le

private noncomputable def cellTerm {n : SimplexCategory} {d : ℕ}
    (σ : (SimplexCategory.sd.{u}.obj n) _⦋d⦌)
    (q : Convexity.StdSimplex ℝ (Fin (d + 1)))
    (j : Fin (d + 1)) : ℝ :=
  q.weights j / (cellFace σ j).card

private noncomputable def cellLevel {n : SimplexCategory} {d : ℕ}
    (σ : (SimplexCategory.sd.{u}.obj n) _⦋d⦌)
    (q : Convexity.StdSimplex ℝ (Fin (d + 1)))
    (j : Fin (d + 1)) : ℝ :=
  ∑ k ∈ Finset.Icc j (Fin.last d), cellTerm σ q k

private theorem cellTerm_pos {n : SimplexCategory} {d : ℕ}
    (σ : (SimplexCategory.sd.{u}.obj n) _⦋d⦌)
    (q : Convexity.StdSimplex ℝ (Fin (d + 1)))
    (hq : ∀ j, 0 < q.weights j) (j : Fin (d + 1)) :
    0 < cellTerm σ q j := by
  apply div_pos (hq j)
  exact_mod_cast Finset.card_pos.mpr (cellFace_nonempty σ j)

private theorem cellLevel_pos {n : SimplexCategory} {d : ℕ}
    (σ : (SimplexCategory.sd.{u}.obj n) _⦋d⦌)
    (q : Convexity.StdSimplex ℝ (Fin (d + 1)))
    (hq : ∀ j, 0 < q.weights j) (j : Fin (d + 1)) :
    0 < cellLevel σ q j := by
  apply Finset.sum_pos
  · intro k _
    exact cellTerm_pos σ q hq k
  · exact ⟨j, Finset.mem_Icc.mpr ⟨le_rfl, Fin.le_last j⟩⟩

private theorem cellLevel_strictAnti {n : SimplexCategory} {d : ℕ}
    (σ : (SimplexCategory.sd.{u}.obj n) _⦋d⦌)
    (q : Convexity.StdSimplex ℝ (Fin (d + 1)))
    (hq : ∀ j, 0 < q.weights j) : StrictAnti (cellLevel σ q) := by
  intro i j hij
  have hsub : Finset.Icc j (Fin.last d) ⊆
      Finset.Ioc i (Fin.last d) := by
    intro k hk
    simp only [Finset.mem_Icc, Finset.mem_Ioc] at hk ⊢
    exact ⟨hij.trans_le hk.1, hk.2⟩
  have hle :
      (∑ k ∈ Finset.Icc j (Fin.last d), cellTerm σ q k) ≤
        ∑ k ∈ Finset.Ioc i (Fin.last d), cellTerm σ q k :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun k _ _ => (cellTerm_pos σ q hq k).le)
  change (∑ k ∈ Finset.Icc j (Fin.last d), cellTerm σ q k) <
    ∑ k ∈ Finset.Icc i (Fin.last d), cellTerm σ q k
  rw [Finset.Icc_eq_cons_Ioc (Fin.le_last i), Finset.sum_cons]
  exact hle.trans_lt (by
    have hpos := cellTerm_pos σ q hq i
    linarith)

private theorem sdCellMap_weights_apply_eq
    {n : SimplexCategory} {d : ℕ}
    (σ : (SimplexCategory.sd.{u}.obj n) _⦋d⦌)
    (q : Convexity.StdSimplex ℝ (Fin (d + 1)))
    (i : Fin (n.len + 1)) :
    (SimplexCategory.sdCellMap σ q).weights i =
      ∑ j, if i ∈ cellFace σ j then cellTerm σ q j else 0 := by
  classical
  rw [SimplexCategory.sdCellMap_weights_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [Convexity.StdSimplex.weights_subBarycenter,
    Finsupp.finsetSum_apply]
  change q.weights j *
      (∑ b ∈ cellFace σ j,
        (Finsupp.single b ((cellFace σ j).card : ℝ)⁻¹) i) =
    if i ∈ cellFace σ j then cellTerm σ q j else 0
  by_cases h : i ∈ cellFace σ j
  · simp only [h, ↓reduceIte]
    simp only [cellTerm, div_eq_mul_inv]
    congr 1
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hbi
      simp [hbi]
    · exact fun hi => (hi h).elim
  · simp only [h, ↓reduceIte]
    apply mul_eq_zero_of_right
    rw [Finset.sum_eq_zero]
    intro b hb
    by_cases hbi : b = i
    · subst b
      exact (h hb).elim
    · simp [hbi]

set_option backward.isDefEq.respectTransparency false in
private theorem cellFace_thresholdSimplex {n : ℕ}
    (x : Convexity.StdSimplex ℝ (Fin (n + 1)))
    (j : Fin (thresholdDim x + 1)) :
    cellFace (thresholdSimplex.{u} x) j =
      Finset.univ.filter (fun i => thresholdLevel x j ≤ x.weights i) := by
  classical
  change ((Finset.univ.filter
    (fun i => thresholdLevel x j ≤ x.weights i)).image
      (ULift.up : Fin (n + 1) → ULift.{u} (Fin (n + 1)))).image
        (fun a => a.down) =
    Finset.univ.filter (fun i => thresholdLevel x j ≤ x.weights i)
  rw [Finset.image_image]
  have hfun : ((fun a : ULift.{u} (Fin (n + 1)) => a.down) ∘
      (ULift.up : Fin (n + 1) → ULift.{u} (Fin (n + 1)))) = id := rfl
  rw [hfun, Finset.image_id]

/--
A lifted vertex `i` belongs to threshold face `j` exactly when
`thresholdLevel x j ≤ x_i`.
-/
theorem mem_thresholdSimplex_face_iff {n : ℕ}
    (x : Convexity.StdSimplex ℝ (Fin (n + 1)))
    (j : Fin (thresholdDim x + 1)) (i : Fin (n + 1)) :
    ULift.up i ∈ ((thresholdSimplex.{u} x).obj j).finset ↔
      thresholdLevel x j ≤ x.weights i := by
  classical
  change ULift.up i ∈ (Finset.univ.filter
    (fun k => thresholdLevel x j ≤ x.weights k)).image ULift.up ↔ _
  simp

/--
The cardinality of a threshold face equals the number of original vertex indices
whose weights lie at or above its threshold, independently of the lifting universe.
-/
theorem thresholdFace_card {n : ℕ}
    (x : Convexity.StdSimplex ℝ (Fin (n + 1)))
    (j : Fin (thresholdDim x + 1)) :
    (thresholdFace.{u} x j).finset.card =
      (Finset.univ.filter
        (fun i => thresholdLevel x j ≤ x.weights i)).card := by
  unfold thresholdFace
  exact Finset.card_image_of_injective _ ULift.up_injective

/--
Every vertex belonging to a threshold face has strictly positive weight in the
original point.
-/
theorem weight_pos_of_mem_thresholdSimplex_face {n : ℕ}
    (x : Convexity.StdSimplex ℝ (Fin (n + 1)))
    (j : Fin (thresholdDim x + 1)) (i : Fin (n + 1))
    (hi : ULift.up i ∈ ((thresholdSimplex.{u} x).obj j).finset) :
    0 < x.weights i :=
  (thresholdLevel_pos x j).trans_le
    ((mem_thresholdSimplex_face_iff (x := x) j i).mp hi)

/--
A lifted vertex belongs to the last threshold face exactly when its original
coordinate is strictly positive.
-/
theorem mem_thresholdSimplex_last_iff {n : ℕ}
    (x : Convexity.StdSimplex ℝ (Fin (n + 1))) (i : Fin (n + 1)) :
    ULift.up i ∈
        ((thresholdSimplex.{u} x).obj (Fin.last (thresholdDim x))).finset ↔
      0 < x.weights i := by
  rw [mem_thresholdSimplex_face_iff]
  constructor
  · exact fun h => (thresholdLevel_pos x _).trans_le h
  · intro hi
    have hiL : x.weights i ∈ thresholdPositiveLevels x :=
      Finset.mem_image.mpr ⟨i,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩
    let a := (thresholdPositiveLevels x).orderIsoOfFin
      (thresholdPositiveLevels_card_eq x) |>.symm ⟨x.weights i, hiL⟩
    let r : Fin (thresholdDim x + 1) := a.rev
    have hr : thresholdLevel x r = x.weights i := by
      change (thresholdPositiveLevels x).orderEmbOfFin
        (thresholdPositiveLevels_card_eq x) r.rev = x.weights i
      rw [show r.rev = a from Fin.rev_rev a]
      exact congrArg Subtype.val
        (((thresholdPositiveLevels x).orderIsoOfFin
          (thresholdPositiveLevels_card_eq x)).apply_symm_apply
            ⟨x.weights i, hiL⟩)
    rw [← hr]
    exact (thresholdLevel_strictAnti x).antitone (Fin.le_last r)

/--
A coordinate is zero exactly when its lifted vertex does not belong to the
maximal threshold face.
-/
theorem weight_eq_zero_iff_not_mem_thresholdSimplex_last {n : ℕ}
    (x : Convexity.StdSimplex ℝ (Fin (n + 1))) (i : Fin (n + 1)) :
    x.weights i = 0 ↔
      ULift.up i ∉
        ((thresholdSimplex.{u} x).obj
          (Fin.last (thresholdDim x))).finset := by
  rw [mem_thresholdSimplex_last_iff]
  constructor
  · intro hzero hpos
    exact (ne_of_gt hpos) hzero
  · intro h
    exact le_antisymm (le_of_not_gt h) (x.weights_nonneg i)

open Classical in
/--
A standard-simplex vertex has the single positive threshold level one.
-/
@[simp]
theorem thresholdPositiveLevels_single {n : ℕ} (i : Fin (n + 1)) :
    thresholdPositiveLevels
      (Convexity.StdSimplex.single (R := ℝ) i) = {1} := by
  ext r
  constructor
  · intro hr
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hr
    have hpos := (Finset.mem_filter.mp ha).2
    rw [Convexity.StdSimplex.weights_single,
      Finsupp.single_apply] at hpos ⊢
    split at hpos <;> simp_all
  · intro hr
    have hr' : r = 1 := by simpa using hr
    subst r
    apply Finset.mem_image.mpr
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · rw [Convexity.StdSimplex.weights_single,
        Finsupp.single_eq_same]
      norm_num
    · rw [Convexity.StdSimplex.weights_single,
        Finsupp.single_eq_same]

/--
A standard-simplex vertex determines a zero-dimensional threshold simplex.
-/
@[simp]
theorem thresholdDim_single {n : ℕ} (i : Fin (n + 1)) :
    thresholdDim (Convexity.StdSimplex.single (R := ℝ) i) = 0 := by
  rw [thresholdDim, thresholdPositiveLevels_single]
  simp

open Classical in
/--
The unique positive threshold level of a standard-simplex vertex is one.
-/
@[simp]
theorem thresholdLevel_single {n : ℕ} (i : Fin (n + 1))
    (j : Fin (thresholdDim
      (Convexity.StdSimplex.single (R := ℝ) i) + 1)) :
    thresholdLevel (Convexity.StdSimplex.single (R := ℝ) i) j = 1 := by
  unfold thresholdLevel
  have hmem := Finset.orderEmbOfFin_mem
    (thresholdPositiveLevels (Convexity.StdSimplex.single (R := ℝ) i))
    (thresholdPositiveLevels_card_eq
      (Convexity.StdSimplex.single (R := ℝ) i)) j.rev
  simpa only [thresholdPositiveLevels_single,
    Finset.mem_singleton] using hmem

/--
The threshold face of the vertex at `i` contains exactly the lifted vertex `i`.
-/
theorem mem_thresholdSimplex_single_face_iff {n : ℕ}
    (i k : Fin (n + 1))
    (j : Fin (thresholdDim
      (Convexity.StdSimplex.single (R := ℝ) i) + 1)) :
    ULift.up k ∈
        ((thresholdSimplex.{u}
          (Convexity.StdSimplex.single (R := ℝ) i)).obj j).finset ↔
      k = i := by
  classical
  rw [mem_thresholdSimplex_face_iff, thresholdLevel_single,
    Convexity.StdSimplex.weights_single, Finsupp.single_apply]
  by_cases h : i = k
  · simp [h]
  · have hk : k ≠ i := Ne.symm h
    simp [h, hk]

private theorem thresholdLambda_div_card {n : ℕ}
    (x : Convexity.StdSimplex ℝ (Fin (n + 1)))
    (j : Fin (thresholdDim x + 1)) :
    thresholdLambda x j /
        ((cellFace (thresholdSimplex.{u} x) j).card : ℝ) =
      thresholdLevel x j - thresholdNextLevel x j := by
  have hcard : (Finset.univ.filter
      (fun i => thresholdLevel x j ≤ x.weights i)).card =
      (cellFace (thresholdSimplex.{u} x) j).card := by
    rw [cellFace_thresholdSimplex]
  unfold thresholdLambda
  rw [hcard]
  have hc : ((cellFace (thresholdSimplex.{u} x) j).card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_pos.mpr
      (cellFace_nonempty (thresholdSimplex.{u} x) j) |>.ne'
  field_simp

private theorem threshold_mem_iff {n : ℕ}
    (x : Convexity.StdSimplex ℝ (Fin (n + 1)))
    (r j : Fin (thresholdDim x + 1)) :
    thresholdLevel x j ≤ thresholdLevel x r ↔ r ≤ j := by
  constructor
  · intro h
    by_contra hrj
    have hjr : j < r := lt_of_not_ge hrj
    exact (not_le_of_gt (thresholdLevel_strictAnti x hjr)) h
  · intro hrj
    exact (thresholdLevel_strictAnti x).antitone hrj

private theorem threshold_raw_reconstruction {n : ℕ}
    (x : Convexity.StdSimplex ℝ (Fin (n + 1)))
    (i : Fin (n + 1)) :
    (∑ j, if i ∈ cellFace (thresholdSimplex.{u} x) j then
        thresholdLambda x j /
          ((cellFace (thresholdSimplex.{u} x) j).card : ℝ)
      else 0) = x.weights i := by
  classical
  by_cases hi : 0 < x.weights i
  · have hiL : x.weights i ∈ thresholdPositiveLevels x :=
      Finset.mem_image.mpr ⟨i,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩
    let a := (thresholdPositiveLevels x).orderIsoOfFin
      (thresholdPositiveLevels_card_eq x) |>.symm ⟨x.weights i, hiL⟩
    let r : Fin (thresholdDim x + 1) := a.rev
    have hr : thresholdLevel x r = x.weights i := by
      change (thresholdPositiveLevels x).orderEmbOfFin
        (thresholdPositiveLevels_card_eq x) r.rev = x.weights i
      rw [show r.rev = a from Fin.rev_rev a]
      exact congrArg Subtype.val
        (((thresholdPositiveLevels x).orderIsoOfFin
          (thresholdPositiveLevels_card_eq x)).apply_symm_apply
            ⟨x.weights i, hiL⟩)
    calc
      (∑ j, if i ∈ cellFace (thresholdSimplex.{u} x) j then
          thresholdLambda x j /
            ((cellFace (thresholdSimplex.{u} x) j).card : ℝ)
        else 0) =
          ∑ j, if r ≤ j then
            (thresholdLevel x j - thresholdNextLevel x j) else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        have hmem : i ∈ cellFace (thresholdSimplex.{u} x) j ↔
            r ≤ j := by
          rw [cellFace_thresholdSimplex, Finset.mem_filter]
          simp only [Finset.mem_univ, true_and]
          rw [← hr]
          exact threshold_mem_iff x r j
        by_cases hrj : r ≤ j
        · have hm := hmem.mpr hrj
          simp [hm, hrj, thresholdLambda_div_card]
        · have hm : i ∉ cellFace (thresholdSimplex.{u} x) j :=
            fun h => hrj (hmem.mp h)
          simp [hm, hrj]
      _ = ∑ j ∈ Finset.Icc r (Fin.last (thresholdDim x)),
          (thresholdLevel x j - thresholdNextLevel x j) := by
        rw [← Finset.sum_filter]
        congr 1
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_Icc, Fin.le_last, and_true]
      _ = thresholdLevel x r := threshold_telescope x r
      _ = x.weights i := hr
  · have hi0 : x.weights i = 0 :=
      le_antisymm (le_of_not_gt hi) (x.weights_nonneg i)
    calc
      (∑ j, if i ∈ cellFace (thresholdSimplex.{u} x) j then
          thresholdLambda x j /
            ((cellFace (thresholdSimplex.{u} x) j).card : ℝ)
        else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        have hmem : i ∉ cellFace (thresholdSimplex.{u} x) j := by
          rw [cellFace_thresholdSimplex, Finset.mem_filter]
          simp only [Finset.mem_univ, true_and, not_le, hi0]
          exact thresholdLevel_pos x j
        simp [hmem]
      _ = x.weights i := hi0.symm

private theorem sum_threshold_face_contribution {n : ℕ}
    (x : Convexity.StdSimplex ℝ (Fin (n + 1)))
    (j : Fin (thresholdDim x + 1)) :
    (∑ i, if i ∈ cellFace (thresholdSimplex.{u} x) j then
        thresholdLambda x j /
          ((cellFace (thresholdSimplex.{u} x) j).card : ℝ)
      else 0) = thresholdLambda x j := by
  classical
  rw [← Finset.sum_filter]
  have hfilter : Finset.univ.filter
      (fun i => i ∈ cellFace (thresholdSimplex.{u} x) j) =
      cellFace (thresholdSimplex.{u} x) j := by
    ext i
    simp
  rw [hfilter, Finset.sum_const, nsmul_eq_mul]
  have hc : ((cellFace (thresholdSimplex.{u} x) j).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr
      (cellFace_nonempty (thresholdSimplex.{u} x) j)).ne'
  field_simp

/--
The positive threshold masses sum to one.
-/
theorem thresholdLambda_sum {n : ℕ}
    (x : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    ∑ j, thresholdLambda x j = 1 := by
  classical
  calc
    (∑ j, thresholdLambda x j) =
        ∑ j, ∑ i, if i ∈ cellFace (thresholdSimplex.{0} x) j then
          thresholdLambda x j /
            ((cellFace (thresholdSimplex.{0} x) j).card : ℝ)
        else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      exact (sum_threshold_face_contribution x j).symm
    _ = ∑ i, ∑ j, if i ∈ cellFace (thresholdSimplex.{0} x) j then
          thresholdLambda x j /
            ((cellFace (thresholdSimplex.{0} x) j).card : ℝ)
        else 0 := Finset.sum_comm
    _ = ∑ i, x.weights i := by
      apply Finset.sum_congr rfl
      intro i _
      exact threshold_raw_reconstruction x i
    _ = 1 := x.total_of_fintype

/--
The standard-simplex point with coordinates given by the threshold masses,
all of which are strictly positive.
-/
noncomputable def thresholdWeights {n : ℕ}
    (x : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    Convexity.StdSimplex ℝ (Fin (thresholdDim x + 1)) where
  weights := Finsupp.equivFunOnFinite.symm (thresholdLambda x)
  nonneg j := by
    simpa using (thresholdLambda_pos x j).le
  total := by
    simpa [Finsupp.sum_fintype] using thresholdLambda_sum x

/--
The `j`-th coordinate of the threshold weight point is `thresholdLambda x j`.
-/
@[simp]
theorem thresholdWeights_weights {n : ℕ}
    (x : Convexity.StdSimplex ℝ (Fin (n + 1)))
    (j : Fin (thresholdDim x + 1)) :
    (thresholdWeights x).weights j = thresholdLambda x j := by
  simp [thresholdWeights]

/--
Every coordinate of the threshold weight point is strictly positive.
-/
theorem thresholdWeights_pos {n : ℕ}
    (x : Convexity.StdSimplex ℝ (Fin (n + 1)))
    (j : Fin (thresholdDim x + 1)) :
    0 < (thresholdWeights x).weights j := by
  rw [thresholdWeights_weights]
  exact thresholdLambda_pos x j

/--
Evaluating the affine cell map of the threshold simplex at its threshold weight
point reconstructs the original standard-simplex point.
-/
theorem sdCellMap_threshold {n : ℕ}
    (x : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    SimplexCategory.sdCellMap (thresholdSimplex.{u} x)
      (thresholdWeights x) = x := by
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro i
  rw [sdCellMap_weights_apply_eq]
  simp only [cellTerm, thresholdWeights_weights]
  exact threshold_raw_reconstruction x i

/--
For an injective ambient simplex map, the affine cell of the mapped threshold
simplex with the original threshold weights reconstructs the ambient image of
the original point.
-/
theorem sdCellMap_threshold_natural_mono {m n : SimplexCategory}
    (f : m ⟶ n) [Mono f]
    (x : Convexity.StdSimplex ℝ (Fin (m.len + 1))) :
    SimplexCategory.sdCellMap
        ((SimplexCategory.sd.{u}.map f).app _ (thresholdSimplex.{u} x))
        (thresholdWeights x) =
      Convexity.StdSimplex.map f x := by
  have h := ContinuousMap.congr_fun
    (SimplexCategory.sdCellMap_natural_mono f (thresholdSimplex.{u} x))
    (thresholdWeights x)
  change _ = Convexity.StdSimplex.map f
    (SimplexCategory.sdCellMap (thresholdSimplex.{u} x)
      (thresholdWeights x)) at h
  rw [sdCellMap_threshold] at h
  exact h

private theorem cellLevel_le_weight_of_mem
    {n : SimplexCategory} {d : ℕ}
    (σ : (SimplexCategory.sd.{u}.obj n) _⦋d⦌)
    (q : Convexity.StdSimplex ℝ (Fin (d + 1)))
    (hq : ∀ j, 0 < q.weights j) {i : Fin (n.len + 1)}
    {j : Fin (d + 1)} (hi : i ∈ cellFace σ j) :
    cellLevel σ q j ≤ (SimplexCategory.sdCellMap σ q).weights i := by
  classical
  rw [sdCellMap_weights_apply_eq]
  change (∑ k ∈ Finset.Icc j (Fin.last d), cellTerm σ q k) ≤
    ∑ k, if i ∈ cellFace σ k then cellTerm σ q k else 0
  calc
    (∑ k ∈ Finset.Icc j (Fin.last d), cellTerm σ q k) =
        ∑ k ∈ Finset.Icc j (Fin.last d),
          if i ∈ cellFace σ k then cellTerm σ q k else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      have hik : i ∈ cellFace σ k :=
        (cellFace_monotone σ (Finset.mem_Icc.mp hk).1) hi
      simp [hik]
    _ ≤ ∑ k, if i ∈ cellFace σ k then cellTerm σ q k else 0 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun k _ _ => by
          by_cases hik : i ∈ cellFace σ k
          · simp [hik, (cellTerm_pos σ q hq k).le]
          · simp [hik])

private theorem weight_lt_cellLevel_of_not_mem
    {n : SimplexCategory} {d : ℕ}
    (σ : (SimplexCategory.sd.{u}.obj n) _⦋d⦌)
    (q : Convexity.StdSimplex ℝ (Fin (d + 1)))
    (hq : ∀ j, 0 < q.weights j) {i : Fin (n.len + 1)}
    {j : Fin (d + 1)} (hi : i ∉ cellFace σ j) :
    (SimplexCategory.sdCellMap σ q).weights i < cellLevel σ q j := by
  classical
  rw [sdCellMap_weights_apply_eq]
  let f : Fin (d + 1) → ℝ := fun k =>
    if i ∈ cellFace σ k then cellTerm σ q k else 0
  have hsum : (∑ k ∈ Finset.Ioc j (Fin.last d), f k) =
      ∑ k, f k := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro k _ hk
    have hkj : k ≤ j := by
      have hnot : ¬j < k := by
        intro hjk
        exact hk (Finset.mem_Ioc.mpr ⟨hjk, Fin.le_last k⟩)
      exact le_of_not_gt hnot
    have hik : i ∉ cellFace σ k := by
      intro hik
      exact hi ((cellFace_monotone σ hkj) hik)
    simp [f, hik]
  have hle :
      (∑ k ∈ Finset.Ioc j (Fin.last d), f k) ≤
        ∑ k ∈ Finset.Ioc j (Fin.last d), cellTerm σ q k := by
    apply Finset.sum_le_sum
    intro k _
    by_cases hik : i ∈ cellFace σ k
    · simp [f, hik]
    · simp [f, hik, (cellTerm_pos σ q hq k).le]
  change (∑ k, f k) <
    ∑ k ∈ Finset.Icc j (Fin.last d), cellTerm σ q k
  rw [← hsum, Finset.Icc_eq_cons_Ioc (Fin.le_last j),
    Finset.sum_cons]
  exact hle.trans_lt (by
    have hpos := cellTerm_pos σ q hq j
    linarith)

private theorem mem_cellFace_iff_cellLevel_le
    {n : SimplexCategory} {d : ℕ}
    (σ : (SimplexCategory.sd.{u}.obj n) _⦋d⦌)
    (q : Convexity.StdSimplex ℝ (Fin (d + 1)))
    (hq : ∀ j, 0 < q.weights j) (i : Fin (n.len + 1))
    (j : Fin (d + 1)) :
    i ∈ cellFace σ j ↔
      cellLevel σ q j ≤ (SimplexCategory.sdCellMap σ q).weights i := by
  constructor
  · exact cellLevel_le_weight_of_mem σ q hq
  · intro h
    by_contra hi
    exact (not_le_of_gt
      (weight_lt_cellLevel_of_not_mem σ q hq hi)) h

private theorem exists_new_cellFace_vertex
    {n : SimplexCategory} {d : ℕ}
    (σ : (SimplexCategory.sd.{u}.obj n) _⦋d⦌)
    (hσ : StrictMono σ.obj) (j : Fin (d + 1)) :
    ∃ i : Fin (n.len + 1), i ∈ cellFace σ j ∧
      ∀ k < j, i ∉ cellFace σ k := by
  obtain rfl | ⟨j, rfl⟩ := j.eq_zero_or_eq_succ
  · obtain ⟨i, hi⟩ := cellFace_nonempty σ 0
    exact ⟨i, hi, fun k hk => (Fin.not_lt_zero k hk).elim⟩
  · have hss : (σ.obj j.castSucc).finset ⊂ (σ.obj j.succ).finset :=
      hσ (by simp)
    obtain ⟨a, ha, ha'⟩ := Finset.exists_of_ssubset hss
    refine ⟨a.down, Finset.mem_image.mpr ⟨a, ha, rfl⟩, ?_⟩
    intro k hk hmem
    have hkj : k ≤ j.castSucc := by
      rcases Fin.succ_le_or_le_castSucc k j with h | h
      · exact (not_le_of_gt hk h).elim
      · exact h
    have hmem' := (cellFace_monotone σ hkj) hmem
    obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp hmem'
    have hba' : b = a := ULift.down_injective hba
    exact ha' (hba' ▸ hb)

private theorem weight_eq_cellLevel_of_first
    {n : SimplexCategory} {d : ℕ}
    (σ : (SimplexCategory.sd.{u}.obj n) _⦋d⦌)
    (q : Convexity.StdSimplex ℝ (Fin (d + 1)))
    {i : Fin (n.len + 1)} {j : Fin (d + 1)}
    (hi : i ∈ cellFace σ j)
    (hfirst : ∀ k < j, i ∉ cellFace σ k) :
    (SimplexCategory.sdCellMap σ q).weights i = cellLevel σ q j := by
  classical
  rw [sdCellMap_weights_apply_eq]
  let f : Fin (d + 1) → ℝ := fun k =>
    if i ∈ cellFace σ k then cellTerm σ q k else 0
  change (∑ k, f k) =
    ∑ k ∈ Finset.Icc j (Fin.last d), cellTerm σ q k
  calc
    (∑ k, f k) = ∑ k ∈ Finset.Icc j (Fin.last d), f k := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro k _ hk
      have hkj : k < j := by
        have hnot : ¬j ≤ k := by
          intro hjk
          exact hk (Finset.mem_Icc.mpr ⟨hjk, Fin.le_last k⟩)
        exact lt_of_not_ge hnot
      have hmem : i ∉ cellFace σ k := hfirst k hkj
      simp [f, hmem]
    _ = ∑ k ∈ Finset.Icc j (Fin.last d), cellTerm σ q k := by
      apply Finset.sum_congr rfl
      intro k hk
      have hmem : i ∈ cellFace σ k :=
        (cellFace_monotone σ (Finset.mem_Icc.mp hk).1) hi
      simp [f, hmem]

private theorem exists_weight_eq_cellLevel
    {n : SimplexCategory} {d : ℕ}
    (σ : (SimplexCategory.sd.{u}.obj n) _⦋d⦌)
    (hσ : StrictMono σ.obj)
    (q : Convexity.StdSimplex ℝ (Fin (d + 1)))
    (j : Fin (d + 1)) :
    ∃ i : Fin (n.len + 1),
      (SimplexCategory.sdCellMap σ q).weights i = cellLevel σ q j := by
  classical
  obtain ⟨i, hi, hfirst⟩ := exists_new_cellFace_vertex σ hσ j
  exact ⟨i, weight_eq_cellLevel_of_first σ q hi hfirst⟩

private theorem weight_eq_zero_of_not_mem_last
    {n : SimplexCategory} {d : ℕ}
    (σ : (SimplexCategory.sd.{u}.obj n) _⦋d⦌)
    (q : Convexity.StdSimplex ℝ (Fin (d + 1)))
    {i : Fin (n.len + 1)}
    (hi : i ∉ cellFace σ (Fin.last d)) :
    (SimplexCategory.sdCellMap σ q).weights i = 0 := by
  rw [sdCellMap_weights_apply_eq]
  apply Finset.sum_eq_zero
  intro j _
  have hij : i ∉ cellFace σ j := by
    intro hij
    exact hi ((cellFace_monotone σ (Fin.le_last j)) hij)
  simp [hij]

private theorem exists_cellLevel_eq_weight_of_pos
    {n : SimplexCategory} {d : ℕ}
    (σ : (SimplexCategory.sd.{u}.obj n) _⦋d⦌)
    (q : Convexity.StdSimplex ℝ (Fin (d + 1)))
    {i : Fin (n.len + 1)}
    (hi : 0 < (SimplexCategory.sdCellMap σ q).weights i) :
    ∃ j : Fin (d + 1),
      cellLevel σ q j = (SimplexCategory.sdCellMap σ q).weights i := by
  classical
  have hlast : i ∈ cellFace σ (Fin.last d) := by
    by_contra h
    rw [weight_eq_zero_of_not_mem_last σ q h] at hi
    exact lt_irrefl 0 hi
  let J : Finset (Fin (d + 1)) :=
    Finset.univ.filter (fun j => i ∈ cellFace σ j)
  have hJ : J.Nonempty := by
    exact ⟨Fin.last d, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hlast⟩⟩
  let j := J.min' hJ
  have hjmem : i ∈ cellFace σ j :=
    (Finset.mem_filter.mp (J.min'_mem hJ)).2
  have hfirst : ∀ k < j, i ∉ cellFace σ k := by
    intro k hkj hk
    have hkJ : k ∈ J :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩
    exact (not_le_of_gt hkj) (J.min'_le k hkJ)
  exact ⟨j, (weight_eq_cellLevel_of_first σ q hjmem hfirst).symm⟩

private theorem thresholdPositiveLevels_sdCellMap
    {n : SimplexCategory} {d : ℕ}
    (σ : (SimplexCategory.sd.{u}.obj n) _⦋d⦌)
    (hσ : StrictMono σ.obj)
    (q : Convexity.StdSimplex ℝ (Fin (d + 1)))
    (hq : ∀ j, 0 < q.weights j) :
    thresholdPositiveLevels (SimplexCategory.sdCellMap σ q) =
      Finset.univ.image (cellLevel σ q) := by
  classical
  ext t
  constructor
  · intro ht
    obtain ⟨i, hi, hit⟩ := Finset.mem_image.mp ht
    have hiPos := (Finset.mem_filter.mp hi).2
    obtain ⟨j, hj⟩ := exists_cellLevel_eq_weight_of_pos σ q hiPos
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj.trans hit⟩
  · intro ht
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨i, hi⟩ := exists_weight_eq_cellLevel σ hσ q j
    apply Finset.mem_image.mpr
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hi⟩
    exact hi ▸ cellLevel_pos σ q hq j

private theorem thresholdPositiveLevels_sdCellMap_card
    {n : SimplexCategory} {d : ℕ}
    (σ : (SimplexCategory.sd.{u}.obj n) _⦋d⦌)
    (hσ : StrictMono σ.obj)
    (q : Convexity.StdSimplex ℝ (Fin (d + 1)))
    (hq : ∀ j, 0 < q.weights j) :
    (thresholdPositiveLevels (SimplexCategory.sdCellMap σ q)).card =
      d + 1 := by
  rw [thresholdPositiveLevels_sdCellMap σ hσ q hq,
    Finset.card_image_of_injective _
      (cellLevel_strictAnti σ q hq).injective]
  simp

private theorem down_mem_cellFace_iff
    {n : SimplexCategory} {d : ℕ}
    (σ : (SimplexCategory.sd.{u}.obj n) _⦋d⦌)
    (j : Fin (d + 1))
    (a : ULift.{u} (Fin (n.len + 1))) :
    a.down ∈ cellFace σ j ↔ a ∈ (σ.obj j).finset := by
  constructor
  · intro h
    obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp h
    have hba' : b = a := ULift.down_injective hba
    exact hba' ▸ hb
  · intro h
    exact Finset.mem_image.mpr ⟨a, h, rfl⟩

private theorem carrier_eq_of_sdCellMap_eq
    {n : SimplexCategory} {d₁ d₂ : ℕ}
    (σ₁ : (SimplexCategory.sd.{u}.obj n) _⦋d₁⦌)
    (hσ₁ : σ₁ ∈ (SimplexCategory.sd.{u}.obj n).nonDegenerate d₁)
    (q₁ : Convexity.StdSimplex ℝ (Fin (d₁ + 1)))
    (hq₁ : ∀ j, 0 < q₁.weights j)
    (σ₂ : (SimplexCategory.sd.{u}.obj n) _⦋d₂⦌)
    (hσ₂ : σ₂ ∈ (SimplexCategory.sd.{u}.obj n).nonDegenerate d₂)
    (q₂ : Convexity.StdSimplex ℝ (Fin (d₂ + 1)))
    (hq₂ : ∀ j, 0 < q₂.weights j)
    (hmap : SimplexCategory.sdCellMap σ₁ q₁ =
      SimplexCategory.sdCellMap σ₂ q₂) :
    SSet.N.mk σ₁ hσ₁ = SSet.N.mk σ₂ hσ₂ := by
  classical
  have hs₁ : StrictMono σ₁.obj :=
    (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono σ₁).mp hσ₁
  have hs₂ : StrictMono σ₂.obj :=
    (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono σ₂).mp hσ₂
  have hd : d₁ = d₂ := by
    have hcard₁ :=
      thresholdPositiveLevels_sdCellMap_card σ₁ hs₁ q₁ hq₁
    have hcard₂ :=
      thresholdPositiveLevels_sdCellMap_card σ₂ hs₂ q₂ hq₂
    rw [hmap] at hcard₁
    omega
  subst d₂
  let L := thresholdPositiveLevels (SimplexCategory.sdCellMap σ₁ q₁)
  have hLcard : L.card = d₁ + 1 :=
    thresholdPositiveLevels_sdCellMap_card σ₁ hs₁ q₁ hq₁
  let f₁ : Fin (d₁ + 1) → ℝ := fun j => cellLevel σ₁ q₁ j.rev
  let f₂ : Fin (d₁ + 1) → ℝ := fun j => cellLevel σ₂ q₂ j.rev
  have hf₁mem : ∀ j, f₁ j ∈ L := by
    intro j
    rw [show L = thresholdPositiveLevels
      (SimplexCategory.sdCellMap σ₁ q₁) from rfl,
      thresholdPositiveLevels_sdCellMap σ₁ hs₁ q₁ hq₁]
    exact Finset.mem_image.mpr ⟨j.rev, Finset.mem_univ _, rfl⟩
  have hf₂mem : ∀ j, f₂ j ∈ L := by
    intro j
    rw [show L = thresholdPositiveLevels
      (SimplexCategory.sdCellMap σ₁ q₁) from rfl, hmap,
      thresholdPositiveLevels_sdCellMap σ₂ hs₂ q₂ hq₂]
    exact Finset.mem_image.mpr ⟨j.rev, Finset.mem_univ _, rfl⟩
  have hf₁strict : StrictMono f₁ := by
    intro i j hij
    exact (cellLevel_strictAnti σ₁ q₁ hq₁)
      ((Fin.rev_lt_rev (i := j) (j := i)).mpr hij)
  have hf₂strict : StrictMono f₂ := by
    intro i j hij
    exact (cellLevel_strictAnti σ₂ q₂ hq₂)
      ((Fin.rev_lt_rev (i := j) (j := i)).mpr hij)
  have hf₁ : f₁ = L.orderEmbOfFin hLcard :=
    Finset.orderEmbOfFin_unique hLcard hf₁mem hf₁strict
  have hf₂ : f₂ = L.orderEmbOfFin hLcard :=
    Finset.orderEmbOfFin_unique hLcard hf₂mem hf₂strict
  have hlevel (j : Fin (d₁ + 1)) :
      cellLevel σ₁ q₁ j = cellLevel σ₂ q₂ j := by
    have h := congrFun (hf₁.trans hf₂.symm) j.rev
    simpa [f₁, f₂] using h
  have hface (j : Fin (d₁ + 1)) : cellFace σ₁ j = cellFace σ₂ j := by
    ext i
    rw [mem_cellFace_iff_cellLevel_le σ₁ q₁ hq₁,
      mem_cellFace_iff_cellLevel_le σ₂ q₂ hq₂,
      hlevel j, hmap]
  have hsigma : σ₁ = σ₂ := by
    apply ComposableArrows.ext
      (h := fun j => ?_)
      (w := by
        intro i hi
        subsingleton)
    apply PartialOrder.NonemptyFiniteChains.ext
    apply (@Finset.image_injective
      (ULift.{u} (Fin (n.len + 1))) (Fin (n.len + 1))
      (instDecidableEqFin (n.len + 1)) ULift.down
      ULift.down_injective)
    exact hface j
  subst σ₂
  rfl

private theorem cellLevel_last {n : SimplexCategory} {d : ℕ}
    (σ : (SimplexCategory.sd.{u}.obj n) _⦋d⦌)
    (q : Convexity.StdSimplex ℝ (Fin (d + 1))) :
    cellLevel σ q (Fin.last d) = cellTerm σ q (Fin.last d) := by
  simp [cellLevel]

private theorem cellLevel_castSucc {n : SimplexCategory} {d : ℕ}
    (σ : (SimplexCategory.sd.{u}.obj n) _⦋d⦌)
    (q : Convexity.StdSimplex ℝ (Fin (d + 1))) (j : Fin d) :
    cellLevel σ q j.castSucc =
      cellTerm σ q j.castSucc + cellLevel σ q j.succ := by
  unfold cellLevel
  rw [Finset.Icc_eq_cons_Ioc (Fin.le_last j.castSucc),
    Finset.sum_cons]
  have hI : Finset.Ioc j.castSucc (Fin.last d) =
      Finset.Icc j.succ (Fin.last d) := by
    ext k
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    exact and_congr Fin.castSucc_lt_iff_succ_le Iff.rfl
  rw [hI]

private theorem cellTerm_eq_of_cellLevel_eq
    {n : SimplexCategory} {d : ℕ}
    (σ : (SimplexCategory.sd.{u}.obj n) _⦋d⦌)
    (q₁ q₂ : Convexity.StdSimplex ℝ (Fin (d + 1)))
    (hlevel : ∀ j, cellLevel σ q₁ j = cellLevel σ q₂ j) :
    ∀ j, cellTerm σ q₁ j = cellTerm σ q₂ j := by
  intro j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · rw [← cellLevel_last σ q₁, ← cellLevel_last σ q₂]
    exact hlevel _
  · have h₁ := cellLevel_castSucc σ q₁ k
    have h₂ := cellLevel_castSucc σ q₂ k
    have h₃ := hlevel k.castSucc
    have h₄ := hlevel k.succ
    linarith

private theorem stdSimplex_eq_of_cellLevel_eq
    {n : SimplexCategory} {d : ℕ}
    (σ : (SimplexCategory.sd.{u}.obj n) _⦋d⦌)
    (q₁ q₂ : Convexity.StdSimplex ℝ (Fin (d + 1)))
    (hlevel : ∀ j, cellLevel σ q₁ j = cellLevel σ q₂ j) :
    q₁ = q₂ := by
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro j
  have hterm := cellTerm_eq_of_cellLevel_eq σ q₁ q₂ hlevel j
  unfold cellTerm at hterm
  have hc : ((cellFace σ j).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr (cellFace_nonempty σ j)).ne'
  exact (div_left_inj' hc).mp hterm

private theorem stdSimplex_eq_of_sdCellMap_eq
    {n : SimplexCategory} {d : ℕ}
    (σ : (SimplexCategory.sd.{u}.obj n) _⦋d⦌)
    (hσ : StrictMono σ.obj)
    (q₁ q₂ : Convexity.StdSimplex ℝ (Fin (d + 1)))
    (hmap : SimplexCategory.sdCellMap σ q₁ =
      SimplexCategory.sdCellMap σ q₂) :
    q₁ = q₂ := by
  apply stdSimplex_eq_of_cellLevel_eq σ
  intro j
  obtain ⟨i, hi, hfirst⟩ := exists_new_cellFace_vertex σ hσ j
  rw [← weight_eq_cellLevel_of_first σ q₁ hi hfirst,
    ← weight_eq_cellLevel_of_first σ q₂ hi hfirst, hmap]

/--
A nondegenerate subdivision carrier of the standard `n`-simplex, together with
barycentric coordinates in its cell whose every coordinate is strictly positive.
-/
structure ThresholdCoordinates (n : ℕ) where
  /--
  The nondegenerate subdivision simplex carrying the threshold coordinates.
  -/
  carrier : (SimplexCategory.sd.{u}.obj ⦋n⦌).N
  /--
  The real standard-simplex point in the dimension of the chosen nondegenerate carrier.
  -/
  point : Convexity.StdSimplex ℝ (Fin (carrier.dim + 1))
  /--
  Every barycentric coordinate of the carrier-cell point is strictly positive.
  -/
  point_pos : ∀ j, 0 < point.weights j

/--
Equal nondegenerate carriers and heterogeneously equal carrier-cell points determine
equal threshold-coordinate data.
-/
@[ext]
theorem ThresholdCoordinates.ext {n : ℕ}
    {a b : ThresholdCoordinates.{u} n}
    (hcarrier : a.carrier = b.carrier)
    (hpoint : HEq a.point b.point) : a = b := by
  cases a with
  | mk ac ap ah =>
    cases b with
    | mk bc bp bh =>
      dsimp only at hcarrier hpoint
      cases hcarrier
      cases hpoint
      rfl

private theorem point_heq_of_carrier_eq_of_sdCellMap_eq
    {n : SimplexCategory} {d₁ d₂ : ℕ}
    (σ₁ : (SimplexCategory.sd.{u}.obj n) _⦋d₁⦌)
    (hσ₁ : σ₁ ∈ (SimplexCategory.sd.{u}.obj n).nonDegenerate d₁)
    (q₁ : Convexity.StdSimplex ℝ (Fin (d₁ + 1)))
    (σ₂ : (SimplexCategory.sd.{u}.obj n) _⦋d₂⦌)
    (hσ₂ : σ₂ ∈ (SimplexCategory.sd.{u}.obj n).nonDegenerate d₂)
    (q₂ : Convexity.StdSimplex ℝ (Fin (d₂ + 1)))
    (hcarrier : SSet.N.mk σ₁ hσ₁ = SSet.N.mk σ₂ hσ₂)
    (hmap : SimplexCategory.sdCellMap σ₁ q₁ =
      SimplexCategory.sdCellMap σ₂ q₂) : HEq q₁ q₂ := by
  have hS : SSet.S.mk σ₁ = SSet.S.mk σ₂ :=
    congrArg SSet.N.toS hcarrier
  have hd : d₁ = d₂ := SSet.S.dim_eq_of_mk_eq hS
  subst d₂
  have hsigma : σ₁ = σ₂ := (SSet.S.ext_iff σ₁ σ₂).mp hS
  subst σ₂
  have hstrict : StrictMono σ₁.obj :=
    (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono σ₁).mp hσ₁
  exact heq_of_eq
    (stdSimplex_eq_of_sdCellMap_eq σ₁ hstrict q₁ q₂ hmap)

/--
The original standard-simplex point obtained by evaluating the affine subdivision
cell of the given carrier at its interior barycentric point.
-/
noncomputable def thresholdCoordinatesToPoint {n : ℕ}
    (c : ThresholdCoordinates.{u} n) :
    Convexity.StdSimplex ℝ (Fin (n + 1)) :=
  SimplexCategory.sdCellMap c.carrier.simplex c.point

/--
The nondegenerate superlevel-face simplex and its strictly positive jump masses
associated to a point of the real standard `n`-simplex.
-/
noncomputable def thresholdCoordinates {n : ℕ}
    (x : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    ThresholdCoordinates.{u} n where
  carrier := SSet.N.mk (thresholdSimplex.{u} x)
    (thresholdSimplex_nonDegenerate (x := x))
  point := thresholdWeights x
  point_pos := thresholdWeights_pos x

/--
Evaluating the threshold coordinates extracted from a standard-simplex point
returns that point.
-/
@[simp]
theorem thresholdCoordinatesToPoint_thresholdCoordinates {n : ℕ}
    (x : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    thresholdCoordinatesToPoint (thresholdCoordinates.{u} x) = x :=
  sdCellMap_threshold (x := x)

/--
Extracting threshold coordinates after evaluating a nondegenerate cell at an
interior point returns the same carrier and cell point.
-/
@[simp]
theorem thresholdCoordinates_thresholdCoordinatesToPoint {n : ℕ}
    (c : ThresholdCoordinates.{u} n) :
    thresholdCoordinates.{u} (thresholdCoordinatesToPoint c) = c := by
  rcases c with ⟨s, q, hq⟩
  let x := thresholdCoordinatesToPoint
    (⟨s, q, hq⟩ : ThresholdCoordinates.{u} n)
  have hmap : SimplexCategory.sdCellMap (thresholdSimplex.{u} x)
      (thresholdWeights x) =
      SimplexCategory.sdCellMap s.simplex q := by
    simpa only [x, thresholdCoordinatesToPoint] using
      sdCellMap_threshold (x := x)
  have hcarrier :
      SSet.N.mk (thresholdSimplex.{u} x)
          (thresholdSimplex_nonDegenerate (x := x)) = s :=
    carrier_eq_of_sdCellMap_eq
      (thresholdSimplex.{u} x)
      (thresholdSimplex_nonDegenerate (x := x))
      (thresholdWeights x) (thresholdWeights_pos x)
      s.simplex s.nonDegenerate q hq hmap
  apply ThresholdCoordinates.ext hcarrier
  exact point_heq_of_carrier_eq_of_sdCellMap_eq
    (thresholdSimplex.{u} x)
    (thresholdSimplex_nonDegenerate (x := x))
    (thresholdWeights x) s.simplex s.nonDegenerate q hcarrier hmap

/--
The set-level equivalence between the real standard `n`-simplex and nondegenerate
subdivision carriers equipped with strictly positive barycentric cell coordinates.
-/
noncomputable def thresholdCoordinatesEquiv (n : ℕ) :
    Convexity.StdSimplex ℝ (Fin (n + 1)) ≃ ThresholdCoordinates.{u} n where
  toFun := thresholdCoordinates
  invFun := thresholdCoordinatesToPoint
  left_inv := thresholdCoordinatesToPoint_thresholdCoordinates
  right_inv := thresholdCoordinates_thresholdCoordinatesToPoint

end SSet

end
